#!/usr/bin/env python3
"""52_frontier_semantic_donors.py — SEMANTIC donor-transfer map for
INCOMPLETELY-FORMALIZED frontier material (part (b)).

Why this differs from scripts 28/44 (the structural / symmetric semantic tracks)
--------------------------------------------------------------------------------
The earlier semantic track (28) hunts hidden abstractions between two MATURE
theorems: it requires both sides to be theorems with a real conclusion head,
shares a conclusion-HEAD word as the blocking anchor, and keeps only pairs that
structurally DIVERGE. That biases toward abstractions which already exist.

The user's standing point: when a structure is genuinely undiscovered /
incompletely formalized, its structural signature is NOT complete, so
structural/AST-shape matching under-recalls exactly the interesting cases. This
script therefore points SEMANTIC matching (mathematical MEANING vocabulary +
abstract ROLE, never the concrete constructor/head) at the FRONTIER and makes
the search ASYMMETRIC:

    frontier target (thin / near a famous open problem, possibly with an opaque
    or missing proof)  --semantic nearest neighbour-->  MATURE CORE-AREA donor.

A mature donor that plays the same mathematical role as an under-developed
frontier statement is a *transfer candidate*: machinery/abstraction the frontier
could import. Structural divergence is REPORTED (structuralGap), never required,
and a frontier target with an opaque value still matches on name+type meaning.

Method (pure stdlib, deterministic)
-----------------------------------
1. Global TF-IDF over concept-word MEANING (declaration name + conclusion head +
   value head) and abstract ROLE tokens (conclusion predicate-role P, proof-value
   role V, constraint-AREA profile R, proof-strategy flags S, coarse shape),
   reusing script 28's identity-free tokenizer.
2. Targets = declarations in FRONTIER-bucket areas that either
   (A) sit in a curated famous-problem / missing-ingredient neighbourhood
       (unit-distance, planar, crossing, incidence, Szemeredi-Trotter,
       degeneracy, chromatic/coloring, jacobian, ramsey, hailstone/collatz,
       Navier-Stokes), or
   (B) are "incomplete/thin" (opaque or missing value, or very small proof term)
       in the highest-opportunity-pressure frontier areas, capped per area.
   Zero targets for a famous seed is itself a footprint finding (reported).
3. Donors = declarations in the 10 MATURE core areas. A streaming second pass
   scores each donor only against targets reached through a DISTINCTIVE shared
   meaning word (document-frequency-anchored inverted index), so common words
   (finite / measurable / continuous ...) cannot blow up the fan-out; the gate
   is >=2 shared meaning words and a meaning-cosine floor.
4. sim = 0.65*meaningCos + 0.35*roleCos. Per target keep the top-K donors and
   flag structuralGap (different concrete conclusion/value head, or the target
   value is opaque). Aggregate a donor-area -> frontier-concept transfer map.

Inputs : data/atlas_features.jsonl, data/atlas_type_skeletons.jsonl,
         data/atlas_classes.jsonl, data/area_maturity_profile.jsonl
Outputs: data/frontier_semantic_donors.jsonl   (top donor pairs)
         data/frontier_semantic_targets.jsonl  (per-target best donor summary)
         data/frontier_semantic_summary.json
"""
import json, math, collections, os, re, time, heapq

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
DATA = os.path.join(ROOT, "data")
FEAT = os.path.join(DATA, "atlas_features.jsonl")
SKEL = os.path.join(DATA, "atlas_type_skeletons.jsonl")
CLS = os.path.join(DATA, "atlas_classes.jsonl")
MAT = os.path.join(DATA, "area_maturity_profile.jsonl")
OUT_DONORS = os.path.join(DATA, "frontier_semantic_donors.jsonl")
OUT_TARGETS = os.path.join(DATA, "frontier_semantic_targets.jsonl")
OUT_SUM = os.path.join(DATA, "frontier_semantic_summary.json")

INCLUDE_KINDS = {"theorem", "definition", "opaque"}
GEN_SUFFIX = ("hcongr",)
TF_CAP = 4
MEANING_W = 0.65
ROLE_W = 0.35
MIN_SHARED_MEANING = 2
MEANING_COS_FLOOR = float(os.environ.get("ATLAS_FS_MEANING_FLOOR", "0.30"))
SIM_FLOOR = float(os.environ.get("ATLAS_FS_SIM_FLOOR", "0.42"))
TOPK = 8
THIN_PER_AREA = int(os.environ.get("ATLAS_FS_THIN_PER_AREA", "100"))
ANCHOR_DF_CAP = 2000          # a meaning word must be this rare to anchor search
SAME_CONCEPT_DF = 400         # shared word rarer than this => same concept family
SHORT_VAL_NODES = 12          # valueNodes <= this counts as a "thin" term
# notation / derived-constructor boilerplate that carries no mathematical role
BOILERPLATE_SUBSTR = ("term_", "«term", "ctoridx", "ctor_idx", ".quot",
                      "notation", "match_", "_match", "anonymous", "raw_",
                      "delab", "parser_", "_parser", "macro_", ".macro")
TOPPRESSURE_AREAS = {"SetTheory", "Dynamics", "Combinatorics", "NumberTheory",
                     "Condensed", "Probability", "AlgebraicTopology",
                     "ModelTheory", "Geometry", "MeasureTheory",
                     "RepresentationTheory", "InformationTheory"}

# famous-problem / missing-ingredient neighbourhoods. Each entry maps a label to
# a predicate over the set of lowercase concept words in the declaration NAME.
def _has(words, *ws):
    return all(w in words for w in ws)

def _any(words, *ws):
    return any(w in words for w in ws)

SEEDS = [
    ("unit_distance", lambda w: _has(w, "unit", "dist") or "unitdist" in w or
                                _has(w, "unit", "distance")),
    ("planar",        lambda w: "planar" in w),
    ("crossing",      lambda w: "crossing" in w or "cross" in w),
    ("incidence",     lambda w: "incidence" in w),
    ("szemeredi_trotter", lambda w: _any(w, "szemeredi", "trotter")),
    ("degeneracy",    lambda w: _any(w, "degeneracy", "degenerate")),
    ("graph_coloring", lambda w: _any(w, "chromatic", "colorable", "coloring")),
    ("jacobian",      lambda w: "jacobian" in w),
    ("ramsey",        lambda w: "ramsey" in w),
    ("collatz_hailstone", lambda w: _any(w, "hailstone", "collatz")),
    ("navier_stokes", lambda w: _any(w, "stokes") or _has(w, "navier")),
]
SEED_LABELS = [s[0] for s in SEEDS]


def log(m):
    print(f"[{time.strftime('%H:%M:%S')}] {m}", flush=True)


def bucket(x):
    if x <= 0:
        return 0
    return min(7, (x - 1).bit_length())


def area_of(module):
    p = module.split(".")
    return p[1] if len(p) >= 2 and p[0] == "Mathlib" else "(root)"


ORDER_ROOTS = {"LE", "LT", "GE", "GT", "Min", "Max", "Subset", "SubsetEq",
               "SSubset", "SSubsetEq", "IsLeast", "IsGreatest", "IsLUB",
               "IsGLB", "Directed", "CovBy", "WCovBy"}
LOGIC_ROLES = {
    "Eq": "equality", "Iff": "iff", "Not": "negation", "And": "and",
    "Or": "or", "Exists": "exists", "False": "false", "True": "true",
    "Membership.mem": "membership",
}

_HUMP = re.compile(r"[A-Z]+(?=[A-Z][a-z])|[A-Z]?[a-z]+|[A-Z]+|\d+")
STOPWORDS = {
    "is", "of", "the", "a", "to", "le", "ge", "lt", "gt", "eq", "ne", "mk",
    "class", "inst", "self", "this", "h", "x", "y", "f", "g", "on", "for",
    "and", "or", "not", "iff", "def", "thm", "aux", "proof",
}
# ultra-common mathematical glue: kept in vectors but never distinctive anchors
GLUE_WORDS = {
    "finite", "infinite", "measurable", "continuous", "compact", "bounded",
    "closed", "open", "linear", "map", "maps", "set", "sets", "function",
    "functions", "type", "types", "lemma", "theorem", "prop", "proof",
    "instance", "structure", "add", "mul", "zero", "one", "two", "neg",
    "sub", "div", "pow", "left", "right", "basic", "core", "def",
}


def concept_words(name):
    out = []
    for seg in (name or "").split("."):
        for w in _HUMP.findall(seg):
            wl = w.lower()
            if len(wl) >= 3 and wl not in STOPWORDS:
                out.append(wl)
    return out


def pred_role(ch, class_names):
    root = ch.split(".")[-1] if ch else ""
    if not root:
        return "no-conclusion"
    if root in LOGIC_ROLES:
        return "P:" + LOGIC_ROLES[root]
    if root in ORDER_ROOTS:
        return "P:order-comp"
    if ch in class_names:
        return "P:instance-goal"
    return "P:other-pred"


def vh_role(vh, has_value, truncated):
    if not has_value:
        return "V:none"
    if not vh or truncated:
        return "V:opaque"
    root = vh.split(".")[-1]
    if root in ("rfl", "Eq.refl"):
        return "V:rfl"
    if root == "mk" or root.endswith(".mk"):
        return "V:constructor"
    if root in ("casesOn",) or root.endswith("casesOn"):
        return "V:cases"
    if root.endswith("recOn") or root.endswith("brecOn") or root in ("rec",):
        return "V:recursor"
    if root in ("Eq.mpr", "Eq.mp", "Iff.mpr", "Iff.mp", "Eq.ndrec",
                "Eq.rec", "id", "Eq.symm"):
        return "V:rewrite"
    return "V:named-lemma"


def is_generated_tail(tail):
    return (tail.endswith("casesOn") or tail.endswith("recOn") or
            tail.endswith("brecOn") or tail in ("rec", "noConfusion",
            "noConfusionType") or tail.endswith("inductionOn"))


def build_counters(r, class_area, class_names, skel_cons):
    name = r["name"]
    ch = r.get("conclusionHead") or ""
    vh = r.get("valueHead") or ""
    prole = pred_role(ch, class_names)
    vrole = vh_role(vh, r.get("hasValue"), r.get("valueTruncated"))

    meaning = collections.Counter()
    for w in concept_words(name):
        meaning[("w", w)] += 1
    for w in concept_words(ch):
        meaning[("w", w)] += 1
    if vh and r.get("hasValue") and not r.get("valueTruncated"):
        for w in concept_words(vh):
            meaning[("w", w)] += 1

    role = collections.Counter()
    role[("k", r["kind"])] += 1
    role[("P", prole)] += 1
    role[("V", vrole)] += 1
    for c in skel_cons.get(name, []):
        a = class_area.get(c)
        if a:
            role[("R", a)] += 1
    role[("s", "pi", bucket(r["nPi"]))] += 1
    role[("s", "nc", bucket(len(skel_cons.get(name, []))))] += 1
    role[("s", "tn", bucket(r["typeNodes"]))] += 1
    role[("s", "td", bucket(r["typeDepth"]))] += 1
    role[("s", "vn", bucket(r["valueNodes"]))] += 1
    role[("s", "vd", bucket(r["valueDepth"]))] += 1
    if r.get("valueIsRfl"):
        role[("S", "rfl")] += 1
    if (r.get("caseRefs") or 0) > 0:
        role[("S", "uses-cases")] += 1
    if (r.get("recRefs") or 0) > 0:
        role[("S", "uses-rec")] += 1
    # cap tf
    meaning = {t: min(TF_CAP, c) for t, c in meaning.items()}
    role = {t: min(TF_CAP, c) for t, c in role.items()}
    return meaning, role, prole, vrole


def eligible(r):
    if r["isGenerated"] or r["kind"] not in INCLUDE_KINDS:
        return False
    if r.get("isInstance") or r.get("isClass"):
        return False
    name, module = r["name"], r["module"]
    if name.startswith("_private") or ".Meta." in module:
        return False
    tail = name.rsplit(".", 1)[-1]
    if tail.startswith(GEN_SUFFIX) or is_generated_tail(tail):
        return False
    low = name.lower()
    if any(b in low for b in BOILERPLATE_SUBSTR):
        return False
    return True


def main():
    # area -> bucket
    bucket_of_area = {}
    with open(MAT, "rb") as f:
        for line in f:
            r = json.loads(line)
            bucket_of_area[r["area"]] = r["bucket"]
    core_areas = {a for a, b in bucket_of_area.items() if b == "core"}
    frontier_areas = {a for a, b in bucket_of_area.items() if b == "frontier"}
    log(f"core areas {len(core_areas)}; frontier areas {len(frontier_areas)}")

    # classes
    class_area, class_names = {}, set()
    with open(CLS, "rb") as f:
        for line in f:
            r = json.loads(line)
            class_names.add(r["name"])
            class_area[r["name"]] = area_of(r["module"])

    # skeleton constraint classes
    skel_cons = {}
    with open(SKEL, "rb") as f:
        for line in f:
            r = json.loads(line)
            skel_cons[r["name"]] = [c["class"] for c in r.get("constraints", [])]
    log(f"skeletons loaded: {len(skel_cons):,}")

    # ---- pass 1: global DF over meaning & role tokens; collect targets ------
    df_meaning = collections.Counter()
    df_role = collections.Counter()
    targets = []            # dict: meta + raw counters
    thin_count = collections.Counter()
    seed_hits = collections.Counter()
    n_scanned = n_elig = 0
    LIMIT = int(os.environ.get("ATLAS_LIMIT", "0"))
    with open(FEAT, "rb") as f:
        for line in f:
            r = json.loads(line)
            n_scanned += 1
            if LIMIT and n_scanned > LIMIT:
                break
            if not eligible(r):
                continue
            n_elig += 1
            area = area_of(r["module"])
            if area not in core_areas and area not in frontier_areas:
                continue
            meaning, role, prole, vrole = build_counters(
                r, class_area, class_names, skel_cons)
            for t in meaning:
                df_meaning[t] += 1
            for t in role:
                df_role[t] += 1

            if area in frontier_areas:
                name_words = set(concept_words(r["name"]))
                seed = next((lab for lab, pred in SEEDS if pred(name_words)),
                            None)
                thin = (not r.get("hasValue") or r.get("valueTruncated") or
                        r.get("valueNodes", 0) <= SHORT_VAL_NODES)
                take, why = False, None
                if seed is not None:
                    take, why = True, "seed:" + seed
                    seed_hits[seed] += 1
                elif (area in TOPPRESSURE_AREAS and thin and
                        thin_count[area] < THIN_PER_AREA):
                    take, why = True, "thin"
                    thin_count[area] += 1
                if take:
                    targets.append({
                        "name": r["name"], "module": r["module"], "area": area,
                        "kind": r["kind"], "ch": r.get("conclusionHead") or "",
                        "vh": r.get("valueHead") or "",
                        "prole": prole, "vrole": vrole,
                        "complete": bool(r.get("hasValue") and
                                         not r.get("valueTruncated")),
                        "why": why, "seed": seed,
                        "meaning": meaning, "role": role})
    log(f"scanned {n_scanned:,}; eligible {n_elig:,}; targets {len(targets):,}")
    log("seed hits: " + json.dumps(dict(seed_hits)))

    # idf
    N = n_elig

    def idf_table(df):
        return {t: math.log((N + 1.0) / (c + 1.0)) + 1.0 for t, c in df.items()}

    idf_m, idf_r = idf_table(df_meaning), idf_table(df_role)

    def normalize(counter, idf):
        w, s = {}, 0.0
        for t, tf in counter.items():
            v = (1.0 + math.log(tf)) * idf.get(t, 1.0)
            w[t] = v
            s += v * v
        n = math.sqrt(s)
        return ({t: v / n for t, v in w.items()} if n else {})

    # target vectors + distinctive-word anchor index
    for t in targets:
        t["mv"] = normalize(t["meaning"], idf_m)
        t["rv"] = normalize(t["role"], idf_r)
        t["mwords"] = {tok[1] for tok in t["meaning"]}
    anchor = collections.defaultdict(list)   # distinctive word -> target idx
    for i, t in enumerate(targets):
        for w in t["mwords"]:
            tok = ("w", w)
            if w in GLUE_WORDS:
                continue
            if df_meaning.get(tok, 0) <= ANCHOR_DF_CAP:
                anchor[w].append(i)
    log(f"distinctive anchor words: {len(anchor):,}")

    def cosine(va, vb):
        if len(va) > len(vb):
            va, vb = vb, va
        return sum(v * vb.get(tok, 0.0) for tok, v in va.items())

    # per-target top-K heaps of (sim, donor meta, mcos, rcos, shared, gap)
    best = [[] for _ in targets]

    def push(i, item):
        h = best[i]
        if len(h) < TOPK:
            heapq.heappush(h, item)
        elif item[0] > h[0][0]:
            heapq.heapreplace(h, item)

    # ---- pass 2: stream CORE donors, score against anchored targets --------
    n_donors = 0
    n_scored = 0
    n_samefamily = 0
    with open(FEAT, "rb") as f:
        for line in f:
            r = json.loads(line)
            if not eligible(r):
                continue
            area = area_of(r["module"])
            if area not in core_areas:
                continue
            n_donors += 1
            meaning, role, prole, vrole = build_counters(
                r, class_area, class_names, skel_cons)
            dwords = {tok[1] for tok in meaning}
            cand = set()
            for w in dwords:
                if w in GLUE_WORDS:
                    continue
                lst = anchor.get(w)
                if lst:
                    cand.update(lst)
            if not cand:
                continue
            mv = normalize(meaning, idf_m)
            rv = normalize(role, idf_r)
            dmeta = (r["name"], area, r.get("conclusionHead") or "",
                     r.get("valueHead") or "")
            for i in cand:
                t = targets[i]
                if t["area"] == area:
                    continue
                shared = dwords & t["mwords"]
                if len(shared) < MIN_SHARED_MEANING:
                    continue
                # sharing a RARE word means the two are the SAME concrete
                # concept family (prime/module variants, same namespace API);
                # an ANALOGY shares role/mid-level meaning but has a different
                # distinctive concept stem, so drop same-family pairs.
                if any(df_meaning.get(("w", w), 0) <= SAME_CONCEPT_DF
                       for w in shared):
                    n_samefamily += 1
                    continue
                mcos = cosine(mv, t["mv"])
                if mcos < MEANING_COS_FLOOR:
                    continue
                rcos = cosine(rv, t["rv"])
                sim = MEANING_W * mcos + ROLE_W * rcos
                n_scored += 1
                if sim < SIM_FLOOR:
                    continue
                gap = (dmeta[2] != t["ch"] or dmeta[3] != t["vh"] or
                       not t["complete"])
                item = (round(sim, 6), dmeta, round(mcos, 6), round(rcos, 6),
                        sorted(shared), gap)
                push(i, item)
    log(f"core donors scanned {n_donors:,}; above-floor pair evaluations "
        f"{n_scored:,}; same-concept-family pairs dropped {n_samefamily:,}")

    # ---- emit ---------------------------------------------------------------
    pair_rows, target_rows = [], []
    gap_pairs = 0
    donor_area_flow = collections.Counter()
    donor_concept_flow = collections.Counter()
    covered = 0
    for i, t in enumerate(targets):
        h = sorted(best[i], key=lambda z: -z[0])
        if not h:
            target_rows.append({
                "target": t["name"], "area": t["area"], "module": t["module"],
                "seed": t["seed"], "why": t["why"], "complete": t["complete"],
                "nDonors": 0, "bestSim": None, "bestDonorArea": None})
            continue
        covered += 1
        best_sim = h[0][0]
        best_area = h[0][1][1]
        target_rows.append({
            "target": t["name"], "area": t["area"], "module": t["module"],
            "seed": t["seed"], "why": t["why"], "complete": t["complete"],
            "nDonors": len(h), "bestSim": best_sim, "bestDonorArea": best_area,
            "bestDonor": h[0][1][0]})
        for sim, dmeta, mcos, rcos, shared, gap in h:
            if gap:
                gap_pairs += 1
                donor_area_flow[(dmeta[1], t["area"])] += 1
                if t["seed"]:
                    donor_concept_flow[(dmeta[1], t["seed"])] += 1
            pair_rows.append({
                "sim": sim, "meaningCos": mcos, "roleCos": rcos,
                "structuralGap": gap, "sharedMeaning": shared[:14],
                "target": {"name": t["name"], "area": t["area"],
                           "module": t["module"], "seed": t["seed"],
                           "complete": t["complete"],
                           "conclusionHead": t["ch"], "valueHead": t["vh"],
                           "predRole": t["prole"], "valueRole": t["vrole"]},
                "donor": {"name": dmeta[0], "area": dmeta[1],
                          "conclusionHead": dmeta[2], "valueHead": dmeta[3]}})

    pair_rows.sort(key=lambda z: -z["sim"])
    with open(OUT_DONORS, "wb") as o:
        for row in pair_rows:
            o.write((json.dumps(row, ensure_ascii=False) + "\n").encode("utf-8"))
    with open(OUT_TARGETS, "wb") as o:
        for row in target_rows:
            o.write((json.dumps(row, ensure_ascii=False) + "\n").encode("utf-8"))

    # seed coverage: how many matched targets got a donor per famous seed
    seed_targets = collections.Counter()
    seed_covered = collections.Counter()
    seed_best = {}
    for row in target_rows:
        if row["seed"]:
            seed_targets[row["seed"]] += 1
            if row["nDonors"]:
                seed_covered[row["seed"]] += 1
                b = seed_best.get(row["seed"])
                if b is None or row["bestSim"] > b:
                    seed_best[row["seed"]] = row["bestSim"]
    seed_coverage = {
        s: {"namedTargets": seed_targets.get(s, 0),
            "withMatureDonor": seed_covered.get(s, 0),
            "bestSim": seed_best.get(s)}
        for s in SEED_LABELS}

    summary = {
        "params": {"meaningWeight": MEANING_W, "roleWeight": ROLE_W,
                   "minSharedMeaning": MIN_SHARED_MEANING,
                   "meaningCosFloor": MEANING_COS_FLOOR, "simFloor": SIM_FLOOR,
                   "topK": TOPK, "thinPerArea": THIN_PER_AREA,
                   "anchorDfCap": ANCHOR_DF_CAP, "sameConceptDf": SAME_CONCEPT_DF,
                   "shortValNodes": SHORT_VAL_NODES},
        "scanned": n_scanned, "eligible": n_elig,
        "coreDonors": n_donors, "targets": len(targets),
        "sameConceptFamilyDropped": n_samefamily,
        "targetsBySeed": dict(seed_hits),
        "thinTargets": dict(thin_count),
        "targetsWithDonor": covered,
        "targetCoverage": round(covered / max(1, len(targets)), 4),
        "donorPairs": len(pair_rows),
        "structuralGapPairs": gap_pairs,
        "famousSeedCoverage": seed_coverage,
        "topDonorToFrontierFlow": [
            {"donorArea": a, "frontierArea": b, "count": c}
            for (a, b), c in donor_area_flow.most_common(25)],
        "topDonorToConceptFlow": [
            {"donorArea": a, "concept": s, "count": c}
            for (a, s), c in donor_concept_flow.most_common(25)],
        "topTransferCandidates": [
            {"sim": p["sim"], "meaningCos": p["meaningCos"],
             "roleCos": p["roleCos"], "structuralGap": p["structuralGap"],
             "sharedMeaning": p["sharedMeaning"],
             "target": p["target"]["name"], "targetArea": p["target"]["area"],
             "targetSeed": p["target"]["seed"],
             "donor": p["donor"]["name"], "donorArea": p["donor"]["area"]}
            for p in pair_rows[:40]],
    }
    with open(OUT_SUM, "wb") as o:
        o.write(json.dumps(summary, ensure_ascii=False, indent=2).encode("utf-8"))
    log("targets with a mature donor: "
        f"{covered}/{len(targets)} ({summary['targetCoverage']})")
    log("famous-seed coverage: " + json.dumps(
        {s: (seed_coverage[s]["namedTargets"],
             seed_coverage[s]["withMatureDonor"]) for s in SEED_LABELS}))
    log("top transfer candidates:")
    for p in summary["topTransferCandidates"][:12]:
        log(f"  {p['sim']:.3f} [{p['targetArea']}->{p['donorArea']}] "
            f"{p['target']}  ~  {p['donor']}")
    log("done.")


if __name__ == "__main__":
    main()
