#!/usr/bin/env python3
"""28_semantic_analogy.py — SEMANTIC (role-based) analogy track.

Motivation (design note): structural matching on the shared conclusion head H /
constraint class C / value head V (script 17) is biased toward abstractions that
ALREADY exist: if two declarations use the same generic constructor, they share
a head and look alike — but that is reuse, not discovery. A genuinely
undiscovered abstraction will have an INCOMPLETE structural signature: its
instances do the same mathematical JOB but currently have different concrete
heads and different proof bodies.

This script therefore strips structural IDENTITY and vectorizes only the
abstract ROLE each declaration plays:
  P  conclusion predicate-role (equality / iff / membership / order-comp /
     instance-goal / exists / ... ) — never which predicate;
  R  prerequisite-role profile: the AREAS of its type-class constraints
     (e.g. "needs one Algebra + one Order class"), not which classes;
  S  proof-strategy role: value-head kind (constructor / recursor / cases /
     rewrite / named lemma / rfl / none) + normalized value composition;
  s  binder / arity / type-size buckets.

We block candidates on a coarse role SIGNATURE (so the high-df role tokens still
generate pairs), score an exact TF-IDF cosine inside each block, and keep only
the STRUCTURALLY DIVERGENT pairs: cross-area, different concrete conclusion
head AND different value head. Those "same role, different surface" pairs are
the hidden-structure candidates the structural track systematically misses.

Pure stdlib, deterministic. Population/exclusions match script 17.

Inputs : data/atlas_features.jsonl, data/atlas_type_skeletons.jsonl,
         data/atlas_classes.jsonl
Outputs: data/semantic_hidden_candidates.jsonl
         data/semantic_role_shortlist.json
         data/semantic_summary.json
"""
import json, math, array, collections, os, time, re

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
DATA = os.path.join(ROOT, "data")
FEAT = os.path.join(DATA, "atlas_features.jsonl")
SKEL = os.path.join(DATA, "atlas_type_skeletons.jsonl")
CLS = os.path.join(DATA, "atlas_classes.jsonl")
_OUT_TAG = os.environ.get("ATLAS_OUT_TAG", "")  # suffix for alternate-threshold runs
OUT_CAND = os.path.join(DATA, "semantic_hidden_candidates" + _OUT_TAG + ".jsonl")
OUT_ROLE = os.path.join(DATA, "semantic_role_shortlist" + _OUT_TAG + ".json")
OUT_SUM = os.path.join(DATA, "semantic_summary" + _OUT_TAG + ".json")

INCLUDE_KINDS = {"theorem", "definition", "opaque"}
NONMATH_AREAS = {"Tactic", "Lean", "(root)"}
GEN_SUFFIX = ("hcongr",)
TF_CAP = 4
SEM_THRESH = float(os.environ.get("ATLAS_SEM_THRESH", "0.80"))  # cosine cutoff
MIN_SHARED_CONCEPTS = 2    # >= shared conclusion+value words total
MIN_SHARED_HEAD_WORDS = 1  # >= this many shared conclusion (result) words
MAX_BLOCK = 1500           # safety cap on a single role block
CAND_CAP = 40000           # emitted pairs
TOPK = 8


def log(m):
    print(f"[{time.strftime('%H:%M:%S')}] {m}", flush=True)


def bucket(x):
    if x <= 0:
        return 0
    return min(7, (x - 1).bit_length())


def area_of(module):
    p = module.split(".")
    return p[1] if len(p) >= 2 and p[0] == "Mathlib" else "(root)"


# ---- conclusion predicate-role (identity stripped) -------------------------
ORDER_ROOTS = {"LE", "LT", "GE", "GT", "Min", "Max", "Subset", "SubsetEq",
               "SSubset", "SSubsetEq", "IsLeast", "IsGreatest", "IsLUB",
               "IsGLB", "Directed", "CovBy", "WCovBy"}
LOGIC_ROLES = {
    "Eq": "equality", "Iff": "iff", "Not": "negation", "And": "and",
    "Or": "or", "Exists": "exists", "False": "false", "True": "true",
    "Membership.mem": "membership",
}


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


# ---- concept words: identity-free but meaning-bearing vocabulary ----------
_HUMP = re.compile(r"[A-Z]+(?=[A-Z][a-z])|[A-Z]?[a-z]+|[A-Z]+|\d+")
STOPWORDS = {
    "is", "of", "the", "a", "to", "le", "ge", "lt", "gt", "eq", "ne", "mk",
    "class", "inst", "self", "this", "h", "x", "y", "f", "g", "on", "for",
    "and", "or", "not", "iff", "def", "thm", "aux", "proof",
}


def concept_words(name):
    """Lowercase camelCase / dotted identifier -> concept word multiset.
    Strips structural identity but keeps mathematical vocabulary
    ('Measurable', 'Compact', 'Finite', 'Closure', 'Comm', 'Monoid')."""
    out = []
    for seg in (name or "").split("."):
        for w in _HUMP.findall(seg):
            wl = w.lower()
            if len(wl) >= 3 and wl not in STOPWORDS:
                out.append(wl)
    return out


def main():
    # class -> area (for prerequisite-role profile + instance-goal detection)
    class_area, class_names = {}, set()
    with open(CLS, "rb") as f:
        for line in f:
            r = json.loads(line)
            class_names.add(r["name"])
            class_area[r["name"]] = area_of(r["module"])
    log(f"classes: {len(class_names):,}")

    skel_cons = {}
    with open(SKEL, "rb") as f:
        for line in f:
            r = json.loads(line)
            skel_cons[r["name"]] = [c["class"] for c in r.get("constraints", [])]

    # ---- tokenize ----------------------------------------------------------
    term_id, term_str, df = {}, [], array.array("i")

    def tid(t):
        j = term_id.get(t)
        if j is None:
            j = len(term_str); term_id[t] = j; term_str.append(t); df.append(0)
        return j

    docs = []           # meta + sparse weighted vector (built after idf)
    raw_toks = []       # parallel list of {tid:tf}
    blocks = collections.defaultdict(list)   # role-sig + one shared head word
    role_members = collections.defaultdict(list)  # role-sig -> all docs
    N_scanned = N = 0
    LIMIT = int(os.environ.get("ATLAS_LIMIT", "0"))
    with open(FEAT, "rb") as f:
        for line in f:
            r = json.loads(line)
            N_scanned += 1
            if LIMIT and N_scanned > LIMIT:
                break
            if r["isGenerated"] or r["kind"] not in INCLUDE_KINDS:
                continue
            if r.get("isInstance") or r.get("isClass"):
                continue
            name, module = r["name"], r["module"]
            area = area_of(module)
            if area in NONMATH_AREAS or name.startswith("_private") or ".Meta." in module:
                continue
            if name.rsplit(".", 1)[-1].startswith(GEN_SUFFIX):
                continue
            # auto-generated inductive API (recursors/case analysis/noConfusion)
            # is boilerplate, not a mathematical statement to analogise
            tail = name.rsplit(".", 1)[-1]
            if (tail.endswith("casesOn") or tail.endswith("recOn") or
                    tail.endswith("brecOn") or tail in ("rec", "noConfusion",
                    "noConfusionType") or tail.endswith("inductionOn")):
                continue

            cons = skel_cons.get(name, [])
            ch = r.get("conclusionHead") or ""
            vh = r.get("valueHead") or ""
            prole = pred_role(ch, class_names)
            vrole = vh_role(vh, r.get("hasValue"), r.get("valueTruncated"))

            # prerequisite-role profile = AREAS of the constraint classes
            careas = []
            for c in cons:
                a = class_area.get(c)
                if a:
                    careas.append(a)
            carea_counter = collections.Counter(careas)

            toks = []
            def add(t, tf=1):
                toks.append((tid(t), tf))
            add(("k", r["kind"]))
            add(("P", prole))
            add(("V", vrole))
            for a, cnt in carea_counter.items():
                add(("R", a), cnt)                    # constraint-area role
            # concept-word vocabulary (identity-free meaning): words of the
            # conclusion head and of the proof value head
            for w in concept_words(ch):
                add(("w", w))
            # (prerequisite CLASS words are intentionally NOT vectorized: the
            # coarse constraint-AREA profile R captures the setting, while the
            # concrete class bundle would otherwise dominate the cosine.)
            if vh and r.get("hasValue") and not r.get("valueTruncated"):
                for w in concept_words(vh):
                    add(("vw", w))
            # binder / type shape
            add(("s", "pi", bucket(r["nPi"])))
            add(("s", "inst", bucket(r["nInstImplicit"])))
            add(("s", "imp", bucket(r["nImplicit"])))
            add(("s", "strict", bucket(r["nStrictImplicit"])))
            add(("s", "default", bucket(r["nDefault"])))
            add(("s", "nc", bucket(len(cons))))
            add(("s", "nca", bucket(len(carea_counter))))   # #distinct areas
            add(("s", "tn", bucket(r["typeNodes"])))
            add(("s", "td", bucket(r["typeDepth"])))
            add(("s", "tdist", bucket(r["typeDistinct"])))
            # value strategy / composition (finer identity-free shape)
            add(("s", "vn", bucket(r["valueNodes"])))
            add(("s", "vd", bucket(r["valueDepth"])))
            add(("s", "vdist", bucket(r["valueDistinct"])))
            add(("s", "vapps", bucket(r["valueApps"])))
            add(("s", "vforall", bucket(r["valueForalls"])))
            if r.get("valueIsRfl"):
                add(("S", "rfl"))
            if (r.get("caseRefs") or 0) > 0:
                add(("S", "uses-cases"))
            if (r.get("recRefs") or 0) > 0:
                add(("S", "uses-rec"))
            if (r.get("valueLams") or 0) > 0:
                add(("S", "uses-lam"))
            if (r.get("valueLets") or 0) > 0:
                add(("S", "uses-let"))

            agg = {}
            for j, tf in toks:
                agg[j] = min(TF_CAP, agg.get(j, 0) + tf)
            raw_toks.append(agg)
            for j in agg:
                df[j] += 1

            # role signature (identity-free; deliberately loose) plus a shared
            # conclusion-word ANCHOR: a declaration enters one block per result
            # word, so any co-blocked pair already shares result vocabulary and
            # no block is ever giant (inverted-index, not full cross product).
            role_sig = (r["kind"], prole, vrole,
                        bucket(r["nPi"]), bucket(r["typeDepth"]),
                        bucket(r["valueNodes"]))
            d = N
            docs.append({"name": name, "module": module, "area": area,
                         "kind": r["kind"],
                         "ch": ch, "vh": vh, "prole": prole, "vrole": vrole,
                         "careas": dict(carea_counter)})
            role_members[role_sig].append(d)
            head_words = set(concept_words(ch))
            if head_words:
                for w in head_words:
                    blocks[role_sig + (("w", w),)].append(d)
            N += 1
    log(f"scanned {N_scanned:,}; embedded {N:,}; vocab {len(term_str):,}; "
        f"blocks {len(blocks):,}")

    # idf + L2 weighted vectors
    idf = [math.log((N + 1.0) / (df[j] + 1.0)) + 1.0 for j in range(len(term_str))]

    def weights(agg):
        w = {}
        s = 0.0
        for j, tf in agg.items():
            v = (1.0 + math.log(tf)) * idf[j]
            w[j] = v
            s += v * v
        n = math.sqrt(s)
        return ({j: v / n for j, v in w.items()} if n else {}), n

    vec, norm = [None] * N, [0.0] * N
    for d, agg in enumerate(raw_toks):
        vec[d], norm[d] = weights(agg)
    del raw_toks

    def cosine(a, b):
        wa, wb = vec[a], vec[b]
        if len(wa) > len(wb):
            wa, wb = wb, wa
        return sum(v * wb[j] for j, v in wa.items() if j in wb)

    # ---- within-block role analogues --------------------------------------
    log("scoring role blocks ...")
    n_block_pairs = 0
    skipped_blocks = 0
    PER_BLOCK_CAP = 12        # keep only the closest divergent pairs per block
    cands = []
    seen_pair = {}            # (i,k) -> best (cos, shared_concepts)
    # per-role-signature spread statistics for the shortlist
    role_spread = {sig: (len(mem), len({docs[d]["area"] for d in mem}),
                       {docs[d]["area"] for d in mem})
                   for sig, mem in role_members.items()}
    for bkey, members in blocks.items():
        if len(members) > MAX_BLOCK:
            skipped_blocks += 1
            continue
        block_cands = []
        M = len(members)
        for a in range(M):
            i = members[a]
            for b in range(a + 1, M):
                k = members[b]
                n_block_pairs += 1
                if docs[i]["area"] == docs[k]["area"]:
                    continue
                # hidden-structure targets are mathematical THEOREMS with a
                # real conclusion (not field projections / no-conclusion defs)
                if docs[i]["kind"] != "theorem" or docs[k]["kind"] != "theorem":
                    continue
                if not docs[i]["ch"] or not docs[k]["ch"]:
                    continue
                # structural DIVERGENCE: different concrete head AND value head
                if docs[i]["ch"] == docs[k]["ch"] and docs[i]["ch"]:
                    continue
                if docs[i]["vh"] == docs[k]["vh"] and docs[i]["vh"]:
                    continue
                # co-blocked decls already share >=1 conclusion word (the
                # anchor); also count shared value words for the total gate.
                sw = sum(1 for j in vec[i]
                         if j in vec[k] and term_str[j][0] == "w")
                svw = sum(1 for j in vec[i]
                          if j in vec[k] and term_str[j][0] == "vw")
                if sw < MIN_SHARED_HEAD_WORDS or sw + svw < MIN_SHARED_CONCEPTS:
                    continue
                c = cosine(i, k)
                if c >= SEM_THRESH:
                    block_cands.append((c, i, k, sw + svw))
        block_cands.sort(key=lambda z: -z[0])
        for c, i, k, nc in block_cands[:PER_BLOCK_CAP]:
            key = (i, k)
            prev = seen_pair.get(key)
            if prev is None or c > prev[0]:
                seen_pair[key] = (c, nc)
    cands = [(c, i, k, nc) for (i, k), (c, nc) in seen_pair.items()]
    log(f"block pairs {n_block_pairs:,}; skipped oversized blocks "
        f"{skipped_blocks}; divergent cross-area candidates {len(cands):,}")

    cands.sort(key=lambda z: -z[0])
    cands = cands[:CAND_CAP]

    # top-K per doc
    best = {}
    for c, i, k, nc in cands:
        for d, o in ((i, k), (k, i)):
            cur = best.get(d)
            if cur is None:
                best[d] = [(c, o)]
            elif len(cur) < TOPK:
                cur.append((c, o))

    with open(OUT_CAND, "wb") as o:
        for c, i, k, nc in cands:
            di, dk = docs[i], docs[k]
            shared = sorted(term_str[j] for j in vec[i] if j in vec[k])
            o.write((json.dumps({
                "cosine": round(c, 6),
                "sharedConcepts": nc,
                "a": {"name": di["name"], "area": di["area"],
                      "conclusionHead": di["ch"], "valueHead": di["vh"]},
                "b": {"name": dk["name"], "area": dk["area"],
                      "conclusionHead": dk["ch"], "valueHead": dk["vh"]},
                "predRole": di["prole"], "valueRole": di["vrole"],
                "constraintAreas": di["careas"],
                "sharedRoleTokens": [":".join(map(str, t)) for t in shared][:12],
            }, ensure_ascii=False) + "\n").encode("utf-8"))

    # role shortlist: signatures spanning many areas with many members and
    # structurally divergent members = richest hidden-abstraction hunting grounds
    shortlist = []
    for bkey, (sz, na, areas) in role_spread.items():
        if na < 3 or sz < 6:
            continue
        kind, prole, vrole = bkey[0], bkey[1], bkey[2]
        shortlist.append({
            "kind": kind, "predRole": prole, "valueRole": vrole,
            "members": sz, "nAreas": na, "areas": sorted(areas),
        })
    shortlist.sort(key=lambda r: (-r["nAreas"], -r["members"]))
    with open(OUT_ROLE, "w", encoding="utf-8") as o:
        json.dump(shortlist, o, ensure_ascii=False, indent=2)

    # how many candidates per predicate role
    cand_prole = collections.Counter(docs[i]["prole"] for _, i, _, _ in cands)
    area_pair = collections.Counter(
        tuple(sorted((docs[i]["area"], docs[k]["area"])))
        for _, i, k, _ in cands)
    summary = {
        "params": {"semThresh": SEM_THRESH, "maxBlock": MAX_BLOCK,
                   "minSharedConcepts": MIN_SHARED_CONCEPTS,
                   "minSharedHeadWords": MIN_SHARED_HEAD_WORDS,
                   "candCap": CAND_CAP, "tfCap": TF_CAP},
        "scanned": N_scanned, "embedded": N, "vocab": len(term_str),
        "roleBlocks": len(blocks), "blockPairs": n_block_pairs,
        "skippedOversizedBlocks": skipped_blocks,
        "hiddenCandidates": len(cands),
        "docsWithHiddenNeighbor": len(best),
        "candidatesByPredRole": dict(cand_prole),
        "roleShortlistEntries": len(shortlist),
        "topAreaPairs": [{"areas": list(a), "count": c}
                         for a, c in area_pair.most_common(25)],
    }
    with open(OUT_SUM, "wb") as o:
        o.write(json.dumps(summary, ensure_ascii=False, indent=2).encode("utf-8"))
    log("summary: " + json.dumps(
        {k: v for k, v in summary.items()
         if k not in ("topAreaPairs", "params", "candidatesByPredRole")}))
    log("top role shortlist:")
    for r in shortlist[:12]:
        log(f"  {r['predRole']:<16} {r['valueRole']:<14} "
            f"areas={r['nAreas']:>2} members={r['members']:>4}")
    log("done.")


if __name__ == "__main__":
    main()
