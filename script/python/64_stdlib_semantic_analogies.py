#!/usr/bin/env python3
"""64_stdlib_semantic_analogies.py — SEMANTIC-FIRST, two-channel analogy scan
over the whole MATURE Mathlib standard library, hunting a second
PointwiseLift-class missing abstraction.

Why two channels
----------------
The user's standing directive: genuinely undiscovered structure is structurally
INCOMPLETE, so structural/AST matching under-recalls interesting cases and
SEMANTIC signal (mathematical meaning vocabulary + abstract role) must lead.
But the one confirmed missing-abstraction result of the project, PointwiseLift
(Set.image2 ~ Filter.map2), has NO shared name vocabulary at all -- "image" vs
"map", "set" vs "filter" -- while its TYPE skeletons are byte-for-byte the same
shape (nPi=6, typeNodes=23, typeDepth=8, zero typeclass constraints). A purely
semantic blocker literally cannot see it. The scan therefore runs two channels
and unions their evidence:

  SEMANTIC channel (leads):
    meaning TF-IDF (name + conclusion head + value head) + abstract role
    (kind / predicate-role P / value-role V); blocked by shared DISTINCTIVE
    meaning words; cross-area and cross-namespace only; same rare-stem families
    dropped. This is where incomplete/undiscovered structure shows up.
  STRUCTURAL channel (reranks / corroborates):
    block on an EXACT coarse TYPE-shape signature (kind, P, V, pi/constraint/
    type-node/type-depth buckets, constraint-area multiset), then keep cross
    area/namespace pairs with high structCos (full type+value shape) and high
    roleCos. PointwiseLift is the positive control for this channel.

Pairs from either channel feed one union-find; a candidate abstraction cluster
must repeat across >=2 areas AND >=2 namespace roots. to_additive twins
(e.g. OreLocalization / AddOreLocalization) are tagged, not celebrated: Mathlib
already generates them. Oversized components are flagged diffuse.

Method (pure stdlib, deterministic). Three sparse vectors per eligible
theorem/definition/opaque in a CORE area:
  meaning : concept words from name + conclusion head + value head
  role    : kind, conclusion predicate-role P, proof/value role V
  struct  : constraint-AREA profile R, coarse shape buckets (pi/constraints/
            type nodes-depth / value nodes-depth), proof-strategy flags
sublinear-TF / smooth-IDF, L2 normalized.

Inputs : data/atlas_features.jsonl, data/atlas_type_skeletons.jsonl,
         data/atlas_classes.jsonl, data/area_maturity_profile.jsonl
Outputs: data/stdlib_semantic_pairs.jsonl
         data/stdlib_semantic_clusters.jsonl
         data/stdlib_semantic_summary.json
"""
import json, math, collections, os, re, time, heapq

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
DATA = os.path.join(ROOT, "data")
FEAT = os.path.join(DATA, "atlas_features.jsonl")
SKEL = os.path.join(DATA, "atlas_type_skeletons.jsonl")
CLS = os.path.join(DATA, "atlas_classes.jsonl")
MAT = os.path.join(DATA, "area_maturity_profile.jsonl")
OUT_PAIRS = os.path.join(DATA, "stdlib_semantic_pairs.jsonl")
OUT_CLUST = os.path.join(DATA, "stdlib_semantic_clusters.jsonl")
OUT_SUM = os.path.join(DATA, "stdlib_semantic_summary.json")

INCLUDE_KINDS = {"theorem", "definition", "opaque"}
GEN_SUFFIX = ("hcongr",)
TF_CAP = 4
MEANING_W = 0.70
ROLE_W = 0.30
MIN_SHARED_MEANING = 2
MEANING_COS_FLOOR = float(os.environ.get("ATLAS_SS_MEANING_FLOOR", "0.32"))
SIM_FLOOR = float(os.environ.get("ATLAS_SS_SIM_FLOOR", "0.45"))
TOPK = 12
# semantic candidate generation band
ANCHOR_CAP = int(os.environ.get("ATLAS_SS_ANCHOR_CAP", "600"))
MIN_ANCHOR_DF = 2
K_RAREST = int(os.environ.get("ATLAS_SS_K_RAREST", "3"))
SAME_CONCEPT_DF = int(os.environ.get("ATLAS_SS_SAME_CONCEPT_DF", "50"))
# a missing abstraction manifests across distinct namespace roots
NAMESPACE_GUARD = os.environ.get("ATLAS_SS_NS_GUARD", "1") == "1"
# structural channel
STRUCT_EDGE = float(os.environ.get("ATLAS_SS_STRUCT_EDGE", "0.80"))
STRUCT_ROLE = float(os.environ.get("ATLAS_SS_STRUCT_ROLE", "0.85"))
STRUCT_GROUP_CAP = int(os.environ.get("ATLAS_SS_STRUCT_GROUP_CAP", "800"))
# tiny signatures (e.g. `def f : α → β`) collide coincidentally; a genuine
# pointwise-lift abstraction has a moderately complex polyadic type
STRUCT_MIN_PI = int(os.environ.get("ATLAS_SS_STRUCT_MIN_PI", "4"))
STRUCT_MIN_TYPENODES = int(os.environ.get("ATLAS_SS_STRUCT_MIN_TN", "15"))
# clustering
CLUSTER_SIM = float(os.environ.get("ATLAS_SS_CLUSTER_SIM", "0.55"))
CLUSTER_STRUCT = float(os.environ.get("ATLAS_SS_CLUSTER_STRUCT", "0.50"))
CLUSTER_MIN_MEMBERS = 3
DIFFUSE = 90
MAX_PAIR_LINES = 100_000

BOILERPLATE_SUBSTR = ("term_", "«term", "ctoridx", "ctor_idx", ".quot",
                      "notation", "match_", "_match", "anonymous", "raw_",
                      "delab", "parser_", "_parser", "macro_", ".macro",
                      "_aux_", "macrorules", "«_")

# PointwiseLift positive control (note Filter's subscript is Unicode ₂)
POSITIVE_CONTROL_STEMS = ("Set.image2", "Filter.map₂")


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
    # auto-generated structure congruence lemmas
    if tail.endswith("congr_simp"):
        return False
    # syntax / notation machinery: Foo.stx, termε, bigOpBinder-style decls
    if tail.endswith("Stx"):
        return False
    if tail == "term" or (tail.startswith("term") and len(tail) > 4
                          and not ("a" <= tail[4] <= "z")):
        return False
    low = name.lower()
    if any(b in low for b in BOILERPLATE_SUBSTR):
        return False
    return True


def additive_twin(ns_a, ns_b):
    """to_additive pairs: one namespace root is the Add-prefixed twin of the
    other, or the names differ only by an Add/Mul swap."""
    a, b = ns_a, ns_b
    if a == "Add" + b or b == "Add" + a:
        return True
    swaps = {("Add" + x[3:], x) for x in (a, b) if x.startswith("Mul")}
    if swaps & {(a, b), (b, a)}:
        return True
    return False


class Intern:
    def __init__(self):
        self.id_of = {}
        self.of_id = []

    def get(self, tok):
        i = self.id_of.get(tok)
        if i is None:
            i = len(self.of_id)
            self.id_of[tok] = i
            self.of_id.append(tok)
        return i


def main():
    bucket_of_area = {}
    with open(MAT, "rb") as f:
        for line in f:
            r = json.loads(line)
            bucket_of_area[r["area"]] = r["bucket"]
    core_areas = {a for a, b in bucket_of_area.items() if b == "core"}
    log(f"core areas ({len(core_areas)}): " + ", ".join(sorted(core_areas)))

    class_area, class_names = {}, set()
    with open(CLS, "rb") as f:
        for line in f:
            r = json.loads(line)
            class_names.add(r["name"])
            class_area[r["name"]] = area_of(r["module"])

    skel_cons = {}
    with open(SKEL, "rb") as f:
        for line in f:
            r = json.loads(line)
            skel_cons[r["name"]] = [c["class"] for c in r.get("constraints", [])]
    log(f"skeletons loaded: {len(skel_cons):,}")

    tok = Intern()
    wtok = Intern()

    names, areas, modules = [], [], []
    chs, vhs, kinds, nspaces = [], [], [], []
    proles, vroles = [], []
    mraw, rraw, sraw = [], [], []
    wids = []
    type_keys = []           # structural blocking signature

    df_m = collections.Counter()
    df_r = collections.Counter()
    df_s = collections.Counter()
    df_w = collections.Counter()
    n_scanned = 0
    LIMIT = int(os.environ.get("ATLAS_LIMIT", "0"))
    with open(FEAT, "rb") as f:
        for line in f:
            r = json.loads(line)
            n_scanned += 1
            if LIMIT and n_scanned > LIMIT:
                break
            if not eligible(r):
                continue
            area = area_of(r["module"])
            if area not in core_areas:
                continue
            name = r["name"]
            ch = r.get("conclusionHead") or ""
            vh = r.get("valueHead") or ""
            prole = pred_role(ch, class_names)
            vrole = vh_role(vh, r.get("hasValue"), r.get("valueTruncated"))

            mc = collections.Counter()
            for w in concept_words(name):
                mc[("w", w)] += 1
            for w in concept_words(ch):
                mc[("w", w)] += 1
            if vh and r.get("hasValue") and not r.get("valueTruncated"):
                for w in concept_words(vh):
                    mc[("w", w)] += 1

            rc = collections.Counter()
            rc[("k", r["kind"])] += 1
            rc[("P", prole)] += 1
            rc[("V", vrole)] += 1

            sc = collections.Counter()
            cons_classes = skel_cons.get(name, [])
            cons_areas = []
            for c in cons_classes:
                a = class_area.get(c)
                if a:
                    sc[("R", a)] += 1
                    cons_areas.append(a)
            pi_b, nc_b = bucket(r["nPi"]), bucket(len(cons_classes))
            tn_b, td_b = bucket(r["typeNodes"]), bucket(r["typeDepth"])
            vn_b, vd_b = bucket(r["valueNodes"]), bucket(r["valueDepth"])
            sc[("s", ("pi", pi_b))] += 1
            sc[("s", ("nc", nc_b))] += 1
            sc[("s", ("tn", tn_b))] += 1
            sc[("s", ("td", td_b))] += 1
            sc[("s", ("vn", vn_b))] += 1
            sc[("s", ("vd", vd_b))] += 1
            if r.get("valueIsRfl"):
                sc[("S", "rfl")] += 1
            if (r.get("caseRefs") or 0) > 0:
                sc[("S", "uses-cases")] += 1
            if (r.get("recRefs") or 0) > 0:
                sc[("S", "uses-rec")] += 1

            mc = {t: min(TF_CAP, c) for t, c in mc.items()}
            rc = {t: min(TF_CAP, c) for t, c in rc.items()}
            sc = {t: min(TF_CAP, c) for t, c in sc.items()}

            names.append(name)
            areas.append(area)
            modules.append(r["module"])
            chs.append(ch)
            vhs.append(vh)
            kinds.append(r["kind"])
            nspaces.append(r.get("namespace") or name.split(".")[0])
            proles.append(prole)
            vroles.append(vrole)

            md, rd, sd = {}, {}, {}
            node_words = []
            for t, c in mc.items():
                ti = tok.get(("M", t))
                md[ti] = c
                df_m[ti] += 1
                if t[0] == "w":
                    wi = wtok.get(t[1])
                    node_words.append(wi)
                    df_w[wi] += 1
            for t, c in rc.items():
                ti = tok.get(("R", t))
                rd[ti] = c
                df_r[ti] += 1
            for t, c in sc.items():
                ti = tok.get(("S", t))
                sd[ti] = c
                df_s[ti] += 1
            mraw.append(md)
            rraw.append(rd)
            sraw.append(sd)
            wids.append(sorted(set(node_words)))
            # EXACT type-shape blocking signature: PointwiseLift matches
            # Set.image2 / Filter.map2 on every one of these fields.
            type_keys.append((
                r["kind"], prole, vrole,
                r["nPi"], r["nImplicit"], r["nDefault"], r["nInstImplicit"],
                r["typeNodes"], r["typeDepth"], r["typeConsts"],
                tuple(sorted(cons_classes))))
    N = len(names)
    log(f"scanned {n_scanned:,}; eligible core nodes N={N:,}")

    def idf_table(df):
        return {t: math.log((N + 1.0) / (c + 1.0)) + 1.0 for t, c in df.items()}

    idf_m, idf_r, idf_s = idf_table(df_m), idf_table(df_r), idf_table(df_s)

    def normalize(raw, idf):
        w, s = {}, 0.0
        for t, tf in raw.items():
            v = (1.0 + math.log(tf)) * idf.get(t, 1.0)
            w[t] = v
            s += v * v
        n = math.sqrt(s)
        return ({t: v / n for t, v in w.items()} if n else {})

    mvec, rvec, svec = [], [], []
    for i in range(N):
        mvec.append(normalize(mraw[i], idf_m))
        rvec.append(normalize(rraw[i], idf_r))
        svec.append(normalize(sraw[i], idf_s))
    mraw = rraw = sraw = None
    idf_m = idf_r = idf_s = None

    def cosine(va, vb):
        if len(va) > len(vb):
            va, vb = vb, va
        return sum(v * vb.get(t, 0.0) for t, v in va.items())

    # edges: i*N+j (i<j) -> (score, channel); heaps per node
    edges = {}
    heaps = collections.defaultdict(list)

    def record_pair(i, j, mcos, rcos, scos, shared, channel):
        """register a pair from one channel; keep the strongest channel."""
        if channel == "semantic":
            score = MEANING_W * mcos + ROLE_W * rcos
        else:
            score = 0.5 * rcos + 0.5 * scos
        key = i * N + j
        prev = edges.get(key)
        if prev is not None and prev[0] >= score:
            return
        edges[key] = (score, channel, scos)
        item = (round(score, 6), i, j, round(mcos, 6), round(rcos, 6),
                round(scos, 6), shared[:12], channel)
        for hx in (i, j):
            h = heaps[hx]
            if len(h) < TOPK:
                heapq.heappush(h, item)
            elif item[0] > h[0][0]:
                heapq.heapreplace(h, item)

    # ============ SEMANTIC CHANNEL ============
    anchor_df = {}
    for wi, df in df_w.items():
        word = wtok.of_id[wi]
        if MIN_ANCHOR_DF <= df <= ANCHOR_CAP and word not in GLUE_WORDS:
            anchor_df[wi] = df
    postings = collections.defaultdict(list)
    anch = []
    for i in range(N):
        ai = sorted(wi for wi in wids[i] if wi in anchor_df)
        anch.append(ai)
        for wi in ai:
            postings[wi].append(i)
    log(f"[semantic] anchor words {len(anchor_df):,}")

    rarest_order = []
    for i in range(N):
        ai = sorted((anchor_df[wi], wi) for wi in anch[i])
        rarest_order.append([wi for _, wi in ai[:K_RAREST]])

    sem_visits = sem_2 = sem_samefam = sem_samens = sem_floor = sem_kept = 0
    for i in range(N):
        ai = anch[i]
        if not ai:
            continue
        cand = []
        for wi in rarest_order[i]:
            for j in postings[wi]:
                if j <= i or areas[j] == areas[i]:
                    continue
                if NAMESPACE_GUARD and nspaces[j] == nspaces[i]:
                    sem_samens += 1
                    continue
                cand.append(j)
        if not cand:
            continue
        ai_set = set(ai)
        for j in set(cand):
            sem_visits += 1
            shared_ids = ai_set.intersection(anch[j])
            if len(shared_ids) < MIN_SHARED_MEANING:
                continue
            sem_2 += 1
            mindf = min(anchor_df[wi] for wi in shared_ids)
            if mindf < SAME_CONCEPT_DF:
                sem_samefam += 1
                continue
            mcos = cosine(mvec[i], mvec[j])
            if mcos < MEANING_COS_FLOOR:
                continue
            rcos = cosine(rvec[i], rvec[j])
            sim = MEANING_W * mcos + ROLE_W * rcos
            if sim < SIM_FLOOR:
                sem_floor += 1
                continue
            scos = cosine(svec[i], svec[j])
            sem_kept += 1
            shared = sorted(wtok.of_id[wi] for wi in shared_ids)
            record_pair(i, j, mcos, rcos, scos, shared, "semantic")
    log(f"[semantic] visits {sem_visits:,}; >=2 anchors {sem_2:,}; "
        f"same-family dropped {sem_samefam:,}; same-ns dropped {sem_samens:,}; "
        f"below floor {sem_floor:,}; kept {sem_kept:,}")

    # ============ STRUCTURAL CHANNEL ============
    groups = collections.defaultdict(list)
    for i, key in enumerate(type_keys):
        groups[key].append(i)
    st_pairs = st_kept = st_role = st_twin = st_simple = 0
    n_overflow_groups = 0
    n_overflow_members = 0
    for key, mem in groups.items():
        if key[3] < STRUCT_MIN_PI or key[7] < STRUCT_MIN_TYPENODES:
            st_simple += 1
            continue
        if len(mem) > STRUCT_GROUP_CAP:
            n_overflow_groups += 1
            n_overflow_members += len(mem)
            continue
        for ai_ in range(len(mem)):
            i = mem[ai_]
            ai_set = set(anch[i])
            for bi_ in range(ai_ + 1, len(mem)):
                j = mem[bi_]
                if areas[j] == areas[i]:
                    continue
                if NAMESPACE_GUARD and nspaces[j] == nspaces[i]:
                    continue
                st_pairs += 1
                rcos = cosine(rvec[i], rvec[j])
                if rcos < STRUCT_ROLE:
                    st_role += 1
                    continue
                scos = cosine(svec[i], svec[j])
                if scos < STRUCT_EDGE:
                    continue
                # same rare meaning stem => same concrete concept family
                shared_ids = ai_set.intersection(anch[j])
                if shared_ids and min(anchor_df[wi] for wi in
                                      shared_ids) < SAME_CONCEPT_DF:
                    sem_samefam += 1
                    continue
                twin = additive_twin(nspaces[i], nspaces[j])
                if twin:
                    st_twin += 1
                mcos = cosine(mvec[i], mvec[j])
                shared = sorted(wtok.of_id[wi] for wi in shared_ids)
                st_kept += 1
                record_pair(i, j, mcos, rcos, scos, shared,
                            "structural-twin" if twin else "structural")
    log(f"[structural] groups {len(groups):,} (simple skipped {st_simple:,}); "
        f"pair tests {st_pairs:,}; kept {st_kept:,} "
        f"(to_additive twins {st_twin:,}); role-rejected {st_role:,}; "
        f"overflow groups {n_overflow_groups:,} ({n_overflow_members:,} members)")

    # restrict edges to the cluster-eligible ones and union-find -----------
    edge_list = []
    struct_edge_score = 0.5 * STRUCT_ROLE + 0.5 * STRUCT_EDGE
    for ekey, (score, ch, scos) in edges.items():
        if ch == "semantic":
            # semantic cluster edges must also show some shape corroboration
            ok = score >= CLUSTER_SIM and scos >= CLUSTER_STRUCT
        else:
            ok = score >= struct_edge_score
        if ok:
            edge_list.append((ekey // N, ekey % N, score, ch))
    log(f"union-find edges {len(edge_list):,} "
        f"(semantic {sum(1 for e in edge_list if e[3]=='semantic')}, "
        f"structural {sum(1 for e in edge_list if e[3].startswith('struct'))})")

    parent = list(range(N))

    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x

    for i, j, _, _ in edge_list:
        ra, rb = find(i), find(j)
        if ra != rb:
            parent[rb] = ra

    comp = collections.defaultdict(list)
    for i, j, _, _ in edge_list:
        r = find(i)
        comp[r].append(i)
        comp[r].append(j)
    clusters = []
    for root, mem in comp.items():
        mem = sorted(set(mem))
        if len(mem) < CLUSTER_MIN_MEMBERS:
            continue
        mem_areas = {areas[m] for m in mem}
        if len(mem_areas) < 2:
            continue
        mem_ns = {nspaces[m] for m in mem}
        if len(mem_ns) < 2:
            continue
        mem_heads = {chs[m] for m in mem if chs[m]}
        es = [(i, j, s, c) for i, j, s, c in edge_list if find(i) == root]
        mean_score = sum(e[2] for e in es) / len(es)
        ch_count = collections.Counter(e[3] for e in es)
        twins = sum(1 for e in es if e[3] == "structural-twin")
        wcount = collections.Counter()
        for m in mem:
            for wi in set(anch[m]):
                wcount[wtok.of_id[wi]] += 1
        signature = [w for w, c in wcount.most_common(12)
                     if c >= max(2, int(0.5 * len(mem)))]
        clusters.append({
            "members": len(mem), "areas": sorted(mem_areas),
            "nAreas": len(mem_areas), "nHeads": len(mem_heads),
            "nNamespaces": len(mem_ns), "meanScore": round(mean_score, 4),
            "semanticEdges": ch_count.get("semantic", 0),
            "structuralEdges": ch_count.get("structural", 0),
            "twinEdges": twins,
            "diffuse": len(mem) > DIFFUSE,
            "signatureWords": signature,
            "representatives": sorted(
                ({"name": names[m], "area": areas[m], "module": modules[m],
                  "namespace": nspaces[m], "kind": kinds[m],
                  "conclusionHead": chs[m], "valueHead": vhs[m]}
                 for m in mem),
                key=lambda z: (z["area"], z["name"]))[:40],
        })
    clusters.sort(key=lambda c: (c["diffuse"], -c["meanScore"],
                                 -c["nAreas"], -c["members"]))
    log(f"candidate clusters: {len(clusters)} "
        f"(diffuse {sum(1 for c in clusters if c['diffuse'])})")

    # ---- positive control: PointwiseLift ----------------------------------
    def find_node(stem):
        return [i for i, nm in enumerate(names) if stem in nm]

    pc_nodes = sorted({i for stem in POSITIVE_CONTROL_STEMS
                       for i in find_node(stem)})
    pc = {"nodes": [names[i] for i in pc_nodes], "components": {},
          "pairScores": []}
    if pc_nodes:
        roots = {}
        for i in pc_nodes:
            roots.setdefault(find(i), []).append(i)
        pc["components"] = {r: sorted(names[i] for i in mem)
                            for r, mem in roots.items()}
        for a in range(len(pc_nodes)):
            for b in range(a + 1, len(pc_nodes)):
                i, j = pc_nodes[a], pc_nodes[b]
                if areas[i] == areas[j]:
                    continue
                mcos = cosine(mvec[i], mvec[j])
                rcos = cosine(rvec[i], rvec[j])
                scos = cosine(svec[i], svec[j])
                mix = MEANING_W * mcos + ROLE_W * rcos
                struct_score = 0.5 * rcos + 0.5 * scos
                pc["pairScores"].append({
                    "a": names[i], "b": names[j],
                    "semanticMix": round(mix, 4),
                    "meaningCos": round(mcos, 4), "roleCos": round(rcos, 4),
                    "structCos": round(scos, 4),
                    "structScore": round(struct_score, 4),
                    "sameComponent": find(i) == find(j)})
        pc["pairScores"].sort(key=lambda z: -z["structScore"])
    log("positive control nodes: " + json.dumps(pc["nodes"][:12],
                                                ensure_ascii=False))

    # ---- emit pairs -------------------------------------------------------
    seen_pairs = set()
    pair_rows = []
    for h in heaps.values():
        for score, a, b, mcos, rcos, scos, shared, channel in h:
            key = (a, b) if a < b else (b, a)
            if key in seen_pairs:
                continue
            seen_pairs.add(key)
            x, y = key
            mix = MEANING_W * mcos + ROLE_W * rcos
            twin = additive_twin(nspaces[x], nspaces[y])
            pair_rows.append({
                "score": score, "channel": channel, "additiveTwin": twin,
                "semanticMix": round(mix, 6), "meaningCos": mcos,
                "roleCos": rcos, "structCos": scos,
                "sharedMeaning": shared,
                "a": {"name": names[x], "area": areas[x],
                      "module": modules[x], "namespace": nspaces[x],
                      "kind": kinds[x], "conclusionHead": chs[x],
                      "valueHead": vhs[x], "predRole": proles[x],
                      "valueRole": vroles[x]},
                "b": {"name": names[y], "area": areas[y],
                      "module": modules[y], "namespace": nspaces[y],
                      "kind": kinds[y], "conclusionHead": chs[y],
                      "valueHead": vhs[y], "predRole": proles[y],
                      "valueRole": vroles[y]}})
    pair_rows.sort(key=lambda z: -z["score"])
    with open(OUT_PAIRS, "wb") as o:
        for row in pair_rows[:MAX_PAIR_LINES]:
            o.write((json.dumps(row, ensure_ascii=False) + "\n").encode("utf-8"))
    with open(OUT_CLUST, "wb") as o:
        for row in clusters:
            o.write((json.dumps(row, ensure_ascii=False) + "\n").encode("utf-8"))

    summary = {
        "params": {"meaningWeight": MEANING_W, "roleWeight": ROLE_W,
                   "minSharedMeaning": MIN_SHARED_MEANING,
                   "meaningCosFloor": MEANING_COS_FLOOR, "simFloor": SIM_FLOOR,
                   "anchorCap": ANCHOR_CAP, "kRarest": K_RAREST,
                   "sameConceptDf": SAME_CONCEPT_DF,
                   "namespaceGuard": NAMESPACE_GUARD,
                   "structEdge": STRUCT_EDGE, "structRole": STRUCT_ROLE,
                   "structGroupCap": STRUCT_GROUP_CAP,
                   "structMinPi": STRUCT_MIN_PI,
                   "structMinTypeNodes": STRUCT_MIN_TYPENODES,
                   "clusterSim": CLUSTER_SIM, "clusterStruct": CLUSTER_STRUCT,
                   "clusterMinMembers": CLUSTER_MIN_MEMBERS,
                   "diffuseThreshold": DIFFUSE},
        "scanned": n_scanned, "eligibleCoreNodes": N,
        "coreAreas": sorted(core_areas),
        "semantic": {"anchorWords": len(anchor_df), "visits": sem_visits,
                     "twoPlusAnchors": sem_2, "sameFamilyDropped": sem_samefam,
                     "sameNamespaceDropped": sem_samens,
                     "belowFloor": sem_floor, "kept": sem_kept},
        "structural": {"groups": len(groups), "simpleGroupsSkipped": st_simple,
                       "pairTests": st_pairs, "kept": st_kept,
                       "additiveTwins": st_twin, "roleRejected": st_role,
                       "overflowGroups": n_overflow_groups,
                       "overflowMembers": n_overflow_members},
        "clusterEdges": len(edge_list),
        "clusters": len(clusters),
        "nondiffuseClusters": sum(1 for c in clusters if not c["diffuse"]),
        "emittedPairs": min(len(pair_rows), MAX_PAIR_LINES),
        "positiveControl": pc,
        "topClusters": [
            {"members": c["members"], "nAreas": c["nAreas"],
             "areas": c["areas"], "meanScore": c["meanScore"],
             "semanticEdges": c["semanticEdges"],
             "structuralEdges": c["structuralEdges"],
             "twinEdges": c["twinEdges"], "diffuse": c["diffuse"],
             "signatureWords": c["signatureWords"],
             "examples": [r["name"] for r in c["representatives"][:8]]}
            for c in clusters[:25]],
        "topPairs": [
            {"score": p["score"], "channel": p["channel"],
             "additiveTwin": p["additiveTwin"],
             "meaningCos": p["meaningCos"], "roleCos": p["roleCos"],
             "structCos": p["structCos"], "sharedMeaning": p["sharedMeaning"],
             "a": p["a"]["name"], "aArea": p["a"]["area"],
             "b": p["b"]["name"], "bArea": p["b"]["area"]}
            for p in pair_rows[:40]],
    }
    with open(OUT_SUM, "wb") as o:
        o.write(json.dumps(summary, ensure_ascii=False, indent=2).encode("utf-8"))
    log(f"pairs emitted {min(len(pair_rows), MAX_PAIR_LINES):,}; "
        f"clusters {len(clusters)}")
    log("top clusters:")
    for c in clusters[:10]:
        log(f"  m={c['members']:3d} areas={c['nAreas']} score="
            f"{c['meanScore']:.3f} sem={c['semanticEdges']} "
            f"str={c['structuralEdges']} twin={c['twinEdges']} "
            f"sig={c['signatureWords'][:6]}")
    log("top pairs:")
    for p in pair_rows[:12]:
        log(f"  {p['score']:.3f} {p['channel'][:9]:9s} "
            f"(m={p['meaningCos']:.3f} r={p['roleCos']:.3f} "
            f"s={p['structCos']:.3f}) [{p['a']['area']}]{p['a']['name']}  ~  "
            f"[{p['b']['area']}]{p['b']['name']}")
    log("done.")


if __name__ == "__main__":
    main()
