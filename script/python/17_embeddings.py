#!/usr/bin/env python3
"""17_embeddings.py — fuzzy (embedding) similarity over type skeletons + features.

Script 15-B finds *exact* discrete-signature twins. This script adds a soft,
deterministic, dependency-free TF-IDF embedding so that near-miss analogies
(one or two type-class / binder / size differences) are also recovered, with
special attention to cross-area analogies the exact method cannot group.

Design constraints honoured:
  * pure Python (numpy is not installed in this environment);
  * deterministic (no randomized hashing; outputs sorted);
  * domain-agnostic vectors: module / namespace / name are NEVER vector tokens
    (they are metadata only), so two declarations from different areas can be
    nearest neighbours;
  * human-authored theorem/definition/opaque declarations only (generated
    declarations excluded, matching script 15);
  * scalable: CSR-compact vectors + inverted-index candidate generation over
    "strong" terms (full conclusion head / constraint class / value head), an
    idf upper-bound prune, then one exact cosine over the full vector.

Inputs : data/atlas_features.jsonl (script 13), data/atlas_type_skeletons.jsonl (09)
Outputs: data/embedding_nearest_neighbors.jsonl
         data/embedding_cross_area_analogies.jsonl
         data/embedding_summary.json
"""
import json, math, array, collections, os, time

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
DATA = os.path.join(ROOT, "data")
FEAT = os.path.join(DATA, "atlas_features.jsonl")
SKEL = os.path.join(DATA, "atlas_type_skeletons.jsonl")
OUT_NN = os.path.join(DATA, "embedding_nearest_neighbors.jsonl")
OUT_X = os.path.join(DATA, "embedding_cross_area_analogies.jsonl")
OUT_SUM = os.path.join(DATA, "embedding_summary.json")

# ---- parameters (fixed; documented in the design note) ---------------------
INCLUDE_KINDS = {"theorem", "definition", "opaque"}
# metaprogramming / infra areas are not mathematical discovery targets
NONMATH_AREAS = {"Tactic", "Lean", "(root)"}
GEN_SUFFIX = ("hcongr",)  # auto congruence lemmas <name>.hcongr_N
GEN_CAP_DF = 80        # a strong term generates pairs only if 2 <= df <= this
COS_THRESH = 0.70      # keep a pair only if exact cosine >= this
TOPK = 8               # nearest neighbours retained per declaration
XCROSS_CAP = 40000     # cap on emitted cross-area pair file
TF_CAP = 4

def bucket(x):
    """0,1,2-3,4-7,... log2 bucket so comparable-size declarations match."""
    if x <= 0:
        return 0
    return min(7, (x - 1).bit_length())

def area_of(module):
    p = module.split(".")
    return p[1] if len(p) >= 2 and p[0] == "Mathlib" else "(root)"

def log(m):
    print(f"[{time.strftime('%H:%M:%S')}] {m}", flush=True)

# ---------------------------------------------------------------------------
# Pass 0: constraints from type skeletons
# ---------------------------------------------------------------------------
log("reading type skeletons (constraints) ...")
skel_constraints = {}
with open(SKEL, "rb") as f:
    for line in f:
        r = json.loads(line)
        cs = tuple(sorted(c["class"] for c in r.get("constraints", [])))
        skel_constraints[r["name"]] = cs
log(f"  skeletons: {len(skel_constraints):,}")

# ---------------------------------------------------------------------------
# Pass 1: tokenize, build vocabulary / df / CSR vectors / metadata
# ---------------------------------------------------------------------------
log("tokenizing features ...")
term_id = {}
term_str = []
df = array.array("i")
def tid(t):
    j = term_id.get(t)
    if j is None:
        j = len(term_str)
        term_id[t] = j
        term_str.append(t)
        df.append(0)
    return j

offsets = array.array("i")      # CSR offsets (len N+1)
flat_t = array.array("i")       # term ids
flat_tf = array.array("b")      # capped tf
meta = []                       # parallel per-doc metadata
strong_terms = set()            # full head / constraint / value (weight terms)
anchor_terms = set()            # conclusion head / constraint only (generate pairs)

def add(tokens, t, tf=1):
    tf = min(TF_CAP, tf)
    j = tid(t)
    tokens.append((j, tf))

N_scanned = N = 0
LIMIT = int(os.environ.get("ATLAS_LIMIT", "0"))  # 0 = full run
with open(FEAT, "rb") as f:
    for line in f:
        r = json.loads(line)
        N_scanned += 1
        if LIMIT and N_scanned > LIMIT:
            break
        if r["isGenerated"] or r["kind"] not in INCLUDE_KINDS:
            continue
        # instances/classes are machine-like boilerplate, not mathematical
        # statements; exclude them (matches the script-15 human-authored view)
        if r.get("isInstance") or r.get("isClass"):
            continue
        name = r["name"]
        module = r["module"]
        if area_of(module) in NONMATH_AREAS:
            continue
        if name.startswith("_private") or ".Meta." in module:
            continue
        last = name.rsplit(".", 1)[-1]
        if last.startswith(GEN_SUFFIX):
            continue
        cons = skel_constraints.get(name, ())
        toks = []
        # kind
        add(toks, ("k", r["kind"]))
        # conclusion head: full + name segments
        ch = r.get("conclusionHead") or ""
        if ch:
            add(toks, ("H", ch))
            for seg in ch.split("."):
                add(toks, ("h", seg))
        # type-class constraints: full + segments, repeated by multiplicity
        for c in cons:
            add(toks, ("C", c))
            for seg in c.split("."):
                add(toks, ("c", seg))
        # value head (only when a trustworthy value exists)
        vh = r.get("valueHead") or ""
        if vh and r.get("hasValue") and not r.get("valueTruncated"):
            add(toks, ("V", vh))
        # structural shape (bucketed so size is a soft signal)
        add(toks, ("s", "pi", bucket(r["nPi"])))
        add(toks, ("s", "inst", bucket(r["nInstImplicit"])))
        add(toks, ("s", "imp", bucket(r["nImplicit"])))
        add(toks, ("s", "strict", bucket(r["nStrictImplicit"])))
        add(toks, ("s", "default", bucket(r["nDefault"])))
        add(toks, ("s", "nc", bucket(len(cons))))
        add(toks, ("s", "tn", bucket(r["typeNodes"])))
        add(toks, ("s", "td", bucket(r["typeDepth"])))
        add(toks, ("s", "tdist", bucket(r["typeDistinct"])))
        # aggregate duplicate term ids into tf map then append sorted
        agg = {}
        for j, tf in toks:
            agg[j] = min(TF_CAP, agg.get(j, 0) + tf)
        offsets.append(len(flat_t))
        for j in sorted(agg):
            flat_t.append(j)
            flat_tf.append(agg[j])
            df[j] += 1
            tag = term_str[j][0]
            if tag in ("H", "C", "V"):
                strong_terms.add(j)
            if tag in ("H", "C"):
                anchor_terms.add(j)
        module = r["module"]
        meta.append({
            "name": name, "kind": r["kind"], "module": module,
            "area": area_of(module), "ch": ch,
            "cons": cons,
            # discrete baseline = what an exact 15-B-style signature sees
            "disc": (ch, cons, r["nPi"], r["nInstImplicit"], r["nImplicit"],
                     r["nStrictImplicit"], r["nDefault"]),
        })
        N += 1
offsets.append(len(flat_t))
log(f"  scanned {N_scanned:,}; embedded {N:,} docs; vocab {len(term_str):,}; strong {len(strong_terms):,}")

# idf + per-doc L2 norms; weights use sublinear tf
idf = [math.log((N + 1.0) / (df[j] + 1.0)) + 1.0 for j in range(len(term_str))]
def w_at(j, tf):
    return (1.0 + math.log(tf)) * idf[j]
norms = array.array("d")
for d in range(N):
    s = 0.0
    for p in range(offsets[d], offsets[d + 1]):
        w = w_at(flat_t[p], flat_tf[p])
        s += w * w
    norms.append(math.sqrt(s))

# ---------------------------------------------------------------------------
# Inverted index over strong terms + candidate pair accumulation
# ---------------------------------------------------------------------------
log("building strong-term postings ...")
postings = {}
for j in anchor_terms:
    if 2 <= df[j] <= GEN_CAP_DF:
        postings[j] = array.array("i")
for d in range(N):
    for p in range(offsets[d], offsets[d + 1]):
        j = flat_t[p]
        if j in postings:
            postings[j].append(d)
log(f"  generating terms: {len(postings):,}")

log("accumulating candidate strong-dots ...")
strong_dot = {}
for j, post in postings.items():
    P = len(post)
    for a in range(P):
        di = post[a]
        # weight of term j in doc di
        # (find tf via its CSR slice; small vectors, linear scan)
        pass
# per-doc weights for all strong (H/C/V) terms: anchor H/C drive candidate
# generation, V (value head) is added at re-rank time and shown for context.
doc_strong_w = [None] * N
for d in range(N):
    m = None
    for p in range(offsets[d], offsets[d + 1]):
        j = flat_t[p]
        if j in strong_terms:
            if m is None:
                m = {}
            m[j] = w_at(j, flat_tf[p])
    if m:
        doc_strong_w[d] = m
strong_dot = {}
for j, post in postings.items():
    P = len(post)
    for a in range(P):
        di = post[a]
        wi = doc_strong_w[di][j]
        for b in range(a + 1, P):
            dk = post[b]
            key = (di, dk) if di < dk else (dk, di)
            w = wi * doc_strong_w[dk][j]
            prev = strong_dot.get(key)
            strong_dot[key] = w if prev is None else prev + w
log(f"  candidate pairs: {len(strong_dot):,}")

# ---------------------------------------------------------------------------
# Exact cosine for candidates that can possibly clear the threshold
# ---------------------------------------------------------------------------
def vec_slice(d):
    return offsets[d], offsets[d + 1]

def rest_dot(di, dk):
    """dot over every term NOT used to generate the pair (i.e. not in a
    generating posting): segments, shape, value head V, AND anchor terms
    whose df fell outside the generation band. Combined with strong_dot this
    equals the exact full-vector dot product."""
    gen_set = GEN_SET
    ai, bi = vec_slice(di)
    ak, bk = vec_slice(dk)
    s = 0.0
    while ai < bi and ak < bk:
        ti, tk = flat_t[ai], flat_t[ak]
        if ti == tk:
            if ti not in gen_set:
                s += w_at(ti, flat_tf[ai]) * w_at(tk, flat_tf[ak])
            ai += 1; ak += 1
        elif ti < tk:
            ai += 1
        else:
            ak += 1
    return s

def shared_strong(di, dk):
    m = doc_strong_w[di]
    out = []
    if not m:
        return out
    for p in range(offsets[dk], offsets[dk + 1]):
        j = flat_t[p]
        if j in m:
            out.append(term_str[j])
    return out

DISC_FIELDS = ["conclusionHead", "constraints", "nPi", "nInstImplicit",
               "nImplicit", "nStrictImplicit", "nDefault"]
def disc_diff(di, dk):
    a, b = meta[di]["disc"], meta[dk]["disc"]
    return [DISC_FIELDS[i] for i in range(len(DISC_FIELDS)) if a[i] != b[i]]

log("scoring candidates ...")
GEN_SET = postings.keys()
best = {}                 # doc -> list of (cos, other, diffFields, shared)
xrows = []
n_kept = n_cross = n_same = n_exactalready = n_fuzzy = 0
area_pair = collections.Counter()
for (i, k), sd in strong_dot.items():
    ni, nk = norms[i], norms[k]
    if ni == 0.0 or nk == 0.0:
        continue
    # idf upper bound: rest terms only add, so prune hopeless pairs now
    if sd / (ni * nk) < COS_THRESH:
        wd = rest_dot(i, k)
        if (sd + wd) / (ni * nk) < COS_THRESH:
            continue
    else:
        wd = rest_dot(i, k)
    cos = (sd + wd) / (ni * nk)
    if cos < COS_THRESH:
        continue
    diff = disc_diff(i, k)
    n_kept += 1
    if diff:
        n_fuzzy += 1
    else:
        n_exactalready += 1
    sh = ["%s:%s" % t for t in shared_strong(i, k)]
    rec_i = (cos, k, diff, sh)
    rec_k = (cos, i, diff, sh)
    for d, rec in ((i, rec_i), (k, rec_k)):
        cur = best.get(d)
        if cur is None:
            best[d] = [rec]
        elif len(cur) < TOPK:
            cur.append(rec)
            if len(cur) == TOPK:
                cur.sort(key=lambda z: -z[0])
        elif rec[0] > cur[-1][0]:
            cur[-1] = rec
            cur.sort(key=lambda z: -z[0])
    ai_, ak_ = meta[i]["area"], meta[k]["area"]
    if ai_ != ak_:
        n_cross += 1
        area_pair[tuple(sorted((ai_, ak_)))] += 1
        xrows.append((cos, i, k, diff, sh))
    else:
        n_same += 1
log(f"  kept pairs {n_kept:,} (fuzzy {n_fuzzy:,}, exact-already {n_exactalready:,}); "
    f"cross-area {n_cross:,}; same-area {n_same:,}")

# ---------------------------------------------------------------------------
# Outputs
# ---------------------------------------------------------------------------
log("writing nearest neighbours ...")
with open(OUT_NN, "wb") as o:
    for d in range(N):
        cur = best.get(d)
        if not cur:
            continue
        cur.sort(key=lambda z: -z[0])
        m = meta[d]
        row = {"name": m["name"], "kind": m["kind"], "module": m["module"],
               "area": m["area"], "neighbors": []}
        for cos, k, diff, sh in cur:
            mk = meta[k]
            row["neighbors"].append({
                "name": mk["name"], "module": mk["module"], "area": mk["area"],
                "cosine": round(cos, 6), "diffFields": diff,
                "sharedStrong": sh[:6]})
        o.write((json.dumps(row, ensure_ascii=False) + "\n").encode("utf-8"))

log("writing cross-area analogies ...")
# fuzzy analogies (the exact method misses these) first, then by cosine
xrows.sort(key=lambda z: (0 if z[3] else 1, -z[0]))
xrows = xrows[:XCROSS_CAP]
with open(OUT_X, "wb") as o:
    for cos, i, k, diff, sh in xrows:
        mi, mk = meta[i], meta[k]
        o.write((json.dumps({
            "cosine": round(cos, 6),
            "a": {"name": mi["name"], "module": mi["module"], "area": mi["area"]},
            "b": {"name": mk["name"], "module": mk["module"], "area": mk["area"]},
            "diffFields": diff, "sharedStrong": sh[:8]},
            ensure_ascii=False) + "\n").encode("utf-8"))

summary = {
    "params": {"includeKinds": sorted(INCLUDE_KINDS), "genCapDf": GEN_CAP_DF,
               "cosThreshold": COS_THRESH, "topK": TOPK, "tfCap": TF_CAP,
               "crossCap": XCROSS_CAP},
    "scanned": N_scanned, "embedded": N, "vocab": len(term_str),
    "strongTerms": len(strong_terms), "anchorTerms": len(anchor_terms),
    "generatingTerms": len(postings),
    "candidatePairs": len(strong_dot), "keptPairs": n_kept,
    "fuzzyPairs_diffNonEmpty": n_fuzzy,
    "exactAlreadyPairs_diffEmpty": n_exactalready,
    "crossAreaPairs": n_cross, "sameAreaPairs": n_same,
    "docsWithNeighbor": len(best), "crossAreaEmitted": len(xrows),
    "topAreaPairs": [{"areas": list(a), "count": c}
                     for a, c in area_pair.most_common(25)],
}
with open(OUT_SUM, "wb") as o:
    o.write(json.dumps(summary, ensure_ascii=False, indent=2).encode("utf-8"))
log("summary: " + json.dumps({k: v for k, v in summary.items()
                              if k not in ("topAreaPairs", "params")}, indent=0))
log("done.")
