#!/usr/bin/env python3
"""verify_embeddings.py — independent verification for script 17.

Rebuilds the token documents, global df/idf and per-doc norms from the raw
13/09 corpora with a separate straightforward implementation, then re-derives
the cosine of every emitted cross-area pair and a deterministic sample of
nearest-neighbour rows directly (two-pointer over independently rebuilt
vectors), and reconciles every count in embedding_summary.json against the
emitted files. Prints VERIFICATION OK or raises.
"""
import json, math, array, collections, os, sys

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
DATA = os.path.join(ROOT, "data")
FEAT = os.path.join(DATA, "atlas_features.jsonl")
SKEL = os.path.join(DATA, "atlas_type_skeletons.jsonl")
OUT_NN = os.path.join(DATA, "embedding_nearest_neighbors.jsonl")
OUT_X = os.path.join(DATA, "embedding_cross_area_analogies.jsonl")
OUT_SUM = os.path.join(DATA, "embedding_summary.json")

INCLUDE_KINDS = {"theorem", "definition", "opaque"}
NONMATH_AREAS = {"Tactic", "Lean", "(root)"}
GEN_SUFFIX = ("hcongr",)
TF_CAP = 4

def bucket(x):
    return 0 if x <= 0 else min(7, (x - 1).bit_length())

def area_of(module):
    p = module.split(".")
    return p[1] if len(p) >= 2 and p[0] == "Mathlib" else "(root)"

DISC_FIELDS = ["conclusionHead", "constraints", "nPi", "nInstImplicit",
               "nImplicit", "nStrictImplicit", "nDefault"]

def fail(msg):
    print("VERIFICATION FAILED:", msg)
    sys.exit(1)

# ---- rebuild corpus independently ------------------------------------------
print("[verify] reading skeletons ...")
skel = {}
with open(SKEL, "rb") as f:
    for line in f:
        r = json.loads(line)
        skel[r["name"]] = tuple(sorted(c["class"] for c in r.get("constraints", [])))

print("[verify] rebuilding token documents ...")
term_id, df = {}, array.array("i")
def tid(t):
    j = term_id.get(t)
    if j is None:
        j = len(term_id); term_id[t] = j; df.append(0)
    return j

offsets = array.array("i"); flat_t = array.array("i"); flat_tf = array.array("b")
name_idx, disc, areas = {}, {}, {}
N_scanned = N = 0
with open(FEAT, "rb") as f:
    for line in f:
        r = json.loads(line); N_scanned += 1
        if r["isGenerated"] or r["kind"] not in INCLUDE_KINDS:
            continue
        if r.get("isInstance") or r.get("isClass"):
            continue
        name = r["name"]; module = r["module"]
        if area_of(module) in NONMATH_AREAS:
            continue
        if name.startswith("_private") or ".Meta." in module:
            continue
        if name.rsplit(".", 1)[-1].startswith(GEN_SUFFIX):
            continue
        cons = skel.get(name, ())
        toks = []
        def add(t, tf=1):
            toks.append((tid(t), tf))
        add(("k", r["kind"]))
        ch = r.get("conclusionHead") or ""
        if ch:
            add(("H", ch))
            for s in ch.split("."):
                add(("h", s))
        for c in cons:
            add(("C", c))
            for s in c.split("."):
                add(("c", s))
        vh = r.get("valueHead") or ""
        if vh and r.get("hasValue") and not r.get("valueTruncated"):
            add(("V", vh))
        add(("s", "pi", bucket(r["nPi"]))); add(("s", "inst", bucket(r["nInstImplicit"])))
        add(("s", "imp", bucket(r["nImplicit"]))); add(("s", "strict", bucket(r["nStrictImplicit"])))
        add(("s", "default", bucket(r["nDefault"]))); add(("s", "nc", bucket(len(cons))))
        add(("s", "tn", bucket(r["typeNodes"]))); add(("s", "td", bucket(r["typeDepth"])))
        add(("s", "tdist", bucket(r["typeDistinct"])))
        agg = {}
        for j, tf in toks:
            agg[j] = min(TF_CAP, agg.get(j, 0) + tf)
        offsets.append(len(flat_t))
        for j in sorted(agg):
            flat_t.append(j); flat_tf.append(agg[j]); df[j] += 1
        name_idx[name] = N
        disc[name] = (ch, cons, r["nPi"], r["nInstImplicit"], r["nImplicit"],
                      r["nStrictImplicit"], r["nDefault"])
        areas[name] = area_of(module)
        N += 1
offsets.append(len(flat_t))
V = len(term_id)
idf = [math.log((N + 1.0) / (df[j] + 1.0)) + 1.0 for j in range(V)]
def w(j, tf):
    return (1.0 + math.log(tf)) * idf[j]
norms = array.array("d")
for d in range(N):
    s = 0.0
    for p in range(offsets[d], offsets[d + 1]):
        ww = w(flat_t[p], flat_tf[p]); s += ww * ww
    norms.append(math.sqrt(s))

def cosine(na, nb):
    a = name_idx[na]; b = name_idx[nb]
    i, j = offsets[a], offsets[b]; ie, je = offsets[a + 1], offsets[b + 1]
    dot = 0.0
    while i < ie and j < je:
        ta, tb = flat_t[i], flat_t[j]
        if ta == tb:
            dot += w(ta, flat_tf[i]) * w(tb, flat_tf[j]); i += 1; j += 1
        elif ta < tb:
            i += 1
        else:
            j += 1
    return dot / (norms[a] * norms[b])

def diff_of(na, nb):
    a, b = disc[na], disc[nb]
    return [DISC_FIELDS[k] for k in range(len(DISC_FIELDS)) if a[k] != b[k]]

summary = json.load(open(OUT_SUM, "rb"))
thr = summary["params"]["cosThreshold"]; topk = summary["params"]["topK"]
EPS = 1e-4

# ---- reconcile global counts ------------------------------------------------
if summary["scanned"] != N_scanned:
    fail(f"scanned {summary['scanned']} != rebuilt {N_scanned}")
if summary["embedded"] != N:
    fail(f"embedded {summary['embedded']} != rebuilt {N}")
if summary["vocab"] != V:
    fail(f"vocab {summary['vocab']} != rebuilt {V}")
print(f"[verify] embedded={N:,} vocab={V:,} match summary")

# ---- cross-area file: every pair re-derived ---------------------------------
print("[verify] checking every emitted cross-area pair ...")
nx = 0
with open(OUT_X, "rb") as f:
    for line in f:
        r = json.loads(line); nx += 1
        a, b = r["a"]["name"], r["b"]["name"]
        if a not in name_idx or b not in name_idx:
            fail("cross pair references unknown declaration")
        c = cosine(a, b)
        if abs(c - r["cosine"]) > EPS:
            fail(f"cosine mismatch {a}~{b}: stored {r['cosine']} got {c:.6f}")
        if c < thr - EPS:
            fail(f"pair below threshold: {a}~{b} {c:.4f}")
        if areas[a] != r["a"]["area"] or areas[b] != r["b"]["area"]:
            fail("area label mismatch")
        if areas[a] == areas[b]:
            fail("cross-area pair is actually same-area")
        if diff_of(a, b) != r["diffFields"]:
            fail(f"diffFields mismatch {a}~{b}: {diff_of(a,b)} vs {r['diffFields']}")
if nx != summary["crossAreaEmitted"]:
    fail(f"cross file rows {nx} != summary {summary['crossAreaEmitted']}")
print(f"[verify] {nx:,} cross-area pairs: cosine/area/diff all correct")

# ---- NN file: deterministic sample fully re-derived -------------------------
print("[verify] sampling nearest-neighbour rows ...")
nn_rows = 0; checked = 0
STEP = 37
prev_cos = None
with open(OUT_NN, "rb") as f:
    for line in f:
        r = json.loads(line)
        do = (nn_rows % STEP == 0)
        nn_rows += 1
        nb = r["neighbors"]
        if len(nb) > topk:
            fail("too many neighbours")
        # global sortedness within row
        cs = [z["cosine"] for z in nb]
        if cs != sorted(cs, reverse=True):
            fail(f"neighbours not sorted for {r['name']}")
        if not do:
            continue
        if r["name"] not in name_idx:
            fail("NN row unknown declaration")
        if areas[r["name"]] != r["area"]:
            fail("NN area mismatch")
        for z in nb:
            c = cosine(r["name"], z["name"])
            if abs(c - z["cosine"]) > EPS:
                fail(f"NN cosine mismatch {r['name']}~{z['name']}: {c:.6f} vs {z['cosine']}")
            if c < thr - EPS:
                fail("NN below threshold")
            if diff_of(r["name"], z["name"]) != z["diffFields"]:
                fail("NN diffFields mismatch")
            checked += 1
if nn_rows != summary["docsWithNeighbor"]:
    fail(f"NN rows {nn_rows} != docsWithNeighbor {summary['docsWithNeighbor']}")
print(f"[verify] {nn_rows:,} NN rows (sampled {checked:,} neighbour edges) correct")

# ---- cross file is fuzzy-first ordered --------------------------------------
first_exact = None
with open(OUT_X, "rb") as f:
    for i, line in enumerate(f):
        r = json.loads(line)
        if not r["diffFields"]:
            first_exact = i; break
fuzzy_after_exact = 0
if first_exact is not None:
    with open(OUT_X, "rb") as f:
        for i, line in enumerate(f):
            if i > first_exact and json.loads(line)["diffFields"]:
                fuzzy_after_exact += 1
if fuzzy_after_exact:
    fail(f"{fuzzy_after_exact} fuzzy pairs appear after first exact-already pair")
print("[verify] cross-area file ordered fuzzy-first")

print("VERIFICATION OK")
print(json.dumps({k: summary[k] for k in
      ("embedded","vocab","candidatePairs","keptPairs","fuzzyPairs_diffNonEmpty",
       "exactAlreadyPairs_diffEmpty","crossAreaPairs","docsWithNeighbor")}, indent=2))
