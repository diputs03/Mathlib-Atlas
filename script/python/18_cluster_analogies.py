#!/usr/bin/env python3
"""18_cluster_analogies.py — cluster the script-17 similarity graph into
analogy communities.

Builds the undirected weighted graph from embedding_nearest_neighbors.jsonl,
runs deterministic union-find connected components across a cosine threshold
sweep, and materialises the primary clustering (THRESHOLD = 0.90): one row per
analogy community with its areas/modules, common constraint/head anchors,
common name suffix, cross-area flag and representative members, plus a full
node -> cluster assignment and a summary (with the strongest cross-area
communities ranked as missing-abstraction candidates).

Pure Python, deterministic (sorted nodes/edges, no randomness).
Inputs : data/atlas_features.jsonl (labels), data/embedding_nearest_neighbors.jsonl
Outputs: data/analogy_clusters.jsonl
         data/analogy_cluster_assignment.jsonl
         data/analogy_cluster_summary.json
"""
import json, os, math, collections, time, array

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
DATA = os.path.join(ROOT, "data")
FEAT = os.path.join(DATA, "atlas_features.jsonl")
NN = os.path.join(DATA, "embedding_nearest_neighbors.jsonl")
OUT_CL = os.path.join(DATA, "analogy_clusters.jsonl")
OUT_AS = os.path.join(DATA, "analogy_cluster_assignment.jsonl")
OUT_SUM = os.path.join(DATA, "analogy_cluster_summary.json")

THRESHOLD = 0.90
SWEEP = (0.95, 0.92, 0.90, 0.85, 0.80, 0.75, 0.70)
MEMBER_CAP = 40

def log(m): print(f"[{time.strftime('%H:%M:%S')}] {m}", flush=True)
def suffix(n): return n.rsplit(".", 1)[-1]
def area_of(module):
    p = module.split(".")
    return p[1] if len(p) >= 2 and p[0] == "Mathlib" else "(root)"

class DSU:
    __slots__ = ("p",)
    def __init__(self, n): self.p = list(range(n))
    def find(self, x):
        p = self.p
        while p[x] != x:
            p[x] = p[p[x]]; x = p[x]
        return x
    def union(self, a, b):
        ra, rb = self.find(a), self.find(b)
        if ra != b:
            # deterministic: smaller root id absorbs
            if ra < rb: self.p[rb] = ra
            else: self.p[ra] = rb

# ---- labels from features ---------------------------------------------------
log("loading labels from features ...")
meta = {}
with open(FEAT, "rb") as f:
    for line in f:
        r = json.loads(line)
        meta[r["name"]] = (r["kind"], r["module"], area_of(r["module"]))

# ---- undirected weighted graph ---------------------------------------------
log("building graph from nearest neighbours ...")
nodes = set()
edges = {}   # (a,b) sorted -> (cosine, diffFields set, sharedStrong set)
with open(NN, "rb") as f:
    for line in f:
        r = json.loads(line)
        a = r["name"]; nodes.add(a)
        for z in r["neighbors"]:
            b = z["name"]; nodes.add(b)
            x, y = (a, b) if a < b else (b, a)
            c = z["cosine"]
            cur = edges.get((x, y))
            if cur is None or c > cur[0]:
                edges[(x, y)] = (c, tuple(z.get("diffFields", [])),
                                 tuple(z.get("sharedStrong", [])))
nodes = sorted(nodes)
idx = {n: i for i, n in enumerate(nodes)}
N = len(nodes)
log(f"  {N:,} nodes, {len(edges):,} undirected edges")

# adjacency for cluster internals (only >= primary threshold)
adj = collections.defaultdict(list)
for (a, b), (c, df, sh) in edges.items():
    if c >= THRESHOLD:
        adj[a].append((b, c, df, sh)); adj[b].append((a, c, df, sh))

# ---- threshold sweep --------------------------------------------------------
log("threshold sweep ...")
sweep = []
for thr in SWEEP:
    dsu = DSU(N); kept = 0
    for (a, b), (c, _, _) in edges.items():
        if c >= thr:
            dsu.union(idx[a], idx[b]); kept += 1
    sizes = collections.Counter(dsu.find(i) for i in range(N))
    multi = sorted((v for v in sizes.values() if v >= 2), reverse=True)
    sweep.append({"threshold": thr, "edgesKept": kept,
                  "clusters": len(multi), "clusteredNodes": sum(multi),
                  "singletons": N - sum(multi),
                  "largest": multi[:8],
                  "sizeHist": dict(collections.Counter(
                      "2" if v == 2 else "3-4" if v <= 4 else
                      "5-8" if v <= 8 else "9-16" if v <= 16 else
                      "17-32" if v <= 32 else "33+" for v in multi))})

# ---- primary clustering -----------------------------------------------------
log(f"primary clustering at {THRESHOLD} ...")
dsu = DSU(N)
for (a, b), (c, _, _) in edges.items():
    if c >= THRESHOLD:
        dsu.union(idx[a], idx[b])
members = collections.defaultdict(list)
for i, n in enumerate(nodes):
    members[dsu.find(i)].append(n)

clusters = []
for root, mem in members.items():
    if len(mem) < 2:
        continue
    mem = sorted(mem)
    size = len(mem)
    areas = collections.Counter(); modules = collections.Counter()
    kinds = collections.Counter()
    for n in mem:
        k, m, ar = meta.get(n, ("?", "?", "(root)"))
        areas[ar] += 1; modules[m] += 1; kinds[k] += 1
    # internal edge stats + anchor/suffix aggregation
    internal = 0; csum = 0.0; cmin = 1.0; fuzzy_edges = 0
    anchor = collections.Counter(); diffc = collections.Counter()
    degw = collections.defaultdict(float)
    seen_edge = set()
    for a in mem:
        for (b, c, df, sh) in adj[a]:
            if b not in idx: continue
            ek = (a, b) if a < b else (b, a)
            # b must be in same cluster
            if dsu.find(idx[a]) != dsu.find(idx[b]): continue
            if ek in seen_edge: continue
            seen_edge.add(ek)
            internal += 1; csum += c; cmin = min(cmin, c)
            if df: fuzzy_edges += 1
            for d in df: diffc[d] += 1
            for s in sh: anchor[s] += 1
            degw[a] += c; degw[b] += c
    suf = collections.Counter(suffix(n) for n in mem)
    top_suf, top_suf_n = suf.most_common(1)[0]
    rep = max(mem, key=lambda n: (degw.get(n, 0.0), n)) if degw else mem[0]
    cross = len(areas) >= 2
    # label: a dominant shared name suffix wins, else strongest anchor
    if top_suf_n >= max(2, math.ceil(size / 2)):
        label = f"{top_suf} family"
    elif anchor:
        label = anchor.most_common(1)[0][0]
    else:
        label = f"{rep} cluster"
    clusters.append({
        "label": label, "size": size, "crossArea": cross,
        "nAreas": len(areas), "areas": dict(areas.most_common()),
        "nModules": len(modules),
        "topModules": [m for m, _ in modules.most_common(8)],
        "kinds": dict(kinds.most_common()),
        "internalEdges": internal,
        "meanCosine": round(csum / internal, 4) if internal else None,
        "minCosine": round(cmin, 4) if internal else None,
        "fuzzyEdges": fuzzy_edges,
        "diffFields": [d for d, _ in diffc.most_common()],
        "commonAnchors": [a for a, _ in anchor.most_common(8)],
        "topSuffix": {"suffix": top_suf, "coverage": top_suf_n},
        "representative": rep,
        "memberCount": size,
        "members": mem[:MEMBER_CAP],
    })

# deterministic ordering: cross-area first, then larger, then label
clusters.sort(key=lambda c: (0 if c["crossArea"] else 1, -c["size"], c["label"]))
for cid, c in enumerate(clusters):
    c["clusterId"] = cid
log(f"  {len(clusters):,} communities (size>=2)")

# ---- assignment -------------------------------------------------------------
root_to_cid = {dsu.find(idx[c["representative"]]): c["clusterId"]
               for c in clusters}
node_cluster = {}
for i, n in enumerate(nodes):
    cid = root_to_cid.get(dsu.find(i))
    if cid is not None:
        node_cluster[n] = cid

# ---- write ------------------------------------------------------------------
log("writing clusters + assignment ...")
with open(OUT_CL, "wb") as o:
    for c in clusters:
        o.write((json.dumps(c, ensure_ascii=False) + "\n").encode("utf-8"))
with open(OUT_AS, "wb") as o:
    for n in nodes:
        cid = node_cluster.get(n)
        if cid is None: continue
        k, m, ar = meta.get(n, ("?", "?", "(root)"))
        o.write((json.dumps({"name": n, "cluster": cid, "area": ar,
                             "module": m, "kind": k,
                             "clusterSize": clusters[cid]["size"],
                             "crossArea": clusters[cid]["crossArea"]},
                            ensure_ascii=False) + "\n").encode("utf-8"))

cross_cl = [c for c in clusters if c["crossArea"]]
cross_cl_sorted = sorted(cross_cl,
                         key=lambda c: (-(c["size"] * c["nAreas"]), -c["size"]))
size_hist = collections.Counter(
    "2" if c["size"] == 2 else "3-4" if c["size"] <= 4 else
    "5-8" if c["size"] <= 8 else "9-16" if c["size"] <= 16 else
    "17-32" if c["size"] <= 32 else "33+" for c in clusters)
summary = {
    "threshold": THRESHOLD, "nodes": N, "undirectedEdges": len(edges),
    "clusters": len(clusters), "crossAreaClusters": len(cross_cl),
    "sameAreaClusters": len(clusters) - len(cross_cl),
    "clusteredNodes": sum(c["size"] for c in clusters),
    "sizeHist": dict(size_hist), "sweep": sweep,
    "topCrossArea": [{"clusterId": c["clusterId"], "label": c["label"],
                      "size": c["size"], "nAreas": c["nAreas"],
                      "areas": c["areas"], "meanCosine": c["meanCosine"],
                      "topSuffix": c["topSuffix"],
                      "commonAnchors": c["commonAnchors"][:5],
                      "representative": c["representative"]}
                     for c in cross_cl_sorted[:30]],
}
with open(OUT_SUM, "wb") as o:
    o.write(json.dumps(summary, ensure_ascii=False, indent=2).encode("utf-8"))
log(f"  cross-area communities: {len(cross_cl):,}; clustered nodes: "
    f"{summary['clusteredNodes']:,}")
log("top cross-area analogy communities:")
for c in cross_cl_sorted[:12]:
    print(f"  #{c['clusterId']:5d} n={c['size']:3d} areas={c['nAreas']:2d} "
          f"cos={c['meanCosine']} label={c['label']!r} areas={list(c['areas'])[:6]}")
log("done.")
