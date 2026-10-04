#!/usr/bin/env python3
"""verify_clusters.py — independent verification for script 18.

Rebuilds the undirected similarity graph from embedding_nearest_neighbors.jsonl
and the union-find components at every sweep threshold, then checks the emitted
clusters / assignment / summary against that independent rebuild:
  * sweep table (clusters, clustered nodes) reproduced exactly;
  * primary components reproduce every cluster's size and full membership
    (cluster row sample + complete assignment file);
  * cross-area flags, area counts and size histogram recomputed and equal;
  * every edge >= threshold stays inside one component (and vice versa for
    cross-component pairs);
  * assignment is a partition (each clustered node exactly once).
"""
import json, os, sys, collections

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
DATA = os.path.join(ROOT, "data")
FEAT = os.path.join(DATA, "atlas_features.jsonl")
NN = os.path.join(DATA, "embedding_nearest_neighbors.jsonl")
CL = os.path.join(DATA, "analogy_clusters.jsonl")
AS = os.path.join(DATA, "analogy_cluster_assignment.jsonl")
SUM = os.path.join(DATA, "analogy_cluster_summary.json")

def fail(m):
    print("VERIFICATION FAILED:", m); sys.exit(1)
def area_of(module):
    p = module.split(".")
    return p[1] if len(p) >= 2 and p[0] == "Mathlib" else "(root)"
def suffix(n): return n.rsplit(".", 1)[-1]

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
        if ra != rb:
            if ra < rb: self.p[rb] = ra
            else: self.p[ra] = rb

# labels
area = {}
for line in open(FEAT, "rb"):
    r = json.loads(line); area[r["name"]] = area_of(r["module"])

# graph
nodes = set(); edges = {}
for line in open(NN, "rb"):
    r = json.loads(line); a = r["name"]; nodes.add(a)
    for z in r["neighbors"]:
        b = z["name"]; nodes.add(b)
        x, y = (a, b) if a < b else (b, a)
        c = z["cosine"]
        if (x, y) not in edges or c > edges[(x, y)]:
            edges[(x, y)] = c
nodes = sorted(nodes); idx = {n: i for i, n in enumerate(nodes)}; N = len(nodes)

def components(thr):
    d = DSU(N)
    for (a, b), c in edges.items():
        if c >= thr: d.union(idx[a], idx[b])
    comp = collections.defaultdict(list)
    for i, n in enumerate(nodes): comp[d.find(i)].append(n)
    return d, comp

summary = json.load(open(SUM, "rb"))
thr = summary["threshold"]

# ---- sweep reproduction -----------------------------------------------------
for s in summary["sweep"]:
    _, comp = components(s["threshold"])
    multi = [v for v in comp.values() if len(v) >= 2]
    if len(multi) != s["clusters"]:
        fail(f"sweep {s['threshold']}: clusters {len(multi)} != {s['clusters']}")
    if sum(len(v) for v in multi) != s["clusteredNodes"]:
        fail(f"sweep {s['threshold']}: clusteredNodes mismatch")
print("[verify] threshold sweep reproduced for", len(summary["sweep"]), "cuts")

# ---- primary components -----------------------------------------------------
dsu, comp = components(thr)
root_members = {tuple(sorted(v)): v for v in comp.values() if len(v) >= 2}
# map representative -> full component
rep_comp = {}
for mem in comp.values():
    if len(mem) >= 2:
        rep_comp[sorted(mem)[0]] = mem  # not used directly; build root map below
root_of = {n: dsu.find(idx[n]) for n in nodes}
root_set = collections.defaultdict(set)
for n in nodes: root_set[root_of[n]].add(n)

clusters = [json.loads(l) for l in open(CL, "rb")]
if len(clusters) != summary["clusters"]:
    fail(f"cluster count {len(clusters)} != summary {summary['clusters']}")

# ---- cluster membership / labels -------------------------------------------
seen_nodes = set()
hist = collections.Counter()
n_cross = 0
for c in clusters:
    full = root_set[root_of[c["representative"]]]
    if c["size"] != len(full) or c["memberCount"] != len(full):
        fail(f"cluster {c['clusterId']} size {c['size']} != component {len(full)}")
    for m in c["members"]:
        if m not in full: fail(f"cluster {c['clusterId']} has outsider {m}")
    if len(c["members"]) > 40: fail("member cap exceeded")
    full_sorted = sorted(full)
    # areas recomputed (iterate sorted to match producer tie-break order)
    ar = collections.Counter(area.get(m, "(root)") for m in full_sorted)
    if dict(ar.most_common()) != c["areas"]:
        fail(f"cluster {c['clusterId']} area counts mismatch")
    cross = len(ar) >= 2
    if cross != c["crossArea"]: fail(f"cluster {c['clusterId']} crossArea flag")
    if cross: n_cross += 1
    # suffix coverage (sorted iteration for deterministic tie-break)
    su = collections.Counter(suffix(m) for m in full_sorted)
    ts, tn = su.most_common(1)[0]
    if c["topSuffix"]["suffix"] != ts or c["topSuffix"]["coverage"] != tn:
        fail(f"cluster {c['clusterId']} topSuffix mismatch")
    v = c["size"]
    hist["2" if v == 2 else "3-4" if v <= 4 else "5-8" if v <= 8 else
         "9-16" if v <= 16 else "17-32" if v <= 32 else "33+"] += 1
if n_cross != summary["crossAreaClusters"]:
    fail("crossAreaClusters count mismatch")
if dict(hist) != summary["sizeHist"]:
    fail(f"sizeHist mismatch {dict(hist)} vs {summary['sizeHist']}")
print(f"[verify] {len(clusters)} clusters: size/areas/suffix/hist all correct "
      f"({n_cross} cross-area)")

# ---- assignment is an exact partition --------------------------------------
assign = {}
for line in open(AS, "rb"):
    r = json.loads(line)
    if r["name"] in assign: fail("duplicate assignment " + r["name"])
    assign[r["name"]] = r
cl_by_id = {c["clusterId"]: c for c in clusters}
clustered = set()
for n, r in assign.items():
    c = cl_by_id[r["cluster"]]
    if r["clusterSize"] != c["size"]: fail("assignment clusterSize mismatch")
    if r["crossArea"] != c["crossArea"]: fail("assignment crossArea mismatch")
    if area.get(n, "(root)") != r["area"]: fail("assignment area mismatch")
    if root_of[n] != root_of[c["representative"]]:
        fail("assignment points to wrong component")
    clustered.add(n)
# every node in a >=2 component must be assigned, and only those
expect = set()
for mem in comp.values():
    if len(mem) >= 2: expect.update(mem)
if clustered != expect:
    fail(f"assignment coverage mismatch (missing {len(expect-clustered)}, "
         f"extra {len(clustered-expect)})")
print(f"[verify] assignment partitions {len(clustered):,} clustered nodes exactly")

# ---- edge/component consistency --------------------------------------------
bad = 0
for (a, b), c in edges.items():
    same = root_of[a] == root_of[b]
    if c >= thr and not same: bad += 1
if bad: fail(f"{bad} edges >= {thr} cross components")
print("[verify] all kept edges lie within their component")
print("VERIFICATION OK")
