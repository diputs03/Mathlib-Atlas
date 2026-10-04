#!/usr/bin/env python3
"""80_neighborhoods.py — competing neighborhood definitions for Phase 4.

Scope (per the falsification plan): two mature areas, Order + Algebra.
Universe: real (non-helper) theorems with proof skeletons (script 77).

Neighborhood definitions, no winner chosen beforehand:
  ns      same namespace
  module  same module
  fam     same (area, conclusion head, nPi bucket)
  dep     dependency neighborhood: >=2 shared rare dependency targets
          (target document frequency over the scoped universe in [2,12])
  sem     semantic neighbors from the standing embedding nearest-neighbor file

Outputs:
  data/anomaly_base_order_algebra.jsonl  per-theorem group sizes + neighbors
  data/neighborhood_summary.json
"""
import json, os, re, math
from collections import Counter, defaultdict

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
DATA = os.path.join(ROOT, "data")
SCOPE = {"Order", "Algebra"}

def is_helper(name):
    return (name.startswith("_private") or "._proof_" in name
            or "._simp_" in name
            or re.search(r"\.eq_\d+$", name) is not None)

def area_of(module):
    if module.startswith("Mathlib."):
        return module.split(".")[1]
    return None

# ------------------------------------------------------------- universe
uni = {}   # name -> record
with open(os.path.join(DATA, "proof_skeletons_core.jsonl"), encoding="utf-8") as f:
    for line in f:
        r = json.loads(line)
        if r["area"] in SCOPE and not is_helper(r["name"]):
            uni[r["name"]] = {"name": r["name"], "module": r["module"],
                              "area": r["area"]}
# attach features
with open(os.path.join(DATA, "atlas_features.jsonl"), encoding="utf-8") as f:
    for line in f:
        r = json.loads(line)
        t = uni.get(r["name"])
        if t is not None:
            for k in ("namespace", "conclusionHead", "nPi", "kind",
                      "typeNodes", "typeDepth", "typeConsts", "typeDistinct",
                      "valueNodes", "valueDepth", "valueApps", "valueConsts",
                      "valueDistinct", "valueForalls", "valueLams",
                      "valueLets", "valueLits", "valueProjs", "valueIsRfl",
                      "caseRefs", "recRefs", "nameDepth", "nImplicit",
                      "nDefault", "nInstImplicit"):
                t[k] = r.get(k)
missing = [n for n, t in uni.items() if "conclusionHead" not in t]
print("universe:", len(uni), "without features:", len(missing))

# ------------------------------------------------------------- static groups
ns_g = Counter(); mod_g = Counter(); fam_g = Counter()
for t in uni.values():
    ns = t.get("namespace") or ""
    t["_ns"] = ns
    ns_g[ns] += 1
    mod_g[t["module"]] += 1
    fk = (t["area"], t.get("conclusionHead") or "",
          (t.get("nPi") or 0) // 2)
    t["_fam"] = fk
    fam_g[fk] += 1

# ------------------------------------------------------------- dependency neighborhood
# pass 1: target document frequency over scoped sources
df = Counter()
with open(os.path.join(DATA, "atlas_edges.jsonl"), encoding="utf-8") as f:
    for line in f:
        r = json.loads(line)
        if r["source"] in uni:
            df[r["target"]] += 1
rare = {t for t, c in df.items() if 2 <= c <= 12}
print("rare targets:", len(rare))
# pass 2: postings
post = defaultdict(list)
with open(os.path.join(DATA, "atlas_edges.jsonl"), encoding="utf-8") as f:
    for line in f:
        r = json.loads(line)
        if r["source"] in uni and r["target"] in rare:
            post[r["target"]].append(r["source"])
shared = defaultdict(Counter)
for tgt, srcs in post.items():
    srcs = list(set(srcs))
    for i in range(len(srcs)):
        for j in range(i + 1, len(srcs)):
            a, b = srcs[i], srcs[j]
            shared[a][b] += 1
            shared[b][a] += 1
dep_nbr = {}
for n, ctr in shared.items():
    dep_nbr[n] = [(m, c) for m, c in ctr.most_common(20) if c >= 2]

# ------------------------------------------------------------- semantic neighbors
sem_nbr = {}
with open(os.path.join(DATA, "embedding_nearest_neighbors.jsonl"),
          encoding="utf-8") as f:
    for line in f:
        r = json.loads(line)
        if r["name"] in uni:
            sem_nbr[r["name"]] = [(q["name"], round(q["cosine"], 4))
                                  for q in r["neighbors"][:10]
                                  if q["name"] in uni]

# ------------------------------------------------------------- write per-theorem rows
out = os.path.join(DATA, "anomaly_base_order_algebra.jsonl")
with open(out, "w", encoding="utf-8") as f:
    for t in uni.values():
        rec = {k: v for k, v in t.items() if not k.startswith("_")}
        rec["nNbrNamespace"] = ns_g[t["_ns"]]
        rec["nNbrModule"] = mod_g[t["module"]]
        rec["nNbrFamily"] = fam_g[t["_fam"]]
        rec["depNeighbors"] = dep_nbr.get(t["name"], [])
        rec["semNeighbors"] = sem_nbr.get(t["name"], [])
        f.write(json.dumps(rec, ensure_ascii=False) + "\n")

summary = {
    "scope": sorted(SCOPE),
    "theorems": len(uni),
    "areaCounts": dict(Counter(t["area"] for t in uni.values())),
    "namespaceGroups": len(ns_g), "moduleGroups": len(mod_g),
    "familyGroups": len(fam_g),
    "theoremsWithDepNeighbors": sum(1 for n in uni if dep_nbr.get(n)),
    "theoremsWithSemNeighbors": sum(1 for n in uni if sem_nbr.get(n)),
    "medianGroupSizes": {
        "namespace": sorted(ns_g.values())[len(ns_g)//2],
        "module": sorted(mod_g.values())[len(mod_g)//2],
        "family": sorted(fam_g.values())[len(fam_g)//2]}}
with open(os.path.join(DATA, "neighborhood_summary.json"), "w",
          encoding="utf-8") as f:
    json.dump(summary, f, ensure_ascii=False, indent=2)
print(json.dumps(summary, indent=2))
