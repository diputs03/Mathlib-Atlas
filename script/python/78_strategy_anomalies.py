#!/usr/bin/env python3
"""78_strategy_anomalies.py — cross-area proof-strategy anomaly ranking.

For every theorem in the core corpus compute its coarse strategy signature
(script-76 normalization). For each signature record the area distribution.

Anomaly classes emitted:
  exported_strategy   a signature dominated by area X (>=70%, >=12 members)
                      with a small number of members in a different area Y:
                      a strategy common in X occurring inside Y.
  shared_strategy_pair area pairs with unusually high overlap in signatures,
                      weighted by signature rarity (rare shared shapes count
                      more).
  within_area_outlier  theorems whose signature's dominant area is not their
                      own (the per-theorem view of exported strategies).

Outputs:
  data/strategy_exported.jsonl
  data/strategy_area_overlap.json
  data/strategy_outliers.jsonl
  data/strategy_anomaly_summary.json
"""
import json, os, math, re
from collections import Counter, defaultdict

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
DATA = os.path.join(ROOT, "data")
AREAS = ["Algebra", "Analysis", "Data", "FieldTheory", "GroupTheory",
         "LinearAlgebra", "Logic", "Order", "RingTheory", "Topology"]

tok_re = re.compile(r"[()]|[^\s()]+")
def coarse(tokens):
    out = []
    for t in tokens:
        if t == "(" or t == ")":
            out.append(t)
        elif t in ("B", "F"):
            out.append("V")
        elif t == "INST":
            out.append("I")
        elif re.fullmatch(r"\(J\d+", t):
            out.append("(J")
        elif len(t) == 2 and t[0] == "L" and t[1] in "ns":
            out.append("L")
        elif t.startswith("K"):
            out.append("K")
        else:
            out.append(t)
    return " ".join(out)

def is_helper(name):
    return (name.startswith("_private") or "._proof_" in name
            or "._simp_" in name
            or re.search(r"\.eq_\d+$", name) is not None)

# ------------------------------------------------------------- pass 1: groups
group_areas = defaultdict(Counter)
group_members = defaultdict(list)
area_sigs = {a: set() for a in AREAS}
n = 0
with open(os.path.join(DATA, "proof_skeletons_core.jsonl"), encoding="utf-8") as f:
    for line in f:
        r = json.loads(line)
        if is_helper(r["name"]):
            continue
        sig = coarse(tok_re.findall(r["skeleton"]))
        group_areas[sig][r["area"]] += 1
        if len(group_members[sig]) < 6:
            group_members[sig].append((r["area"], r["name"], r["module"]))
        area_sigs[r["area"]].add(sig)
        n += 1

# ------------------------------------------------------------- exported strategies
exported = []
outliers = []
for sig, ac in group_areas.items():
    total = sum(ac.values())
    if total < 4:
        continue
    dom, domn = ac.most_common(1)[0]
    dom_frac = domn / total
    if total >= 12 and dom_frac >= 0.70 and len(ac) > 1:
        others = {a: c for a, c in ac.items() if a != dom}
        rec = dict(signature=sig, dominantArea=dom, dominantFrac=dom_frac,
                   size=total, others=others,
                   members=group_members[sig])
        exported.append(rec)
        for area, name, mod in group_members[sig]:
            if area != dom:
                outliers.append(dict(name=name, module=mod, area=area,
                                     dominantArea=dom, size=total,
                                     signature=sig))

# score: rarity of the strategy elsewhere + size + dominance purity
for rec in exported:
    rec["score"] = (math.log(1 + rec["size"]) * rec["dominantFrac"]
                    * sum(rec["others"].values()))
exported.sort(key=lambda r: -r["score"])
outliers.sort(key=lambda r: -r["size"])

# ----------------------------------------------- area overlap (rare signatures)
# document frequency per signature
df = Counter()
for sig, ac in group_areas.items():
    df[sig] = len(ac)
overlap = {a: {} for a in AREAS}
for sig, ac in group_areas.items():
    present = list(ac)
    w = 1.0 / (1 + sum(group_areas[sig].values()))  # rare shapes weigh more
    for i in range(len(present)):
        for j in range(i + 1, len(present)):
            x, y = present[i], present[j]
            overlap[x][y] = overlap[x].get(y, 0) + w
            overlap[y][x] = overlap[y].get(x, 0) + w

# ------------------------------------------------------------- write
with open(os.path.join(DATA, "strategy_exported.jsonl"), "w",
          encoding="utf-8") as f:
    for r in exported:
        f.write(json.dumps(r, ensure_ascii=False) + "\n")
with open(os.path.join(DATA, "strategy_outliers.jsonl"), "w",
          encoding="utf-8") as f:
    for r in outliers:
        f.write(json.dumps(r, ensure_ascii=False) + "\n")
with open(os.path.join(DATA, "strategy_area_overlap.json"), "w",
          encoding="utf-8") as f:
    json.dump(overlap, f, ensure_ascii=False, indent=2)

area_counts = Counter()
for sig, ac in group_areas.items():
    for a, c in ac.items():
        area_counts[a] += c
summary = dict(theorems=n, coarseGroups=len(group_areas),
               exportedStrategyGroups=len(exported),
               outlierTheorems=len(outliers),
               areaTheorems=dict(area_counts),
               topOverlap=[])
for a in AREAS:
    for b, w in sorted(overlap[a].items(), key=lambda x: -x[1])[:3]:
        summary["topOverlap"].append({"areas": [a, b], "weight": round(w, 2)})
with open(os.path.join(DATA, "strategy_anomaly_summary.json"), "w",
          encoding="utf-8") as f:
    json.dump(summary, f, ensure_ascii=False, indent=2)

print(json.dumps({k: summary[k] for k in
                  ("theorems", "coarseGroups", "exportedStrategyGroups",
                   "outlierTheorems")}, indent=2))
print("\nTop overlap pairs:")
seen = set()
for a in AREAS:
    for b, w in sorted(overlap[a].items(), key=lambda x: -x[1])[:2]:
        k = tuple(sorted((a, b)))
        if k not in seen:
            seen.add(k)
            print(f"  {k[0]:15s} ~ {k[1]:15s} {w:8.1f}")
print("\nTop exported-strategy groups:")
for r in exported[:12]:
    print(f"  score {r['score']:6.2f} size {r['size']:4d} "
          f"dom {r['dominantArea']:12s} others {r['others']}")
