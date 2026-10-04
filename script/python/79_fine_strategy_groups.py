#!/usr/bin/env python3
"""79_fine_strategy_groups.py — cross-area strategy sharing at the fine level.

Fine signature: keep the full proof tree and every named constant (K tokens
kept verbatim); erase only variables (B/F -> V), instances (INST -> I),
projection indices (Jn -> J), literal values (Ln/Ls -> L).

Two theorems share a fine signature when they apply the same named lemmas in
the same arrangement up to variable/instantiation choices.

Outputs:
  data/strategy_fine_groups.jsonl   (multi-area groups only)
  data/strategy_fine_summary.json
"""
import json, os, re
from collections import Counter, defaultdict

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
DATA = os.path.join(ROOT, "data")
AREAS = ["Algebra", "Analysis", "Data", "FieldTheory", "GroupTheory",
         "LinearAlgebra", "Logic", "Order", "RingTheory", "Topology"]

tok_re = re.compile(r"[()]|[^\s()]+")
def fine(tokens):
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
        else:
            out.append(t)   # K tokens and structure kept verbatim
    return " ".join(out)

def is_helper(name):
    return (name.startswith("_private") or "._proof_" in name
            or "._simp_" in name
            or re.search(r"\.eq_\d+$", name) is not None)

groups = defaultdict(Counter)
members = defaultdict(list)
n = 0
with open(os.path.join(DATA, "proof_skeletons_core.jsonl"), encoding="utf-8") as f:
    for line in f:
        r = json.loads(line)
        if is_helper(r["name"]):
            continue
        sig = fine(tok_re.findall(r["skeleton"]))
        groups[sig][r["area"]] += 1
        if len(members[sig]) < 12:
            members[sig].append((r["area"], r["name"], r["module"]))
        n += 1

multi = []
for sig, ac in groups.items():
    if len(ac) > 1:
        total = sum(ac.values())
        multi.append(dict(signature=sig, size=total, areas=dict(ac),
                          members=members[sig]))
multi.sort(key=lambda g: -g["size"])

with open(os.path.join(DATA, "strategy_fine_groups.jsonl"), "w",
          encoding="utf-8") as f:
    for g in multi:
        f.write(json.dumps(g, ensure_ascii=False) + "\n")

cross_area_pairs = Counter()
for g in multi:
    present = list(g["areas"])
    for i in range(len(present)):
        for j in range(i + 1, len(present)):
            cross_area_pairs[tuple(sorted((present[i], present[j])))] += 1

summary = dict(theorems=n, fineGroups=len(groups),
               crossAreaGroups=len(multi),
               crossAreaGroupSizes=Counter(str(g["size"]) for g in multi),
               topAreaPairs=[{"pair": list(p), "groups": c}
                             for p, c in cross_area_pairs.most_common(15)],
               topGroups=[{"size": g["size"], "areas": g["areas"],
                           "signature": g["signature"][:300]}
                          for g in multi[:20]])
with open(os.path.join(DATA, "strategy_fine_summary.json"), "w",
          encoding="utf-8") as f:
    json.dump(summary, f, ensure_ascii=False, indent=2)

print(json.dumps({k: summary[k] for k in
                  ("theorems", "fineGroups", "crossAreaGroups")}, indent=2))
print("\nTop area pairs:", summary["topAreaPairs"][:10])
for g in multi[:10]:
    print(f"\n--- size {g['size']} areas {g['areas']}")
    print("   ", g["signature"][:200])
    for a, nm, m in g["members"][:8]:
        print("    ", a, m.replace("Mathlib.", ""), "::", nm)
