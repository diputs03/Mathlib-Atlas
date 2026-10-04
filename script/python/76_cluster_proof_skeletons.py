#!/usr/bin/env python3
"""76_cluster_proof_skeletons.py — cluster Order proof skeletons by strategy.

Two-level grouping:
  coarse signature: erase lemma identity (Kxxx -> K), variables (B/F -> V),
    instances (INST -> I), projections (Jn -> J), literals (Ln/Ls -> L);
    keep the full tree structure. Identical coarse signatures = the same
    proof shape up to which named lemmas are used.
  within each coarse group: sub-signature keeps the ordered Kxxx tokens
    (which named lemmas are applied) — distinguishes genuinely shared
    derivations from shape-only coincidences.

Outputs:
  data/proof_strategy_groups_order.jsonl   (one row per coarse group)
  data/proof_strategy_members_order.jsonl  (members with sub-key)
  data/proof_strategy_summary_order.json
"""
import json, os, re
from collections import Counter, defaultdict

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
DATA = os.path.join(ROOT, "data")

rows = [json.loads(l) for l in
        open(os.path.join(DATA, "proof_skeletons_order.jsonl"), encoding="utf-8")]

def is_helper(name):
    return (name.startswith("_private") or "._proof_" in name
            or "._simp_" in name)

excluded_helpers = sum(1 for r in rows if is_helper(r["name"]))
rows = [r for r in rows if not is_helper(r["name"])]

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
        elif t.startswith("(J") or t.startswith("J") and t[1:].isdigit():
            out.append("J")
        elif t in ("Ln", "Ls") or (len(t) == 2 and t[0] == "L" and
                                    t[1] in "ns"):
            out.append("L")
        elif t.startswith("K"):
            out.append("K")
        else:
            out.append(t)
    return " ".join(out)

def named_seq(tokens):
    """ordered sequence of named-lemma tokens (strategy's lemma chain)."""
    return tuple(t for t in tokens if t.startswith("K"))

groups = defaultdict(list)
for r in rows:
    toks = tok_re.findall(r["skeleton"])
    c = coarse(toks)
    groups[c].append((r, named_seq(toks)))

# build group records
grecs = []
members = []
for sig, mem in groups.items():
    sub = Counter(s for _, s in mem)
    nmod = len({r["module"].split(".")[2] if len(r["module"].split(".")) > 2
                 else r["module"] for r, _ in mem})
    grecs.append(dict(
        signature=sig, size=len(mem), nSubKeys=len(sub),
        nModules=nmod,
        depth=sig.count("("),
        topSubKeys=[{"key": list(k), "count": n}
                    for k, n in sub.most_common(5)]))
    for (r, s) in mem:
        members.append(dict(group=sig, name=r["name"], module=r["module"],
                            subKey=list(s)))
grecs.sort(key=lambda g: -g["size"])

with open(os.path.join(DATA, "proof_strategy_groups_order.jsonl"), "w",
          encoding="utf-8") as f:
    for g in grecs:
        f.write(json.dumps(g, ensure_ascii=False) + "\n")
with open(os.path.join(DATA, "proof_strategy_members_order.jsonl"), "w",
          encoding="utf-8") as f:
    for m in members:
        f.write(json.dumps(m, ensure_ascii=False) + "\n")

sizes = Counter()
for g in grecs:
    if g["size"] == 1:
        sizes["singleton"] += 1
    elif 2 <= g["size"] <= 4:
        sizes["2-4"] += 1
    elif 5 <= g["size"] <= 20:
        sizes["5-20"] += 1
    elif 21 <= g["size"] <= 100:
        sizes["21-100"] += 1
    else:
        sizes[">100"] += 1
summary = dict(theorems=len(rows), excludedHelpers=excluded_helpers,
               coarseGroups=len(grecs),
               sizeBins=dict(sizes),
               multiMemberGroups=sum(1 for g in grecs if g["size"] > 1),
               top20=[{"size": g["size"], "nSubKeys": g["nSubKeys"],
                       "nModules": g["nModules"],
                       "signature": g["signature"][:300]}
                      for g in grecs[:20]])
with open(os.path.join(DATA, "proof_strategy_summary_order.json"), "w",
          encoding="utf-8") as f:
    json.dump(summary, f, ensure_ascii=False, indent=2)

print(json.dumps({k: summary[k] for k in
                  ("theorems", "coarseGroups", "multiMemberGroups",
                   "sizeBins")}, indent=2))
for g in grecs[:15]:
    print(f"\n--- size {g['size']:5d}  subkeys {g['nSubKeys']:5d}  "
          f"modules {g['nModules']}")
    print("   ", g["signature"][:220])
