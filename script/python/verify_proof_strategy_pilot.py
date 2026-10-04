#!/usr/bin/env python3
"""verify_proof_strategy_pilot.py — checks for scripts 75/76 (Order pilot)."""
import json, os, sys
from collections import Counter

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
DATA = os.path.join(ROOT, "data")
fails = []
def check(cond, msg):
    print(("PASS  " if cond else "FAIL  ") + msg)
    if not cond:
        fails.append(msg)

raw = [json.loads(l) for l in
       open(os.path.join(DATA, "proof_skeletons_order.jsonl"), encoding="utf-8")]
groups = [json.loads(l) for l in
          open(os.path.join(DATA, "proof_strategy_groups_order.jsonl"),
               encoding="utf-8")]
members = [json.loads(l) for l in
           open(os.path.join(DATA, "proof_strategy_members_order.jsonl"),
                encoding="utf-8")]
summary = json.load(open(os.path.join(DATA,
        "proof_strategy_summary_order.json"), encoding="utf-8"))

# raw extraction properties
check(all(set(r) == {"name", "module", "skeleton"} for r in raw),
      "skeleton rows have the required schema")
check(all(r["module"].startswith("Mathlib.Order") for r in raw),
      "all rows are Order modules")
check(len(raw) == 26828, "26,828 extracted skeletons")

# helper filtering
def is_helper(name):
    return (name.startswith("_private") or "._proof_" in name
            or "._simp_" in name)
real = [r for r in raw if not is_helper(r["name"])]
check(len(real) == summary["theorems"] == 17964,
      "17,964 real theorems after helper filter")
check(summary["excludedHelpers"] == len(raw) - len(real),
      "excluded helper count consistent")

# groups partition the real theorems
check(sum(g["size"] for g in groups) == len(real),
      "group sizes sum to theorem count")
check(len(members) == len(real), "one member row per real theorem")
mset = Counter(m["group"] for m in members)
check(all(mset[g["signature"]] == g["size"] for g in groups),
      "member rows match each group")
check(groups == sorted(groups, key=lambda g: -g["size"]),
      "groups sorted by size")

# the positive control: 41 Fin interval lemmas in one coarse group
fin = [g for g in groups if g["size"] == 41]
check(len(fin) == 1, "exactly one size-41 group")
g = fin[0]
ctrl_names = [m["name"] for m in members if m["group"] == g["signature"]]
required = ["Fin.image_succ_Ico", "Fin.image_castSucc_Icc",
            "Fin.finsetImage_succ_uIcc", "Fin.map_succEmb_Ico",
            "Fin.preimage_succ_Ico_succ", "Fin.image_castSucc_Ioo",
            "Fin.finsetImage_castSucc_Icc"]
check(all(n in ctrl_names for n in required),
      "positive control: all Fin interval families co-grouped")
check(len({m["module"].split(".")[3] if
           len(m["module"].split(".")) > 3 else m["module"]
           for m in members if m["group"] == g["signature"]}) >= 2,
      "control spans Set and Finset interval modules")

# secondary control: 28 dualEquiv category lemmas
dual = [g for g in groups if g["size"] == 28]
check(len(dual) == 1 and
      all("dualEquiv" in m["name"] or "Equiv" in m["name"]
          for m in members if m["group"] == dual[0]["signature"]),
      "secondary control: dualEquiv functor/inverse family grouped")

# REC presence (induction strategy is rare in Order)
rec_rows = [r for r in real if "REC" in r["skeleton"]]
check(len(rec_rows) > 0, "REC (induction/match) proofs present in corpus")

print()
if fails:
    print(f"{len(fails)} CHECK(S) FAILED")
    sys.exit(1)
print("ALL CHECKS PASSED")
