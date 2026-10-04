#!/usr/bin/env python3
"""87_positive_controls.py — define known same-strategy families and test
whether normalized trees reunite them.

Controls (same strategy, different exact skeletons):
  F  Fin interval family (Fin-specific interval image/map/preimage proofs;
     the campaign that split into 41 fine keys in script 79)
  D  bundled order category dualEquiv functor/inverse lemmas (28 in 76)
  T  to_additive twins: additive/multiplicative name pairs present in the
     corpus (sanity control — proofs must be identical)

Output:
  data/positive_controls.json  — member lists + exact-match diagnostics
The pass/fail gate (reunited without flooding noise) is evaluated after
the approximate matcher in 88; this script supplies ground truth.
"""
import json, os, re
from collections import Counter, defaultdict

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
DATA = os.path.join(ROOT, "data")

rows = {}
for l in open(os.path.join(DATA, "proof_norm_core.jsonl"), encoding="utf-8"):
    r = json.loads(l)
    rows[r["name"]] = r

# ---- Fin interval family: Fin-specific wrapper proofs (73). These wrap a
# generic addNat/castAdd interval lemma with Fin coercions; they split
# into 41 fine keys in script 79 despite one strategy. ----
wrap_re = re.compile(r"(castSucc|valEmbedding|sectL|revPerm|preimage_rev)",
                     re.I)
fin_fam = set()
for n, r in rows.items():
    if "Interval" in r["module"] and wrap_re.search(n):
        fin_fam.add(n)

# ---- dualEquiv category family ----
dual_fam = {n for n, r in rows.items()
            if "dualEquiv" in n and r["area"] == "Order"}

# ---- to_additive twins: pair names by simple Add<->Mul translation ----
def twin(n):
    table = [("AddEquiv", "MulEquiv"), ("addEquiv", "mulEquiv"),
             ("AddMonoid", "Monoid"), ("AddComm", "Comm"),
             ("toAdditive", "toMultiplicative"), ("Add", "Mul")]
    for a, b in table:
        if a in n:
            cand = n.replace(a, b)
            if cand in rows and cand != n:
                return cand
    return None
twin_pairs = []
seen = set()
for n in rows:
    t = twin(n)
    if t and (t, n) not in seen:
        seen.add((n, t))
        twin_pairs.append([n, t])

families = {"Fin": sorted(fin_fam), "Dual": sorted(dual_fam),
            "Twin": sorted(x for p in twin_pairs for x in p)}

# ---- exact-match diagnostics on core and norm ----
def diagnostics(members):
    members = set(members)
    core_groups = Counter(r["core"] for n, r in rows.items() if n in members)
    # noise: outsiders sharing the family's most common core key
    top_key, top_n = core_groups.most_common(1)[0]
    outsiders = sum(1 for n, r in rows.items()
                    if r["core"] == top_key and n not in members)
    norm_groups = Counter(r["norm"] for n, r in rows.items() if n in members)
    return {"members": len(members),
            "distinctCore": len(core_groups),
            "topCoreShare": round(top_n/len(members), 3),
            "topCoreOutsiders": outsiders,
            "distinctNorm": len(norm_groups)}

result = {f: diagnostics(m) for f, m in families.items()}
result["twinPairCount"] = len(twin_pairs)
result["twinPairsAllIdenticalCore"] = all(
    rows[a]["core"] == rows[b]["core"] for a, b in twin_pairs)
with open(os.path.join(DATA, "positive_controls.json"), "w",
          encoding="utf-8") as f:
    json.dump({"families": families, "diagnostics": result}, f,
              ensure_ascii=False, indent=1)
print(json.dumps(result, indent=1))
print("\nFin family sample:", sorted(fin_fam)[:8])
print("Dual family sample:", sorted(dual_fam)[:8])
