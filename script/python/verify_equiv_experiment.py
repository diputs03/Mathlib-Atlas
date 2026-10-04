#!/usr/bin/env python3
"""verify_equiv_experiment.py — independent checks for scripts 70-74 outputs."""
import json, os, sys
from collections import Counter

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
DATA = os.path.join(ROOT, "data")
NOTES = os.path.join(ROOT, "notes")
fails = []
def check(cond, msg):
    print(("PASS  " if cond else "FAIL  ") + msg)
    if not cond:
        fails.append(msg)

files = ["equiv_candidate_summary.json", "equiv_ranked.jsonl",
         "equiv_ranked_summary.json", "equiv_candidates.jsonl",
         "equiv_gap_declarations.jsonl", "equiv_adjudication.jsonl",
         "equiv_adjudication_summary.json"]
for f in files:
    p = os.path.join(DATA, f)
    check(os.path.exists(p) and os.path.getsize(p) > 0, f"exists & nonempty: {f}")

cand = [json.loads(l) for l in open(os.path.join(DATA, "equiv_candidates.jsonl"), encoding="utf-8")]
ranked = [json.loads(l) for l in open(os.path.join(DATA, "equiv_ranked.jsonl"), encoding="utf-8")]
adj = [json.loads(l) for l in open(os.path.join(DATA, "equiv_adjudication.jsonl"), encoding="utf-8")]
gaps = [json.loads(l) for l in open(os.path.join(DATA, "equiv_gap_declarations.jsonl"), encoding="utf-8")]
csum = json.load(open(os.path.join(DATA, "equiv_candidate_summary.json"), encoding="utf-8"))
asum = json.load(open(os.path.join(DATA, "equiv_adjudication_summary.json"), encoding="utf-8"))

check(len(cand) == len(ranked) == len(adj) == csum["eligiblePairs"],
      f"candidate/ ranked/ adjudication counts agree ({len(cand)})")

# adjudication counts consistent and exhaustive
c = Counter(r["cls"] for r in adj)
check(sum(c.values()) == len(adj), "adjudication classes exhaustive")
check(dict(c) == {k: v for k, v in asum["counts"].items() if v},
      "adjudication summary counts match rows")

# every manually adjudicated pair carries source evidence
manual_pairs = {("CStarMatrix","Matrix"), ("ConnectedComponents","ZerothHomotopy"),
                ("MaximalSpectrum","PrimeSpectrum"), ("MaximalSpectrum","Subtype"),
                ("Prod","RegularWreathProduct"), ("BotHom","TopHom"),
                ("OrderAddMonoidIso","OrderMonoidIso"), ("PSigma","Sigma"),
                ("InfTopHom","SupBotHom"), ("sInfHom","sSupHom"),
                ("InfHom","SupHom"), ("WithBot","WithTop"),
                ("MonoidHom","ShelfHom")}
seen = set(); notes_ok = True
for r in adj:
    k = tuple(sorted(r["pair"]))
    if k in manual_pairs:
        seen.add(k)
        if not r["note"] or r["rule"] != "manual source adjudication":
            notes_ok = False
check(seen == manual_pairs, "all manual pairs adjudicated")
check(notes_ok, "manual pairs carry nonempty source evidence")

# ranking: scores sorted, coverage components consistent
sorted_ok = all(ranked[i]["score"] >= ranked[i+1]["score"]
                for i in range(len(ranked)-1))
check(sorted_ok, "ranked file sorted by score")
cov_ok = all(0.0 <= r["coverage"] <= 1.0 for r in ranked)
check(cov_ok, "coverage values within [0,1]")

# gap declarations: sides/names consistent, cap respected
cap = csum["params"]["GAP_CAP"]
per_pair = Counter((tuple(r["pair"])) for r in gaps)
check(all(n <= cap for n in per_pair.values()), "gap rows per pair within cap")
pair_set = {tuple(r["pair"]) for r in cand}
check(all(tuple(r["pair"]) in pair_set for r in gaps),
      "gap rows reference emitted pairs")
check(all(r["side"] in ("A","B") for r in gaps), "gap sides valid")

# Lean falsification: zero-byte log
p = os.path.join(NOTES, "72_equiv_transport.log")
check(os.path.exists(p) and os.path.getsize(p) == 0,
      "Lean falsification log is zero bytes")

# the decision-gate null claim: no missing generic mechanism / lemma
check(c.get("missing_generic_abstraction", 0) == 0,
      "null: zero missing_generic_abstraction")
check(c.get("missing_transport_lemma", 0) == 0,
      "null: zero missing_transport_lemma")

print()
if fails:
    print(f"{len(fails)} CHECK(S) FAILED")
    sys.exit(1)
print("ALL CHECKS PASSED")
