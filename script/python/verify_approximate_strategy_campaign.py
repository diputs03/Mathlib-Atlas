#!/usr/bin/env python3
"""verify_approximate_strategy_campaign.py — checks for scripts 86-90."""
import json, os, sys, re
from collections import Counter

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
DATA = os.path.join(ROOT, "data")
fails = []
def check(cond, msg):
    print(("PASS  " if cond else "FAIL  ") + msg)
    if not cond:
        fails.append(msg)

# 86 outputs
norm = [json.loads(l) for l in
        open(os.path.join(DATA, "proof_norm_core.jsonl"), encoding="utf-8")]
check(len(norm) == 166948, "86: 166,948 normalized real theorem trees")
check(all(set(r) >= {"name","module","area","norm","core"} for r in norm),
      "86: rows have norm + core layers")
def balanced(sexp):
    return sexp.count("(") == sexp.count(")")
check(all(balanced(r["norm"]) and balanced(r["core"]) for r in norm),
      "86: all trees balanced")
# core must not contain canonicalized leaves C/P (they were pruned)
check(not any(re.search(r"(^|\s)(C|P)(\s|$)", r["core"]) for r in norm),
      "86: core has no C/P leaves")

# 87 controls
ctrl = json.load(open(os.path.join(DATA, "positive_controls.json"),
                      encoding="utf-8"))
diag = ctrl["diagnostics"]
check(len(ctrl["families"]["Fin"]) == 73, "87: 73 Fin wrapper controls")
check(len(ctrl["families"]["Dual"]) == 32, "87: 32 dual controls")
check(diag["Fin"]["topCoreOutsiders"] == 0,
      "87: exact core produces no noise (and cannot reunite families)")

# 88 v2 outputs
summ = json.load(open(os.path.join(DATA, "proof_match_summary.json"),
                      encoding="utf-8"))
check(summ["theorems"] == 166948, "88: all theorems fingerprinted")
check(summ["matches"] == 550975, "88: 550,975 matches")
check(summ["crossAreaMatches"] == 264035, "88: 264,035 cross-area")
gate = summ["controlGate"]
check(gate["Fin"]["memberCoverage"] < 0.25
      and gate["Fin"]["outsiderRatio"] > 0.99,
      "88: gate fails — Fin family not reunited, component 99.9% outsiders")
check(gate["Dual"]["memberCoverage"] < 0.1,
      "88: gate fails — dual family not reunited")
check(gate["Twin"]["memberCoverage"] < 0.1,
      "88: gate fails — twin family not reunited")

# 89 characterization
char = json.load(open(os.path.join(DATA,
          "approx_match_characterization.json"), encoding="utf-8"))
check(char["allMatchMeanGenericFraction"] > 0.99,
      "89: >99% of shared tokens are generic idiom vocabulary")
check(char["sampleMeanGenericFractionCross"] > 0.99,
      "89: >99% generic in cross-area samples")
samples = [json.loads(l) for l in
           open(os.path.join(DATA, "approx_match_samples.jsonl"),
                encoding="utf-8")]
check(len(samples) == 90, "89: 90 adjudicated samples")
# samples are either generic idiom matches or the known option-tag family
TAG_PREFIX = ("OnePoint.", "WithTop.", "WithBot.", "WithZero.", "WithOne.")
def known_tag(s):
    return (s["rareShared"] == ["Ksome_injective"]
            and s["a"].startswith(TAG_PREFIX)
            and s["b"].startswith(TAG_PREFIX))
check(all(s["genericFractionOfShared"] >= 0.9 or known_tag(s)
          for s in samples),
      "89: samples are generic idioms or the known option-tag family; "
      "zero new cross-area strategy")

# outcome C recorded? (freeze note existence checked by caller)
print()
if fails:
    print(f"{len(fails)} CHECK(S) FAILED")
    sys.exit(1)
print("ALL CHECKS PASSED — outcome C: normalized proof representation")
print("is inadequate for cross-theory strategy discovery at this layer.")
