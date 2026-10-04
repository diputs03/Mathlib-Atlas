#!/usr/bin/env python3
"""71_rank_equiv_candidates.py — rank Equiv pairs for Lean falsification.

The gate question is narrow: is there a pair where
  (a) the Equiv genuinely identifies the two APIs (high transported-key
      coverage), yet
  (b) a substantial asymmetric residual remains on one side?

Score components:
  coverage  = matched keys / min(keys on either side)   [transport reality]
  gapRate   = one-sided decls / total footprint          [residual size]
  asymm     = |gapA-gapB| / (gapA+gapB)                  [one-sidedness]
  instCov   = shared instance classes / min(class sets)  [structure transport]
  uniform   = whether a uniform-family witness exists
  sep       = cross-namespace/module separation (derived from witness names)
  artifact  = alias/re-export/generated likelihood penalty (witness names)

Outputs:
  data/equiv_ranked.jsonl
  data/equiv_ranked_summary.json   (coverage distribution for the decision gate)
"""
import json, os, re

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
DATA = os.path.join(ROOT, "data")
COVERAGE_FLOOR = 0.35
TOPN = 30

rows = [json.loads(l) for l in
        open(os.path.join(DATA, "equiv_candidates.jsonl"), encoding="utf-8")]

out = []
for r in rows:
    min_keys = max(1, min(r["keysA"], r["keysB"]))
    coverage = r["matchedKeys"] / min_keys
    total_fp = r["footprintA"] + r["footprintB"]
    gap = r["gapDeclsA"] + r["gapDeclsB"]
    gap_rate = gap / total_fp
    asymm = abs(r["gapDeclsA"] - r["gapDeclsB"]) / max(1, gap)
    min_inst = max(1, min(len(r["instanceClassesA"]),
                          len(r["instanceClassesB"])))
    inst_cov = len(r["instanceShared"]) / min_inst
    # separation: witness modules vs carrier "home" modules approximated by
    # whether the two carrier names share a namespace prefix in witness set
    a, b = r["pair"]
    witness_ns = {w.split(".")[0] for w in r["witnesses"]}
    sep = 1.0 if len(witness_ns) >= 2 else 0.4
    # artifact penalty: witnesses that look like generated/alias machinery
    bad = 0
    for w in r["witnesses"]:
        last = w.split(".")[-1]
        if last.startswith("inst") or "refl" in last.lower() \
           or last in ("rfl",):
            bad += 1
    artifact = bad / max(1, len(r["witnesses"]))
    uniform = 1.0 if r["uniformWitnesses"] >= 1 else 0.0
    # final score: coverage is the gate; among covered pairs, reward a real,
    # one-sided, structure-level gap and separation; penalize artifacts.
    if coverage < COVERAGE_FLOOR:
        score = 0.10 * coverage
    else:
        score = (0.30 * coverage + 0.20 * min(1.0, gap_rate * 3)
                 + 0.15 * asymm + 0.10 * inst_cov + 0.10 * uniform
                 + 0.10 * sep + 0.05 * (1 - artifact))
    out.append(dict(score=round(score, 4), coverage=round(coverage, 3),
                    gapRate=round(gap_rate, 4), asymm=round(asymm, 3),
                    instCov=round(inst_cov, 3), uniform=uniform,
                    sep=sep, artifact=round(artifact, 2), **r))

out.sort(key=lambda x: -x["score"])
with open(os.path.join(DATA, "equiv_ranked.jsonl"), "w",
          encoding="utf-8") as f:
    for r in out:
        f.write(json.dumps(r, ensure_ascii=False) + "\n")

# coverage distribution = the evidence the decision gate needs
cov_buckets = {"0.00-0.10": 0, "0.10-0.35": 0, "0.35-0.60": 0,
               "0.60-0.85": 0, "0.85-1.00": 0, "1.00": 0}
for r in out:
    c = r["coverage"]
    if c >= 1.0:
        cov_buckets["1.00"] += 1
    elif c >= 0.85:
        cov_buckets["0.85-1.00"] += 1
    elif c >= 0.60:
        cov_buckets["0.60-0.85"] += 1
    elif c >= 0.35:
        cov_buckets["0.35-0.60"] += 1
    elif c >= 0.10:
        cov_buckets["0.10-0.35"] += 1
    else:
        cov_buckets["0.00-0.10"] += 1
n_gated = sum(1 for r in out if r["coverage"] >= COVERAGE_FLOOR)
summary = dict(totalPairs=len(out), coverageFloor=COVERAGE_FLOOR,
               pairsAboveFloor=n_gated, coverageBuckets=cov_buckets,
               top=[{k: r[k] for k in
                     ("score","coverage","gapRate","asymm","instCov",
                      "uniform","pair","matchedKeys","keysA","keysB",
                      "gapDeclsA","gapDeclsB","instanceGapA",
                      "instanceGapB","witnesses")}
                    for r in out[:TOPN]])
with open(os.path.join(DATA, "equiv_ranked_summary.json"), "w",
          encoding="utf-8") as f:
    json.dump(summary, f, ensure_ascii=False, indent=2)

print("coverage distribution:", cov_buckets)
print(f"pairs above {COVERAGE_FLOOR}: {n_gated} / {len(out)}")
for r in out[:20]:
    print(f"  {r['score']:.3f} cov={r['coverage']:.2f} gap={r['gapRate']:.3f} "
          f"asym={r['asymm']:.2f} inst={r['instCov']:.2f} u={r['uniform']:.0f} "
          f"{r['pair']} matched={r['matchedKeys']} gapD={r['gapDeclsA']}/"
          f"{r['gapDeclsB']}")
