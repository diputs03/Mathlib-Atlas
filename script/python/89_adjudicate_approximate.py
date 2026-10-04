#!/usr/bin/env python3
"""89_adjudicate_approximate.py — bounded adjudication of the v2 result.

Characterizes what the 551k matches consist of and supplies top/random
cross-area samples for source inspection.
Outputs:
  data/approx_match_characterization.json
  data/approx_match_samples.jsonl   (top 50 + random 40 cross-area)
"""
import json, os, re, random
from collections import Counter, defaultdict

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
DATA = os.path.join(ROOT, "data")
random.seed(89)

norm = {}
for l in open(os.path.join(DATA, "proof_norm_core.jsonl"), encoding="utf-8"):
    r = json.loads(l)
    norm[r["name"]] = r

# document frequency of tokens over core strings (cheap; no tree parse)
df = Counter()
for r in norm.values():
    toks = {t for t in r["core"].split()
            if t not in ("(", ")")}
    for t in toks:
        df[t] += 1
GENERIC_DF = 100   # token seen in >=100 proofs = common idiom vocabulary

matches = [json.loads(l) for l in
           open(os.path.join(DATA, "proof_matches.jsonl"), encoding="utf-8")]
cross = [m for m in matches if m["crossArea"]]
print("matches", len(matches), "cross", len(cross))

def shared_generic(m):
    r1, r2 = norm[m["a"]], norm[m["b"]]
    t1 = set(r1["core"].split()) - {"(", ")"}
    t2 = set(r2["core"].split()) - {"(", ")"}
    sh = t1 & t2
    if not sh:
        return 1.0, []
    gen = {t for t in sh if not t.startswith("K") or df[t] >= GENERIC_DF}
    return len(gen)/len(sh), sorted(sh - gen)

# score distribution
buckets = Counter()
for m in matches:
    buckets = buckets
    s = m["score"]
    key = "0.95+" if s >= .95 else "0.90" if s >= .90 \
        else "0.85" if s >= .85 else "0.80" if s >= .80 else "0.75"
    buckets[key] += 1

# sample: top 50 cross + 40 random cross
top = cross[:50]
rnd = random.sample(cross, 40)
sample = top + rnd
generic_frac = []
rare_shared_counts = Counter()
with open(os.path.join(DATA, "approx_match_samples.jsonl"), "w",
          encoding="utf-8") as f:
    for m in sample:
        gf, rare = shared_generic(m)
        generic_frac.append(gf)
        for t in rare:
            rare_shared_counts[t] += 1
        rec = dict(m)
        rec["genericFractionOfShared"] = round(gf, 3)
        rec["rareShared"] = rare[:12]
        f.write(json.dumps(rec, ensure_ascii=False) + "\n")

# global estimate on a 400-pair random sample of ALL matches
est = random.sample(matches, 400)
gfall = [shared_generic(m)[0] for m in est]
char = {"matches": len(matches), "crossArea": len(cross),
        "scoreBuckets": dict(buckets),
        "sampleMeanGenericFractionCross": round(sum(generic_frac)
                                                /len(generic_frac), 3),
        "allMatchMeanGenericFraction": round(sum(gfall)/len(gfall), 3),
        "topRareSharedInCrossSample": rare_shared_counts.most_common(20)}
json.dump(char, open(os.path.join(DATA,
          "approx_match_characterization.json"), "w", encoding="utf-8"),
          ensure_ascii=False, indent=1)
print(json.dumps(char, indent=1))
