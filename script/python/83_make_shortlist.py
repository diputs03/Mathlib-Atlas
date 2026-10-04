import json, os
from collections import defaultdict
ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
DATA = os.path.join(ROOT, "data")
rows = [json.loads(l) for l in
        open(os.path.join(DATA, "anomaly_scored_order_algebra.jsonl"),
             encoding="utf-8")]
by_dim = defaultdict(list)
for r in rows:
    if r["singleDimAnomaly"]:
        by_dim[r["maxDim"]].append(r)
short = []
for d in ("type", "proof", "dependency", "generality", "semantic"):
    short.extend(by_dim[d][:14])
with open(os.path.join(DATA, "anomaly_adjudication_shortlist.jsonl"), "w",
          encoding="utf-8") as f:
    for r in short:
        f.write(json.dumps(r, ensure_ascii=False) + "\n")
for d in ("type", "proof", "dependency", "generality", "semantic"):
    print(f"\n######## {d} ########")
    for r in by_dim[d][:14]:
        print(f"  {r['maxScore']:5} {r['name']}")
        print(f"        {r['module']}  {r['anomaly']}")
