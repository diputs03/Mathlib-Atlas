#!/usr/bin/env python3
"""81_local_anomaly_scorer.py — local anomaly vectors, v3 (percentile model).

v2 problems fixed: module-level robust z on heavy-tailed integer features
with tiny modules saturated the cap and produced 21k "anomalies".

v3 design:
  Stage A  compute raw per-theorem features (expensive edge/skeleton passes)
           and dump them so ranking reruns never rescan large files:
             data/anomaly_raw_order_algebra.jsonl
  Stage B  rank from the dump:
    - heavy-tailed sizes enter as log, converted to empirical percentiles
      over the scoped corpus (per area pooled with scope-wide fallback);
    - a dimension is a LOCAL anomaly only when the theorem is extreme
      globally (percentile >=0.95) AND its module peers are concentrated
      below 0.60 (median peer percentile);
    - dimensions without data (semantic coverage) are NA.

Outputs:
  data/anomaly_scored_order_algebra.jsonl
  data/anomaly_ranking_summary.json
"""
import json, os, re, math, sys
from collections import Counter, defaultdict

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
DATA = os.path.join(ROOT, "data")
RAW = os.path.join(DATA, "anomaly_raw_order_algebra.jsonl")

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

# =========================================================== STAGE A
if not os.path.exists(RAW):
    base = {}
    with open(os.path.join(DATA, "anomaly_base_order_algebra.jsonl"),
              encoding="utf-8") as f:
        for line in f:
            r = json.loads(line)
            base[r["name"]] = r
    sig_freq = defaultdict(Counter)
    own_sig = {}
    with open(os.path.join(DATA, "proof_skeletons_core.jsonl"),
              encoding="utf-8") as f:
        for line in f:
            r = json.loads(line)
            if r["name"] in base:
                sig = coarse(tok_re.findall(r["skeleton"]))
                own_sig[r["name"]] = sig
                sig_freq[r["area"]][sig] += 1
    df = Counter()
    with open(os.path.join(DATA, "atlas_edges.jsonl"), encoding="utf-8") as f:
        for line in f:
            r = json.loads(line)
            if r["source"] in base:
                df[r["target"]] += 1
    rare = {t for t, c in df.items() if 2 <= c <= 12}
    rare_count = Counter()
    with open(os.path.join(DATA, "atlas_edges.jsonl"), encoding="utf-8") as f:
        for line in f:
            r = json.loads(line)
            if r["source"] in base and r["target"] in rare:
                rare_count[r["source"]] += 1
    ns_in_mod = defaultdict(Counter)
    by_mod = defaultdict(list)
    for r in base.values():
        by_mod[r["module"]].append(r)
    for mod, rows in by_mod.items():
        for r in rows:
            ns_in_mod[mod][r.get("namespace") or ""] += 1
    with open(RAW, "w", encoding="utf-8") as f:
        for name, r in base.items():
            same = [c for nm, c in r.get("semNeighbors", [])]
            isolation = (1 - sum(same)/len(same)) if same else None
            rec = {"name": name, "module": r["module"], "area": r["area"],
                   "namespace": r.get("namespace"),
                   "conclusionHead": r.get("conclusionHead"),
                   "typeNodes": r.get("typeNodes"),
                   "typeDepth": r.get("typeDepth"),
                   "typeConsts": r.get("typeConsts"),
                   "valueNodes": r.get("valueNodes"),
                   "valueDepth": r.get("valueDepth"),
                   "rareTargets": rare_count.get(name, 0),
                   "nPi": r.get("nPi"),
                   "nInstImplicit": r.get("nInstImplicit"),
                   "rarity": 1.0/(1+sig_freq[r["area"]][own_sig[name]]),
                   "nsFraction": ns_in_mod[r["module"]]
                       [r.get("namespace") or ""]/len(by_mod[r["module"]]),
                   "isolation": isolation}
            f.write(json.dumps(rec, ensure_ascii=False) + "\n")
    print("stage A dumped", RAW)

# =========================================================== STAGE B
rows = [json.loads(l) for l in open(RAW, encoding="utf-8")]
by_mod = defaultdict(list)
for r in rows:
    by_mod[r["module"]].append(r)

def pct_fn(vals):
    vals = sorted(v for v in vals if v is not None)
    n = len(vals)
    def p(x):
        if x is None:
            return None
        lo, hi = 0, n
        while lo < hi:
            mid = (lo + hi)//2
            if vals[mid] < x:
                lo = mid+1
            else:
                hi = mid
        return lo/n
    return p

# percentile maps over scoped corpus (pooled; areas share scale)
p_type = pct_fn([math.log1p(r["typeNodes"] or 0) for r in rows])
p_proof = pct_fn([math.log1p(r["valueNodes"] or 0) for r in rows])
p_dep = pct_fn([r["rareTargets"] for r in rows])
p_gen = pct_fn([math.log1p(r["nPi"] or 0) for r in rows])
p_ns = pct_fn([r["nsFraction"] for r in rows])
p_sem = pct_fn([r["isolation"] for r in rows])

def axis(r, getraw, transform, pfun):
    g = pfun(transform(getraw(r)))
    if g is None:
        return None, None
    peers = [q for q in by_mod[r["module"]] if q["name"] != r["name"]]
    if len(peers) < 4:
        return None, g
    pg = sorted(v for v in
                (pfun(transform(getraw(q))) for q in peers)
                if v is not None)
    if not pg:
        return None, g
    peer_med = pg[len(pg)//2]
    if g >= 0.95 and peer_med <= 0.60:
        return min(10.0, 10*(g-0.95)/0.05), g
    return 0.0, g

scored = []
ident = lambda x: (x if x is not None else 0)
for r in rows:
    a = {}
    a["type"], g_t = axis(r, lambda q: q["typeNodes"],
        lambda x: math.log1p(x or 0), p_type)
    a["proof"], g_p = axis(r, lambda q: q["valueNodes"],
        lambda x: math.log1p(x or 0), p_proof)
    a["dependency"], g_d = axis(r, lambda q: q["rareTargets"], ident, p_dep)
    a["generality"], g_g = axis(r, lambda q: q["nPi"],
        lambda x: math.log1p(x or 0), p_gen)
    a["namespace"], g_n = axis(r, lambda q: q["nsFraction"], ident, p_ns)
    a["semantic"], g_s = axis(r, lambda q: q["isolation"], ident, p_sem)
    present = {d: round(v, 2) for d, v in a.items() if v}
    na = [d for d, v in a.items() if v is None]
    high = [d for d, v in present.items() if v >= 3]
    mild = [d for d, v in present.items() if 1.5 <= v < 3]
    if present:
        maxDim = max(present, key=present.get)
        scored.append({"name": r["name"], "module": r["module"],
                       "area": r["area"], "namespace": r["namespace"],
                       "conclusionHead": r["conclusionHead"],
                       "anomaly": present, "naDims": na, "highDims": high,
                       "singleDimAnomaly": len(high)==1 and len(mild)==0,
                       "maxDim": maxDim,
                       "maxScore": round(present[maxDim], 3)})
scored.sort(key=lambda r: -r["maxScore"])
with open(os.path.join(DATA, "anomaly_scored_order_algebra.jsonl"), "w",
          encoding="utf-8") as f:
    for r in scored:
        f.write(json.dumps(r, ensure_ascii=False) + "\n")
dims = ["type","proof","dependency","generality","namespace","semantic"]
summary = {"theorems": len(rows),
           "withAnyLocalAnomaly": len(scored),
           "singleDimAnomalies": sum(r["singleDimAnomaly"] for r in scored),
           "perDimHigh": {d: sum(1 for r in scored if d in r["highDims"])
                          for d in dims},
           "perDimNA": {d: sum(1 for r in rows
                        if d in [x for x in []]) for d in dims},
           "top": [{"name": r["name"], "area": r["area"],
                    "dim": r["maxDim"], "score": r["maxScore"],
                    "module": r["module"], "anomaly": r["anomaly"]}
                   for r in scored[:40]]}
with open(os.path.join(DATA, "anomaly_ranking_summary.json"), "w",
          encoding="utf-8") as f:
    json.dump(summary, f, ensure_ascii=False, indent=2)
print(json.dumps({k: summary[k] for k in
                  ("theorems","withAnyLocalAnomaly","singleDimAnomalies",
                   "perDimHigh")}, indent=2))
