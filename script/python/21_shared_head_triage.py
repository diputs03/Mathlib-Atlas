#!/usr/bin/env python3
"""21_shared_head_triage.py — second-stage triage of the script-19
`shared_head_analogy` communities.

A shared conclusion head is usually NOT a missing abstraction; it is one of:
  head_api           most members live in the head's own namespace
                     (AddHom.comp, Set.InvOn.mono, PullbackCone.flip, ...):
                     the head's already-generic API.
  bundled_witness    external carriers each supply a *witness* of the head
                     (X.equivalence : Equivalence R, gi : GaloisInsertion ...),
                     with a uniform suffix and small proof terms -> trivial
                     bundles through the head's generic constructor.
  repeated_proof     external carriers, uniform suffix, but LARGE proof terms
                     (median valueNodes high): the same non-trivial argument is
                     re-derived per carrier -- the real candidate list.
  mixed              anything else.

Pure Python, deterministic.
Inputs : data/community_triage.jsonl (shared_head rows),
         data/analogy_cluster_assignment.jsonl, data/atlas_features.jsonl
Outputs: data/shared_head_triage.jsonl, data/shared_head_triage_summary.json
"""
import json, os, collections, statistics, time

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
DATA = os.path.join(ROOT, "data")
def P(n): return os.path.join(DATA, n)
def log(m): print(f"[{time.strftime('%H:%M:%S')}] {m}", flush=True)
def suffix(n): return n.rsplit(".", 1)[-1]
def carrier(n):
    p = n.rsplit(".", 1); return p[0] if len(p) == 2 else ""

sha = [json.loads(l) for l in open(P("community_triage.jsonl"), "rb")]
sha = [r for r in sha if r["status"] == "shared_head_analogy"]
members_of = collections.defaultdict(list)
for line in open(P("analogy_cluster_assignment.jsonl"), "rb"):
    r = json.loads(line); members_of[r["cluster"]].append(r["name"])
need = {n for r in sha for n in members_of[r["clusterId"]]}
feat = {}
for line in open(P("atlas_features.jsonl"), "rb"):
    r = json.loads(line)
    if r["name"] in need:
        feat[r["name"]] = (r.get("valueNodes", 0) or 0, r.get("valueDepth", 0) or 0)
log(f"{len(sha)} shared_head communities; {len(feat)} member features")

# A bundled witness is small: constructor + a handful of field proofs.
BUNDLE_NODE_CAP = 25      # median valueNodes at/below which witnesses are trivial
rows = []
cnt = collections.Counter()
for r in sha:
    cid = r["clusterId"]; mem = sorted(members_of[cid])
    heads = r["headAnchors"]
    head_last = heads[0].rsplit(".", 1)[-1] if heads else ""
    api, ext = [], []
    for m in mem:
        tail = carrier(m).rsplit(".", 1)[-1]
        (api if tail == head_last else ext).append(m)
    frac_api = len(api) / len(mem)
    suf = collections.Counter(suffix(m) for m in ext)
    ext_suf, ext_suf_n = (suf.most_common(1)[0] if suf else ("", 0))
    ext_suf_cov = ext_suf_n / len(ext) if ext else 0.0
    nodes = [feat.get(m, (0, 0))[0] for m in ext]
    med_nodes = statistics.median(nodes) if nodes else 0

    if frac_api >= 0.5:
        sub = "head_api"
    elif ext and ext_suf_cov >= 0.5:
        sub = "bundled_witness" if med_nodes <= BUNDLE_NODE_CAP else "repeated_proof"
    else:
        sub = "mixed"
    cnt[sub] += 1
    rows.append({
        "clusterId": cid, "subStatus": sub, "head": heads[0] if heads else "",
        "size": len(mem), "nAreas": r["nAreas"], "areas": r["areas"],
        "apiFrac": round(frac_api, 3), "nExternal": len(ext),
        "externalSuffix": {"suffix": ext_suf, "coverage": round(ext_suf_cov, 3)},
        "medianValueNodes": med_nodes,
        "score": round(len(ext) * r["nAreas"] * ext_suf_cov, 2),
        "externalMembers": ext[:24],
    })

rank = {"repeated_proof": 0, "mixed": 1, "bundled_witness": 2, "head_api": 3}
rows.sort(key=lambda r: (rank[r["subStatus"]], -r["score"], -r["size"]))
with open(P("shared_head_triage.jsonl"), "wb") as o:
    for r in rows:
        o.write((json.dumps(r, ensure_ascii=False) + "\n").encode("utf-8"))

def topN(sub, k=20):
    out = []
    for r in rows:
        if r["subStatus"] == sub:
            out.append({k2: r[k2] for k2 in
                        ("clusterId", "head", "size", "nAreas", "apiFrac",
                         "externalSuffix", "medianValueNodes", "score")})
            if len(out) >= k: break
    return out
summary = {"sharedHeadCommunities": len(rows), "bySubStatus": dict(cnt),
           "repeatedProof": topN("repeated_proof"),
           "mixed": topN("mixed"),
           "topBundledWitness": topN("bundled_witness", 12),
           "topHeadApi": topN("head_api", 12)}
with open(P("shared_head_triage_summary.json"), "wb") as o:
    o.write(json.dumps(summary, ensure_ascii=False, indent=2).encode("utf-8"))
log("sub-status: " + json.dumps(dict(cnt)))
for sub in ("repeated_proof", "mixed"):
    log(f"== {sub} ==")
    for r in summary["repeatedProof" if sub == "repeated_proof" else "mixed"]:
        print(f"  #{r['clusterId']} n={r['size']} areas={r['nAreas']} "
              f"medNodes={r['medianValueNodes']} head={r['head']} "
              f"suf={r['externalSuffix']}")
log("done.")
