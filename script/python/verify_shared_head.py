#!/usr/bin/env python3
"""verify_shared_head_triage.py — independently recompute sub-status and
metrics for every shared_head row and compare to data/shared_head_triage*."""
import json, os, sys, collections, statistics

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
DATA = os.path.join(ROOT, "data")
def P(n): return os.path.join(DATA, n)
def fail(m): print("VERIFICATION FAILED:", m); sys.exit(1)
def suffix(n): return n.rsplit(".", 1)[-1]
def carrier(n):
    p = n.rsplit(".", 1); return p[0] if len(p) == 2 else ""

BUNDLE_NODE_CAP = 25
sha = {r["clusterId"]: r for r in
       (json.loads(l) for l in open(P("community_triage.jsonl"), "rb"))
       if r["status"] == "shared_head_analogy"}
members_of = collections.defaultdict(list)
for line in open(P("analogy_cluster_assignment.jsonl"), "rb"):
    r = json.loads(line); members_of[r["cluster"]].append(r["name"])
need = {n for cid in sha for n in members_of[cid]}
feat = {}
for line in open(P("atlas_features.jsonl"), "rb"):
    r = json.loads(line)
    if r["name"] in need:
        feat[r["name"]] = (r.get("valueNodes", 0) or 0, r.get("valueDepth", 0) or 0)

def derive(cid):
    r = sha[cid]; mem = sorted(members_of[cid])
    heads = r["headAnchors"]; hl = heads[0].rsplit(".", 1)[-1] if heads else ""
    api, ext = [], []
    for m in mem:
        (api if carrier(m).rsplit(".", 1)[-1] == hl else ext).append(m)
    fa = len(api) / len(mem)
    suf = collections.Counter(suffix(m) for m in ext)
    es, esn = (suf.most_common(1)[0] if suf else ("", 0))
    esc = esn / len(ext) if ext else 0.0
    nodes = [feat.get(m, (0, 0))[0] for m in ext]
    med = statistics.median(nodes) if nodes else 0
    if fa >= 0.5: sub = "head_api"
    elif ext and esc >= 0.5:
        sub = "bundled_witness" if med <= BUNDLE_NODE_CAP else "repeated_proof"
    else: sub = "mixed"
    return sub, round(fa, 3), len(ext), es, round(esc, 3), med, len(mem)

rows = [json.loads(l) for l in open(P("shared_head_triage.jsonl"), "rb")]
summ = json.load(open(P("shared_head_triage_summary.json"), "rb"))
if set(sha) != {r["clusterId"] for r in rows}: fail("coverage")
cc = collections.Counter(); rank = {"repeated_proof":0,"mixed":1,"bundled_witness":2,"head_api":3}
prev = None
for r in rows:
    sub, fa, nex, es, esc, med, n = derive(r["clusterId"])
    cc[sub] += 1
    if sub != r["subStatus"]: fail(f"{r['clusterId']} {r['subStatus']} != {sub}")
    if abs(fa - r["apiFrac"]) > 1e-6: fail("apiFrac")
    if nex != r["nExternal"]: fail("nExternal")
    if es != r["externalSuffix"]["suffix"] or abs(esc-r["externalSuffix"]["coverage"])>1e-6:
        fail("externalSuffix")
    if med != r["medianValueNodes"]: fail("medianValueNodes")
    if n != r["size"]: fail("size")
    key = (rank[sub], -r["score"], -n)
    if prev is not None and key < prev: fail("order")
    prev = key
if dict(cc) != summ["bySubStatus"]: fail(f"bySubStatus {dict(cc)} != {summ['bySubStatus']}")
if summ["sharedHeadCommunities"] != len(rows): fail("summary count")
print("[verify]", len(rows), "shared_head communities re-derived; sub-status/metrics/order correct")
print("[verify] bySubStatus:", dict(cc))
print("VERIFICATION OK")
