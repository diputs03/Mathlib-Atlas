#!/usr/bin/env python3
"""verify_community_triage.py — independently recompute every triage metric
and status label from the raw clusters/assignment/features/classes and compare
to data/community_triage*.json. Deterministic ordering is also checked."""
import json, os, sys, collections

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
DATA = os.path.join(ROOT, "data")
def P(n): return os.path.join(DATA, n)
def fail(m): print("VERIFICATION FAILED:", m); sys.exit(1)
def suffix(n): return n.rsplit(".", 1)[-1]
def carrier(n):
    p = n.rsplit(".", 1); return p[0] if len(p) == 2 else ""
def norm_class(s):
    s = s[0].lower() + s[1:] if s else s
    return s[4:] if s.startswith("inst") else s

classes = {json.loads(l)["name"] for l in open(P("atlas_classes.jsonl"), "rb")}
clusters = {c["clusterId"]: c for c in
            (json.loads(l) for l in open(P("analogy_clusters.jsonl"), "rb"))}
members_of = collections.defaultdict(list)
module_of = {}
for line in open(P("analogy_cluster_assignment.jsonl"), "rb"):
    r = json.loads(line); members_of[r["cluster"]].append(r["name"])
    module_of[r["name"]] = r["module"]
INFRA_MARK = (".Tactic.", ".Lean.", ".Util.", ".Meta.", "PrettyPrinter",
              "Parenthesizer", "Formatter", "Delaborator")
def is_infra(n):
    m = module_of.get(n, ""); return any(k in m for k in INFRA_MARK)
need = set()
for cid, c in clusters.items():
    if c["crossArea"]: need.update(members_of[cid])
feat = {}
for line in open(P("atlas_features.jsonl"), "rb"):
    r = json.loads(line)
    if r["name"] in need:
        feat[r["name"]] = (bool(r.get("valueIsRfl")), bool(r.get("isInstance")))

def derive(c):
    mem = sorted(members_of[c["clusterId"]]); n = len(mem)
    suf = collections.Counter(suffix(m) for m in mem)
    ts, tn = suf.most_common(1)[0]; suf_cov = tn / n
    car = {carrier(m) for m in mem if carrier(m)}
    ca = [a[2:] for a in c.get("commonAnchors", [])
          if a.startswith("C:") and a[2:] in classes]
    ha = [a[2:] for a in c.get("commonAnchors", []) if a.startswith("H:")]
    built = sorted(set(ca) & set(ha))
    builds_by_name = norm_class(ts) in {norm_class(b) for b in built}
    nrfl = sum(1 for m in mem if feat.get(m, (False, False))[0])
    ninst = sum(1 for m in mem if feat.get(m, (False, False))[1])
    ninfra = sum(1 for m in mem if is_infra(m))
    inst, rfl, infra = ninst / n, nrfl / n, ninfra / n
    if infra >= 0.5:
        st = "infra"
    elif built and builds_by_name and len(car) >= 2:
        st = "structure_lifted_per_carrier"
    elif ca and (suf_cov >= 0.5 or inst >= 0.5):
        st = "generic_api_exists"
    elif suf_cov >= 0.6 and len(car) >= 3 and c["nAreas"] >= 2 and not ca:
        st = "pointwise_repeated"
    elif ha and suf_cov < 0.5:
        st = "shared_head_analogy"
    else:
        st = "weak"
    if st in ("pointwise_repeated", "structure_lifted_per_carrier"):
        sc = n * c["nAreas"] * suf_cov * (1 - 0.5 * rfl)
    elif st == "shared_head_analogy":
        sc = n * c["nAreas"] * 0.5
    else:
        sc = 0.0
    return (st, round(sc, 3), round(suf_cov, 3), round(inst, 3), round(rfl, 3),
            len(car), ca, ha, n, built)

rows = [json.loads(l) for l in open(P("community_triage.jsonl"), "rb")]
summary = json.load(open(P("community_triage_summary.json"), "rb"))
expect_ids = {cid for cid, c in clusters.items() if c["crossArea"]}
got_ids = {r["clusterId"] for r in rows}
if expect_ids != got_ids:
    fail(f"coverage: missing {len(expect_ids-got_ids)} extra {len(got_ids-expect_ids)}")
sc = collections.Counter()
rank = {"structure_lifted_per_carrier": 0, "pointwise_repeated": 1,
        "shared_head_analogy": 2, "generic_api_exists": 3, "weak": 4, "infra": 5}
prev = None
for r in rows:
    c = clusters[r["clusterId"]]
    st, score, suf_cov, inst, rfl, ncar, ca, ha, n, built = derive(c)
    sc[st] += 1
    if st != r["status"]: fail(f"{r['clusterId']} status {r['status']} != {st}")
    if abs(score - r["opportunityScore"]) > 1e-6:
        fail(f"{r['clusterId']} score {r['opportunityScore']} != {score}")
    if abs(suf_cov - r["topSuffix"]["coverage"]) > 1e-6:
        fail(f"{r['clusterId']} suffix coverage")
    if abs(inst - r["instanceFrac"]) > 1e-6: fail("instanceFrac")
    if abs(rfl - r["rflFrac"]) > 1e-6: fail("rflFrac")
    if ncar != r["nCarriers"]: fail("nCarriers")
    if n != r["size"]: fail("size")
    if ca != r["classAnchors"]: fail("classAnchors")
    if built != r["builtClass"]: fail("builtClass")
    key = (rank[st], -score, -n)
    if prev is not None and key < prev: fail("rows not in declared order")
    prev = key
if dict(sc) != summary["byStatus"]:
    fail(f"byStatus {dict(sc)} != {summary['byStatus']}")
if summary["crossAreaCommunities"] != len(rows):
    fail("summary count")
print("[verify]", len(rows), "cross-area communities re-derived; status/score/order correct")
print("[verify] byStatus:", dict(sc))
print("VERIFICATION OK")
