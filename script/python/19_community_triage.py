#!/usr/bin/env python3
"""19_community_triage.py — classify script-18 cross-area analogy communities
by *abstraction status*, turning the cluster list into a prioritized worklist.

For each cross-area community we combine the cluster structure with script-13
features and the script-10 class table:

  generic_api_exists   a real Mathlib typeclass is a shared constraint anchor
                       (C:<class>) and the members are uniform-suffix
                       instances/lemmas -> an abstraction already captures the
                       family (case B's Is*Apply, InjSurj transfer, ...).
  pointwise_repeated   uniform declaration suffix across >=3 distinct carrier
                       namespaces / >=2 areas, members are concrete
                       instances/defs, but NO shared real class anchor -> the
                       same construction is re-derived per carrier: a candidate
                       missing abstraction.
  shared_head_analogy  members share a conclusion head but no uniform suffix ->
                       same statement-shape across areas (possible common lemma).
  weak                 none of the above.

Candidates are ranked by an opportunity score rewarding size, area spread,
uniformity and non-trivial (non-rfl) proofs.

Pure Python, deterministic.
Inputs : data/analogy_clusters.jsonl, data/analogy_cluster_assignment.jsonl,
         data/atlas_features.jsonl, data/atlas_classes.jsonl
Outputs: data/community_triage.jsonl, data/community_triage_summary.json
"""
import json, os, collections, time

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
DATA = os.path.join(ROOT, "data")
def P(n): return os.path.join(DATA, n)

def log(m): print(f"[{time.strftime('%H:%M:%S')}] {m}", flush=True)
def suffix(n): return n.rsplit(".", 1)[-1]
def carrier(n):
    p = n.rsplit(".", 1)
    return p[0] if len(p) == 2 else ""
def norm_class(s):  # AddCommMonoid -> addCommMonoid ; instAdd -> add
    s = s[0].lower() + s[1:] if s else s
    return s[4:] if s.startswith("inst") else s

# ---- class table ------------------------------------------------------------
classes = set()
for line in open(P("atlas_classes.jsonl"), "rb"):
    classes.add(json.loads(line)["name"])
log(f"classes: {len(classes):,}")

# ---- clusters + full assignment ---------------------------------------------
clusters = [json.loads(l) for l in open(P("analogy_clusters.jsonl"), "rb")]
members_of = collections.defaultdict(list)
module_of = {}
for line in open(P("analogy_cluster_assignment.jsonl"), "rb"):
    r = json.loads(line)
    members_of[r["cluster"]].append(r["name"])
    module_of[r["name"]] = r["module"]
log(f"clusters {len(clusters):,}; assignment loaded")

INFRA_MARK = (".Tactic.", ".Lean.", ".Util.", ".Meta.", "PrettyPrinter",
              "Parenthesizer", "Formatter", "Delaborator")
def is_infra(name):
    m = module_of.get(name, "")
    return any(k in m for k in INFRA_MARK)

# ---- features for clustered nodes only --------------------------------------
need = set()
for c in clusters:
    if c["crossArea"]:
        need.update(members_of[c["clusterId"]])
feat = {}
for line in open(P("atlas_features.jsonl"), "rb"):
    r = json.loads(line)
    if r["name"] in need:
        feat[r["name"]] = (bool(r.get("valueIsRfl")), bool(r.get("isInstance")),
                           r.get("conclusionHead", ""))
log(f"features for {len(feat):,} clustered nodes")

rows = []
status_count = collections.Counter()
for c in clusters:
    if not c["crossArea"]:
        continue
    cid = c["clusterId"]
    mem = sorted(members_of[cid])
    n = len(mem)
    suf = collections.Counter(suffix(m) for m in mem)
    top_suf, top_suf_n = suf.most_common(1)[0]
    suf_cov = top_suf_n / n
    carriers = collections.Counter(carrier(m) for m in mem if carrier(m))
    # shared real class anchors
    class_anchors = []
    for a in c.get("commonAnchors", []):
        if a.startswith("C:"):
            cn = a[2:]
            if cn in classes:
                class_anchors.append(cn)
    head_anchors = [a[2:] for a in c.get("commonAnchors", []) if a.startswith("H:")]
    # classes the members themselves CONSTRUCT (class is both constraint and
    # conclusion head) => same structure lifted independently per carrier
    built_class = sorted(set(class_anchors) & set(head_anchors))
    # declaration suffix names the structure it builds (Set.addCommMonoid ...)
    builds_by_name = norm_class(top_suf) in {norm_class(b) for b in built_class}
    # feature aggregates
    n_rfl = n_inst = n_infra = 0
    for m in mem:
        rfl, inst, _ = feat.get(m, (False, False, ""))
        if inst: n_inst += 1
        if rfl: n_rfl += 1
        if is_infra(m): n_infra += 1
    inst_frac = n_inst / n
    rfl_frac = n_rfl / n
    infra_frac = n_infra / n
    n_carriers = len(carriers)

    # ---- classification (priority order) ----
    if infra_frac >= 0.5:
        status = "infra"
    elif built_class and builds_by_name and n_carriers >= 2:
        status = "structure_lifted_per_carrier"
    elif class_anchors and (suf_cov >= 0.5 or inst_frac >= 0.5):
        status = "generic_api_exists"
    elif (suf_cov >= 0.6 and n_carriers >= 3 and c["nAreas"] >= 2
          and not class_anchors):
        status = "pointwise_repeated"
    elif head_anchors and suf_cov < 0.5:
        status = "shared_head_analogy"
    else:
        status = "weak"
    status_count[status] += 1

    # opportunity score: concrete, uniform, wide-spread, non-rfl families first
    if status in ("pointwise_repeated", "structure_lifted_per_carrier"):
        score = n * c["nAreas"] * suf_cov * (1.0 - 0.5 * rfl_frac)
    elif status == "shared_head_analogy":
        score = n * c["nAreas"] * 0.5
    else:
        score = 0.0
    rows.append({
        "clusterId": cid, "status": status, "opportunityScore": round(score, 3),
        "label": c["label"], "size": n, "nAreas": c["nAreas"],
        "areas": c["areas"], "nCarriers": n_carriers,
        "topSuffix": {"suffix": top_suf, "coverage": round(suf_cov, 3)},
        "classAnchors": class_anchors, "builtClass": built_class,
        "headAnchors": head_anchors[:5],
        "instanceFrac": round(inst_frac, 3), "rflFrac": round(rfl_frac, 3),
        "infraFrac": round(infra_frac, 3),
        "meanCosine": c["meanCosine"],
        "topCarriers": [x for x, _ in carriers.most_common(8)],
        "members": mem[:30],
    })

# deterministic ordering: status rank, then score desc, then size
rank = {"structure_lifted_per_carrier": 0, "pointwise_repeated": 1,
        "shared_head_analogy": 2, "generic_api_exists": 3, "weak": 4, "infra": 5}
rows.sort(key=lambda r: (rank[r["status"]], -r["opportunityScore"], -r["size"]))
with open(P("community_triage.jsonl"), "wb") as o:
    for r in rows:
        o.write((json.dumps(r, ensure_ascii=False) + "\n").encode("utf-8"))

def topN(status, k=15):
    out = []
    for r in rows:
        if r["status"] == status:
            out.append({"clusterId": r["clusterId"], "label": r["label"],
                        "size": r["size"], "nAreas": r["nAreas"],
                        "suffix": r["topSuffix"], "nCarriers": r["nCarriers"],
                        "rflFrac": r["rflFrac"], "builtClass": r["builtClass"],
                        "classAnchors": r["classAnchors"],
                        "headAnchors": r["headAnchors"],
                        "score": r["opportunityScore"]})
            if len(out) >= k: break
    return out

summary = {"crossAreaCommunities": len(rows),
           "byStatus": dict(status_count),
           "topStructureLifted": topN("structure_lifted_per_carrier"),
           "topPointwiseRepeated": topN("pointwise_repeated"),
           "topSharedHeadAnalogy": topN("shared_head_analogy"),
           "topGenericApiExists": topN("generic_api_exists", 10)}
with open(P("community_triage_summary.json"), "wb") as o:
    o.write(json.dumps(summary, ensure_ascii=False, indent=2).encode("utf-8"))
log("status counts: " + json.dumps(dict(status_count)))
log("top structure_lifted_per_carrier candidates:")
for r in summary["topStructureLifted"][:12]:
    print(f"  #{r['clusterId']} n={r['size']} areas={r['nAreas']} "
          f"carriers={r['nCarriers']} builds={r['builtClass']} {r['label']}")
log("done.")
