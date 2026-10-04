#!/usr/bin/env python3
"""42_frontier_generalization_scan.py — area-stratified missing-generalization.

Script 36 found 0 missing generalizations globally, and script 40 showed frontier
areas carry ~2.2x the concrete-statement rate. This script re-runs 36's EXACT
generic/specialized classifier (generic = forall prefix binds a Sort/Type
variable; signature = (conclusionHead, constraint-class tuple, nDefault)) but
keeps each group's area profile, so we can:

  1. measure missing-generalization PRESSURE PER AREA (specialized-only repeated
     shape groups per 1,000 theorems), and compare frontier vs core buckets;
  2. emit a frontier-majority shortlist of surviving named-operator groups for
     hand / kernel inspection.

Filters are identical to 36 (class/prop-fact heads and bare logical heads
excluded; namespace artifacts removed) so the global result must reproduce 5
survivors — a built-in consistency check.

Inputs : data/atlas_corpus.jsonl, atlas_type_skeletons.jsonl,
         atlas_classes.jsonl, area_maturity_profile.jsonl (buckets)
Outputs: data/frontier_generalization_shortlist.jsonl,
         data/area_opportunity_density.jsonl, data/frontier_scan_summary.json
Pure stdlib, streaming, deterministic.
"""
import json, os, collections

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
DATA = os.path.join(ROOT, "data")
MIN_SPEC, MIN_CARRIERS = 3, 2
GEN_TAILS = ("casesOn", "recOn", "brecOn", "inductionOn", "noConfusion",
             "noConfusionType", "rec", "mk")
LOGIC = {"eq", "iff", "exists", "le", "lt", "ge", "gt", "and", "or", "not",
         "true", "false", "heq", "mem", "subset", "ssubset", "ne", "nonempty",
         "dvd"}


def is_generic(node):
    while isinstance(node, dict) and "binderInfo" in node:
        bt = node.get("binderType")
        if isinstance(bt, dict) and bt.get("tag") == "sort":
            return True
        node = node["body"]
    return False


def carrier_root(ns):
    return (ns or "").split(".")[0]


def main():
    class_heads = set()
    for line in open(os.path.join(DATA, "atlas_classes.jsonl"), encoding="utf-8"):
        class_heads.add(json.loads(line)["name"].split(".")[-1])
    bucket = {}
    for line in open(os.path.join(DATA, "area_maturity_profile.jsonl"), encoding="utf-8"):
        r = json.loads(line)
        bucket[r["area"]] = r["bucket"]

    skel = {}
    for line in open(os.path.join(DATA, "atlas_type_skeletons.jsonl"), encoding="utf-8"):
        s = json.loads(line)
        if s.get("kind") == "theorem":
            skel[s["name"]] = (s.get("conclusionHead"),
                               tuple(sorted(c["class"] for c in s.get("constraints", []))),
                               s.get("nDefault", 0))

    groups = {}
    area_th = collections.Counter()
    n_th = 0
    for line in open(os.path.join(DATA, "atlas_corpus.jsonl"), encoding="utf-8"):
        r = json.loads(line)
        if r.get("kind") != "theorem":
            continue
        mod = r.get("module", "")
        if not mod.startswith("Mathlib"):
            continue
        name = r["name"]
        if name.split(".")[-1] in GEN_TAILS or name.startswith("_"):
            continue
        sk = skel.get(name)
        ta = r.get("typeAst")
        if sk is None or not sk[0] or not isinstance(ta, dict):
            continue
        n_th += 1
        area = mod.split(".")[1] if mod.count(".") >= 1 else ""
        area_th[area] += 1
        head, ckey, ndef = sk
        g = groups.setdefault((head, ckey, ndef),
                              {"gen": 0, "spec": 0, "areas": collections.Counter(),
                               "carriers": set(), "ex": []})
        if is_generic(ta):
            g["gen"] += 1
        else:
            g["spec"] += 1
            g["areas"][area] += 1
            g["carriers"].add(carrier_root(r.get("namespace")))
            if len(g["ex"]) < 12:
                g["ex"].append(name)

    # classify specialized-only groups; per-area pressure counters
    raw_by_area = collections.Counter()     # specialized-only >=MIN_SPEC (pre-filter)
    reject_by_area = collections.defaultdict(collections.Counter)
    survivors = []
    for (head, ckey, ndef), g in groups.items():
        if g["gen"] > 0:
            continue
        if g["spec"] < MIN_SPEC:
            continue
        dom_area = max(sorted(g["areas"]), key=lambda a: g["areas"][a])
        raw_by_area[dom_area] += 1
        tail = head.split(".")[-1]
        carriers_all = {c for c in g["carriers"] if c}
        carriers = {c for c in carriers_all
                    if c != "[anonymous]" and c != "definition"
                    and not c.startswith("inst")}
        if tail in class_heads:
            reject_by_area[dom_area]["classPropHead"] += 1
        elif tail.lower() in LOGIC:
            reject_by_area[dom_area]["logicalHead"] += 1
        elif not ckey:
            reject_by_area[dom_area]["emptyConstraints"] += 1
        elif len(carriers) < MIN_CARRIERS:
            reject_by_area[dom_area]["singleCarrierOrArtifact"] += 1
        else:
            reject_by_area[dom_area]["survives"] += 1
        if tail in class_heads or tail.lower() in LOGIC or not ckey:
            continue
        if len(carriers) < MIN_CARRIERS:
            continue
        areas_sorted = sorted(g["areas"].items(), key=lambda kv: (-kv[1], kv[0]))
        b = bucket.get(dom_area, "other")
        survivors.append({
            "conclusionHead": head, "constraints": list(ckey), "nDefault": ndef,
            "nSpecialized": g["spec"], "dominantArea": dom_area,
            "dominantBucket": b, "nCarriers": len(carriers),
            "carriers": sorted(carriers),
            "areas": [{"area": a, "n": c} for a, c in areas_sorted],
            "examples": g["ex"]})
    survivors.sort(key=lambda x: (x["dominantBucket"] != "frontier",
                                  -x["nSpecialized"], x["conclusionHead"]))
    with open(os.path.join(DATA, "frontier_generalization_shortlist.jsonl"),
              "wb") as o:
        for rec in survivors:
            o.write((json.dumps(rec, ensure_ascii=False) + "\n").encode("utf-8"))

    # per-area density rows
    dens = []
    for area in sorted(area_th):
        th = area_th[area]
        dens.append({"area": area, "bucket": bucket.get(area, "other"),
                     "theorems": th,
                     "specializedOnlyGroups": raw_by_area[area],
                     "pressurePer1000": round(1000 * raw_by_area[area] / th, 3)
                     if th else 0.0,
                     "rejectReasons": dict(reject_by_area[area])})
    dens.sort(key=lambda x: -x["pressurePer1000"])
    with open(os.path.join(DATA, "area_opportunity_density.jsonl"), "wb") as o:
        for rec in dens:
            o.write((json.dumps(rec, ensure_ascii=False) + "\n").encode("utf-8"))

    def bmean(bk, key):
        v = [d[key] for d in dens if d["bucket"] == bk and d["theorems"] >= 500]
        return round(sum(v) / len(v), 3) if v else 0.0
    bucket_reject = {}
    for bk in ("core", "frontier", "other", "infra"):
        c = collections.Counter()
        for d in dens:
            if d["bucket"] == bk:
                c.update(d["rejectReasons"])
        tot = sum(c.values())
        bucket_reject[bk] = {k: round(c[k] / tot, 3) for k in c} if tot else {}
    summary = {
        "theorems": n_th,
        "specializedOnlyShapeGroups": sum(raw_by_area.values()),
        "survivorsAfterFilters": len(survivors),
        "bucketMeanPressurePer1000": {
            b: bmean(b, "pressurePer1000")
            for b in ("core", "frontier", "other", "infra")},
        "bucketRejectReasonShare": bucket_reject,
        "topPressureAreas": dens[:15],
        "frontierMajorityShortlist": [s for s in survivors
                                      if s["dominantBucket"] == "frontier"],
        "allSurvivors": survivors,
    }
    with open(os.path.join(DATA, "frontier_scan_summary.json"), "w",
              encoding="utf-8") as o:
        json.dump(summary, o, ensure_ascii=False, indent=2)

    print(f"theorems {n_th}; specialized-only groups "
          f"{sum(raw_by_area.values())}; survivors (must equal 36's 5): "
          f"{len(survivors)}")
    print("bucket mean pressure (specialized-only groups / 1000 theorems):")
    for b in ("core", "frontier", "other", "infra"):
        print(f"  {b:<9} {summary['bucketMeanPressurePer1000'][b]}  "
              f"reject-share {summary['bucketRejectReasonShare'][b]}")
    print("top pressure areas:")
    for d in dens[:15]:
        print(f"  {d['area']:<20} {d['bucket']:<9} groups={d['specializedOnlyGroups']:<4} "
              f"per1000={d['pressurePer1000']}")
    print("frontier-majority survivors:")
    for s in summary["frontierMajorityShortlist"]:
        print(f"  {s['conclusionHead']:<24} {s['dominantArea']} spec={s['nSpecialized']} "
              f"carriers={s['carriers'][:5]}")


if __name__ == "__main__":
    main()
