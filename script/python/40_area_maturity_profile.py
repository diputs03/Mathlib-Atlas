#!/usr/bin/env python3
"""40_area_maturity_profile.py — abstraction maturity vs opportunity pressure.

Motivation (user directive): the mature stdlib core is where prior sweeps found
everything already abstracted; contemporary / frontier areas are less developed
and may hold more missing abstractions. This script gives every top-level area a
transparent "abstraction maturity" profile from already-verified artifacts and
compares frontier areas against the core.

Per-area proxies (all directly counted, no model):
  from features : decls, theorem/def/instance/class counts, rfl-closed fraction,
                  value-truncated fraction, mean instance constraints per theorem,
                  CONCRETE-theorem fraction (theorems with 0 implicit type binder
                  AND 0 instance binder -> stated on a fixed carrier, not generic),
                  mean proof/type term size.
  from 38       : modules, namespace roots.
  from 39       : classes instantiated in area, shared-class bridge degree.
  from 14       : cross-area reference degree (outAreas/inAreas, refs).

Maturity score = mean of cross-area percentile ranks (higher = more abstracted):
  generic-statement share (1 - concrete fraction), instance-constraint density,
  rfl-closed share, instance density. Opportunity pressure = 1 - maturity for
  areas above a size floor. Buckets are a DECLARED heuristic, printed in output.

Inputs : data/atlas_features.jsonl + summaries from 14/38/39 (all present)
Outputs: data/area_maturity_profile.jsonl, data/area_maturity_summary.json
Pure stdlib, deterministic.
"""
import json, os, collections

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
DATA = os.path.join(ROOT, "data")
FEAT = os.path.join(DATA, "atlas_features.jsonl")
NS_SUM = os.path.join(DATA, "namespace_structure_summary.json")
BR_SUM = os.path.join(DATA, "typeclass_bridge_summary.json")
BR_PAIR = os.path.join(DATA, "area_class_bridges.jsonl")
AREA_SUM14 = os.path.join(DATA, "atlas_area_summary.jsonl")
OUT_PROF = os.path.join(DATA, "area_maturity_profile.jsonl")
OUT_SUM = os.path.join(DATA, "area_maturity_summary.json")

SIZE_FLOOR = 500  # ignore tiny areas when ranking opportunity pressure

# Declared buckets (heuristic, surfaced in the output, not inferred).
FRONTIER = {"CategoryTheory", "AlgebraicGeometry", "AlgebraicTopology",
            "Condensed", "NumberTheory", "RepresentationTheory", "Geometry",
            "Combinatorics", "Dynamics", "Probability", "MeasureTheory",
            "InformationTheory", "ModelTheory", "SetTheory"}
CORE = {"Algebra", "Data", "Order", "Logic", "GroupTheory", "RingTheory",
        "FieldTheory", "LinearAlgebra", "Topology", "Analysis"}
INFRA = {"Tactic", "Lean", "Control", "Util", "Testing", "Init", "Basic",
         "Computability"}


def area_of(module):
    p = module.split(".")
    return p[1] if len(p) >= 2 and p[0] == "Mathlib" else ""


def bucket(a):
    if a in FRONTIER:
        return "frontier"
    if a in CORE:
        return "core"
    if a in INFRA:
        return "infra"
    return "other"


def pct_rank(values):
    """value -> percentile rank in [0,1] (average rank, ties share)."""
    order = sorted(values)
    n = len(order)
    out = {}
    i = 0
    while i < n:
        j = i
        while j + 1 < n and order[j + 1] == order[i]:
            j += 1
        rank = (i + j) / 2 / max(1, n - 1)
        for k in range(i, j + 1):
            out[order[k]] = rank
        i = j + 1
    return out


def main():
    agg = collections.defaultdict(lambda: collections.Counter())
    sumval = collections.defaultdict(lambda: collections.Counter())
    for line in open(FEAT, encoding="utf-8"):
        r = json.loads(line)
        a = area_of(r.get("module", ""))
        if not a:
            continue
        c = agg[a]
        c["decls"] += 1
        c[r.get("kind", "?")] += 1
        if r.get("isInstance"):
            c["instances"] += 1
        if r.get("isClass"):
            c["classes"] += 1
        if r.get("isGenerated"):
            c["generated"] += 1
        if r.get("valueTruncated"):
            c["valueTruncated"] += 1
        sv = sumval[a]
        sv["valueNodes"] += r.get("valueNodes", 0) or 0
        sv["typeNodes"] += r.get("typeNodes", 0) or 0
        if r.get("kind") == "theorem":
            c["theorems"] += 1
            if r.get("valueIsRfl"):
                c["rfl"] += 1
            ni = r.get("nInstImplicit", 0) or 0
            nim = r.get("nImplicit", 0) or 0
            sv["instConstr"] += ni
            if ni == 0 and nim == 0:
                c["concreteThm"] += 1

    # joins
    ns = {a["area"]: a for a in
          json.load(open(NS_SUM, encoding="utf-8"))["areas"]}
    bridge_deg = collections.Counter()
    bridge_shared = collections.Counter()
    for line in open(BR_PAIR, encoding="utf-8"):
        p = json.loads(line)
        bridge_deg[p["areaA"]] += 1
        bridge_deg[p["areaB"]] += 1
        bridge_shared[p["areaA"]] += p["sharedClasses"]
        bridge_shared[p["areaB"]] += p["sharedClasses"]
    area14 = {}
    for line in open(AREA_SUM14, encoding="utf-8"):
        s = json.loads(line)
        area14[s["area"]] = s
    cls_inst = {}
    if os.path.exists(BR_SUM):
        for a in json.load(open(BR_SUM, encoding="utf-8"))["areas"]:
            cls_inst[a["area"]] = a["classesInstantiated"]

    # build rows
    rows = {}
    for a, c in agg.items():
        th = c["theorems"]
        sv = sumval[a]
        rows[a] = {
            "area": a, "bucket": bucket(a),
            "decls": c["decls"], "theorems": th,
            "definitions": c.get("definition", 0),
            "instances": c["instances"], "classes": c["classes"],
            "generated": c["generated"],
            "rflFraction": round(c["rfl"] / th, 4) if th else 0.0,
            "truncatedFraction": round(c["valueTruncated"] / c["decls"], 4),
            "concreteTheoremFraction": round(c["concreteThm"] / th, 4) if th else 0.0,
            "genericTheoremShare": round(1 - c["concreteThm"] / th, 4) if th else 0.0,
            "meanInstConstraints": round(sv["instConstr"] / th, 3) if th else 0.0,
            "instanceDensity": round(c["instances"] / c["decls"], 4),
            "meanValueNodes": round(sv["valueNodes"] / c["decls"], 1),
            "modules": ns.get(a, {}).get("modules", 0),
            "namespaceRoots": ns.get(a, {}).get("namespaceRoots", 0),
            "classesInstantiated": cls_inst.get(a, 0),
            "bridgeDegree": bridge_deg[a],
            "bridgeSharedClasses": bridge_shared[a],
            "refOutAreas": area14.get(a, {}).get("outAreas", 0),
            "refInAreas": area14.get(a, {}).get("inAreas", 0)}

    # percentile-rank composite maturity
    keys = list(rows)
    rank_generic = pct_rank([rows[a]["genericTheoremShare"] for a in keys])
    rank_constr = pct_rank([rows[a]["meanInstConstraints"] for a in keys])
    rank_rfl = pct_rank([rows[a]["rflFraction"] for a in keys])
    rank_inst = pct_rank([rows[a]["instanceDensity"] for a in keys])
    for a in keys:
        r = rows[a]
        mat = (rank_generic[r["genericTheoremShare"]]
               + rank_constr[r["meanInstConstraints"]]
               + rank_rfl[r["rflFraction"]]
               + rank_inst[r["instanceDensity"]]) / 4
        r["maturityScore"] = round(mat, 4)
        r["opportunityPressure"] = round(1 - mat, 4) if r["decls"] >= SIZE_FLOOR else None

    ordered = sorted(rows.values(), key=lambda r: (-r["decls"], r["area"]))
    with open(OUT_PROF, "wb") as o:
        for r in ordered:
            o.write((json.dumps(r, ensure_ascii=False) + "\n").encode("utf-8"))

    # bucket means
    def mean(vals):
        return round(sum(vals) / len(vals), 4) if vals else 0.0
    buckets = collections.defaultdict(list)
    for r in ordered:
        buckets[r["bucket"]].append(r)
    bucket_summary = {}
    for b, rs in buckets.items():
        bucket_summary[b] = {
            "nAreas": len(rs),
            "meanGenericShare": mean([x["genericTheoremShare"] for x in rs]),
            "meanConcreteFraction": mean([x["concreteTheoremFraction"] for x in rs]),
            "meanInstConstraints": mean([x["meanInstConstraints"] for x in rs]),
            "meanRflFraction": mean([x["rflFraction"] for x in rs]),
            "meanMaturity": mean([x["maturityScore"] for x in rs]),
            "meanOpportunityPressure": mean(
                [x["opportunityPressure"] for x in rs
                 if x["opportunityPressure"] is not None]),
            "totalDecls": sum(x["decls"] for x in rs)}

    opp_rank = sorted(
        (r for r in ordered if r["opportunityPressure"] is not None),
        key=lambda r: (-r["opportunityPressure"], -r["decls"]))
    summary = {
        "sizeFloor": SIZE_FLOOR,
        "bucketsDeclared": {"frontier": sorted(FRONTIER), "core": sorted(CORE),
                            "infra": sorted(INFRA)},
        "bucketMeans": bucket_summary,
        "highestOpportunityPressure": [
            {"area": r["area"], "bucket": r["bucket"], "decls": r["decls"],
             "concreteFraction": r["concreteTheoremFraction"],
             "maturity": r["maturityScore"],
             "opportunity": r["opportunityPressure"]}
            for r in opp_rank[:15]],
        "mostMature": [
            {"area": r["area"], "bucket": r["bucket"],
             "maturity": r["maturityScore"]}
            for r in sorted(ordered, key=lambda r: -r["maturityScore"])[:10]],
    }
    with open(OUT_SUM, "w", encoding="utf-8") as o:
        json.dump(summary, o, ensure_ascii=False, indent=2)

    print("bucket means:")
    for b in ("core", "frontier", "other", "infra"):
        if b in bucket_summary:
            m = bucket_summary[b]
            print(f"  {b:<9} areas={m['nAreas']:<2} genericShare="
                  f"{m['meanGenericShare']:<6} concrete={m['meanConcreteFraction']:<6} "
                  f"instConstr={m['meanInstConstraints']:<6} rfl={m['meanRflFraction']:<6} "
                  f"maturity={m['meanMaturity']:<6} opp={m['meanOpportunityPressure']}")
    print("highest opportunity pressure (size>=floor):")
    for r in opp_rank[:15]:
        print(f"  {r['area']:<20} {r['bucket']:<9} decls={r['decls']:<6} "
              f"concrete={r['concreteTheoremFraction']:<6} mat={r['maturityScore']} "
              f"opp={r['opportunityPressure']}")


if __name__ == "__main__":
    main()
