#!/usr/bin/env python3
"""39_typeclass_bridge_structure.py — which typeclasses glue areas together.

Distinct from 14/15 (reference-edge bridges) and 38 (cross-cutting namespaces):
here the conduit is the INSTANCE graph. An abstract class is a typeclass bridge
when concrete instances of it are declared across many top-level areas. Those
classes are the abstract vocabulary that lets one mathematical area reuse
machinery developed for another — a direct operationalization of "theory bridge".

Inputs : data/atlas_instances.jsonl (className, targetHead, module, mathlib)
         data/atlas_classes.jsonl   (class metadata: parents, nInstances)
         data/atlas_area_edges.jsonl (14's reference-edge area graph, optional)
Outputs: data/typeclass_bridge_summary.json
         data/typeclass_bridge_classes.jsonl  (per-class area/carrier spread)
         data/area_class_bridges.jsonl        (area pairs sharing classes)
Pure stdlib, streaming, deterministic.
"""
import json, os, itertools, collections

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
DATA = os.path.join(ROOT, "data")
INST = os.path.join(DATA, "atlas_instances.jsonl")
CLASSES = os.path.join(DATA, "atlas_classes.jsonl")
AREA_EDGES = os.path.join(DATA, "atlas_area_edges.jsonl")
OUT_SUM = os.path.join(DATA, "typeclass_bridge_summary.json")
OUT_CLS = os.path.join(DATA, "typeclass_bridge_classes.jsonl")
OUT_PAIR = os.path.join(DATA, "area_class_bridges.jsonl")

BRIDGE_AREAS = 3  # >= this many areas = a bridge class


def area_of(module):
    p = module.split(".")
    return p[1] if len(p) >= 2 and p[0] == "Mathlib" else ""


def main():
    # class metadata (parents count = hierarchy height signal)
    meta = {}
    for line in open(CLASSES, encoding="utf-8"):
        c = json.loads(line)
        meta[c["name"]] = {"nParents": len(c.get("parents", [])),
                           "hasStructure": c.get("hasStructure", False)}

    cls = collections.defaultdict(
        lambda: {"n": 0, "areas": collections.Counter(), "carriers": set(),
                 "modules": set()})
    area_classes = collections.defaultdict(set)   # area -> set(className)
    n_inst = n_ml = 0
    for line in open(INST, encoding="utf-8"):
        r = json.loads(line)
        n_inst += 1
        if not r.get("mathlib"):
            continue
        n_ml += 1
        area = area_of(r.get("module", ""))
        cn = r.get("className")
        if not cn or not area:
            continue
        g = cls[cn]
        g["n"] += 1
        g["areas"][area] += 1
        th = r.get("targetHead")
        if th:
            g["carriers"].add(th)
        g["modules"].add(r["module"])
        area_classes[area].add(cn)

    # per-class rows
    rows = []
    hist = collections.Counter()
    bridge = 0
    for cn, g in cls.items():
        nareas = len(g["areas"])
        hist[min(nareas, 15)] += 1
        tot = sum(g["areas"].values())
        order = sorted(g["areas"].items(), key=lambda kv: (-kv[1], kv[0]))
        dom, dn = order[0]
        if nareas >= BRIDGE_AREAS:
            bridge += 1
        m = meta.get(cn, {})
        rows.append({
            "class": cn,
            "instances": g["n"],
            "nAreas": nareas,
            "nCarriers": len(g["carriers"]),
            "nModules": len(g["modules"]),
            "nParents": m.get("nParents", 0),
            "dominantArea": dom,
            "dominantShare": round(dn / tot, 4) if tot else 0.0,
            "areas": [{"area": a, "instances": c} for a, c in order]})
    rows.sort(key=lambda x: (-x["nAreas"], -x["instances"], x["class"]))
    with open(OUT_CLS, "wb") as o:
        for row in rows:
            o.write((json.dumps(row, ensure_ascii=False) + "\n").encode("utf-8"))

    # area-pair shared-class graph (only classes spanning >=2 areas contribute)
    pair_classes = collections.defaultdict(set)
    for cn, g in cls.items():
        if len(g["areas"]) >= 2:
            for a, b in itertools.combinations(sorted(g["areas"]), 2):
                pair_classes[(a, b)].add(cn)
    pair_rows = []
    for (a, b), cs in pair_classes.items():
        pair_rows.append({"areaA": a, "areaB": b, "sharedClasses": len(cs),
                          "topClasses": sorted(
                              cs, key=lambda c: (-cls[c]["n"], c))[:12]})
    pair_rows.sort(key=lambda x: (-x["sharedClasses"], x["areaA"], x["areaB"]))
    with open(OUT_PAIR, "wb") as o:
        for row in pair_rows:
            o.write((json.dumps(row, ensure_ascii=False) + "\n").encode("utf-8"))

    # per-area breadth: how many distinct classes are instantiated there
    area_breadth = sorted(
        ({"area": a, "classesInstantiated": len(cs)}
         for a, cs in area_classes.items()),
        key=lambda x: -x["classesInstantiated"])

    top_bridge = [{"class": r["class"], "nAreas": r["nAreas"],
                   "instances": r["instances"], "nCarriers": r["nCarriers"],
                   "nParents": r["nParents"],
                   "dominantShare": r["dominantShare"]}
                  for r in rows[:25] if r["nAreas"] >= 2]

    # optional comparison with 14's reference-edge area graph
    ref_top = []
    if os.path.exists(AREA_EDGES):
        ref = [json.loads(l) for l in open(AREA_EDGES, encoding="utf-8")]
        # tolerate either {source,target,weight} or {areaA,areaB,...}
        def w(x):
            return x.get("weight", x.get("edges", x.get("count", 0)))
        ref.sort(key=lambda x: -w(x))
        ref_top = ref[:15]

    summary = {
        "totalInstances": n_inst,
        "mathlibInstances": n_ml,
        "distinctClassesWithInstance": len(cls),
        "bridgeClassesGe3Areas": bridge,
        "areasPerClassHist": dict(sorted(hist.items())),
        "areas": area_breadth,
        "topBridgeClasses": top_bridge,
        "topAreaPairsBySharedClass": pair_rows[:20],
        "referenceEdgeAreaTop": ref_top,
        "params": {"bridgeAreaThreshold": BRIDGE_AREAS},
    }
    with open(OUT_SUM, "w", encoding="utf-8") as o:
        json.dump(summary, o, ensure_ascii=False, indent=2)

    print(f"instances {n_inst} (mathlib {n_ml}); classes with instances "
          f"{len(cls)}; bridge classes (>={BRIDGE_AREAS} areas) {bridge}")
    print("top typeclass bridges (areas/inst/carriers/parents/domShare):")
    for r in top_bridge[:15]:
        print(f"  {r['class']:<22} areas={r['nAreas']:<2} inst={r['instances']:<4} "
              f"carriers={r['nCarriers']:<4} parents={r['nParents']} "
              f"domShare={r['dominantShare']}")
    print("area pairs most glued by shared classes:")
    for r in pair_rows[:10]:
        print(f"  {r['sharedClasses']:<3} {r['areaA']} <-> {r['areaB']}")


if __name__ == "__main__":
    main()
