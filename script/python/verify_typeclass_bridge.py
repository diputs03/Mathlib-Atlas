#!/usr/bin/env python3
"""verify_typeclass_bridge.py — independent rebuild of script 39."""
import json, os, sys, itertools, collections

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
DATA = os.path.join(ROOT, "data")


def area_of(m):
    p = m.split(".")
    return p[1] if len(p) >= 2 and p[0] == "Mathlib" else ""


def main():
    nparents = {}
    for line in open(os.path.join(DATA, "atlas_classes.jsonl"), encoding="utf-8"):
        c = json.loads(line)
        nparents[c["name"]] = len(c.get("parents", []))

    cls = collections.defaultdict(
        lambda: {"n": 0, "ar": collections.Counter(), "car": set(), "mod": set()})
    n_inst = n_ml = n_used = 0
    for line in open(os.path.join(DATA, "atlas_instances.jsonl"), encoding="utf-8"):
        r = json.loads(line)
        n_inst += 1
        if not r.get("mathlib"):
            continue
        n_ml += 1
        a = area_of(r.get("module", ""))
        cn = r.get("className")
        if not cn or not a:
            continue
        n_used += 1
        g = cls[cn]
        g["n"] += 1
        g["ar"][a] += 1
        if r.get("targetHead"):
            g["car"].add(r["targetHead"])
        g["mod"].add(r["module"])

    rebuilt = {}
    bridge = 0
    for cn, g in cls.items():
        tot = sum(g["ar"].values())
        order = sorted(g["ar"].items(), key=lambda kv: (-kv[1], kv[0]))
        dom, dn = order[0]
        if len(g["ar"]) >= 3:
            bridge += 1
        rebuilt[cn] = (g["n"], len(g["ar"]), len(g["car"]), len(g["mod"]),
                       nparents.get(cn, 0), dom, round(dn / tot, 4))

    # pair graph
    pairs = {}
    for cn, g in cls.items():
        if len(g["ar"]) >= 2:
            for a, b in itertools.combinations(sorted(g["ar"]), 2):
                pairs.setdefault((a, b), set()).add(cn)

    sumry = json.load(open(os.path.join(DATA, "typeclass_bridge_summary.json"),
                           encoding="utf-8"))
    wr_cls = [json.loads(l) for l in open(
        os.path.join(DATA, "typeclass_bridge_classes.jsonl"), encoding="utf-8")]
    wr_pair = [json.loads(l) for l in open(
        os.path.join(DATA, "area_class_bridges.jsonl"), encoding="utf-8")]

    errs = []
    if sumry["totalInstances"] != n_inst:
        errs.append("total inst mismatch")
    if sumry["mathlibInstances"] != n_ml:
        errs.append("mathlib inst mismatch")
    if sumry["distinctClassesWithInstance"] != len(cls):
        errs.append("distinct class mismatch")
    if sumry["bridgeClassesGe3Areas"] != bridge:
        errs.append("bridge count mismatch")
    if sum(g["n"] for g in cls.values()) != n_used:
        errs.append("instance conservation broken")
    if sum(r["instances"] for r in wr_cls) != n_used:
        errs.append("written class rows don't conserve instances")

    # class bijection + order
    if len(wr_cls) != len(rebuilt):
        errs.append(f"class rows {len(wr_cls)} != {len(rebuilt)}")
    prev = None
    for w in wr_cls:
        b = rebuilt.get(w["class"])
        if b is None:
            errs.append(f"class {w['class']} not rebuilt")
            continue
        exp = (w["instances"], w["nAreas"], w["nCarriers"], w["nModules"],
               w["nParents"], w["dominantArea"], w["dominantShare"])
        if exp != b:
            errs.append(f"class {w['class']}: {exp} != {b}")
        # areas list sums to instances, sorted desc
        if sum(a["instances"] for a in w["areas"]) != w["instances"]:
            errs.append(f"class {w['class']} area breakdown doesn't sum")
        cur = (-w["nAreas"], -w["instances"], w["class"])
        if prev is not None and cur < prev:
            errs.append(f"class rows unsorted at {w['class']}")
        prev = cur

    # pair bijection
    if len(wr_pair) != len(pairs):
        errs.append(f"pair rows {len(wr_pair)} != {len(pairs)}")
    prev = None
    for w in wr_pair:
        key = (w["areaA"], w["areaB"])
        b = pairs.get(key)
        if b is None:
            errs.append(f"pair {key} not rebuilt")
            continue
        if w["sharedClasses"] != len(b):
            errs.append(f"pair {key}: {w['sharedClasses']} != {len(b)}")
        if set(w["topClasses"]) - b:
            errs.append(f"pair {key} lists a class not spanning it")
        cur = (-w["sharedClasses"], w["areaA"], w["areaB"])
        if prev is not None and cur < prev:
            errs.append("pair rows unsorted")
        prev = cur

    print(f"instances {n_inst} (mathlib {n_ml}, area-tagged {n_used}); "
          f"classes {len(cls)}, bridge>=3areas {bridge}, area pairs {len(pairs)}")
    if errs:
        print("VERIFICATION FAILED")
        for e in errs[:30]:
            print("  FAIL:", e)
        sys.exit(1)
    print("counts, conservation, class/pair bijections and order all match")
    print("VERIFICATION OK")


if __name__ == "__main__":
    main()
