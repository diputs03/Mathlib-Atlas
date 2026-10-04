#!/usr/bin/env python3
"""verify_frontier_scan.py — independent rebuild of script 42."""
import json, os, sys, collections

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
DATA = os.path.join(ROOT, "data")
MIN_SPEC, MIN_CARRIERS = 3, 2
GEN_TAILS = ("casesOn", "recOn", "brecOn", "inductionOn", "noConfusion",
             "noConfusionType", "rec", "mk")
LOGIC = {"eq", "iff", "exists", "le", "lt", "ge", "gt", "and", "or", "not",
         "true", "false", "heq", "mem", "subset", "ssubset", "ne", "nonempty",
         "dvd"}


def generic(node):
    while isinstance(node, dict) and "binderInfo" in node:
        bt = node.get("binderType")
        if isinstance(bt, dict) and bt.get("tag") == "sort":
            return True
        node = node["body"]
    return False


def main():
    chead = set()
    for line in open(os.path.join(DATA, "atlas_classes.jsonl"), encoding="utf-8"):
        chead.add(json.loads(line)["name"].split(".")[-1])
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
    nth = 0
    for line in open(os.path.join(DATA, "atlas_corpus.jsonl"), encoding="utf-8"):
        r = json.loads(line)
        if r.get("kind") != "theorem" or not r.get("module", "").startswith("Mathlib"):
            continue
        name = r["name"]
        if name.split(".")[-1] in GEN_TAILS or name.startswith("_"):
            continue
        sk = skel.get(name)
        ta = r.get("typeAst")
        if sk is None or not sk[0] or not isinstance(ta, dict):
            continue
        nth += 1
        area = r["module"].split(".")[1] if r["module"].count(".") >= 1 else ""
        area_th[area] += 1
        head, ckey, ndef = sk
        g = groups.setdefault((head, ckey, ndef),
                              {"gen": 0, "spec": 0, "ar": collections.Counter(),
                               "car": set()})
        if generic(ta):
            g["gen"] += 1
        else:
            g["spec"] += 1
            g["ar"][area] += 1
            g["car"].add((r.get("namespace") or "").split(".")[0])

    raw = collections.Counter()
    rej = collections.defaultdict(collections.Counter)
    surv = {}
    for (head, ckey, ndef), g in groups.items():
        if g["gen"] > 0 or g["spec"] < MIN_SPEC:
            continue
        dom = max(sorted(g["ar"]), key=lambda a: g["ar"][a])
        raw[dom] += 1
        tail = head.split(".")[-1]
        car = {c for c in g["car"] if c and c != "[anonymous]"
               and c != "definition" and not c.startswith("inst")}
        if tail in chead:
            rej[dom]["classPropHead"] += 1
        elif tail.lower() in LOGIC:
            rej[dom]["logicalHead"] += 1
        elif not ckey:
            rej[dom]["emptyConstraints"] += 1
        elif len(car) < MIN_CARRIERS:
            rej[dom]["singleCarrierOrArtifact"] += 1
        else:
            rej[dom]["survives"] += 1
            surv[head] = (g["spec"], dom, len(car))

    # rebuild density rows
    rebuilt = {}
    for a in area_th:
        rebuilt[a] = (area_th[a], raw[a],
                      round(1000 * raw[a] / area_th[a], 3), dict(rej[a]))

    wdens = [json.loads(l) for l in open(
        os.path.join(DATA, "area_opportunity_density.jsonl"), encoding="utf-8")]
    wshort = [json.loads(l) for l in open(
        os.path.join(DATA, "frontier_generalization_shortlist.jsonl"), encoding="utf-8")]
    summ = json.load(open(os.path.join(DATA, "frontier_scan_summary.json"),
                          encoding="utf-8"))
    errs = []
    if nth != summ["theorems"]:
        errs.append(f"theorems {nth} != {summ['theorems']}")
    if sum(raw.values()) != summ["specializedOnlyShapeGroups"]:
        errs.append("specialized-only total mismatch")
    if len(wshort) != summ["survivorsAfterFilters"]:
        errs.append("shortlist vs summary count")
    if len(wshort) != len(surv):
        errs.append(f"survivors {len(wshort)} != {len(surv)} (must be 5)")
    if len(surv) != 5:
        errs.append(f"global survivor count {len(surv)} != 5 (36 consistency)")
    # density bijection
    if len(wdens) != len(rebuilt):
        errs.append("density row count")
    for w in wdens:
        b = rebuilt.get(w["area"])
        if b is None:
            errs.append(f"area {w['area']} missing")
            continue
        if (w["theorems"], w["specializedOnlyGroups"], w["pressurePer1000"],
                w["rejectReasons"]) != b:
            errs.append(f"area {w['area']} mismatch")
    # shortlist bijection
    for w in wshort:
        b = surv.get(w["conclusionHead"])
        if b is None:
            errs.append(f"survivor {w['conclusionHead']} missing")
        elif (w["nSpecialized"], w["dominantArea"], w["nCarriers"]) != b:
            errs.append(f"survivor {w['conclusionHead']} mismatch")
    # density sorted desc
    vals = [d["pressurePer1000"] for d in wdens]
    if vals != sorted(vals, reverse=True):
        errs.append("density not sorted")
    # bucket means reproduce
    for bk, mv in summ["bucketMeanPressurePer1000"].items():
        v = [b[2] for a, b in rebuilt.items()
             if bucket.get(a) == bk and b[0] >= 500]
        exp = round(sum(v) / len(v), 3) if v else 0.0
        if abs(exp - mv) > 1e-9:
            errs.append(f"bucket {bk} mean {exp} != {mv}")

    print(f"theorems {nth}; specialized-only {sum(raw.values())}; "
          f"survivors {len(surv)}")
    if errs:
        print("VERIFICATION FAILED")
        for e in errs[:30]:
            print("  FAIL:", e)
        sys.exit(1)
    print("density/shortlist/bucket-means/36-consistency all match")
    print("VERIFICATION OK")


if __name__ == "__main__":
    main()
