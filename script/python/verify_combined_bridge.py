#!/usr/bin/env python3
"""verify_combined_bridge.py — independent rebuild of script 41."""
import json, os, sys, itertools, collections

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
DATA = os.path.join(ROOT, "data")


def norm(d):
    mx = max(d.values()) or 1
    return {k: v / mx for k, v in d.items()}


def pct_rank(values):
    order = sorted(values)
    n = len(order)
    out, i = {}, 0
    while i < n:
        j = i
        while j + 1 < n and order[j + 1] == order[i]:
            j += 1
        rk = (i + j) / 2 / max(1, n - 1)
        for k in range(i, j + 1):
            out[order[k]] = rk
        i = j + 1
    return out


def main():
    ref = collections.Counter()
    for line in open(os.path.join(DATA, "atlas_area_edges.jsonl"), encoding="utf-8"):
        e = json.loads(line)
        if e["sourceArea"] == e["targetArea"]:
            continue
        ref[tuple(sorted((e["sourceArea"], e["targetArea"])))] += e["refs"]
    nsp = collections.Counter()
    for line in open(os.path.join(DATA, "namespace_crosscutting.jsonl"), encoding="utf-8"):
        r = json.loads(line)
        if r["nAreas"] < 2:
            continue
        for a, b in itertools.combinations(sorted({x["area"] for x in r["areas"]}), 2):
            nsp[(a, b)] += 1
    inst = {}
    for line in open(os.path.join(DATA, "area_class_bridges.jsonl"), encoding="utf-8"):
        r = json.loads(line)
        inst[(r["areaA"], r["areaB"])] = r["sharedClasses"]

    pairs = sorted(set(ref) | set(nsp) | set(inst))
    rn, nn_, ii = norm(ref), norm(nsp), norm(inst)
    rebuilt = {}
    for k in pairs:
        rR, rN, rI = rn.get(k, 0.0), nn_.get(k, 0.0), ii.get(k, 0.0)
        nv = int(ref.get(k, 0) > 0) + int(nsp.get(k, 0) > 0) + int(inst.get(k, 0) > 0)
        rebuilt[k] = (ref.get(k, 0), nsp.get(k, 0), inst.get(k, 0),
                      round(rR, 4), round(rN, 4), round(rI, 4),
                      round((rR + rN + rI) / 3, 4), nv)

    wr = [json.loads(l) for l in open(
        os.path.join(DATA, "theory_bridge_area_pairs.jsonl"), encoding="utf-8")]
    wa = [json.loads(l) for l in open(
        os.path.join(DATA, "theory_bridge_areas.jsonl"), encoding="utf-8")]
    summ = json.load(open(os.path.join(DATA, "theory_bridge_summary.json"),
                          encoding="utf-8"))
    errs = []
    if len(wr) != len(pairs):
        errs.append(f"pair rows {len(wr)} != {len(pairs)}")
    if summ["areaPairs"] != len(pairs):
        errs.append("summary pair count")
    if summ["robustPairsAll3Views"] != sum(1 for k in pairs if rebuilt[k][7] == 3):
        errs.append("robust count")
    prev = None
    for w in wr:
        k = (w["areaA"], w["areaB"])
        b = rebuilt.get(k)
        if b is None:
            errs.append(f"pair {k} missing")
            continue
        exp = (w["refEdges"], w["sharedNamespaces"], w["sharedClasses"],
               w["refNorm"], w["nsNorm"], w["classNorm"], w["composite"], w["nViews"])
        if exp != b:
            errs.append(f"pair {k}: {exp} != {b}")
        if not (0 <= w["composite"] <= 1):
            errs.append(f"pair {k} composite range")
        cur = -w["composite"]
        if prev is not None and cur < prev - 1e-12:
            errs.append(f"pairs not composite-sorted at {k}")
        prev = cur

    # area centrality rebuild
    areas = sorted({a for k in pairs for a in k})
    inc = {a: collections.Counter() for a in areas}
    for w in wr:
        for a in (w["areaA"], w["areaB"]):
            inc[a]["R"] += w["refNorm"]
            inc[a]["N"] += w["nsNorm"]
            inc[a]["I"] += w["classNorm"]
    rR, rN, rI = (pct_rank([inc[a][v] for a in areas]) for v in ("R", "N", "I"))
    amap = {r["area"]: r for r in wa}
    if len(wa) != len(areas):
        errs.append(f"area rows {len(wa)} != {len(areas)}")
    for a in areas:
        w = amap.get(a)
        if w is None:
            errs.append(f"area {a} missing")
            continue
        exp = (round(rR[inc[a]["R"]], 4), round(rN[inc[a]["N"]], 4),
               round(rI[inc[a]["I"]], 4),
               round((rR[inc[a]["R"]] + rN[inc[a]["N"]] + rI[inc[a]["I"]]) / 3, 4))
        got = (w["refCentrality"], w["namespaceCentrality"],
               w["classCentrality"], w["compositeBridge"])
        if exp != got:
            errs.append(f"area {a}: {got} != {exp}")
    # area rows sorted desc
    vals = [r["compositeBridge"] for r in wa]
    if vals != sorted(vals, reverse=True):
        errs.append("area rows not sorted")

    byv = collections.Counter(b[7] for b in rebuilt.values())
    if summ["pairsByViewCount"] != {str(k): v for k, v in sorted(byv.items())}:
        errs.append(f"byViewCount {summ['pairsByViewCount']} != {dict(byv)}")

    print(f"pairs {len(pairs)} (by views {dict(byv)}), areas {len(areas)}")
    if errs:
        print("VERIFICATION FAILED")
        for e in errs[:30]:
            print("  FAIL:", e)
        sys.exit(1)
    print("pair/area bijections, normalizations, composites and order match")
    print("VERIFICATION OK")


if __name__ == "__main__":
    main()
