#!/usr/bin/env python3
"""41_combined_bridge_ranking.py — reconcile the three theory-bridge views.

Atlas now has three INDEPENDENT measures of how mathematical areas are coupled:
  * R reference edges (14): directed declaration-term references between areas;
  * N shared namespaces (38): a namespace opened/used in both areas;
  * I shared typeclasses (39): an abstract class instantiated in both areas.
This script brings them to a common area-pair / area scale (each view divided by
its own maximum -> [0,1]) and produces:
  * combined AREA-PAIR coupling (three raw + three normalized + mean + #views),
  * per-area bridge centrality across the three mechanisms,
  * agreement analysis: pairs robust in all three vs mechanism-specific.

Inputs : data/atlas_area_edges.jsonl, data/namespace_crosscutting.jsonl,
         data/area_class_bridges.jsonl, data/area_maturity_profile.jsonl
Outputs: data/theory_bridge_area_pairs.jsonl, data/theory_bridge_areas.jsonl,
         data/theory_bridge_summary.json
Pure stdlib, deterministic.
"""
import json, os, itertools, collections

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
DATA = os.path.join(ROOT, "data")


def norm(d):
    if not d:
        return {}
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
    # ---- view R: reference edges (symmetrize directed) ----
    ref = collections.Counter()
    for line in open(os.path.join(DATA, "atlas_area_edges.jsonl"), encoding="utf-8"):
        e = json.loads(line)
        a, b = e["sourceArea"], e["targetArea"]
        if a == b:
            continue
        key = tuple(sorted((a, b)))
        ref[key] += e["refs"]

    # ---- view N: shared cross-cutting namespaces ----
    nsp = collections.Counter()
    for line in open(os.path.join(DATA, "namespace_crosscutting.jsonl"), encoding="utf-8"):
        r = json.loads(line)
        if r["nAreas"] < 2:
            continue
        areas = sorted({x["area"] for x in r["areas"]})
        for a, b in itertools.combinations(areas, 2):
            nsp[(a, b)] += 1

    # ---- view I: shared typeclasses ----
    inst = {}
    for line in open(os.path.join(DATA, "area_class_bridges.jsonl"), encoding="utf-8"):
        r = json.loads(line)
        inst[(r["areaA"], r["areaB"])] = r["sharedClasses"]

    # union of pairs, normalized per view
    pairs = sorted(set(ref) | set(nsp) | set(inst))
    rn, nn_, inn = norm(ref), norm(nsp), norm(inst)
    pair_rows = []
    for key in pairs:
        a, b = key
        rR, rN, rI = rn.get(key, 0.0), nn_.get(key, 0.0), inn.get(key, 0.0)
        nviews = int(ref.get(key, 0) > 0) + int(nsp.get(key, 0) > 0) + \
                 int(inst.get(key, 0) > 0)
        comp = (rR + rN + rI) / 3
        pair_rows.append({
            "areaA": a, "areaB": b,
            "refEdges": ref.get(key, 0), "sharedNamespaces": nsp.get(key, 0),
            "sharedClasses": inst.get(key, 0),
            "refNorm": round(rR, 4), "nsNorm": round(rN, 4),
            "classNorm": round(rI, 4),
            "composite": round(comp, 4), "nViews": nviews})
    pair_rows.sort(key=lambda x: (-x["composite"], x["areaA"], x["areaB"]))
    with open(os.path.join(DATA, "theory_bridge_area_pairs.jsonl"), "wb") as o:
        for r in pair_rows:
            o.write((json.dumps(r, ensure_ascii=False) + "\n").encode("utf-8"))

    # ---- per-area centrality: sum incident normalized coupling per view ----
    areas = sorted({a for k in pairs for a in k})
    inc = {a: collections.Counter() for a in areas}
    for r in pair_rows:
        for a in (r["areaA"], r["areaB"]):
            inc[a]["R"] += r["refNorm"]
            inc[a]["N"] += r["nsNorm"]
            inc[a]["I"] += r["classNorm"]
    rkR = pct_rank([inc[a]["R"] for a in areas])
    rkN = pct_rank([inc[a]["N"] for a in areas])
    rkI = pct_rank([inc[a]["I"] for a in areas])
    # context: bucket + decls
    ctx = {}
    mp = os.path.join(DATA, "area_maturity_profile.jsonl")
    if os.path.exists(mp):
        for line in open(mp, encoding="utf-8"):
            r = json.loads(line)
            ctx[r["area"]] = (r["bucket"], r["decls"])
    area_rows = []
    for a in areas:
        c = inc[a]
        comp = (rkR[c["R"]] + rkN[c["N"]] + rkI[c["I"]]) / 3
        b, d = ctx.get(a, ("other", 0))
        area_rows.append({
            "area": a, "bucket": b, "decls": d,
            "refCentrality": round(rkR[c["R"]], 4),
            "namespaceCentrality": round(rkN[c["N"]], 4),
            "classCentrality": round(rkI[c["I"]], 4),
            "compositeBridge": round(comp, 4)})
    area_rows.sort(key=lambda x: -x["compositeBridge"])
    with open(os.path.join(DATA, "theory_bridge_areas.jsonl"), "wb") as o:
        for r in area_rows:
            o.write((json.dumps(r, ensure_ascii=False) + "\n").encode("utf-8"))

    # ---- agreement analysis ----
    by_views = collections.Counter(r["nViews"] for r in pair_rows)
    robust = [r for r in pair_rows if r["nViews"] == 3]
    only = {v: [r for r in pair_rows if r["nViews"] == 1 and
                ((r["refEdges"] > 0) if v == "R" else
                 (r["sharedNamespaces"] > 0) if v == "N" else
                 (r["sharedClasses"] > 0))] for v in ("R", "N", "I")}
    summary = {
        "areaPairs": len(pair_rows),
        "pairsByViewCount": dict(sorted(by_views.items())),
        "robustPairsAll3Views": len(robust),
        "topCombinedPairs": pair_rows[:20],
        "topBridgeAreas": area_rows[:15],
        "referenceOnlyPairs": sorted(
            only["R"], key=lambda x: -x["refNorm"])[:8],
        "namespaceOnlyPairs": sorted(
            only["N"], key=lambda x: -x["nsNorm"])[:8],
        "classOnlyPairs": sorted(
            only["I"], key=lambda x: -x["classNorm"])[:8],
    }
    with open(os.path.join(DATA, "theory_bridge_summary.json"), "w",
              encoding="utf-8") as o:
        json.dump(summary, o, ensure_ascii=False, indent=2)

    print(f"area pairs {len(pair_rows)}; by #views {dict(sorted(by_views.items()))}; "
          f"robust(all 3) {len(robust)}")
    print("top combined area pairs (R-ref / N-ns / I-class, composite, views):")
    for r in pair_rows[:15]:
        print(f"  {r['areaA']:<16}- {r['areaB']:<16} "
              f"R={r['refNorm']:<6} N={r['nsNorm']:<6} I={r['classNorm']:<6} "
              f"comp={r['composite']:<6} v={r['nViews']}")
    print("top bridge areas:")
    for r in area_rows[:12]:
        print(f"  {r['area']:<18} {r['bucket']:<9} R={r['refCentrality']:<6} "
              f"N={r['namespaceCentrality']:<6} I={r['classCentrality']:<6} "
              f"comp={r['compositeBridge']}")


if __name__ == "__main__":
    main()
