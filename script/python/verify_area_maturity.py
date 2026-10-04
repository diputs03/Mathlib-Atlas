#!/usr/bin/env python3
"""verify_area_maturity.py — independent rebuild of script 40."""
import json, os, sys, collections

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
DATA = os.path.join(ROOT, "data")

FRONTIER = {"CategoryTheory", "AlgebraicGeometry", "AlgebraicTopology",
            "Condensed", "NumberTheory", "RepresentationTheory", "Geometry",
            "Combinatorics", "Dynamics", "Probability", "MeasureTheory",
            "InformationTheory", "ModelTheory", "SetTheory"}
CORE = {"Algebra", "Data", "Order", "Logic", "GroupTheory", "RingTheory",
        "FieldTheory", "LinearAlgebra", "Topology", "Analysis"}
INFRA = {"Tactic", "Lean", "Control", "Util", "Testing", "Init", "Basic",
         "Computability"}


def area_of(m):
    p = m.split(".")
    return p[1] if len(p) >= 2 and p[0] == "Mathlib" else ""


def bucket(a):
    return "frontier" if a in FRONTIER else "core" if a in CORE else \
           "infra" if a in INFRA else "other"


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
    agg = collections.defaultdict(collections.Counter)
    sv = collections.defaultdict(collections.Counter)
    total = 0
    for line in open(os.path.join(DATA, "atlas_features.jsonl"), encoding="utf-8"):
        r = json.loads(line)
        a = area_of(r.get("module", ""))
        if not a:
            continue
        total += 1
        c = agg[a]
        c["decls"] += 1
        c[r.get("kind", "?")] += 1
        if r.get("isInstance"):
            c["inst"] += 1
        if r.get("kind") == "theorem":
            c["th"] += 1
            if r.get("valueIsRfl"):
                c["rfl"] += 1
            ni = r.get("nInstImplicit", 0) or 0
            nim = r.get("nImplicit", 0) or 0
            sv[a]["ic"] += ni
            if ni == 0 and nim == 0:
                c["conc"] += 1

    rebuilt = {}
    for a, c in agg.items():
        th = c["th"]
        rebuilt[a] = (
            c["decls"], th, c["inst"],
            round(c["rfl"] / th, 4) if th else 0.0,
            round(c["conc"] / th, 4) if th else 0.0,
            round(1 - c["conc"] / th, 4) if th else 0.0,
            round(sv[a]["ic"] / th, 3) if th else 0.0,
            round(c["inst"] / c["decls"], 4),
            bucket(a))

    keys = list(rebuilt)
    rg = pct_rank([rebuilt[a][5] for a in keys])
    rc = pct_rank([rebuilt[a][6] for a in keys])
    rr = pct_rank([rebuilt[a][3] for a in keys])
    ri = pct_rank([rebuilt[a][7] for a in keys])
    mat = {a: round((rg[rebuilt[a][5]] + rc[rebuilt[a][6]] +
                    rr[rebuilt[a][3]] + ri[rebuilt[a][7]]) / 4, 4)
           for a in keys}

    written = [json.loads(l) for l in open(
        os.path.join(DATA, "area_maturity_profile.jsonl"), encoding="utf-8")]
    summary = json.load(open(os.path.join(DATA, "area_maturity_summary.json"),
                             encoding="utf-8"))
    errs = []
    if sum(c["decls"] for c in agg.values()) != total:
        errs.append("internal conservation")
    if total != 574391:
        errs.append(f"total {total} != 574391")
    if sum(r["decls"] for r in written) != total:
        errs.append("written rows don't sum to total")
    if len(written) != len(rebuilt):
        errs.append(f"rows {len(written)} != {len(rebuilt)}")

    prev = None
    for w in written:
        b = rebuilt.get(w["area"])
        if b is None:
            errs.append(f"{w['area']} missing")
            continue
        if (w["decls"], w["theorems"], w["instances"], w["rflFraction"],
                w["concreteTheoremFraction"], w["genericTheoremShare"],
                w["meanInstConstraints"], w["instanceDensity"],
                w["bucket"]) != b:
            errs.append(f"{w['area']} metrics mismatch")
        if abs(w["maturityScore"] - mat[w["area"]]) > 1e-9:
            errs.append(f"{w['area']} maturity {w['maturityScore']} != {mat[w['area']]}")
        if not (0 <= w["maturityScore"] <= 1):
            errs.append(f"{w['area']} maturity out of range")
        cur = (-w["decls"], w["area"])
        if prev is not None and cur < prev:
            errs.append("rows not decl-sorted")
        prev = cur

    # bucket means recompute
    for bname, bs in summary["bucketMeans"].items():
        members = [w for w in written if w["bucket"] == bname]
        if bs["nAreas"] != len(members):
            errs.append(f"bucket {bname} area count")
        if bs["totalDecls"] != sum(x["decls"] for x in members):
            errs.append(f"bucket {bname} decls")
        gm = round(sum(x["genericTheoremShare"] for x in members) / len(members), 4)
        if abs(gm - bs["meanGenericShare"]) > 1e-3:
            errs.append(f"bucket {bname} generic mean {gm} != {bs['meanGenericShare']}")

    # declared buckets echoed
    if set(summary["bucketsDeclared"]["frontier"]) != FRONTIER:
        errs.append("frontier bucket list mismatch")

    print(f"areas {len(written)}; total decls {total}")
    for b in ("core", "frontier", "other", "infra"):
        if b in summary["bucketMeans"]:
            m = summary["bucketMeans"][b]
            print(f"  {b:<9} n={m['nAreas']:<2} maturity={m['meanMaturity']} "
                  f"opp={m['meanOpportunityPressure']} concrete={m['meanConcreteFraction']}")
    if errs:
        print("VERIFICATION FAILED")
        for e in errs[:30]:
            print("  FAIL:", e)
        sys.exit(1)
    print("conservation, per-area metrics, composite, bucket means and order match")
    print("VERIFICATION OK")


if __name__ == "__main__":
    main()
