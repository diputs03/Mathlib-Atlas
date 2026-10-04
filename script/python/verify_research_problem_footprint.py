#!/usr/bin/env python3
"""verify_research_problem_footprint.py — independent rebuild of script 45."""
import json, os, re, sys, collections

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
DATA = os.path.join(ROOT, "data")
# same profile spec, declared independently here
SPEC = {
 "navier_stokes": (r"navier|stokes", ["Mathlib.Analysis.ODE"]),
 "collatz": (r"hailstone|collatz",
             ["Mathlib.Dynamics.PeriodicPts", "Mathlib.Dynamics.OmegaLimit",
              "Mathlib.Dynamics.FixedPoints"]),
 "multicolor_ramsey": (r"ramsey",
             ["Mathlib.Combinatorics.SimpleGraph.Coloring",
              "Mathlib.Combinatorics.SimpleGraph.Clique",
              "Mathlib.Combinatorics.SimpleGraph.Extremal"]),
 "erdos_unit_distance": (r"unitdist",
             ["Mathlib.Combinatorics.SimpleGraph.UnitDistance",
              "Mathlib.Combinatorics.SimpleGraph.Extremal"]),
 "jacobian_conjecture": (r"jacobianconjecture",
             ["Mathlib.MeasureTheory.Function.Jacobian", "Mathlib.RingTheory.Etale",
              "Mathlib.AlgebraicGeometry.Morphisms.Etale",
              "Mathlib.RingTheory.Extension.Presentation",
              "Mathlib.Algebra.MvPolynomial"]),
 "fermat_last_theorem_control": (r"fermat", ["Mathlib.NumberTheory.FLT"]),
}


def main():
    acc = {k: {"d": 0, "s": 0, "mods": collections.Counter(),
               "kinds": collections.Counter()} for k in SPEC}
    rx = {k: re.compile(v[0], re.I) for k, v in SPEC.items()}
    for line in open(os.path.join(DATA, "atlas_features.jsonl"), encoding="utf-8"):
        r = json.loads(line)
        nm, mod = r["name"], r["module"]
        for k, (_, sup) in SPEC.items():
            hd = bool(rx[k].search(nm))
            hs = any(mod.startswith(p) for p in sup)
            if not (hd or hs):
                continue
            if hd:
                acc[k]["d"] += 1
            if hs:
                acc[k]["s"] += 1
            acc[k]["mods"][mod] += 1
            acc[k]["kinds"][r.get("kind", "?")] += 1

    written = {r["id"]: r for r in (json.loads(l) for l in open(
        os.path.join(DATA, "research_problem_footprint.jsonl"), encoding="utf-8"))}
    summ = json.load(open(os.path.join(DATA, "research_problem_summary.json"),
                          encoding="utf-8"))
    errs = []
    if set(written) != set(SPEC):
        errs.append(f"problem set {set(written)} != {set(SPEC)}")
    for k, a in acc.items():
        w = written.get(k)
        if w is None:
            continue
        if w["directNamedDecls"] != a["d"]:
            errs.append(f"{k}: direct {w['directNamedDecls']} != {a['d']}")
        if w["supportDecls"] != a["s"]:
            errs.append(f"{k}: support {w['supportDecls']} != {a['s']}")
        if w["nSupportModules"] != len(a["mods"]):
            errs.append(f"{k}: module count {w['nSupportModules']} != {len(a['mods'])}")
        if w["kinds"] != dict(a["kinds"]):
            errs.append(f"{k}: kinds mismatch")
        # module list bijection
        wmods = {m["module"]: m["n"] for m in w["topModules"]}
        amods = dict(a["mods"].most_common(12))
        if wmods != amods:
            errs.append(f"{k}: topModules mismatch")
        # status consistency
        expect = ("named-material-present" if a["d"] > 0 else
                  "supporting-machinery-only" if a["s"] > 0 else "absent")
        if w["status"] != expect:
            errs.append(f"{k}: status {w['status']} != {expect}")
    # summary cross-check
    for sp in summ["problems"]:
        a = acc[sp["id"]]
        if sp["direct"] != a["d"] or sp["support"] != a["s"]:
            errs.append(f"summary {sp['id']} mismatch")

    for k in SPEC:
        print(f"{k:<30} direct={acc[k]['d']:<4} support={acc[k]['s']:<5} "
              f"modules={len(acc[k]['mods'])}")
    if errs:
        print("VERIFICATION FAILED")
        for e in errs[:30]:
            print("  FAIL:", e)
        sys.exit(1)
    print("counts, module lists, kinds, status, summary all match")
    print("VERIFICATION OK")


if __name__ == "__main__":
    main()
