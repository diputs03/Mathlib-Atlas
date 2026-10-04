#!/usr/bin/env python3
"""45_research_problem_footprint.py — famous modern/open problems in the corpus.

The user's "frontier" means research-level / famous open problems (Navier-Stokes,
Collatz, multicolor Ramsey numbers, Erdos unit-distance, Jacobian conjecture),
not Mathlib's internal area buckets. For a curated problem list this measures,
reproducibly from atlas_features.jsonl:

  direct   : declarations whose NAME names the problem/object (regex)
  support  : declarations in named adjacent-theory modules (prefix match) that
             would be the formal scaffolding for an attack
and records the top-level (non _private) exemplar declarations. Fermat's Last
Theorem (n=3,4 actually proved in Mathlib) is included as a positive control.

This script measures FORMAL FOOTPRINT ONLY; whether the open statement itself is
present (it is not, for all five open problems) is annotated in the note.
Outputs: data/research_problem_footprint.jsonl, data/research_problem_summary.json
Pure stdlib, streaming, deterministic.
"""
import json, os, re, collections

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
DATA = os.path.join(ROOT, "data")

# direct: name regex (problem-named object). support: module-prefixes (scaffold).
PROBLEMS = [
    {"id": "navier_stokes", "area": "Analysis/PDE",
     "name": "Navier-Stokes existence & smoothness (Clay Millennium)",
     "direct": r"navier|stokes",
     "support": ["Mathlib.Analysis.ODE"]},
    {"id": "collatz", "area": "Dynamics/NumberTheory",
     "name": "Collatz (3x+1) conjecture",
     "direct": r"hailstone|collatz",
     "support": ["Mathlib.Dynamics.PeriodicPts", "Mathlib.Dynamics.OmegaLimit",
                 "Mathlib.Dynamics.FixedPoints"]},
    {"id": "multicolor_ramsey", "area": "Combinatorics",
     "name": "Multicolor Ramsey numbers R(r1,...,rk)",
     "direct": r"ramsey",
     "support": ["Mathlib.Combinatorics.SimpleGraph.Coloring",
                 "Mathlib.Combinatorics.SimpleGraph.Clique",
                 "Mathlib.Combinatorics.SimpleGraph.Extremal"]},
    {"id": "erdos_unit_distance", "area": "Combinatorics/Geometry",
     "name": "Erdos unit-distance problem in the plane",
     "direct": r"unitdist",
     "support": ["Mathlib.Combinatorics.SimpleGraph.UnitDistance",
                 "Mathlib.Combinatorics.SimpleGraph.Extremal"]},
    {"id": "jacobian_conjecture", "area": "AlgebraicGeometry/RingTheory",
     "name": "Jacobian conjecture (polynomial automorphism)",
     "direct": r"jacobianconjecture",
     "support": ["Mathlib.MeasureTheory.Function.Jacobian",
                 "Mathlib.RingTheory.Etale",
                 "Mathlib.AlgebraicGeometry.Morphisms.Etale",
                 "Mathlib.RingTheory.Extension.Presentation",
                 "Mathlib.Algebra.MvPolynomial"]},
    {"id": "fermat_last_theorem_control", "area": "NumberTheory",
     "name": "Fermat's Last Theorem (positive control; n=3,4 proved in Mathlib)",
     "direct": r"fermat",
     "support": ["Mathlib.NumberTheory.FLT"]},
]


def main():
    for p in PROBLEMS:
        p["_drx"] = re.compile(p["direct"], re.I)
        p["directN"] = 0
        p["supportN"] = 0
        p["modules"] = collections.Counter()
        p["kinds"] = collections.Counter()
        p["exemplars"] = []

    for line in open(os.path.join(DATA, "atlas_features.jsonl"), encoding="utf-8"):
        r = json.loads(line)
        nm, mod = r.get("name", ""), r.get("module", "")
        for p in PROBLEMS:
            hit_d = bool(p["_drx"].search(nm))
            hit_s = any(mod.startswith(pre) for pre in p["support"])
            if not (hit_d or hit_s):
                continue
            if hit_d:
                p["directN"] += 1
            if hit_s:
                p["supportN"] += 1
            p["modules"][mod] += 1
            p["kinds"][r.get("kind", "?")] += 1
            if hit_d and not nm.startswith("_private") and len(p["exemplars"]) < 18:
                p["exemplars"].append(nm)

    rows = []
    for p in PROBLEMS:
        if p["directN"] > 0:
            status = "named-material-present"
        elif p["supportN"] > 0:
            status = "supporting-machinery-only"
        else:
            status = "absent"
        rows.append({
            "id": p["id"], "problem": p["name"], "area": p["area"],
            "status": status,
            "directNamedDecls": p["directN"], "supportDecls": p["supportN"],
            "nSupportModules": len(p["modules"]),
            "kinds": dict(p["kinds"]),
            "topModules": [{"module": m, "n": c}
                           for m, c in p["modules"].most_common(12)],
            "namedExemplars": sorted(set(p["exemplars"]))[:18],
        })
    rows.sort(key=lambda r: r["id"])
    with open(os.path.join(DATA, "research_problem_footprint.jsonl"),
              "wb") as o:
        for r in rows:
            o.write((json.dumps(r, ensure_ascii=False) + "\n").encode("utf-8"))
    summary = {
        "corpusCommit": "bbcd1968ee6950abe88b85dba6995da346c4b2a8",
        "nProblems": len(rows),
        "problems": [{"id": r["id"], "status": r["status"],
                      "direct": r["directNamedDecls"], "support": r["supportDecls"]}
                     for r in rows],
    }
    with open(os.path.join(DATA, "research_problem_summary.json"), "w",
              encoding="utf-8") as o:
        json.dump(summary, o, ensure_ascii=False, indent=2)

    for r in rows:
        print(f"\n{r['id']:<28} {r['status']:<26} "
              f"direct={r['directNamedDecls']:<4} support={r['supportDecls']:<5} "
              f"modules={r['nSupportModules']}")
        for m in r["topModules"][:6]:
            print(f"    {m['n']:4d} {m['module']}")
        if r["namedExemplars"]:
            print("    exemplars:", ", ".join(r["namedExemplars"][:8]))


if __name__ == "__main__":
    main()
