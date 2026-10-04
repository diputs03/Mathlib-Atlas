#!/usr/bin/env python3
"""46_unit_distance_frontier.py — dependency frontier for Erdos unit-distance.

Script 45 ranked Erdos unit-distance the most research-ready target. The classic
O(n^{4/3}) upper bound (Spencer-Szemeredi-Trotter) needs a specific chain of
ingredients. This script measures, reproducibly from atlas_features.jsonl, the
formal footprint of EACH ingredient (name regex + adjacent module prefixes) and
pairs it with a curated verdict (present / partial / absent) and an explicit
note where a keyword is a FALSE FRIEND (same word, different math).

The script computes raw footprints; the verdict/note are authored analysis and
are checked for internal consistency (an 'absent' ingredient must have 0 direct
hits; a 'present' ingredient must have >0 in its expected modules).

Outputs: data/unit_distance_frontier.jsonl, data/unit_distance_frontier_summary.json
Pure stdlib, streaming, deterministic.
"""
import json, os, re, collections

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
DATA = os.path.join(ROOT, "data")

# proof-order ingredients. layer: combinatorial / geometric / topological.
# verdict is the authored classification; expectModules are where a 'present'
# ingredient must actually live (to defeat false-friend keyword hits).
INGREDIENTS = [
    {"id": "unit_distance_graph", "layer": "combinatorial", "step": 1,
     "role": "The unit-distance graph object itself",
     "rx": r"unitdist", "modules": ["Mathlib.Combinatorics.SimpleGraph.UnitDistance"],
     "verdict": "present", "expectModules": ["Mathlib.Combinatorics.SimpleGraph.UnitDistance"]},
    {"id": "euclidean_plane", "layer": "geometric", "step": 2,
     "role": "Euclidean plane / inner-product space hosting the points",
     "rx": r"euclidean|innerproduct", "modules": ["Mathlib.Analysis.InnerProductSpace",
                                            "Mathlib.Geometry.Euclidean"],
     "verdict": "present", "expectModules": ["Mathlib.Analysis.InnerProductSpace"]},
    {"id": "turan_extremal", "layer": "combinatorial", "step": 3,
     "role": "Extremal graph bounds (baseline)",
     "rx": r"turan", "modules": ["Mathlib.Combinatorics.SimpleGraph.Extremal"],
     "verdict": "present", "expectModules": ["Mathlib.Combinatorics.SimpleGraph.Extremal.Turan"]},
    {"id": "zarankiewicz_k23", "layer": "combinatorial", "step": 4,
     "role": "K_{s,t}-free / Zarankiewicz bound (two points share <=2 unit circles)",
     "rx": r"zarankiewicz", "modules": ["Mathlib.Combinatorics.SimpleGraph.Extremal"],
     "verdict": "present",
     "expectModules": ["Mathlib.Combinatorics.SimpleGraph.Extremal.Zarankiewicz"]},
    {"id": "abstract_euler_char", "layer": "topological", "step": 5,
     "role": "Euler characteristic (abstract/homological) — building block",
     "rx": r"eulercharacteristic|euler_characteristic",
     "modules": ["Mathlib.Algebra.Homology.EulerCharacteristic"],
     "verdict": "partial", "expectModules": ["Mathlib.Algebra.Homology.EulerCharacteristic"]},
    {"id": "point_line_incidence", "layer": "geometric", "step": 6,
     "role": "Geometric point-line incidence counts (I(P,L))",
     "rx": r"incidence|incident",
     "modules": ["Mathlib.Combinatorics.Enumerative.IncidenceAlgebra",
                 "Mathlib.Combinatorics.SimpleGraph"],
     "verdict": "absent", "expectModules": [],
     "note": "Keyword hits are combinatorial IncidenceAlgebra (Mobius) and graph "
             "edge-vertex incidence, NOT geometric point-line incidences."},
    {"id": "szemeredi_trotter", "layer": "geometric", "step": 7,
     "role": "Szemeredi-Trotter incidence theorem",
     "rx": r"szemeredi|trotter",
     "modules": ["Mathlib.Combinatorics.SimpleGraph.Regularity",
                 "Mathlib.Combinatorics.Extremal.RuzsaSzemeredi"],
     "verdict": "absent", "expectModules": [],
     "note": "False friend: present material is the Szemeredi REGULARITY lemma and "
             "Ruzsa-Szemeredi graphs, not the Szemeredi-Trotter incidence bound."},
    {"id": "crossing_number", "layer": "topological", "step": 8,
     "role": "Graph crossing-number / crossing lemma",
     "rx": r"crossing|upcrossing",
     "modules": ["Mathlib.Probability.Martingale"],
     "verdict": "absent", "expectModules": [],
     "note": "False friend: hits are martingale upcrossing inequalities; no graph "
             "crossing number exists."},
    {"id": "planar_graph", "layer": "topological", "step": 9,
     "role": "Planar graphs / planar embedding + V-E+F=2",
     "rx": r"planar", "modules": ["Mathlib.LinearAlgebra.AffineSpace"],
     "verdict": "absent", "expectModules": [],
     "note": "False friend: 'planar' means coplanar affine vectors; no planar graph "
             "theory or planar Euler formula."},
    {"id": "graph_degeneracy", "layer": "combinatorial", "step": 10,
     "role": "Graph degeneracy (k-degenerate) used in crossing->edge bound",
     "rx": r"degenerat",
     "modules": ["Mathlib.AlgebraicTopology.SimplicialSet",
                 "Mathlib.LinearAlgebra.Matrix", "Mathlib.LinearAlgebra.RootSystem"],
     "verdict": "absent", "expectModules": [],
     "note": "False friend: 'nondegenerate' matrices/simplices/root systems; no "
             "graph degeneracy ordering."},
]


def main():
    for ing in INGREDIENTS:
        ing["_rx"] = re.compile(ing["rx"], re.I)
        ing["direct"] = 0
        ing["modcounts"] = collections.Counter()
        ing["kinds"] = collections.Counter()

    for line in open(os.path.join(DATA, "atlas_features.jsonl"), encoding="utf-8"):
        r = json.loads(line)
        nm, mod = r.get("name", ""), r.get("module", "")
        for ing in INGREDIENTS:
            if ing["_rx"].search(nm) or any(mod.startswith(p) for p in ing["modules"]):
                if ing["_rx"].search(nm):
                    ing["direct"] += 1
                if any(mod.startswith(p) for p in ing["modules"]):
                    ing["modcounts"][mod] += 1
                    ing["kinds"][r.get("kind", "?")] += 1

    rows = []
    for ing in sorted(INGREDIENTS, key=lambda x: x["step"]):
        expect_hits = sum(c for m, c in ing["modcounts"].items()
                          if any(m.startswith(e) for e in ing["expectModules"]))
        rows.append({
            "step": ing["step"], "id": ing["id"], "layer": ing["layer"],
            "role": ing["role"], "verdict": ing["verdict"],
            "directNameHits": ing["direct"],
            "expectedModuleDecls": expect_hits,
            "allMatchedModules": [{"module": m, "n": c}
                                  for m, c in ing["modcounts"].most_common(8)],
            "note": ing.get("note", "")})
    with open(os.path.join(DATA, "unit_distance_frontier.jsonl"),
              "wb") as o:
        for r in rows:
            o.write((json.dumps(r, ensure_ascii=False) + "\n").encode("utf-8"))

    by_v = collections.Counter(r["verdict"] for r in rows)
    frontier = [r["id"] for r in rows if r["verdict"] != "present"]
    summary = {
        "target": "Erdos unit-distance upper bound (Spencer-Szemeredi-Trotter O(n^{4/3}))",
        "nIngredients": len(rows),
        "byVerdict": dict(by_v),
        "missingOrPartialFrontier": frontier,
        "presentChain": [r["id"] for r in rows if r["verdict"] == "present"],
    }
    with open(os.path.join(DATA, "unit_distance_frontier_summary.json"), "w",
              encoding="utf-8") as o:
        json.dump(summary, o, ensure_ascii=False, indent=2)

    for r in rows:
        flag = {"present": "OK ", "partial": "~~ ", "absent": "GAP"}[r["verdict"]]
        print(f"{flag} step{r['step']:>2} [{r['layer']:<13}] {r['id']:<24} "
              f"direct={r['directNameHits']:<4} expected={r['expectedModuleDecls']}")
        if r["note"]:
            print(f"        note: {r['note']}")
    print("\nby verdict:", dict(by_v))
    print("frontier (build these):", frontier)


if __name__ == "__main__":
    main()
