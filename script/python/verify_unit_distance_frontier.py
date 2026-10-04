#!/usr/bin/env python3
"""verify_unit_distance_frontier.py — independent rebuild of script 46."""
import json, os, re, sys, collections

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
DATA = os.path.join(ROOT, "data")
# independent copy of the ingredient spec (rx, module prefixes, verdict)
SPEC = [
 ("unit_distance_graph", r"unitdist", ["Mathlib.Combinatorics.SimpleGraph.UnitDistance"], "present"),
 ("euclidean_plane", r"euclidean|innerproduct", ["Mathlib.Analysis.InnerProductSpace",
                                          "Mathlib.Geometry.Euclidean"], "present"),
 ("turan_extremal", r"turan", ["Mathlib.Combinatorics.SimpleGraph.Extremal"], "present"),
 ("zarankiewicz_k23", r"zarankiewicz", ["Mathlib.Combinatorics.SimpleGraph.Extremal"], "present"),
 ("abstract_euler_char", r"eulercharacteristic|euler_characteristic",
  ["Mathlib.Algebra.Homology.EulerCharacteristic"], "partial"),
 ("point_line_incidence", r"incidence|incident",
  ["Mathlib.Combinatorics.Enumerative.IncidenceAlgebra",
   "Mathlib.Combinatorics.SimpleGraph"], "absent"),
 ("szemeredi_trotter", r"szemeredi|trotter",
  ["Mathlib.Combinatorics.SimpleGraph.Regularity",
   "Mathlib.Combinatorics.Extremal.RuzsaSzemeredi"], "absent"),
 ("crossing_number", r"crossing|upcrossing", ["Mathlib.Probability.Martingale"], "absent"),
 ("planar_graph", r"planar", ["Mathlib.LinearAlgebra.AffineSpace"], "absent"),
 ("graph_degeneracy", r"degenerat",
  ["Mathlib.AlgebraicTopology.SimplicialSet", "Mathlib.LinearAlgebra.Matrix",
   "Mathlib.LinearAlgebra.RootSystem"], "absent"),
]
EXPECT = {
 "unit_distance_graph": ["Mathlib.Combinatorics.SimpleGraph.UnitDistance"],
 "euclidean_plane": ["Mathlib.Analysis.InnerProductSpace"],
 "turan_extremal": ["Mathlib.Combinatorics.SimpleGraph.Extremal.Turan"],
 "zarankiewicz_k23": ["Mathlib.Combinatorics.SimpleGraph.Extremal.Zarankiewicz"],
 "abstract_euler_char": ["Mathlib.Algebra.Homology.EulerCharacteristic"],
 "point_line_incidence": [], "szemeredi_trotter": [], "crossing_number": [],
 "planar_graph": [], "graph_degeneracy": [],
}


def main():
    acc = {i: {"d": 0, "mc": collections.Counter()} for i, _, _, _ in SPEC}
    rxs = {i: re.compile(rx, re.I) for i, rx, _, _ in SPEC}
    for line in open(os.path.join(DATA, "atlas_features.jsonl"), encoding="utf-8"):
        r = json.loads(line)
        nm, mod = r["name"], r["module"]
        for i, _, prefs, _ in SPEC:
            hd = bool(rxs[i].search(nm))
            hm = any(mod.startswith(p) for p in prefs)
            if hd:
                acc[i]["d"] += 1
            if hm:
                acc[i]["mc"][mod] += 1

    written = {r["id"]: r for r in (json.loads(l) for l in open(
        os.path.join(DATA, "unit_distance_frontier.jsonl"), encoding="utf-8"))}
    summ = json.load(open(os.path.join(DATA, "unit_distance_frontier_summary.json"),
                          encoding="utf-8"))
    errs = []
    if set(written) != {i for i, *_ in SPEC}:
        errs.append("ingredient set mismatch")
    for i, _, _, verdict in SPEC:
        w = written.get(i)
        if w is None:
            continue
        a = acc[i]
        if w["directNameHits"] != a["d"]:
            errs.append(f"{i}: direct {w['directNameHits']} != {a['d']}")
        exp = sum(c for m, c in a["mc"].items()
                  if any(m.startswith(e) for e in EXPECT[i]))
        if w["expectedModuleDecls"] != exp:
            errs.append(f"{i}: expected {w['expectedModuleDecls']} != {exp}")
        if w["verdict"] != verdict:
            errs.append(f"{i}: verdict {w['verdict']} != {verdict}")
        # internal consistency
        if verdict == "present" and exp == 0:
            errs.append(f"{i}: marked present but 0 expected-module decls")
        if verdict == "absent" and exp != 0:
            errs.append(f"{i}: marked absent but has expected-module decls")
        # matched-module bijection
        wm = {m["module"]: m["n"] for m in w["allMatchedModules"]}
        am = dict(a["mc"].most_common(8))
        if wm != am:
            errs.append(f"{i}: matched-module list mismatch")
    bv = collections.Counter(v for _, _, _, v in SPEC)
    if summ["byVerdict"] != dict(bv):
        errs.append("summary byVerdict mismatch")
    fr = [i for i, _, _, v in SPEC if v != "present"]
    if summ["missingOrPartialFrontier"] != fr:
        errs.append("frontier list mismatch")

    for i, _, _, v in SPEC:
        print(f"{v:<8} {i:<24} direct={acc[i]['d']:<4} "
              f"expected={sum(c for m,c in acc[i]['mc'].items() if any(m.startswith(e) for e in EXPECT[i]))}")
    if errs:
        print("VERIFICATION FAILED")
        for e in errs[:30]:
            print("  FAIL:", e)
        sys.exit(1)
    print("counts, module lists, verdict consistency, summary all match")
    print("VERIFICATION OK")


if __name__ == "__main__":
    main()
