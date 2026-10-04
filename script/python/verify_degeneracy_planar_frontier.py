#!/usr/bin/env python3
"""verify_degeneracy_planar_frontier.py — independent rebuild of script 47."""
import json, os, re, sys, collections

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
DATA = os.path.join(ROOT, "data")
SCOPE = ("Mathlib.Combinatorics.SimpleGraph", "Mathlib.Combinatorics.Graph")
SPEC = [
 ("graph_degeneracy", "vertex_degree", r"\bdegree\b", "present"),
 ("graph_degeneracy", "neighbor_set", r"neighborSet", "present"),
 ("graph_degeneracy", "subgraph_induce_delete", r"subgraph|induce|deleteVerts", "present"),
 ("graph_degeneracy", "min_degree_vertex", r"minimal_degree|minDegree|degree_le", "present"),
 ("graph_degeneracy", "greedy_coloring", r"coloring|colorable", "present"),
 ("graph_degeneracy", "elimination_ordering",
  r"linearorder|wellfounded|elimination|peeling|degeneracyorder", "absent"),
 ("graph_degeneracy", "degeneracy_theorem", r"degener", "absent"),
 ("planar_graph", "cycles", r"iscycle|\bcycle\b", "present"),
 ("planar_graph", "connectedness", r"connected", "present"),
 ("planar_graph", "trees_acyclic", r"istree|acyclic|\btree\b", "present"),
 ("planar_graph", "plane_drawing", r"embed|drawing|plane", "absent"),
 ("planar_graph", "faces", r"\bface\b|outerface|region", "absent"),
 ("planar_graph", "planar_euler_formula", r"euler(?!ian)", "absent"),
]


def main():
    acc = {(t, i): {"n": 0, "mods": collections.Counter()} for t, i, _, _ in SPEC}
    rxs = {(t, i): re.compile(rx, re.I) for t, i, rx, _ in SPEC}
    for line in open(os.path.join(DATA, "atlas_features.jsonl"), encoding="utf-8"):
        r = json.loads(line)
        if not r["module"].startswith(SCOPE):
            continue
        for key, p in rxs.items():
            if p.search(r["name"]):
                acc[key]["n"] += 1
                acc[key]["mods"][r["module"]] += 1

    written = {(r["target"], r["id"]): r for r in (json.loads(l) for l in open(
        os.path.join(DATA, "degeneracy_planar_frontier.jsonl"), encoding="utf-8"))}
    summ = json.load(open(os.path.join(DATA, "degeneracy_planar_summary.json"),
                          encoding="utf-8"))
    errs = []
    if set(written) != {(t, i) for t, i, _, _ in SPEC}:
        errs.append("item set mismatch")
    for t, i, _, verdict in SPEC:
        w = written.get((t, i))
        a = acc[(t, i)]
        if w is None:
            continue
        if w["nameHits"] != a["n"]:
            errs.append(f"{i}: hits {w['nameHits']} != {a['n']}")
        if w["verdict"] != verdict:
            errs.append(f"{i}: verdict {w['verdict']} != {verdict}")
        wm = {m["module"]: m["n"] for m in w["topModules"]}
        if wm != dict(a["mods"].most_common(5)):
            errs.append(f"{i}: module list mismatch")
        if verdict == "present" and a["n"] == 0:
            errs.append(f"{i}: present but 0 hits")
        if verdict == "absent" and i not in ("plane_drawing",) and a["n"] != 0:
            errs.append(f"{i}: absent but {a['n']} hits")
    # summary consistency
    for t in ("graph_degeneracy", "planar_graph"):
        items = [x for x in SPEC if x[0] == t]
        npres = sum(1 for x in items if x[3] == "present")
        miss = [x[1] for x in items if x[3] != "present"]
        if summ[t]["present"] != npres or summ[t]["missing"] != miss:
            errs.append(f"summary {t} mismatch")
    if summ["graph_degeneracy"]["gapKind"] != "assembly" or \
            summ["planar_graph"]["gapKind"] != "layer":
        errs.append("gapKind mismatch")

    for t in ("graph_degeneracy", "planar_graph"):
        print(t, summ[t])
    if errs:
        print("VERIFICATION FAILED")
        for e in errs[:30]:
            print("  FAIL:", e)
        sys.exit(1)
    print("hits, modules, verdict consistency, gap kinds, summary all match")
    print("VERIFICATION OK")


if __name__ == "__main__":
    main()
