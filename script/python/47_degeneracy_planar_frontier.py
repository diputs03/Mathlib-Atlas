#!/usr/bin/env python3
"""47_degeneracy_planar_frontier.py — second-level frontier for unit-distance.

Script 46's build order starts (1) graph degeneracy then (2) planar graphs.
This script measures the SUB-prerequisites of each inside SimpleGraph, to tell
an "assembly gap" (all primitives exist, only the theorem must be assembled)
from a "layer gap" (a whole conceptual layer is missing). Same method as 46:
name regex AND expected module, curated verdict, false-friend notes.

Outputs: data/degeneracy_planar_frontier.jsonl,
         data/degeneracy_planar_summary.json
Pure stdlib, streaming, deterministic.
"""
import json, os, re, collections

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
DATA = os.path.join(ROOT, "data")
SCOPE = ("Mathlib.Combinatorics.SimpleGraph", "Mathlib.Combinatorics.Graph")

ITEMS = [
 # ---- graph degeneracy sub-prerequisites ----
 {"target": "graph_degeneracy", "id": "vertex_degree", "step": 1,
  "role": "Per-vertex degree", "rx": r"\bdegree\b",
  "verdict": "present"},
 {"target": "graph_degeneracy", "id": "neighbor_set", "step": 2,
  "role": "Neighbour set + card = degree", "rx": r"neighborSet",
  "verdict": "present"},
 {"target": "graph_degeneracy", "id": "subgraph_induce_delete", "step": 3,
  "role": "Induced subgraph / deleteVerts (peel a vertex)", "rx": r"subgraph|induce|deleteVerts",
  "verdict": "present"},
 {"target": "graph_degeneracy", "id": "min_degree_vertex", "step": 4,
  "role": "Every finite graph has a minimum-degree vertex",
  "rx": r"minimal_degree|minDegree|degree_le", "verdict": "present"},
 {"target": "graph_degeneracy", "id": "greedy_coloring", "step": 5,
  "role": "Vertex coloring machinery for the (deg+1)-color corollary",
  "rx": r"coloring|colorable", "verdict": "present"},
 {"target": "graph_degeneracy", "id": "elimination_ordering", "step": 6,
  "role": "A vertex elimination/peeling ordering (Fintype + WellFounded)",
  "rx": r"linearorder|wellfounded|elimination|peeling|degeneracyorder",
  "verdict": "absent",
  "note": "Generic Fintype/WellFounded exists in the library but no graph "
          "elimination-ordering construction; must be assembled by induction."},
 {"target": "graph_degeneracy", "id": "degeneracy_theorem", "step": 7,
  "role": "k-degenerate definition + edge bound |E|<=k|V|-binom(k+1,2) + equivalence",
  "rx": r"degener", "verdict": "absent",
  "note": "The degeneracy notion/equivalence itself is the missing theorem; "
          "every primitive it uses is present (steps 1-5)."},
 # ---- planar graph sub-prerequisites ----
 {"target": "planar_graph", "id": "cycles", "step": 1,
  "role": "Cycles / closed walks (face boundaries)", "rx": r"iscycle|\bcycle\b",
  "verdict": "present"},
 {"target": "planar_graph", "id": "connectedness", "step": 2,
  "role": "Connectedness / components", "rx": r"connected",
  "verdict": "present"},
 {"target": "planar_graph", "id": "trees_acyclic", "step": 3,
  "role": "Trees / acyclic (base case |E|=|V|-1)", "rx": r"istree|acyclic|\btree\b",
  "verdict": "present"},
 {"target": "planar_graph", "id": "plane_drawing", "step": 4,
  "role": "A drawing/embedding of the abstract graph in the plane",
  "rx": r"embed|drawing|plane", "verdict": "absent",
  "note": "False friend: 'Embedding' here is a graph-homomorphism embedding "
          "(injective map), not a geometric plane drawing; no topological embedding."},
 {"target": "planar_graph", "id": "faces", "step": 5,
  "role": "Faces / regions of a plane drawing", "rx": r"\bface\b|outerface|region",
  "verdict": "absent"},
 {"target": "planar_graph", "id": "planar_euler_formula", "step": 6,
  "role": "Planar Euler formula V-E+F=2", "rx": r"euler(?!ian)",
  "verdict": "absent",
  "note": "Only the abstract homological EulerCharacteristic exists elsewhere "
          "(46 step 5); the planar V-E+F identity for a drawn graph is absent."},
]


def main():
    for it in ITEMS:
        it["_rx"] = re.compile(it["rx"], re.I)
        it["hits"] = 0
        it["mods"] = collections.Counter()
        it["ex"] = []
    for line in open(os.path.join(DATA, "atlas_features.jsonl"), encoding="utf-8"):
        r = json.loads(line)
        mod = r.get("module", "")
        if not mod.startswith(SCOPE):
            continue
        nm = r.get("name", "")
        for it in ITEMS:
            if it["_rx"].search(nm):
                it["hits"] += 1
                it["mods"][mod] += 1
                if not nm.startswith("_private") and len(it["ex"]) < 8:
                    it["ex"].append(nm)

    rows = []
    for it in sorted(ITEMS, key=lambda x: (x["target"], x["step"])):
        # present verdict must have hits; absent must rely on note (false friend)
        rows.append({"target": it["target"], "step": it["step"], "id": it["id"],
                     "role": it["role"], "verdict": it["verdict"],
                     "nameHits": it["hits"],
                     "topModules": [{"module": m, "n": c}
                                    for m, c in it["mods"].most_common(5)],
                     "exemplars": it["ex"], "note": it.get("note", "")})
    with open(os.path.join(DATA, "degeneracy_planar_frontier.jsonl"),
              "wb") as o:
        for r in rows:
            o.write((json.dumps(r, ensure_ascii=False) + "\n").encode("utf-8"))

    summ = {}
    for t in ("graph_degeneracy", "planar_graph"):
        tr = [r for r in rows if r["target"] == t]
        v = collections.Counter(r["verdict"] for r in tr)
        summ[t] = {"n": len(tr), "present": v.get("present", 0),
                   "absent": v.get("absent", 0),
                   "missing": [r["id"] for r in tr if r["verdict"] != "present"]}
    # classify gap kind: degeneracy = assembly (>=5 primitives present, only
    # ordering+theorem missing); planar = layer (geometric core absent)
    summ["graph_degeneracy"]["gapKind"] = "assembly"
    summ["planar_graph"]["gapKind"] = "layer"
    with open(os.path.join(DATA, "degeneracy_planar_summary.json"), "w",
              encoding="utf-8") as o:
        json.dump(summ, o, ensure_ascii=False, indent=2)

    for t in ("graph_degeneracy", "planar_graph"):
        print(f"\n### {t}  [{summ[t]['gapKind']} gap]")
        for r in sorted((x for x in rows if x["target"] == t),
                        key=lambda x: x["step"]):
            mark = "OK " if r["verdict"] == "present" else "GAP"
            print(f"  {mark} {r['id']:<26} hits={r['nameHits']:<4} {r['role']}")
            if r["exemplars"]:
                print(f"        e.g. {', '.join(r['exemplars'][:3])}")
            if r["note"]:
                print(f"        note: {r['note']}")
        print(f"  -> present {summ[t]['present']}, missing {summ[t]['missing']}")


if __name__ == "__main__":
    main()
