#!/usr/bin/env python3
"""verify_stdlib_semantic_analogies.py — deterministic checks for script 64.

Validates the three outputs of 64_stdlib_semantic_analogies.py (two-channel,
semantic-first scan):
  * stdlib_semantic_pairs.jsonl    (per-channel floors, cross-area/namespace,
                                    sorting, score identities, payload shape)
  * stdlib_semantic_clusters.jsonl (membership / area / namespace invariants)
  * stdlib_semantic_summary.json   (counts agree with line counts; positive
                                    control PointwiseLift family is found by
                                    the structural channel and co-clusters)

Exit code is 0 only when every check passes.
"""
import json, os, sys

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
DATA = os.path.join(ROOT, "data")
PAIRS = os.path.join(DATA, "stdlib_semantic_pairs.jsonl")
CLUST = os.path.join(DATA, "stdlib_semantic_clusters.jsonl")
SUM = os.path.join(DATA, "stdlib_semantic_summary.json")

EPS = 1e-3
SEMANTIC_CHANNELS = {"semantic"}
STRUCT_CHANNELS = {"structural", "structural-twin"}

failures = []


def check(cond, msg):
    if not cond:
        failures.append(msg)


def read_jsonl(path):
    rows = []
    with open(path, "rb") as f:
        for line in f:
            line = line.strip()
            if line:
                rows.append(json.loads(line))
    return rows


def main():
    for p in (PAIRS, CLUST, SUM):
        check(os.path.exists(p), f"missing output {os.path.basename(p)}")
    if failures:
        for m in failures:
            print("FAIL", m)
        return 1

    pairs = read_jsonl(PAIRS)
    clusters = read_jsonl(CLUST)
    with open(SUM, "rb") as f:
        summary = json.load(f)

    params = summary["params"]
    meaning_floor = params["meaningCosFloor"]
    sim_floor = params["simFloor"]
    min_shared = params["minSharedMeaning"]
    diffuse_at = params["diffuseThreshold"]
    struct_edge = params["structEdge"]
    struct_role = params["structRole"]
    mw, rw = params["meaningWeight"], params["roleWeight"]

    # ---- pairs -------------------------------------------------------------
    check(len(pairs) > 0, "no pairs emitted")
    check(len(pairs) <= 100_000, "pair file exceeds MAX_PAIR_LINES")
    seen = set()
    prev = None
    n_sem = n_struct = 0
    for p in pairs:
        a, b = p["a"], p["b"]
        ch = p["channel"]
        check(ch in SEMANTIC_CHANNELS | STRUCT_CHANNELS,
              f"unknown channel {ch} in {a['name']}")
        check(a["name"] != b["name"], f"self pair {a['name']}")
        check(a["area"] != b["area"],
              f"same-area pair {a['name']} ~ {b['name']} ({a['area']})")
        if params.get("namespaceGuard", True):
            check(a["namespace"] != b["namespace"],
                  f"same-namespace pair {a['name']} ~ {b['name']}")
        for cos in ("score", "semanticMix", "meaningCos", "roleCos",
                    "structCos"):
            check(-1e-6 <= p[cos] <= 1 + 1e-6,
                  f"{cos} out of range in {a['name']}")
        mix = mw * p["meaningCos"] + rw * p["roleCos"]
        check(abs(mix - p["semanticMix"]) < 2e-3,
              f"semanticMix != {mw}*m+{rw}*r for {a['name']}")
        if ch in SEMANTIC_CHANNELS:
            n_sem += 1
            check(len(p["sharedMeaning"]) >= min_shared,
                  f"semantic pair with <{min_shared} anchors: {a['name']}")
            check(p["meaningCos"] >= meaning_floor - 1e-9,
                  f"meaningCos below floor: {a['name']} ~ {b['name']}")
            check(p["semanticMix"] >= sim_floor - 1e-9,
                  f"semantic mix below floor: {a['name']} ~ {b['name']}")
            check(abs(p["score"] - p["semanticMix"]) < EPS,
                  f"semantic score != mix: {a['name']} ~ {b['name']}")
        else:
            n_struct += 1
            check(p["structCos"] >= struct_edge - 1e-9,
                  f"structural pair structCos below edge: {a['name']}")
            check(p["roleCos"] >= struct_role - 1e-9,
                  f"structural pair roleCos below edge: {a['name']}")
            ss = 0.5 * p["roleCos"] + 0.5 * p["structCos"]
            check(abs(p["score"] - ss) < EPS,
                  f"structural score != 0.5*r+0.5*s: {a['name']}")
            if ch == "structural-twin":
                check(p["additiveTwin"],
                      f"twin channel but additiveTwin false: {a['name']}")
        key = tuple(sorted((a["name"], b["name"])))
        check(key not in seen, f"duplicate pair {key}")
        seen.add(key)
        if prev is not None:
            check(p["score"] <= prev + 1e-12, "pairs not sorted by desc score")
        prev = p["score"]
        for side in (a, b):
            for field in ("name", "area", "module", "namespace", "kind",
                          "conclusionHead", "valueHead", "predRole",
                          "valueRole"):
                check(field in side, f"pair side missing field {field}")
    check(n_sem > 0, "no semantic-channel pairs emitted")
    check(n_struct > 0, "no structural-channel pairs emitted")

    # ---- clusters ----------------------------------------------------------
    for c in clusters:
        check(c["members"] >= params["clusterMinMembers"],
              "cluster below min members")
        check(c["nAreas"] >= 2, "cluster does not span 2 areas")
        check(c["nNamespaces"] >= 2, "cluster confined to one namespace")
        check(len(c["areas"]) == c["nAreas"], "cluster area list/count mismatch")
        reps = c["representatives"]
        check(1 <= len(reps) <= 40, "cluster representative count out of range")
        rep_names = [r["name"] for r in reps]
        check(len(set(rep_names)) == len(rep_names),
              "duplicate representatives in cluster")
        rep_areas = {r["area"] for r in reps}
        check(rep_areas.issubset(set(c["areas"])),
              "representative area outside declared cluster areas")
        check(c["diffuse"] == (c["members"] > diffuse_at),
              "diffuse flag inconsistent with member count")
        for w in c["signatureWords"]:
            check(isinstance(w, str) and len(w) >= 2,
                  "bad signature word in cluster")
        check(0 <= c["meanScore"] <= 1, "cluster meanScore out of range")
        for e in ("semanticEdges", "structuralEdges", "twinEdges"):
            check(c[e] >= 0, f"negative {e}")
        check(c["semanticEdges"] + c["structuralEdges"] + c["twinEdges"] > 0,
              "cluster with no edges")

    pri = [(c["diffuse"], -c["meanScore"]) for c in clusters]
    check(pri == sorted(pri), "clusters not in declared sort order")

    # ---- summary counts ----------------------------------------------------
    check(summary["eligibleCoreNodes"] > 100_000,
          "suspiciously few eligible core nodes (full run expected)")
    check(summary["emittedPairs"] == len(pairs),
          "summary.emittedPairs != pair line count")
    check(summary["clusters"] == len(clusters),
          "summary.clusters != cluster line count")
    check(summary["nondiffuseClusters"] ==
          sum(1 for c in clusters if not c["diffuse"]),
          "nondiffuse cluster count mismatch")
    sem = summary["semantic"]
    check(sem["twoPlusAnchors"] >= sem["kept"],
          "semantic funnel: kept > twoPlusAnchors")
    check(sem["visits"] >= sem["twoPlusAnchors"],
          "semantic funnel: visits < twoPlusAnchors")
    st = summary["structural"]
    check(st["pairTests"] >= st["kept"],
          "structural funnel: kept > pairTests")
    check(st["additiveTwins"] <= st["kept"],
          "structural funnel: twins > kept")
    check(summary["clusterEdges"] >= 0, "negative clusterEdges")

    # ---- positive control: PointwiseLift via structural channel -----------
    pc = summary["positiveControl"]
    has_set = any(n.startswith("Set.image2") for n in pc["nodes"])
    has_filter = any("Filter.map₂" in n for n in pc["nodes"])
    check(has_set, "positive control: Set.image2 not found in core corpus")
    check(has_filter, "positive control: Filter.map₂ not found in core corpus")
    cross = [q for q in pc["pairScores"]
             if {q["a"], q["b"]} == {"Set.image2", "Filter.map₂"}]
    check(len(cross) > 0,
          "positive control: definition pair Set.image2 ~ Filter.map₂ missing")
    # the PointwiseLift lemma family should also be recovered: count how many
    # cross lemma pairs co-cluster structurally
    family = [q for q in pc["pairScores"] if q["sameComponent"]]
    check(len(family) >= 5,
          f"positive control: only {len(family)} co-clustered PointwiseLift "
          "family pairs (expected the parallel lemma families to connect)")
    if cross:
        best = cross[0]
        print(f"positive control definitions Set.image2~Filter.map₂: "
              f"structScore={best['structScore']} "
              f"(structCos={best['structCos']}, roleCos={best['roleCos']}, "
              f"meaningCos={best['meaningCos']}, "
              f"sameComponent={best['sameComponent']})")
        check(best["structCos"] >= 0.80,
              "positive control: structCos unexpectedly low for PointwiseLift")
        check(best["sameComponent"],
              "positive control: Set.image2 and Filter.map₂ not co-clustered")
        print(f"positive control family: {len(family)} co-clustered cross pairs")

    print(f"pairs={len(pairs)} (semantic {n_sem}, structural {n_struct}) "
          f"clusters={len(clusters)} "
          f"nondiffuse={summary['nondiffuseClusters']} "
          f"eligibleNodes={summary['eligibleCoreNodes']:,}")
    if failures:
        for m in failures:
            print("FAIL", m)
        return 1
    print("ALL CHECKS PASSED")
    return 0


if __name__ == "__main__":
    sys.exit(main())
