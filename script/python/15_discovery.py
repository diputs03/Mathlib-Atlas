#!/usr/bin/env python3
"""15 - Discovery experiments over the Atlas corpus.

Consumes the joined per-declaration picture (13 features, 09 type skeletons,
14 graph stats) and the 09 reference edges to surface *candidate* mathematical
patterns. Everything here is a structural hypothesis for a human/AI to inspect,
not a claim:

  A. Repeated type signatures  -> candidate missing abstractions (the same
     typed construction, with the same typeclass constraints, independently
     repeated under many namespaces).
  B. Cross-area structural twins -> candidate analogies (same discrete type +
     proof shape and size regime, different mathematical area / conclusion).
  C. Generalization families    -> same namespace + conclusion + constraints
     with an arity ladder (specialization families to unify).
  D. Anomalies                   -> reduction-heavy rfl proofs, giant terms,
     theorem hubs, recursion-heavy proofs.
  E. Bridge declarations         -> a declaration whose dependencies and
     dependents collectively span many top-level areas (32-bit area masks).

Outputs (data/discovery_*.jsonl) + notes/15_discovery_report.md.
Pure Python, deterministic (all groups sorted).
"""

import json
import os
from collections import defaultdict

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
D = os.path.join(ROOT, "data")
NOTES = os.path.join(ROOT, "notes")

# thresholds (documented in the report)
MIN_CLUSTER_SIZE = 6        # A
MIN_CLUSTER_NS = 3          # A: distinct namespaces
MIN_TWIN_SIZE = 4           # B
MIN_TWIN_AREAS = 2          # B
MIN_FAMILY_SIZE = 4         # C
MIN_FAMILY_ARITY_SPREAD = 2 # C
BRIDGE_MIN_AREAS = 8        # E: out+in area reach
EXEMPLARS = 10


def load_jsonl(name):
    with open(os.path.join(D, name), "rb") as f:
        for line in f:
            yield json.loads(line)


def lb(x):
    """floor(log2) bucket (bit_length); 0 -> 0."""
    return x.bit_length() if x else 0


def constraint_tuple(skel):
    c = [(e["class"], e["count"]) for e in skel.get("constraints", [])]
    return tuple(sorted(c))


def jdump(o):
    return json.dumps(o, ensure_ascii=False, separators=(",", ":"))


def main():
    rec = {}
    print("loading 13 features ...", flush=True)
    for r in load_jsonl("atlas_features.jsonl"):
        rec[r["name"]] = {
            "name": r["name"], "kind": r["kind"], "module": r["module"],
            "area": r["area"] if "area" in r else None,
            "namespace": r["namespace"], "conclusionHead": r["conclusionHead"],
            "nPi": r["nPi"], "nDefault": r["nDefault"], "nImplicit": r["nImplicit"],
            "nStrictImplicit": r["nStrictImplicit"], "nInstImplicit": r["nInstImplicit"],
            "typeNodes": r["typeNodes"], "typeDepth": r["typeDepth"],
            "typeDistinct": r["typeDistinct"], "hasValue": r["hasValue"],
            "valueNodes": r["valueNodes"], "valueDepth": r["valueDepth"],
            "valueDistinct": r["valueDistinct"], "valueApps": r["valueApps"],
            "recRefs": r["recRefs"], "caseRefs": r["caseRefs"],
            "valueIsRfl": r["valueIsRfl"], "constraints": (),
            "isGenerated": r["isGenerated"], "isInstance": r["isInstance"],
            "isClass": r["isClass"], "valueTruncated": r["valueTruncated"],
            "typeTruncated": r["typeTruncated"],
        }
    # area is in 14 node stats; features carry module -> derive
    for v in rec.values():
        p = v["module"].split(".")
        v["area"] = p[1] if len(p) >= 2 else "(root)"

    print("loading 09 skeletons (constraints) ...", flush=True)
    for r in load_jsonl("atlas_type_skeletons.jsonl"):
        x = rec.get(r["name"])
        if x is not None:
            x["constraints"] = constraint_tuple(r)

    print("loading 14 node stats (degrees) ...", flush=True)
    for r in load_jsonl("atlas_node_graph_stats.jsonl"):
        x = rec.get(r["name"])
        if x is not None:
            x["inRefs"] = r["inRefs"]; x["inNeighbors"] = r["inNeighbors"]
            x["outRefs"] = r["outRefs"]; x["outNeighbors"] = r["outNeighbors"]
    nodes = list(rec.values())
    N = len(nodes)
    # Human-authored subset: the raw signature space is dominated by
    # elaborator-generated decls (_simp_N, ._proof_N, .match_N, Lean.Macro /
    # ParserDescr, macroRules auxiliaries) flagged by 13's isGenerated. The
    # mathematical-construction experiments (A/B/C) cluster the human subset;
    # bridge (E) and anomaly (D) analyses keep all declarations.
    human = [x for x in nodes if not x["isGenerated"]]
    n_generated = N - len(human)
    print(f"  joined {N} nodes ({n_generated} generated excluded from A/B/C)",
          flush=True)

    # ---------- A. repeated type signatures (missing abstractions) ----------
    print("experiment A: repeated type signatures ...", flush=True)
    groupsA = defaultdict(list)
    for x in human:
        sig = (x["kind"], x["nPi"], x["nDefault"], x["nImplicit"],
               x["nStrictImplicit"], x["nInstImplicit"], x["constraints"],
               x["conclusionHead"])
        groupsA[sig].append(x)
    clustersA = []
    for sig, members in groupsA.items():
        nss = {m["namespace"] for m in members}
        areas = {m["area"] for m in members}
        if len(members) >= MIN_CLUSTER_SIZE and len(nss) >= MIN_CLUSTER_NS:
            clustersA.append((members, nss, areas, sig))
    # constraint-bearing, non-generic-conclusion clusters first: those are the
    # strongest "same abstraction repeated" signals; Eq/Iff/None tail is generic.
    def a_key(c):
        sig = c[3]
        specific = (0 if sig[6] else 1, 0 if sig[7] not in ("Eq", "Iff", None) else 1)
        return (specific, -len(c[1]), -len(c[2]), -len(c[0]))
    clustersA.sort(key=a_key)
    with open(os.path.join(D, "discovery_type_clusters.jsonl"), "w",
              encoding="utf-8", newline="\n") as f:
        for members, nss, areas, sig in clustersA:
            ms = sorted(members, key=lambda m: (m["module"], m["name"]))
            f.write(jdump({
                "kind": sig[0], "nPi": sig[1], "nDefault": sig[2],
                "nImplicit": sig[3], "nStrictImplicit": sig[4],
                "nInstImplicit": sig[5],
                "constraints": [{"class": c, "count": k} for c, k in sig[6]],
                "conclusionHead": sig[7],
                "size": len(ms), "namespaceSpread": len(nss), "areaSpread": len(areas),
                "namespaces": sorted(nss)[:EXEMPLARS], "areas": sorted(areas),
                "exemplars": [{"name": m["name"], "module": m["module"],
                               "area": m["area"]} for m in ms[:EXEMPLARS]],
            }) + "\n")

    # ---------- B. cross-area structural twins (analogies) ----------
    print("experiment B: cross-area structural twins ...", flush=True)
    groupsB = defaultdict(list)
    for x in human:
        sig = (x["kind"], x["nPi"], x["nInstImplicit"], x["nImplicit"],
               x["constraints"], lb(x["typeNodes"]), lb(x["typeDepth"]),
               lb(x["typeDistinct"]), x["hasValue"], lb(x["valueNodes"]),
               lb(x["valueDepth"]), x["valueIsRfl"], x["recRefs"] > 0,
               x["caseRefs"] > 0, lb(x["valueApps"]))
        groupsB[sig].append(x)
    twinsB = []
    for sig, members in groupsB.items():
        areas = {m["area"] for m in members}
        nss = {m["namespace"] for m in members}
        if len(members) >= MIN_TWIN_SIZE and len(areas) >= MIN_TWIN_AREAS \
           and len(nss) >= MIN_TWIN_AREAS:
            twinsB.append((members, areas, nss, sig))
    twinsB.sort(key=lambda c: (0 if c[3][4] else 1, -len(c[1]), -len(c[0])))
    with open(os.path.join(D, "discovery_cross_area_twins.jsonl"), "w",
              encoding="utf-8", newline="\n") as f:
        for members, areas, nss, sig in twinsB:
            # up to two exemplars per area, deterministic
            by_area = defaultdict(list)
            for m in sorted(members, key=lambda m: m["name"]):
                if len(by_area[m["area"]]) < 2:
                    by_area[m["area"]].append(m)
            ex = [m for a in sorted(by_area) for m in by_area[a]][:EXEMPLARS]
            f.write(jdump({
                "kind": sig[0], "nPi": sig[1], "nInstImplicit": sig[2],
                "constraints": [{"class": c, "count": k} for c, k in sig[4]],
                "typeNodesBucket": sig[5], "valueNodesBucket": sig[9],
                "valueIsRfl": sig[11], "usesRecursor": sig[12],
                "usesCasesOn": sig[13],
                "size": len(members), "areaSpread": len(areas),
                "namespaceSpread": len(nss), "areas": sorted(areas),
                "exemplars": [{"name": m["name"], "area": m["area"],
                               "module": m["module"],
                               "conclusionHead": m["conclusionHead"]} for m in ex],
            }) + "\n")

    # ---------- C. generalization families ----------
    print("experiment C: generalization families ...", flush=True)
    groupsC = defaultdict(list)
    for x in human:
        if x["kind"] != "theorem":
            continue
        key = (x["namespace"], x["conclusionHead"], x["constraints"])
        groupsC[key].append(x)
    families = []
    for key, members in groupsC.items():
        arities = {m["nPi"] for m in members}
        if len(members) >= MIN_FAMILY_SIZE and len(arities) >= MIN_FAMILY_ARITY_SPREAD:
            families.append((key, members, arities))
    families.sort(key=lambda c: -len(c[1]))
    with open(os.path.join(D, "discovery_generalization_families.jsonl"), "w",
              encoding="utf-8", newline="\n") as f:
        for (ns, concl, cons), members, arities in families:
            ms = sorted(members, key=lambda m: (m["nPi"], m["name"]))
            f.write(jdump({
                "namespace": ns, "conclusionHead": concl,
                "constraints": [{"class": c, "count": k} for c, k in cons],
                "size": len(ms), "aritySpread": len(arities),
                "arities": sorted(arities),
                "members": [{"name": m["name"], "nPi": m["nPi"],
                             "module": m["module"]} for m in ms[:EXEMPLARS]],
            }) + "\n")

    # ---------- E. bridge declarations (area masks via edge stream) ----------
    print("experiment E: streaming edges for area masks ...", flush=True)
    name_idx = {x["name"]: i for i, x in enumerate(nodes)}
    area_bit = {a: 1 << i for i, a in enumerate(sorted({x["area"] for x in nodes}))}
    bit_area = {v: k for k, v in area_bit.items()}
    node_area_bit = [area_bit[x["area"]] for x in nodes]
    out_mask = [0] * N
    in_mask = [0] * N
    for r in load_jsonl("atlas_relations.jsonl"):
        s = name_idx.get(r["source"])
        t = name_idx.get(r["target"])
        if s is not None and t is not None:
            out_mask[s] |= node_area_bit[t]
            in_mask[t] |= node_area_bit[s]

    def popcount(v):
        return v.bit_count()

    bridges = []
    for i, x in enumerate(nodes):
        reach = popcount(out_mask[i]) + popcount(in_mask[i])
        if reach >= BRIDGE_MIN_AREAS:
            bridges.append((i, reach))
    bridges.sort(key=lambda b: -b[1])
    with open(os.path.join(D, "discovery_bridge_declarations.jsonl"), "w",
              encoding="utf-8", newline="\n") as f:
        for i, reach in bridges:
            x = nodes[i]
            om, im = out_mask[i], in_mask[i]
            f.write(jdump({
                "name": x["name"], "kind": x["kind"], "module": x["module"],
                "area": x["area"], "areaReach": reach,
                "isInstance": x["isInstance"], "isClass": x["isClass"],
                "outAreas": sorted(bit_area[b] for b in (1 << k for k in range(32)) if om & b),
                "inAreas": sorted(bit_area[b] for b in (1 << k for k in range(32)) if im & b),
                "outAreaCount": popcount(om), "inAreaCount": popcount(im),
                "outNeighbors": x.get("outNeighbors", 0),
                "inNeighbors": x.get("inNeighbors", 0),
            }) + "\n")

    # ---------- D. anomalies ----------
    print("experiment D: anomalies ...", flush=True)
    anomalies = {"reduction_heavy_rfl": [], "giant_term": [],
                 "theorem_hub": [], "recursion_heavy": []}
    for x in nodes:
        # giant/reduction-heavy = value walk hit the 50,000-node cap (13 flag)
        if x["valueIsRfl"] and x["valueTruncated"]:
            anomalies["reduction_heavy_rfl"].append(x)
        if not x["valueIsRfl"] and x["valueTruncated"]:
            anomalies["giant_term"].append(x)
        if x["recRefs"] + x["caseRefs"] >= 200:
            anomalies["recursion_heavy"].append(x)
    anomalies["reduction_heavy_rfl"].sort(key=lambda x: -x["valueNodes"])
    anomalies["giant_term"].sort(key=lambda x: -x["valueNodes"])
    anomalies["recursion_heavy"].sort(key=lambda x: -(x["recRefs"] + x["caseRefs"]))
    thm = [x for x in human if x["kind"] == "theorem"]
    thm.sort(key=lambda x: -x.get("inNeighbors", 0))
    anomalies["theorem_hub"] = thm[:200]
    with open(os.path.join(D, "discovery_anomalies.jsonl"), "w",
              encoding="utf-8", newline="\n") as f:
        for cat, lst in anomalies.items():
            for x in lst[:200]:
                f.write(jdump({
                    "category": cat, "name": x["name"], "kind": x["kind"],
                    "module": x["module"], "area": x["area"],
                    "valueNodes": x["valueNodes"], "valueIsRfl": x["valueIsRfl"],
                    "recRefs": x["recRefs"], "caseRefs": x["caseRefs"],
                    "outNeighbors": x.get("outNeighbors", 0),
                    "inNeighbors": x.get("inNeighbors", 0),
                }) + "\n")

    # ---------- report ----------
    print("writing report ...", flush=True)
    L = []
    w = L.append
    w("# 15 - Discovery experiments report\n")
    w(f"Joined node set: {N} Mathlib declarations (13 features + 09 skeletons + 14 stats).")
    w(f"{n_generated} elaborator-generated declarations (13 isGenerated: _simp_N, ._proof_N, "
      f".match_N, Lean.Macro/ParserDescr, macroRules auxiliaries) are excluded from the "
      f"mathematical-construction experiments A/B/C, leaving {len(human)} human-authored; "
      f"they are retained for bridge (E) and anomaly (D) analyses.")
    w("All results are *candidate structural hypotheses*, ranked deterministically.\n")
    w("## A. Repeated type signatures (candidate missing abstractions)")
    w("Signature = kind, exact binder counts, multiset of typeclass constraints, "
      "conclusion head. Clusters (size>="
      f"{MIN_CLUSTER_SIZE}, >={MIN_CLUSTER_NS} namespaces): **{len(clustersA)}**. "
      "Ranked with constraint-bearing / non-Eq-Iff clusters first.\n")
    w("Top 15 (most semantically specific first):")
    w("| size | ns | areas | kind | nPi | constraints | conclusion |")
    w("|---|---|---|---|---|---|---|")
    for members, nss, areas, sig in clustersA[:15]:
        cons = ", ".join(f"{c}×{k}" for c, k in sig[6]) or "—"
        w(f"| {len(members)} | {len(nss)} | {len(areas)} | {sig[0]} | {sig[1]} | "
          f"{cons} | {sig[7]} |")
    w("")
    w("## B. Cross-area structural twins (candidate analogies)")
    w("Signature abstracts names and conclusion head, keeps arity/constraints and "
      "log-binned type/value size and proof style; human-authored members must span "
      f"multiple areas and namespaces: **{len(twinsB)} twin groups**, constraint-bearing "
      "ranked first.\n")
    w("Top 15 by area spread (with one exemplar per area):")
    for members, areas, nss, sig in twinsB[:15]:
        ex = sorted({(m["area"], m["conclusionHead"], m["name"]) for m in members})
        w(f"- **{len(members)} members across {len(areas)} areas** "
          f"({sig[0]}, nPi={sig[1]}, constraints="
          f"{[c for c,k in sig[4]] or '—'}, rfl={sig[11]}): "
          + "; ".join(f"{a}:{h}({nm})" for a, h, nm in sorted(ex)[:6]))
    w("")
    w("## C. Generalization families")
    w(f"Same namespace + conclusion head + constraints with an arity ladder "
      f"(spread>={MIN_FAMILY_ARITY_SPREAD}): **{len(families)} families**.\nTop 15:")
    w("| namespace | conclusion | size | arities |")
    w("|---|---|---|---|")
    for (ns, concl, cons), members, arities in families[:15]:
        w(f"| {ns} | {concl} | {len(members)} | {sorted(arities)} |")
    w("")
    w(f"## E. Bridge declarations (area reach >={BRIDGE_MIN_AREAS}): {len(bridges)}\nTop 20:")
    w("| reach (out+in) | out areas | in areas | name | area |")
    w("|---|---|---|---|---|")
    for i, reach in bridges[:20]:
        x = nodes[i]
        w(f"| {reach} | {popcount(out_mask[i])} | {popcount(in_mask[i])} | "
          f"{x['name']} | {x['area']} |")
    w("")
    w("## D. Anomaly counts")
    w("reduction_heavy_rfl / giant_term = value walk hit the 50,000-node cap (13 "
      "valueTruncated), split by whether the proof closes by rfl; recursion_heavy = "
      "recRefs+caseRefs>=200; theorem_hub = top human theorems by distinct dependents.")
    for cat, lst in anomalies.items():
        w(f"- {cat}: {len(lst)}" + (" (capped at 200 in file)" if len(lst) > 200 else ""))
    w("\nTop reduction-heavy rfl proofs:")
    for x in anomalies["reduction_heavy_rfl"][:10]:
        w(f"  - valueNodes={x['valueNodes']} {x['name']} [{x['module']}]")
    w("\nTop theorem hubs (theorems most used by distinct others):")
    for x in anomalies["theorem_hub"][:10]:
        w(f"  - inNeighbors={x['inNeighbors']} {x['name']} [{x['module']}]")
    w("")
    with open(os.path.join(NOTES, "15_discovery_report.md"), "w",
              encoding="utf-8", newline="\n") as f:
        f.write("\n".join(L) + "\n")

    print("A clusters:", len(clustersA))
    print("B twin groups:", len(twinsB))
    print("C families:", len(families))
    print("E bridges:", len(bridges))
    print("D anomalies:", {k: len(v) for k, v in anomalies.items()})


if __name__ == "__main__":
    main()
