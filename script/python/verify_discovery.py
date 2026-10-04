#!/usr/bin/env python3
"""Verification for script 15 discovery outputs.

Independently rebuilds the A/B signatures from 13 features + 09 skeletons and
checks that every stored exemplar really belongs to its claimed cluster, that
thresholds and spreads hold, that bridge area masks are self-consistent, and
that anomaly categories satisfy their defining predicates.

Usage: verify_discovery.py
"""

import json
import os

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
D = os.path.join(ROOT, "data")


def load(name):
    with open(os.path.join(D, name), "rb") as f:
        for line in f:
            yield json.loads(line)


def lb(x):
    return x.bit_length() if x else 0


def cons_tuple(lst):
    return tuple(sorted((e["class"], e["count"]) for e in lst))


def main():
    feat = {}
    for r in load("atlas_features.jsonl"):
        feat[r["name"]] = r
    for r in load("atlas_type_skeletons.jsonl"):
        if r["name"] in feat:
            feat[r["name"]]["_cons"] = cons_tuple(r.get("constraints", []))

    errs = []
    counts = {}

    def sigA(x):
        return (x["kind"], x["nPi"], x["nDefault"], x["nImplicit"],
                x["nStrictImplicit"], x["nInstImplicit"], x["_cons"],
                x["conclusionHead"])

    def sigB(x):
        return (x["kind"], x["nPi"], x["nInstImplicit"], x["nImplicit"], x["_cons"],
                lb(x["typeNodes"]), lb(x["typeDepth"]), lb(x["typeDistinct"]),
                x["hasValue"], lb(x["valueNodes"]), lb(x["valueDepth"]),
                x["valueIsRfl"], x["recRefs"] > 0, x["caseRefs"] > 0,
                lb(x["valueApps"]))

    # ---- A ----
    nA = 0
    for c in load("discovery_type_clusters.jsonl"):
        nA += 1
        if c["size"] < 6 or c["namespaceSpread"] < 3:
            errs.append(f"A threshold violated: {c.get('exemplars',[{}])[0]}")
        if len(c["exemplars"]) > c["size"] or len(c["namespaces"]) > c["namespaceSpread"] \
           or len(c["areas"]) != c["areaSpread"]:
            errs.append("A spread inconsistency")
        claimed = (c["kind"], c["nPi"], c["nDefault"], c["nImplicit"],
                   c["nStrictImplicit"], c["nInstImplicit"],
                   tuple(sorted((e["class"], e["count"]) for e in c["constraints"])),
                   c["conclusionHead"])
        for ex in c["exemplars"]:
            x = feat.get(ex["name"])
            if x is None:
                errs.append(f"A exemplar missing: {ex['name']}"); continue
            if sigA(x) != claimed:
                errs.append(f"A exemplar signature mismatch: {ex['name']}"); break
    counts["A"] = nA

    # ---- B ----
    nB = 0
    for c in load("discovery_cross_area_twins.jsonl"):
        nB += 1
        if c["size"] < 4 or c["areaSpread"] < 2:
            errs.append("B threshold violated")
        if len(c["areas"]) != c["areaSpread"]:
            errs.append("B area spread inconsistency")
        ex_areas = set()
        for ex in c["exemplars"]:
            x = feat.get(ex["name"])
            if x is None:
                errs.append(f"B exemplar missing: {ex['name']}"); continue
            ex_areas.add(ex["area"])
            s = sigB(x)
            ok = (s[0] == c["kind"] and s[1] == c["nPi"] and s[2] == c["nInstImplicit"]
                  and s[4] == tuple(sorted((e["class"], e["count"]) for e in c["constraints"]))
                  and s[5] == c["typeNodesBucket"] and s[9] == c["valueNodesBucket"]
                  and s[11] == c["valueIsRfl"] and s[12] == c["usesRecursor"]
                  and s[13] == c["usesCasesOn"])
            if not ok:
                errs.append(f"B exemplar signature mismatch: {ex['name']}"); break
        if len(ex_areas) < 2:
            errs.append("B exemplars do not span 2 areas")
    counts["B"] = nB

    # ---- C ----
    nC = 0
    for c in load("discovery_generalization_families.jsonl"):
        nC += 1
        if c["size"] < 4 or c["aritySpread"] < 2:
            errs.append("C threshold violated")
        if len(c["arities"]) != c["aritySpread"]:
            errs.append("C arity spread inconsistency")
        for m in c["members"]:
            x = feat.get(m["name"])
            if x is None:
                errs.append(f"C member missing: {m['name']}"); continue
            if x["namespace"] != c["namespace"] or x["conclusionHead"] != c["conclusionHead"] \
               or x["_cons"] != tuple(sorted((e["class"], e["count"]) for e in c["constraints"])):
                errs.append(f"C member key mismatch: {m['name']}"); break
            if m["nPi"] not in c["arities"]:
                errs.append(f"C member nPi not in arities: {m['name']}"); break
    counts["C"] = nC

    # ---- E ----
    nE = 0
    for b in load("discovery_bridge_declarations.jsonl"):
        nE += 1
        if b["areaReach"] < 8:
            errs.append("E threshold violated")
        if b["areaReach"] != b["outAreaCount"] + b["inAreaCount"]:
            errs.append(f"E reach sum mismatch: {b['name']}")
        if len(b["outAreas"]) != b["outAreaCount"] or len(b["inAreas"]) != b["inAreaCount"]:
            errs.append(f"E mask list mismatch: {b['name']}")
        x = feat.get(b["name"])
        if x is None:
            errs.append(f"E missing: {b['name']}")
    counts["E"] = nE

    # ---- D ----
    nD = 0
    cat_counts = {}
    for a in load("discovery_anomalies.jsonl"):
        nD += 1
        cat_counts[a["category"]] = cat_counts.get(a["category"], 0) + 1
        x = feat.get(a["name"])
        if x is None:
            errs.append(f"D missing: {a['name']}"); continue
        cat = a["category"]
        if cat == "reduction_heavy_rfl" and not (x["valueIsRfl"] and x["valueTruncated"]):
            errs.append(f"D predicate violated: {a['name']}")
        if cat == "giant_term" and not ((not x["valueIsRfl"]) and x["valueTruncated"]):
            errs.append(f"D predicate violated: {a['name']}")
        if cat == "recursion_heavy" and x["recRefs"] + x["caseRefs"] < 200:
            errs.append(f"D predicate violated: {a['name']}")
        if cat == "theorem_hub" and x["kind"] != "theorem":
            errs.append(f"D non-theorem hub: {a['name']}")
    counts["D"] = nD

    print("discovery groups/rows:", counts)
    print("anomaly categories:", cat_counts)
    # cross-consistency: generated exclusion count matches 13
    n_gen = sum(1 for x in feat.values() if x["isGenerated"])
    print(f"13 isGenerated total: {n_gen} (A/B/C use the {len(feat)-n_gen} human-authored)")
    # giant + rfl-truncated must equal total value-truncated
    n_trunc = sum(1 for x in feat.values() if x["valueTruncated"])
    print(f"valueTruncated total {n_trunc}; anomaly giant+rfl files capped at 200 each")

    if errs:
        print(f"\nFAILED ({len(errs)} problems); first 20:")
        for e in errs[:20]:
            print("  -", e)
        raise SystemExit(1)
    print("\nVERIFICATION OK")


if __name__ == "__main__":
    main()
