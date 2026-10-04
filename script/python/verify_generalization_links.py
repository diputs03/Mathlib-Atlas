#!/usr/bin/env python3
"""verify_generalization_links.py — independent rebuild of script 36.

Re-derives generic/specialized classification, shape groups and the filtered
opportunity set from the raw corpus + skeletons using an independent walk, then
asserts:
  * summary counts reconcile (generic+specialized+skipped, group partition),
  * the written opportunities file is exactly the recomputed filtered set,
    in deterministic order, row by row (bijection),
  * every surviving opportunity satisfies the filter invariants.
"""
import json, os, sys

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
DATA = os.path.join(ROOT, "data")
LOGIC = {"eq", "iff", "exists", "le", "lt", "ge", "gt", "and", "or", "not",
         "true", "false", "heq", "mem", "subset", "ssubset", "ne", "nonempty",
         "dvd"}
GEN_TAILS = ("casesOn", "recOn", "brecOn", "inductionOn", "noConfusion",
             "noConfusionType", "rec", "mk")
MIN_SPEC, MIN_CARRIERS = 3, 2


def binds_sort(node):
    # independent formulation: iterate the pi spine, flag any Sort/Type binder
    while isinstance(node, dict):
        if "binderInfo" not in node:
            return False
        bt = node.get("binderType")
        if isinstance(bt, dict) and bt.get("tag") == "sort":
            return True
        node = node.get("body")
    return False


def main():
    classes = set()
    for line in open(os.path.join(DATA, "atlas_classes.jsonl"), encoding="utf-8"):
        classes.add(json.loads(line)["name"].split(".")[-1])

    skel = {}
    for line in open(os.path.join(DATA, "atlas_type_skeletons.jsonl"), encoding="utf-8"):
        s = json.loads(line)
        if s.get("kind") == "theorem":
            skel[s["name"]] = (s.get("conclusionHead"),
                               tuple(sorted(c["class"] for c in s.get("constraints", []))),
                               s.get("nDefault", 0))

    groups = {}
    n_gen = n_spec = n_skip = n_th = 0
    for line in open(os.path.join(DATA, "atlas_corpus.jsonl"), encoding="utf-8"):
        r = json.loads(line)
        if r.get("kind") != "theorem":
            continue
        if not r.get("module", "").startswith("Mathlib"):
            continue
        name = r["name"]
        if name.split(".")[-1] in GEN_TAILS or name.startswith("_"):
            continue
        sk = skel.get(name)
        ta = r.get("typeAst")
        if sk is None or not sk[0] or not isinstance(ta, dict):
            n_skip += 1
            continue
        n_th += 1
        head, ckey, ndef = sk
        key = (head, ckey, ndef)
        g = groups.setdefault(key, {"g": 0, "s": 0, "car": set(), "ex": []})
        if binds_sort(ta):
            g["g"] += 1
            n_gen += 1
        else:
            g["s"] += 1
            n_spec += 1
            ns = (r.get("namespace") or "").split(".")[0]
            g["car"].add(ns)  # artifacts kept here; filtered at the same stage as script
            if len(g["ex"]) < 12:
                g["ex"].append(name)

    rebuilt = []
    n_cov = n_puregen = n_speconly = raw = rej_class = rej_logic = 0
    for (head, ckey, ndef), g in groups.items():
        if g["g"] > 0:
            if g["s"] > 0:
                n_cov += 1
            else:
                n_puregen += 1
            continue
        n_speconly += 1
        raw_car = {c for c in g["car"] if c}
        if not (g["s"] >= MIN_SPEC and len(raw_car) >= MIN_CARRIERS):
            continue
        raw += 1
        tail = head.split(".")[-1]
        if tail in classes:
            rej_class += 1
            continue
        if tail.lower() in LOGIC or not ckey:
            rej_logic += 1
            continue
        car = {c for c in raw_car
               if c != "[anonymous]" and c != "definition" and not c.startswith("inst")}
        if len(car) < MIN_CARRIERS:
            rej_logic += 1
            continue
        rebuilt.append({"conclusionHead": head, "constraints": list(ckey),
                        "nDefault": ndef, "nSpecialized": g["s"],
                        "nCarriers": len(car), "carriers": sorted(car),
                        "examples": g["ex"]})
    rebuilt.sort(key=lambda o: (-o["nCarriers"], -o["nSpecialized"],
                                o["conclusionHead"]))

    # load written outputs
    written = [json.loads(l) for l in open(
        os.path.join(DATA, "generalization_opportunities.jsonl"), encoding="utf-8")]
    summary = json.load(open(os.path.join(DATA, "generalization_summary.json"),
                             encoding="utf-8"))

    errs = []
    # 1. summary reconciliation
    if summary["theoremsConsidered"] != n_th:
        errs.append(f"theorems {summary['theoremsConsidered']} != {n_th}")
    if summary["genericTheorems"] != n_gen:
        errs.append(f"generic {summary['genericTheorems']} != {n_gen}")
    if summary["specializedTheorems"] != n_spec:
        errs.append(f"specialized {summary['specializedTheorems']} != {n_spec}")
    if summary["skippedNoSkeleton"] != n_skip:
        errs.append(f"skipped {summary['skippedNoSkeleton']} != {n_skip}")
    if n_gen + n_spec != n_th:
        errs.append("generic+specialized != theorems")
    if summary["shapeGroups"] != len(groups):
        errs.append("shapeGroups mismatch")
    if summary["coveredGroupsGenericPlusSpec"] != n_cov:
        errs.append("covered mismatch")
    if summary["pureGenericGroups"] != n_puregen:
        errs.append("pureGeneric mismatch")
    if summary["specializedOnlyGroups"] != n_speconly:
        errs.append("specOnly mismatch")
    if n_cov + n_puregen + n_speconly != len(groups):
        errs.append("group partition does not sum")
    if summary["rawOpportunities"] != raw:
        errs.append("raw mismatch")
    if summary["rejectedClassPropHead"] != rej_class:
        errs.append("rejectClass mismatch")
    if summary["generalizationOpportunities"] != len(rebuilt):
        errs.append("opportunity count mismatch vs rebuilt")

    # 2. bijection with written file
    if len(written) != len(rebuilt):
        errs.append(f"written {len(written)} != rebuilt {len(rebuilt)}")
    for i, (w, b) in enumerate(zip(written, rebuilt)):
        for k in ("conclusionHead", "constraints", "nDefault", "nSpecialized",
                  "nCarriers", "carriers", "examples"):
            if w.get(k) != b.get(k):
                errs.append(f"row {i} key {k}: {w.get(k)!r} != {b.get(k)!r}")
        # written also carries areas; just require present
        if "areas" not in w:
            errs.append(f"row {i} missing areas")

    # 3. invariants on every survivor
    for w in written:
        if w["nSpecialized"] < MIN_SPEC:
            errs.append(f"{w['conclusionHead']} under min spec")
        if w["nCarriers"] < MIN_CARRIERS:
            errs.append(f"{w['conclusionHead']} under min carriers")
        if not w["constraints"]:
            errs.append(f"{w['conclusionHead']} empty constraints")
        if w["conclusionHead"].split(".")[-1].lower() in LOGIC:
            errs.append(f"{w['conclusionHead']} logical head leaked")
        if w["conclusionHead"].split(".")[-1] in classes:
            errs.append(f"{w['conclusionHead']} class head leaked")

    print(f"theorems {n_th} = generic {n_gen} + specialized {n_spec}; "
          f"skipped {n_skip}")
    print(f"groups {len(groups)} = covered {n_cov} + pureGeneric {n_puregen} "
          f"+ specOnly {n_speconly}")
    print(f"raw {raw} -> rejectClass {rej_class} rejectLogic/empty {rej_logic} "
          f"-> opportunities {len(rebuilt)}")
    if errs:
        print("VERIFICATION FAILED")
        for e in errs[:30]:
            print("  FAIL:", e)
        sys.exit(1)
    print(f"output file matches rebuilt set ({len(written)} rows, deterministic)")
    print("VERIFICATION OK")


if __name__ == "__main__":
    main()
