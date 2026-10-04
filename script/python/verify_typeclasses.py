#!/usr/bin/env python3
"""Verification for script 10 (typeclass / instance registries), alias-aware.

Classes file holds both canonical classes (isAlias=false) and abbrev aliases
(isAlias=true, aliasOf=canonical). Instances carry a canonical className and,
when the raw head was an alias, classAlias. Optionally cross-check 09 type
skeleton constraints (their raw heads may be aliases).

Usage:
  verify_typeclasses.py atlas_classes.jsonl atlas_instances.jsonl \
      [--skeletons atlas_type_skeletons.jsonl]
"""

import argparse
import collections
import json
import sys

CLASS_REQ = {"name", "module", "mathlib", "isAlias", "aliasOf",
             "hasStructure", "outParams", "fields", "parents", "nInstances"}
INST_REQ = {"name", "module", "mathlib", "className", "classAlias",
            "targetHead", "priority", "attrKind"}
ATTR_KINDS = {"global", "scoped", "local"}
# Built-in binder/type markers that can head an instImplicit constraint but are
# not classes (outParam α wraps an output-parameter type and is definitionally α).
NON_CLASS_MARKERS = {"outParam"}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("classes")
    ap.add_argument("instances")
    ap.add_argument("--skeletons")
    args = ap.parse_args()

    rows = [json.loads(l) for l in open(args.classes, "rb")]
    canonical = {}   # name -> row
    aliases = {}     # alias name -> canonical
    cbad = cdup = 0
    names = set()
    n_with_parents = parent_edges = 0
    non_class_parents = []
    for r in rows:
        if CLASS_REQ - r.keys():
            cbad += 1
        if r["name"] in names:
            cdup += 1
        names.add(r["name"])
        if r["isAlias"]:
            aliases[r["name"]] = r["aliasOf"]
        else:
            canonical[r["name"]] = r
    for r in rows:
        for p in r["parents"]:
            parent_edges += 1
            if p["name"] not in names:
                non_class_parents.append((r["name"], p["name"]))
            if r["parents"]:
                pass
        if r["parents"]:
            n_with_parents += 1
    bad_alias_target = [a for a, t in aliases.items() if t not in canonical]
    sum_canonical_ninst = sum(r["nInstances"] for r in canonical.values())
    sum_alias_ninst = sum(r["nInstances"] for r in rows if r["isAlias"])
    mathlib_classes = sum(1 for r in rows if r["mathlib"])

    print(f"class rows            : {len(rows)} = {len(canonical)} canonical + "
          f"{len(aliases)} aliases (Mathlib {mathlib_classes})")
    print(f"class duplicates/bad  : {cdup}/{cbad}; bad alias targets: "
          f"{len(bad_alias_target)}")
    print(f"classes with parents  : {n_with_parents} ({parent_edges} parent edges; "
          f"{len(non_class_parents)} to non-class structures)")
    for x in non_class_parents[:10]:
        print("    non-class parent:", x)
    print(f"sum canonical nInstances: {sum_canonical_ninst:,}; "
          f"sum alias nInstances: {sum_alias_ninst:,}")

    inst_n = mathlib_inst = no_class = via_alias = 0
    idup = ibad = 0
    unknown_class = bad_alias = 0
    attr = collections.Counter()
    seen = set()
    with open(args.instances, "rb") as fh:
        for raw in fh:
            r = json.loads(raw)
            inst_n += 1
            if INST_REQ - r.keys():
                ibad += 1
            if r["name"] in seen:
                idup += 1
            seen.add(r["name"])
            if r["mathlib"]:
                mathlib_inst += 1
            attr[r["attrKind"]] += 1
            if r["attrKind"] not in ATTR_KINDS:
                ibad += 1
            cn = r["className"]
            if cn is None:
                no_class += 1
            elif cn not in canonical:
                unknown_class += 1
            if r["classAlias"] is not None:
                via_alias += 1
                if r["classAlias"] not in aliases:
                    bad_alias += 1
    resolved = inst_n - no_class
    print(f"\ninstances             : {inst_n} (Mathlib {mathlib_inst})")
    print(f"instance duplicates/bad: {idup}/{ibad}")
    print(f"instances w/o class   : {no_class}; via alias: {via_alias}")
    print(f"className not canonical: {unknown_class}; bad classAlias: {bad_alias}")
    print(f"attrKind              : {dict(attr)}")

    ok = (cdup == 0 and cbad == 0 and idup == 0 and ibad == 0
          and unknown_class == 0 and bad_alias == 0 and not bad_alias_target
          and sum_canonical_ninst == resolved
          and sum_alias_ninst == via_alias)
    if sum_canonical_ninst != resolved:
        print(f"MISMATCH canonical nInstances {sum_canonical_ninst} vs resolved {resolved}")
    if sum_alias_ninst != via_alias:
        print(f"MISMATCH alias nInstances {sum_alias_ninst} vs viaAlias {via_alias}")

    if args.skeletons:
        constr_total = 0
        distinct = set()
        not_any = collections.Counter()
        markers = collections.Counter()
        with open(args.skeletons, "rb") as fh:
            for raw in fh:
                r = json.loads(raw)
                for c in r["constraints"]:
                    constr_total += 1
                    distinct.add(c["class"])
                    if c["class"] in NON_CLASS_MARKERS:
                        markers[c["class"]] += 1
                    elif c["class"] not in names:
                        not_any[c["class"]] += 1
        covered = len(distinct) - len(not_any) - len(markers)
        print(f"\n09 constraint slots   : {constr_total:,}")
        print(f"distinct constrained classes: {len(distinct)}; resolved in registry "
              f"{covered}; non-class markers {dict(markers)}; unresolved {len(not_any)}")
        print("top unresolved:", not_any.most_common(10))
        ok = ok and len(not_any) == 0

    print("\nVERIFICATION", "OK" if ok else "FAILED")
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
