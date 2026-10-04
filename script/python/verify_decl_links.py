#!/usr/bin/env python3
"""Verification for script 12 (structural declaration links).

Checks schema, uniqueness, internal symmetry of the inductive-family links
(constructor <-> memberInductive, recursor <-> recursorOf, recursorRule targets
a known constructor), equation/alias label consistency, and (optionally) that
every class parent edge from script 10 appears here as a structExtends link.

Usage:
  verify_decl_links.py atlas_decl_links.jsonl [--classes atlas_classes.jsonl]
"""

import argparse
import collections
import json
import re
import sys

REQ = {"source", "target", "relation", "detail", "module", "mathlib"}
RELATIONS = {"constructor", "memberInductive", "recursor", "recursorOf",
             "recursorRule", "mutualInductive", "structExtends", "projection",
             "equationLemma", "unfoldLemma", "alias"}
EQ_RE = re.compile(r"^eq_\d+$")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("links")
    ap.add_argument("--classes")
    args = ap.parse_args()

    rows = []
    seen = set()
    dup = bad = bad_flag = 0
    rel = collections.Counter()
    by_rel = collections.defaultdict(list)
    for raw in open(args.links, "rb"):
        r = json.loads(raw)
        rows.append(r)
        if REQ - r.keys():
            bad += 1
        if r["relation"] not in RELATIONS:
            bad += 1
        key = (r["source"], r["target"], r["relation"])
        if key in seen:
            dup += 1
        seen.add(key)
        rel[r["relation"]] += 1
        by_rel[r["relation"]].append(r)
        flag = bool(r["module"]) and r["module"].startswith("Mathlib")
        if r["mathlib"] != flag:
            bad_flag += 1

    constructor = {(r["source"], r["target"]) for r in by_rel["constructor"]}
    member = {(r["source"], r["target"]) for r in by_rel["memberInductive"]}
    recursor = {(r["source"], r["target"]) for r in by_rel["recursor"]}
    recof = {(r["source"], r["target"]) for r in by_rel["recursorOf"]}
    ctor_of = {c: i for (c, i) in member}                 # ctor -> inductive
    inductive_rec = {i: r for (i, r) in recursor}        # inductive -> recursor

    # constructor <-> memberInductive symmetry
    member_missing = [(i, c) for (i, c) in constructor if (c, i) not in member]
    ctor_missing = [(c, i) for (c, i) in member if (i, c) not in constructor]

    # recursor <-> recursorOf symmetry
    recof_missing = [(i, r) for (i, r) in recursor if (r, i) not in recof]

    # recursorRule: target must be a real constructor. It belongs either to the
    # recursed type's own mutual block or to a nested inductive type that
    # occurs inside it (List/Array/Prod/... constructors); the latter are
    # legitimate and are counted separately as nested rules.
    recof_targets = collections.defaultdict(set)
    for (r, i) in recof:
        recof_targets[r].add(i)
    bad_rule = nested_rule = 0
    for r in by_rel["recursorRule"]:
        ind = ctor_of.get(r["target"])
        if ind is None:
            bad_rule += 1
        elif ind not in recof_targets.get(r["source"], set()):
            nested_rule += 1

    # equation / unfold label and suffix consistency (targets may be private)
    bad_eq = 0
    for r in by_rel["equationLemma"]:
        s = r["detail"] or ""
        if not EQ_RE.match(s) or not r["target"].endswith("." + s):
            bad_eq += 1
    for r in by_rel["unfoldLemma"]:
        if r["detail"] not in ("eq_def", "eq_unfold") or \
           not r["target"].endswith("." + r["detail"]):
            bad_eq += 1

    # alias never self; projection carries a field name
    bad_alias = sum(1 for r in by_rel["alias"] if r["source"] == r["target"])
    bad_proj = sum(1 for r in by_rel["projection"] if not r["detail"])
    bad_ext = sum(1 for r in by_rel["structExtends"]
                  if r["detail"] not in (None, "subobject"))

    print(f"total links           : {len(rows)} (dup {dup}, bad {bad}, bad-flag {bad_flag})")
    print("relation breakdown    :")
    for k in sorted(rel):
        print(f"  {k:16s} {rel[k]:,}")
    print(f"\nconstructor/member symmetry: missing member {len(member_missing)}, "
          f"missing constructor {len(ctor_missing)}")
    print(f"recursor/recursorOf symmetry missing: {len(recof_missing)}")
    print(f"bad recursorRule: {bad_rule} (nested-type rules: {nested_rule}); "
          f"bad eq/unfold: {bad_eq}; "
          f"bad alias: {bad_alias}; bad projection: {bad_proj}; bad extends: {bad_ext}")

    ok = (dup == 0 and bad == 0 and bad_flag == 0 and not member_missing
          and not ctor_missing and not recof_missing and bad_rule == 0
          and bad_eq == 0 and bad_alias == 0 and bad_proj == 0 and bad_ext == 0)

    if args.classes:
        extends = {(r["source"], r["target"]) for r in by_rel["structExtends"]}
        missing = 0
        n_parent = 0
        for raw in open(args.classes, "rb"):
            c = json.loads(raw)
            if c["isAlias"]:
                continue
            for p in c["parents"]:
                n_parent += 1
                if (c["name"], p["name"]) not in extends:
                    missing += 1
        print(f"\nclass parent edges from 10: {n_parent}; absent from structExtends: {missing}")
        ok = ok and missing == 0

    print("\nVERIFICATION", "OK" if ok else "FAILED")
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
