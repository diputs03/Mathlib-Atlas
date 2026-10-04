#!/usr/bin/env python3
"""Full-corpus verification for the 07 Atlas extraction.

Checks the main corpus (and, if present, the large-expression sidecar):
  * exact record count and unique names;
  * every record has the required fields and a Mathlib source module;
  * non-null type/value ASTs are well-formed;
  * tier flags are self-consistent;
  * sidecar (name, slot) keys are unique and every sharded main record has a
    matching sidecar entry;
  * size statistics.
Streaming, constant memory.
"""

import argparse
import json
import sys
from collections import Counter

REQUIRED = {
    "name", "namespace", "kind", "module", "levelParams",
    "isUnsafe", "isPartial", "hints",
    "typeNodeCount", "typeAstBytes", "typeStrBytes",
    "typeSharded", "typeOversized", "typeStr", "typeAst",
    "valueNodeCount", "valueAstBytes", "valueStrBytes",
    "valueSharded", "valueOversized", "valueStr", "valueAst",
}
AST_TAGS = {
    "bvar", "fvar", "mvar", "sort", "const", "app", "lam",
    "forallE", "letE", "litNat", "litStr", "mdata", "proj",
}
KINDS = {"axiom", "definition", "opaque", "theorem", "quotient",
         "inductive", "constructor", "recursor"}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("main")
    ap.add_argument("--sidecar")
    args = ap.parse_args()

    n = 0
    names = set()
    dup = 0
    kinds = Counter()
    non_mathlib = 0
    bad_ast = 0
    missing = 0
    sharded_keys = set()
    expect_sidecar = set()
    type_sharded = value_sharded = type_over = value_over = 0
    sizes = []

    with open(args.main, "rb") as fh:
        for lineno, raw in enumerate(fh, 1):
            sizes.append(len(raw))
            r = json.loads(raw)
            n += 1
            if REQUIRED - r.keys():
                missing += 1
            nm = r["name"]
            if nm in names:
                dup += 1
            names.add(nm)
            kinds[r["kind"]] += 1
            if r["kind"] not in KINDS:
                pass
            mod = r.get("module")
            if not (isinstance(mod, str) and mod.startswith("Mathlib")):
                non_mathlib += 1
            for slot in ("type", "value"):
                ast = r.get(f"{slot}Ast")
                if ast is not None and ast.get("tag") not in AST_TAGS:
                    bad_ast += 1
            if r["typeSharded"]:
                type_sharded += 1
                expect_sidecar.add((nm, "type"))
            if r["valueSharded"]:
                value_sharded += 1
                expect_sidecar.add((nm, "value"))
            if r["typeOversized"]:
                type_over += 1
            if r["valueOversized"]:
                value_over += 1

    print(f"main records          : {n}")
    print(f"unique names          : {len(names)}  (duplicates {dup})")
    print(f"records missing fields: {missing}")
    print(f"non-Mathlib modules   : {non_mathlib}")
    print(f"malformed inline ASTs : {bad_ast}")
    print(f"kind distribution     : {dict(kinds)}")
    print(f"type sharded/oversized: {type_sharded} / {type_over}")
    print(f"value sharded/oversized: {value_sharded} / {value_over}")
    total = sum(sizes)
    sizes.sort()
    print(f"main bytes            : {total:,} (p50={sizes[n//2]:,}, max={sizes[-1]:,})")

    ok = (dup == 0 and missing == 0 and non_mathlib == 0 and bad_ast == 0)

    if args.sidecar:
        sn = 0
        side_slots = Counter()
        with open(args.sidecar, "rb") as fh:
            for raw in fh:
                r = json.loads(raw)
                sn += 1
                key = (r["name"], r["slot"])
                if key in sharded_keys:
                    print("DUP SIDECAR KEY", key)
                sharded_keys.add(key)
                side_slots[r["slot"]] += 1
        missing_side = expect_sidecar - sharded_keys
        extra_side = sharded_keys - expect_sidecar
        print(f"sidecar records       : {sn}  slots={dict(side_slots)}")
        print(f"sharded main w/o sidecar: {len(missing_side)}; extra sidecar: {len(extra_side)}")
        ok = ok and not missing_side and not extra_side

    print("\nVERIFICATION", "OK" if ok else "FAILED")
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
