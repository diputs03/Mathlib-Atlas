#!/usr/bin/env python3
"""Validate an Atlas JSONL corpus produced by 07_persistent_corpus.lean.

Usage:
    python script/python/validate_corpus.py data/atlas_corpus.jsonl [--head N]

Checks:
  * every line is a single, parseable JSON object;
  * the required field set is present on every record;
  * structural ASTs (`typeAst`, and `valueAst` when present) are well formed;
  * reports kind/module/value coverage and byte-size statistics.
"""

import argparse
import json
import statistics
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


def check_ast(node, path, errors):
    if not isinstance(node, dict):
        errors.append(f"{path}: AST node is not an object")
        return
    tag = node.get("tag")
    if tag not in AST_TAGS:
        errors.append(f"{path}: bad AST tag {tag!r}")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("path")
    ap.add_argument("--head", type=int, default=None,
                    help="only inspect the first N records")
    args = ap.parse_args()

    n = 0
    kinds = Counter()
    has_value = 0
    sharded = 0
    oversized = 0
    type_sharded = 0
    module_null = 0
    sizes = []
    errors = []

    with open(args.path, "r", encoding="utf-8") as fh:
        for lineno, line in enumerate(fh, 1):
            if args.head is not None and n >= args.head:
                break
            line = line.rstrip("\n")
            if not line:
                errors.append(f"line {lineno}: empty")
                continue
            sizes.append(len(line.encode("utf-8")))
            try:
                rec = json.loads(line)
            except json.JSONDecodeError as e:
                errors.append(f"line {lineno}: invalid JSON: {e}")
                continue
            n += 1

            missing = REQUIRED - rec.keys()
            if missing:
                errors.append(f"line {lineno} ({rec.get('name')}): missing {sorted(missing)}")

            kinds[rec.get("kind")] += 1
            if rec.get("valueAst") is not None:
                has_value += 1
            if rec.get("valueSharded") or rec.get("typeSharded"):
                sharded += 1
            if rec.get("valueOversized") or rec.get("typeOversized"):
                oversized += 1
            if rec.get("typeSharded"):
                type_sharded += 1
            if rec.get("module") is None:
                module_null += 1
            check_ast(rec.get("typeAst"), f"line {lineno} typeAst", errors) if rec.get("typeAst") is not None else None
            if rec.get("valueAst") is not None:
                check_ast(rec["valueAst"], f"line {lineno} valueAst", errors)

    print(f"records parsed : {n}")
    print(f"kinds          : {dict(kinds)}")
    print(f"with valueAst  : {has_value} ({has_value / n:.1%})" if n else "no records")
    print(f"decls sharded  : {sharded} (type-sharded {type_sharded})")
    print(f"decls oversized: {oversized}")
    print(f"module == null : {module_null}")
    if sizes:
        total = sum(sizes)
        print(f"total bytes    : {total:,}")
        print(f"min / median / max record bytes: "
              f"{min(sizes):,} / {int(statistics.median(sizes)):,} / {max(sizes):,}")
        print(f"mean record bytes: {total / len(sizes):,.0f}")

    if errors:
        print(f"\n{len(errors)} ERROR(S); first 20:", file=sys.stderr)
        for e in errors[:20]:
            print("  " + e, file=sys.stderr)
        sys.exit(1)
    print("\nvalidation OK")


if __name__ == "__main__":
    main()
