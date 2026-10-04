#!/usr/bin/env python3
"""Verification for script 13 (per-declaration structural features).

Internal consistency, row count vs the Mathlib corpus, optional cross-check of
the type-skeleton fields against script 09, and truncation counts vs 07/08/09.

Usage:
  verify_features.py atlas_features.jsonl \
      [--skeletons atlas_type_skeletons.jsonl]
"""

import argparse
import collections
import json
import sys

REQ = {"name", "kind", "module", "namespace", "nameDepth",
        "typeNodes", "typeDepth", "typeConsts", "typeDistinct",
        "nPi", "nDefault", "nImplicit", "nStrictImplicit", "nInstImplicit",
        "conclusionHead", "typeTruncated",
        "hasValue", "valueNodes", "valueDepth", "valueConsts", "valueDistinct",
        "valueLams", "valueForalls", "valueApps", "valueLets", "valueLits",
        "valueProjs", "recRefs", "caseRefs", "valueHead", "valueIsRfl",
        "valueTruncated", "isClass", "isInstance", "isInstName", "isGenerated"}
MATHLIB_DECLS = 574391
# truncation envelopes measured by 07/08/09 (type ~2535, value ~26907/26908)
TYPE_TRUNC_RANGE = (2000, 3000)
VALUE_TRUNC_RANGE = (25000, 28000)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("features")
    ap.add_argument("--skeletons")
    args = ap.parse_args()

    rows = []
    seen = set()
    dup = bad = 0
    bad_order = bad_value = bad_pi = bad_module = bad_rfl = 0
    kind = collections.Counter()
    trunc_t = trunc_v = 0
    n_value = n_rfl = n_class = n_inst = n_gen = 0
    for raw in open(args.features, "rb"):
        r = json.loads(raw)
        rows.append(r)
        if REQ - r.keys():
            bad += 1
        if r["name"] in seen:
            dup += 1
        seen.add(r["name"])
        kind[r["kind"]] += 1
        if not (r["typeNodes"] >= r["typeConsts"] >= r["typeDistinct"] >= 0):
            bad_order += 1
        if r["nPi"] != r["nDefault"] + r["nImplicit"] + \
                r["nStrictImplicit"] + r["nInstImplicit"]:
            bad_pi += 1
        if r["module"] is None or not r["module"].startswith("Mathlib"):
            bad_module += 1
        if r["typeTruncated"]:
            trunc_t += 1
        if r["hasValue"]:
            n_value += 1
            if not (r["valueNodes"] >= r["valueConsts"] >= r["valueDistinct"] >= 0):
                bad_order += 1
            if r["valueNodes"] < r["valueLams"] + r["valueApps"]:
                bad_value += 1
        else:
            if r["valueNodes"] or r["valueConsts"] or r["valueHead"] is not None \
               or r["valueIsRfl"]:
                bad_value += 1
        if r["valueTruncated"]:
            trunc_v += 1
        if r["valueIsRfl"]:
            n_rfl += 1
            if not r["hasValue"]:
                bad_rfl += 1
        if r["isClass"]:
            n_class += 1
        if r["isInstance"]:
            n_inst += 1
        if r["isGenerated"]:
            n_gen += 1

    n = len(rows)
    print(f"feature rows          : {n} (dup {dup}, bad {bad})")
    print(f"kinds                 : {dict(kind)}")
    print(f"bad ordering/value/pi/module/rfl: {bad_order}/{bad_value}/{bad_pi}/"
          f"{bad_module}/{bad_rfl}")
    print(f"hasValue {n_value}; rfl-closed {n_rfl}; isClass {n_class}; "
          f"isInstance {n_inst}; generated {n_gen}")
    print(f"truncated type {trunc_t}, value {trunc_v}")

    ok = (dup == 0 and bad == 0 and bad_order == 0 and bad_value == 0
          and bad_pi == 0 and bad_module == 0 and bad_rfl == 0
          and n == MATHLIB_DECLS
          and TYPE_TRUNC_RANGE[0] <= trunc_t <= TYPE_TRUNC_RANGE[1]
          and VALUE_TRUNC_RANGE[0] <= trunc_v <= VALUE_TRUNC_RANGE[1])
    if n != MATHLIB_DECLS:
        print(f"COUNT MISMATCH {n} != {MATHLIB_DECLS}")

    # distributions
    for fld in ["typeNodes", "valueNodes", "nPi", "typeDepth", "valueDepth"]:
        vals = sorted(r[fld] for r in rows)
        q = lambda p: vals[int(p * (len(vals) - 1))]
        print(f"{fld:10s} median={q(.5)} p90={q(.9)} p99={q(.99)} max={vals[-1]}")

    if args.skeletons:
        fmap = {r["name"]: r for r in rows}
        miss = mismatch = matched = 0
        for raw in open(args.skeletons, "rb"):
            s = json.loads(raw)
            r = fmap.get(s["name"])
            if r is None:
                miss += 1
                continue
            matched += 1
            for a, b in [("nPi", "nPi"), ("nDefault", "nDefault"),
                         ("nImplicit", "nImplicit"),
                         ("nStrictImplicit", "nStrictImplicit"),
                         ("nInstImplicit", "nInstImplicit")]:
                if r[a] != s[b]:
                    mismatch += 1
            if (r["conclusionHead"] or None) != (s["conclusionHead"] or None):
                mismatch += 1
            if r["typeTruncated"] != s["typeRolesTruncated"]:
                mismatch += 1
        print(f"\n09 skeleton join: matched {matched}, missing {miss}, mismatches {mismatch}")
        ok = ok and miss == 0 and mismatch == 0

    print("\nVERIFICATION", "OK" if ok else "FAILED")
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
