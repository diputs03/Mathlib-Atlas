#!/usr/bin/env python3
"""Verification for script 11 (namespace tree + namespace/module incidence).

Checks tree integrity, internal aggregation reconciliation, and the
namespace/module mismatch; cross-totals against the known Mathlib declaration
count (574391, same environment filter as 06/07).

Usage:
  verify_namespaces.py atlas_namespaces.jsonl atlas_namespace_modules.jsonl
"""

import argparse
import collections
import json
import sys

NS_REQ = {"name", "parent", "depth", "root", "nDecls", "nMathlib",
          "nModules", "kinds"}
PR_REQ = {"namespace", "module", "mathlib", "nDecls", "nMathlib", "kinds"}
MATHLIB_DECLS = 574391


def kinds_sum(k):
    return sum(k.values())


def lean_segments(nm):
    """Split a Lean dotted name, ignoring dots inside quoted «...» segments."""
    if nm == "":
        return []
    parts, cur, quoted = [], [], False
    for ch in nm:
        if ch == "«":
            quoted = True
        elif ch == "»":
            quoted = False
        if ch == "." and not quoted:
            parts.append("".join(cur)); cur = []
        else:
            cur.append(ch)
    parts.append("".join(cur))
    return parts


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("namespaces")
    ap.add_argument("pairs")
    args = ap.parse_args()

    nodes = [json.loads(l) for l in open(args.namespaces, "rb")]
    by_name = {}
    dup = bad = 0
    for n in nodes:
        if NS_REQ - n.keys():
            bad += 1
        if n["name"] in by_name:
            dup += 1
        by_name[n["name"]] = n

    # tree integrity
    no_root = "" not in by_name
    bad_parent = bad_depth = bad_root = bad_kindsum = bad_mathlib = 0
    total_decls = total_mathlib = 0
    for n in nodes:
        nm = n["name"]
        total_decls += n["nDecls"]
        total_mathlib += n["nMathlib"]
        if kinds_sum(n["kinds"]) != n["nDecls"]:
            bad_kindsum += 1
        if n["nMathlib"] > n["nDecls"]:
            bad_mathlib += 1
        expect_depth = 0 if nm == "" else len(lean_segments(nm))
        if n["depth"] != expect_depth:
            bad_depth += 1
        expect_root = "" if nm == "" else lean_segments(nm)[0]
        if n["root"] != expect_root:
            bad_root += 1
        if nm == "":
            if n["parent"] is not None:
                bad_parent += 1
        else:
            if n["parent"] not in by_name:
                bad_parent += 1
            elif by_name[n["parent"]]["depth"] != n["depth"] - 1:
                bad_parent += 1

    # pairs
    pair_decls = pair_mathlib = 0
    pdup = pbad = pbad_ns = pbad_flag = pbad_kindsum = 0
    seen = set()
    mod_ns = collections.defaultdict(set)
    ns_modcount = collections.Counter()
    for raw in open(args.pairs, "rb"):
        p = json.loads(raw)
        if PR_REQ - p.keys():
            pbad += 1
        key = (p["namespace"], p["module"])
        if key in seen:
            pdup += 1
        seen.add(key)
        if kinds_sum(p["kinds"]) != p["nDecls"]:
            pbad_kindsum += 1
        if p["nMathlib"] > p["nDecls"]:
            pbad += 1
        if p["namespace"] not in by_name:
            pbad_ns += 1
        flag = p["module"].startswith("Mathlib")
        if p["mathlib"] != flag:
            pbad_flag += 1
        pair_decls += p["nDecls"]
        pair_mathlib += p["nMathlib"]
        mod_ns[p["module"]].add(p["namespace"])
        ns_modcount[p["namespace"]] += 1

    # every constant with a module is counted in exactly one pair; constants
    # without a module (prelude/helper) appear only in the node totals.
    no_module = total_decls - pair_decls

    multi_mod_ns = [nm for nm, n in by_name.items() if n["nModules"] > 1]
    multi_ns_mod = [m for m, s in mod_ns.items() if len(s) > 1]

    print(f"namespace nodes       : {len(nodes)} (dup {dup}, bad {bad})")
    print(f"total decls (Σ nodes) : {total_decls:,}; Mathlib {total_mathlib:,}")
    print(f"tree: missing-root {no_root}, bad-parent {bad_parent}, "
          f"bad-depth {bad_depth}, bad-root {bad_root}")
    print(f"node kinds/mathlib bad: {bad_kindsum}/{bad_mathlib}")
    print(f"\nincidence pairs       : {len(seen)} (dup {pdup}, bad {pbad}, "
          f"unknown-ns {pbad_ns}, bad-flag {pbad_flag}, bad-kindsum {pbad_kindsum})")
    print(f"Σ pair decls          : {pair_decls:,}; Mathlib {pair_mathlib:,}; "
          f"decls w/o module {no_module:,}")
    print(f"\nnamespaces spanning >1 module : {len(multi_mod_ns)}")
    print(f"modules hosting >1 namespace  : {len(multi_ns_mod)} of {len(mod_ns)}")
    top_ns = sorted(by_name.values(), key=lambda x: -x["nDecls"])[:12]
    print("top namespaces by nDecls:")
    for n in top_ns:
        print(f"  {n['nDecls']:7d}  {n['name'] or '<root>'}  (modules {n['nModules']})")
    top_spread = sorted(by_name.values(), key=lambda x: -x["nModules"])[:8]
    print("namespaces across most modules:")
    for n in top_spread:
        print(f"  {n['nModules']:5d}  {n['name'] or '<root>'}")
    top_mod = sorted(mod_ns.items(), key=lambda kv: -len(kv[1]))[:8]
    print("modules hosting most namespaces:")
    for m, s in top_mod:
        print(f"  {len(s):5d}  {m}")

    ok = (dup == 0 and bad == 0 and pdup == 0 and pbad == 0 and not no_root
          and bad_parent == 0 and bad_depth == 0 and bad_root == 0
          and bad_kindsum == 0 and bad_mathlib == 0 and pbad_ns == 0
          and pbad_flag == 0 and pbad_kindsum == 0 and no_module >= 0
          and total_mathlib == MATHLIB_DECLS and pair_mathlib == MATHLIB_DECLS
          and 777000 <= total_decls <= 778000)
    if total_mathlib != MATHLIB_DECLS:
        print(f"MISMATHLIB node nMathlib {total_mathlib} != {MATHLIB_DECLS}")
    if pair_mathlib != MATHLIB_DECLS:
        print(f"MISMATHLIB pair nMathlib {pair_mathlib} != {MATHLIB_DECLS}")
    print("\nVERIFICATION", "OK" if ok else "FAILED")
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
