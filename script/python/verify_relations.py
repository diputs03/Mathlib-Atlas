#!/usr/bin/env python3
"""Verification for script 09 (richer Expr relationships).

Inputs:
  relations  : data/atlas_relations.jsonl
  skeletons  : data/atlas_type_skeletons.jsonl
Optional:
  --edges PATH        : the 08 edge file to reconcile against. The four type-role
                        counts on every relation row must sum, globally and per
                        pair, to 08's typeCount (likewise value), and the row /
                        source sets must match.
  --join-prefix STR   : also do an exact PER-PAIR reconciliation but only for
                        sources whose name starts with this prefix (bounded RAM).

Streaming, constant memory apart from the (optional) prefix join and source sets.
"""

import argparse
import collections
import json
import sys

REL_REQUIRED = {"source", "target", "targetKind", "isSelf",
                "typeHeadMain", "typeArgMain", "typeHeadBinder", "typeArgBinder",
                "valueHeadMain", "valueArgMain", "valueHeadBinder",
                "valueArgBinder"}
TYPE_ROLES = ["typeHeadMain", "typeArgMain", "typeHeadBinder", "typeArgBinder"]
VALUE_ROLES = ["valueHeadMain", "valueArgMain", "valueHeadBinder",
               "valueArgBinder"]
SKEL_REQUIRED = {"name", "kind", "module", "nPi", "nDefault", "nImplicit",
                 "nStrictImplicit", "nInstImplicit", "constraints",
                 "conclusionHead", "typeRolesTruncated", "valueRolesTruncated"}
KINDS = {"axiom", "definition", "opaque", "theorem", "quotient",
         "inductive", "constructor", "recursor", "unknown"}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("relations")
    ap.add_argument("skeletons")
    ap.add_argument("--edges")
    ap.add_argument("--join-prefix", default=None)
    args = ap.parse_args()

    # ---- relations -------------------------------------------------------
    n = 0
    seen = set()
    dup = bad = selfe = 0
    rel_src = set()
    sum_type = sum_value = 0
    role_tot = collections.Counter()
    prefix_rel = {}

    with open(args.relations, "rb") as fh:
        for raw in fh:
            r = json.loads(raw)
            n += 1
            if REL_REQUIRED - r.keys():
                bad += 1
            s, t = r["source"], r["target"]
            key = (s, t)
            if key in seen:
                dup += 1
            seen.add(key)
            rel_src.add(s)
            if r["targetKind"] not in KINDS:
                bad += 1
            if r["isSelf"] != (s == t):
                bad += 1
            if r["isSelf"]:
                selfe += 1
            tv = sum(r[k] for k in TYPE_ROLES)
            vv = sum(r[k] for k in VALUE_ROLES)
            for k in TYPE_ROLES + VALUE_ROLES:
                if not isinstance(r[k], int) or r[k] < 0:
                    bad += 1
                role_tot[k] += r[k]
            if tv + vv == 0:
                bad += 1  # a relation row must reference the target somewhere
            sum_type += tv
            sum_value += vv
            if args.join_prefix and (args.join_prefix == "*"
                                      or s.startswith(args.join_prefix)):
                prefix_rel[key] = (tv, vv)

    print(f"relation rows         : {n}")
    print(f"unique (source,target): {len(seen)} (duplicates {dup})")
    print(f"distinct sources      : {len(rel_src)}")
    print(f"self relations        : {selfe}")
    print(f"bad relation rows     : {bad}")
    print(f"role totals           : {dict(role_tot)}")
    print(f"sum of type roles     : {sum_type:,}")
    print(f"sum of value roles    : {sum_value:,}")
    ok = dup == 0 and bad == 0

    # ---- skeletons -------------------------------------------------------
    sn = 0
    sbad = 0
    with_constr = 0
    constr_slots = 0
    binder_tot = collections.Counter()
    concl = collections.Counter()
    skel_names = set()
    with open(args.skeletons, "rb") as fh:
        for raw in fh:
            r = json.loads(raw)
            sn += 1
            if SKEL_REQUIRED - r.keys():
                sbad += 1
            skel_names.add(r["name"])
            if r["nPi"] != (r["nDefault"] + r["nImplicit"]
                            + r["nStrictImplicit"] + r["nInstImplicit"]):
                sbad += 1
            for k in ("nDefault", "nImplicit", "nStrictImplicit", "nInstImplicit"):
                binder_tot[k] += r[k]
            csum = sum(c["count"] for c in r["constraints"])
            constr_slots += csum
            # each instImplicit binder contributes at most one constraint head
            if csum > r["nInstImplicit"]:
                sbad += 1
            if r["nInstImplicit"] > 0:
                with_constr += 1
            concl[r["conclusionHead"]] += 1
    print(f"\nskeleton rows         : {sn}")
    print(f"bad skeleton rows     : {sbad}")
    print(f"binder totals         : {dict(binder_tot)}")
    print(f"decls w/ constraints  : {with_constr} ({constr_slots} constraint slots)")
    print(f"top conclusion heads  : {concl.most_common(10)}")
    ok = ok and sbad == 0
    # Every relation source must have a skeleton; a declaration with ZERO
    # references legitimately has a skeleton but no relation rows (so relation
    # sources are a subset, not necessarily equal).
    if rel_src - skel_names:
        print("relation sources missing a skeleton:", len(rel_src - skel_names))
        ok = False
    print(f"skeletons w/o any relation: {len(skel_names - rel_src)}")

    # ---- reconcile against 08 edges -------------------------------------
    if args.edges:
        en = 0
        e_src = set()
        e_type = e_value = 0
        prefix_edge = {}
        with open(args.edges, "rb") as fh:
            for raw in fh:
                r = json.loads(raw)
                en += 1
                e_src.add(r["source"])
                e_type += r["typeCount"]
                e_value += r["valueCount"]
                if args.join_prefix and (args.join_prefix == "*"
                        or r["source"].startswith(args.join_prefix)):
                    prefix_edge[(r["source"], r["target"])] = (
                        r["typeCount"], r["valueCount"])
        print(f"\nedge rows             : {en}")
        print(f"sum edge typeCount    : {e_type:,}")
        print(f"sum edge valueCount   : {e_value:,}")
        if en != n:
            print("ROW COUNT MISMATCH"); ok = False
        if e_src != rel_src:
            print("SOURCE SET MISMATCH:", len(e_src ^ rel_src)); ok = False
        if e_type != sum_type:
            print(f"TYPE SUM MISMATCH {e_type} vs {sum_type}"); ok = False
        if e_value != sum_value:
            print(f"VALUE SUM MISMATCH {e_value} vs {sum_value}"); ok = False
        if args.join_prefix:
            keys = set(prefix_rel) | set(prefix_edge)
            mism = [k for k in keys if prefix_rel.get(k) != prefix_edge.get(k)]
            print(f"per-pair join [{args.join_prefix}]: {len(keys)} pairs, "
                  f"mismatches {len(mism)}")
            if mism:
                ok = False
        if en == n and e_type == sum_type and e_value == sum_value:
            print("global role<->edge reconciliation: EXACT")

    print("\nVERIFICATION", "OK" if ok else "FAILED")
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
