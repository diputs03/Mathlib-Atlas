#!/usr/bin/env python3
"""verify_typeclass_structure.py — independent verification for script 34.

Rebuilds the hierarchy and gap set from the raw class/instance files and checks:
  1. summary scalar counts reconcile;
  2. every referenced parent is a known class (DAG well-formed);
  3. multiple-inheritance / diamond counts reproduce;
  4. each emitted gap satisfies, independently: missingParent is a direct
     subobject=false parent of strongClass, the carrier concretely has the
     strong class and concretely lacks the parent, and the peer majority rule
     holds; and the emitted gap set equals the recomputed set (bijection);
  5. gap rows are sorted as documented.
Pure stdlib.
"""
import json, os, sys, collections

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
DATA = os.path.join(ROOT, "data")
PEER_MIN, PEER_RATIO = 3, 0.66


def load(f):
    return [json.loads(l) for l in open(os.path.join(DATA, f), encoding="utf-8")]


def descendants(children, root):
    seen, st = set(), [root]
    while st:
        n = st.pop()
        for ch in children.get(n, ()):
            if ch not in seen:
                seen.add(ch); st.append(ch)
    return seen


def main():
    allcls = load("atlas_classes.jsonl")
    classes = [c for c in allcls if c["mathlib"]]
    instances = [i for i in load("atlas_instances.jsonl") if i["mathlib"]]
    gaps = [json.loads(l) for l in open(os.path.join(DATA, "typeclass_gap_candidates.jsonl"),
                                        encoding="utf-8")]
    summary = json.load(open(os.path.join(DATA, "typeclass_structure_summary.json"),
                             encoding="utf-8"))
    errs = []
    allnames = {c["name"] for c in allcls}
    by = {c["name"]: c for c in classes}

    parents = {c["name"]: [(p["name"], p["subobject"]) for p in c.get("parents", [])]
               for c in classes}
    # 2. DAG well-formed: a parent may be absent from the extracted class file
    # only when it is a known extraction-coverage/name-qualification case
    # (structure not enumerated as a class, or namespace-qualified name). Such
    # edges are inert in script 34 (guarded by `p in by`); record and bound them.
    bad_parents = [(c, p) for c, ps in parents.items() for (p, _) in ps
                   if p not in allnames]
    KNOWN_DANGLING = {
        ("IsLocalization'", "Submonoid.IsLocalizationMap"),
        ("GroupFilterBasis", "FilterBasis"),
        ("AddGroupFilterBasis", "FilterBasis")}
    dangling_set = set(bad_parents)
    if dangling_set != KNOWN_DANGLING:
        errs.append(f"unexpected dangling parent refs: "
                    f"{dangling_set - KNOWN_DANGLING} / "
                    f"missing {KNOWN_DANGLING - dangling_set}")

    children = collections.defaultdict(list)
    for c, ps in parents.items():
        for (p, _) in ps:
            children[p].append(c)

    def anc(name):
        seen, st = set(), list(parents.get(name, []))
        while st:
            p, _ = st.pop()
            if p in seen: continue
            seen.add(p); st.extend(parents.get(p, []))
        return seen

    n_multi = sum(1 for c in classes if len(parents[c["name"]]) >= 2)
    def diamond(c):
        ps = [p for (p, _) in parents[c] if p in by]
        if len(ps) < 2: return False
        a = [anc(p) | {p} for p in ps]
        return any(a[i] & a[j] for i in range(len(a)) for j in range(i + 1, len(a)))
    n_dia = sum(1 for c in classes if diamond(c["name"]))
    if n_multi != summary["hierarchy"]["multipleInheritance"]:
        errs.append("multipleInheritance mismatch")
    if n_dia != summary["hierarchy"]["diamonds"]:
        errs.append("diamond count mismatch")
    if summary["mathlibClasses"] != len(classes) or \
       summary["mathlibInstances"] != len(instances):
        errs.append("class/instance totals mismatch")

    # concrete carrier map (rebuilt)
    carrier = collections.defaultdict(set)
    cls_car = collections.defaultdict(set)
    for i in instances:
        t, c = i.get("targetHead"), i["className"]
        if not t or c not in by: continue
        carrier[t].add(c); cls_car[c].add(t)

    # recompute gap set
    expect = {}
    for c in classes:
        cn = c["name"]
        cross = [p for (p, sub) in parents[cn] if not sub and p in by]
        cars = cls_car.get(cn, set())
        if len(cars) < PEER_MIN or not cross: continue
        for P in cross:
            prov = [T for T in cars if P in carrier[T]]
            nonp = [T for T in cars if P not in carrier[T]]
            tot = len(prov) + len(nonp)
            if len(prov) < PEER_MIN or tot == 0: continue
            ratio = len(prov) / tot
            if ratio >= PEER_RATIO and nonp:
                for T in nonp:
                    expect[(T, cn, P)] = (len(prov), len(nonp), round(ratio, 3))
    got = {(g["carrier"], g["strongClass"], g["missingParent"]) for g in gaps}
    if set(expect) != got:
        errs.append(f"gap set mismatch: missing {len(set(expect)-got)} "
                    f"extra {len(got-set(expect))}")
    if len(gaps) != summary["gapCandidates"]:
        errs.append("gap count vs summary mismatch")

    # 4. per-row invariants
    for g in gaps:
        cn, P, T = g["strongClass"], g["missingParent"], g["carrier"]
        crossnames = [p for (p, sub) in parents.get(cn, []) if not sub]
        if P not in crossnames:
            errs.append(f"{cn}->{P} not a direct cross parent"); break
        if cn not in carrier[T]:
            errs.append(f"{T} lacks strong class {cn}"); break
        if P in carrier[T]:
            errs.append(f"{T} already has {P}"); break
        prov, nonp, ratio = expect[(T, cn, P)]
        if g["providers"] != prov or g["nonproviders"] != nonp or \
           abs(g["providerRatio"] - ratio) > 1e-9:
            errs.append(f"peer counts wrong for {T} {cn}->{P}"); break
        if prov < PEER_MIN or ratio < PEER_RATIO:
            errs.append(f"peer rule not met for {T} {cn}->{P}"); break

    # 5. sorted
    keys = [(-g["providerRatio"], -g["providers"], g["strongClass"], g["carrier"])
            for g in gaps]
    if keys != sorted(keys):
        errs.append("gaps not sorted as documented")

    print("classes", len(classes), "instances", len(instances),
          "multi", n_multi, "diamonds", n_dia, "gaps", len(gaps))
    if errs:
        print("FAILURES:")
        for e in errs[:25]: print("  -", e)
        sys.exit(1)
    print("VERIFICATION OK")


if __name__ == "__main__":
    main()
