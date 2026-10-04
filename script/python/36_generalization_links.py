#!/usr/bin/env python3
"""36_generalization_links.py — theorem generalization/specialization families.

Distinct from analogy (17-33): here we ask, for each theorem *shape*, whether a
fully polymorphic (generic) version exists, or only concrete specializations.

A theorem is GENERIC when its forall prefix introduces a universe-polymorphic
type variable (a binder whose type is `Sort`/`Type`, tag "sort"); it is
SPECIALIZED when it has no such binder and instead reasons about a concrete
carrier (e.g. `{n : Nat}`). Theorems are grouped by a generalization signature
  (conclusionHead, sorted constraint-class tuple, nDefault explicit args),
which is invariant under specializing the carrier (a,b stay the same arity).

A group is COVERED when it has >=1 generic member (the general theorem exists).
A GENERALIZATION OPPORTUNITY is a group with several concrete specializations over
>=2 distinct carriers (namespace roots) but NO generic member: the shape was
re-proved per carrier and the polymorphic theorem may be missing.

Inputs : data/atlas_corpus.jsonl (typeAst), data/atlas_type_skeletons.jsonl
Outputs: data/generalization_opportunities.jsonl, data/generalization_summary.json
Pure stdlib, deterministic, streaming, online aggregation.
"""
import json, os, collections

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
DATA = os.path.join(ROOT, "data")
CORPUS = os.path.join(DATA, "atlas_corpus.jsonl")
SKEL = os.path.join(DATA, "atlas_type_skeletons.jsonl")
OUT_OPP = os.path.join(DATA, "generalization_opportunities.jsonl")
OUT_SUM = os.path.join(DATA, "generalization_summary.json")

MIN_SPEC = 3          # >= this many specialized members
MIN_CARRIERS = 2      # across >= this many distinct carriers
GEN_TAILS = ("casesOn", "recOn", "brecOn", "inductionOn", "noConfusion",
             "noConfusionType", "rec", "mk")
# ultra-generic logical heads: grouping on these alone over-merges unrelated
# statements, so they only qualify when backed by real (nonempty) constraints.
# Stored as the head's LAST segment (conclusionHead may be qualified, e.g. LE.le)
GENERIC_LOGIC_HEADS = {"eq", "iff", "exists", "le", "lt", "ge", "gt", "and",
                       "or", "not", "true", "false", "heq", "mem", "subset",
                       "ssubset", "ne", "nonempty", "dvd"}


def load_class_heads():
    p = os.path.join(DATA, "atlas_classes.jsonl")
    heads = set()
    for line in open(p, encoding="utf-8"):
        c = json.loads(line)
        heads.add(c["name"].split(".")[-1])
    return heads


def is_generic(type_ast):
    """True iff the forall prefix binds a universe-sorted type variable."""
    node = type_ast
    while isinstance(node, dict) and "binderInfo" in node:
        bt = node.get("binderType")
        if isinstance(bt, dict) and bt.get("tag") == "sort":
            return True
        node = node["body"]
    return False


def constraint_key(constraints):
    return tuple(sorted(c["class"] for c in (constraints or [])))


def carrier_root(namespace):
    if not namespace:
        return ""
    return namespace.split(".")[0]


def main():
    class_heads = load_class_heads()
    # skeleton lookup (small fields): conclusionHead, constraints, nDefault
    skel = {}
    for line in open(SKEL, encoding="utf-8"):
        s = json.loads(line)
        if s.get("kind") != "theorem":
            continue
        skel[s["name"]] = (s.get("conclusionHead"),
                           constraint_key(s.get("constraints")),
                           s.get("nDefault", 0))

    # online aggregation per signature
    groups = {}
    n_theorems = n_generic = n_specialized = n_skipped = 0
    for line in open(CORPUS, encoding="utf-8"):
        r = json.loads(line)
        if r.get("kind") != "theorem":
            continue
        mod = r.get("module", "")
        if not mod.startswith("Mathlib"):
            continue
        name = r["name"]
        tail = name.split(".")[-1]
        if tail in GEN_TAILS or name.startswith("_"):
            continue
        sk = skel.get(name)
        if sk is None:
            n_skipped += 1
            continue
        head, ckey, ndef = sk
        if not head:
            n_skipped += 1
            continue
        ta = r.get("typeAst")
        if not isinstance(ta, dict):
            n_skipped += 1
            continue
        n_theorems += 1
        gen = is_generic(ta)
        key = (head, ckey, ndef)
        g = groups.get(key)
        if g is None:
            g = {"generic": 0, "spec": 0, "carriers": set(), "areas": set(),
                 "examples": []}
            groups[key] = g
        area = mod.split(".")[1] if mod.count(".") >= 1 else ""
        if gen:
            g["generic"] += 1
            n_generic += 1
        else:
            g["spec"] += 1
            n_specialized += 1
            g["carriers"].add(carrier_root(r.get("namespace", "")))
            g["areas"].add(area)
            if len(g["examples"]) < 12:
                g["examples"].append(name)

    # classify groups
    opps = []
    raw_opps = 0
    reject_class_head = reject_empty_constr = 0
    n_covered = n_spec_only = n_pure_generic = 0
    for (head, ckey, ndef), g in groups.items():
        carriers = {c for c in g["carriers"] if c}
        if g["generic"] > 0:
            if g["spec"] > 0:
                n_covered += 1
            else:
                n_pure_generic += 1
            continue
        n_spec_only += 1
        if not (g["spec"] >= MIN_SPEC and len(carriers) >= MIN_CARRIERS):
            continue
        raw_opps += 1
        # second-stage: a missing generic LEMMA has real hypotheses (constraints)
        # and is not a per-carrier class/prop-fact. Bare logical connectives
        # (Eq/Iff/Exists/order...) cannot identify a common statement from
        # head+constraints+arity alone, so they are excluded outright.
        head_tail = head.split(".")[-1]
        if head_tail in class_heads:
            reject_class_head += 1
            continue
        if head_tail.lower() in GENERIC_LOGIC_HEADS or not ckey:
            reject_empty_constr += 1
            continue
        # drop namespace-extraction artifacts from the carrier set
        carriers = {c for c in carriers
                    if c and c != "[anonymous]" and c != "definition"
                    and not c.startswith("inst")}
        if len(carriers) < MIN_CARRIERS:
            reject_empty_constr += 1
            continue
        opps.append({
            "conclusionHead": head,
            "constraints": list(ckey),
            "nDefault": ndef,
            "nSpecialized": g["spec"],
            "nCarriers": len(carriers),
            "carriers": sorted(carriers),
            "areas": sorted(a for a in g["areas"] if a),
            "examples": g["examples"]})
    opps.sort(key=lambda o: (-o["nCarriers"], -o["nSpecialized"],
                             o["conclusionHead"]))
    with open(OUT_OPP, "wb") as o:
        for rec in opps:
            o.write((json.dumps(rec, ensure_ascii=False) + "\n").encode("utf-8"))

    summary = {
        "theoremsConsidered": n_theorems,
        "genericTheorems": n_generic,
        "specializedTheorems": n_specialized,
        "skippedNoSkeleton": n_skipped,
        "shapeGroups": len(groups),
        "coveredGroupsGenericPlusSpec": n_covered,
        "pureGenericGroups": n_pure_generic,
        "specializedOnlyGroups": n_spec_only,
        "rawOpportunities": raw_opps,
        "rejectedClassPropHead": reject_class_head,
        "rejectedEmptyConstraints": reject_empty_constr,
        "generalizationOpportunities": len(opps),
        "params": {"minSpec": MIN_SPEC, "minCarriers": MIN_CARRIERS},
        "topOpportunities": opps[:25],
    }
    with open(OUT_SUM, "w", encoding="utf-8") as o:
        json.dump(summary, o, ensure_ascii=False, indent=2)

    print(f"theorems {n_theorems} (generic {n_generic}, specialized "
          f"{n_specialized}, skipped {n_skipped})")
    print(f"shape groups {len(groups)}: covered(gen+spec) {n_covered}, "
          f"pure-generic {n_pure_generic}, specialized-only {n_spec_only}")
    print(f"GENERALIZATION OPPORTUNITIES: {len(opps)}")
    for o in opps[:30]:
        print(f"  {o['conclusionHead']:<22} ndef={o['nDefault']} "
              f"spec={o['nSpecialized']:<3} carriers={o['nCarriers']} "
              f"{o['carriers'][:6]}")


if __name__ == "__main__":
    main()
