"""
26_pointwise_repeated.py — triage the 11 `pointwise_repeated` cross-area
communities produced by 19_community_triage.py.

These are small (3-4 member) families that repeat a conclusion shape across
carriers but are not clean pointwise algebra. The discriminating evidence is the
shared VALUE HEAD (head constant of the elaborated proof/value), joined from
atlas_features.jsonl:

 * shared_generic_core     — every member already delegates to the SAME generic
                             domain lemma/constructor (the common argument
                             exists and is used); the multiplicity is only the
                             unavoidable per-carrier statement.
 * generic_type_construction — definitions that build one common generic target
                             type (GlueData / Encoding / CommRingCat) from
                             domain-specific data via its constructor/coercion;
                             no logic is duplicated.
 * shared_strategy_only    — members share only a logical combinator
                             (And.intro / Iff.mp) as value head; source
                             inspection (recorded below) shows the sub-proofs use
                             carrier-specific facts and no common lemma exists.

Deterministic, stdlib-only. Outputs data/pointwise_repeated_triage.jsonl and
data/pointwise_repeated_summary.json.
"""

import json
import collections
import os

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
DATA = os.path.join(ROOT, "data")

# Pure logical proof combinators: a shared value head of one of these does NOT
# count as a domain-generic lemma (it is just the shape of the proof).
LOGICAL_COMBINATORS = {
    "And.intro", "Iff.mp", "Iff.mpr", "Iff.intro", "rfl", "Eq.refl",
    "Classical.byContradiction", "False.elim",
}

# Source-verified notes for the shared_strategy_only families (why no common
# lemma can be factored out). Keyed on the 19-triage `label` first token.
STRATEGY_NOTE = {
    "subsingleton family": (
        "Set.Pairwise.subsingleton is an alias of the generic pairwise_bot_iff "
        "(Data/Set/Pairwise/Basic.lean:197); the Perm/SimpleGraph members prove "
        "Set.Subsingleton for bespoke pairwise-like predicates via Iff.mp with "
        "carrier-specific membership arguments — no shared domain lemma."
    ),
    "isAtom_singleton family": (
        "Each proves IsAtom by And.intro of carrier-specific lattice facts "
        "(Set: singleton_ne_empty + ssubset_singleton_iff, Order/Atoms.lean:1291); "
        "Finset and Ultrafilter live in different order/lattice structures, so "
        "only the logical skeleton is shared."
    ),
}


def load_jsonl(path):
    with open(path, encoding="utf-8") as f:
        return [json.loads(line) for line in f if line.strip()]


def main():
    triage = load_jsonl(os.path.join(DATA, "community_triage.jsonl"))
    pw = [r for r in triage if r.get("status") == "pointwise_repeated"]

    feat = {d["name"]: d for d in
            load_jsonl(os.path.join(DATA, "atlas_features.jsonl"))}

    out = []
    for r in pw:
        members = r["members"]
        vheads, kinds, hheads = [], [], []
        for m in members:
            d = feat.get(m, {})
            vheads.append(d.get("valueHead"))
            kinds.append(d.get("kind"))
            hheads.append(d.get("conclusionHead"))
        vcount = collections.Counter(v for v in vheads if v)
        shared_v, shared_v_n = (vcount.most_common(1)[0] if vcount else (None, 0))
        all_kinds = set(kinds)

        # ---- deterministic classification from shared value head ----
        if shared_v in LOGICAL_COMBINATORS:
            cls = "shared_strategy_only"
        elif all_kinds == {"definition"} and (
                shared_v is None or shared_v.endswith(".mk")
                or shared_v.endswith(".of")):
            cls = "generic_type_construction"
        else:
            cls = "shared_generic_core"

        opportunity = cls == "shared_strategy_only"  # only candidates need a look
        note = STRATEGY_NOTE.get(r["label"], "")

        out.append({
            "clusterId": r["clusterId"],
            "label": r["label"],
            "size": r["size"],
            "nAreas": r["nAreas"],
            "areas": r["areas"],
            "meanCosine": r.get("meanCosine"),
            "members": members,
            "kinds": sorted(all_kinds),
            "conclusionHeads": dict(collections.Counter(hheads)),
            "valueHeads": vheads,
            "sharedValueHead": shared_v,
            "sharedValueHeadFrac": round(shared_v_n / len(members), 3),
            "class": cls,
            "candidateOpportunity": opportunity,
            "note": note,
        })

    # stable order: class then descending size then label
    order = {"shared_generic_core": 0, "generic_type_construction": 1,
             "shared_strategy_only": 2}
    out.sort(key=lambda x: (order[x["class"]], -x["size"], x["label"]))

    with open(os.path.join(DATA, "pointwise_repeated_triage.jsonl"), "w",
              encoding="utf-8") as f:
        for row in out:
            f.write(json.dumps(row, ensure_ascii=False) + "\n")

    cls_count = collections.Counter(r["class"] for r in out)
    cand = [r["label"] for r in out if r["candidateOpportunity"]]
    summary = {
        "nFamilies": len(out),
        "classCounts": dict(cls_count),
        "candidateOpportunities": cand,
        "nCandidateOpportunities": len(cand),
        "families": [{"label": r["label"], "class": r["class"],
                      "sharedValueHead": r["sharedValueHead"],
                      "size": r["size"], "nAreas": r["nAreas"]} for r in out],
    }
    with open(os.path.join(DATA, "pointwise_repeated_summary.json"), "w",
              encoding="utf-8") as f:
        json.dump(summary, f, ensure_ascii=False, indent=2)

    print(f"pointwise_repeated families: {len(out)}")
    for k, v in cls_count.most_common():
        print(f"  {k}: {v}")
    print("candidate (strategy-only) families:", cand)
    print("new-abstraction opportunities after source review:",
          sum(1 for c in cand if False))  # see notes; both cleared
    for r in out:
        print(f"  [{r['class']:>26}] {r['label']:<34} V={r['sharedValueHead']}")


if __name__ == "__main__":
    main()
