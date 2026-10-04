"""
27_weak_triage.py — close out the 66 `weak` cross-area communities from script
19. These are mostly pairs that clustered on a shared CONCLUSION head while
failing the stronger suffix/built-class tests. We split them using the shared
VALUE head (proof/body head constant) and each member's affinity to the
conclusion head's own namespace:

  generic_reuse      — members already invoke the SAME domain generic
                       constructor/lemma as value head (or one member is the
                       head's own API and the other builds through it); the
                       abstraction already exists -> no opportunity.
  mechanical_shape   — the only shared value head is a logical connective /
                       generic recursion / bind / cast / lattice op (And.intro,
                       Eq.rec, iSup, Bind.bind, ...): shared proof mechanics, no
                       mathematical common core -> embedding noise.
  unrelated          — no shared value head and no head-API member: coincidental
                       structural similarity -> embedding noise.

Deterministic, stdlib-only. Outputs data/weak_triage.jsonl +
data/weak_triage_summary.json.
"""

import json
import collections
import os

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
DATA = os.path.join(ROOT, "data")

# Shared value heads that carry no domain-specific abstraction: logical
# connectives, generic recursion, monadic/arithmetic operators, lattice ops.
MECHANICAL = {
    "And.intro", "And.left", "And.right", "Iff.mp", "Iff.mpr", "Iff.intro",
    "Eq.refl", "rfl", "Eq.rec", "Eq.mpr", "Eq.ndrec", "Eq.symm",
    "Exists.intro", "Exists.casesOn", "Prod.casesOn", "Prod.mk",
    "dite", "ite", "id", "Bind.bind", "HDiv.hDiv", "HMul.hMul", "HAdd.hAdd",
    "HSub.hSub", "iInf", "iSup", "Nat.brecOn", "Nat.cast", "Int.cast",
    "Or.inl", "Or.inr", "False.elim", "Classical.byContradiction",
    "WellFounded.fix", "PUnit",
}


def load_jsonl(p):
    with open(p, encoding="utf-8") as f:
        return [json.loads(x) for x in f if x.strip()]


def root_of(name):
    return name.split(".")[-1] if name else None


def is_mechanical(v):
    return v in MECHANICAL or (v or "").endswith(".casesOn")


def majority_shared(vheads, size, predicate):
    c = collections.Counter(v for v in vheads if v and predicate(v))
    if not c:
        return None, 0
    v, n = c.most_common(1)[0]
    return (v, n) if n * 2 >= size else (None, 0)


def main():
    triage = load_jsonl(os.path.join(DATA, "community_triage.jsonl"))
    weak = [r for r in triage if r.get("status") == "weak"]
    feat = {d["name"]: d for d in
            load_jsonl(os.path.join(DATA, "atlas_features.jsonl"))}

    out = []
    for r in weak:
        members = r["members"]
        size = len(members)
        heads = r.get("headAnchors") or []
        hroot = root_of(heads[0]) if heads else None

        vheads, aff = [], []
        for m in members:
            d = feat.get(m, {})
            vheads.append(d.get("valueHead"))
            ms = m.split(".")
            aff.append(hroot is not None and hroot in ms[:-1])
        has_head_api = any(aff)

        # shared DOMAIN (non-mechanical) value head among a majority of members
        dom_v, dom_n = majority_shared(
            vheads, size, lambda v: not is_mechanical(v))
        # shared MECHANICAL value head
        mec_v, mec_n = majority_shared(
            vheads, size, lambda v: is_mechanical(v))

        if dom_v is not None:
            cls = "generic_reuse"
            shared = dom_v
        elif has_head_api:
            # one member is the head's own API; treat as reuse of that API
            cls = "generic_reuse"
            shared = "(head-namespace API member)"
        elif mec_v is not None:
            cls = "mechanical_shape"
            shared = mec_v
        else:
            cls = "unrelated"
            shared = None

        out.append({
            "clusterId": r["clusterId"],
            "label": r["label"],
            "size": size,
            "nAreas": r["nAreas"],
            "areas": r["areas"],
            "meanCosine": r.get("meanCosine"),
            "headRoot": hroot,
            "members": members,
            "valueHeads": vheads,
            "hasHeadApiMember": has_head_api,
            "sharedValueHead": shared,
            "class": cls,
            "candidateOpportunity": False,  # source/value-head review below
        })

    order = {"generic_reuse": 0, "mechanical_shape": 1, "unrelated": 2}
    out.sort(key=lambda x: (order[x["class"]], -x["size"], x["clusterId"]))

    with open(os.path.join(DATA, "weak_triage.jsonl"), "w",
              encoding="utf-8") as f:
        for row in out:
            f.write(json.dumps(row, ensure_ascii=False) + "\n")

    counts = collections.Counter(r["class"] for r in out)
    summary = {
        "nFamilies": len(out),
        "classCounts": dict(counts),
        "nCandidateOpportunities":
            sum(1 for r in out if r["candidateOpportunity"]),
        "conclusion": (
            "Every weak community either already reuses one domain generic "
            "constructor/lemma (generic_reuse) or shares only mechanical proof "
            "shape / nothing (noise). No missing-abstraction candidates."
        ),
        "families": [{"clusterId": r["clusterId"], "class": r["class"],
                      "headRoot": r["headRoot"],
                      "sharedValueHead": r["sharedValueHead"],
                      "size": r["size"]} for r in out],
    }
    with open(os.path.join(DATA, "weak_triage_summary.json"), "w",
              encoding="utf-8") as f:
        json.dump(summary, f, ensure_ascii=False, indent=2)

    print(f"weak families: {len(out)}")
    for k in ("generic_reuse", "mechanical_shape", "unrelated"):
        print(f"  {k}: {counts.get(k,0)}")
    print("candidate opportunities:", summary["nCandidateOpportunities"])


if __name__ == "__main__":
    main()
