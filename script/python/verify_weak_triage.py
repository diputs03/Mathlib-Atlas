"""
verify_weak_triage.py — independent verification for script 27.

Re-derives each weak community's class from community_triage.jsonl +
atlas_features.jsonl and checks the output row-by-row. VERIFICATION OK on
success.
"""

import json
import collections
import os

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
DATA = os.path.join(ROOT, "data")

MECHANICAL = {
    "And.intro", "And.left", "And.right", "Iff.mp", "Iff.mpr", "Iff.intro",
    "Eq.refl", "rfl", "Eq.rec", "Eq.mpr", "Eq.ndrec", "Eq.symm",
    "Exists.intro", "Exists.casesOn", "Prod.casesOn", "Prod.mk",
    "dite", "ite", "id", "Bind.bind", "HDiv.hDiv", "HMul.hMul", "HAdd.hAdd",
    "HSub.hSub", "iInf", "iSup", "Nat.brecOn", "Nat.cast", "Int.cast",
    "Or.inl", "Or.inr", "False.elim", "Classical.byContradiction",
    "WellFounded.fix", "PUnit",
}
CLASSES = {"generic_reuse", "mechanical_shape", "unrelated"}


def load_jsonl(p):
    with open(p, encoding="utf-8") as f:
        return [json.loads(x) for x in f if x.strip()]


def is_mech(v):
    return v in MECHANICAL or (v or "").endswith(".casesOn")


def majority(vheads, size, pred):
    c = collections.Counter(v for v in vheads if v and pred(v))
    if not c:
        return None
    v, n = c.most_common(1)[0]
    return v if n * 2 >= size else None


def derive(members, head_roots, feat):
    size = len(members)
    hroot = head_roots[0].split(".")[-1] if head_roots else None
    vh, aff = [], []
    for m in members:
        d = feat.get(m, {})
        vh.append(d.get("valueHead"))
        ms = m.split(".")
        aff.append(hroot is not None and hroot in ms[:-1])
    dom = majority(vh, size, lambda v: not is_mech(v))
    mec = majority(vh, size, is_mech)
    if dom is not None:
        return "generic_reuse", any(aff)
    if any(aff):
        return "generic_reuse", True
    if mec is not None:
        return "mechanical_shape", any(aff)
    return "unrelated", any(aff)


def main():
    tri = load_jsonl(os.path.join(DATA, "community_triage.jsonl"))
    weak = [r for r in tri if r.get("status") == "weak"]
    feat = {d["name"]: d for d in
            load_jsonl(os.path.join(DATA, "atlas_features.jsonl"))}
    out = load_jsonl(os.path.join(DATA, "weak_triage.jsonl"))
    summary = json.load(open(os.path.join(DATA, "weak_triage_summary.json"),
                             encoding="utf-8"))
    errors = []

    if len(weak) != 66:
        errors.append(f"expected 66 weak, got {len(weak)}")
    if len(out) != len(weak):
        errors.append(f"output {len(out)} != input {len(weak)}")
    by_id = {r["clusterId"]: r for r in out}
    if set(by_id) != {r["clusterId"] for r in weak}:
        errors.append("clusterId set mismatch")

    counts = collections.Counter()
    for r in weak:
        cid = r["clusterId"]
        o = by_id.get(cid)
        if o is None:
            errors.append(f"{cid} missing"); continue
        if o["class"] not in CLASSES:
            errors.append(f"{cid}: bad class {o['class']}")
        if o["members"] != r["members"]:
            errors.append(f"{cid}: members mutated")
        exp, _ = derive(r["members"], r.get("headAnchors") or [], feat)
        if o["class"] != exp:
            errors.append(f"{cid}: {o['class']} != re-derived {exp}")
        # internal consistency of generic_reuse
        if o["class"] == "generic_reuse":
            if not o["hasHeadApiMember"] and (
                    not o["sharedValueHead"] or
                    is_mech(o["sharedValueHead"]) or
                    o["sharedValueHead"].startswith("(")):
                errors.append(f"{cid}: generic_reuse without domain core/API")
        if o["class"] == "mechanical_shape" and not is_mech(
                o["sharedValueHead"] or ""):
            errors.append(f"{cid}: mechanical_shape non-mechanical V")
        if o["candidateOpportunity"]:
            errors.append(f"{cid}: unexpected candidate flag")
        for m in r["members"]:
            if m not in feat:
                errors.append(f"{cid}: member absent from features {m}")
        counts[o["class"]] += 1

    want = {"generic_reuse": 49, "mechanical_shape": 15, "unrelated": 2}
    if dict(counts) != want:
        errors.append(f"distribution {dict(counts)} != {want}")
    if summary["classCounts"] != want or summary["nFamilies"] != 66:
        errors.append("summary mismatch")
    if summary["nCandidateOpportunities"] != 0:
        errors.append("expected zero candidates")

    if errors:
        print("VERIFICATION FAILED")
        for e in errors:
            print("  -", e)
        raise SystemExit(1)
    print("VERIFICATION OK")
    print("  classes:", dict(counts))
    print("  candidate opportunities: 0")


if __name__ == "__main__":
    main()
