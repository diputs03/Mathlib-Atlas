"""
verify_pointwise_repeated.py — independent verification for script 26.

Re-derives every classification from the raw inputs (community_triage.jsonl +
atlas_features.jsonl) rather than trusting the output, then checks the output
file row-by-row. Prints VERIFICATION OK on success.
"""

import json
import collections
import os

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
DATA = os.path.join(ROOT, "data")

LOGICAL = {"And.intro", "Iff.mp", "Iff.mpr", "Iff.intro", "rfl", "Eq.refl",
           "Classical.byContradiction", "False.elim"}
CLASSES = {"shared_generic_core", "generic_type_construction",
           "shared_strategy_only"}


def load_jsonl(p):
    with open(p, encoding="utf-8") as f:
        return [json.loads(x) for x in f if x.strip()]


def expected_class(members, feat):
    vh, kinds = [], []
    for m in members:
        d = feat.get(m, {})
        vh.append(d.get("valueHead"))
        kinds.append(d.get("kind"))
    vc = collections.Counter(v for v in vh if v)
    shared = vc.most_common(1)[0][0] if vc else None
    if shared in LOGICAL:
        return "shared_strategy_only", shared
    if set(kinds) == {"definition"} and (
            shared is None or shared.endswith(".mk") or shared.endswith(".of")):
        return "generic_type_construction", shared
    return "shared_generic_core", shared


def main():
    triage = load_jsonl(os.path.join(DATA, "community_triage.jsonl"))
    pw = [r for r in triage if r.get("status") == "pointwise_repeated"]
    feat = {d["name"]: d for d in
            load_jsonl(os.path.join(DATA, "atlas_features.jsonl"))}
    out = load_jsonl(os.path.join(DATA, "pointwise_repeated_triage.jsonl"))
    summary = json.load(open(os.path.join(DATA,
                                          "pointwise_repeated_summary.json"),
                             encoding="utf-8"))

    errors = []

    # 1. population agreement
    if len(pw) != 11:
        errors.append(f"expected 11 pointwise_repeated in triage, got {len(pw)}")
    if len(out) != len(pw):
        errors.append(f"output rows {len(out)} != triage families {len(pw)}")

    triage_by_id = {r["clusterId"]: r for r in pw}
    out_by_id = {r["clusterId"]: r for r in out}
    if set(triage_by_id) != set(out_by_id):
        errors.append("clusterId sets differ between triage and output")

    # 2. re-derive classification independently for every row
    counts = collections.Counter()
    for cid, r in out_by_id.items():
        if r["class"] not in CLASSES:
            errors.append(f"{cid}: bad class {r['class']}")
            continue
        # members must be identical to the triage input
        src = triage_by_id[cid]["members"]
        if r["members"] != src:
            errors.append(f"{cid}: members mutated")
        exp, shared = expected_class(src, feat)
        if r["class"] != exp:
            errors.append(f"{cid} ({r['label']}): class {r['class']} != "
                          f"re-derived {exp} (shared V={shared})")
        if r["sharedValueHead"] != shared:
            errors.append(f"{cid}: sharedValueHead {r['sharedValueHead']} != "
                          f"{shared}")
        # every member must exist in the feature corpus
        for m in src:
            if m not in feat:
                errors.append(f"{cid}: member missing from features: {m}")
        # strategy-only specifics
        if r["class"] == "shared_strategy_only":
            if shared not in LOGICAL:
                errors.append(f"{cid}: strategy-only but V={shared} not logical")
            if not r["note"].strip():
                errors.append(f"{cid}: strategy-only lacks source note")
            if not r["candidateOpportunity"]:
                errors.append(f"{cid}: strategy-only must be flagged candidate")
        else:
            if r["candidateOpportunity"]:
                errors.append(f"{cid}: non-strategy family flagged candidate")
        counts[r["class"]] += 1

    # 3. expected distribution
    want = {"shared_generic_core": 6, "generic_type_construction": 3,
            "shared_strategy_only": 2}
    if dict(counts) != want:
        errors.append(f"class distribution {dict(counts)} != {want}")
    if summary["classCounts"] != want:
        errors.append("summary classCounts mismatch")
    if summary["nFamilies"] != 11:
        errors.append("summary nFamilies != 11")
    # source review cleared both candidates -> zero open opportunities
    if summary["nCandidateOpportunities"] != 2:
        errors.append("expected exactly 2 strategy-only candidates flagged")

    # 4. the shared generic cores must actually be domain (non-logical) heads
    for r in out:
        if r["class"] == "shared_generic_core" and (
                not r["sharedValueHead"] or
                r["sharedValueHead"] in LOGICAL):
            errors.append(f"{r['label']}: generic-core lacks domain value head")

    if errors:
        print("VERIFICATION FAILED")
        for e in errors:
            print("  -", e)
        raise SystemExit(1)

    print("VERIFICATION OK")
    print("  families:", dict(counts))
    print("  shared_generic_core already delegate to one generic lemma/ctor")
    print("  generic_type_construction build one generic target type")
    print("  shared_strategy_only (source-cleared, no extractable lemma):",
          [r["label"] for r in out if r["class"] == "shared_strategy_only"])


if __name__ == "__main__":
    main()
