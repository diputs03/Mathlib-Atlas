#!/usr/bin/env python3
"""31_semantic_ledger.py — close the 627-pair semantic-candidate ledger.

Script 28 produced 627 structurally-divergent cross-area semantic pairs; probes
29 (case F, filter-relative) and 30 (case G, real/manifold smoothness) explained
the two large families kernel-side. This script assigns EVERY remaining pair to
a documented family with a MECHANICAL rule, so that the only pairs a human must
read are the small `unresolved` residual. Families:

  F_locus        global / on-set / at-point / within / almost-everywhere /
                 eventually — one Filter-relative generic (case F, probe 29).
  G_smooth       real-space vs manifold differentiability/smoothness (case G,
                 probe 30), incl. UniqueDiff/UniqueMDiff.
  add_mul_twin   additive vs multiplicative twin of ONE definition (to_additive).
  cat_dual       categorical dual / exactness: Limit/Colimit, Exact/ShortExact,
                 Left/Right, Epi/Mono, Injective/Surjective, co-/contra-.
  strength_arity strict/non-strict, arity (Injective/Injective2), point/global
                 (IsPeriodicPt/Periodic), connected/path-connected, strict order.
  same_root      identical conclusion-root (the divergence is elsewhere).
  num_domain     variant over Nat/Int/Rat/NNRat predicates.
  unresolved     anything not matched — listed for manual inspection.

Pure stdlib, deterministic. Inputs data/semantic_hidden_candidates.jsonl.
Outputs data/semantic_ledger.jsonl, data/semantic_ledger_summary.json.
"""
import json, collections, os

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
CAND = os.path.join(ROOT, "data", "semantic_hidden_candidates.jsonl")
OUT = os.path.join(ROOT, "data", "semantic_ledger.jsonl")
SUM = os.path.join(ROOT, "data", "semantic_ledger_summary.json")

# ---- mechanical normalizers -------------------------------------------------
LOCUS_STRIP = ("WithinAt", "OnWith", "At", "On", "With", "AE")
EVENTUALLY = ("EventuallyEqSet", "EventuallyEq", "EventuallyLE", "EventuallyLT",
              "EventuallyNE", "EventuallyGE", "EventuallyGT", "Eventually")
# filter-relative "tendsto / uniform-on-a-filter / has-prod" family
FILTER_MARK = ("Tendsto", "UniformlyOn", "OnFilter", "HasProd")
SMOOTH_MARK = ("ContDiff", "ContMDiff", "FDeriv", "MFDeriv", "Deriv",
               "Differentiable", "MDifferentiable", "UniqueDiff",
               "UniqueMDiff", "Smooth")
DUAL_PAIRS = [("Limit", "Colimit"), ("Epi", "Mono"),
              ("Injective", "Surjective"), ("Covariant", "Contravariant")]
DUAL_MARK = ("ShortExact", "Exact", "Left", "Right", "Homology")


def root(h):
    return (h or "").split(".")[-1]


def locus_base(r):
    """Strip locus decoration; return (base, was_decorated)."""
    for e in EVENTUALLY:
        if r.startswith(e) or r == e:
            return "Eventually", True
    orig = r
    for suf in LOCUS_STRIP:
        if r.endswith(suf) and len(r) > len(suf):
            r = r[: -len(suf)]
            break
    # leading almost-everywhere / quasi markers
    for pre in ("AE", "Quasi"):
        if r.startswith(pre) and len(r) > len(pre):
            r = r[len(pre):]
            break
    return r, (r != orig)


def addmul_norm(r):
    # to_additive twins: drop Add/Mul ornament
    return r.replace("Add", "").replace("Mul", "")


def concept_norm(r):
    """Same mathematical concept under bundled/unbundled or naming variants."""
    s = r
    for pre in ("Is",):
        if s.startswith(pre):
            s = s[len(pre):]
    for suf in ("Category", "Space"):
        if s.endswith(suf):
            s = s[: -len(suf)]
    for a, b in (("DirSup", "Sup"), ("PathConnected", "Connected"),
                 ("ClosedEmbedding", "Embedding"), ("Affine", "Linear"),
                 ("ℓp", "")):
        s = s.replace(a, b)
    return s.lower()


def is_smooth(r):
    return any(m in r for m in SMOOTH_MARK)


def is_filter_relative(a, b):
    ma = [m for m in FILTER_MARK if m in a]
    mb = [m for m in FILTER_MARK if m in b]
    return bool(ma) and bool(mb)


def is_dual(a, b):
    s = a + b
    for x, y in DUAL_PAIRS:
        if (x in a and y in b) or (y in a and x in b):
            return True
    if "Exact" in a and "Exact" in b:
        return True
    if (("Left" in a and "Right" in b) or ("Right" in a and "Left" in b)):
        return True
    if "Homology" in a and "Homology" in b:
        return True
    return False


def is_strength_arity(a, b):
    if a.replace("Strict", "") == b or b.replace("Strict", "") == a:
        return True
    pairs = [("Injective", "Injective2"), ("IsPeriodicPt", "Periodic"),
             ("IsConnected", "IsPathConnected"), ("SSubset", "Subset"),
             ("Subset", "SSubset"), ("IsClosedEmbedding", "IsEmbedding"),
             ("DirSupClosed", "SupClosed"),
             ("LocallyConnectedSpace", "LocallyPathConnectedSpace"),
             ("AffineIndependent", "LinearIndependent")]
    for x, y in pairs:
        if {a, b} == {x, y}:
            return True
    return False


def classify(ra, rb):
    # F: filter-relative locus family
    ba, da = locus_base(ra)
    bb, db = locus_base(rb)
    if (ba == bb and (da or db)) or (ba == "Eventually" and bb == "Eventually"):
        return "F_locus"
    if is_filter_relative(ra, rb):
        return "F_locus"
    # G: real vs manifold smoothness
    if is_smooth(ra) and is_smooth(rb):
        return "G_smooth"
    # additive/multiplicative twin of one definition
    if addmul_norm(ra) == addmul_norm(rb) and ra != rb:
        return "add_mul_twin"
    # categorical dual / exactness / left-right
    if is_dual(ra, rb):
        return "cat_dual"
    # strict / arity / point-global / strength variant
    if is_strength_arity(ra, rb):
        return "strength_arity"
    # numeric-domain predicate variants
    num = ("Nat", "Int", "Rat", "NNRat", "NNReal", "EReal", "ENNReal")
    if any(x in ra for x in num) and any(x in rb for x in num):
        return "num_domain"
    # same concept under bundled/unbundled or naming ornament
    if concept_norm(ra) == concept_norm(rb) and ra != rb:
        return "bundled_concept"
    # same root (divergence is in constraints/value, not head)
    if ra == rb:
        return "same_root"
    return "unresolved"


def main():
    rows = [json.loads(l) for l in open(CAND, encoding="utf-8")]
    out = []
    bucket = collections.Counter()
    unresolved = []
    for r in rows:
        ra, rb = root(r["a"]["conclusionHead"]), root(r["b"]["conclusionHead"])
        fam = classify(ra, rb)
        bucket[fam] += 1
        rec = {"cosine": r["cosine"], "family": fam,
               "a": {"name": r["a"]["name"], "area": r["a"]["area"], "head": ra},
               "b": {"name": r["b"]["name"], "area": r["b"]["area"], "head": rb}}
        out.append(rec)
        if fam == "unresolved":
            unresolved.append(rec)
    with open(OUT, "wb") as o:
        for rec in out:
            o.write((json.dumps(rec, ensure_ascii=False) + "\n").encode("utf-8"))
    # unresolved grouped by head pair for manual reading
    uc = collections.Counter(tuple(sorted((x["a"]["head"], x["b"]["head"])))
                             for x in unresolved)
    summary = {"total": len(rows), "byFamily": dict(bucket),
               "unresolved": len(unresolved),
               "unresolvedHeadPairs": [{"heads": list(k), "count": c}
                                       for k, c in uc.most_common()]}
    with open(SUM, "w", encoding="utf-8") as o:
        json.dump(summary, o, ensure_ascii=False, indent=2)
    print(f"total {len(rows)}")
    for k, v in bucket.most_common():
        print(f"  {k:<15}{v}")
    print(f"\nunresolved head pairs ({len(unresolved)} rows):")
    for (a, b), c in uc.most_common(60):
        print(f"  {c:>2}  {a}  <->  {b}")


if __name__ == "__main__":
    main()
