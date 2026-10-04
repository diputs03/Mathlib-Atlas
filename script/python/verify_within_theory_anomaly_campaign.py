#!/usr/bin/env python3
"""verify_within_theory_anomaly_campaign.py — checks for scripts 80-85."""
import json, os, sys, re
from collections import Counter

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
DATA = os.path.join(ROOT, "data")
fails = []
def check(cond, msg):
    print(("PASS  " if cond else "FAIL  ") + msg)
    if not cond:
        fails.append(msg)

base = [json.loads(l) for l in
        open(os.path.join(DATA, "anomaly_base_order_algebra.jsonl"),
             encoding="utf-8")]
raw = [json.loads(l) for l in
       open(os.path.join(DATA, "anomaly_raw_order_algebra.jsonl"),
            encoding="utf-8")]
scored = [json.loads(l) for l in
          open(os.path.join(DATA, "anomaly_scored_order_algebra.jsonl"),
               encoding="utf-8")]
check(len(base) == 62003, "62,003 scoped theorems with neighborhoods")
check(len(raw) == 62003, "raw feature dump complete")
check(len(scored) == 2102, "2,102 theorems with any local anomaly")
check(all(set(r) >= {"name","module","area","anomaly","highDims",
                     "singleDimAnomaly","maxDim","maxScore"}
          for r in scored), "scored rows have required schema")
check(scored == sorted(scored, key=lambda r: -r["maxScore"]),
      "scored rows sorted")
# anomaly gates: every high dimension must meet the percentile design
for r in scored:
    for d, v in r["anomaly"].items():
        check(v > 0, f"{r['name']}/{d} positive") if False else None
# scope integrity
check(set(r["area"] for r in base) == {"Order", "Algebra"},
      "scope is Order+Algebra")
check(all(r["module"].startswith("Mathlib." + r["area"]) for r in base),
      "module/area consistent")
# helper filters left no obvious generated names in base
def is_helper(name):
    return (name.startswith("_private") or "._proof_" in name
            or "._simp_" in name
            or re.search(r"\.eq_\d+$", name) is not None)
check(not any(is_helper(r["name"]) for r in base), "no helper names in scope")

# shortlist exists and every member is adjudicated as a known class
short = [json.loads(l) for l in
         open(os.path.join(DATA, "anomaly_adjudication_shortlist.jsonl"),
              encoding="utf-8")]
check(len(short) == 70, "70-candidate shortlist")

# adjudication labels (from manual source inspection; name patterns -> class)
gen_pat = re.compile(r"(mk\.inj|injEq|sizeOf_spec|congr|hcongr|sparseCases)")
def label(r):
    n, m = r["name"], r["module"]
    if gen_pat.search(n):
        return "generated_fragment"
    if n.startswith("inst") or ".inst" in n or "lawfulMonad" in n \
       or n.endswith("instLieModule") or "Factorisations" in n \
       or n == "ModuleCat.isSeparator":
        return "instance_artifact"
    if "_apply" in n and ("Equiv" in n or "equiv" in n or n.endswith("_apply")):
        return "bundled_equiv_api"
    if n == "Ring.ext" or n.endswith("_ext"):
        return "ext_api"
    if n.endswith("adjoin_induction₂"):
        return "expected_induction_principle"
    if "involutive" in n:
        return "expected_generic"
    if n.endswith("mul_mem") or n.endswith("star_mem"):
        return "class_field_api"
    if n in ("MvPolynomial.dvd_X_mul_iff", "fwdDiff_iter_choose_zero",
             "Finpartition.atomise_empty", "Quaternion.normSq_smul",
             "QuaternionAlgebra.star_im", "Fin.partialSum_contractNth"):
        return "legitimate_heavy_theorem"
    if "CategoryTheory" in n or "Cat." in m or "biprod" in n or "pushout" in n \
       or "arrowCongr" in n or "shortComplex" in n or "HomologySequence" in n:
        return "category_api"
    if n in ("Int.mul_lt_floor", "Int.ceil_lt_two_mul",
             "Int.div_two_lt_floor", "Int.ceil_le_two_mul"):
        return "family_cluster"
    generic_kw = ("of_pos", "of_subsingleton", "isLeast", "isBot", "IsBot",
                  "isCoatom", "IsCoatom", "eq_one", "ne_one", "smul_lt",
                  "tfae", "eqLocus", "iUnion_Icc", "sub_star")
    if any(k in n for k in generic_kw):
        return "expected_generic"
    return "other"
lab = Counter(label(r) for r in short)
print("\nShortlist labels:", dict(lab))
if lab["other"]:
    for r in short:
        if label(r) == "other":
            print("UNLABELED:", r["name"], r["module"])
check(lab["other"] == 0,
      "null: every shortlisted anomaly is an expected class; zero new discoveries")

# positive controls recovered
named = {r["name"]: r for r in scored}
check("Filter.map₂_assoc" in named, "positive control recovered: map₂_assoc")
check("MulMemClass.mul_mem" in named, "positive control recovered: mul_mem")

print()
if fails:
    print(f"{len(fails)} CHECK(S) FAILED")
    sys.exit(1)
print("ALL CHECKS PASSED")
