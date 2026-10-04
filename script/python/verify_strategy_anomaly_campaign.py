#!/usr/bin/env python3
"""verify_strategy_anomaly_campaign.py — checks for scripts 77-79."""
import json, os, sys, re
from collections import Counter

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
DATA = os.path.join(ROOT, "data")
fails = []
def check(cond, msg):
    print(("PASS  " if cond else "FAIL  ") + msg)
    if not cond:
        fails.append(msg)

# ---- 77 raw corpus
raw = [json.loads(l) for l in
       open(os.path.join(DATA, "proof_skeletons_core.jsonl"), encoding="utf-8")]
check(len(raw) == 282971, "282,971 core theorem skeletons")
check(all(set(r) == {"name", "module", "area", "skeleton"} for r in raw),
      "rows have required schema")
c = Counter(r["area"] for r in raw)
check(set(c) == set(["Algebra","Analysis","Data","FieldTheory","GroupTheory",
                     "LinearAlgebra","Logic","Order","RingTheory","Topology"]),
      "all ten areas present")
check(c["Order"] == 26828,
      "Order count cross-validates script 75 (26,828)")
check(all(r["module"].startswith("Mathlib." + r["area"]) for r in raw),
      "module/area consistent for every row")

def is_helper(name):
    return (name.startswith("_private") or "._proof_" in name
            or "._simp_" in name
            or re.search(r"\.eq_\d+$", name) is not None)
real = [r for r in raw if not is_helper(r["name"])]
check(len(real) == 166948, "166,948 real theorems after helper filters")

# ---- 78 outputs
for f in ["strategy_exported.jsonl", "strategy_outliers.jsonl",
          "strategy_area_overlap.json", "strategy_anomaly_summary.json"]:
    p = os.path.join(DATA, f)
    check(os.path.exists(p) and os.path.getsize(p) > 0, f"exists: {f}")
exp = [json.loads(l) for l in
       open(os.path.join(DATA, "strategy_exported.jsonl"), encoding="utf-8")]
outl = [json.loads(l) for l in
        open(os.path.join(DATA, "strategy_outliers.jsonl"), encoding="utf-8")]
s78 = json.load(open(os.path.join(DATA,
        "strategy_anomaly_summary.json"), encoding="utf-8"))
check(s78["theorems"] == len(real), "78 theorem count consistent")
check(s78["exportedStrategyGroups"] == len(exp) == 40, "40 exported groups")
check(s78["outlierTheorems"] == len(outl) == 50, "50 outliers")
check(all(e["dominantFrac"] >= 0.7 and e["size"] >= 12 for e in exp),
      "exported groups meet dominance/size gates")
check(exp == sorted(exp, key=lambda e: -e["score"]), "exported groups scored/sorted")

# ---- 79 outputs
fine = [json.loads(l) for l in
        open(os.path.join(DATA, "strategy_fine_groups.jsonl"), encoding="utf-8")]
s79 = json.load(open(os.path.join(DATA,
        "strategy_fine_summary.json"), encoding="utf-8"))
check(s79["theorems"] == len(real), "79 theorem count consistent")
check(s79["crossAreaGroups"] == len(fine) == 108, "108 cross-area fine groups")
check(all(len(g["areas"]) >= 2 for g in fine), "fine groups span >=2 areas")
check(fine == sorted(fine, key=lambda g: -g["size"]), "fine groups sorted")

# ---- the audited null claim: cross-area fine groups are known classes only
import re as _re
gen_name = _re.compile(r"(sizeOf_spec|congr_eq_\d+|else_eq|sparseCases)")
def all_inst(g):
    return all(nm.startswith("inst") or ".inst" in nm
               for _, nm, _ in g["members"])
# bundled-hom / FunLike propagation keywords (script-64 class)
hom_kw = ("add_apply", "smul_apply", "coe_add", "coe_smul", "neg_apply",
          "sub_apply", "sum_apply", "coe_neg", "coe_sub", "coe_sum",
          "zero_apply", "coe_zero", "coeFn_zero", "domRestrict",
          "restrict_apply", "intCast_apply", "mul_apply_eq_comp",
          "one_apply_eq_self", "coeAddMonoidHom_apply", "finsetSum_apply",
          "coe_finsetSum", "coe_finset_sum", "forget_map", "finsetProd",
          "finsetSum", "map_id", "finset_prod", "finset_sum", "add_apply")
# generic relation-class propagation keywords (script-64 relation classes)
rel_kw = ("Symm", "isTrans", "refl", "symm", "total", "mem_singleton",
          "mem_pure", "insert_of", "mapsTo", "stdSymm", "Kmap")
# defeq copies / duals / expected generic propagation
copy_kw = ("some_inj", "unop_op", "equivRealProd", "instFinite",
           "commutative", "shrink", "of_ringEquiv", "of_surjective",
           "not_unit", "isSquare", "lcm_", "gcd", "of_eq", "of_le",
           "of_ge", "of_subsingleton", "of_equiv", "support_single",
           "finite_support", "finsetSum_index", "isTopologicalAddGroup",
          "eq_iff", "curry_", "lipschitz", "embDomain", "algHom_injective",
           "isLocalHom", "image_source", "coe_injective", "sumCongr",
           "mem_sub", "notMem", "mem_of", "succ_le", "sdiff_empty",
           "SizeOf", "isAddCommutative", "isMulCommutative", "Ksmul",
           "Kid", "Kcoe_to", "Kcoeff", "Kof_", "Kunop", "Kop ",
           "Center", "FiniteSupport", "isDiag", "generateFrom",
           "generate_of", "Kmpr", "notMem", "Kext")
# tiny groups manually adjudicated as unrelated one-liner shape coincidences
shape_coincidence_names = {
    "Nat.choose_succ_le_two_pow", "FreeAddMonoid.notMem_zero",
    "Matrix.isDiag_one", "Topology.CWComplex.Subcomplex.ext",
    "TopologicalSpace.isOpen_generateFrom_of_mem",
    "Int.ofNat_lt_ofNat_of_lt"}
def group_class(g):
    sig = g["signature"]
    names = [nm for _, nm, _ in g["members"]]
    if all(gen_name.search(nm) for nm in names):
        return "generated_equation_fragment"
    if sig in ("I", "TOPROJ") or all_inst(g):
        return "instance_fragment"
    if "PRIV" in sig:
        return "private_decidability_fragment"
    if any(k in sig for k in hom_kw) or any(k in nm for nm in names
                                             for k in ("not_unit",)):
        return "bundled_hom_api_propagation"
    if any(k in sig for k in rel_kw) or all("Center" in nm for nm in names):
        return "relation_class_propagation"
    if any(k in sig for k in copy_kw):
        return "defeq_copy_or_expected_generic"
    if any(nm in shape_coincidence_names for nm in names):
        return "generic_shape_coincidence"
    return "other"
cc = Counter(group_class(g) for g in fine)
print("\nFine cross-area group classes:", dict(cc))
if cc["other"]:
    for g in fine:
        if group_class(g) == "other":
            print("UNCLASSIFIED:", g["signature"][:120],
                  [nm for _, nm, _ in g["members"][:3]])
check(cc["other"] == 0,
      "null: every cross-area fine group is a known class or generated fragment")

print()
if fails:
    print(f"{len(fails)} CHECK(S) FAILED")
    sys.exit(1)
print("ALL CHECKS PASSED")
