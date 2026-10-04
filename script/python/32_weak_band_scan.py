#!/usr/bin/env python3
"""32_weak_band_scan.py — hunt a possible case H in the 0.70-0.80 semantic band.

Script 28 kept cosine >= 0.80 (627 pairs, fully closed by 29-31). This script
looks at the WEAKER band [0.70, 0.80) produced by a 0.70-threshold run:

  weak pair  = loose(>=0.70) minus tight(>=0.80)
For each weak pair it applies the SAME family rules as 31_semantic_ledger
(imported, not copied). Pairs those rules cannot place (`unresolved`) are the
only place a genuinely new abstraction could hide; everything else is an
already-known family that merely scored below the strict cutoff.

Inputs : data/semantic_hidden_candidates_loose070.jsonl  (ATLAS_SEM_THRESH=0.70)
         data/semantic_hidden_candidates.jsonl           (the 627, >=0.80)
Outputs: data/semantic_weak_band_residual.jsonl          (novel unresolved only)
         data/semantic_weak_band_summary.json
Pure stdlib, deterministic.
"""
import json, os, sys, collections

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
sys.path.insert(0, os.path.join(ROOT, "script", "python"))
import importlib.util
_spec = importlib.util.spec_from_file_location(
    "led", os.path.join(ROOT, "script", "python", "31_semantic_ledger.py"))
led = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(led)  # main() is guarded, only functions load

DATA = os.path.join(ROOT, "data")
LOOSE = os.path.join(DATA, "semantic_hidden_candidates_loose070.jsonl")
TIGHT = os.path.join(DATA, "semantic_hidden_candidates.jsonl")
OUT = os.path.join(DATA, "semantic_weak_band_residual.jsonl")
SUM = os.path.join(DATA, "semantic_weak_band_summary.json")
BAND_LO, BAND_HI = 0.70, 0.80


def pairkey(r):
    return frozenset((r["a"]["name"], r["b"]["name"]))


# ---- weak-band second-stage classifier -------------------------------------
# In [0.70,0.80) the residual is dominated by surface variants whose HEAD ROOTS
# differ, so the strict ledger-31 rules leave them "unresolved". These broader
# normalizers are applied ONLY to the weak band.
STRENGTH_TOKENS = ("Strongly", "Strong", "Weak", "Strict", "Local", "Locally",
                   "Uniform", "Antitone", "Generalized", "Gen", "Open", "Closed",
                   "Split", "Regular", "Normal", "Quasi", "Left", "Right",
                   "Pred", "Succ", "Formal", "Formally", "Null", "Baire",
                   "Increasing", "Approximate", "Semi", "OfSize", "OfShape",
                   "Binary", "Finite", "System", "Operator", "TVS", "Nhd",
                   "OnBall", "On", "At", "₂", "2")
ORDER_CMP = ("LE", "LT", "GE", "GT")
ARROW_WORDS = ("Injective", "Surjective", "Bijective", "Mono", "Epi", "IsIso",
               "Inverse", "Involutive", "Total", "Dvd", "Saturated")
CATLIM_WORDS = ("Limit", "Colimit", "Limits", "Colimits", "Biproduct",
                "Product", "Kernel", "Cokernel", "Pullback", "Epimorphism",
                "Monomorphism")
MEAS_WORDS = ("Measurable", "Integrable", "Summable", "Measure", "Tight",
              "Progressive", "MeasurePreserving")
FIN_WORDS = ("Finite", "FG", "RkFinite", "TorsionFree", "Presentation",
             "Dimensional", "Free")
INDEP_WORDS = ("Independent", "Indep", "Disjoint")


def strength_norm(r):
    s = r
    # order-comparator suffixes collapse
    for c in ORDER_CMP:
        if s.endswith(c):
            s = s[: -len(c)]
    for t in STRENGTH_TOKENS:
        s = s.replace(t, "")
    # weak/strong single-letter prefixes W/S before a capital (WSameSide etc.)
    if len(s) > 1 and s[0] in "WS" and s[1].isupper():
        s = s[1:]
    return s


def has_prefix_word(r):
    return r.startswith(("Has", "Preserves", "Reflects"))


def weak_family(ra, rb):
    # independence cluster (kept distinct for separate inspection)
    if all(any(w in x for w in INDEP_WORDS) for x in (ra, rb)):
        return "wb_independence"
    # categorical arrow strength / existence-preservation-reflection
    if all(any(w in x for w in ARROW_WORDS) for x in (ra, rb)):
        return "wb_arrow_strength"
    if (all(has_prefix_word(x) for x in (ra, rb)) and
            all(any(w in x for w in CATLIM_WORDS) for x in (ra, rb))):
        return "wb_cat_limit"
    if all(any(w in x for w in CATLIM_WORDS) for x in (ra, rb)):
        return "wb_cat_limit"
    # measurability / integrability strength family
    if all(any(w in x for w in MEAS_WORDS) for x in (ra, rb)):
        return "wb_measure"
    # finiteness / module-finiteness family
    if all(any(w in x for w in FIN_WORDS) for x in (ra, rb)):
        return "wb_finiteness"
    # notation / carrier twin: iSup/sSup, SMul/Mul, ModEq/SModEq, MemLp
    def notation(x):
        return x.replace("iSup", "Sup").replace("sSup", "Sup") \
                .replace("SModEq", "ModEq").replace("SMul", "Mul") \
                .replace("MemLp", "mem").replace("Memℓp", "mem").lower()
    if notation(ra) == notation(rb) and ra != rb:
        return "wb_notation_twin"
    # generic weak/strong/local/uniform/order-comparator normalization
    if strength_norm(ra) == strength_norm(rb) and ra != rb:
        return "wb_strength_variant"
    # Is/Has/Of naming ornament on a common core
    def core(x):
        for p in ("Is", "Has", "Of"):
            if x.startswith(p):
                x = x[len(p):]
        for s in ("Set", "Map", "Category"):
            if x.endswith(s):
                x = x[: -len(s)]
        return x.lower()
    if core(ra) == core(rb) and ra != rb:
        return "wb_naming"
    return "wb_noise"


def main():
    loose = [json.loads(l) for l in open(LOOSE, encoding="utf-8")]
    tight = [json.loads(l) for l in open(TIGHT, encoding="utf-8")]
    tightset = {pairkey(r) for r in tight}

    fam_counter = collections.Counter()
    weak_counter = collections.Counter()
    residual = []
    n_weak = 0
    for r in loose:
        if pairkey(r) in tightset:
            continue
        c = r["cosine"]
        if not (BAND_LO <= c < BAND_HI):
            continue
        n_weak += 1
        ra, rb = led.root(r["a"]["conclusionHead"]), led.root(r["b"]["conclusionHead"])
        fam = led.classify(ra, rb)
        fam_counter[fam] += 1
        if fam == "unresolved":
            wf = weak_family(ra, rb)
            weak_counter[wf] += 1
            if wf == "wb_noise":
                residual.append({
                    "cosine": c, "sharedConcepts": r.get("sharedConcepts"),
                    "predRole": r.get("predRole"), "valueRole": r.get("valueRole"),
                    "a": {"name": r["a"]["name"], "area": r["a"]["area"],
                          "head": ra, "valueHead": r["a"].get("valueHead")},
                    "b": {"name": r["b"]["name"], "area": r["b"]["area"],
                          "head": rb, "valueHead": r["b"].get("valueHead")},
                    "sharedTokens": r.get("sharedRoleTokens", [])})
    residual.sort(key=lambda z: -z["cosine"])
    with open(OUT, "wb") as o:
        for rec in residual:
            o.write((json.dumps(rec, ensure_ascii=False) + "\n").encode("utf-8"))
    # group residual by head-pair for quick reading
    hc = collections.Counter(
        tuple(sorted((x["a"]["head"], x["b"]["head"]))) for x in residual)
    summary = {"looseTotal": len(loose), "tightTotal": len(tight),
               "weakBandTotal": n_weak, "weakByFamily": dict(fam_counter),
               "secondStageOfUnresolved": dict(weak_counter),
               "novelResidual": len(residual),
               "residualHeadPairs": [{"heads": list(k), "count": c}
                                     for k, c in hc.most_common()]}
    with open(SUM, "w", encoding="utf-8") as o:
        json.dump(summary, o, ensure_ascii=False, indent=2)
    print(f"loose {len(loose)}  tight {len(tight)}  weak-band {n_weak}")
    print("weak-band first-stage (ledger-31) breakdown:")
    for k, v in fam_counter.most_common():
        print(f"  {k:<15}{v}")
    print("second-stage breakdown of the unresolved:")
    for k, v in weak_counter.most_common():
        print(f"  {k:<20}{v}")
    print(f"NOVEL irreducible residual (wb_noise): {len(residual)}")
    for x in residual[:60]:
        print(f"  {x['cosine']:.3f} {x['a']['area']}.{x['a']['head']} <-> "
              f"{x['b']['area']}.{x['b']['head']} | {x['a']['name']} <-> "
              f"{x['b']['name']}")


if __name__ == "__main__":
    main()
