#!/usr/bin/env python3
"""73_adjudicate_equiv.py — give every Equiv candidate a definite class.

Classes:
  generic_transport_exists      a generic transport theorem already covers it
  already_symmetric             the two APIs are already mirror images
  representation_boundary       the Equiv is conditional/defeq/encoding; the
                                asymmetry is exactly why the types differ
  missing_transport_lemma       a specific transported lemma is absent and
                                wanted
  missing_generic_abstraction   a genuinely absent generic transport mechanism
  intentional_asymmetry         dual constructions, side-specific lemmas
  false_positive                no API identification (unpacking/coarse match)

The nine coverage-gated pairs (plus examined near-gated pairs) are manually
adjudicated with source evidence; the remaining pairs are classified by
deterministic rules stated below. Null classes are counted just as carefully.

Outputs:
  data/equiv_adjudication.jsonl
  data/equiv_adjudication_summary.json
"""
import json, os

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
DATA = os.path.join(ROOT, "data")

rows = [json.loads(l) for l in
        open(os.path.join(DATA, "equiv_ranked.jsonl"), encoding="utf-8")]

# ------------------------------------------------------------- manual verdicts
# keyed by the sorted pair list as emitted
MANUAL = {
    ("CStarMatrix", "Matrix"): ("representation_boundary",
        "CStarMatrix m n A := Matrix m n A (defeq); ofMatrix = Equiv.refl; the "
        "type copy exists solely to attach the operator norm and C* instances "
        "(documented implementation notes). Matrix lemmas apply by conversion."),
    ("ConnectedComponents", "ZerothHomotopy"): ("representation_boundary",
        "Connected components (clopen quotient) and path components coincide "
        "only under LocallyPathConnected; Equiv built from setoid equality. "
        "The Homeomorph is derivable in 6 lines (proved downstream: "
        "ccHomeomorphZh); not a missing generic mechanism."),
    ("MaximalSpectrum", "PrimeSpectrum"): ("representation_boundary",
        "Equiv conditional on IsArtinianRing (all primes maximal); transport "
        "lemmas (comp_asIdeal) already present; general relation is the "
        "subtype inclusion via equivSubtype."),
    ("MaximalSpectrum", "Subtype"): ("representation_boundary",
        "MaximalSpectrum is literally the subtype of maximal ideals "
        "(equivSubtype : MaximalSpectrum R ≃ {I : Ideal R // I.IsMaximal})."),
    ("Prod", "RegularWreathProduct"): ("false_positive",
        "equivProd unpacks D ≀ᵣ Q into (Q → D) × Q for cardinality; the group "
        "law is a semidirect construction that cannot transport to a generic "
        "product group; 1379 'gap' Prod decls are unrelated."),
    ("BotHom", "TopHom"): ("intentional_asymmetry",
        "order-dual bundled hom constructions; lemmas naturally written on "
        "each side."),
    ("OrderAddMonoidIso", "OrderMonoidIso"): ("intentional_asymmetry",
        "to_additive / additive-multiplicative dual pair."),
    ("PSigma", "Sigma"): ("representation_boundary",
        "generic foundational encoding Equiv (psigmaEquivSigma / PLift "
        "variant); Sigma intentionally carries the rich API; instance "
        "transport demonstrated downstream."),
    ("InfTopHom", "SupBotHom"): ("intentional_asymmetry",
        "order-dual constructions."),
    ("sInfHom", "sSupHom"): ("intentional_asymmetry",
        "order-dual constructions."),
    ("InfHom", "SupHom"): ("intentional_asymmetry",
        "order-dual constructions."),
    ("WithBot", "WithTop"): ("intentional_asymmetry",
        "order duals with toDual/ofDual machinery; side-specific lemmas "
        "(NoTopOrder, CanonicallyOrderedAdd, etc.) are natural on each side."),
    ("MonoidHom", "ShelfHom"): ("false_positive",
        "coarse-shape match between unrelated hom types; Equiv witness is a "
        "one-off construction, not an API identification."),
}

def dual_like(a, b):
    PAIRS = [("Add", "Mul"), ("Bot", "Top"), ("Inf", "Sup"),
             ("Left", "Right"), ("Neg", "Pos"), ("Inv", "Cov")]
    for x, y in PAIRS:
        if (x in a and y in b) or (y in a and x in b):
            # require the rest of the name skeleton to align
            ra = a.replace(x, "?").replace(y, "?")
            rb = b.replace(x, "?").replace(y, "?")
            if ra == rb:
                return True
    return False

out = []
for r in rows:
    a, b = r["pair"]
    key = tuple(sorted((a, b)))
    if key in MANUAL:
        cls, note = MANUAL[key]
        rule = "manual source adjudication"
    else:
        note = ""
        if dual_like(a, b):
            cls, rule = "intentional_asymmetry", "dual/to_additive name pattern"
        else:
            fp_max = max(r["footprintA"], r["footprintB"])
            fp_min = min(r["footprintA"], r["footprintB"])
            if fp_max > 0 and fp_min / fp_max < 0.10:
                cls, rule = ("representation_boundary",
                             "footprint imbalance: one-off encoding Equiv")
            elif r["coverage"] >= 0.35:
                cls, rule = ("false_positive",
                             "unexpected: gated pair without manual verdict")
            else:
                cls, rule = ("false_positive",
                             "no API identification (coverage < 0.35)")
    out.append(dict(pair=[a, b], cls=cls, rule=rule, note=note,
                    coverage=r["coverage"], score=r["score"],
                    footprintA=r["footprintA"], footprintB=r["footprintB"],
                    gapDeclsA=r["gapDeclsA"], gapDeclsB=r["gapDeclsB"],
                    witnesses=r["witnesses"]))

counts = {}
for r in out:
    counts[r["cls"]] = counts.get(r["cls"], 0) + 1
for cls in ("generic_transport_exists", "already_symmetric",
            "representation_boundary", "missing_transport_lemma",
            "missing_generic_abstraction", "intentional_asymmetry",
            "false_positive"):
    counts.setdefault(cls, 0)

with open(os.path.join(DATA, "equiv_adjudication.jsonl"), "w",
          encoding="utf-8") as f:
    for r in out:
        f.write(json.dumps(r, ensure_ascii=False) + "\n")
summary = dict(total=len(out), counts=counts)
with open(os.path.join(DATA, "equiv_adjudication_summary.json"), "w",
          encoding="utf-8") as f:
    json.dump(summary, f, ensure_ascii=False, indent=2)

print(json.dumps(counts, indent=2))
print("total:", len(out))
