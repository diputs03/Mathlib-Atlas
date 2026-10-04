# Script 26 — triage of the `pointwise_repeated` cross-area communities

## Inputs / outputs

- Inputs: `data/community_triage.jsonl` (the 11 rows with status
  `pointwise_repeated` from script 19) joined to `data/atlas_features.jsonl`.
- Script: `script/python/26_pointwise_repeated.py` (stdlib only, deterministic).
- Verifier: `script/python/verify_pointwise_repeated.py` → **VERIFICATION OK**.
- Outputs: `data/pointwise_repeated_triage.jsonl` (11 rows),
  `data/pointwise_repeated_summary.json`.

## Discriminator: the shared value head

Each family shares a conclusion head (that is why it clustered). The decisive
extra signal is the **head constant of the elaborated proof/value**
(`valueHead`): it reveals whether the members already invoke one common generic
lemma/constructor or merely share a logical proof shape.

| class | criterion | meaning |
|---|---|---|
| `shared_generic_core` | all members delegate to the same domain lemma/constructor as value head | common argument already exists and is used; no opportunity |
| `generic_type_construction` | definitions building one generic target type via `.mk`/`.of`/coercion | legitimate adapters, no duplicated logic |
| `shared_strategy_only` | shared value head is a pure logical combinator (`And.intro`/`Iff.mp`) | only the proof skeleton is shared; inspected by hand |

## Result: 6 / 3 / 2, zero open opportunities

### shared_generic_core (6) — already factored
| family | shared generic core |
|---|---|
| dependsOn_restrict | `Set.dependsOn_domRestrict` (Set is the primitive; Finset/Preorder reduce to it) |
| isMulCommutative_closure | `IsMulCommutative.of_setLike_mul_comm` (generic SetLike lemma) |
| isTerminalPUnit | `CategoryTheory.Limits.IsTerminal.ofUnique` |
| covBy_insert | `WCovBy.covBy_of_lt` |
| isBasis_gen | `Filter.IsBasis.mk` (UniformFun/UniformOnFun build a Filter basis) |
| lt_wf | `Subrelation.wf` |

The large node counts (e.g. isBasis_gen up to 4,739) are carrier-specific
verification fed into a single generic builder — exactly the desired design.

### generic_type_construction (3) — by design
- toGlueData (cosine 1.0, 4-node defs): each domain `GlueData` → the generic
  `CategoryTheory.GlueData`;
- encoding: each syntax type builds a `Computability.Encoding` via `Encoding.mk`;
- residueField: each AG context builds a `CommRingCat` via `CommRingCat.of`.

### shared_strategy_only (2) — source-cleared, nothing to extract
- **subsingleton family**: `Set.Pairwise.subsingleton` is itself an alias of
  the generic `pairwise_bot_iff` (Data/Set/Pairwise/Basic.lean:197); the
  Equiv.Perm / SimpleGraph members prove `Set.Subsingleton` for bespoke
  pairwise-like predicates with carrier-specific membership arguments.
- **isAtom_singleton family**: each proves `IsAtom` with `And.intro` of
  carrier-specific lattice facts (Set uses `singleton_ne_empty` +
  `ssubset_singleton_iff`, Order/Atoms.lean:1291); Finset and Ultrafilter are
  different lattices, so only the two-conjunct skeleton is common.

## Conclusion

The `pointwise_repeated` bucket contains **no unexploited abstraction**: 6
families already call a single generic core, 3 are legitimate constructions of
a shared generic type, and the 2 remaining share only a logical skeleton over
genuinely different structures. This matches cases B and D (FunLike Is*Apply and
Equivalence witnesses): most cross-area multiplicity in Mathlib is either
already abstracted or mathematically irreducible. The one positive construction
this arc produced remains case E (the Set/Filter `PointwiseLift` ladder,
scripts 23–25).
