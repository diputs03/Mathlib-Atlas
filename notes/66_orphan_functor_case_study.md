# 66 — Orphan-functor falsification: a case study in detection → verification

Date: 2026-09-23
Experiment: `script/lean/66_orphan_functor_falsification.lean`
(EXIT=0, compile log 0 bytes, no `sorry`/`admit`)
Probe: `script/lean/66b_pi_functor_probe.lean` (fails to synthesize — result)
Detector: script 64 structural channel; design note `notes/64_stdlib_semantic_analogies_design.md`

## 1. The claim under test

Script 64's exact type-shape channel found six type constructors with a
hand-written unary lift `map : (α → β) → F α → F β` but no registered
`Functor F`: **Sym2, WithBot, WithTop, OnePoint, Stream', Cycle**. A
detector's output is a *hypothesis*. This case study records the falsification
protocol, the verdict per candidate, and — equally important — the false
positives, which are the training signal for what Atlas must not abstract.

## 2. Protocol (the "hard way", downstream only)

Nothing in `external/mathlib4` was touched. For each candidate the experiment
declares, in its own section:

1. `instance : Functor F where map := F.map` — tests that the existing lift's
   signature (implicit binders, universe levels, argument order) literally
   matches the core class.
2. `instance : LawfulFunctor F` — tests the identity and composition laws
   (`id_map`, `comp_map`, plus `map_const`), using source lemmas when present
   and proving them from scratch when not.
3. Definitional sanity examples: `f <$> s = F.map f s` by `rfl`.

A candidate is a **clean omission** only if both instances compile with no
elaboration tricks and no blocker (existing instance, universe mismatch,
missing law, active diamond).

Toolchain note learned during the campaign: in Lean 4.34 core,
`LawfulFunctor`'s fields are `map_const`, `id_map`, `comp_map` (not the older
`map_id`/`map_comp`), and the binders of `comp_map` are ordered
`(h : α → β) (g : β → γ)` with goal `(g ∘ h) <$> x = g <$> h <$> x`.
`map_const := rfl` works whenever `mapConst` is not overridden.

## 3. Verdicts

| Candidate | Underlying definition | `Functor` | `LawfulFunctor` | Verdict |
|---|---|---|---|---|
| **Sym2** | `abbrev Sym2 α := Quot (Sym2.Rel α)` | ✓ `map := Sym2.map` | ✓ via existing `Sym2.map_id`, `Sym2.map_comp` | **clean omission** |
| **WithBot** | `def WithBot α := Option α` | ✓ `map := WithBot.map` | ✓ via existing `map_id`, `map_map` | **clean omission** |
| **WithTop** | `def WithTop α := Option α` | ✓ | ✓ via existing `map_id`, `map_map` | **clean omission** |
| **OnePoint** | `def OnePoint X := Option X` | ✓ | ✓ via existing `map_id`, `map_comp` | **clean omission** |
| **Stream'** | `def Stream' α := ℕ → α` | ✓ | ✓ via existing `map_id`, `map_map` | **clean omission** |
| **Cycle** | `def Cycle α := Quotient (IsRotated.setoid α)` | ✓ | ✓ **laws proved in the experiment** (`Quotient.inductionOn'` + `map_coe` + `List.map_id`/`map_map`) | **clean omission, slightly weaker** — the laws were not in source; they take six lines |

Corroborating probes:
- No `Functor (fun α => ℕ → α)` (reader functor) exists at this toolchain, so
  the Stream' instance has no Pi-type diamond.
- WithBot/WithTop/OnePoint are `def … := Option`, not `abbrev`. Instance
  search cannot see Option's `Functor` through a semireducible `def`, so no
  active diamond is created; and the branches are definitionally equal anyway
  (`map := Option.map`). Residual risk is only stylistic: an upstream reviewer
  may prefer these stay unregistered to avoid notation in order/topology files.
- OnePoint's topology concern (arbitrary functions are not continuous) is
  orthogonal: a data-level `Functor` asserts nothing about continuity; a
  continuous version belongs to `ContinuousMap`.

Net result: **6/6 detector claims survive falsification.** All six are
genuine, kernel-verified omissions of `Functor` (and, by extension, candidate
sites for future `Applicative` instances where `map₂` exists).

## 4. False positives — what Atlas must learn NOT to abstract

The detector surfaced or nearly surfaced several classes of candidates that
correctly must not become instances. These are the scientifically valuable
part of the campaign.

1. **Hypothesis-constrained lifts (rejected).**
   - `CompactCoherentification.map`: its lift requires a
     `CompactCoherentSpace`-style hypothesis and a compatibility argument;
       it is not a plain `(α → β) → F α → F β`.
   - `SummationFilter.map`: a subtype-restricted pushforward requiring the
     summation-filter compatibility hypothesis.
   Lesson for Atlas: a `map`-shaped constant is a functor candidate only when
   its type is exactly `{α β} → (α → β) → F α → F β` with **zero extra
   hypotheses**; any extra propositional argument classifies it out.
2. **Alias-of-integrated-type (conditional, not automatic).** WithBot,
   WithTop, OnePoint reduce to `Option`, which already has the full hierarchy.
   Registering again is safe here (semireducible `def`, equal branches) but is
   a judgment call, not an obvious omission. Atlas must tag every
   `def F := G` candidate as "alias of an already-integrated constructor" and
   require an explicit reason (notation, documentation) before flagging it.
3. **Quotient/newtype lifts with no proved laws (incomplete, not free).**
   Cycle had `map` but neither functor law. The claim "functorial" was not
   established until the laws were proved; a detector that treats the presence
   of `map` as proof of a missing `Functor` would over-claim. The required
   pipeline is `map exists → laws exist or are proved → instance`.
4. **Elaboration/notation lookalikes (pre-filtered).** `macroRules`
   auxiliaries, `termπ`/`termφ` syntax declarations, `_aux_`/`_eq` generated
   constants, and auto-generated `congr_simp` lemmas have shapes that mimic
   small definitions; they must be excluded before detection rather than
   adjudicated by hand each time.
5. **Same-theory duplicates (not cross-theory analogies).** Cross-module
   re-exports (`LinearMap` vs `ContinuousLinearMap` shared lemmas,
   `TensorProduct` vs `Algebra.TensorProduct`) and `to_additive` twins
   co-cluster strongly but are propagation/generation patterns, not missing
   abstractions. Atlas's namespace/area guards plus a same-stem rarity floor
   remove most of these; the remainder must be classified, not promoted.

## 5. What this changes in the Atlas model

- The structural channel's claim is now **adjudicated evidence**: exact
  type-shape blocking → source verification → downstream kernel-verified
  instances, with a documented precision ledger. The detection→verification
  process, not the instances themselves, is the reusable scientific artifact.
- A candidate must pass four gates before being called an omission:
  (a) no instance already present; (b) signature matches the class, including
  universe levels; (c) the class laws are present in source or proved;
  (d) no extra hypotheses or active diamond. Each failed gate becomes a named
  false-positive class (§4).
- The semantic-channel null result from script 64 stands: in the mature stdlib
  the missing-integration signal is structural; semantics teaches propagation
  and renaming patterns.

## 6. Disposition

- PR-shaped material for the six clean omissions is kept in
  `notes/66_pr_candidate.md`; it is separate from Atlas and is not submitted
  without an explicit decision.
- The map-family scan is frozen per `notes/66_scan_freeze.md`: no further
  hunting for `map`/`map₂` families.
- Next: return to discovery on a different phenomenon over the enlarged
  adjudicated dataset.
