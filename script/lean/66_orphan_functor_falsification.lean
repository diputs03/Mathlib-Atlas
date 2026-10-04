/-
Copyright (c 2026). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mathlib Atlas

# 66 — Orphan-functor falsification (downstream experiment; Mathlib untouched)

Script 64's structural channel flagged six type constructors that carry a
hand-written unary lift `map : (α → β) → F α → F β` (and, for several, a
binary lift `map₂`) but have no registered `Functor` instance:

  Sym2, WithBot, WithTop, OnePoint, Stream', Cycle.

This file *falsifies* the detector's claim the hard way: for each candidate it
registers a `Functor` instance using the existing lift and a `LawfulFunctor`
instance. Every candidate is in its own section so that a genuine blocker
(universe mismatch, missing law, instance diamond) can be read off directly.
A candidate is a CLEAN OMISSION only if both instances compile with no
elaboration tricks; otherwise it is recorded as a false positive of the
detector in `notes/66_orphan_functor_case_study.md`.

Acceptance: `lake env lean script/lean/66_orphan_functor_falsification.lean`
exits 0 with an empty compile log.
-/

import Mathlib

/-! ## 1. `Sym2` — unordered pairs -/

instance : Functor Sym2 where
  map := Sym2.map

instance : LawfulFunctor Sym2 where
  map_const := rfl
  id_map x := congrFun Sym2.map_id x
  comp_map h g x := by
    show Sym2.map (g ∘ h) x = Sym2.map g (Sym2.map h x)
    rw [Sym2.map_comp (f := h) (g := g)]
    simp only [Function.comp_apply]

/-! ## 2. `WithBot` — `Option` with a bottom element -/

instance : Functor WithBot where
  map := WithBot.map

instance : LawfulFunctor WithBot where
  map_const := rfl
  id_map x := congrFun WithBot.map_id x
  comp_map h g x := (WithBot.map_map g h x).symm

/-! ## 3. `WithTop` — `Option` with a top element -/

instance : Functor WithTop where
  map := WithTop.map

instance : LawfulFunctor WithTop where
  map_const := rfl
  id_map x := congrFun WithTop.map_id x
  comp_map h g x := (WithTop.map_map g h x).symm

/-! ## 4. `OnePoint` — one-point compactification carrier -/

instance : Functor OnePoint where
  map := OnePoint.map

instance : LawfulFunctor OnePoint where
  map_const := rfl
  id_map x := congrFun OnePoint.map_id x
  comp_map h g x := by
    show OnePoint.map (g ∘ h) x = OnePoint.map g (OnePoint.map h x)
    rw [OnePoint.map_comp (g := h) (f := g)]
    simp only [Function.comp_apply]

/-! ## 5. `Stream'` — infinite sequences (`ℕ → α`) -/

instance : Functor Stream' where
  map := Stream'.map

instance : LawfulFunctor Stream' where
  map_const := rfl
  id_map x := Stream'.map_id x
  comp_map h g x := (Stream'.map_map g h x).symm

/-! ## 6. `Cycle` — lists modulo cyclic permutation

`Cycle.map` exists in Mathlib but the functor laws were never proved. They are
established here directly from the quotient and `List` functor laws. -/

instance : Functor Cycle where
  map := Cycle.map

instance : LawfulFunctor Cycle where
  map_const := rfl
  id_map x := by
    induction x using Quotient.inductionOn'
    show Cycle.map id _ = _
    rw [Cycle.mk''_eq_coe, Cycle.map_coe, List.map_id]
  comp_map h g x := by
    induction x using Quotient.inductionOn'
    show Cycle.map (g ∘ h) _ = Cycle.map g (Cycle.map h _)
    rw [Cycle.mk''_eq_coe, Cycle.map_coe]
    simp only [Cycle.map_coe, List.map_map]

/-! ## Sanity checks: the instances synthesize and behave -/

example (f : α → β) (s : Sym2 α) : f <$> s = Sym2.map f s := rfl
example (f : α → β) (s : Cycle α) : f <$> s = Cycle.map f s := rfl
example (f : α → β) (s : Stream' α) : f <$> s = Stream'.map f s := rfl
