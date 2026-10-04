/-
35_instance_gap_check.lean — kernel check of script-34's 20 peer-relative gap rules.

Script 34 flagged concrete carriers that instantiate a strong class C but do not
redeclare a *cross* parent P (subobject=false) that most peers declare. The
question is whether P is genuinely missing (a synthesis failure) or is supplied
POLYMORPHICALLY by the structure projection `C.toP` (so no concrete instance is
needed). For each rule we assume only `[C α]` and build `P α` by `inferInstance`;
success proves the parent is always available and the "gap" is a redundant-
instance style difference, not a missing instance.
-/
import Mathlib

-- Each line compiles iff the parent synthesizes from the strong class alone.
example (α : Type*) [CommGroup α] : CommMonoid α := inferInstance
example (α : Type*) [CommMonoidWithZero α] : MonoidWithZero α := inferInstance
example (α : Type*) [AddGroupWithOne α] : AddGroup α := inferInstance
example (α : Type*) [CancelCommMonoid α] : LeftCancelMonoid α := inferInstance
example (α : Type*) [NonUnitalNonAssocRing α] :
    NonUnitalNonAssocSemiring α := inferInstance
example (α : Type*) [NonUnitalRing α] : NonUnitalSemiring α := inferInstance
example (α : Type*) [SemigroupWithZero α] : MulZeroClass α := inferInstance
example (α : Type*) [MulZeroOneClass α] : MulZeroClass α := inferInstance
example (α : Type*) [AddCommGroupWithOne α] : AddCommMonoidWithOne α := inferInstance
example (α : Type*) [AddCancelMonoid α] : AddRightCancelMonoid α := inferInstance
example (α : Type*) [NonUnitalNormedCommRing α] : NonUnitalCommRing α := inferInstance
example (α : Type*) [CancelMonoid α] : RightCancelMonoid α := inferInstance
example (α : Type*) [NonUnitalSeminormedCommRing α] : NonUnitalCommRing α := inferInstance
example (α : Type*) [CompleteBooleanAlgebra α] : BooleanAlgebra α := inferInstance
example (α : Type*) [DivisionCommMonoid α] : CommMonoid α := inferInstance
example (α : Type*) [LeftCancelMonoid α] : LeftCancelSemigroup α := inferInstance
example (α : Type*) [RightCancelMonoid α] : RightCancelSemigroup α := inferInstance
example (α : Type*) [CommCStarAlgebra α] : CStarAlgebra α := inferInstance
example (α : Type*) [NonUnitalNonAssocCommSemiring α] : CommMagma α := inferInstance
example (α : Type*) [BiheytingAlgebra α] : CoheytingAlgebra α := inferInstance

-- Show WHICH projection closes the strongest example (CommGroup -> CommMonoid).
#synth CommMonoid ℤ

#eval ()
