import Mathlib

-- Does the reader (Pi) functor exist, which could diamond against Stream'?
#synth Functor (fun α : Type => ℕ → α)
