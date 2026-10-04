import Mathlib

open Lean
open Lean.Elab
open Lean.Elab.Command

def atlasConstantKind : ConstantInfo → String
  | .axiomInfo _   => "axiom"
  | .defnInfo _    => "definition"
  | .opaqueInfo _  => "opaque"
  | .thmInfo _     => "theorem"
  | .quotInfo _    => "quotient"
  | .inductInfo _  => "inductive"
  | _              => "other"

elab "atlasInspect " name:ident : command => do
  let env ← getEnv
  match env.find? name.getId with
  | some info =>
      logInfo m!"Name: {name.getId}"
      logInfo m!"Kind: {atlasConstantKind info}"
      logInfo m!"Type: {info.type}"
  | none =>
      logInfo m!"Declaration not found: {name.getId}"

atlasInspect Nat.one_mem_properDivisors_iff_one_lt
