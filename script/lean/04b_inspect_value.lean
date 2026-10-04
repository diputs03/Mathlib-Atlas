import Mathlib

open Lean
open Lean.Elab
open Lean.Elab.Command

elab "atlasValue " declName:ident : command => do
  let env ← getEnv
  let name := declName.getId

  match env.find? name with
  | none =>
      logInfo m!"Declaration not found: {name}"

  | some info =>
      logInfo m!"Name: {name}"
      match info with
      | .axiomInfo val =>
          logInfo m!"Kind: axiom"
          logInfo m!"Type: {val.type}"

      | .defnInfo val =>
          logInfo m!"Kind: definition"
          logInfo m!"Type: {val.type}"
          logInfo m!"Value: {val.value}"

      | .opaqueInfo val =>
          logInfo m!"Kind: opaque"
          logInfo m!"Type: {val.type}"
          logInfo m!"Value: {val.value}"

      | .thmInfo val =>
          logInfo m!"Kind: theorem"
          logInfo m!"Type: {val.type}"
          logInfo m!"Value: {val.value}"

      | .quotInfo val =>
          logInfo m!"Kind: quotient"
          logInfo m!"Type: {val.type}"

      | .inductInfo val =>
          logInfo m!"Kind: inductive"
          logInfo m!"Type: {val.type}"

      | .ctorInfo val =>
          logInfo m!"Kind: constructor"
          logInfo m!"Type: {val.type}"

      | .recInfo val =>
          logInfo m!"Kind: recursor"
          logInfo m!"Type: {val.type}"

atlasValue Nat.one_mem_properDivisors_iff_one_lt
