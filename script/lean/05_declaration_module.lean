import Mathlib

open Lean
open Lean.Elab
open Lean.Elab.Command

elab "atlasModule " declName:ident : command => do
  let env ← getEnv
  let name := declName.getId

  match env.find? name with
  | none =>
      logInfo m!"Declaration not found: {name}"

  | some info =>
      logInfo m!"Declaration: {name}"
      logInfo m!"Type: {info.type}"

      match env.getModuleIdxFor? name with
      | some moduleIdx =>
          let moduleName := env.header.moduleNames[moduleIdx.toNat]?
          logInfo m!"Module index: {moduleIdx}"
          logInfo m!"Module: {moduleName}"

      | none =>
          logInfo m!"No module information found."

atlasModule Nat.one_mem_properDivisors_iff_one_lt
