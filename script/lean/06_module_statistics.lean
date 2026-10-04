import Mathlib

open Lean
open Lean.Elab
open Lean.Elab.Command

elab "atlasModuleStats " : command => do
  let env ← getEnv

  let mut mathlibCount : Nat := 0
  let mut modules : Std.HashMap Name Nat := {}

  for (name, _) in env.constants.toList do
    match env.getModuleIdxFor? name with
    | some moduleIdx =>
        let moduleName := env.header.moduleNames[moduleIdx.toNat]?

        match moduleName with
        | some m =>
            let moduleString := m.toString

            if moduleString.startsWith "Mathlib" then
              mathlibCount := mathlibCount + 1

              let oldCount := modules.getD m 0
              modules := modules.insert m (oldCount + 1)

            else
              pure ()

        | none =>
            pure ()

    | none =>
        pure ()

  logInfo m!"Mathlib declarations: {mathlibCount}"
  logInfo m!"Distinct Mathlib modules: {modules.size}"

  logInfo m!"First 30 modules:"

  let mut shown : Nat := 0

  for (moduleName, count) in modules.toList do
    if shown < 30 then
      logInfo m!"{count}  {moduleName}"
      shown := shown + 1
    else
      pure ()

atlasModuleStats
