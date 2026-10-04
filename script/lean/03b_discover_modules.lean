import Lean

open Lean

def main : IO Unit := do
  let moduleName : Name := `Mathlib.Algebra.Group.Basic

  let imports : Array Import :=
    #[{ module := moduleName }]

  let env ← Lean.importModules
    imports
    (opts := {})
    (trustLevel := 0)

  IO.println s!"Module: {moduleName}"
  IO.println s!"Declarations: {env.constants.toList.length}"
#eval main
