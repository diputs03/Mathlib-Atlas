import Mathlib

open Lean
open Lean.Elab
open Lean.Elab.Command

elab "atlas_list_declarations" : command => do
  let env ← getEnv

  logInfo m!"Total declarations in environment: {env.constants.toList.length}"

  let mut count := 0

  for (name, info) in env.constants.toList do
    if count < 100 then
      logInfo m!"{name} :: {info.type}"
      count := count + 1

atlas_list_declarations
