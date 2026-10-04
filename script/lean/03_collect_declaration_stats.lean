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

elab "atlasStats" : command => do
  let env ← getEnv

  let mut axioms : Nat := 0
  let mut definitions : Nat := 0
  let mut opaques : Nat := 0
  let mut theorems : Nat := 0
  let mut quotients : Nat := 0
  let mut inductives : Nat := 0
  let mut others : Nat := 0

  for (_, info) in env.constants.toList do
    match atlasConstantKind info with
    | "axiom"       => axioms := axioms + 1
    | "definition"  => definitions := definitions + 1
    | "opaque"      => opaques := opaques + 1
    | "theorem"     => theorems := theorems + 1
    | "quotient"    => quotients := quotients + 1
    | "inductive"   => inductives := inductives + 1
    | _             => others := others + 1

  logInfo m!"Total:       {env.constants.toList.length}"
  logInfo m!"Axioms:      {axioms}"
  logInfo m!"Definitions: {definitions}"
  logInfo m!"Opaques:     {opaques}"
  logInfo m!"Theorems:    {theorems}"
  logInfo m!"Quotients:   {quotients}"
  logInfo m!"Inductives:  {inductives}"
  logInfo m!"Other:       {others}"

atlasStats
