/-
77_proof_skeletons_core.lean — scale proof-skeleton extraction to all ten
core areas in a SINGLE Mathlib load (single compile discipline).

Output: data/proof_skeletons_core.jsonl
Rows: {name, module, area, skeleton}
Acceptance: EXIT=0, zero-byte compile log.
Normalization identical to script 75; do not rename token classes.
-/
import Mathlib

open Lean

def atlasCap : Nat := 50000

def atlasCoreAreas : List String :=
  ["Algebra", "Analysis", "Data", "FieldTheory", "GroupTheory",
   "LinearAlgebra", "Logic", "Order", "RingTheory", "Topology"]

def atlasAreaOf (modName : Name) : Option String :=
  let s := modName.toString
  if !s.startsWith "Mathlib." then none else
    let rest := s.drop "Mathlib.".length
    let head := (rest.takeWhile (· != '.')).toString
    if atlasCoreAreas.contains head then some head else none

partial def atlasNodes (e : Expr) (n : Nat) : Nat :=
  if n > atlasCap then n else
    match e with
    | .app fn arg => atlasNodes arg (atlasNodes fn (n + 1))
    | .lam _ t body _ => atlasNodes body (atlasNodes t (n + 1))
    | .forallE _ t body _ => atlasNodes body (atlasNodes t (n + 1))
    | .letE _ t v body _ =>
        atlasNodes body (atlasNodes v (atlasNodes t (n + 1)))
    | .mdata _ body => atlasNodes body n
    | .proj _ _ body => atlasNodes body (n + 1)
    | _ => n + 1

partial def atlasSkel (e : Expr) (acc : Array String) : Array String :=
  match e with
  | .bvar _ => acc.push "B"
  | .fvar _ => acc.push "F"
  | .mvar _ => acc.push "M"
  | .sort _ => acc.push "T"
  | .lit v =>
      let c : Char := match v with | .natVal _ => 'n' | .strVal _ => 's'
      acc.push s!"L{c}"
  | .const name _ =>
      let s := name.toString
      let last := name.lastComponentAsString
      let tok :=
        if s.endsWith ".rec" || s.endsWith ".brec" || s.endsWith ".recOn"
           || s.endsWith ".casesOn" || s.endsWith ".below" then "REC"
        else if last.length > 2 && last.startsWith "to"
                && (((last.toList.drop 2).head?).getD ' ').isUpper then "TOPROJ"
        else if last.startsWith "inst"
                || (s.splitOn ".inst").length > 1 then "INST"
        else if s.startsWith "_private" then "PRIV"
        else s!"K{last}"
      acc.push tok
  | .app fn arg =>
      let acc := acc.push "(A"
      let acc := atlasSkel fn acc
      (atlasSkel arg acc).push ")"
  | .lam _ t body _ =>
      let acc := acc.push "(L"
      let acc := atlasSkel t acc
      (atlasSkel body acc).push ")"
  | .forallE _ t body _ =>
      let acc := acc.push "(Q"
      let acc := atlasSkel t acc
      (atlasSkel body acc).push ")"
  | .letE _ t v body _ =>
      let acc := acc.push "(E"
      let acc := atlasSkel t acc
      let acc := atlasSkel v acc
      (atlasSkel body acc).push ")"
  | .mdata _ body => atlasSkel body acc
  | .proj _ i body =>
      let acc := acc.push s!"(J{i}"
      (atlasSkel body acc).push ")"

elab "atlasProofSkeletonsCore" : command => do
  let env ← getEnv
  -- resume support: names already present in the output file
  let mut seen : Std.HashSet String := {}
  let hIn ← IO.FS.Handle.mk "data/proof_skeletons_core.jsonl" .read
  while true do
    let line ← hIn.getLine
    if line.isEmpty then break
    let line := line.trimAscii.toString
    if line.startsWith "{" then
      match Json.parse line with
      | .ok j =>
        match j.getObjVal? "name" with
        | .ok (Json.str n) => seen := seen.insert n
        | _ => pure ()
      | _ => pure ()
  let out ← IO.FS.Handle.mk "data/proof_skeletons_core.jsonl" .append
  let mut n : Nat := 0
  let mut kept : Nat := 0
  let mut skipped : Nat := 0
  let mut truncated : Nat := 0
  let mut perArea : Std.HashMap String Nat := {}
  for (name, info) in env.constants.toList do
    n := n + 1
    let some modIdx := env.getModuleIdxFor? name | continue
    let some modName := env.header.moduleNames[modIdx.toNat]? | continue
    let some area := atlasAreaOf modName | continue
    let .thmInfo val := info | continue
    if seen.contains name.toString then
      skipped := skipped + 1
      continue
    if atlasNodes val.value 0 > atlasCap then
      truncated := truncated + 1
      continue
    let toks := atlasSkel val.value #[]
    let skel := String.intercalate " " toks.toList
    let row := Json.mkObj [
      ("name", Json.str name.toString),
      ("module", Json.str modName.toString),
      ("area", Json.str area),
      ("skeleton", Json.str skel)]
    out.putStrLn (row.compress)
    kept := kept + 1
    perArea := perArea.insert area ((perArea.getD area 0) + 1)
    if kept % 2000 = 0 then out.flush
  out.flush
  IO.println s!"scanned {n}; new {kept}; resumed/skipped {skipped}; truncated {truncated}"
  for area in atlasCoreAreas do
    IO.println s!"  {area}: new {perArea.getD area 0}"

atlasProofSkeletonsCore
