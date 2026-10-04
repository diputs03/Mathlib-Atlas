/-
75_proof_skeletons_order.lean — proof-strategy pilot instrumentation.

Extracts proof/value skeletons for theorems of ONE mature area (Order) so we
can test whether different theorem statements share an underlying proof
strategy, without persisting all proof terms.

Skeleton normalization (vocabulary derived from the actual terms):
  bvar B, fvar F, mvar M, sort T, literal Ln/Ls
  constants classified:
    `.rec/.brec/.recOn/.casesOn/.below` -> REC       (induction / match)
    `toX` parent projections            -> TOPROJ
    `inst*` / `.inst*` instances        -> INST
    private/anonymous names             -> PRIV
    other named constants               -> K(short name)
  app (A ..), lam (L ..), forall (Q ..), let (E ..),
  projection (J idx ..); metadata dropped.

Output: data/proof_skeletons_order.jsonl
Acceptance: EXIT=0, zero-byte compile log.
-/
import Mathlib

open Lean

def atlasAreaPrefix : String := "Mathlib.Order"
def atlasCap : Nat := 50000

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

elab "atlasProofSkeletons" : command => do
  let env ← getEnv
  let out ← IO.FS.Handle.mk "data/proof_skeletons_order.jsonl" .write
  let mut n : Nat := 0
  let mut kept : Nat := 0
  let mut truncated : Nat := 0
  for (name, info) in env.constants.toList do
    n := n + 1
    let some modIdx := env.getModuleIdxFor? name | continue
    let some modName := env.header.moduleNames[modIdx.toNat]? | continue
    if !modName.toString.startsWith atlasAreaPrefix then continue
    let .thmInfo val := info | continue
    if atlasNodes val.value 0 > atlasCap then
      truncated := truncated + 1
      continue
    let toks := atlasSkel val.value #[]
    let skel := String.intercalate " " toks.toList
    let row := Json.mkObj [
      ("name", Json.str name.toString),
      ("module", Json.str modName.toString),
      ("skeleton", Json.str skel)]
    out.putStrLn (row.compress)
    kept := kept + 1
  IO.println s!"scanned {n}; kept {kept}; truncated {truncated}"

atlasProofSkeletons
