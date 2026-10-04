import Mathlib

/-!
# 12 — Structural declaration links (families, equation lemmas, aliases)

Scripts 08/09 record references found by walking expressions, and 10 records
class `extends`. Script 12 records the *structural* links the environment itself
encodes between declarations — links that are not just "B's term mentions A":

* inductive families : inductive → constructors (`constructor`), inductive →
  recursor (`recursor`), constructor → its inductive (`memberInductive`),
  recursor → inductive (`recursorOf`) and → rule constructors (`recursorRule`),
  mutual-block members (`mutualInductive`);
* structure layout   : structure → parent structures (`structExtends`, for ALL
  structures, not only classes) and → projection functions (`projection`);
* equation lemmas    : a definition → its generated `eq_1/eq_2/…` theorems
  (`equationLemma`) and its `eq_def`/`eq_unfold` unfolding lemma (`unfoldLemma`),
  resolved through Lean's pure inverse `declFromEqLikeName` (which also recovers
  private-mangled equation lemmas);
* aliases            : an `alias`/`export` name → its canonical declaration
  (`alias`), from `getAliasState`.

All links are direct, one-hop and labelled; no transitive closure is taken.

Output: `data/atlas_decl_links.jsonl`, one row
    {source, target, relation, detail, module, mathlib}
where module/mathlib describe the source declaration.

Run (Windows, no WSL) from the repository root:
    lake env lean script\lean\12_decl_links.lean
-/

open Lean
open Lean.Elab
open Lean.Elab.Command

def atlasLinksPath : String := "data/atlas_decl_links.jsonl"
def atlasLimit : Option Nat := .none

def atlasModuleOf (env : Environment) (name : Name) : Option Name := do
  let idx ← env.getModuleIdxFor? name
  env.header.moduleNames[idx.toNat]?

/-- Write one structural link row (top-level so it holds no mutable state). -/
def atlasWriteLink (h : IO.FS.Handle) (env : Environment)
    (source target : Name) (relation detail : String) : IO Unit := do
  let mod? := atlasModuleOf env source
  let isMathlib : Bool :=
    match mod? with
    | some m => m.toString.startsWith "Mathlib"
    | none   => false
  let moduleJson : Json :=
    match mod? with
    | some m => Json.str m.toString
    | none   => Json.null
  let detailJson : Json :=
    if detail.isEmpty then Json.null else Json.str detail
  let row := Json.mkObj [
    ("source", Json.str source.toString),
    ("target", Json.str target.toString),
    ("relation", Json.str relation),
    ("detail", detailJson),
    ("module", moduleJson),
    ("mathlib", toJson isMathlib)]
  h.putStrLn row.compress

elab "atlasDeclLinks" : command => do
  let env ← getEnv
  let h ← IO.FS.Handle.mk atlasLinksPath IO.FS.Mode.write

  let mut scanned : Nat := 0
  let emit (source target : Name) (relation detail : String) : CommandElabM Unit :=
    atlasWriteLink h env source target relation detail

  for (name, ci) in env.constants.toList do
    let underCap : Bool :=
      match atlasLimit with
      | some lim => scanned < lim
      | none     => true
    if !underCap then break else pure ()
    scanned := scanned + 1

    match ci with
    | .inductInfo v =>
        for c in v.ctors do emit name c "constructor" ""
        let recName := Name.str name "rec"
        if env.contains recName then emit name recName "recursor" "" else pure ()
        for other in v.all do
          if other != name then emit name other "mutualInductive" "" else pure ()
        match Lean.getStructureInfo? env name with
        | some si =>
            for p in si.parentInfo do
              emit name p.structName "structExtends" (if p.subobject then "subobject" else "")
            for f in si.fieldInfo do
              if env.contains f.projFn then
                emit name f.projFn "projection" f.fieldName.toString
              else pure ()
        | none => pure ()
    | .ctorInfo v =>
        emit name v.induct "memberInductive" (toString v.cidx)
    | .recInfo v =>
        for ind in v.all do emit name ind "recursorOf" ""
        for rule in v.rules do emit name rule.ctor "recursorRule" ""
    | _ => pure ()

    match Lean.Meta.declFromEqLikeName env name with
    | some (parent, suffix) =>
        if suffix == "eq_def" || suffix == "eq_unfold" then
          emit parent name "unfoldLemma" suffix
        else
          emit parent name "equationLemma" suffix
    | none => pure ()

  for (aliasName, canonicals) in (Lean.getAliasState env).toList do
    for canon in canonicals do emit aliasName canon "alias" ""

  h.flush
  logInfo m!"Constants scanned: {scanned}"
  logInfo m!"Output: {atlasLinksPath} (relation breakdown: verifier)"

atlasDeclLinks
