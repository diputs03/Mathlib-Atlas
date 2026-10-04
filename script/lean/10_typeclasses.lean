import Mathlib

/-!
# 10 — Typeclass / instance structure

Builds two small reference registries from the environment's own typeclass
extensions (NOT inferred from names):

* `data/atlas_classes.jsonl`   — every typeclass: direct superclasses
  (`extends` parents, via structure info), fields, out-parameter positions and
  how many instances implement it; PLUS `abbrev` class aliases (e.g.
  `DecidableEq` is an abbrev for `Decidable`, `FunLike` for `DFunLike`) with an
  `aliasOf` pointer to the canonical class;
* `data/atlas_instances.jsonl` — every registered `@[instance]`: the canonical
  class it implements (`className`, resolving abbrev aliases), the raw head
  name when it was an alias (`classAlias`), the type constructor its head
  argument targets (best-effort), priority and attribute kind.

These are *reference layers* spanning core / Std / Mathlib, so all classes and
instances are emitted; each row carries its source `module` and a `mathlib`
flag.

API (verified against Lean 4.34.0-rc2 core):
* classes : `(Lean.classExtension.getState env).outParamMap`, `Lean.isClass`;
* parents/fields : `Lean.getStructureInfo? env n`;
* instances : `(Meta.instanceExtension.getState env).instanceNames`;
* aliases : a `defnInfo` with `hints = .abbrev` whose value (after peeling
  binders) has a class constant as its head, followed to a fixed point.

Run (Windows, no WSL) from the repository root:
    lake env lean script\lean\10_typeclasses.lean
-/

open Lean
open Lean.Elab
open Lean.Elab.Command

def atlasClassesPath : String := "data/atlas_classes.jsonl"
def atlasInstancesPath : String := "data/atlas_instances.jsonl"
def atlasLimit : Option Nat := .none
/-- Max abbrev→abbrev hops when resolving a class alias. -/
def atlasAliasMaxHops : Nat := 8

def atlasModuleOf (env : Environment) (name : Name) : Option Name := do
  let idx ← env.getModuleIdxFor? name
  env.header.moduleNames[idx.toNat]?

/-- Peel outer binders (forall / lambda / let), returning the body. -/
partial def peelBinders : Expr → Expr
  | .forallE _ _ b _ => peelBinders b
  | .lam _ _ b _    => peelBinders b
  | .letE _ _ _ b _ => peelBinders b
  | e              => e

/-- Head constant of an application spine (skip metadata). -/
def headConstName : Expr → Option Name
  | .const n _ => some n
  | .app f _   => headConstName f
  | .mdata _ e => headConstName e
  | _          => none

def attrKindStr : AttributeKind → String
  | .global => "global"
  | .scoped => "scoped"
  | .local  => "local"

/-- Is this constant an `abbrev`? -/
def abbrevValueHead? (env : Environment) (n : Name) : Option Name := do
  let ci ← env.find? n
  match ci with
  | .defnInfo v =>
      match v.hints with
      | .abbrev => headConstName (peelBinders v.value)
      | _ => none
  | _ => none

/-- Resolve a possibly-abbreviated class name to the canonical registered
    class (fixed point, bounded); returns the start if it cannot resolve. -/
partial def resolveClass (env : Environment) (start : Name) : Name :=
  let rec go (cur : Name) (hops : Nat) : Name :=
    if Lean.isClass env cur then cur
    else if hops = 0 then cur
    else match abbrevValueHead? env cur with
      | some h => go h (hops - 1)
      | none   => cur
  go start atlasAliasMaxHops

elab "atlasTypeclasses" : command => do
  let env ← getEnv
  let hCls ← IO.FS.Handle.mk atlasClassesPath IO.FS.Mode.write
  let hInst ← IO.FS.Handle.mk atlasInstancesPath IO.FS.Mode.write

  ---------------------------------------------------------------------------
  -- Pass 1: instances (resolving abbrev aliases to canonical classes).
  ---------------------------------------------------------------------------
  let instState := Meta.instanceExtension.getState env
  let instList := instState.instanceNames.toList

  let mut instWritten : Nat := 0
  let mut instMathlib : Nat := 0
  let mut noClassName : Nat := 0
  let mut viaAlias : Nat := 0
  let mut perClass : Std.HashMap Name Nat := {}
  let mut perAlias : Std.HashMap Name Nat := {}

  for (instName, entry) in instList do
    let underCap : Bool :=
      match atlasLimit with
      | some lim => instWritten < lim
      | none     => true
    if !underCap then break else pure ()

    let mod? := atlasModuleOf env instName
    let isMathlib : Bool :=
      match mod? with
      | some m => m.toString.startsWith "Mathlib"
      | none   => false
    if isMathlib then instMathlib := instMathlib + 1 else pure ()

    let mut classNameJson : Json := Json.null
    let mut aliasJson : Json := Json.null
    let mut targetHeadJson : Json := Json.null
    match env.find? instName with
    | some ci =>
        let rawHead? := headConstName (peelBinders ci.type)
        match rawHead? with
        | some raw =>
            let resolved := resolveClass env raw
            if Lean.isClass env resolved then
              classNameJson := Json.str resolved.toString
              perClass := perClass.insert resolved (perClass.getD resolved 0 + 1)
              if resolved != raw then
                aliasJson := Json.str raw.toString
                viaAlias := viaAlias + 1
                perAlias := perAlias.insert raw (perAlias.getD raw 0 + 1)
              else pure ()
              -- type constructor the class is instantiated on (first arg)
              let concl := peelBinders ci.type
              let args := concl.getAppArgs
              if 0 < args.size then
                match headConstName args[0]! with
                | some th => targetHeadJson := Json.str th.toString
                | none    => pure ()
              else pure ()
            else noClassName := noClassName + 1
        | none => noClassName := noClassName + 1
    | none => noClassName := noClassName + 1

    let moduleJson : Json :=
      match mod? with
      | some m => Json.str m.toString
      | none   => Json.null

    let row := Json.mkObj [
      ("name", Json.str instName.toString),
      ("module", moduleJson),
      ("mathlib", toJson isMathlib),
      ("className", classNameJson),
      ("classAlias", aliasJson),
      ("targetHead", targetHeadJson),
      ("priority", toJson entry.priority),
      ("attrKind", Json.str (attrKindStr entry.attrKind))
    ]
    hInst.putStrLn row.compress
    instWritten := instWritten + 1
  hInst.flush

  ---------------------------------------------------------------------------
  -- Pass 2a: registered classes.
  ---------------------------------------------------------------------------
  let classList := (Lean.classExtension.getState env).outParamMap.toList
  let mut clsWritten : Nat := 0
  let mut clsMathlib : Nat := 0
  let mut clsWithParents : Nat := 0

  for (clsName, outParams) in classList do
    let mod? := atlasModuleOf env clsName
    let isMathlib : Bool :=
      match mod? with
      | some m => m.toString.startsWith "Mathlib"
      | none   => false
    if isMathlib then clsMathlib := clsMathlib + 1 else pure ()

    let mut fieldArr : Array Json := #[]
    let mut parentArr : Array Json := #[]
    let mut hasStructure : Bool := false
    match Lean.getStructureInfo? env clsName with
    | some si =>
        hasStructure := true
        for fn in si.fieldNames do
          fieldArr := fieldArr.push (Json.str fn.toString)
        if 0 < si.parentInfo.size then clsWithParents := clsWithParents + 1 else pure ()
        for p in si.parentInfo do
          parentArr := parentArr.push <| Json.mkObj [
            ("name", Json.str p.structName.toString),
            ("subobject", toJson p.subobject),
            ("projFn", Json.str p.projFn.toString)]
    | none => pure ()

    let mut outArr : Array Json := #[]
    for pos in outParams do outArr := outArr.push (toJson pos)
    let moduleJson : Json :=
      match mod? with
      | some m => Json.str m.toString
      | none   => Json.null

    let row := Json.mkObj [
      ("name", Json.str clsName.toString),
      ("module", moduleJson),
      ("mathlib", toJson isMathlib),
      ("isAlias", toJson false),
      ("aliasOf", Json.null),
      ("hasStructure", toJson hasStructure),
      ("outParams", Json.arr outArr),
      ("fields", Json.arr fieldArr),
      ("parents", Json.arr parentArr),
      ("nInstances", toJson (perClass.getD clsName 0))
    ]
    hCls.putStrLn row.compress
    clsWritten := clsWritten + 1

  ---------------------------------------------------------------------------
  -- Pass 2b: abbrev class aliases (name resolves to a registered class).
  ---------------------------------------------------------------------------
  let mut aliasWritten : Nat := 0
  for (name, ci) in env.constants.toList do
    match ci with
    | .defnInfo v =>
        match v.hints with
        | .abbrev =>
            let resolved := resolveClass env name
            if Lean.isClass env resolved && resolved != name then
              let mod? := atlasModuleOf env name
              let moduleJson : Json :=
                match mod? with
                | some m => Json.str m.toString
                | none   => Json.null
              let isMathlib : Bool :=
                match mod? with
                | some m => m.toString.startsWith "Mathlib"
                | none   => false
              let row := Json.mkObj [
                ("name", Json.str name.toString),
                ("module", moduleJson),
                ("mathlib", toJson isMathlib),
                ("isAlias", toJson true),
                ("aliasOf", Json.str resolved.toString),
                ("hasStructure", toJson false),
                ("outParams", Json.arr #[]),
                ("fields", Json.arr #[]),
                ("parents", Json.arr #[]),
                ("nInstances", toJson (perAlias.getD name 0))
              ]
              hCls.putStrLn row.compress
              aliasWritten := aliasWritten + 1
            else pure ()
        | _ => pure ()
    | _ => pure ()
  hCls.flush

  logInfo m!"Registered classes:     {clsWritten} (Mathlib {clsMathlib})"
  logInfo m!"Classes with parents:   {clsWithParents}"
  logInfo m!"Abbrev class aliases:    {aliasWritten}"
  logInfo m!"Instances total:         {instWritten} (Mathlib {instMathlib})"
  logInfo m!"Instances via alias:     {viaAlias}"
  logInfo m!"Instances w/o class:     {noClassName}"
  logInfo m!"Classes output: {atlasClassesPath}"
  logInfo m!"Instances output: {atlasInstancesPath}"

atlasTypeclasses
