import Mathlib

/-!
# 09 — Richer Expr relationships

Script 08 records *that* a constant is referenced (type vs value, multiplicity).
Script 09 records the **structural role** of every reference, plus a compact
**type skeleton** per declaration.  It is a strictly finer decomposition of the
same `Expr.const` occurrences: for each `(source, target)` the four type-role
counts sum to 08's `typeCount`, and the four value-role counts sum to
`valueCount` (verified downstream against `atlas_edges.jsonl`).

## Role axes (two independent bits of context carried during traversal)

* `isHead` — the constant is at the HEAD of an application spine (the callee /
  predicate / operator), reached by following `.app.fn`; versus appearing inside
  an ARGUMENT subterm.  Head-of-conclusion is the relation/predicate a theorem
  establishes; head-of-proof-body is the lemma applied as a proof step.
* `inBinder` — the occurrence is inside the TYPE of a `forallE`/`lam` binder (a
  hypothesis / constraint), versus in the main conclusion/body reached after
  peeling binders.

The 2×2 roles per layer:

| role | in a TYPE means | in a VALUE/proof means |
|---|---|---|
| headMain | head constant of the conclusion (e.g. `Eq`, `Membership.mem`) | lemma/constructor applied as a proof step |
| argMain | mentioned in the conclusion term, not its head | passed as an argument |
| headBinder | head of a hypothesis type (e.g. `Group` in `[Group G]`) | head of a lambda-introduced hypothesis type |
| argBinder | nested inside a hypothesis type | nested in a lambda binder type |

## Type skeleton (`atlas_type_skeletons.jsonl`)

For each declaration's TYPE we peel only the OUTER `forallE` spine (the
declaration's own parameters/hypotheses), recording:
* `nPi` and counts of binders by `BinderInfo`
  (default / implicit / strictImplicit / instImplicit);
* `constraints`: head constant + multiplicity of every `instImplicit` binder —
  i.e. the typeclass constraints `[Foo ...]` the declaration assumes (this is
  the clean, attribute-free way to read required classes — from binders, not the
  instance attribute);
* `conclusionHead`: head constant of the conclusion after the outer binders.

Direct one-hop references only; same node-bounded traversal discipline as 08.

Run (Windows, no WSL) from the repository root:
    lake env lean script\lean\09_expr_relations.lean
-/

open Lean
open Lean.Elab
open Lean.Elab.Command

/-! ### Configuration -/

def atlasRelationsPath : String := "data/atlas_relations.jsonl"
def atlasSkeletonPath : String := "data/atlas_type_skeletons.jsonl"

def atlasMathlibOnlySources : Bool := true
def atlasLimit : Option Nat := .none
def atlasIncludeValue : Bool := true
/-- Max Expr nodes visited per expression (same envelope as 07/08). -/
def atlasNodeBudget : Nat := 50_000

/-! ### Classification / provenance -/

def atlasConstantKind : ConstantInfo → String
  | .axiomInfo _   => "axiom"
  | .defnInfo _    => "definition"
  | .opaqueInfo _  => "opaque"
  | .thmInfo _     => "theorem"
  | .quotInfo _    => "quotient"
  | .inductInfo _  => "inductive"
  | .ctorInfo _    => "constructor"
  | .recInfo _     => "recursor"

def atlasModuleOf (env : Environment) (name : Name) : Option Name := do
  let idx ← env.getModuleIdxFor? name
  env.header.moduleNames[idx.toNat]?

/-! ### Role counts and bounded role walker -/

structure RoleCounts where
  headMain : Nat := 0
  argMain : Nat := 0
  headBinder : Nat := 0
  argBinder : Nat := 0
  deriving Inhabited

def RoleCounts.bump (rc : RoleCounts) (isHead inBinder : Bool) : RoleCounts :=
  match isHead, inBinder with
  | true,  false => { rc with headMain := rc.headMain + 1 }
  | false, false => { rc with argMain := rc.argMain + 1 }
  | true,  true  => { rc with headBinder := rc.headBinder + 1 }
  | false, true  => { rc with argBinder := rc.argBinder + 1 }

/-- Returns `(target → RoleCounts, remaining budget, truncated)`.
    `isHead` follows the application function spine; `.app` arguments lose head
    status.  A `forallE`/`lam` binder type is traversed as its own head with
    `inBinder = true`, while the body keeps the outer context (so peeling the
    type's outer foralls carries head status through to the conclusion). -/
partial def walkRoles :
    Nat → Bool → Bool → Expr → Std.HashMap Name RoleCounts →
    Std.HashMap Name RoleCounts × Nat × Bool
  | 0, _, _, _, acc => (acc, 0, true)
  | budget+1, isHead, inBinder, e, acc =>
      match e with
      | .const n _ =>
          (acc.insert n ((acc.getD n {}).bump isHead inBinder), budget, false)
      | .bvar _ | .fvar _ | .mvar _ | .sort _ | .lit _ =>
          (acc, budget, false)
      | .mdata _ b => walkRoles budget isHead inBinder b acc
      | .proj _ _ b => walkRoles budget isHead inBinder b acc
      | .app f a =>
          let (m1, r1, t1) := walkRoles budget isHead inBinder f acc
          let (m2, r2, t2) := walkRoles r1 false inBinder a m1
          (m2, r2, t1 || t2)
      | .forallE _ bt body _ | .lam _ bt body _ =>
          let (m1, r1, t1) := walkRoles budget true true bt acc
          let (m2, r2, t2) := walkRoles r1 isHead inBinder body m1
          (m2, r2, t1 || t2)
      | .letE _ t v b _ =>
          let (m1, r1, t1) := walkRoles budget false inBinder t acc
          let (m2, r2, t2) := walkRoles r1 false inBinder v m1
          let (m3, r3, t3) := walkRoles r2 isHead inBinder b m2
          (m3, r3, t1 || t2 || t3)

/-! ### Head constant and outer-Pi type skeleton -/

/-- Head constant of an application spine (skip metadata); `none` for a
    variable/sort/projection head. -/
def headConstName : Expr → Option Name
  | .const n _   => some n
  | .app f _     => headConstName f
  | .mdata _ e   => headConstName e
  | _            => none

structure Skel where
  nPi : Nat := 0
  nDefault : Nat := 0
  nImplicit : Nat := 0
  nStrictImplicit : Nat := 0
  nInstImplicit : Nat := 0
  constraints : Std.HashMap Name Nat := {}
  deriving Inhabited

def Skel.bumpBinder (sk : Skel) (bi : BinderInfo) : Skel :=
  match bi with
  | .default        => { sk with nPi := sk.nPi + 1, nDefault := sk.nDefault + 1 }
  | .implicit       => { sk with nPi := sk.nPi + 1, nImplicit := sk.nImplicit + 1 }
  | .strictImplicit => { sk with nPi := sk.nPi + 1, nStrictImplicit := sk.nStrictImplicit + 1 }
  | .instImplicit   => { sk with nPi := sk.nPi + 1, nInstImplicit := sk.nInstImplicit + 1 }

/-- Peel only the OUTER forall spine; returns `(skeleton, conclusion, remaining
    budget, truncated)`. -/
partial def peelPis : Nat → Expr → Skel → Skel × Expr × Nat × Bool
  | 0, e, sk => (sk, e, 0, true)
  | budget+1, e, sk =>
      match e with
      | .forallE _ bt body bi =>
          let sk1 := sk.bumpBinder bi
          let sk2 :=
            match bi with
            | .instImplicit =>
                match headConstName bt with
                | some cn =>
                    { sk1 with constraints :=
                        sk1.constraints.insert cn (sk1.constraints.getD cn 0 + 1) }
                | none => sk1
            | _ => sk1
          peelPis budget body sk2
      | conclusion => (sk, conclusion, budget, false)

/-! ### Extraction command -/

elab "atlasExprRelations" : command => do
  let env ← getEnv
  let hRel ← IO.FS.Handle.mk atlasRelationsPath IO.FS.Mode.write
  let hSkel ← IO.FS.Handle.mk atlasSkeletonPath IO.FS.Mode.write

  let mut scanned : Nat := 0
  let mut sourcesWritten : Nat := 0
  let mut relationsWritten : Nat := 0
  let mut nTruncType : Nat := 0
  let mut nTruncValue : Nat := 0
  let mut nWithConstraints : Nat := 0

  let tStart ← IO.monoMsNow
  for (name, info) in env.constants.toList do
    scanned := scanned + 1

    let mod? := atlasModuleOf env name
    let keep : Bool :=
      match atlasMathlibOnlySources, mod? with
      | true, some m => m.toString.startsWith "Mathlib"
      | true, none   => false
      | false, _     => true
    let underCap : Bool :=
      match atlasLimit with
      | some lim => sourcesWritten < lim
      | none     => true

    if keep && underCap then
      -- Role decomposition, type layer (root is head, not in binder).
      let (typeMap, _, typeTrunc) := walkRoles atlasNodeBudget true false info.type {}
      if typeTrunc then nTruncType := nTruncType + 1 else pure ()

      -- Role decomposition, value/proof layer.
      let mut valueMap : Std.HashMap Name RoleCounts := {}
      let mut valueTrunc : Bool := false
      if atlasIncludeValue then
        match info.value? true with
        | none   => pure ()
        | some v =>
            let (vm, _, vt) := walkRoles atlasNodeBudget true false v {}
            valueMap := vm
            valueTrunc := vt
      if valueTrunc then nTruncValue := nTruncValue + 1 else pure ()

      -- One relation row per referenced target.
      let mut targets : Std.HashSet Name := {}
      for (t, _) in typeMap.toList do targets := targets.insert t
      for (t, _) in valueMap.toList do targets := targets.insert t

      for target in targets.toList do
        let tc : RoleCounts := typeMap.getD target {}
        let vc : RoleCounts := valueMap.getD target {}
        let targetKind :=
          match env.find? target with
          | some ci => atlasConstantKind ci
          | none    => "unknown"
        let row := Json.mkObj [
          ("source", Json.str name.toString),
          ("target", Json.str target.toString),
          ("targetKind", Json.str targetKind),
          ("isSelf", toJson (target == name)),
          ("typeHeadMain", toJson tc.headMain),
          ("typeArgMain", toJson tc.argMain),
          ("typeHeadBinder", toJson tc.headBinder),
          ("typeArgBinder", toJson tc.argBinder),
          ("valueHeadMain", toJson vc.headMain),
          ("valueArgMain", toJson vc.argMain),
          ("valueHeadBinder", toJson vc.headBinder),
          ("valueArgBinder", toJson vc.argBinder)
        ]
        hRel.putStrLn row.compress
        relationsWritten := relationsWritten + 1

      -- Type skeleton (outer Pi spine + conclusion head).
      let (sk, conclusion, _, _) := peelPis atlasNodeBudget info.type {}
      if sk.nInstImplicit > 0 then nWithConstraints := nWithConstraints + 1 else pure ()

      let mut carr : Array Json := #[]
      for (cn, ct) in sk.constraints.toList do
        carr := carr.push <| Json.mkObj [
          ("class", Json.str cn.toString), ("count", toJson ct)]
      let conclusionJson : Json :=
        match headConstName conclusion with
        | some cn => Json.str cn.toString
        | none    => Json.null
      let moduleJson : Json :=
        match mod? with
        | some m => Json.str m.toString
        | none   => Json.null

      let skel := Json.mkObj [
        ("name", Json.str name.toString),
        ("kind", Json.str (atlasConstantKind info)),
        ("module", moduleJson),
        ("nPi", toJson sk.nPi),
        ("nDefault", toJson sk.nDefault),
        ("nImplicit", toJson sk.nImplicit),
        ("nStrictImplicit", toJson sk.nStrictImplicit),
        ("nInstImplicit", toJson sk.nInstImplicit),
        ("constraints", Json.arr carr),
        ("conclusionHead", conclusionJson),
        ("typeRolesTruncated", toJson typeTrunc),
        ("valueRolesTruncated", toJson valueTrunc)
      ]
      hSkel.putStrLn skel.compress

      sourcesWritten := sourcesWritten + 1
      if sourcesWritten % 25000 = 0 then
        logInfo m!"  ... {sourcesWritten} sources, {relationsWritten} relations"
      else pure ()
    else pure ()

    match atlasLimit with
    | some lim => if sourcesWritten >= lim then break else pure ()
    | none     => pure ()

  hRel.flush
  hSkel.flush
  let tEnd ← IO.monoMsNow

  logInfo m!"Scanned constants:            {scanned}"
  logInfo m!"Source declarations:          {sourcesWritten}"
  logInfo m!"Relation rows written:        {relationsWritten}"
  logInfo m!"Decls w/ typeclass constraints: {nWithConstraints}"
  logInfo m!"Sources w/ truncated type roles:  {nTruncType}"
  logInfo m!"Sources w/ truncated value roles: {nTruncValue}"
  logInfo m!"Extraction ms (excl. import): {tEnd - tStart}"
  logInfo m!"Relations output: {atlasRelationsPath}"
  logInfo m!"Skeleton output:  {atlasSkeletonPath}"

atlasExprRelations
