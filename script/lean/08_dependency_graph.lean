import Mathlib

/-!
# 08 — Persistent labelled dependency graph

Builds the DIRECT, named-declaration dependency graph of Mathlib as JSON Lines:
one edge per ordered `(source, target)` pair of constants, where `target` is a
`Expr.const` occurring in the source's type and/or value/proof term.

## Edge labels (kept separate, never collapsed into one "depends on")

* `inType` / `inValue` : which LAYER the reference occurs in — the type
  signature vs the proof/definition body (see transfer note §18: type dependency
  and proof/body dependency are different notions);
* `typeCount` / `valueCount` : occurrence multiplicity within each layer;
* `targetKind` : the target's `ConstantInfo` kind
  (`axiom|definition|opaque|theorem|quotient|inductive|constructor|recursor`,
  or `unknown`).  Constructor / recursor / inductive dependencies are therefore
  already labelled; typeclass-*instance* dependencies are deferred (an instance
  is a def/theorem carrying the `instance` attribute; join with an instance list
  later rather than over-claiming here);
* `isSelf` : self-reference (e.g. recursive definitions / well-founded fixes).

## Scope and non-goals

* These are DIRECT (one-hop) named references.  Transitive closure, axiom
  dependency (`#print axioms`) and definitional/reduction dependency are
  DERIVED analyses over these edges + node data, not computed here (transfer
  note §18–20).  Kernel conversion and reduction are deliberately not modelled
  as hidden theorem edges.
* Only SOURCE declarations are filtered to Mathlib source modules (via the
  environment, not name prefixes).  Edges may point at core/Batteries targets;
  `targetKind` and the corpus record that boundary.
* Reference collection is node-bounded (`atlasNodeBudget`) so that the handful of
  pathologically large proof terms cannot stall extraction; truncation is
  reported per declaration and per layer, never silent.

Run (Windows, no WSL) from the repository root:
    lake env lean script\lean\08_dependency_graph.lean
-/

open Lean
open Lean.Elab
open Lean.Elab.Command

/-! ### Configuration -/

def atlasEdgesPath : String := "data/atlas_edges.jsonl"

/-- Only emit edges whose SOURCE is declared in a `Mathlib` source module. -/
def atlasMathlibOnlySources : Bool := true

/-- Optional cap on source declarations emitted (`none` = whole environment). -/
def atlasLimit : Option Nat := .none

/-- Collect references from value/proof terms as well as types. -/
def atlasIncludeValueEdges : Bool := true

/-- At most this many Expr nodes are visited per expression when collecting
    references; traversal beyond it is flagged as truncated.  Set to the same
    50k-node envelope proven tractable by script 07: distinct targets are
    essentially always reached well before this, while repetition (which only
    affects multiplicity) dominates large proof terms. -/
def atlasNodeBudget : Nat := 50_000

/-! ### Classification / provenance (shared shape with 07) -/

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

/-! ### Bounded reference collection -/

/-- Returns `(targetName → occurrence count, remaining budget, truncated)`.
    The shared budget bounds total work even for terms with tens of millions of
    nodes.  Universe levels (`Level`) are intentionally not treated as
    declaration references (they are universe parameters). -/
partial def collectRefs :
    Nat → Expr → Std.HashMap Name Nat → Std.HashMap Name Nat × Nat × Bool
  | 0, _, acc => (acc, 0, true)
  | budget+1, e, acc =>
      match e with
      | .const n _ =>
          (acc.insert n (acc.getD n 0 + 1), budget, false)
      | .bvar _ | .fvar _ | .mvar _ | .sort _ | .lit _ =>
          (acc, budget, false)
      | .mdata _ b => collectRefs budget b acc
      | .proj _ _ b => collectRefs budget b acc
      | .app f a =>
          let (m1, r1, t1) := collectRefs budget f acc
          let (m2, r2, t2) := collectRefs r1 a m1
          (m2, r2, t1 || t2)
      | .lam _ t b _ | .forallE _ t b _ =>
          let (m1, r1, t1) := collectRefs budget t acc
          let (m2, r2, t2) := collectRefs r1 b m1
          (m2, r2, t1 || t2)
      | .letE _ t v b _ =>
          let (m1, r1, t1) := collectRefs budget t acc
          let (m2, r2, t2) := collectRefs r1 v m1
          let (m3, r3, t3) := collectRefs r2 b m2
          (m3, r3, t1 || t2 || t3)

/-! ### Edge extraction command -/

elab "atlasEdges" : command => do
  let env ← getEnv
  let h ← IO.FS.Handle.mk atlasEdgesPath IO.FS.Mode.write

  let mut scanned : Nat := 0
  let mut sourcesWritten : Nat := 0
  let mut edgesWritten : Nat := 0
  let mut nTruncType : Nat := 0
  let mut nTruncValue : Nat := 0
  let mut nSelfEdges : Nat := 0

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
      -- Type layer.
      let (typeMap, _, typeTrunc) := collectRefs atlasNodeBudget info.type {}
      if typeTrunc then nTruncType := nTruncType + 1 else pure ()

      -- Value/proof layer.
      let mut valueMap : Std.HashMap Name Nat := {}
      let mut valueTrunc : Bool := false
      if atlasIncludeValueEdges then
        match info.value? true with
        | none   => pure ()
        | some v =>
            let (vm, _, vt) := collectRefs atlasNodeBudget v {}
            valueMap := vm
            valueTrunc := vt
      if valueTrunc then nTruncValue := nTruncValue + 1 else pure ()

      -- Union of referenced targets.
      let mut targets : Std.HashSet Name := {}
      for (t, _) in typeMap.toList do targets := targets.insert t
      for (t, _) in valueMap.toList do targets := targets.insert t

      for target in targets.toList do
        let typeCount := typeMap.getD target 0
        let valueCount := valueMap.getD target 0
        let targetKind :=
          match env.find? target with
          | some ci => atlasConstantKind ci
          | none    => "unknown"
        let isSelf := target == name
        if isSelf then nSelfEdges := nSelfEdges + 1 else pure ()

        let edge := Json.mkObj [
          ("source", Json.str name.toString),
          ("target", Json.str target.toString),
          ("inType", toJson (if typeCount > 0 then true else false)),
          ("inValue", toJson (if valueCount > 0 then true else false)),
          ("typeCount", toJson typeCount),
          ("valueCount", toJson valueCount),
          ("targetKind", Json.str targetKind),
          ("isSelf", toJson isSelf)
        ]
        h.putStrLn edge.compress
        edgesWritten := edgesWritten + 1

      sourcesWritten := sourcesWritten + 1
      if sourcesWritten % 25000 = 0 then
        logInfo m!"  ... {sourcesWritten} sources, {edgesWritten} edges"
      else pure ()
    else pure ()

    match atlasLimit with
    | some lim => if sourcesWritten >= lim then break else pure ()
    | none     => pure ()

  h.flush
  let tEnd ← IO.monoMsNow

  logInfo m!"Scanned constants:        {scanned}"
  logInfo m!"Source declarations:      {sourcesWritten}"
  logInfo m!"Edges written:            {edgesWritten}"
  logInfo m!"Self-edges:               {nSelfEdges}"
  logInfo m!"Sources w/ truncated type refs:  {nTruncType}"
  logInfo m!"Sources w/ truncated value refs: {nTruncValue}"
  logInfo m!"Extraction ms (excl. import):    {tEnd - tStart}"
  logInfo m!"Output:                   {atlasEdgesPath}"

atlasEdges
