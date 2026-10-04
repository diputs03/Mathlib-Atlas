import Mathlib

/-!
# 13 — Semantic / structural features (per declaration)

The compact, analysis-ready feature layer consumed by graph analysis (14) and
discovery experiments (15). For every Mathlib declaration it records, in one
bounded walk of the type and of the value/proof term:

* **type shape** — node count and AST depth, constant occurrences (total and
  distinct), outer-Pi binder counts by `BinderInfo`, number of typeclass
  constraints, and the conclusion head;
* **value/proof shape** — node count/depth, constant occurrences, counts of
  lambdas / foralls / applications / lets / literals / projections, the body
  head after peeling binders, whether the proof is closed by reflexivity
  (`…rfl`, i.e. definitional equality rather than a named lemma), and how often
  it uses recursors / `casesOn` (structural induction/recursion signal);
* **flags** — kind, class / instance status, namespace and name-depth, and
  generated / instance-name heuristics.

Intrinsic features only; graph-topological features (degree, centrality) are
left to 14. Same 50,000-node bounded-walk envelope as 08/09, with truncation
counted and flagged, never silent.

Output: `data/atlas_features.jsonl`.

Run (Windows, no WSL) from the repository root:
    lake env lean script\lean\13_features.lean
-/

open Lean
open Lean.Elab
open Lean.Elab.Command

def atlasFeaturesPath : String := "data/atlas_features.jsonl"
def atlasLimit : Option Nat := .none
def atlasNodeBudget : Nat := 50_000

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

def headConstName : Expr → Option Name
  | .const n _   => some n
  | .app f _     => headConstName f
  | .mdata _ e   => headConstName e
  | _            => none

/-- Peel outer binders (forall / lambda / let), returning the body. -/
partial def peelBinders : Expr → Expr
  | .forallE _ _ b _ => peelBinders b
  | .lam _ _ b _    => peelBinders b
  | .letE _ _ _ b _ => peelBinders b
  | e              => e

def lastSeg : Name → String
  | .str _ s => s
  | _       => ""

def isRecursorSeg (s : String) : Bool :=
  s == "rec" || s == "recOn" || s == "brecOn" || s == "ndrecOn" ||
  s == "ndrecOnOn" || s == "below" || s == "ibelow"

/-! ### Bounded feature walker -/

structure Feat where
  consts : Nat := 0
  distinct : Std.HashSet Name := {}
  lams : Nat := 0
  foralls : Nat := 0
  apps : Nat := 0
  lets : Nat := 0
  lits : Nat := 0
  projs : Nat := 0
  recRefs : Nat := 0
  caseRefs : Nat := 0
  deriving Inhabited

def featBumpConst (f : Feat) (n : Name) : Feat :=
  let s := lastSeg n
  { f with
      consts := f.consts + 1,
      distinct := f.distinct.insert n,
      recRefs := f.recRefs + (if isRecursorSeg s then 1 else 0),
      caseRefs := f.caseRefs + (if s == "casesOn" then 1 else 0) }

/-- Returns (accumulator, nodes visited, subtree depth, remaining budget,
    truncated). -/
partial def walkFeat : Nat → Expr → Feat → Feat × Nat × Nat × Nat × Bool
  | 0, _, acc => (acc, 0, 0, 0, true)
  | budget+1, e, acc =>
    match e with
    | .bvar _ | .fvar _ | .mvar _ | .sort _ =>
        (acc, 1, 1, budget, false)
    | .lit _ =>
        ({ acc with lits := acc.lits + 1 }, 1, 1, budget, false)
    | .const n _ =>
        (featBumpConst acc n, 1, 1, budget, false)
    | .mdata _ b =>
        let (a1, n1, d1, r1, t1) := walkFeat budget b acc
        (a1, n1 + 1, d1 + 1, r1, t1)
    | .proj _ _ b =>
        let (a1, n1, d1, r1, t1) :=
          walkFeat budget b { acc with projs := acc.projs + 1 }
        (a1, n1 + 1, d1 + 1, r1, t1)
    | .app f a =>
        let (a1, n1, d1, r1, t1) := walkFeat budget f { acc with apps := acc.apps + 1 }
        let (a2, n2, d2, r2, t2) := walkFeat r1 a a1
        (a2, n1 + n2 + 1, (max d1 d2) + 1, r2, t1 || t2)
    | .forallE _ bt body _ =>
        let (a1, n1, d1, r1, t1) :=
          walkFeat budget bt { acc with foralls := acc.foralls + 1 }
        let (a2, n2, d2, r2, t2) := walkFeat r1 body a1
        (a2, n1 + n2 + 1, (max d1 d2) + 1, r2, t1 || t2)
    | .lam _ bt body _ =>
        let (a1, n1, d1, r1, t1) :=
          walkFeat budget bt { acc with lams := acc.lams + 1 }
        let (a2, n2, d2, r2, t2) := walkFeat r1 body a1
        (a2, n1 + n2 + 1, (max d1 d2) + 1, r2, t1 || t2)
    | .letE _ t v b _ =>
        let (a1, n1, d1, r1, t1) :=
          walkFeat budget t { acc with lets := acc.lets + 1 }
        let (a2, n2, d2, r2, t2) := walkFeat r1 v a1
        let (a3, n3, d3, r3, t3) := walkFeat r2 b a2
        (a3, n1 + n2 + n3 + 1, (max (max d1 d2) d3) + 1, r3, t1 || t2 || t3)

/-! ### Outer-Pi binder skeleton (counts only) -/

structure Skel where
  nPi : Nat := 0
  nDefault : Nat := 0
  nImplicit : Nat := 0
  nStrictImplicit : Nat := 0
  nInstImplicit : Nat := 0
  deriving Inhabited

def Skel.bump (sk : Skel) (bi : BinderInfo) : Skel :=
  match bi with
  | .default        => { sk with nPi := sk.nPi + 1, nDefault := sk.nDefault + 1 }
  | .implicit       => { sk with nPi := sk.nPi + 1, nImplicit := sk.nImplicit + 1 }
  | .strictImplicit => { sk with nPi := sk.nPi + 1, nStrictImplicit := sk.nStrictImplicit + 1 }
  | .instImplicit   => { sk with nPi := sk.nPi + 1, nInstImplicit := sk.nInstImplicit + 1 }

partial def peelPis : Nat → Expr → Skel → Skel × Expr
  | 0, e, sk => (sk, e)
  | budget+1, e, sk =>
      match e with
      | .forallE _ _ body bi => peelPis budget body (sk.bump bi)
      | conclusion => (sk, conclusion)

def userDisplayName (n : Name) : Name :=
  (Lean.privateToUserName? n).getD n

def isGeneratedName (s : String) : Bool :=
  s.contains ".match_" || s.contains "._proof" || s.contains ".eq_" ||
  s.contains ".splitter" || s.contains ".brecOn" ||
  (match s.splitOn "." |>.getLast? with | some t => t.startsWith "_" | none => false)

elab "atlasFeatures" : command => do
  let env ← getEnv
  let h ← IO.FS.Handle.mk atlasFeaturesPath IO.FS.Mode.write

  let mut scanned : Nat := 0
  let mut written : Nat := 0
  let mut nTruncType : Nat := 0
  let mut nTruncValue : Nat := 0
  let mut nRfl : Nat := 0
  let tStart ← IO.monoMsNow

  for (name, info) in env.constants.toList do
    scanned := scanned + 1
    let mod? := atlasModuleOf env name
    let keep : Bool :=
      match mod? with
      | some m => m.toString.startsWith "Mathlib"
      | none   => false
    let underCap : Bool :=
      match atlasLimit with
      | some lim => written < lim
      | none     => true

    if keep && underCap then
      -- type layer
      let (tf, tn, td, _, tTrunc) := walkFeat atlasNodeBudget info.type {}
      if tTrunc then nTruncType := nTruncType + 1 else pure ()
      let (sk, conclusion) := peelPis atlasNodeBudget info.type {}
      let conclusionJson : Json :=
        match headConstName conclusion with
        | some cn => Json.str cn.toString
        | none    => Json.null

      -- value layer
      let mut hasValue : Bool := false
      let mut vf : Feat := {}
      let mut vn : Nat := 0
      let mut vd : Nat := 0
      let mut vTrunc : Bool := false
      let mut valueHeadJson : Json := Json.null
      let mut isRfl : Bool := false
      match info.value? true with
      | some v =>
          hasValue := true
          let (a, nN, dD, _, tr) := walkFeat atlasNodeBudget v {}
          vf := a; vn := nN; vd := dD; vTrunc := tr
          match headConstName (peelBinders v) with
          | some hn =>
              valueHeadJson := Json.str hn.toString
              if lastSeg hn == "rfl" then isRfl := true else pure ()
          | none => pure ()
      | none => pure ()
      if vTrunc then nTruncValue := nTruncValue + 1 else pure ()
      if isRfl then nRfl := nRfl + 1 else pure ()

      let disp := userDisplayName name
      let kind := atlasConstantKind info
      let last := lastSeg disp
      let moduleJson : Json :=
        match mod? with
        | some m => Json.str m.toString
        | none   => Json.null

      let row := Json.mkObj [
        ("name", Json.str name.toString),
        ("kind", Json.str kind),
        ("module", moduleJson),
        ("namespace", Json.str (if disp.getPrefix == Name.anonymous then "" else disp.getPrefix.toString)),
        ("nameDepth", toJson disp.getNumParts),
        ("typeNodes", toJson tn),
        ("typeDepth", toJson td),
        ("typeConsts", toJson tf.consts),
        ("typeDistinct", toJson tf.distinct.size),
        ("nPi", toJson sk.nPi),
        ("nDefault", toJson sk.nDefault),
        ("nImplicit", toJson sk.nImplicit),
        ("nStrictImplicit", toJson sk.nStrictImplicit),
        ("nInstImplicit", toJson sk.nInstImplicit),
        ("conclusionHead", conclusionJson),
        ("typeTruncated", toJson tTrunc),
        ("hasValue", toJson hasValue),
        ("valueNodes", toJson vn),
        ("valueDepth", toJson vd),
        ("valueConsts", toJson vf.consts),
        ("valueDistinct", toJson vf.distinct.size),
        ("valueLams", toJson vf.lams),
        ("valueForalls", toJson vf.foralls),
        ("valueApps", toJson vf.apps),
        ("valueLets", toJson vf.lets),
        ("valueLits", toJson vf.lits),
        ("valueProjs", toJson vf.projs),
        ("recRefs", toJson vf.recRefs),
        ("caseRefs", toJson vf.caseRefs),
        ("valueHead", valueHeadJson),
        ("valueIsRfl", toJson isRfl),
        ("valueTruncated", toJson vTrunc),
        ("isClass", toJson (Lean.isClass env name)),
        ("isInstance", toJson (Meta.isInstanceCore env name)),
        ("isInstName", toJson (last.startsWith "inst")),
        ("isGenerated", toJson (isGeneratedName disp.toString))
      ]
      h.putStrLn row.compress
      written := written + 1
      if written % 50000 = 0 then logInfo m!"  ... {written} features" else pure ()
    else pure ()

    match atlasLimit with
    | some lim => if written >= lim then break else pure ()
    | none     => pure ()

  h.flush
  let tEnd ← IO.monoMsNow
  logInfo m!"Scanned constants:        {scanned}"
  logInfo m!"Feature rows written:     {written}"
  logInfo m!"Reflexivity-closed proofs: {nRfl}"
  logInfo m!"Truncated type walks:     {nTruncType}"
  logInfo m!"Truncated value walks:    {nTruncValue}"
  logInfo m!"Extraction ms (excl. import): {tEnd - tStart}"
  logInfo m!"Output: {atlasFeaturesPath}"

atlasFeatures
