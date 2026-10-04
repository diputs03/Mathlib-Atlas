import Mathlib

/-!
# 68 — Conclusion-term layer (quantifier prefix + conclusion as S-expressions)

Script 67's coarse ladder scan established a detectability boundary: deciding
whether two theorems are the *same statement at different hypothesis
strengths* requires term-level comparison of the conclusion, which the compact
feature layer (node counts, conclusion head) deliberately discards. Full proof
persistence (step 07, ~70+ GB) is far more than needed; this script extracts
the minimal layer that makes vertical generalization detection precise:

for every Mathlib declaration, the **type only**, split into
* the outer `forall` prefix — one entry per binder with its `BinderInfo` tag
  and the binder-type term — and
* the **conclusion term** after the prefix,

serialized as a small S-expression (constants by name; sorts; de Bruijn
structure; literals; projections). Proof/value terms are not included.

Output: `data/atlas_conclusion_terms.jsonl`
Run:    lake env lean script\lean\68_conclusion_terms.lean
-/

open Lean
open Lean.Elab
open Lean.Elab.Command

def atlasConclusionPath : String := "data/atlas_conclusion_terms.jsonl"
def atlasTermBudget : Nat := 20_000

/-- The ten mature core areas; other modules are not serialized. -/
def atlasCoreAreas : Std.HashSet String :=
  Std.HashSet.ofList
    ["Algebra", "Analysis", "Data", "FieldTheory", "GroupTheory",
     "LinearAlgebra", "Logic", "Order", "RingTheory", "Topology"]

def atlasModuleOf (env : Environment) (name : Name) : Option Name := do
  let idx ← env.getModuleIdxFor? name
  env.header.moduleNames[idx.toNat]?

/-- Core-area classification from the source module name. -/
def atlasModuleArea (m : Name) : Option String :=
  match m.toString.splitOn "." with
  | "Mathlib" :: a :: _ => some a
  | _                  => none

def lastSegStr : Name → String
  | .str _ s => s
  | _        => ""

def isGeneratedNameStr (s : String) : Bool :=
  s.contains ".match_" || s.contains "._proof" || s.contains ".eq_" ||
  s.contains ".splitter" || s.contains ".brecOn" ||
  (match s.splitOn "." |>.getLast? with | some t => t.startsWith "_" | none => false)

def escapeStr : String → String
  | s => s.foldl (fun acc c =>
      if c == '\\' then acc ++ "\\\\"
      else if c == '"' then acc ++ "\\\""
      else acc.push c) ""

/-! ### S-expression encoder -/

def biTag : BinderInfo → String
  | .default        => "d"
  | .implicit       => "i"
  | .strictImplicit => "h"
  | .instImplicit   => "c"

/-- Encode an expression under a node budget; returns (term, budget left,
    truncated). -/
partial def encExpr : Nat → Expr → String × Nat × Bool
  | 0, _ => ("X", 0, true)
  | budget+1, e =>
    match e with
    | .bvar i =>
        (s!"(b {i})", budget, false)
    | .fvar _ =>
        ("(f)", budget, false)
    | .mvar _ =>
        ("(m)", budget, false)
    | .sort _ =>
        ("(t)", budget, false)
    | .const n _ =>
        (s!"(c {escapeStr n.toString})", budget, false)
    | .lit l =>
        match l with
        | .natVal v   => (s!"(n {v})", budget, false)
        | .strVal v    => (s!"(s \"{escapeStr v}\")", budget, false)
    | .mdata _ b =>
        encExpr budget b
    | .proj s i b =>
        let (t1, r1, _tr1) := encExpr budget b
        (s!"(j {s} {i} {t1})", r1, _tr1)
    | .app fn arg =>
        let (t1, r1, tr1) := encExpr budget fn
        let (t2, r2, tr2) := encExpr r1 arg
        (s!"(a {t1} {t2})", r2, tr1 || tr2)
    | .lam _ bt body bi =>
        let (t1, r1, tr1) := encExpr budget bt
        let (t2, r2, tr2) := encExpr r1 body
        (s!"(l {biTag bi} {t1} {t2})", r2, tr1 || tr2)
    | .forallE _ bt body bi =>
        let (t1, r1, tr1) := encExpr budget bt
        let (t2, r2, tr2) := encExpr r1 body
        (s!"(q {biTag bi} {t1} {t2})", r2, tr1 || tr2)
    | .letE _ t v body _ =>
        let (t1, r1, tr1) := encExpr budget t
        let (t2, r2, tr2) := encExpr r1 v
        let (t3, r3, tr3) := encExpr r2 body
        (s!"(e {t1} {t2} {t3})", r3, tr1 || tr2 || tr3)

/-- Peel the outer forall prefix, recording binder tag + encoded binder type.
    Returns (prefix JSON array, conclusion term, truncated). -/
partial def peelPrefix : Nat → Expr → Array Json → String → Array Json × String × Bool
  | 0, _, acc, _ => (acc, "X", true)
  | budget+1, e, acc, _ =>
    match e with
    | .forallE _ bt body bi =>
        let (_tt, r1, _tr1) := encExpr budget bt
        let entry : Json := s!"{biTag bi}:{_tt}"
        peelPrefix r1 body (acc.push entry) ""
    | conclusion =>
        let (tc, _, tr2) := encExpr budget conclusion
        (acc, tc, tr2)

elab "atlasConclusion" : command => do
  let env ← getEnv
  let h ← IO.FS.Handle.mk atlasConclusionPath IO.FS.Mode.write

  let mut scanned : Nat := 0
  let mut written : Nat := 0
  let mut nTrunc : Nat := 0
  let tStart ← IO.monoMsNow

  for (name, info) in env.constants.toList do
    scanned := scanned + 1
    let mod? := atlasModuleOf env name
    let keep : Bool :=
      let disp := (Lean.privateToUserName? name).getD name
      match mod? with
      | some m =>
          match atlasModuleArea m with
          | some a =>
              atlasCoreAreas.contains a && ¬ isGeneratedNameStr disp.toString
          | none   => false
      | none   => false

    if keep then
      let (pfx, term, trunc) := peelPrefix atlasTermBudget info.type #[] ""
      if trunc then nTrunc := nTrunc + 1 else pure ()

      let modJson : Json :=
        match mod? with
        | some m => Json.str m.toString
        | none   => Json.null

      let row := Json.mkObj [
        ("name", Json.str name.toString),
        ("kind", Json.str (match info with
          | .axiomInfo _   => "axiom"
          | .defnInfo _    => "definition"
          | .opaqueInfo _  => "opaque"
          | .thmInfo _     => "theorem"
          | .quotInfo _    => "quotient"
          | .inductInfo _  => "inductive"
          | .ctorInfo _    => "constructor"
          | .recInfo _     => "recursor")),
        ("module", modJson),
        ("prefix", Json.arr pfx),
        ("conclusion", Json.str term),
        ("truncated", toJson trunc)
      ]
      h.putStrLn row.compress
      written := written + 1
      if written % 10000 = 0 then
        h.flush
        logInfo m!"  ... {written} rows"
      else pure ()
    else pure ()

  h.flush
  let tEnd ← IO.monoMsNow
  logInfo m!"Scanned constants:   {scanned}"
  logInfo m!"Rows written:        {written}"
  logInfo m!"Truncated terms:     {nTrunc}"
  logInfo m!"Extraction ms:       {tEnd - tStart}"
  logInfo m!"Output: {atlasConclusionPath}"

atlasConclusion
