import Mathlib

/-!
# 07 — Persistent Atlas corpus (first machine-readable raw corpus)

## What this produces

One JSON Lines record per declaration (one JSON object per line).  For the type
we preserve

* `typeStr` : the pretty-printed expression string (human readable), and
* `typeAst` : a faithful structural encoding of every `Expr` constructor,

and, when `atlasStoreValues` is true, the same pair for the value/proof
(`valueStr`/`valueAst`); by default proof *terms* are only measured
(`valueNodeCount`, `valueOversized`), because they are the source of the
corpus' extreme heavy tail.  Downstream analysis therefore never has to
re-parse pretty-printed strings, and no structural information is discarded
prematurely (full terms remain one config flag away).  Provenance (the source
module) is taken from the Lean environment, never inferred from the
declaration-name prefix.

## The elaborated-term size problem, and the three tiers

Fully elaborated kernel terms carry enormous amounts of typeclass / implicit /
universe detail.  Measured on this commit over a 5,000-declaration Mathlib
sample, the *median* declaration is a few KB, but a small number of terms are
pathological (one machine-generated proof term alone is ~1.6 GB, i.e. tens of
millions of Expr nodes), and structural ASTs are ~3.7x the size of the pretty
strings.  Inlining everything would yield a corpus on the order of 100 GB.

We never *silently* drop anything.  Every expression (type or value) is routed
through ONE policy, `tierExpr`, into three tiers:

1. inline  — AST bytes ≤ `atlasAstInlineCap` AND pretty-string bytes ≤
   `atlasStrInlineCap`: both `Str` and `Ast` live in the MAIN record;
2. sharded — node count ≤ `atlasExprNodeCap` but the term is too big to inline:
   the FULL `{str, ast}` is written, keyed by `(name, slot)`, to the sidecar
   `atlasLargeExprsPath`, and the main record keeps the readable string (when it
   itself is small), the exact byte/node counts, and `<slot>Sharded = true`;
3. oversized — node count > `atlasExprNodeCap`: we never build the term (the
   bounded counter `sizeWithin` visits at most the cap's worth of nodes, which
   is what keeps extraction fast); the main record records `<slot>Oversized` and
   a sentinel count, so the term is still *known* and can be targeted later.

The labelled dependency graph / edge taxonomy is deliberately NOT built here;
that is 08.

Run (Windows, no WSL) from the repository root:
    lake env lean script\lean\07_persistent_corpus.lean
-/

open Lean
open Lean.Elab
open Lean.Elab.Command

/-! ### Configuration -/

/-- Main corpus path (JSON Lines). -/
def atlasOutPath : String := "data/atlas_corpus.jsonl"

/-- Sidecar shard for large-but-encodable expressions (JSON Lines). -/
def atlasLargeExprsPath : String := "data/atlas_large_exprs.jsonl"

/-- Keep only declarations whose source module starts with `Mathlib`. -/
def atlasMathlibOnly : Bool := true

/-- Optional cap on emitted main records (`none` = whole environment).
    Set `.some 5000` for a bounded sample, `.none` for the full corpus. -/
def atlasLimit : Option Nat := .none

/-- Emit value/proof expressions at all (types are always emitted). -/
def atlasIncludeValue : Bool := true

/-- Store the value/proof *terms* (pretty string + structural AST), inline or to
    the sidecar.  When false (the default), the main corpus is the high-signal
    *signature* layer — kind, provenance, namespace, level params and the full
    type — while each value is still measured: `valueNodeCount` and
    `valueOversized` are recorded so proof size is never invisible.  Full proof
    terms are the source of the corpus' extreme heavy tail (one measured term is
    ~1.6 GB), so they are opt-in; flip this to true to preserve them. -/
def atlasStoreValues : Bool := false

/-- Above this many Expr nodes an expression is tier-3 "oversized". -/
def atlasExprNodeCap : Nat := 50_000

/-- A structural AST at most this many UTF-8 bytes is kept inline in the main
    record; larger (but node-bounded) ASTs go to the sidecar. -/
def atlasAstInlineCap : Nat := 64_000

/-- A pretty expression string at most this many UTF-8 bytes is kept inline;
    larger strings are still preserved, but only in the sidecar. -/
def atlasStrInlineCap : Nat := 200_000

/-! ### Declaration kind -/

def atlasConstantKind : ConstantInfo → String
  | .axiomInfo _   => "axiom"
  | .defnInfo _    => "definition"
  | .opaqueInfo _  => "opaque"
  | .thmInfo _     => "theorem"
  | .quotInfo _    => "quotient"
  | .inductInfo _  => "inductive"
  | .ctorInfo _    => "constructor"
  | .recInfo _     => "recursor"

/-! ### Structural encoding of universe levels and expressions -/

def atlasBinderInfo : BinderInfo → String
  | .default        => "default"
  | .implicit       => "implicit"
  | .strictImplicit => "strictImplicit"
  | .instImplicit   => "instImplicit"

def atlasHints : ReducibilityHints → String
  | .opaque    => "opaque"
  | .abbrev    => "abbrev"
  | .regular _ => "regular"

/-- Enclosing namespace = name with its final component removed. -/
def atlasNamespace : Name → String
  | .str pre _ => pre.toString
  | .num pre _ => pre.toString
  | .anonymous => ""

/-- Pretty-render an expression through `MessageData` (effectful). -/
def atlasPretty (e : Expr) : BaseIO String :=
  MessageData.toString m!"{e}"

partial def encLevel : Level → Json
  | .zero => Json.mkObj [("tag", Json.str "zero")]
  | .succ l => Json.mkObj [("tag", Json.str "succ"), ("lvl", encLevel l)]
  | .max a b =>
      Json.mkObj [("tag", Json.str "max"), ("lhs", encLevel a), ("rhs", encLevel b)]
  | .imax a b =>
      Json.mkObj [("tag", Json.str "imax"), ("lhs", encLevel a), ("rhs", encLevel b)]
  | .param n => Json.mkObj [("tag", Json.str "param"), ("name", Json.str n.toString)]
  | .mvar _ => Json.mkObj [("tag", Json.str "mvar")]

/-- Faithful encoding of every `Expr` constructor. -/
partial def encExpr : Expr → Json
  | .bvar i =>
      Json.mkObj [("tag", Json.str "bvar"), ("deBruijn", toJson i)]
  | .fvar id =>
      Json.mkObj [("tag", Json.str "fvar"), ("name", Json.str id.name.toString)]
  | .mvar id =>
      Json.mkObj [("tag", Json.str "mvar"), ("name", Json.str id.name.toString)]
  | .sort l =>
      Json.mkObj [("tag", Json.str "sort"), ("level", encLevel l)]
  | .const name levels =>
      Json.mkObj [
        ("tag", Json.str "const"),
        ("name", Json.str name.toString),
        ("levels", Json.arr (levels.map encLevel).toArray)
      ]
  | .app fn arg =>
      Json.mkObj [("tag", Json.str "app"), ("fn", encExpr fn), ("arg", encExpr arg)]
  | .lam n ty body bi =>
      Json.mkObj [
        ("tag", Json.str "lam"),
        ("binderName", Json.str n.toString),
        ("binderInfo", Json.str (atlasBinderInfo bi)),
        ("binderType", encExpr ty),
        ("body", encExpr body)
      ]
  | .forallE n ty body bi =>
      Json.mkObj [
        ("tag", Json.str "forallE"),
        ("binderName", Json.str n.toString),
        ("binderInfo", Json.str (atlasBinderInfo bi)),
        ("binderType", encExpr ty),
        ("body", encExpr body)
      ]
  | .letE n ty val body nonDep =>
      Json.mkObj [
        ("tag", Json.str "letE"),
        ("name", Json.str n.toString),
        ("nonDep", toJson nonDep),
        ("type", encExpr ty),
        ("value", encExpr val),
        ("body", encExpr body)
      ]
  | .lit l =>
      match l with
      | .natVal v => Json.mkObj [("tag", Json.str "litNat"), ("value", toJson v)]
      | .strVal s => Json.mkObj [("tag", Json.str "litStr"), ("value", Json.str s)]
  | .mdata _ body =>
      Json.mkObj [("tag", Json.str "mdata"), ("body", encExpr body)]
  | .proj tname idx st =>
      Json.mkObj [
        ("tag", Json.str "proj"),
        ("typeName", Json.str tname.toString),
        ("idx", toJson idx),
        ("struct", encExpr st)
      ]

/-- Bounded Expr-node count.  Returns the exact count iff it is at most `budget`;
    otherwise `none`, having visited at most ~`budget` nodes (it prunes as soon
    as the budget is exhausted).  This bounds work even for terms with tens of
    millions of nodes. -/
partial def sizeWithin : Nat → Expr → Option Nat
  | 0, _ => none
  | budget+1, e =>
      match e with
      | .bvar _ | .fvar _ | .mvar _ | .sort _ | .const _ _ | .lit _ => some 1
      | .mdata _ b => sizeWithin (budget + 1) b
      | .proj _ _ b => (fun nb => 1 + nb) <$> sizeWithin budget b
      | .app f a =>
          match sizeWithin budget f with
          | none => none
          | some nf =>
            match sizeWithin (budget - nf) a with
            | none => none
            | some na =>
                let t := 1 + nf + na
                if t > budget + 1 then none else some t
      | .lam _ t b _ | .forallE _ t b _ =>
          match sizeWithin budget t with
          | none => none
          | some nt =>
            match sizeWithin (budget - nt) b with
            | none => none
            | some nb =>
                let t := 1 + nt + nb
                if t > budget + 1 then none else some t
      | .letE _ t v b _ =>
          match sizeWithin budget t with
          | none => none
          | some nt =>
            match sizeWithin (budget - nt) v with
            | none => none
            | some nv =>
              match sizeWithin (budget - nt - nv) b with
              | none => none
              | some nb =>
                  let t := 1 + nt + nv + nb
                  if t > budget + 1 then none else some t

/-! ### Environment-derived provenance -/

def atlasModuleOf (env : Environment) (name : Name) : Option Name := do
  let idx ← env.getModuleIdxFor? name
  env.header.moduleNames[idx.toNat]?

/-! ### Uniform size tiering for one expression -/

/-- The main-record view of one size-tiered expression, plus an optional
    sidecar record carrying the full expression when it was withheld. -/
structure Tiered where
  nodeCount  : Nat
  astBytes   : Nat
  strBytes   : Nat
  sharded    : Bool
  oversized  : Bool
  strJson    : Json
  astJson    : Json
  shardRec?  : Option Json

/-- Route one expression (`slot` = "type" | "value") through the three tiers. -/
def tierExpr (slot : String) (declName : Name) (kind : String) (e : Expr) :
    CommandElabM Tiered := do
  match sizeWithin atlasExprNodeCap e with
  | none =>
      -- Tier 3: pathological; never build/pretty-print the term.
      pure {
        nodeCount := atlasExprNodeCap + 1
        astBytes := 0
        strBytes := 0
        sharded := false
        oversized := true
        strJson := Json.null
        astJson := Json.null
        shardRec? := none
      }
  | some nodes =>
      let ast := encExpr e
      let astBytes := ast.compress.utf8ByteSize
      let str ← atlasPretty e
      let strBytes := str.utf8ByteSize
      let astInline := astBytes ≤ atlasAstInlineCap
      let strInline := strBytes ≤ atlasStrInlineCap
      let needShard := ¬(astInline && strInline)
      let shardRec? :=
        if needShard then
          some (Json.mkObj [
            ("name", Json.str declName.toString),
            ("slot", Json.str slot),
            ("kind", Json.str kind),
            ("nodeCount", toJson nodes),
            ("astBytes", toJson astBytes),
            ("strBytes", toJson strBytes),
            ("str", if strInline then Json.null else Json.str str),
            ("ast", if astInline then Json.null else ast)
          ])
        else none
      pure {
        nodeCount := nodes
        astBytes
        strBytes
        sharded := needShard
        oversized := false
        strJson := if strInline then Json.str str else Json.null
        astJson := if astInline then ast else Json.null
        shardRec?
      }

/-! ### Extraction command -/

elab "atlasCorpus" : command => do
  let env ← getEnv

  let hMain ← IO.FS.Handle.mk atlasOutPath IO.FS.Mode.write
  let hLarge ← IO.FS.Handle.mk atlasLargeExprsPath IO.FS.Mode.write

  let mut written : Nat := 0
  let mut scanned : Nat := 0
  let mut nSharded : Nat := 0
  let mut nOversized : Nat := 0

  for (name, info) in env.constants.toList do
    scanned := scanned + 1

    let mod? := atlasModuleOf env name

    -- Filter by *source module*, never by name prefix.
    let keep : Bool :=
      match atlasMathlibOnly, mod? with
      | true, some m => m.toString.startsWith "Mathlib"
      | true, none   => false
      | false, _     => true

    let underCap : Bool :=
      match atlasLimit with
      | some lim => written < lim
      | none     => true

    if keep && underCap then
      let kind := atlasConstantKind info
      let nsStr := atlasNamespace name

      -- Tier the type.
      let tTier ← tierExpr "type" name kind info.type
      match tTier.shardRec? with
      | some r => hLarge.putStrLn r.compress
      | none   => pure ()

      -- Tier the value/proof, if any.
      let mut vNodeCount : Nat := 0
      let mut vAstBytes : Nat := 0
      let mut vStrBytes : Nat := 0
      let mut vSharded : Bool := false
      let mut vOversized : Bool := false
      let mut vStrJson : Json := Json.null
      let mut vAstJson : Json := Json.null

      if atlasIncludeValue then
        match info.value? true with
        | none => pure ()
        | some v =>
          if atlasStoreValues then
            -- Full tiering: build, pretty-print, and (if needed) shard the term.
            let vTier ← tierExpr "value" name kind v
            vNodeCount := vTier.nodeCount
            vAstBytes := vTier.astBytes
            vStrBytes := vTier.strBytes
            vSharded := vTier.sharded
            vOversized := vTier.oversized
            vStrJson := vTier.strJson
            vAstJson := vTier.astJson
            match vTier.shardRec? with
            | some r => hLarge.putStrLn r.compress
            | none   => pure ()
          else
            -- Signature-only mode: measure size (bounded) but do not build,
            -- pretty-print, or store the proof term.
            match sizeWithin atlasExprNodeCap v with
            | none =>
                vOversized := true
                vNodeCount := atlasExprNodeCap + 1
            | some nodes =>
                vNodeCount := nodes

      if tTier.sharded || vSharded then nSharded := nSharded + 1 else pure ()
      if tTier.oversized || vOversized then nOversized := nOversized + 1 else pure ()

      let fields : List (String × Json) := [
        ("name", Json.str name.toString),
        ("namespace", Json.str nsStr),
        ("kind", Json.str kind),
        ("module", match mod? with
                   | some m => Json.str m.toString
                   | none   => Json.null),
        ("levelParams",
          Json.arr (info.levelParams.map (fun p => Json.str p.toString)).toArray),
        ("isUnsafe", toJson info.isUnsafe),
        ("isPartial", toJson info.isPartial),
        ("hints", Json.str (atlasHints info.hints)),
        ("typeNodeCount", toJson tTier.nodeCount),
        ("typeAstBytes", toJson tTier.astBytes),
        ("typeStrBytes", toJson tTier.strBytes),
        ("typeSharded", toJson tTier.sharded),
        ("typeOversized", toJson tTier.oversized),
        ("typeStr", tTier.strJson),
        ("typeAst", tTier.astJson),
        ("valueNodeCount", toJson vNodeCount),
        ("valueAstBytes", toJson vAstBytes),
        ("valueStrBytes", toJson vStrBytes),
        ("valueSharded", toJson vSharded),
        ("valueOversized", toJson vOversized),
        ("valueStr", vStrJson),
        ("valueAst", vAstJson)
      ]

      hMain.putStrLn (Json.mkObj fields).compress
      written := written + 1

      if written % 25000 = 0 then
        logInfo m!"  ... {written} records (decls w/ sharded {nSharded}, w/ oversized {nOversized})"
      else pure ()
    else pure ()

    match atlasLimit with
    | some lim => if written >= lim then break else pure ()
    | none     => pure ()

  hMain.flush
  hLarge.flush

  logInfo m!"Scanned constants:        {scanned}"
  logInfo m!"Records written:          {written}"
  logInfo m!"Decls w/ sharded expr:    {nSharded}"
  logInfo m!"Decls w/ oversized expr:  {nOversized}"
  logInfo m!"Main corpus:              {atlasOutPath}"
  logInfo m!"Large-expression shard:   {atlasLargeExprsPath}"

atlasCorpus
