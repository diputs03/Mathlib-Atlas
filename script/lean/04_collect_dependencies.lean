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

partial def collectNames (e : Expr) : Array Name :=
  match e with
  | .bvar _ =>
      #[]

  | .fvar _ =>
      #[]

  | .mvar _ =>
      #[]

  | .sort _ =>
      #[]

  | .const name _ =>
      #[name]

  | .app fn arg =>
      collectNames fn ++ collectNames arg

  | .lam _ binderType body _ =>
      collectNames binderType ++ collectNames body

  | .forallE _ binderType body _ =>
      collectNames binderType ++ collectNames body

  | .letE _ type value body _ =>
      collectNames type ++
      collectNames value ++
      collectNames body

  | .lit _ =>
      #[]

  | .mdata _ body =>
      collectNames body

  | .proj _ _ body =>
      collectNames body

elab "atlasDeps " declName:ident : command => do
  let env ← getEnv
  let name := declName.getId

  match env.find? name with
  | none =>
      logInfo m!"Declaration not found: {name}"

  | some info =>
      let deps := collectNames info.type

      logInfo m!"Declaration: {name}"
      logInfo m!"Kind: {atlasConstantKind info}"
      logInfo m!"Type: {info.type}"
      logInfo m!"Type dependencies: {deps.size}"

      for dep in deps do
        logInfo m!"  {dep}"

atlasDeps Nat.one_mem_properDivisors_iff_one_lt
