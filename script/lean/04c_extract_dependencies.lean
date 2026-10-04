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
  | .ctorInfo _    => "constructor"
  | .recInfo _     => "recursor"

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
      logInfo m!"Declaration: {name}"
      logInfo m!"Kind: {atlasConstantKind info}"

      let typeDeps := collectNames info.type

      logInfo m!"Type dependencies: {typeDeps.size}"

      for dep in typeDeps do
        logInfo m!"  [type] {dep}"

      match info with
      | .defnInfo val =>
          let valueDeps := collectNames val.value

          logInfo m!"Value dependencies: {valueDeps.size}"

          for dep in valueDeps do
            logInfo m!"  [value] {dep}"

      | .opaqueInfo val =>
          let valueDeps := collectNames val.value

          logInfo m!"Value dependencies: {valueDeps.size}"

          for dep in valueDeps do
            logInfo m!"  [value] {dep}"

      | .thmInfo val =>
          let valueDeps := collectNames val.value

          logInfo m!"Proof dependencies: {valueDeps.size}"

          for dep in valueDeps do
            logInfo m!"  [proof] {dep}"

      | _ =>
          logInfo m!"No value/proof expression available for this declaration kind."

atlasDeps Nat.one_mem_properDivisors_iff_one_lt
