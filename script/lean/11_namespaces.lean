import Mathlib

/-!
# 11 — Namespace / theory-structure substrate

A declaration's *namespace* (derived from the segments of its `Name`) is a
different axis from its source *module* (the file it was defined in, obtained
from the environment in 05/07). A namespace can span many modules and a module
can host many namespaces; a mathematical "theory" is a still-higher, inferred
notion. Script 11 builds the deterministic substrate for that later inference:

* `data/atlas_namespaces.jsonl` — every namespace node that occurs (the prefix
  of some declaration, with all ancestor nodes materialised) as a tree: parent,
  depth, top-level segment, direct declaration count by kind, Mathlib count,
  and the number of distinct source modules contributing directly;
* `data/atlas_namespace_modules.jsonl` — the many-to-many incidence: one row per
  (namespace, module) that contains declarations, with counts by kind. This is
  what lets downstream analysis measure (and eventually cluster across) the
  namespace/module mismatch instead of assuming they coincide.

The root namespace (top-level declarations such as `instSemiringNat`) is emitted
as the node with name "". Private declarations are stored under mangled
`_private.<module>.<hash>.<name>` internal names; these are normalised back with
`Lean.privateToUserName?` (verified to recover 100% of private names) before the
namespace is derived, so the tree reflects user-facing names.

Run (Windows, no WSL) from the repository root:
    lake env lean script\lean\11_namespaces.lean
-/

open Lean
open Lean.Elab
open Lean.Elab.Command

def atlasNamespacesPath : String := "data/atlas_namespaces.jsonl"
def atlasNsModulePath : String := "data/atlas_namespace_modules.jsonl"
def atlasLimit : Option Nat := .none

def atlasModuleOf (env : Environment) (name : Name) : Option Name := do
  let idx ← env.getModuleIdxFor? name
  env.header.moduleNames[idx.toNat]?

/-- Exhaustive ConstantInfo kind classifier. -/
def kindOf : ConstantInfo → String
  | .axiomInfo _   => "axiom"
  | .defnInfo _    => "definition"
  | .opaqueInfo _  => "opaque"
  | .thmInfo _     => "theorem"
  | .quotInfo _    => "quotient"
  | .inductInfo _  => "inductive"
  | .ctorInfo _    => "constructor"
  | .recInfo _     => "recursor"

/-- Mutable aggregate counts shared by namespace nodes and (ns,module) pairs. -/
structure Stat where
  nDecls : Nat := 0
  nMathlib : Nat := 0
  kinds : Std.HashMap String Nat := {}

def statBump (s : Stat) (kind : String) (mathlib : Bool) : Stat :=
  { s with
      nDecls := s.nDecls + 1,
      nMathlib := s.nMathlib + (if mathlib then 1 else 0),
      kinds := s.kinds.insert kind (s.kinds.getD kind 0 + 1) }

/-- A namespace node: its aggregate stat plus the set of contributing modules
    and the set of child namespaces (for the reverse summary). -/
structure NsNode where
  stat : Stat := {}
  mods : Std.HashSet Name := {}

/-- Insert every missing ancestor of `ns` (including the anonymous root). -/
partial def ensureAncestors (m : Std.HashMap Name NsNode) (ns : Name) :
    Std.HashMap Name NsNode :=
  if m.contains ns then m
  else
    let m := m.insert ns {}
    if ns == Name.anonymous then m else ensureAncestors m ns.getPrefix

def nameStr (n : Name) : String :=
  if n == Name.anonymous then "" else n.toString

/-- Recover the user-facing name of a `_private.<module>.<hash>.<name>` mangled
    private declaration; other names pass through. -/
def userDisplayName (n : Name) : Name :=
  (Lean.privateToUserName? n).getD n

/-- Render a kind-count map as a JSON object. -/
def kindsJson (k : Std.HashMap String Nat) : Json :=
  let arr := k.toList.foldl (fun a (k, v) => a.push (k, toJson v)) #[]
  Json.mkObj arr.toList

elab "atlasNamespaces" : command => do
  let env ← getEnv
  let hNs ← IO.FS.Handle.mk atlasNamespacesPath IO.FS.Mode.write
  let hPair ← IO.FS.Handle.mk atlasNsModulePath IO.FS.Mode.write

  let mut nsMap : Std.HashMap Name NsNode := {}
  let mut pairMap : Std.HashMap (Name × Name) Stat := {}
  let mut modNs : Std.HashMap Name (Std.HashSet Name) := {}
  let mut scanned : Nat := 0

  for (name, ci) in env.constants.toList do
    let underCap : Bool :=
      match atlasLimit with
      | some lim => scanned < lim
      | none     => true
    if !underCap then break else pure ()
    scanned := scanned + 1

    let ns := (userDisplayName name).getPrefix
    let kind := kindOf ci
    let mod? := atlasModuleOf env name
    let isMathlib : Bool :=
      match mod? with
      | some m => m.toString.startsWith "Mathlib"
      | none   => false

    nsMap := ensureAncestors nsMap ns
    let node := nsMap.getD ns {}
    let mut mods := node.mods
    match mod? with
    | some m => mods := mods.insert m
    | none   => pure ()
    nsMap := nsMap.insert ns { node with stat := statBump node.stat kind isMathlib,
                                          mods := mods }

    match mod? with
    | some m =>
        let key := (ns, m)
        pairMap := pairMap.insert key (statBump (pairMap.getD key {}) kind isMathlib)
        let set := (modNs.getD m {}).insert ns
        modNs := modNs.insert m set
    | none => pure ()

  ---------------------------------------------------------------------------
  -- Write namespace nodes.
  ---------------------------------------------------------------------------
  let mut nodesWritten : Nat := 0
  let mut multiModuleNs : Nat := 0
  let mut maxModules : Nat := 0
  let mut maxModulesName : Name := Name.anonymous
  for (ns, node) in nsMap.toList do
    let parentJson : Json :=
      if ns == Name.anonymous then Json.null
      else Json.str (nameStr ns.getPrefix)
    let row := Json.mkObj [
      ("name", Json.str (nameStr ns)),
      ("parent", parentJson),
      ("depth", toJson ns.getNumParts),
      ("root", Json.str (nameStr ns.getRoot)),
      ("nDecls", toJson node.stat.nDecls),
      ("nMathlib", toJson node.stat.nMathlib),
      ("nModules", toJson node.mods.size),
      ("kinds", kindsJson node.stat.kinds)
    ]
    hNs.putStrLn row.compress
    nodesWritten := nodesWritten + 1
    if node.mods.size > 1 then multiModuleNs := multiModuleNs + 1 else pure ()
    if node.mods.size > maxModules then
      maxModules := node.mods.size
      maxModulesName := ns
    else pure ()

  ---------------------------------------------------------------------------
  -- Write (namespace, module) incidence rows.
  ---------------------------------------------------------------------------
  let mut pairsWritten : Nat := 0
  for ((ns, m), st) in pairMap.toList do
    let isMathlib : Bool := m.toString.startsWith "Mathlib"
    let row := Json.mkObj [
      ("namespace", Json.str (nameStr ns)),
      ("module", Json.str m.toString),
      ("mathlib", toJson isMathlib),
      ("nDecls", toJson st.nDecls),
      ("nMathlib", toJson st.nMathlib),
      ("kinds", kindsJson st.kinds)
    ]
    hPair.putStrLn row.compress
    pairsWritten := pairsWritten + 1
  hNs.flush; hPair.flush

  let mut multiNsModules : Nat := 0
  for (_, set) in modNs.toList do
    if set.size > 1 then multiNsModules := multiNsModules + 1 else pure ()

  logInfo m!"Constants scanned:      {scanned}"
  logInfo m!"Namespace nodes:         {nodesWritten} (incl. anonymous root)"
  logInfo m!"(namespace,module) rows: {pairsWritten}"
  logInfo m!"namespaces spanning >1 module: {multiModuleNs} (max {maxModules} at {maxModulesName})"
  logInfo m!"modules hosting >1 namespace: {multiNsModules} (of {modNs.size} modules)"
  logInfo m!"Namespaces output: {atlasNamespacesPath}"
  logInfo m!"Incidence output:  {atlasNsModulePath}"

atlasNamespaces
