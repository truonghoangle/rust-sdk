import Lean
open Lean

/-! Dump the elaborated translation of the current Lake workspace for
scripts/check-original-linkage.sh: every constant of the modules
`Rmcp.{TypesExternal,Types,FunsExternal,Funs}` that is not an auxiliary one, as one JSON object per
line (name, module, kind, universe parameters, canonical type, canonical body), and what the
translation modules export besides constants (instance and reducibility entries, and the number of
module entries of every environment extension).

For a definition whose value is a structure constructor applied to arguments, the line also
holds the canonical arguments with the field names (`spine`), so that a std trait instance can be
compared field by field (human decision XD2, 2026-11-28).

Canonical form: binder names, hygiene and metadata are dropped (de Bruijn indices stay); a reference
to an auxiliary constant of these modules (an internal name such as `_proof_3`/`_sizeOf_1`, a
matcher `match_N`, or any theorem) is replaced by its content -- a theorem by its statement (proofs
of one proposition are interchangeable), any other auxiliary by its type and value -- since Lean
numbers and shares such constants module-wide. -/

def mods : List Name := [`Rmcp.TypesExternal, `Rmcp.Types, `Rmcp.FunsExternal, `Rmcp.Funs]

def modOf (env : Environment) (n : Name) : Name :=
  match env.getModuleIdxFor? n with
  | some i => env.header.moduleNames[i.toNat]!
  | none => .anonymous

def kind : ConstantInfo → String
  | .axiomInfo _ => "axiom" | .defnInfo _ => "def" | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque" | .quotInfo _ => "quot" | .inductInfo _ => "inductive"
  | .ctorInfo _ => "ctor" | .recInfo _ => "rec"

def isAux (env : Environment) (n : Name) : Bool :=
  mods.contains (modOf env n) &&
    (n.isInternal || Meta.isMatcherCore env n ||
      match env.find? n with | some (.thmInfo _) => true | _ => false)

abbrev M := StateRefT (Std.HashMap Name String) IO

mutual
partial def canon (env : Environment) : Expr → M String
  | .bvar i => pure s!"#{i}"
  | .sort l => pure s!"Sort({l})"
  | .const n ls => do
      let lv := s!".\{{", ".intercalate (ls.map toString)}}"
      if isAux env n then pure s!"⟦{← canonAux env n}⟧{lv}" else pure s!"{n}{lv}"
  | .app f a => do pure s!"({← canon env f} {← canon env a})"
  | .lam _ t b bi => do pure s!"(fun[{repr bi}] {← canon env t} => {← canon env b})"
  | .forallE _ t b bi => do pure s!"(pi[{repr bi}] {← canon env t} -> {← canon env b})"
  | .letE _ t v b nd => do pure s!"(let[{nd}] {← canon env t} := {← canon env v}; {← canon env b})"
  | .lit (.natVal k) => pure s!"N{k}"
  | .lit (.strVal s) => pure s!"S{repr s}"
  | .mdata _ e => canon env e
  | .proj s i e => do pure s!"(proj {s} {i} {← canon env e})"
  | .fvar _ => throw (IO.userError "free variable in a closed constant")
  | .mvar _ => throw (IO.userError "metavariable in a closed constant")

partial def canonAux (env : Environment) (n : Name) : M String := do
  if let some s := (← get)[n]? then return s
  let some ci := env.find? n | throw (IO.userError s!"unknown constant {n}")
  let s ← match ci with
    | .thmInfo v => do pure s!"thm {v.levelParams} : {← canon env v.type}"
    | .defnInfo v => do pure s!"def {v.levelParams} : {← canon env v.type} := {← canon env v.value}"
    | .opaqueInfo v => do pure s!"opaque {v.levelParams} : {← canon env v.type} := {← canon env v.value}"
    | ci => do pure s!"{kind ci} {ci.levelParams} : {← canon env ci.type}"
  modify (·.insert n s)
  return s
end

/-- The leading `fun` binders (their canonical types) and the body under them. -/
partial def stripLams (env : Environment) : Expr → M (List String × Expr)
  | .lam _ t b bi => do
      let (ls, e) ← stripLams env b
      pure (s!"[{repr bi}] {← canon env t}" :: ls, e)
  | .mdata _ e => stripLams env e
  | e => pure ([], e)

/-- For a definition whose value is, under its leading `fun` binders, a constructor of a structure
applied to arguments (a trait instance, human decision XD2): the constructor, its universe levels,
the binders, the number of parameters, the field names and the canonical arguments, so that
scripts/linkage/compare_env.py can compare two such values field by field. -/
def spine (env : Environment) : ConstantInfo → M (Option Json)
  | .defnInfo v => do
      let (lams, e) ← stripLams env v.value
      let .const c ls := e.getAppFn | return none
      let some (.ctorInfo cv) := env.find? c | return none
      let some _ := getStructureInfo? env cv.induct | return none
      let args ← e.getAppArgs.toList.mapM (canon env)
      return some (Json.mkObj [("ctor", toString c), ("levels", toString ls), ("lams", toJson lams),
        ("nparams", toJson cv.numParams),
        ("fields", toJson ((getStructureFields env cv.induct).toList.map toString)),
        ("args", toJson args)])
  | _ => return none

def body (env : Environment) : ConstantInfo → M String
  | .defnInfo v => do pure s!"{← canon env v.value} safety={repr v.safety}"
  | .thmInfo _ => pure ""
  | .opaqueInfo v => do pure s!"{← canon env v.value} unsafe={v.isUnsafe}"
  | .inductInfo v => pure s!"params={v.numParams} indices={v.numIndices} all={v.all} ctors={v.ctors} rec={v.isRec} unsafe={v.isUnsafe} reflexive={v.isReflexive} nested={v.numNested}"
  | .ctorInfo v => pure s!"induct={v.induct} cidx={v.cidx} params={v.numParams} fields={v.numFields} unsafe={v.isUnsafe}"
  | .recInfo v => do
      let rs ← v.rules.mapM fun r => do pure s!"{r.ctor}/{r.nfields}/{← canon env r.rhs}"
      pure s!"all={v.all} params={v.numParams} indices={v.numIndices} motives={v.numMotives} minors={v.numMinors} k={v.k} unsafe={v.isUnsafe} rules={rs}"
  | .axiomInfo v => pure s!"unsafe={v.isUnsafe}"
  | .quotInfo _ => pure ""

def main (args : List String) : IO Unit := do
  let out := args.head!
  initSearchPath (← findSysroot)
  unsafe enableInitializersExecution
  let env ← importModules #[{ module := `Rmcp.Funs }] {} (loadExts := true)
  let h ← IO.FS.Handle.mk out .write
  let act : M Unit := do
    for (n, ci) in env.constants.map₁.toList do
      let m := modOf env n
      if mods.contains m && isAux env n then
        h.putStrLn (Json.mkObj [("aux", toString n), ("module", toString m)]).compress
      if mods.contains m && !isAux env n then
        let j := Json.mkObj [("c", toString n), ("module", toString m), ("kind", kind ci),
          ("lparams", toString ci.levelParams), ("type", ← canon env ci.type),
          ("body", ← body env ci), ("spine", (← spine env ci).getD Json.null)]
        h.putStrLn j.compress
  act.run' {}
  -- What the translation modules export besides constants (review a6-2): every instance entry
  -- (scoped or global, any priority, on any constant: class and head of its first argument), every
  -- reducibility entry, and the number of module entries of every environment extension.
  let exts ← persistentEnvExtensionsRef.get
  for m in [`Rmcp.Types, `Rmcp.Funs] do
    let some idx := env.getModuleIdx? m | throw (IO.userError s!"no module {m}")
    for entry in Meta.instanceExtension.ext.getModuleEntries env idx do
      let (scope, e) := match entry with
        | .global e => ("global", e)
        | .scoped ns e => (s!"scoped {ns}", e)
      let n := e.globalName?.getD .anonymous
      let body := ((env.find? n).map (·.type.getForallBody)).getD (.sort .zero)
      let cls := (body.getAppFn.constName?).getD .anonymous
      let arg := ((body.getAppArgs[0]?).bind (·.getAppFn.constName?)).getD .anonymous
      h.putStrLn (Json.mkObj [("inst", toString n), ("module", toString m),
        ("prio", toJson e.priority), ("kind", scope),
        ("class", toString cls), ("arg", toString arg)]).compress
    for (n, st) in reducibilityCoreExt.getModuleEntries env idx do
      h.putStrLn (Json.mkObj [("red", toString n), ("module", toString m),
        ("status", toString (repr st)), ("owner", toString (modOf env n)),
        ("aux", toJson (isAux env n))]).compress
    for e in exts do
      h.putStrLn (Json.mkObj [("ext", toString e.name), ("module", toString m),
        ("n", toJson (e.getModuleEntries env idx).size)]).compress
