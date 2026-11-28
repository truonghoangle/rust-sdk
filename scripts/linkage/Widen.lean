import Lean
open Lean

/-! The committed-only fields of the std trait instances that step 4 of
scripts/check-original-linkage.sh found equal up to fields only the committed block sets (human
decision XD2, rule (b); review finding TR4). For each such field the unmodified-source side holds
the default of the Aeneas structure (Lean fills it in), the committed side the value Aeneas
printed. scripts/linkage/compare_env.py accepts the field only if

* the two values are definitionally equal: kernel `isDefEq` in env2 (the committed translation
  with the hand-written external models of formal/trusted/Rmcp, as `lake build Rmcp RmcpExternal`
  builds it) of the committed value and of the env0 value, transported exactly (constant by
  constant, as JSON, no elaboration); the env0 value must be closed, all its constants must exist
  in env2, and no constant it reaches in env0 may be one of the listed instances (whose values
  differ between the sides); or
* no definition reachable from the unmodified-source translation (env0, its four modules, the
  externals being the generated templates) and no definition reachable from the hand-written
  external models (env2, modules Rmcp.TypesExternal and Rmcp.FunsExternal) projects the field:
  neither the projection function, nor `Expr.proj` at the field's index, nor an eliminator of the
  structure (its recursor, `casesOn` and the other auxiliary recursors, `noConfusionType` and
  `noConfusion`, the internal `_sizeOf_…` functions; a `match` on it) occurs in it. The structure's own generated
  declarations are not counted as uses.

The definitional-equality check is done in env2 and not in env1 because a committed field may name
an external function (`assert_fields_are_eq := String.Insts.CoreCmpEq.assert_fields_are_eq`),
an axiom of the template but a definition of the hand-written models. Transporting the env0 value
is sound because its constants are library constants or unmodified-source translation constants,
which step 5 shows elaborate identically on both sides, and none reaches a listed instance.

Modes (each run with `lake env lean --run` in the environment named):

* `export <fields.json> <out.json>` (env0): for each listed instance and field, the structure, the
  field index, the env0 value as a JSON tree, whether it is closed (the instance has no
  parameters), whether a constant it reaches is a listed instance, and the env0 definitions that
  project the field (count and the first five).
* `committed <export.json> <out.json>` (env2): for each, whether the transported env0 value is
  definitionally equal to the committed value (with the reason if not), and the definitions
  reachable from the external models that project the field.

Reachability follows every constant of a type or value of a definition, opaque, axiom, inductive
(its constructors), constructor (its inductive) and recursor (its rules), from all constants of
the root modules; theorems are neither followed nor inspected (a proof determines no value).
Stated limit: code outside both environments (the specs and proofs of formal/, downstream users)
is not inspected; it sees the committed values. -/

/-! ### Expressions as JSON (exact, no elaboration) -/

def nameJ : Name → Json
  | .anonymous => Json.arr #[]
  | .str p s => match nameJ p with
    | Json.arr a => Json.arr (a.push (Json.str s)) | j => j
  | .num p k => match nameJ p with
    | Json.arr a => Json.arr (a.push (toJson k)) | j => j

def nameOfJ (j : Json) : Except String Name := do
  let .arr a := j | throw "name: not an array"
  a.foldlM (init := Name.anonymous) fun n c => match c with
    | Json.str s => pure (Name.str n s)
    | Json.num k => match k.mantissa.toNat? with
      | some m => if k.exponent == 0 then pure (Name.num n m) else throw "name: bad number"
      | none => throw "name: bad number"
    | _ => throw "name: bad component"

partial def levelJ : Level → Except String Json
  | .zero => pure (Json.arr #["z"])
  | .succ l => do pure (Json.arr #["s", ← levelJ l])
  | .max a b => do pure (Json.arr #["m", ← levelJ a, ← levelJ b])
  | .imax a b => do pure (Json.arr #["i", ← levelJ a, ← levelJ b])
  | .param n => pure (Json.arr #["p", nameJ n])
  | .mvar _ => throw "level metavariable"

partial def levelOfJ (j : Json) : Except String Level := do
  let .arr a := j | throw "level: not an array"
  let tag ← match a[0]? with | some (Json.str t) => pure t | _ => throw "level: no tag"
  match tag, a.size with
  | "z", 1 => pure .zero
  | "s", 2 => pure (.succ (← levelOfJ a[1]!))
  | "m", 3 => pure (.max (← levelOfJ a[1]!) (← levelOfJ a[2]!))
  | "i", 3 => pure (.imax (← levelOfJ a[1]!) (← levelOfJ a[2]!))
  | "p", 2 => pure (.param (← nameOfJ a[1]!))
  | _, _ => throw "level: bad tag"

def biJ : BinderInfo → String
  | .default => "d" | .implicit => "i" | .strictImplicit => "s" | .instImplicit => "c"

def biOfJ : String → Except String BinderInfo
  | "d" => pure .default | "i" => pure .implicit | "s" => pure .strictImplicit
  | "c" => pure .instImplicit | _ => throw "binder info: bad tag"

/-- Metadata is dropped (it does not change definitional equality); free variables and
metavariables cannot occur in a closed value and fail. -/
partial def exprJ : Expr → Except String Json
  | .bvar i => pure (Json.arr #["b", toJson i])
  | .sort l => do pure (Json.arr #["S", ← levelJ l])
  | .const n ls => do pure (Json.arr #["c", nameJ n, Json.arr (← ls.toArray.mapM levelJ)])
  | .app f a => do pure (Json.arr #["a", ← exprJ f, ← exprJ a])
  | .lam _ t b bi => do pure (Json.arr #["l", ← exprJ t, ← exprJ b, Json.str (biJ bi)])
  | .forallE _ t b bi => do pure (Json.arr #["f", ← exprJ t, ← exprJ b, Json.str (biJ bi)])
  | .letE _ t v b nd => do pure (Json.arr #["e", ← exprJ t, ← exprJ v, ← exprJ b, toJson nd])
  | .lit (.natVal k) => pure (Json.arr #["n", Json.str (toString k)])
  | .lit (.strVal s) => pure (Json.arr #["t", Json.str s])
  | .mdata _ e => exprJ e
  | .proj s i e => do pure (Json.arr #["j", nameJ s, toJson i, ← exprJ e])
  | .fvar _ => throw "free variable"
  | .mvar _ => throw "metavariable"

partial def exprOfJ (j : Json) : Except String Expr := do
  let .arr a := j | throw "expr: not an array"
  let nat (x : Json) : Except String Nat := match x.getNat? with
    | .ok k => pure k | .error e => throw e
  let tag ← match a[0]? with | some (Json.str t) => pure t | _ => throw "expr: no tag"
  match tag, a.size with
  | "b", 2 => pure (.bvar (← nat a[1]!))
  | "S", 2 => pure (.sort (← levelOfJ a[1]!))
  | "c", 3 => do
      let .arr ls := a[2]! | throw "expr: levels"
      pure (.const (← nameOfJ a[1]!) (← ls.toList.mapM levelOfJ))
  | "a", 3 => pure (.app (← exprOfJ a[1]!) (← exprOfJ a[2]!))
  | "l", 4 => do
      let .str bi := a[3]! | throw "expr: binder info"
      pure (.lam `x (← exprOfJ a[1]!) (← exprOfJ a[2]!) (← biOfJ bi))
  | "f", 4 => do
      let .str bi := a[3]! | throw "expr: binder info"
      pure (.forallE `x (← exprOfJ a[1]!) (← exprOfJ a[2]!) (← biOfJ bi))
  | "e", 5 => do
      let nd ← match a[4]! with | .bool b => pure b | _ => throw "expr: let flag"
      pure (.letE `x (← exprOfJ a[1]!) (← exprOfJ a[2]!) (← exprOfJ a[3]!) nd)
  | "n", 2 => do
      let .str s := a[1]! | throw "expr: nat literal"
      let some k := s.toNat? | throw "expr: nat literal"
      pure (.lit (.natVal k))
  | "t", 2 => do
      let .str s := a[1]! | throw "expr: string literal"
      pure (.lit (.strVal s))
  | "j", 4 => pure (.proj (← nameOfJ a[1]!) (← nat a[2]!) (← exprOfJ a[3]!))
  | _, _ => throw "expr: bad tag"

/-! ### The listed fields -/

def mods : List Name := [`Rmcp.TypesExternal, `Rmcp.Types, `Rmcp.FunsExternal, `Rmcp.Funs]

def modOf (env : Environment) (n : Name) : Name :=
  match env.getModuleIdxFor? n with
  | some i => env.header.moduleNames[i.toNat]!
  | none => .anonymous

/-- The structure constructor application under the leading `fun` binders of the value of the
definition `n`: (number of binders, constructor info, arguments). -/
partial def ctorApp (env : Environment) (n : Name) : Except String (Nat × ConstructorVal × Array Expr) := do
  let some (.defnInfo v) := env.find? n | throw s!"{n} is no definition"
  let rec strip (k : Nat) : Expr → Nat × Expr
    | .lam _ _ b _ => strip (k + 1) b
    | .mdata _ e => strip k e
    | e => (k, e)
  let (k, e) := strip 0 v.value
  let .const c _ := e.getAppFn | throw s!"{n}: value is no constructor application"
  let some (.ctorInfo cv) := env.find? c | throw s!"{n}: {c} is no constructor"
  let some _ := getStructureInfo? env cv.induct | throw s!"{n}: {cv.induct} is no structure"
  return (k, cv, e.getAppArgs)

/-- The field `f` of the instance `n`: structure, field index, number of binders, value. -/
def fieldOf (env : Environment) (n : Name) (f : String) :
    Except String (Name × Nat × Nat × Expr) := do
  let (k, cv, args) ← ctorApp env n
  let fields := getStructureFields env cv.induct
  let some i := fields.idxOf? (Name.mkSimple f) | throw s!"{n}: {cv.induct} has no field {f}"
  let some v := args[cv.numParams + i]? | throw s!"{n}: constructor not fully applied"
  return (cv.induct, i, k, v)

/-! ### Reachability and projections -/

/-- The expressions of a constant that reachability follows (theorems: none). -/
def exprsOf (env : Environment) : ConstantInfo → Array Expr
  | .thmInfo _ => #[]
  | .defnInfo v => #[v.type, v.value]
  | .opaqueInfo v => #[v.type, v.value]
  | .inductInfo v => #[v.type] ++ v.ctors.toArray.filterMap fun c => (env.find? c).map (·.type)
  | .recInfo v => #[v.type] ++ v.rules.toArray.map (·.rhs)
  | ci => #[ci.type]

/-- The constants reached from the roots (the roots included); theorems are not followed. -/
partial def reach (env : Environment) (roots : Array Name) : NameSet := Id.run do
  let mut seen : NameSet := {}
  let mut todo := roots.toList
  while true do
    match todo with
    | [] => break
    | n :: rest =>
      todo := rest
      if seen.contains n then continue
      seen := seen.insert n
      let some ci := env.find? n | continue
      let mut next : Array Name := #[]
      match ci with
      | .ctorInfo v => next := next.push v.induct
      | _ => pure ()
      for e in exprsOf env ci do
        next := next ++ e.getUsedConstants
      for m in next do
        if !seen.contains m then todo := m :: todo
  return seen

/-- Names of the eliminators Lean generates for an inductive type `s` (as `s.<x>`) or for its
constructor (as `s.mk.<x>`). -/
def elimSuffixes : List String :=
  ["rec", "casesOn", "recOn", "brecOn", "binductionOn", "below", "ibelow", "noConfusionType",
   "noConfusion", "ctorIdx", "toCtorIdx", "ctorElim", "ctorElimType"]

/-- The eliminators of the structure `s` that Lean generates with it: named `s.<x>` or
`s.mk.<x>` (its constructor), its recursor and auxiliary recursors (`casesOn`, `recOn`,
`brecOn`, …), `noConfusionType` and `noConfusion`, and the internal `_sizeOf_…` functions. -/
def isElim (env : Environment) (s n : Name) : Bool :=
  let ctor := (getStructureCtor env s).name
  (n.getPrefix == s || n.getPrefix == ctor) &&
    (isAuxRecursor env n || isNoConfusion env n || n.isInternal ||
      match n with | .str _ x => elimSuffixes.contains x | _ => false)

/-- A projection function of the structure `s` (any field). -/
def isProjOf (env : Environment) (s n : Name) : Bool :=
  match env.getProjectionFnInfo? n with
  | some info => match env.find? info.ctorName with
    | some (.ctorInfo cv) => cv.induct == s
    | _ => false
  | none => false

/-- Whether `e` projects field `i` (projection function `pf`) of structure `s`: `Expr.proj` at
that index, the projection function, or one of the structure's eliminators (a `match` or
`casesOn` on it can read every field). -/
def projects (env : Environment) (e : Expr) (s : Name) (i : Nat) (pf : Name) : Bool :=
  (e.find? fun x => match x with
    | .proj s' i' _ => s' == s && i' == i
    | .const n _ => n == pf || isElim env s n
    | _ => false).isSome

/-- The reached definitions (and other non-theorems) that project the field. The structure's own
generated declarations (its projection functions and eliminators) are the field and its
eliminators, not uses of them, and are not listed. -/
def projectors (env : Environment) (reached : NameSet) (s : Name) (i : Nat) (f : String) :
    Array Name := Id.run do
  let pf := s ++ Name.mkSimple f
  let mut out := #[]
  for n in reached.toArray.qsort Name.lt do
    if n == pf || isElim env s n || isProjOf env s n then continue
    let some ci := env.find? n | continue
    if (exprsOf env ci).any (projects env · s i pf) then out := out.push n
  return out

def readFields (p : String) : IO (Array (Name × Array String)) := do
  let j ← IO.ofExcept (Json.parse (← IO.FS.readFile p))
  let .obj kv := j | throw (IO.userError "fields: not an object")
  kv.toArray.mapM fun (k, v) => do
    let fs ← IO.ofExcept (fromJson? (α := Array String) v)
    pure (k.toName, fs)

def load (m : Name) : IO Environment := do
  initSearchPath (← findSysroot)
  importModules #[{ module := m }] {} (loadExts := true)

def rootsOf (env : Environment) (ms : List Name) : Array Name :=
  env.constants.map₁.toList.toArray.filterMap fun (n, _) =>
    if ms.contains (modOf env n) then some n else none

def projJ (env : Environment) (reached : NameSet) (s : Name) (i : Nat) (f : String) : Json :=
  let ps := projectors env reached s i f
  Json.mkObj [("count", toJson ps.size), ("first", toJson ((ps.toList.take 5).map toString))]

def exportMode (fieldsPath out : String) : IO Unit := do
  let env ← load `Rmcp.Funs
  let fields ← readFields fieldsPath
  let listed : NameSet := fields.foldl (fun s (n, _) => s.insert n) {}
  let reached := reach env (rootsOf env mods)
  let mut res : Array (String × Json) := #[]
  for (n, fs) in fields do
    let mut per : Array (String × Json) := #[]
    for f in fs do
      let (s, i, k, v) ← IO.ofExcept (fieldOf env n f)
      let closed := k == 0 && !v.hasLooseBVars && !v.hasFVar && !v.hasMVar && !v.hasLevelParam
      let vj := if closed then (exprJ v).toOption else none
      let viaListed := (reach env v.getUsedConstants).toList.any listed.contains
      per := per.push (f, Json.mkObj [("struct", toString s), ("index", toJson i),
        ("closed", toJson (closed && vj.isSome)), ("value", vj.getD Json.null),
        ("reaches_listed", toJson viaListed), ("env0_projectors", projJ env reached s i f)])
    res := res.push (n.toString, Json.mkObj per.toList)
  IO.FS.writeFile out (Json.mkObj res.toList).compress

/-- In env2 (the committed translation with the hand-written externals, as `lake build Rmcp
RmcpExternal` builds it): for each listed field, whether the transported env0 value is
definitionally equal to the committed value, and the definitions reachable from the external
models that project the field. -/
def committedMode (exportPath out : String) : IO Unit := do
  let env ← load `Rmcp.Funs
  let j ← IO.ofExcept (Json.parse (← IO.FS.readFile exportPath))
  let .obj insts := j | throw (IO.userError "export: not an object")
  let reached := reach env (rootsOf env [`Rmcp.TypesExternal, `Rmcp.FunsExternal])
  let mut res : Array (String × Json) := #[]
  for (n, per) in insts.toArray do
    let .obj per := per | throw (IO.userError "export: bad entry")
    let mut out : Array (String × Json) := #[]
    for (f, o) in per.toArray do
      let s := ((o.getObjValAs? String "struct").toOption.getD "").toName
      let some i := (getStructureFields env s).idxOf? (Name.mkSimple f)
        | throw (IO.userError s!"{s} has no field {f} in env2")
      unless some i == (o.getObjValAs? Nat "index").toOption do
        throw (IO.userError s!"field {f} of {s} has another index in env2 than in env0")
      let closed := (o.getObjValAs? Bool "closed").toOption.getD false
      let reachesListed := (o.getObjValAs? Bool "reaches_listed").toOption.getD true
      let verdict : Except String Bool := do
        unless closed do throw "the env0 value is not closed"
        if reachesListed then throw "the env0 value reaches a listed instance"
        let v0 ← exprOfJ (← o.getObjVal? "value")
        for c in v0.getUsedConstants do
          unless env.contains c do throw s!"constant {c} of the env0 value is not in env2"
        let (s', i', k, v1) ← fieldOf env n.toName f
        unless k == 0 do throw "the committed instance has parameters"
        unless s' == s && i' == i do throw "structure or field index differs"
        match Kernel.isDefEq env {} v0 v1 with
        | .ok b => pure b
        | .error _ => throw "kernel isDefEq raised an exception"
      let (d, why) := match verdict with
        | .ok b => (b, if b then "" else "not definitionally equal")
        | .error e => (false, e)
      out := out.push (f, Json.mkObj [("struct", toString s), ("index", toJson i),
        ("defeq", toJson d), ("reason", toJson why),
        ("ext_projectors", projJ env reached s i f)])
    res := res.push (n, Json.mkObj out.toList)
  IO.FS.writeFile out (Json.mkObj res.toList).compress

def main (args : List String) : IO Unit := do
  unsafe enableInitializersExecution
  match args with
  | ["export", f, o] => exportMode f o
  | ["committed", e, o] => committedMode e o
  | _ => throw (IO.userError "usage: Widen.lean export <fields.json> <out.json> | committed <export.json> <out.json>")
