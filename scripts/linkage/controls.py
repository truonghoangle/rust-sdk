"""Positive and negative controls of the XD2 rules of scripts/check-original-linkage.sh (human
decision XD2, 2026-11-28; review findings TR4 and TR10 of the patch-08 translation round 1).

Usage: python3 -I scripts/linkage/controls.py <linkage-dir> <controls-dir>
  <linkage-dir>   the scratch directory of a passing run of scripts/check-original-linkage.sh on
                  the current commit (out/Rmcp, env0 and env1 dumps, instance-fields.json and the
                  Widen.lean results); not modified.
  <controls-dir>  outside the repository; new, empty, or an earlier run's (marker
                  .rmcp-linkage-controls). Every case writes only below it.

Three groups, each case with its expected outcome (exit status and a message):
 A. the text step (step 4, the Python of check-original-linkage.sh, extracted from the script, so
    the controls test the code that runs), on copies of the unmodified-source and committed
    translations with one edit: the binder rule XD2(a) (`let`, `let mut`, `have`, named argument
    `(x :=`, structure-instance fields; a value, a type or an application before `:=` stays a
    lookup) and the instance rule XD2(b);
 B. compare_env.py on the dumps and Widen.lean results of the run, edited: the instance exception
    of step 5 and the TR4 rule (definitionally equal, or projected by nothing);
 C. Widen.lean end to end on a synthetic translation built with make_env.py (three environments
    as in step 5): a committed-only field that is definitionally equal (passes), one that differs
    but is projected by nothing (passes), and ones projected by a definition of env0, by a `match`
    of env0, and by a hand-written external model only (each fails).
Exit 0 iff every case has its expected outcome."""
import json, os, re, shutil, subprocess, sys

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
LIN = os.path.join(ROOT, "scripts", "linkage")
if len(sys.argv) != 3:
    sys.exit(__doc__)
LK, CTL = (os.path.realpath(a) for a in sys.argv[1:])
for d in (LK, CTL):
    if d == ROOT or d.startswith(ROOT + os.sep) or ROOT.startswith(d + os.sep) or d in ("/", os.path.realpath(os.path.expanduser("~"))):
        sys.exit(f"[controls] error: {d} must lie outside the repository and not contain it")
if os.path.exists(CTL) and os.listdir(CTL) and not os.path.isfile(os.path.join(CTL, ".rmcp-linkage-controls")):
    sys.exit(f"[controls] error: {CTL} is not empty and has no marker .rmcp-linkage-controls")
os.makedirs(CTL, exist_ok=True)
open(os.path.join(CTL, ".rmcp-linkage-controls"), "w").close()
for need in ("out/Rmcp/Funs.lean", "env0/dump.jsonl", "env1/dump.jsonl", "instance-fields.json",
             "widen-export.json", "widen-committed.json"):
    if not os.path.isfile(os.path.join(LK, need)):
        sys.exit(f"[controls] error: {LK}/{need} missing (run scripts/check-original-linkage.sh first)")

def fresh(name):
    d = os.path.join(CTL, name)
    if os.path.isdir(d):
        shutil.rmtree(d)   # below CTL, which carries the marker
    os.makedirs(d)
    return d

results = []
def report(group, name, ok, detail):
    results.append(ok)
    print(f"[controls] {'PASS' if ok else 'FAIL'} {group} {name}: {detail}")

def outcome(r, expect):
    out = r.stdout + r.stderr
    ok = (r.returncode != 0) == (expect is not None) and (expect is None or expect in out)
    last = out.strip().splitlines()[-1][:200] if out.strip() else ""
    return ok, f"exit {r.returncode}; {last}"

# ---------------------------------------------------------------------------------------------
# A. Text step.
script = open(os.path.join(ROOT, "scripts", "check-original-linkage.sh"), encoding="utf-8").read()
m = re.search(r'^python3 -I - "\$SCR/out/Rmcp" "\$ROOT/formal/translation/Rmcp" "\$SCR/instance-fields.json" <<\'PY\'\n(.*?)^PY$',
              script, re.S | re.M)
if not m:
    sys.exit("[controls] error: the step-4 Python of check-original-linkage.sh was not found")
step4 = os.path.join(CTL, "step4.py")
open(step4, "w", encoding="utf-8").write(m.group(1))
FILES = ("Funs.lean", "Types.lean", "FunsExternal_Template.lean", "TypesExternal_Template.lean")
UNMOD, COMM = os.path.join(LK, "out", "Rmcp"), os.path.join(ROOT, "formal", "translation", "Rmcp")

def text_case(name, sides, old, new, expect):
    d = fresh("text-" + name)
    for side, src in (("unmod", UNMOD), ("comm", COMM)):
        os.makedirs(os.path.join(d, side))
        for f in FILES:
            shutil.copy(os.path.join(src, f), os.path.join(d, side, f))
    for side in sides:
        p = os.path.join(d, side, "Funs.lean")
        s = open(p, encoding="utf-8").read()
        if s.count(old) != 1:
            report("A", name, False, f"the edited text occurs {s.count(old)} times in the {side} Funs.lean")
            return
        open(p, "w", encoding="utf-8").write(s.replace(old, new))
    r = subprocess.run([sys.executable, "-I", step4, os.path.join(d, "unmod"), os.path.join(d, "comm"),
                        os.path.join(d, "w.json")], capture_output=True, text=True)
    report("A", name, *outcome(r, expect))

X34 = "def model.elicitation_schema.EnumSchemaBuilderMultiSelect.single_select"
X34B = X34 + """
  (self : model.elicitation_schema.EnumSchemaBuilder
  model.elicitation_schema.MultiSelect) :
  Result (model.elicitation_schema.EnumSchemaBuilder
    model.elicitation_schema.SingleSelect)
  := do
  ok
    {
      enum_values := self.enum_values,
      titled := self.titled,
      title := self.title,
      description := self.description,
      enum_titles := self.enum_titles,
      min_items := none,"""
OK_LINE = "  := do\n  ok\n    {\n      enum_values"
def body(line):
    """X34 with LINE inserted before its `ok` (both sides edited: the blocks stay equal)."""
    return X34B.replace(OK_LINE, "  := do\n" + line + "\n  ok\n    {\n      enum_values")
SHADOW = "`min_items` in model.elicitation_schema.EnumSchemaBuilderMultiSelect.single_select may resolve"
BOTH = ("unmod", "comm")
text_case("positive (unedited translations)", (), X34, X34, None)
# XD2(a): field names of a structure instance (the real X34) are no lookups; a value is.
text_case("a value shadowed", ("comm",), X34,
          "def model.elicitation_schema.EnumSchemaBuilderMultiSelect.none : Nat := 0\n\n" + X34,
          "`none` in model.elicitation_schema.EnumSchemaBuilderMultiSelect.single_select may resolve")
text_case("a field value changed", ("comm",), X34B, X34B.replace("min_items := none,", "min_items := self.min_items,"),
          "DIFFERS in committed Funs.lean: model.elicitation_schema.EnumSchemaBuilderMultiSelect.single_select")
text_case("a let type", ("unmod",), X34B, body("  let y : min_items := 0"), SHADOW)
text_case("a brace with a colon", ("unmod",), X34B,
          X34B.replace("    {\n      enum_values", "    {\n      x : Nat\n      enum_values"),
          "may resolve to the committed-only declaration")
# XD2(a), review finding TR10: the `let mut`, `have` and named-argument branches.
text_case("a let mut binder", BOTH, X34B, body("  let mut min_items := 0"), None)
text_case("a have binder", BOTH, X34B, body("  have min_items := 0"), None)
text_case("a have type", BOTH, X34B, body("  have h : min_items := 0"), SHADOW)
text_case("a have value", BOTH, X34B, body("  have y := min_items"), SHADOW)
text_case("a named argument", BOTH, X34B, body("  let y ← core.option.Option.unwrap_or (min_items := none) none"), None)
text_case("a named argument value", BOTH, X34B, body("  let y ← core.option.Option.unwrap_or (x := min_items) none"), SHADOW)
text_case("an application before :=", BOTH, X34B, body("  let y ← core.option.Option.unwrap_or (f min_items := none) none"), SHADOW)
text_case("a named argument inside a brace", BOTH, X34B, body("  let y ← f { x := g (min_items := none) }"), None)
text_case("a dotted name in binder position", BOTH, X34B, body("  have model.elicitation_schema.EnumSchemaBuilderMultiSelect.min_items := 0"),
          "may resolve to the committed-only declaration `model.elicitation_schema.EnumSchemaBuilderMultiSelect.min_items`")
# XD2(b): std trait instances.
text_case("b shared field changed", ("comm",),
          "  cmp := alloc.string.String.Insts.CoreCmpOrd.cmp\n  min :=",
          "  cmp := alloc.string.String.Insts.CoreCmpPartialOrdString.partial_cmp\n  min :=",
          "DIFFERS in committed Funs.lean: alloc.string.String.Insts.CoreCmpOrd")
text_case("b field only in the unmodified block", ("comm",),
          "  partialEqInst := alloc.string.String.Insts.CoreCmpPartialEqString\n  assert_fields_are_eq :=",
          "  assert_fields_are_eq :=", "DIFFERS in committed Funs.lean: alloc.string.String.Insts.CoreCmpEq")
text_case("b impl_def without a self-reference", ("comm",),
          "def alloc.string.String.Insts.CoreCmpEq : core.cmp.Eq String := {",
          "impl_def alloc.string.String.Insts.CoreCmpEq : core.cmp.Eq String := {",
          "DIFFERS in committed Funs.lean: alloc.string.String.Insts.CoreCmpEq")
text_case("b instance type changed", ("comm",),
          "impl_def alloc.string.String.Insts.CoreCmpOrd : core.cmp.Ord String := {",
          "impl_def alloc.string.String.Insts.CoreCmpOrd : core.cmp.Ord Str := {",
          "DIFFERS in committed Funs.lean: alloc.string.String.Insts.CoreCmpOrd")
text_case("b committed-only instance field naming another function", ("comm",),
          "  clone := alloc.string.String.Insts.CoreCloneClone.clone\n",
          "  clone := alloc.string.String.Insts.CoreCmpOrd.cmp\n",
          "may resolve to the committed-only declaration `alloc.string.String.Insts.CoreCloneClone`")

# ---------------------------------------------------------------------------------------------
# B. compare_env.py on the run's dumps and Widen.lean results.
CMP = os.path.join(LIN, "compare_env.py")
D0, D1 = os.path.join(LK, "env0", "dump.jsonl"), os.path.join(LK, "env1", "dump.jsonl")
W = json.load(open(os.path.join(LK, "instance-fields.json")))
E = json.load(open(os.path.join(LK, "widen-export.json")))
C = json.load(open(os.path.join(LK, "widen-committed.json")))
lines1 = open(D1, encoding="utf-8").read().splitlines()
ORD, EQ = "rmcp.alloc.string.String.Insts.CoreCmpOrd", "rmcp.alloc.string.String.Insts.CoreCmpEq"

def dump_edit(field):
    out = []
    for l in lines1:
        o = json.loads(l)
        if o.get("c") == ORD:
            sp = o["spine"]; i = sp["nparams"] + sp["fields"].index(field)
            sp["args"][i] += " changed"; o["body"] = "changed " + o["body"]
            l = json.dumps(o)
        out.append(l)
    return out

def cmp_case(name, d1, w, e, c, expect, also=None):
    d = fresh("cmp-" + name.replace(" ", "-"))
    p1 = os.path.join(d, "d1.jsonl")
    open(p1, "w").write("\n".join(d1) + "\n")
    args = [D0, p1]
    for x, fn in ((w, "w.json"), (e, "e.json"), (c, "c.json")):
        if x is None:
            break
        json.dump(x, open(os.path.join(d, fn), "w")); args.append(os.path.join(d, fn))
    r = subprocess.run([sys.executable, "-I", CMP] + args, capture_output=True, text=True)
    ok, detail = outcome(r, expect)
    if also and also not in r.stdout + r.stderr:
        ok, detail = False, f"missing {also!r}; " + detail
    report("B", name, ok, detail)

def with_c(f, **kv):
    c = json.loads(json.dumps(C)); c[ORD][f].update(kv); return c
def with_e(f, **kv):
    e = json.loads(json.dumps(E)); e[ORD][f].update(kv); return e
cmp_case("positive (the run)", lines1, W, E, C, None, "2 std trait instance(s) equal up to committed-only fields")
cmp_case("no instance list", lines1, {}, None, None, f"{ORD}: body differs")
cmp_case("shared field cmp changed", dump_edit("cmp"), W, E, C, f"{ORD}: body differs")
cmp_case("listed field min changed", dump_edit("min"), W, E, C, None)
cmp_case("wrong field listed", lines1, {**W, ORD: ["max"]}, E, C, f"{ORD}: body differs")
cmp_case("unknown instance listed", lines1, {**W, "rmcp.no.such.Inst": ["x"]}, E, C, "no constant")
# TR4: the committed-only fields.
cmp_case("TR4 results missing", lines1, W, None, None, "have no Widen.lean results")
cmp_case("TR4 results incomplete", lines1, W, {ORD: E[ORD]}, C, "results cover")
cmp_case("TR4 not defeq, projected by nothing", lines1, W, E, with_c("min", defeq=False, reason="control"),
         None, "no definition of env0 or of the external models projects")
cmp_case("TR4 not defeq, projected in env0", lines1, W,
         with_e("min", env0_projectors={"count": 1, "first": ["rmcp.control"]}),
         with_c("min", defeq=False, reason="control"), "is not definitionally equal")
cmp_case("TR4 not defeq, projected by an external model", lines1, W, E,
         with_c("min", defeq=False, reason="control", ext_projectors={"count": 2, "first": ["ExtModel.control"]}),
         "is not definitionally equal")
cmp_case("TR4 defeq, projected (accepted)", lines1, W,
         with_e("min", env0_projectors={"count": 1, "first": ["rmcp.control"]}), C, None,
         "definitionally equal to the default")
cmp_case("TR4 index differs", lines1, W, with_e("min", index=3), C, "structure or field index differs")

# ---------------------------------------------------------------------------------------------
# C. Widen.lean end to end on a synthetic translation.
HEAD = "module\npublic import Aeneas\n{imports}@[expose] public section\nopen Aeneas Aeneas.Std Result\n\nnamespace rmcp\n\n"
TYPES_EXT = HEAD.format(imports="") + "\n\n".join(
    f"structure S{k} where\n  a : Nat\n  f{k} : Nat → Result Nat := fun x => ok x" for k in range(1, 6)) + "\n\nend rmcp\n"
TYPES = HEAD.format(imports="public import Rmcp.TypesExternal\n") + "end rmcp\n"
FUNS_EXT_TEMPLATE = HEAD.format(imports="public import Rmcp.Types\n") + "end rmcp\n"
# The hand-written external models: one projects S4.f4.
FUNS_EXT_MODELS = HEAD.format(imports="public import Rmcp.Types\n") + \
    "def model4 (s : S4) : Result Nat := s.f4 0\n\nend rmcp\n"
USES = ("def uses3 (s : S3) : Result Nat := s.f3 1\n\n"
        "def uses5 (s : S5) : Nat := match s with\n  | { a := a, f5 := _ } => a\n\n")
def funs(committed):
    """Instances inst1..inst5; COMMITTED is the set of k whose field f<k> the committed side sets
    (inst1: `ok (x + 0)`, definitionally `ok x`; the others: `ok (x + 1)`)."""
    out = HEAD.format(imports="public import Rmcp.Types\npublic import Rmcp.FunsExternal\n") + USES
    for k in range(1, 6):
        v = f", f{k} := fun x => ok (x + {0 if k == 1 else 1})" if k in committed else ""
        out += f"def inst{k} : S{k} := {{ a := {k}{v} }}\n\n"
    return out + "end rmcp\n"

def build(name, funs_text, funs_ext):
    d = os.path.join(CTL, "syn-" + name)
    if os.path.isdir(d):
        shutil.rmtree(d)   # below CTL, which carries the marker
    src = fresh("syn-src-" + name)
    for fn, t in (("Types.lean", TYPES), ("Funs.lean", funs_text), ("TypesExternal.lean", TYPES_EXT),
                  ("FunsExternal.lean", funs_ext)):
        open(os.path.join(src, fn), "w").write(t)
    subprocess.run([sys.executable, "-I", os.path.join(LIN, "make_env.py"), ROOT, d] +
                   [os.path.join(src, f) for f in ("Types.lean", "Funs.lean", "TypesExternal.lean", "FunsExternal.lean")],
                   check=True)
    r = subprocess.run(["lake", "build", "Rmcp"], cwd=d, capture_output=True, text=True)
    if r.returncode != 0:
        sys.exit(f"[controls] error: synthetic environment {name} does not build:\n{r.stdout[-2000:]}{r.stderr[-2000:]}")
    return d

def lean_run(env, *args):
    subprocess.run(["lake", "env", "lean", "--run", os.path.join(LIN, args[0])] + list(args[1:]),
                   cwd=env, check=True)

ENV0 = []
def synthetic(name, committed, expect, present, absent=()):
    if not ENV0:
        ENV0.append(build("env0", funs(set()), FUNS_EXT_TEMPLATE))
    e0 = ENV0[0]
    e1 = build(name + "-env1", funs(committed), FUNS_EXT_TEMPLATE)
    e2 = build(name + "-env2", funs(committed), FUNS_EXT_MODELS)
    d = fresh("syn-run-" + name)
    fields = {f"rmcp.inst{k}": [f"f{k}"] for k in sorted(committed)}
    fp, ep, cp = (os.path.join(d, x) for x in ("fields.json", "export.json", "committed.json"))
    json.dump(fields, open(fp, "w"))
    for env, out in ((e0, "d0.jsonl"), (e1, "d1.jsonl")):
        lean_run(env, "Dump.lean", os.path.join(d, out))
    lean_run(e0, "Widen.lean", "export", fp, ep)
    lean_run(e2, "Widen.lean", "committed", ep, cp)
    r = subprocess.run([sys.executable, "-I", CMP, os.path.join(d, "d0.jsonl"), os.path.join(d, "d1.jsonl"), fp, ep, cp],
                       capture_output=True, text=True)
    out = r.stdout + r.stderr
    ok, detail = outcome(r, expect)
    miss = [p for p in present if p not in out] + [p for p in absent if p in out]
    if miss:
        ok, detail = False, f"output lacks or has {miss}; " + detail
    report("C", name, ok, detail)

synthetic("first", {1, 2, 3, 4, 5}, "elaborated difference",
          ["rmcp.inst1.f1: the committed value is definitionally equal",
           "rmcp.inst2.f2: the committed value differs from the default",
           "rmcp.inst3.f3: the committed value is not definitionally equal to the default of the unmodified side (not definitionally equal) and rmcp.S3.f3 is projected by 1 definition(s) of env0 ['rmcp.uses3']",
           "rmcp.inst4.f4: the committed value is not definitionally equal to the default of the unmodified side (not definitionally equal) and rmcp.S4.f4 is projected by 0 definition(s) of env0 [] and 1 of the external models ['rmcp.model4']",
           "rmcp.inst5.f5: the committed value is not definitionally equal"],
          ["rmcp.inst1.f1: the committed value is not", "rmcp.inst2.f2: the committed value is not"])
synthetic("positive", {1, 2}, None,
          ["rmcp.inst1.f1: the committed value is definitionally equal",
           "rmcp.inst2.f2: the committed value differs from the default",
           "2 std trait instance(s) equal up to committed-only fields"])

n_ok = sum(results)
print(f"[controls] {n_ok} of {len(results)} cases have their expected outcome")
sys.exit(0 if n_ok == len(results) else 1)
