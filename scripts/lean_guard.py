#!/usr/bin/env python3
"""Checks of the Lean project in formal/, called by scripts/lean-guard.sh (run with python3 -I).

  lean_guard.py fresh FORMAL        CI, first step: no FORMAL/.lake, nothing tracked by git
                                    under a .lake directory (see check_fresh).
  lean_guard.py lakefile FORMAL     formal/lean-toolchain is LEAN_TOOLCHAIN; formal/lakefile.toml
                                    has exactly the structure of plan Section 5 (see
                                    check_lakefile); no formal/lakefile.lean;
                                    formal/lake-manifest.json pins the recorded commits
                                    (see check_manifest).
  lean_guard.py sources FORMAL      banned words and constructs in the Lean sources, tracked or
                                    nested .lake paths, case variants of .lean (see check_sources).
  lean_guard.py axiom-lock LOCK GOT every trusted axiom written by lean-axiom-audit.lean (GOT)
                                    that a Defs/Proofs/Specs constant uses is in LOCK, every
                                    LOCK entry is declared, statement hashes agree (see
                                    check_axiom_lock).
  lean_guard.py native-lock LOCK GOT
                                    every native-code axiom written by lean-axiom-audit.lean
                                    (GOT) is an Aeneas toStr side condition declared in
                                    Rmcp.Types or Rmcp.Funs; those a Defs/Proofs/Specs constant
                                    uses are in LOCK (formal/trusted/native-axioms.lock), with
                                    the locked module and statement hash (see
                                    check_native_lock).
  lean_guard.py build-log FILE      the `lake build` log has a "Build completed successfully"
                                    line and no `warning:`/`error:` line.
  lean_guard.py selftest            self-tests of the two exact `sources` exemptions (generated
                                    macro-site docstrings; the one dupNamespace option), of the
                                    autoImplicit rules of `sources` and of the leanOptions rule
                                    of `lakefile` (the autoImplicit
                                    option of Rmcp and RmcpExternal).
  lean_guard.py archive PKG ARCHIVE PKG/.lake/build and the Lake release ARCHIVE hold the same
                                    regular files with the same bytes, *.hash and *.trace
                                    excepted (see check_archive).
  lean_guard.py roots FORMAL        prints the audit arguments for lean-axiom-audit.lean:
                                    the trusted modules (roots of RmcpExternal, comma-separated)
                                    on line 1, the roots of the default-target libraries on line 2.
  lean_guard.py leanpath FORMAL     prints LEAN_PATH for the audit: the package library
                                    directories of the manifest, then the project's.
  lean_guard.py buildtree FORMAL    formal/.lake/build/lib/lean holds only modules named Rmcp,
                                    Defs, Proofs, Specs or below them, and no symlink.
  lean_guard.py unpack TAR FORMAL   extracts the CI build artifact into FORMAL/.lake (only
                                    build/ and build.log; see unpack_build).

Exit status: 0 pass, 1 check failed, 2 usage or internal error.
"""
import hashlib
import json
import os
import re
import subprocess
import sys
import tarfile

if sys.version_info < (3, 11):
    sys.exit("lean_guard.py: python3 >= 3.11 is needed (tomllib)")
import tomllib  # noqa: E402


def fail(msgs):
    for m in msgs:
        print(f"[lean-guard] {m}", file=sys.stderr)
    sys.exit(1)


# ---------------------------------------------------------------------------------------
# lakefile

# The five libraries of plan Section 5: srcDir and roots are fixed; leanOptions must be
# exactly { warningAsError = true }, for Rmcp and RmcpExternal exactly LIB_OPTIONS[n] (human
# decisions XD3 and XD9, 2026-11-28: autoImplicit off for the generated code and the trusted
# models, so a name that nothing defines fails the build); no other key (no moreLeanArgs, weakLeanArgs, globs,
# extraDepTargets, precompileModules, ...).
LIBS = {
    "Rmcp": ("translation", ["Rmcp.Types", "Rmcp.Funs"]),
    "RmcpExternal": ("trusted", ["Rmcp.TypesExternal", "Rmcp.FunsExternal"]),
    "Defs": ("specs", ["Defs"]),
    "Proofs": ("proofs", ["Proofs"]),
    "Specs": ("specs", ["Specs"]),
}
LIB_FIELDS = {"name", "srcDir", "roots", "leanOptions"}
LIB_OPTIONS_DEFAULT = {"warningAsError": True}
LIB_OPTIONS = {"Rmcp": {"warningAsError": True, "autoImplicit": False},
               "RmcpExternal": {"warningAsError": True, "autoImplicit": False}}
PACKAGE_FIELDS = {"name", "defaultTargets", "require", "lean_lib"}
REQUIRE_FIELDS = {"name", "git", "rev", "subDir"}
REQUIRED_DEFAULTS = {"Defs", "Proofs", "Specs"}


# formal/lake-manifest.json: the commit of every package Lake fetches. The Aeneas entry must
# match the lakefile (url = git, inputRev = rev) and the commit of the pinned tag
# (nightly-2026.11.24-fb44cb4, formal/CONTRIBUTING.md "Pinned toolchain"); the other
# packages (Mathlib and its dependencies, inherited from the Aeneas package) must have the
# commits recorded at S03. Changing the Aeneas rev means updating this table in the same PR.
AENEAS_COMMIT = "fb44cb400eb6bfe7dce97422ebe8fa748b7e4f9b"
# formal/lean-toolchain must be exactly this line (the Lean toolchain of the pinned Aeneas
# rev, backends/lean/lean-toolchain of the bundle, copied by scripts/aeneas-install.sh).
# elan runs whatever toolchain that file names, so it is checked before any `lean`/`lake`
# runs (CI runs `sources` before installing elan). Updated in the same PR as the Aeneas rev.
LEAN_TOOLCHAIN = "leanprover/lean4:v4.36.0"
MANIFEST_PACKAGES = {
    "aeneas": ("https://github.com/AeneasVerif/aeneas", AENEAS_COMMIT),
    "mathlib": ("https://github.com/leanprover-community/mathlib4.git",
                "fc4f59e577feb1a4956671bc04ac18aaaf8cd842"),
    "plausible": ("https://github.com/leanprover-community/plausible",
                  "054b228ce0ac61d767c6e71ba73a24728f191b72"),
    "LeanSearchClient": ("https://github.com/leanprover-community/LeanSearchClient",
                         "4fb58e749ef3fc0395fe274f6cab70c2ea85f1c9"),
    "importGraph": ("https://github.com/leanprover-community/import-graph",
                    "8370c640afcd1cc3fb1cb9bf1560cc66eafee5e0"),
    "proofwidgets": ("https://github.com/leanprover-community/ProofWidgets4",
                     "2f0f3520daeac2d9310ff25b7a877a0e5cdaa203"),
    "aesop": ("https://github.com/leanprover-community/aesop",
              "66ff77cf0c4c898799e4b94d14db55f7a02d0c5a"),
    "Qq": ("https://github.com/leanprover-community/quote4",
           "ff055a2fcc835935e0ae607339b455a5f5896b4b"),
    "batteries": ("https://github.com/leanprover-community/batteries",
                  "b4b25a3886a16daacaf6615c2eea7170a6e8f458"),
    "Cli": ("https://github.com/leanprover/lean4-cli",
            "50810f72af7618bee62fe9800dc26e806c188703"),
}


def check_manifest(formal, cfg):
    """Errors for formal/lake-manifest.json against the lakefile and MANIFEST_PACKAGES."""
    errs = []
    with open(os.path.join(formal, "lake-manifest.json"), encoding="utf-8") as f:
        man = json.load(f)
    if man.get("name") != "rmcp_formal" or man.get("packagesDir") != ".lake/packages":
        errs.append("lake-manifest.json: name must be rmcp_formal and packagesDir .lake/packages")
    pkgs = man.get("packages")
    if not isinstance(pkgs, list) or not all(isinstance(e, dict) for e in pkgs):
        return errs + ["lake-manifest.json: packages is not a list of objects"]
    got = {e.get("name"): e for e in pkgs}
    if len(got) != len(pkgs) or set(got) != set(MANIFEST_PACKAGES):
        errs.append(f"lake-manifest.json: packages {sorted(map(str, got))}, expected exactly "
                    f"{sorted(MANIFEST_PACKAGES)}")
    for name, (url, rev) in MANIFEST_PACKAGES.items():
        e = got.get(name)
        if e is None:
            continue
        if e.get("type") != "git" or e.get("url") != url or e.get("rev") != rev:
            errs.append(f"lake-manifest.json: {name}: type {e.get('type')!r}, url {e.get('url')!r}, "
                        f"rev {e.get('rev')!r}; expected git, {url}, {rev}")
    req = (cfg.get("require") or [{}])[0]
    a = got.get("aeneas", {})
    if isinstance(req, dict) and (a.get("url"), a.get("inputRev"), a.get("subDir")) != (
            req.get("git"), req.get("rev"), req.get("subDir")):
        errs.append(f"lake-manifest.json: aeneas url/inputRev/subDir {a.get('url')!r}/"
                    f"{a.get('inputRev')!r}/{a.get('subDir')!r} differ from the lakefile "
                    f"{req.get('git')!r}/{req.get('rev')!r}/{req.get('subDir')!r}")
    return errs


def load_lakefile(formal):
    errs = []
    if os.path.lexists(os.path.join(formal, "lakefile.lean")):
        errs.append("formal/lakefile.lean exists (Lake would use it instead of lakefile.toml)")
    with open(os.path.join(formal, "lakefile.toml"), "rb") as f:
        cfg = tomllib.load(f)
    return cfg, errs


def check_toolchain(formal):
    """Errors for formal/lean-toolchain: its content, stripped, must be LEAN_TOOLCHAIN."""
    path = os.path.join(formal, "lean-toolchain")
    if os.path.islink(path) or not os.path.isfile(path):
        return [f"{path}: missing, or not a regular file"]
    with open(path, encoding="utf-8", errors="replace") as f:
        got = f.read().strip()
    if got != LEAN_TOOLCHAIN:
        return [f"lean-toolchain: {got!r}, expected exactly {LEAN_TOOLCHAIN!r} (lean_guard.py, LEAN_TOOLCHAIN)"]
    return []


def lib_option_errors(n, opts):
    """Errors for the leanOptions OPTS of library N: exactly LIB_OPTIONS[N] (Rmcp, RmcpExternal) or
    LIB_OPTIONS_DEFAULT (every other library); values compared with their TOML types, so
    `autoImplicit = "false"` or `warningAsError = 1` fail."""
    want = LIB_OPTIONS.get(n, LIB_OPTIONS_DEFAULT)
    if not (isinstance(opts, dict) and opts == want
            and all(type(opts[k]) is type(want[k]) for k in want)):
        shown = ", ".join(f"{k} = {str(v).lower()}" for k, v in want.items())
        return [f"lakefile.toml: library {n}: leanOptions {opts!r}, expected exactly {{ {shown} }}"]
    return []


def check_lakefile(formal):
    cfg, errs = load_lakefile(formal)
    errs += check_toolchain(formal)
    extra = set(cfg) - PACKAGE_FIELDS
    if extra:
        errs.append(f"lakefile.toml: package-level key(s) not allowed: {sorted(extra)}")
    if cfg.get("name") != "rmcp_formal":
        errs.append(f"lakefile.toml: package name {cfg.get('name')!r}, expected 'rmcp_formal'")
    reqs = cfg.get("require", [])
    if not (isinstance(reqs, list) and len(reqs) == 1 and isinstance(reqs[0], dict)):
        errs.append("lakefile.toml: expected exactly one [[require]] (aeneas)")
    else:
        r = reqs[0]
        if set(r) - REQUIRE_FIELDS:
            errs.append(f"lakefile.toml: [[require]] key(s) not allowed: {sorted(set(r) - REQUIRE_FIELDS)}")
        if (r.get("name"), r.get("git"), r.get("subDir")) != (
                "aeneas", "https://github.com/AeneasVerif/aeneas", "backends/lean"):
            errs.append("lakefile.toml: [[require]] must be aeneas from "
                        "https://github.com/AeneasVerif/aeneas, subDir backends/lean")
        if not isinstance(r.get("rev"), str) or not r.get("rev"):
            errs.append("lakefile.toml: [[require]] aeneas has no rev")
    libs = cfg.get("lean_lib", [])
    if not isinstance(libs, list):
        errs.append("lakefile.toml: lean_lib is not an array of tables")
        libs = []
    names = [lib.get("name") for lib in libs if isinstance(lib, dict)]
    if sorted(map(str, names)) != sorted(LIBS) or len(names) != len(libs):
        errs.append(f"lakefile.toml: libraries {names}, expected exactly {sorted(LIBS)}")
    for lib in libs:
        if not isinstance(lib, dict):
            continue
        n = lib.get("name")
        if set(lib) != LIB_FIELDS:
            errs.append(f"lakefile.toml: library {n}: keys {sorted(lib)}, expected exactly {sorted(LIB_FIELDS)}")
        errs += lib_option_errors(n, lib.get("leanOptions"))
        if n in LIBS:
            src, roots = LIBS[n]
            if lib.get("srcDir") != src:
                errs.append(f"lakefile.toml: library {n}: srcDir {lib.get('srcDir')!r}, expected {src!r}")
            if lib.get("roots") != roots:
                errs.append(f"lakefile.toml: library {n}: roots {lib.get('roots')!r}, expected {roots}")
    dt = cfg.get("defaultTargets")
    if not (isinstance(dt, list) and all(isinstance(t, str) for t in dt)
            and set(dt) <= set(LIBS) and REQUIRED_DEFAULTS <= set(dt)):
        errs.append(f"lakefile.toml: defaultTargets {dt!r} must be library names including "
                    f"{sorted(REQUIRED_DEFAULTS)}")
    errs += check_manifest(formal, cfg)
    if errs:
        fail(errs + ["lakefile check failed"])
    print(f"[lean-guard] lean-toolchain: {LEAN_TOOLCHAIN}")
    print(f"[lean-guard] lakefile: the five libraries of plan Section 5, each with exactly "
          f"leanOptions = {{ warningAsError = true }} (Rmcp and RmcpExternal: also autoImplicit = false); "
          f"defaultTargets {dt}")
    print(f"[lean-guard] lake-manifest.json: {len(MANIFEST_PACKAGES)} packages at the recorded "
          f"commits (aeneas {AENEAS_COMMIT[:8]}, matching the lakefile)")


def audit_roots(formal):
    cfg, errs = load_lakefile(formal)
    if errs:
        fail(errs)
    libs = {lib["name"]: lib for lib in cfg.get("lean_lib", [])}
    ext_roots = libs.get("RmcpExternal", {}).get("roots", [])
    roots = [r for t in cfg.get("defaultTargets", []) for r in libs[t]["roots"]]
    print(",".join(ext_roots) if ext_roots else "-")
    print(" ".join(roots))


def lean_path(formal):
    """Prints the library directories of the packages in formal/lake-manifest.json (in
    manifest order), then formal/.lake/build/lib/lean, ':'-separated, for LEAN_PATH."""
    with open(os.path.join(formal, "lake-manifest.json"), encoding="utf-8") as f:
        man = json.load(f)
    dirs = []
    for e in man["packages"]:
        name, sub = e["name"], e.get("subDir") or ""
        if not re.fullmatch(r"[A-Za-z0-9_-]+", name) or ".." in sub.split("/"):
            fail([f"lake-manifest.json: unexpected package name or subDir {name!r} {sub!r}"])
        dirs.append(os.path.join(formal, ".lake", "packages", name, sub, ".lake", "build", "lib", "lean"))
    dirs.append(os.path.join(formal, ".lake", "build", "lib", "lean"))
    print(":".join(os.path.normpath(d) for d in dirs))


# Module roots of this project; formal/.lake/build/lib/lean may hold nothing else (no
# Init, Lean, Lake, Mathlib, ... module that could stand in for a toolchain or package module).
PROJECT_ROOTS = ("Rmcp", "Defs", "Proofs", "Specs")


def check_build_tree(formal):
    lib = os.path.join(formal, ".lake", "build", "lib", "lean")
    if not os.path.isdir(lib) or os.path.islink(lib):
        fail([f"{lib} is missing or not a directory; run lake build first"])
    errs = []
    for e in sorted(os.listdir(lib)):
        root = e.split(".", 1)[0]
        path = os.path.join(lib, e)
        if root not in PROJECT_ROOTS or (os.path.isdir(path) and e != root):
            errs.append(f"{path}: not a module of this project ({'/'.join(PROJECT_ROOTS)})")
    for dirpath, dirnames, filenames in os.walk(lib):
        for n in dirnames + filenames:
            if os.path.islink(os.path.join(dirpath, n)):
                errs.append(f"{os.path.join(dirpath, n)}: symlink in the build output")
    if errs:
        fail(errs + ["unexpected entries in formal/.lake/build/lib/lean"])


# ---------------------------------------------------------------------------------------
# sources

ID = r"[A-Za-z0-9_'!?]"


def word(w):
    return re.compile(rf"(?<!{ID}){re.escape(w)}(?!{ID})")


# Banned in every hand-written and generated Lean file (comments and docstrings included).
WORDS_ALL = ["warningAsError", "sorry", "sorryAx", "admit", "native_decide", "bv_decide",
             "skipKernelTC", "proofAsSorry", "implemented_by", "extern", "unsafe",
             "ofReduceBool", "ofReduceNat", "trustCompiler"]
RULES_ALL = [(w, word(w)) for w in WORDS_ALL] + [
    # `decide +native`, `-native`, `(native := true)`, `{ native := true }`: the `native`
    # option of decide (kernel reduction replaced by compiled code, axiom Lean.ofReduceBool).
    ("native option (+native/-native)", re.compile(rf"(?:(?<=\s)|(?<=[(\[{{,])|^)[+-]native(?!{ID})", re.M)),
    ("native option (native :=)", re.compile(rf"(?<!{ID})(?<!\.)native\s*:=")),
]
# How `set_option NAME VALUE` is matched (Lean v4.36.0, the pinned toolchain; tried in
# formal/trusted/evidence/README.md, "Guard rules for set_option"): NAME is a dotted name whose
# components are each plain (`linter`) or «…»-quoted (`«linter»`), and no whitespace is needed
# after `set_option` or between a closing `»` and VALUE (`set_option«autoImplicit»false`); VALUE
# is the token `true` or `false` (also numerals and strings, which Bool options reject; `«false»`
# is a syntax error); a comment may stand between `set_option` and NAME and between NAME and
# VALUE.
NAME_COMP = rf"(?:«[^»]*»|{ID}+)"
OPT_NAME = rf"{NAME_COMP}(?:\.{NAME_COMP})*"
VALUE_SEP = r"(?:(?<=»)\s*|\s+)"
# Hand-written only: generated files carry `set_option linter.* false` (Aeneas emits it).
# Matches `set_option` of every option whose first name component is `linter` or `«linter»`
# (later components plain or quoted) with value `false`.
RULE_LINTER = ("set_option linter.<name> false",
               re.compile(rf"(?<!{ID})set_option\s*(?:linter|«linter»)\.{OPT_NAME}{VALUE_SEP}false(?!{ID})"))
# The options that bind unknown names as implicit variables (human decision XD3, 2026-11-28: the
# library Rmcp is built with `autoImplicit = false`, so a name the translation uses but nothing
# defines is an error; review finding TR7: this must not depend on Aeneas never emitting the
# option). Generated files: the two option names may not occur at all, as whole words (any value,
# the `in` form, «…» quoting; Aeneas emits neither). Hand-written files: `set_option` of either,
# plain or «…»-quoted, with or without whitespace after `set_option`, may only have the value
# `false` (the `in` form included), preceded by whitespace only (line breaks allowed); any other
# value, or a comment before the value, is reported (review findings TR7, TR11).
RULE_AUTOIMPLICIT_GEN = ("autoImplicit/relaxedAutoImplicit in generated code",
                         re.compile(rf"(?<!{ID})(?:autoImplicit|relaxedAutoImplicit)(?!{ID})"))
RULE_AUTOIMPLICIT_ON = ("set_option autoImplicit/relaxedAutoImplicit other than false",
                        re.compile(rf"(?<!{ID})set_option\s*(?:«(?:autoImplicit|relaxedAutoImplicit)»"
                                   rf"|(?:autoImplicit|relaxedAutoImplicit)(?!{ID}))"
                                   rf"(?!\s*false(?!{ID}))"))
# All files (generated included): no comment (`--`, `/-`, `/--`) anywhere between `set_option` and
# its value, i.e. after `set_option` or after the option name (plain or quoted components), so that
# neither RULE_LINTER nor the autoImplicit rules can be evaded by a comment (review findings TR7,
# TR12). A comment after the value is not matched.
RULE_SETOPT_COMMENT = ("comment between set_option and its value",
                       re.compile(rf"(?<!{ID})set_option\s*(?:{OPT_NAME}\s*)?(?:/-|--)"))
# Every hand-written file (trusted/ included) and the generated files: what runs code at
# elaboration time (during `lake build`) or changes the environment or options from a
# metaprogram. Such code could add declarations without a kernel check (caught by the replay
# in `axioms`), but also rewrite sources or build outputs while the build runs, which no later
# check of the build output can detect (formal/README.md, "What CI checks"). None of it is
# needed in specs, definitions, proofs or externals.
#
# META_WORDS was derived from the pinned toolchain and packages (the S03 evidence (git history at 223ff12),
# fix round 5, W1): every syntax kind whose registered elaborator or macro reaches, through
# constant bodies, `implemented_by` and `_unsafe_rec`, an evaluation primitive
# (Environment.evalConst/evalConstCheck, Meta.evalExpr(')/Term.evalTerm, elabEvalCoreUnsafe,
# IO.Process.spawn/output/run, loadDynlib), or whose macro builds syntax of such a kind, over
# all 8929 built modules of Lean, Lake, Mathlib, Aeneas and the other manifest packages; then
# the keyword of each kind (`#` commands are covered by HASH_CMD). Kinds that only evaluate
# declarations registered through an attribute are covered by ATTR_ALLOWED. Not banned
# (accepted residual, human decision 2026-11-22): tactics whose configuration or rule clauses
# are compiled and run (linarith/nlinarith, aesop and its wrappers, saturate/forward, Aeneas
# step/progress); `discharger` and `preprocessors` (the code-valued linarith fields) are banned.
# Matching is on whole tokens, as Lean tokenizes: a word is hit unless preceded or followed by
# an identifier character (letters, digits, `_`, `'`, `!`, `?`), so `by_elab` must be listed
# itself and `my_elaborate`, `elab_as_elim` or `List.drop` are not hit by `elab`.
META_WORDS = [
    # core: commands, terms and tactics that evaluate code
    "run_cmd", "run_tac", "run_elab", "run_meta", "by_elab", "include_str", "test_extern",
    "register_error_explanation", "show_panel_widgets", "with_panel_widgets", "bv_check",
    "bv_decide?", "autoParam",
    # core: declaring syntax, elaborators, macros, initialisers, options, simprocs
    "elab", "elab_rules", "initialize", "builtin_initialize", "macro", "macro_rules", "syntax",
    "simproc", "dsimproc", "simproc_decl", "builtin_simproc", "register_option",
    "register_simp_attr", "declare_syntax_cat", "declare_simp_like_tactic",
    # Mathlib, Batteries, Qq, Plausible, ProofWidgets, Aeneas
    "eval%", "trace", "success_if_fail_with_msg", "pi_lower_bound", "pi_upper_bound",
    "lrat_proof", "from_lrat", "run_conv", "run_tacq", "by_elabq", "plausible", "bv_tac",
    "initialize_simps_projections", "initialize_simps_projections?", "discharger",
    "preprocessors",
    # environment and option changes from metaprograms
    "addDecl", "addAndCompile", "modifyEnv", "setEnv", "withOptions",
    # the monads and types metaprograms are written in, and the namespace Lean.Elab
    # (also as `Elab` after `open Lean`)
    "IO", "EIO", "BaseIO", "CoreM", "MetaM", "TermElabM", "TacticM", "CommandElabM", "MacroM",
    "SimpM", "DelabM", "CommandElab", "TermElab", "Elab",
]


def meta_word(w):
    # `trace` is the Mathlib tactic; `set_option trace.<class>` stays allowed.
    if w == "trace":
        return re.compile(rf"(?<!{ID})(?<!\.)trace(?!{ID})(?!\.)")
    if w.endswith("%"):
        return re.compile(rf"(?<!{ID}){re.escape(w)}")
    return word(w)


RULES_META = [(w, meta_word(w)) for w in META_WORDS] + [
    ("Lean.Elab", re.compile(rf"(?<!{ID})Lean\.Elab(?!{ID})")),
    # Options under `debug.` (debug.skipKernelTC, debug.proofAsSorry, ...).
    ("debug.<option>", re.compile(rf"(?<!{ID})debug\.")),
]

# `#` commands: every one except these is banned. `#eval`, `#guard`, `#assert` (Aeneas),
# `#register_spec_info` (Aeneas), `#test`/`#sample` (Plausible), `#exit`, `#leansearch`, ...
# run code or have side effects; none is needed outside specs/Drafts/. `#guard_msgs` is
# further restricted by GUARD/GUARD_OK; `#check` and `#print` only elaborate and print.
HASH_CMD = re.compile(r"(?<![A-Za-z0-9_'!?.)\]}])#[A-Za-z_][A-Za-z0-9_'!?]*")
HASH_ALLOWED = {"#check", "#print", "#guard_msgs"}

# Attributes: every one except these is banned (in `@[...]` and `attribute [...]`, after an
# optional `local`/`scoped` or `-`). An attribute can hand its declaration to code that the
# build later runs (KeyedDecls attributes such as command_elab/term_elab/tactic/macro, init,
# simproc, norm_num, positivity, aesop rule builders, linters, delaborators, try?
# suggestion generators, doc roles, ...), so the list is an allowlist of attributes that only
# tag a theorem or definition for an existing procedure, or set reducibility, compiler or
# documentation flags; none evaluates the declaration it is put on. The first group is what
# Aeneas emits in the generated translation (pilot run 3); the rest is ordinary proof use.
# Extending it is a reviewed change of this file.
ATTR_ALLOWED = {
    # Aeneas, generated code
    "reducible", "irreducible", "global_simps", "discriminant", "rust_fun", "rust_type",
    "rust_trait", "rust_trait_impl", "rust_loop", "rust_loop_body", "rust_const",
    "trait_default",
    # Aeneas, proofs (lemma tags read by step/progress, scalar_tac, simp_lists, simp_scalar,
    # bvify, agrind)
    "step", "step_pure", "step_pure_def", "step_simps", "progress", "progress_pure",
    "progress_pure_def", "progress_simps", "scalar_tac", "scalar_tac_simps", "scalar_tac_nonlin",
    "simp_lists", "simp_lists_simps", "simp_scalar", "bvify", "bvify_simps", "agrind",
    # Lean core and Mathlib: simp sets and lemma tags, instances, reducibility, compiler hints
    "simp", "instance", "semireducible", "inline", "noinline", "specialize", "ext", "simps",
    "norm_cast", "push_cast", "grind", "congr", "refl", "symm", "trans", "gcongr", "fun_prop",
    "match_pattern", "elab_as_elim", "induction_eliminator", "cases_eliminator",
    "inherit_doc", "deprecated", "nolint", "pp_nodot", "expose", "wf_preprocess",
}
ATTR_START = re.compile(r"@\[|(?<![A-Za-z0-9_'!?.])attribute\s*\[")
ATTR_NAME = re.compile(r"[A-Za-z_][A-Za-z0-9_'!?.]*")


def attr_blocks(text):
    """(position, content) of every `@[...]` and `attribute [...]` (brackets nested, string
    literals skipped)."""
    for m in ATTR_START.finditer(text):
        i, depth, start = m.end(), 1, m.end()
        while i < len(text) and depth:
            c = text[i]
            if c == '"':
                i += 1
                while i < len(text) and text[i] != '"':
                    i += 2 if text[i] == "\\" else 1
            elif c in "([{":
                depth += 1
            elif c in ")]}":
                depth -= 1
            i += 1
        yield m.start(), text[start:i - 1]


def attr_names(content):
    """Attribute names in the content of `@[...]`: the first identifier of each top-level
    comma-separated entry after `local`/`scoped`/`-`; None for an entry without one."""
    entries, depth, cur, i = [], 0, "", 0
    while i < len(content):
        c = content[i]
        if c == '"':
            j = i + 1
            while j < len(content) and content[j] != '"':
                j += 2 if content[j] == "\\" else 1
            cur += content[i:j + 1]
            i = j + 1
            continue
        if c in "([{":
            depth += 1
        elif c in ")]}":
            depth -= 1
        if c == "," and depth == 0:
            entries.append(cur)
            cur = ""
        else:
            cur += c
        i += 1
    entries.append(cur)
    names = []
    for e in entries:
        e = e.strip()
        e = re.sub(r"^(?:(?:local|scoped)\s+)?-?\s*", "", e)
        m = ATTR_NAME.match(e)
        names.append(m.group(0) if m else None)
    return names


RULE_AXIOM = ("axiom (outside trusted/)", word("axiom"))


# trusted/ only: no name in the namespace `rmcp`, and no `export`. The generated Rmcp.Funs
# works inside `namespace rmcp` and refers to Aeneas library names (`toStr`, ...) and to the
# externals unqualified; the externals are declared at root level (as in the templates, e.g.
# `model.request_state_wire.prim.hmac_sha256`, although translation.json lists the Lean name
# `rmcp.model...`), so an `rmcp.<x>` declared in trusted/ (or an alias `rmcp.<x>` added by
# `export` inside `namespace rmcp`) would silently take precedence over the library name or
# the external that the generated code means. The rule is on tokens, not on declaration
# forms: after comments (`--`, nested `/- -/`, docstrings), string literals and character
# literals are blanked (trusted_code), every identifier token whose first component is
# `rmcp` (also after `_root_.`, and quoted as `«rmcp»`, or a quoted first component starting
# with `rmcp.`) fails, and so does the keyword `export`. The one exception is a line that is
# exactly `open rmcp` (TRUSTED_OPEN_OK): FunsExternal.lean needs it, from the Aeneas template,
# for the trait structures of Rmcp.Types (`core.hash.BuildHasher`, `zeroize.Zeroize`, ...);
# `open` declares nothing. lean-axiom-audit.lean checks the same on the build output (no
# constant of a trusted module in the namespace `rmcp`, no alias added by a trusted module).
EXT_ID = re.compile(r"(?:«[^»\n]*»|[^\W\d][\w'!?]*)(?:\.(?:«[^»\n]*»|[^\W\d][\w'!?]*))*")
EXT_ID_COMP = re.compile(r"«[^»\n]*»|[^.«]+")
EXT_OPEN_OK = re.compile(r"^open rmcp$", re.M)


# Pinned exception for generated files (human decision 2026-11-23, S21; replaces a lexing-based
# exemption that four review rounds bypassed). formal/trusted/translation-pins.txt (trusted, read
# by review) records, per generated file, its sha256 and the exact text of the lines on which a
# META word is excused (today the T06 line holding the MCP method name "initialize"). A hit is
# excused only if the file's bytes have the pinned sha256 AND the hit's whole line equals a pinned
# line; any other file content gets the strict rule. No lexing is involved.
PINS_FILE = os.path.join("trusted", "translation-pins.txt")


def load_translation_pins(formal):
    """{rel path: (sha256, {line number: (word, exact text)})} from PINS_FILE, and errors.
    Format, one entry per line; `#` comments (in column 1) and blank lines ignored:
      file <rel path under formal/, starting with translation/> sha256 <64 lowercase hex digits>
      line <line number> <META word> <exact text of that line>   (belongs to the last `file`)
    The pin file must be a regular file (not a symlink) without CR bytes; a path pinned twice,
    a line number pinned twice, or a malformed entry is an error."""
    pins, errs, cur = {}, [], None
    path = os.path.join(formal, PINS_FILE)
    if os.path.islink(path) or (os.path.exists(path) and not os.path.isfile(path)):
        return pins, [f"{PINS_FILE}: must be a regular file, not a symlink or directory"]
    if not os.path.exists(path):
        return pins, errs
    with open(path, "rb") as f:
        raw_bytes = f.read()
    if b"\r" in raw_bytes:
        return pins, [f"{PINS_FILE}: CR byte (use LF line endings)"]
    try:
        content = raw_bytes.decode("utf-8")
    except UnicodeDecodeError:
        return pins, [f"{PINS_FILE}: not UTF-8"]
    for k, raw in enumerate(content.split("\n"), 1):
        if not raw.strip() or raw.startswith("#"):
            continue
        m = re.fullmatch(r"file (translation/[\w/.-]+\.lean) sha256 ([0-9a-f]{64})", raw)
        ml = re.fullmatch(r"line ([1-9][0-9]*) (\S+) (.*)", raw)
        if m:
            cur = m.group(1)
            if os.path.normpath(cur) != cur:
                errs.append(f"{PINS_FILE}:{k}: path {cur} is not normal")
            elif not os.path.isfile(os.path.join(formal, cur)):
                errs.append(f"{PINS_FILE}:{k}: pinned file {cur} does not exist")
            if cur in pins:
                errs.append(f"{PINS_FILE}:{k}: {cur} pinned twice")
            pins[cur] = (m.group(2), {})
        elif ml and cur is not None:
            n = int(ml.group(1))
            if n in pins[cur][1]:
                errs.append(f"{PINS_FILE}:{k}: line {n} of {cur} pinned twice")
            pins[cur][1][n] = (ml.group(2), ml.group(3))
        else:
            errs.append(f"{PINS_FILE}:{k}: malformed entry")
    return pins, errs


def line_at(text, pos):
    a = text.rfind("\n", 0, pos) + 1
    b = text.find("\n", pos)
    return text[a:] if b < 0 else text[a:b]


def external_code(text):
    """TEXT with comments (`--` to the end of the line; `/- -/` nested, docstrings included),
    string literals (also raw `r"…"`, `r#"…"#`, interpolated) and character literals replaced
    by spaces; newlines are kept, so line numbers stay."""
    out, i, n = list(text), 0, len(text)

    def blank(a, b):
        for k in range(a, min(b, n)):
            if out[k] != "\n":
                out[k] = " "

    idch = re.compile(r"[\w'!?]")
    while i < n:
        c = text[i]
        if text.startswith("/-", i):
            depth, j = 1, i + 2
            while j < n and depth:
                if text.startswith("/-", j):
                    depth, j = depth + 1, j + 2
                elif text.startswith("-/", j):
                    depth, j = depth - 1, j + 2
                else:
                    j += 1
            blank(i, j)
            i = j
        elif text.startswith("--", i):
            j = text.find("\n", i)
            j = n if j < 0 else j
            blank(i, j)
            i = j
        elif c == "r" and (i == 0 or not idch.match(text[i - 1])) and \
                re.match(r'r#*"', text[i:i + 300]):
            hashes = re.match(r'r(#*)"', text[i:]).group(1)
            close = '"' + hashes
            j = text.find(close, i + 2 + len(hashes))
            j = n if j < 0 else j + len(close)
            blank(i, j)
            i = j
        elif c == '"':
            j = i + 1
            while j < n and text[j] != '"':
                j += 2 if text[j] == "\\" else 1
            blank(i, j + 1)
            i = j + 1
        elif c == "'" and (i == 0 or not idch.match(text[i - 1])):
            m = re.match(r"'(?:\\(?:x[0-9a-fA-F]{2}|u[0-9a-fA-F]{4}|.)|[^\\'\n])'", text[i:])
            if m:
                blank(i, i + m.end())
                i += m.end()
            else:
                i += 1
        else:
            i += 1
    return "".join(out)


def external_ns_errors(rel, text):
    """Hits of the trusted/ rule (see TRUSTED_ID) in TEXT, as error strings."""
    code = EXT_OPEN_OK.sub(lambda m: " " * len(m.group(0)), external_code(text))
    errs = []
    for m in EXT_ID.finditer(code):
        tok = m.group(0)
        comps = EXT_ID_COMP.findall(tok)
        if comps and comps[0] == "_root_":
            comps = comps[1:]
        first = comps[0].strip("«»") if comps else ""
        if first == "rmcp" or first.startswith("rmcp."):
            errs.append(f"{rel}:{lineno(code, m.start())}: banned: identifier {tok} in the namespace "
                        "rmcp (trusted/; only the line `open rmcp` is allowed)")
        elif tok == "export":
            errs.append(f"{rel}:{lineno(code, m.start())}: banned: export (trusted/; an alias "
                        "could shadow a name the generated code means)")
    return errs


GUARD = re.compile(r"#guard_msgs(?![A-Za-z0-9_'!?])")
# The only accepted form, in specs/Specs.lean, specs/Specs/ and proofs/Proofs/Internal/: `#guard_msgs in` (no option:
# `(drop …)` would swallow messages, `(error)` etc. would let info pass) followed, on the same
# or the next line, by exactly one `#print axioms <name>` and the end of that line.
GUARD_OK = re.compile(r"#guard_msgs[ \t]+in[ \t]*(?:\r?\n[ \t]*)?#print[ \t]+axioms[ \t]+\S+[ \t]*(?:\r?\n|\Z)")

SKIP_DIRS = {".lake"}


def tracked_lake_paths(formal):
    """Paths tracked by git under FORMAL with a `.lake` component, or None if FORMAL is not
    in a git work tree (or git is missing). Lake loads a committed
    `.lake/config/<idx>/lakefile.olean` (with its trace) as compiled configuration at its first
    command, before any guard could look at it, so nothing under a `.lake` directory may be
    committed."""
    try:
        r = subprocess.run(["git", "-C", formal, "ls-files", "-z", "--", "."],
                           capture_output=True, check=False)
    except OSError:
        return None
    if r.returncode != 0:
        return None
    paths = [p for p in r.stdout.decode("utf-8", "replace").split("\0") if p]
    return [p for p in paths if ".lake" in p.split("/")]


def check_fresh(formal):
    """CI, first step after checkout (before elan or any Lake command): FORMAL/.lake must not
    exist and git must track nothing under a `.lake` directory below FORMAL."""
    errs = []
    if os.path.lexists(os.path.join(formal, ".lake")):
        errs.append(f"{os.path.join(formal, '.lake')} exists in a fresh checkout (committed Lake state?)")
    tracked = tracked_lake_paths(formal)
    if tracked is None:
        errs.append(f"{formal} is not in a git work tree (git ls-files failed)")
    else:
        errs += [f"{p}: tracked by git under a .lake directory" for p in tracked]
    if errs:
        fail(errs + ["fresh-checkout check failed"])
    print("[lean-guard] fresh checkout: no formal/.lake, nothing tracked under a .lake directory")


def lineno(text, pos):
    return text.count("\n", 0, pos) + 1


# Two exact exemptions (human decision 2026-11-24, Aeneas upgrade to nightly-2026.11.24-fb44cb4;
# exercised by `lean_guard.py selftest`).
# (1) Generated files: Aeneas adds to the `Source:` field of a docstring, for an item generated
# from a Rust macro, the phrase MACRO_SITE_PHRASE. The word `macro` is excused only inside that
# phrase, and only on a line that is exactly such a `Source:` line (MACRO_SITE_LINE). Such a
# line (`Source: '…', lines …; …`) is not valid Lean outside a comment, so the word cannot be
# a command there.
MACRO_SITE_PHRASE = "this code is generated from a macro invocation at:"
MACRO_SITE_LINE = re.compile(r"[ ]*Source: '[^'\n]*', lines [0-9:-]+; "
                             + re.escape(MACRO_SITE_PHRASE) + r" '[^'\n]*', lines [0-9:-]+( -/)?")
# (2) trusted/: exactly one `set_option linter.dupNamespace false in`, in DUPNS_FILE, directly
# before the docstring, attributes and `def` of DUPNS_DECL (the Aeneas name repeats `zeroize`,
# which the Lean 4.36 linter rejects; the name is fixed by the `rust_fun` mapping).
DUPNS_FILE = "trusted/Rmcp/FunsExternal.lean"
DUPNS_LINE = "set_option linter.dupNamespace false in"
DUPNS_DECL = "zeroize.Zeroize.Blanket.zeroize"
# The docstring and the attribute lines may not contain `/-`: a nested comment opened there
# (Lean nests block comments) would extend the comment past the `def` line, and the option would
# then apply to a later declaration (review finding upg-a-2).
DUPNS_NEXT = re.compile(r"\n/--(?:(?!-/|/-).)*-/\n(?:@\[(?:(?!/-)[^\]\n])*\]\n)*def "
                        + re.escape(DUPNS_DECL) + r"[ \n]", re.S)


def macro_site_excused(text, pos):
    """The `macro` hit at POS lies inside MACRO_SITE_PHRASE on a MACRO_SITE_LINE."""
    line = line_at(text, pos)
    a = text.rfind("\n", 0, pos) + 1
    off = line.find(MACRO_SITE_PHRASE)
    return (MACRO_SITE_LINE.fullmatch(line) is not None and off >= 0
            and pos - a == off + MACRO_SITE_PHRASE.index("macro"))


def dupns_excused(rel, text, pos):
    """The linter hit at POS is the one allowed DUPNS_LINE before DUPNS_DECL in DUPNS_FILE."""
    a = text.rfind("\n", 0, pos) + 1
    b = text.find("\n", pos)
    return (rel == DUPNS_FILE and a == pos and text[a:b] == DUPNS_LINE
            and DUPNS_NEXT.match(text, b) is not None)


def check_sources(formal):
    formal = os.path.abspath(formal)
    errs, nfiles = [], 0
    pins, pin_errs = load_translation_pins(formal)
    errs += pin_errs
    tracked = tracked_lake_paths(formal)
    if tracked is None:
        print("[lean-guard] note: not a git work tree; the check of tracked .lake paths is skipped")
    else:
        errs += [f"{p}: tracked by git under a .lake directory" for p in tracked]
    for dirpath, dirnames, filenames in os.walk(formal):
        rel_dir = os.path.relpath(dirpath, formal)
        if rel_dir == ".":
            dirnames[:] = [d for d in dirnames if d not in SKIP_DIRS]
        for d in list(dirnames):
            if d == ".lake":
                errs.append(f"{os.path.join(rel_dir, d)}: .lake directory below formal/ (only formal/.lake is Lake's)")
                dirnames.remove(d)
        for d in list(dirnames):
            if os.path.islink(os.path.join(dirpath, d)):
                errs.append(f"{os.path.join(rel_dir, d)}: symlinked directory under formal/")
                dirnames.remove(d)
        for fn in filenames:
            path = os.path.join(dirpath, fn)
            rel = os.path.normpath(os.path.join(rel_dir, fn))
            if not fn.endswith(".lean"):
                if fn.lower().endswith(".lean"):
                    errs.append(f"{rel}: Lean file name with a case variant of .lean")
                continue
            if os.path.islink(path):
                errs.append(f"{rel}: symlinked Lean file under formal/")
                continue
            if rel.startswith("specs/Drafts/"):
                continue
            nfiles += 1
            with open(path, "rb") as f:
                raw_bytes = f.read()
            text = raw_bytes.decode("utf-8", errors="replace")
            generated = rel.startswith("translation/")
            template = generated and fn.endswith("_Template.lean")
            rules = list(RULES_ALL) + RULES_META + [RULE_SETOPT_COMMENT]
            if not generated:
                rules += [RULE_LINTER, RULE_AUTOIMPLICIT_ON]
            else:
                rules.append(RULE_AUTOIMPLICIT_GEN)
            if not template and not rel.startswith("trusted/"):
                rules.append(RULE_AXIOM)
            if rel.startswith("trusted/"):
                errs += external_ns_errors(rel, text)
            # Pinned exception, generated files only (PINS_FILE): a META word is excused only at
            # a pinned line number, if it is the pinned word, the line has the pinned text, and the
            # file's bytes (the same bytes the text was decoded from) have the pinned sha256.
            pinned = {}
            if generated and rel in pins:
                if hashlib.sha256(raw_bytes).hexdigest() == pins[rel][0]:
                    pinned = pins[rel][1]
                    for n, (_, want) in pinned.items():
                        lines = text.split("\n")
                        if n > len(lines) or lines[n - 1] != want:
                            errs.append(f"{PINS_FILE}: line {n} of {rel} does not have the pinned text")
                else:
                    errs.append(f"{rel}: note: sha256 differs from its pin in {PINS_FILE}; "
                                "the strict rule applies (update the pin in a reviewed PR)")
            used = set()
            dupns = 0
            for name, rx in rules:
                for m in rx.finditer(text):
                    n = lineno(text, m.start())
                    if generated and name == "macro" and macro_site_excused(text, m.start()):
                        continue
                    if (name, rx) == RULE_LINTER and dupns_excused(rel, text, m.start()):
                        dupns += 1
                        if dupns == 1:
                            continue
                    if ((name, rx) in RULES_META and n in pinned and pinned[n][0] == name
                            and line_at(text, m.start()) == pinned[n][1]):
                        used.add(n)
                        continue
                    errs.append(f"{rel}:{n}: banned: {name}")
            for n in sorted(set(pinned) - used):
                errs.append(f"{PINS_FILE}: line {n} of {rel} is pinned but excuses no hit")
            for m in HASH_CMD.finditer(text):
                if m.group(0) not in HASH_ALLOWED:
                    errs.append(f"{rel}:{lineno(text, m.start())}: banned: {m.group(0)} (only "
                                f"{', '.join(sorted(HASH_ALLOWED))} are allowed)")
            for pos, content in attr_blocks(text):
                for n in attr_names(content):
                    if n not in ATTR_ALLOWED:
                        errs.append(f"{rel}:{lineno(text, pos)}: banned: attribute {n or content.strip()!r} "
                                    "(not in ATTR_ALLOWED)")
            # Restated statements with their axiom checks: public API in specs/Specs/, internal
            # (private) functions and model laws in proofs/Proofs/Internal/ (human decision 2026-11-24).
            in_specs = (rel == "specs/Specs.lean" or rel.startswith("specs/Specs/")
                        or rel.startswith("proofs/Proofs/Internal/"))
            for m in GUARD.finditer(text):
                # Prose: `#guard_msgs` written in backticks cannot be a command (a backtick
                # before `#` does not parse in Lean), so it is skipped.
                if text[m.start() - 1:m.start()] == "`" and text[m.end():m.end() + 1] == "`":
                    continue
                ln = lineno(text, m.start())
                if not in_specs:
                    errs.append(f"{rel}:{ln}: #guard_msgs is allowed only in specs/Specs.lean, specs/Specs/ "
                                "and proofs/Proofs/Internal/")
                elif not GUARD_OK.match(text, m.start()):
                    errs.append(f"{rel}:{ln}: #guard_msgs must be exactly `#guard_msgs in` followed by "
                                "one `#print axioms <name>` line (no options, no drop)")
    if errs:
        fail(errs + ["banned words or constructs in Lean sources (see scripts/lean-guard.sh, 'sources')"])
    print(f"[lean-guard] sources: {nfiles} Lean file(s) checked; no banned words or constructs")


# ---------------------------------------------------------------------------------------
# build log

# Lake replayed four `sorry` warnings of the Aeneas library up to nightly-2026.08.20-5d08da4
# (Aeneas/Std/Slice.lean, Aeneas/Std/StringIter.lean); nightly-2026.11.24-fb44cb4 has none, so no
# warning or error line is allowed (lead decision N10 of the Aeneas upgrade).
ALLOWED_LOG_LINES = set()
LOG_FLAG = re.compile(r"warning:|error:")


def check_build_log(path):
    if not os.path.isfile(path) or os.path.getsize(path) == 0:
        fail([f"build log {path} is missing or empty", "build-log check failed"])
    with open(path, encoding="utf-8", errors="replace") as f:
        lines = f.read().splitlines()
    bad, allowed = [], 0
    for i, line in enumerate(lines, 1):
        if not LOG_FLAG.search(line):
            continue
        if line.rstrip("\r") in ALLOWED_LOG_LINES:
            allowed += 1
        else:
            bad.append(f"{path}:{i}: {line}")
    if not any(line.startswith("Build completed successfully") for line in lines):
        bad.append(f"{path}: no 'Build completed successfully' line")
    if bad:
        fail(bad + ["build log has warning/error lines (none is allowed)"])
    print("[lean-guard] build log: no warning or error line")


# ---------------------------------------------------------------------------------------
# Aeneas archive vs installed build

# Lake's own bookkeeping, rewritten locally after unpacking (not compared).
SKIP_EXT = (".hash", ".trace")


def sha(data):
    return hashlib.sha256(data).hexdigest()


def check_archive(pkg_lake, archive):
    """Every regular file of ARCHIVE except *.hash/*.trace (oleans incl. .olean.private and
    .olean.server, .ilean, .ir, .c, .json, shared libraries, ...) must be present in
    PKG/.lake/build with the same bytes, and the build must hold no other file (no symlink,
    no file missing from the archive), *.hash/*.trace excepted."""
    build = os.path.join(pkg_lake, "build")
    in_archive, errs = {}, []
    with tarfile.open(archive, "r:gz") as tf:
        for mem in tf.getmembers():
            name = os.path.normpath(mem.name)
            if mem.isdir() or name.endswith(SKIP_EXT):
                continue
            if not mem.isfile():
                errs.append(f"{name}: archive member is not a regular file or directory")
                continue
            in_archive[name] = sha(tf.extractfile(mem).read())
    present = set()
    for dirpath, dirnames, filenames in os.walk(build):
        for d in dirnames:
            if os.path.islink(os.path.join(dirpath, d)):
                errs.append(f"{os.path.relpath(os.path.join(dirpath, d), build)}: symlink in the Aeneas build")
        for fn in filenames:
            path = os.path.join(dirpath, fn)
            rel = os.path.normpath(os.path.relpath(path, build))
            if fn.endswith(SKIP_EXT):
                continue
            if os.path.islink(path) or not os.path.isfile(path):
                errs.append(f"{rel}: not a regular file in the Aeneas build")
                continue
            present.add(rel)
            with open(path, "rb") as f:
                got = sha(f.read())
            if rel not in in_archive:
                errs.append(f"{rel}: in the Aeneas build but not in the release archive")
            elif in_archive[rel] != got:
                errs.append(f"{rel}: differs from the release archive")
    for rel in sorted(set(in_archive) - present):
        errs.append(f"{rel}: in the release archive but missing from the Aeneas build")
    if errs:
        fail(errs[:20] + [f"{len(errs)} difference(s) between the Aeneas build and {os.path.basename(archive)}"])
    print(f"[lean-guard] Aeneas build: {len(present)} file(s) identical to {os.path.basename(archive)} "
          f"(every regular file except *.hash, *.trace)")


def unpack_build(tar, formal):
    """Extracts the build artifact TAR (made in CI job `build` with
    `tar -C formal/.lake -cf TAR build build.log`) into FORMAL/.lake: only regular files and
    directories under build/ and the file build.log, no absolute or `..` path, no link or
    device; FORMAL/.lake/build and build.log must not exist yet."""
    dest = os.path.join(formal, ".lake")
    for n in ("build", "build.log"):
        if os.path.lexists(os.path.join(dest, n)):
            fail([f"{os.path.join(dest, n)} already exists; unpack into a fresh checkout"])
    errs, members = [], []
    with tarfile.open(tar, "r:") as tf:
        for m in tf.getmembers():
            name = m.name
            parts = name.split("/")
            ok_path = (not name.startswith("/") and ".." not in parts
                       and (parts[0] == "build" or name == "build.log"))
            if not ok_path:
                errs.append(f"{name}: outside build/ and build.log")
            elif not (m.isfile() or m.isdir()) or (m.isdir() and name == "build.log"):
                errs.append(f"{name}: not a regular file or directory")
            else:
                members.append(m)
        if errs:
            fail(errs[:20] + [f"build artifact {tar} rejected ({len(errs)} member(s))"])
        os.makedirs(dest, exist_ok=True)
        tf.extractall(dest, members=members, filter="data")
    print(f"[lean-guard] build artifact: {len(members)} member(s) unpacked into {dest}")


# ---------------------------------------------------------------------------------------
# trusted-axiom lock

LOCK_LINE = re.compile(r"(\S+) sha256:([0-9a-f]{64})")


def check_axiom_lock(lock, got):
    """LOCK (formal/trusted/axioms.lock): lines `<axiom name> sha256:<hex>`, `#` comments and
    blank lines ignored. GOT (written by lean-axiom-audit.lean): lines `<used|unused> TAB
    <name> TAB <canonical statement>` for every axiom declared in the roots of RmcpExternal
    that are in the audited import closure; `used` if it is reachable from a constant declared
    in a module of the Defs, Proofs or Specs library (audit scope, human decision 2026-11-23;
    every constant of those modules counts; computed by one order-independent walk, a superset
    of what `#print axioms` reports).
    Fails if a `used` axiom is not in the lock, if a lock entry names no declared trusted axiom
    (stale), or if the sha256 of the canonical statement (UTF-8) of a declared axiom differs
    from its lock entry. `unused` axioms are listed for information and need no entry; a lock
    entry for a declared but `unused` axiom is reported as unused (allowed), so a reviewed
    model can be locked before a theorem depends on it. The statement of a declared, unlocked,
    `unused` axiom is not checked: it can change or vanish without a failure (only the source
    diff of trusted/ and the informational list show it)."""
    want, errs = {}, []
    with open(lock, encoding="utf-8") as f:
        for i, line in enumerate(f, 1):
            s = line.strip()
            if not s or s.startswith("#"):
                continue
            m = LOCK_LINE.fullmatch(s)
            if not m or m.group(1) in want:
                errs.append(f"{lock}:{i}: not `<name> sha256:<64 hex>` or a duplicate name: {s}")
                continue
            want[m.group(1)] = m.group(2)
    have, used = {}, set()
    with open(got, encoding="utf-8") as f:
        for line in f.read().splitlines():
            parts = line.split("\t", 2)
            if len(parts) != 3 or parts[0] not in ("used", "unused") or parts[1] in have:
                errs.append(f"{got}: malformed line {line!r}")
                continue
            usage, name, stmt = parts
            have[name] = sha(stmt.encode("utf-8"))
            if usage == "used":
                used.add(name)
    base = os.path.basename(lock)
    for n in sorted(used - set(want)):
        errs.append(f"trusted axiom {n} is used by a Defs/Proofs/Specs constant but not in {base} "
                    f"(after review, add the line: {n} sha256:{have[n]})")
    for n in sorted(set(want) - set(have)):
        errs.append(f"{base} lists {n}, which is not an axiom declared in the RmcpExternal roots "
                    "of the audited import closure (stale entry)")
    for n in sorted(set(want) & set(have)):
        if want[n] != have[n]:
            errs.append(f"trusted axiom {n}: statement hash {have[n]} differs from the lock ({want[n]})")
    if errs:
        fail(errs + ["trusted axioms differ from formal/trusted/axioms.lock"])
    for n in sorted(used):
        print(f"[lean-guard] trusted axiom {n}: used, locked")
    for n in sorted((set(want) & set(have)) - used):
        print(f"[lean-guard] trusted axiom {n}: locked, unused by Defs/Proofs/Specs (allowed)")
    unlocked = sorted(set(have) - used - set(want))
    if unlocked:
        print(f"[lean-guard] note: {len(unlocked)} trusted axiom(s) declared but used by no "
              "Defs/Proofs/Specs constant (no lock entry needed):")
        for n in unlocked:
            print(f"[lean-guard]   {n}")
    print(f"[lean-guard] trusted axioms: {len(have)} declared, {len(used)} used and locked, "
          f"{len(set(want) & set(have)) - len(used)} locked but unused, {len(unlocked)} "
          f"unused and unlocked; matching {base}")


# ---------------------------------------------------------------------------------------
# native-code axiom lock

# The roots of the generated library (LIBS, pinned in the lakefile check): the only modules
# whose native-code axioms may be locked.
RMCP_ROOTS = tuple(LIBS["Rmcp"][1])
NATIVE_LOCK_LINE = re.compile(r"(\S+) (\S+) sha256:([0-9a-f]{64})")
# Canonical statement (lean-axiom-audit.lean, `canonical`, wrapped as `(U [] …)`) of the
# Aeneas toStr side condition `decide (LIT.toByteArray.size ≤ Aeneas.Std.U32.max) = true`;
# @SIZE@ stands for the term `ByteArray.size (String.toByteArray LIT)`. The audit checks the
# same form on the Expr (`toStrSideCondition`); this repeats the check on its output.
TOSTR_FORM = ("(U [] (A (A (A (C Eq (s 0)) (C Bool)) (A (A (C Decidable.decide) "
              "(A (A (A (A (C LE.le 0) (C Nat)) (C instLENat)) @SIZE@) (C Aeneas.Std.U32.max))) "
              "(A (A (C Nat.decLe) @SIZE@) (C Aeneas.Std.U32.max)))) (C Bool.true)))")
STR_LIT = re.compile(r'\(T ("(?:[^"\\]|\\.)*")\)')


def is_tostr_form(stmt):
    m = STR_LIT.search(stmt)
    if not m:
        return False
    size = f"(A (C ByteArray.size) (A (C String.toByteArray) (T {m.group(1)})))"
    return stmt == TOSTR_FORM.replace("@SIZE@", size)


def check_native_lock(lock, got):
    """Native-code axioms (human decision 2026-11-22, as in the SPQR project; see
    lean-axiom-audit.lean, "Native-code axioms"). LOCK (formal/trusted/native-axioms.lock):
    lines `<axiom name> <declaring module> sha256:<hex>`, `#` comments and blank lines ignored.
    GOT (written by lean-axiom-audit.lean): `module TAB <name>` for every module of the audited
    import closure, and `native TAB <used|unused> TAB <name> TAB <module> TAB <canonical
    statement>` for every native-code axiom reachable from any project constant (the audit's
    one order-independent walk over all of them); `used` if it is reachable from a constant
    declared in a module of the Defs, Proofs or Specs library (the audit scope of axioms.lock,
    human decision 2026-11-23, applied to this lock by the lead). Fails if any reached native
    axiom (used or not) has a statement other than the toStr form (TOSTR_FORM) or is declared in
    a module other than the roots of the generated Rmcp library (RMCP_ROOTS: Rmcp.Types,
    Rmcp.Funs; so a hand-written `Aeneas.Std.toStr "x"` in Proofs, Specs, Defs or trusted/ fails
    even if listed), if a lock entry names another module, if a `used` native axiom is not in
    the lock, if the module or statement hash of a reached axiom differs from its lock entry, or
    if a lock entry whose module is in the closure is not reached there (stale: no longer
    declared, since every native axiom declared in a project module is reached by itself). A
    lock entry for a reached but `unused` axiom is reported as unused (allowed); reached
    `unused` axioms without an entry are listed for information. Entries for an Rmcp root that
    is not in the closure are only reported."""
    want, errs = {}, []
    with open(lock, encoding="utf-8") as f:
        for i, line in enumerate(f, 1):
            s = line.strip()
            if not s or s.startswith("#"):
                continue
            m = NATIVE_LOCK_LINE.fullmatch(s)
            if not m or m.group(1) in want:
                errs.append(f"{lock}:{i}: not `<name> <module> sha256:<64 hex>` or a duplicate name: {s}")
                continue
            want[m.group(1)] = (m.group(2), m.group(3))
            if m.group(2) not in RMCP_ROOTS:
                errs.append(f"{lock}:{i}: module {m.group(2)} is not a root of the generated Rmcp "
                            f"library ({', '.join(RMCP_ROOTS)}); only their native-code axioms "
                            "may be locked")
    modules, have, used = set(), {}, set()
    with open(got, encoding="utf-8") as f:
        for line in f.read().splitlines():
            parts = line.split("\t")
            if len(parts) == 2 and parts[0] == "module":
                modules.add(parts[1])
            elif (len(parts) == 5 and parts[0] == "native" and parts[1] in ("used", "unused")
                  and parts[2] not in have):
                _, usage, name, mod, stmt = parts
                if not is_tostr_form(stmt):
                    errs.append(f"native-code axiom {name} ({mod}) is not an Aeneas toStr side "
                                "condition of a string literal; it cannot be locked")
                if mod not in RMCP_ROOTS:
                    errs.append(f"native-code axiom {name} is declared in {mod}, not in a root of "
                                f"the generated Rmcp library ({', '.join(RMCP_ROOTS)}); it cannot "
                                "be locked")
                have[name] = (mod, sha(stmt.encode("utf-8")))
                if usage == "used":
                    used.add(name)
            else:
                errs.append(f"{got}: malformed line {line!r}")
    base = os.path.basename(lock)
    for n in sorted(used - set(want)):
        errs.append(f"native-code axiom {n} is used by a Defs/Proofs/Specs constant but not in "
                    f"{base} (after review, add the line: {n} {have[n][0]} sha256:{have[n][1]})")
    unchecked = []
    for n in sorted(set(want) - set(have)):
        if want[n][0] in modules:
            errs.append(f"{base} lists {n} ({want[n][0]}), which is not a native-code axiom "
                        "reached by the audited roots (stale entry)")
        elif want[n][0] in RMCP_ROOTS:
            unchecked.append(n)
    for n in sorted(set(want) & set(have)):
        if want[n] != have[n]:
            errs.append(f"native-code axiom {n}: module/statement hash {have[n][0]} {have[n][1]} "
                        f"differs from the lock ({want[n][0]} {want[n][1]})")
    if errs:
        fail(errs + [f"native-code axioms differ from formal/trusted/{base}"])
    for n in sorted(used):
        print(f"[lean-guard] native-code axiom {n} ({have[n][0]}): toStr side condition, used, "
              "locked")
    for n in sorted((set(want) & set(have)) - used):
        print(f"[lean-guard] native-code axiom {n} ({have[n][0]}): toStr side condition, locked, "
              "unused by Defs/Proofs/Specs (allowed)")
    unlocked = sorted(set(have) - used - set(want))
    if unlocked:
        print(f"[lean-guard] note: {len(unlocked)} native-code axiom(s) reached (toStr side "
              "conditions) but used by no Defs/Proofs/Specs constant (no lock entry needed):")
        for n in unlocked:
            print(f"[lean-guard]   {n} ({have[n][0]})")
    if unchecked:
        mods = sorted({want[n][0] for n in unchecked})
        print(f"[lean-guard] note: {len(unchecked)} entr(y/ies) of {base} not checked: "
              f"module(s) {', '.join(mods)} not reached from the roots")
    print(f"[lean-guard] native-code axioms: {len(have)} reached, {len(used)} used and locked, "
          f"{len(set(want) & set(have)) - len(used)} locked but unused, {len(unlocked)} unused "
          f"and unlocked; matching {base}")


def selftest():
    """Positive and negative cases of the two exact exemptions of check_sources and of its
    autoImplicit rules, run on temporary formal/ trees (each case: files to write, expected pass,
    expected message), and of the leanOptions rule of check_lakefile (lib_option_errors)."""
    import tempfile
    src_line = ("    Source: 'crates/rmcp/src/model.rs', lines 91:8-91:25; " + MACRO_SITE_PHRASE
                + " 'crates/rmcp/src/model.rs', lines 144:0-144:40 -/")
    gen = "translation/Rmcp/Types.lean"
    zero = ("/-- doc -/\n@[rust_fun \"zeroize::{zeroize::Zeroize<@Z>}::zeroize\"]\ndef "
            + DUPNS_DECL + " {Z : Type} : Z → Z := id\n")
    cases = [
        ("macro site in generated docstring", {gen: "/-- [x]\n" + src_line + "\n"}, True, None),
        ("macro site line with extra text", {gen: "/-- [x]\n" + src_line + " macro\n"}, False, "banned: macro"),
        ("macro phrase in code position", {gen: "def f := 1 -- " + MACRO_SITE_PHRASE + "\nmacro \"x\" : term => `(1)\n"},
         False, "banned: macro"),
        ("macro site in a hand-written file", {"proofs/Proofs/X.lean": "/-- [x]\n" + src_line + "\n"},
         False, "banned: macro"),
        ("second macro on a site line", {gen: src_line.replace("Source:", "Source: macro") + "\n"},
         False, "banned: macro"),
        ("dupNamespace option on the one declaration", {DUPNS_FILE: DUPNS_LINE + "\n" + zero}, True, None),
        ("dupNamespace option twice", {DUPNS_FILE: DUPNS_LINE + "\n" + DUPNS_LINE + "\n" + zero}, False,
         "banned: set_option linter"),
        ("dupNamespace option on another declaration",
         {DUPNS_FILE: DUPNS_LINE + "\n/-- doc -/\ndef other.zeroize.x : Nat := 1\n"}, False,
         "banned: set_option linter"),
        ("dupNamespace option in another trusted file", {"trusted/Rmcp/TypesExternal.lean": DUPNS_LINE + "\n" + zero},
         False, "banned: set_option linter"),
        ("dupNamespace option, nested comment in the docstring hides the def (upg-a-2)",
         {DUPNS_FILE: DUPNS_LINE + "\n/-- /- -/\ndef " + DUPNS_DECL + " : Nat := 1\n-/\ndef other.x : Nat := 1\n"},
         False, "banned: set_option linter"),
        ("dupNamespace option, nested comment opened in an attribute line",
         {DUPNS_FILE: DUPNS_LINE + "\n/-- doc -/\n@[simp /-]\ndef " + DUPNS_DECL + " : Nat := 1\n-/]\ndef other.x : Nat := 1\n"},
         False, "banned: set_option linter"),
        ("dupNamespace option, nested comment closed inside the docstring",
         {DUPNS_FILE: DUPNS_LINE + "\n/-- a /- b -/ c -/\ndef " + DUPNS_DECL + " : Nat := 1\n"},
         False, "banned: set_option linter"),
        ("other linter option on the declaration",
         {DUPNS_FILE: "set_option linter.unusedVariables false in\n" + zero}, False, "banned: set_option linter"),
        # autoImplicit (human decision XD3, review finding TR7)
        ("generated: autoImplicit true", {gen: "set_option autoImplicit true\n"}, False,
         "banned: autoImplicit/relaxedAutoImplicit in generated code"),
        ("generated: autoImplicit false", {gen: "set_option autoImplicit false\n"}, False,
         "banned: autoImplicit/relaxedAutoImplicit in generated code"),
        ("generated: relaxedAutoImplicit, in form", {gen: "set_option relaxedAutoImplicit true in\ndef x := 1\n"},
         False, "banned: autoImplicit/relaxedAutoImplicit in generated code"),
        ("generated: quoted option name", {gen: "set_option «autoImplicit» true in\ndef x := 1\n"}, False,
         "banned: autoImplicit/relaxedAutoImplicit in generated code"),
        ("generated: comment before the option name", {gen: "set_option /- x -/ autoImplicit true\n"}, False,
         "banned: comment between set_option and its value"),
        ("generated: comment between name and value",
         {gen: "set_option maxHeartbeats /- x -/ 1000000\n"}, False, "banned: comment between set_option and its value"),
        ("generated: comment after the value", {gen: "set_option maxHeartbeats 1000000 -- x\n"}, True, None),
        ("generated: in a template", {"translation/Rmcp/FunsExternal_Template.lean": "set_option autoImplicit true\n"},
         False, "banned: autoImplicit/relaxedAutoImplicit in generated code"),
        ("hand-written: autoImplicit false", {"proofs/Proofs/X.lean": "set_option autoImplicit false\n"}, True, None),
        ("hand-written: relaxedAutoImplicit false in",
         {"proofs/Proofs/X.lean": "set_option relaxedAutoImplicit false in\ndef x := 1\n"}, True, None),
        ("hand-written: autoImplicit true", {"proofs/Proofs/X.lean": "set_option autoImplicit true\n"}, False,
         "banned: set_option autoImplicit/relaxedAutoImplicit other than false"),
        ("hand-written: relaxedAutoImplicit true in", {"trusted/Rmcp/TypesExternal.lean":
         "set_option relaxedAutoImplicit true in\ndef x := 1\n"}, False,
         "banned: set_option autoImplicit/relaxedAutoImplicit other than false"),
        ("hand-written: quoted option name", {"specs/Defs.lean": "set_option «autoImplicit» true\n"}, False,
         "banned: set_option autoImplicit/relaxedAutoImplicit other than false"),
        ("hand-written: value on the next line", {"specs/Defs.lean": "set_option autoImplicit\n  true\n"}, False,
         "banned: set_option autoImplicit/relaxedAutoImplicit other than false"),
        ("hand-written: comment before the option name", {"specs/Defs.lean": "set_option -- x\n  autoImplicit true\n"},
         False, "banned: comment between set_option and its value"),
        # review finding TR11: no space before «, quoted names, the `in` form, quoted name with false
        ("hand-written: no space before the quoted name (TR11)",
         {"specs/Defs.lean": "set_option«autoImplicit» true\n"}, False,
         "banned: set_option autoImplicit/relaxedAutoImplicit other than false"),
        ("hand-written: no space, quoted name, in form (TR11)",
         {"specs/Defs.lean": "set_option«relaxedAutoImplicit» true in\ndef x := 1\n"}, False,
         "banned: set_option autoImplicit/relaxedAutoImplicit other than false"),
        ("hand-written: line break before the unquoted name",
         {"specs/Defs.lean": "set_option\n  autoImplicit true\n"}, False,
         "banned: set_option autoImplicit/relaxedAutoImplicit other than false"),
        ("hand-written: quoted name, false (TR11)",
         {"proofs/Proofs/X.lean": "set_option «relaxedAutoImplicit» false\n"}, True, None),
        ("hand-written: quoted name, false, in form (TR11)",
         {"proofs/Proofs/X.lean": "set_option «autoImplicit» false in\ndef x := 1\n"}, True, None),
        ("hand-written: no space, quoted name, no space, false (TR11)",
         {"proofs/Proofs/X.lean": "set_option«autoImplicit»false\n"}, True, None),
        ("hand-written: false on the next line", {"proofs/Proofs/X.lean": "set_option autoImplicit\n  false\n"},
         True, None),
        ("hand-written: comment before false (TR12)",
         {"specs/Defs.lean": "set_option autoImplicit /- c -/ false\n"}, False,
         "banned: comment between set_option and its value"),
        ("hand-written: autoImplicit as a name prefix is another option",
         {"specs/Defs.lean": "set_option autoImplicitX true\n"}, True, None),
        # review finding TR12: comments between name and value, quoted components of linter names
        ("hand-written: linter, comment between name and value (TR12)",
         {"proofs/Proofs/X.lean": "set_option linter.unusedVariables /- c -/ false in\ndef x := 1\n"}, False,
         "banned: comment between set_option and its value"),
        ("hand-written: linter, line comment between name and value (TR12)",
         {"proofs/Proofs/X.lean": "set_option linter.unusedVariables -- c\n  false in\ndef x := 1\n"}, False,
         "banned: comment between set_option and its value"),
        ("hand-written: linter, quoted first component (TR12)",
         {"proofs/Proofs/X.lean": "set_option «linter».unusedVariables false in\ndef x := 1\n"}, False,
         "banned: set_option linter"),
        ("hand-written: linter, quoted later component (TR12)",
         {"proofs/Proofs/X.lean": "set_option linter.«unusedVariables» false in\ndef x := 1\n"}, False,
         "banned: set_option linter"),
        ("hand-written: linter, all components quoted, no spaces (TR12)",
         {"proofs/Proofs/X.lean": "set_option«linter».«unusedVariables»false\n"}, False,
         "banned: set_option linter"),
        ("hand-written: linter, value on the next line (TR12)",
         {"proofs/Proofs/X.lean": "set_option linter.unusedVariables\n  false in\ndef x := 1\n"}, False,
         "banned: set_option linter"),
        ("hand-written: linter switched on", {"proofs/Proofs/X.lean": "set_option linter.unusedVariables true\n"},
         True, None),
        ("hand-written: comment after the value", {"proofs/Proofs/X.lean": "set_option autoImplicit false -- c\n"},
         True, None),
        ("hand-written: falsehood is not false", {"specs/Defs.lean": "set_option autoImplicit falsehood\n"}, False,
         "banned: set_option autoImplicit/relaxedAutoImplicit other than false"),
        ("hand-written: the word in a docstring", {"specs/Defs.lean": "/-- built with `autoImplicit = false` -/\ndef x := 1\n"},
         True, None),
    ]
    bad = []
    # The leanOptions rule of check_lakefile (lib_option_errors): the one extra option of Rmcp
    # and RmcpExternal.
    opt_cases = [
        ("Rmcp with autoImplicit off", "Rmcp", {"warningAsError": True, "autoImplicit": False}, True),
        ("Rmcp without autoImplicit", "Rmcp", {"warningAsError": True}, False),
        ("Rmcp with autoImplicit on", "Rmcp", {"warningAsError": True, "autoImplicit": True}, False),
        ("Rmcp without warningAsError", "Rmcp", {"autoImplicit": False}, False),
        ("Rmcp with warningAsError off", "Rmcp", {"warningAsError": False, "autoImplicit": False}, False),
        ("Rmcp with a third option", "Rmcp",
         {"warningAsError": True, "autoImplicit": False, "relaxedAutoImplicit": False}, False),
        ("Rmcp with a string value", "Rmcp", {"warningAsError": True, "autoImplicit": "false"}, False),
        ("Rmcp with an integer value", "Rmcp", {"warningAsError": 1, "autoImplicit": False}, False),
        ("RmcpExternal with autoImplicit off", "RmcpExternal",
         {"warningAsError": True, "autoImplicit": False}, True),
        ("RmcpExternal without autoImplicit", "RmcpExternal", {"warningAsError": True}, False),
        ("RmcpExternal with autoImplicit on", "RmcpExternal",
         {"warningAsError": True, "autoImplicit": True}, False),
        ("RmcpExternal with a string value", "RmcpExternal",
         {"warningAsError": True, "autoImplicit": "false"}, False),
        ("RmcpExternal with a third option", "RmcpExternal",
         {"warningAsError": True, "autoImplicit": False, "relaxedAutoImplicit": False}, False),
        ("Proofs with autoImplicit off", "Proofs", {"warningAsError": True, "autoImplicit": False}, False),
        ("Proofs default", "Proofs", {"warningAsError": True}, True),
        ("Specs not a table", "Specs", "warningAsError", False),
    ]
    for name, lib, opts, ok in opt_cases:
        if (not lib_option_errors(lib, opts)) != ok:
            bad.append(f"selftest case {name!r}: expected {'pass' if ok else 'fail'}")
    for name, files, ok, msg in cases:
        with tempfile.TemporaryDirectory() as d:
            for rel, content in files.items():
                os.makedirs(os.path.dirname(os.path.join(d, rel)), exist_ok=True)
                with open(os.path.join(d, rel), "w", encoding="utf-8") as f:
                    f.write(content)
            import io, contextlib
            err, out = io.StringIO(), io.StringIO()
            try:
                with contextlib.redirect_stderr(err), contextlib.redirect_stdout(out):
                    check_sources(d)
                passed = True
            except SystemExit as e:
                passed = e.code == 0
            if passed != ok or (msg and msg not in err.getvalue()):
                bad.append(f"selftest case {name!r}: expected {'pass' if ok else 'fail'}"
                           f"{' with ' + repr(msg) if msg else ''}, got {'pass' if passed else 'fail'}: "
                           f"{err.getvalue().strip()[:300]}")
    if bad:
        fail(bad + ["selftest failed"])
    print(f"[lean-guard] selftest: {len(cases)} cases of the sources exemptions and autoImplicit rules and "
          f"{len(opt_cases)} cases of the lakefile leanOptions rule pass")


COMMANDS = {"selftest": (selftest, 0), "fresh": (check_fresh, 1), "axiom-lock": (check_axiom_lock, 2),
            "native-lock": (check_native_lock, 2),
            "lakefile": (check_lakefile, 1), "sources": (check_sources, 1),
            "build-log": (check_build_log, 1), "archive": (check_archive, 2),
            "roots": (audit_roots, 1), "leanpath": (lean_path, 1),
            "buildtree": (check_build_tree, 1), "unpack": (unpack_build, 2)}


def main(argv):
    if not argv or argv[0] not in COMMANDS or len(argv) - 1 != COMMANDS[argv[0]][1]:
        print(__doc__, file=sys.stderr)
        sys.exit(2)
    fn, _ = COMMANDS[argv[0]]
    try:
        fn(*argv[1:])
    except (OSError, ValueError, tomllib.TOMLDecodeError, tarfile.TarError, KeyError, TypeError) as e:
        print(f"[lean-guard] error: {e}", file=sys.stderr)
        sys.exit(2)


if __name__ == "__main__":
    main(sys.argv[1:])
