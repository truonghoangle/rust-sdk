#!/usr/bin/env bash
# Guards around `lake build` for the Lean project in formal/ (plan Section 5, "CI").
#
# The build gate is `warningAsError` in every library plus `lake build --wfail` (usable
# again since Aeneas nightly-2026.11.24-fb44cb4, whose library replays no warning). A file could switch the option off, hide messages, add declarations
# without a kernel check, or run code during the build, so CI also runs the subcommands
# below. The checks are in scripts/lean_guard.py (run with `python3 -I`, Python >= 3.11) and
# scripts/lean-axiom-audit.lean. In CI (.github/workflows/lean-build.yml) both jobs run
# `fresh` and `sources` right after checkout, before elan is installed and before any `lean`
# or `lake` command (Lake would load committed Lake state, and elan would run the toolchain
# named in formal/lean-toolchain); job `build` then runs `lake build`; job `check`, on a
# fresh runner with the scripts of a fresh checkout, fetches the dependencies and runs
# `aeneas-archive`, then `unpack-build`, `build-log` and `axioms` on the uploaded build
# output, so code run by the build cannot change these scripts.
#
#   scripts/lean-guard.sh fresh
#       CI only, first step: fails if formal/.lake exists or git tracks any path under a
#       `.lake` directory below formal/ (a committed .lake/config/<idx>/lakefile.olean with
#       its trace is loaded and run by Lake at its first command).
#
#   scripts/lean-guard.sh sources
#       First `lean_guard.py selftest` (the two exact exemptions of step 3: the Aeneas
#       macro-site phrase in generated docstrings and the one dupNamespace option in trusted/;
#       the autoImplicit rules of step 3; and the leanOptions rule of step 1).
#       0. formal/lean-toolchain is exactly leanprover/lean4:v4.36.0 (LEAN_TOOLCHAIN in
#          lean_guard.py, updated with the Aeneas rev); git tracks nothing under a `.lake`
#          directory below formal/ (skipped with a note outside a git work tree); no `.lake`
#          directory below formal/ other than formal/.lake; no file named with a case
#          variant of `.lean` (`Foo.LEAN`).
#       1. formal/lakefile.toml (parsed as TOML) has exactly the five libraries of plan
#          Section 5: Rmcp (srcDir translation), RmcpExternal (trusted), Defs (specs),
#          Proofs (proofs), Specs (specs), with their fixed roots, each with exactly the keys
#          name, srcDir, roots, leanOptions and leanOptions exactly { warningAsError = true }
#          (Rmcp and RmcpExternal: exactly { warningAsError = true, autoImplicit = false },
#          human decisions XD3, XD9);
#          package-level keys only name, defaultTargets, require, lean_lib (so no
#          leanOptions, moreLeanArgs, weakLeanArgs, moreServerArgs, ... at any level); one
#          [[require]] (aeneas); defaultTargets include Defs, Proofs, Specs; and no
#          formal/lakefile.lean (Lake would prefer it).
#       2. formal/lake-manifest.json lists exactly the ten packages recorded in
#          lean_guard.py (MANIFEST_PACKAGES) with their git url and commit: aeneas at
#          fb44cb400eb6bfe7dce97422ebe8fa748b7e4f9b with url, inputRev and subDir equal to the
#          lakefile's git, rev and subDir; mathlib at fc4f59e577feb1a4956671bc04ac18aaaf8cd842;
#          and the eight packages Mathlib brings in.
#       3. Every .lean file under formal/ except formal/.lake/ and formal/specs/Drafts/ fails
#          on the rules of lean_guard.py (check_sources; the full lists, and how the list of
#          code-running forms was derived from the pinned toolchain and packages, are in
#          the S03 evidence (git history at 223ff12), fix round 5): banned whole tokens (WORDS_ALL:
#          sorry, admit, native_decide, unsafe, implemented_by, extern, ...; META_WORDS:
#          every keyword whose elaborator or macro runs code at elaboration time, such as
#          run_cmd, run_tac, by_elab, include_str, elab, macro, syntax, initialize,
#          plausible, ...; the metaprogramming monads and Lean.Elab), every `#` command
#          except #check, #print and the `#guard_msgs in #print axioms <name>` form (allowed
#          only in formal/specs/Specs.lean, formal/specs/Specs/ and
#          formal/proofs/Proofs/Internal/), every attribute not in
#          ATTR_ALLOWED (in `@[...]` and `attribute [...]`), the `native` option of decide,
#          `debug.` options, `set_option linter.<name> false` (each name component plain or
#          «…»-quoted; except in formal/translation/, where Aeneas emits it), a comment
#          anywhere between `set_option` and its value (before or after the option name), the
#          option names autoImplicit and relaxedAutoImplicit anywhere in formal/translation/ and
#          `set_option` of either (plain or «…»-quoted, with or without whitespace after
#          `set_option`) with a value other than `false` elsewhere (human decision XD3, review
#          findings TR7, TR11, TR12), and `axiom` outside formal/trusted/ (and the unbuilt
#          Aeneas *_Template.lean files). Comments and docstrings count (exception, S21,
#          generated files only: a word on a line pinned, with the file's sha256, in the
#          trusted file formal/trusted/translation-pins.txt; today the MCP method name
#          "initialize" in T06). Symlinks under
#          formal/ (outside .lake/) fail. In formal/trusted/ only, after comments, string and
#          character literals are blanked: any identifier whose first component is `rmcp`
#          (also `_root_.rmcp`, `«rmcp»`) and the keyword `export` fail; the only exception
#          is a line that is exactly `open rmcp` (lean_guard.py, trusted_ns_errors).
#
#   scripts/lean-guard.sh build-log FILE
#       FILE is the output of `lake build` (`set -o pipefail; lake build 2>&1 | tee FILE`).
#       Fails unless it has a "Build completed successfully" line and no line containing
#       `warning:` or `error:` (up to nightly-2026.08.20-5d08da4 the Aeneas library replayed
#       four `sorry` warnings, which were allowed; nightly-2026.11.24-fb44cb4 has none).
#
#   scripts/lean-guard.sh axioms
#       Only after a successful `lake build`. Fails if formal/.lake/build/lib/lean holds
#       anything but modules named Rmcp, Defs, Proofs, Specs or below them, or a symlink;
#       then runs scripts/lean-axiom-audit.lean with the toolchain's own `lean` (not
#       `lake env`, which would put formal/.lake/build/bin first on PATH and
#       formal/.lake/build/lib on the shared-library path), LEAN_PATH = toolchain library,
#       package libraries, project build (in that order), and no dynamic-loader variables.
#       The audit imports the roots of the default-target libraries without running any
#       imported code (loadExts := false) and fails if a project .olean is stale (its Lake
#       trace records another source hash than the current source's), if the constants
#       declared in project modules reach (one order-independent walk over all of them,
#       through types, values and whole inductive blocks; a superset of `#print axioms`) an
#       axiom other than propext, Classical.choice, Quot.sound, the native-code axioms below
#       and the axioms declared in the roots of RmcpExternal
#       (catches sorryAx, also inherited from the Aeneas library or hidden from the build
#       log, and Lean.ofReduceBool), or if the kernel rejects a project constant when all of
#       them are replayed (Lean.Environment.replay, as leanchecker does) onto the
#       non-project modules they import (catches declarations added without a kernel check,
#       e.g. with debug.skipKernelTC, and altered .olean files). Finally the locks, with the
#       audit scope of the human decision 2026-11-23 (axioms.lock; the lead applied the same
#       rule to the native lock): an axiom is `used` if it is reachable from some constant
#       declared in a Defs, Proofs or Specs module (every constant, including private
#       helpers, instances and auxiliary declarations), transitively through any constant
#       (also the generated Rmcp.Types/Rmcp.Funs definitions), computed by the same walk
#       from those constants only. Every used axiom
#       declared in the roots of RmcpExternal must be in formal/trusted/axioms.lock with the
#       sha256 of its canonical statement; a lock entry must name a declared axiom (else
#       stale), with the same hash; declared but unused axioms are listed and need no entry,
#       and an entry for one is reported as unused (allowed) (lean_guard.py axiom-lock).
#       So the statement of a declared but unlocked axiom that is not used (today all 41
#       placeholders) can change or vanish without this check failing, in any PR; only the
#       source diff of trusted/ and the informational list show it.
#       Native-code axioms (a `_native` name component, from `decide +native` /
#       `native_decide`, or Lean.trustCompiler; human decision 2026-11-22, as in the SPQR
#       project) are a separate trust class: the audit accepts one that the same walk
#       reaches only if its statement is the Aeneas `toStr` side condition of a string
#       literal, `decide ("...".toByteArray.size <= Aeneas.Std.U32.max) = true`, lists them
#       separately, and lean_guard.py native-lock requires each used one (same scope) to be
#       in formal/trusted/native-axioms.lock with the sha256 of its canonical statement; both
#       require the declaring module (of every reached axiom, used or not, and of every lock
#       entry) to be Rmcp.Types or Rmcp.Funs; a lock entry whose module is in the audited
#       import closure but that is not reached there is stale and fails; an entry for a
#       reached but unused one is reported as unused (allowed). The audit also fails if a
#       root of RmcpExternal declares a constant in the namespace `rmcp` or adds an alias
#       (`export`). Only the import closure of the default-target roots is audited: until a
#       Defs/Proofs/Specs module imports Rmcp.Funs (S06) or Rmcp and RmcpExternal join
#       defaultTargets (a lakefile change by the lead), the trusted-module checks,
#       axioms.lock and the native lock are not enforced on them (native-lock entries for
#       Rmcp.Types/Funs are reported as not checked; any axioms.lock entry fails as stale
#       until RmcpExternal is reached), even if their .olean files exist from an explicit
#       `lake build Rmcp RmcpExternal`.
#
#   scripts/lean-guard.sh aeneas-archive
#       Checks every Aeneas Lean-library release archive that Lake downloaded
#       (preferReleaseBuild; Lake itself checks no digest) against
#       formal/trusted/aeneas-bundle.sha256, and that the installed Aeneas build and the
#       archive hold the same regular files with the same bytes (every file except *.hash
#       and *.trace: .olean, .olean.private, .olean.server, .ilean, .ir, .c, .json, shared
#       libraries, ...). Fails if the Aeneas package has a build but no archive, unless
#       LEAN_GUARD_AENEAS_FROM_SOURCE=1 is set (explicit marker that the Aeneas library was
#       built from its pinned sources).
#
#   scripts/lean-guard.sh unpack-build TAR
#       CI job `check`: extracts the artifact of job `build` (a tar of formal/.lake/build and
#       formal/.lake/build.log) into formal/.lake, refusing any member outside build/ and
#       build.log, absolute or `..` paths, links and devices, and an existing build.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
F="$ROOT/formal"

log() { printf '[lean-guard] %s\n' "$*"; }
die() { printf '[lean-guard] error: %s\n' "$*" >&2; exit 1; }

command -v python3 >/dev/null 2>&1 || die "python3 not found"
py() { python3 -I "$ROOT/scripts/lean_guard.py" "$@"; }

guard_sources() {
  py selftest
  py lakefile "$F"
  py sources "$F"
}

guard_axioms() {
  local out trusted roots libdir sysroot lp tmp rc
  out="$(py roots "$F")"
  trusted="$(sed -n 1p <<<"$out")"
  roots="$(sed -n 2p <<<"$out")"
  [[ -n "$roots" ]] || die "no default-target roots in formal/lakefile.toml"
  libdir="$F/.lake/build/lib/lean"
  [[ -d "$libdir" ]] || die "no $libdir; run lake build first"
  # The build output may come from an untrusted build (CI job `build`), so no Lean code of it
  # may run here, and nothing in it may stand in for the toolchain: not `lake env` (it puts
  # formal/.lake/build/bin first on PATH and formal/.lake/build/lib on the shared-library
  # path), but the toolchain's own lean with LEAN_PATH = toolchain library, then the packages
  # of the manifest, then the project's build (so no project .olean can shadow Init, Lean,
  # Lake or a package module), and no dynamic-loader variables.
  py buildtree "$F"
  sysroot="$(cd "$F" && lean --print-prefix)"
  [[ -x "$sysroot/bin/lean" && -d "$sysroot/lib/lean" ]] || die "no Lean toolchain at '$sysroot'"
  lp="$(py leanpath "$F")"
  tmp="$(mktemp -d)"
  rc=0
  # shellcheck disable=SC2086 # roots is a space-separated list of module names
  (cd "$F" && env -u LD_LIBRARY_PATH -u LD_PRELOAD -u DYLD_LIBRARY_PATH -u DYLD_INSERT_LIBRARIES \
      -u DYLD_FALLBACK_LIBRARY_PATH LEAN_SYSROOT="$sysroot" LEAN_PATH="$sysroot/lib/lean:$lp" \
      "$sysroot/bin/lean" --run "$ROOT/scripts/lean-axiom-audit.lean" "$libdir" "$trusted" \
      "$tmp/axioms.txt" "$tmp/native.txt" $roots) || rc=$?
  if [[ $rc -eq 0 ]]; then
    if [[ -f "$tmp/axioms.txt" && -f "$tmp/native.txt" ]]; then
      # Both locks are compared (and reported) even if the first comparison fails.
      py axiom-lock "$F/trusted/axioms.lock" "$tmp/axioms.txt" || rc=$?
      py native-lock "$F/trusted/native-axioms.lock" "$tmp/native.txt" || rc=$?
    else
      printf '[lean-guard] error: the audit wrote no trusted-axiom or native-axiom list\n' >&2; rc=1
    fi
  fi
  rm -f "$tmp/axioms.txt" "$tmp/native.txt"; rmdir "$tmp"
  return "$rc"
}

guard_aeneas_archive() {
  local tag lake archives=() a olean
  tag="$(awk '
    /^[[:space:]]*\[/ { in_req = ($0 ~ /^[[:space:]]*\[\[require\]\]/); is_aeneas = 0; rev = ""; next }
    in_req && /^[[:space:]]*name[[:space:]]*=[[:space:]]*"aeneas"[[:space:]]*(#.*)?$/ { is_aeneas = 1 }
    in_req && /^[[:space:]]*rev[[:space:]]*=/ { rev = $0 }
    in_req && is_aeneas && rev != "" { sub(/^[^"]*"/, "", rev); sub(/".*$/, "", rev); print rev; exit }
  ' "$F/lakefile.toml")"
  [[ -n "$tag" ]] || die "no rev for the aeneas requirement in formal/lakefile.toml"
  [[ -d "$F/.lake/packages/aeneas" ]] || die "Aeneas package not fetched; run lake build first"
  lake="$F/.lake/packages/aeneas/backends/lean/.lake"
  if [[ -d "$lake" ]]; then
    while IFS= read -r a; do archives+=("$a"); done \
      < <(find "$lake" -maxdepth 1 -type f -name 'lean-build-aeneas-*.tar.gz' | sort)
  fi
  if [[ ${#archives[@]} -eq 0 ]]; then
    olean=""
    [[ ! -d "$lake/build" ]] || olean="$(find "$lake/build" -name '*.olean' -print -quit)"
    if [[ -z "$olean" ]]; then
      log "no Aeneas build and no release archive (nothing built yet)"
      return 0
    fi
    [[ "${LEAN_GUARD_AENEAS_FROM_SOURCE:-}" == "1" ]] \
      || die "the Aeneas library has .olean files but no verified release archive; set LEAN_GUARD_AENEAS_FROM_SOURCE=1 only if it was built from its pinned sources"
    log "no Aeneas release archive: built from source (LEAN_GUARD_AENEAS_FROM_SOURCE=1)"
    return 0
  fi
  [[ ${#archives[@]} -eq 1 ]] || die "more than one Aeneas release archive in $lake: ${archives[*]}"
  a="${archives[0]}"
  "$ROOT/scripts/aeneas-install.sh" --verify "$a" "$tag/$(basename "$a")"
  py archive "$lake" "$a"
}

case "${1:-}" in
  fresh) [[ $# -eq 1 ]] || die "usage: $0 fresh"; py fresh "$F" ;;
  sources) [[ $# -eq 1 ]] || die "usage: $0 sources"; guard_sources ;;
  build-log) [[ $# -eq 2 ]] || die "usage: $0 build-log FILE"; py build-log "$2" ;;
  axioms) [[ $# -eq 1 ]] || die "usage: $0 axioms"; guard_axioms ;;
  aeneas-archive) [[ $# -eq 1 ]] || die "usage: $0 aeneas-archive"; guard_aeneas_archive ;;
  unpack-build) [[ $# -eq 2 ]] || die "usage: $0 unpack-build TAR"; py unpack "$2" "$F" ;;
  *) die "usage: $0 fresh | sources | build-log FILE | axioms | aeneas-archive | unpack-build TAR" ;;
esac
