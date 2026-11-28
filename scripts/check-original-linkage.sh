#!/usr/bin/env bash
# Linkage check for the Phase 2 targets (master plan (git history at 9047c72), Section 19).
#
# What it shows, in two parts:
#  (a) The SDK source is upstream (origin/main 7caec76), checked on the committed tree (HEAD):
#      the tree of crates/rmcp/src is PINNED_SRC_TREE; every other tracked file under crates/
#      plus the root Cargo.toml (mode, blob id, path) hashes to PINNED_CRATES_DIGEST, leaving out
#      only crates/rmcp/Cargo.toml; and that manifest, with its [package.metadata.charon] table
#      removed, hashes to PINNED_MANIFEST_DIGEST (so no [lib] path, feature or dependency differs
#      from upstream). The working tree has no change, deletion, untracked, skip-worktree or
#      assume-unchanged file under crates/, Cargo.toml or formal/translation/.
#  (b) The translation does not depend on any translation patch: translated from that source with
#      NO patch applied, every block of Funs.lean, Types.lean and the two External templates equals
#      a block of the committed formal/translation/, up to the `Source: '…', lines …` docstring
#      field (patch 01 shifts the line numbers of model.rs by two), with every block holding at
#      most one declaration; and (step 5, which decides, human decision 2026-11-26) built as Lean,
#      every constant of the unmodified-source translation elaborates identically in the committed
#      one, its externals have the same types, and what the committed translation modules export
#      besides constants (instances, reducibility, environment-extension entries, new names
#      outside `rmcp.`) differs only as Aeneas's new declarations make it differ; see the step-5
#      comment for the exact rules, the gates it relies on (scripts/lean-guard.sh sources, the CI
#      stale-translation check) and its two stated limits (the hand-written
#      formal/trusted/Rmcp/*.lean; attribute entries of the growing extensions on existing
#      constants). The text scan of step 4 below is a fail-closed pre-check, not the guarantee.
# A Phase 2 record may say `linkage: ORIGINAL` only while this passes on its commit. Not covered
# (stated in plan Section 19): a patch that changes the BODY of an `opaque` SDK item reached by a
# Phase 2 target is invisible to any comparison of translations (only its signature is
# translated); the script therefore requires the SDK-side opaque list to be exactly
# rmcp::transport::auth::AuthorizationManager (a type with no body; SDK_OPAQUE below), no SDK item
# excluded, and no unmodified-source External template citing crates/rmcp/src (the SDK_OPAQUE
# test only sees entries starting with `rmcp::`; an impl-first pattern such as `{impl … for
# rmcp::…}` is caught by the template check instead, S23 review 2026-11-24); a committed-only
# (patched) declaration, or a name Lean generates for a committed-only structure or inductive
# (constructor, projections, recursors), that could shadow a name used in a Phase 2 block also
# fails. The scan reads only the layout Aeneas emits and fails closed ("cannot be scanned") on
# anything else, on both sides: every block holds exactly one declaration whose head (attributes,
# noncomputable/private/partial/unsafe, keyword, full name) it reads and that only docstrings or
# comments precede, or every code line of the block is exactly one header command (module,
# import, `@[expose] public section`, `open` of plain namespaces without in/renaming/hiding,
# set_option, namespace, end, section); a committed header block must also be one of the
# unmodified source; no `extends`; no
# `where` or `let rec` auxiliary declaration in a def/theorem/abbrev/opaque; structure/class
# members `  f g : T` or `  C ::` and inductive constructors `| C : T` or `| C`, one per line after
# a head that `where` ends; no interpolated string (`s!"…"`); no non-ASCII letter Lean does not
# read as one. One lexer pass drops string literals (also raw r#"…"#), char literals, `--` and
# nested `/- … -/` comments; identifiers follow Lean's rules (letter-like ranges, subscripts,
# `«…»`) and are compared without guillemets. The block's own declared name and identifiers
# whose first segment is a parameter of the declaration's own signature (a binder group at
# bracket depth 0 before the type colon, only when a depth-0 `:=` follows, and only after its
# group closes: not in earlier binders, its own type or its default value) are no lookups (human
# decisions 2026-11-25 and 2026-11-26, patch 05; reviews a1-2, a2-1, b2-1, a3-1, b3-1, a4-1, b4-1,
# b4-2; negative controls formal/trusted/evidence/linkage-scan/, git history at 9047c72); nor
# (human decision XD2, 2026-11-28, patch 08) a one-segment identifier directly before a `:=` of
# the body that is a binder or a field name: after `let`, `let mut` or `have`, after `(` (a named
# argument), or a structure-instance field (innermost bracket `{`, no `:` before it inside that
# brace at its depth, and after `{`, `,`, `with` or first on its line). Two committed-side
# differences of a std trait-instance block (`@[reducible, rust_trait_impl …]` with a
# `/rustc/` Source) are accepted (XD2): extra fields that only the committed block sets (Aeneas
# emits a field only for a method the translated code reaches; the others take the defaults of
# the Aeneas structure), with `def` becoming `impl_def` when one of them refers to the instance
# itself; and a token `P.m` read as field access on such a committed-only instance block `P`
# whose field is `m := P.m` (both readings name the same function). Step 5 then checks that the
# elaborated values differ exactly at those extra fields, that each extra field is definitionally
# equal (with the hand-written externals) to the default the unmodified side gets or is projected
# by no definition reachable from the unmodified-source translation or the external models (review
# finding TR4), and that every unmodified-source constant elaborates identically. Positive and
# negative controls of these XD2 rules (the binder branches `let`, `let mut`, `have`, `(x :=` and
# structure-instance fields; the instance rule; the TR4 rule, on the run's results and end to end
# on a synthetic translation): `python3 -I scripts/linkage/controls.py <scratch-dir>
# <controls-dir>` after a passing run (reviews TR4, TR10). Not read by this pre-check, and
# covered by step 5 (formal/trusted/evidence/linkage-elab/, git history at 9047c72): names
# resolved through the type of a term (generalized field notation `t.a`, `(e).a`, `e |>.a`, and
# leading-dot `.a` resolved against the expected type; linkage-scan/limits/), generated names
# beyond those listed in auto_names (e.g. anonymous instance names), and the forms of reviews
# a5-1/a5-2/a5-3. Covered by neither: declarations of the hand-written
# formal/trusted/Rmcp/*.lean (the trusted base; step 5 builds both sides with the generated
# templates, and reads the hand-written externals only in env2, for the committed-only instance
# fields of review finding TR4). Not pinned:
# dependency resolution beyond PINNED_DEPS (workspace members outside crates/ take part in it;
# both sides of the comparison share it, and the stale-translation check requires a clean tree).
#
# How: copy the tracked files into <scratch-dir>/src, rewrite only the copy's
# [package.metadata.charon] (drop the Phase 1 start points rmcp::model::request_state{,_wire},
# which exist only with patch 01, and the skills start points of K05-K07, K13-K16, which need
# patch 04; drop the opaque function entries ...::request_state_wire::prim,
# ...::request_state::_::now_ms and ...::skill::prim (patch 04); drop the patch-05 start points of
# metadata_resolver.rs (N03-N07, N09-N11 and the helpers with_base_url, proxy_host,
# allowed_addresses; N01 and N08 stay) and the opaque entries ...::metadata_resolver::{Lookup, prim};
# drop the seven patch-06 start points of auth.rs (A04-A10, none ORIGINAL) and the opaque entry
# ...::auth::prim; drop the four patch-07 start points of mcp_headers.rs (G01-G04, none ORIGINAL)
# and the opaque entry ...::mcp_headers::prim; drop the eight patch-08 start points of
# elicitation_schema.rs (X29, X32/X35, X33/X38, X36, X37, X40, X74, X75; the other targets
# X01-X75 stay, ORIGINAL) and the opaque entry ...::elicitation_schema::prim;
# keep the other exclude entries outside
# rmcp::model::request_state*; keep hide_marker_traits), then run scripts/aeneas-translate.sh on
# that copy with RMCP_NO_PATCHES=1 and RMCP_TARGET_SET=phase2 into <scratch-dir>/out, so every
# toolchain, environment, dependency, glob and target check of the real translation applies.
#
# Usage: scripts/check-original-linkage.sh <scratch-dir>
#   <scratch-dir>  outside the repository; new, empty, or an earlier run's (marker
#                  .rmcp-linkage-dir). src/ and out/ are replaced; llbc/ is the translate
#                  script's work directory (its work/, out/ and cargo-home/ are replaced by it,
#                  target/ is kept as a build cache).
# Writes only inside <scratch-dir>. Step 5 also reads the Lean packages of formal/.lake/packages
# and refuses to run unless Aeneas and Mathlib are built there (`lake exe cache get && lake build
# Aeneas` in formal), so Lake does not build them in place (review a6-4).
set -euo pipefail

# Tree id of crates/rmcp/src at upstream origin/main 7caec762799bece6fba38e4298b8ca7db8bac12c
# (`git rev-parse 7caec76:crates/rmcp/src`). Changing the pinned commit changes this value.
PINNED_SRC_TREE="4efe696aeae5f3c4ba89a3c83145a93f901feaa2"
# sha256 of the `git ls-tree -r <rev> -- crates Cargo.toml` lines without crates/rmcp/Cargo.toml
# (203 lines at 7caec76), and sha256 of crates/rmcp/Cargo.toml parsed with tomllib, its
# [package.metadata.charon] table removed, serialised with json.dumps(sort_keys=True); both equal
# at 7caec76 and at the S22 commit. Stored here because CI checks out at depth 1.
PINNED_CRATES_DIGEST="0be33db37cc195f951ca4c2095ffe5091edcb24de7aeef8bfb6f998914706c84"
PINNED_MANIFEST_DIGEST="75e978b5c8d0e0e549cdff137a2db03de4464ef58f047b213ef2d8af866ecb4e"

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
log() { printf '[linkage] %s\n' "$*"; }
die() { printf '[linkage] error: %s\n' "$*" >&2; exit 1; }

[[ $# -eq 1 ]] || die "usage: $0 <scratch-dir>"
# shellcheck source=scripts/llbc-dir-guard.sh
source "$ROOT/scripts/llbc-dir-guard.sh"   # canon_path, within

# Scratch directory guard (its own, not check_llbc_dir; <scratch-dir>/llbc goes through that one
# inside aeneas-translate.sh). The path is checked before anything is created.
base="$(basename "$1")"
[[ -n "$base" && "$base" != "." && "$base" != ".." && "$base" != "/" ]] \
  || die "refused scratch directory $1 (its last component must be a plain name)"
parent="$(dirname "$1")"
[[ -d "$parent" ]] || die "the parent of the scratch directory ($parent) does not exist"
SCR="$(canon_path "$parent")/$(basename "$1")"
[[ ! -L "$SCR" ]] || SCR="$(canon_path "$SCR")"
ROOT_C="$(canon_path "$ROOT")"
within "$SCR" "$ROOT_C" && die "the scratch directory ($SCR) must lie outside the repository"
within "$ROOT_C" "$SCR" && die "the scratch directory ($SCR) contains the repository"
HOME_C="$(canon_path "$HOME")"
[[ "$SCR" != "/" ]] && ! within "$HOME_C" "$SCR" || die "refused scratch directory $SCR (/, \$HOME or an ancestor)"
if [[ -e "$SCR" ]]; then
  [[ -d "$SCR" ]] || die "$SCR exists and is not a directory"
  if [[ -n "$(ls -A "$SCR")" && ! -f "$SCR/.rmcp-linkage-dir" ]]; then
    die "$SCR is not empty and has no marker .rmcp-linkage-dir from an earlier run"
  fi
fi
mkdir -p "$SCR"
touch "$SCR/.rmcp-linkage-dir"
for d in src out; do
  [[ ! -L "$SCR/$d" ]] || die "$SCR/$d is a symlink"
  rm -rf "${SCR:?}/$d"
done

# (a) The SDK source is the pinned upstream tree, unchanged in the working tree.
got_tree="$(git -C "$ROOT" rev-parse HEAD:crates/rmcp/src)" || die "git rev-parse failed"
[[ "$got_tree" == "$PINNED_SRC_TREE" ]] \
  || die "crates/rmcp/src at HEAD is tree $got_tree, not the pinned upstream tree $PINNED_SRC_TREE (7caec76)"
digests="$(cd "$ROOT" && python3 -I -c '
import hashlib, json, subprocess, tomllib
out = subprocess.run(["git", "ls-tree", "-r", "HEAD", "--", "crates", "Cargo.toml"],
                     capture_output=True, text=True, check=True).stdout
lines = [l for l in out.splitlines() if l.split("\t", 1)[1] != "crates/rmcp/Cargo.toml"]
print(hashlib.sha256(("\n".join(lines) + "\n").encode()).hexdigest())
man = subprocess.run(["git", "show", "HEAD:crates/rmcp/Cargo.toml"],
                     capture_output=True, text=True, check=True).stdout
d = tomllib.loads(man)
d.get("package", {}).get("metadata", {}).pop("charon", None)
print(hashlib.sha256(json.dumps(d, sort_keys=True).encode()).hexdigest())
')" || die "computing the source digests failed"
read -r got_crates got_manifest <<<"$(tr '\n' ' ' <<<"$digests")"
[[ "$got_crates" == "$PINNED_CRATES_DIGEST" ]] \
  || die "the tracked files under crates/ and Cargo.toml (without crates/rmcp/Cargo.toml) differ from upstream 7caec76 (digest $got_crates)"
[[ "$got_manifest" == "$PINNED_MANIFEST_DIGEST" ]] \
  || die "crates/rmcp/Cargo.toml outside [package.metadata.charon] differs from upstream 7caec76 (digest $got_manifest)"
dirty="$(git -C "$ROOT" status --porcelain --untracked-files=all -- crates Cargo.toml formal/translation)"
[[ -z "$dirty" ]] || { printf '%s\n' "$dirty" >&2; die "uncommitted, deleted or untracked files under crates/, Cargo.toml or formal/translation/"; }
hidden="$(git -C "$ROOT" ls-files -v -- crates Cargo.toml formal/translation | grep -E '^([a-z]|S) ' || true)"
[[ -z "$hidden" ]] || { printf '%s\n' "$hidden" >&2; die "skip-worktree or assume-unchanged files under crates/, Cargo.toml or formal/translation/"; }
log "source is upstream 7caec76 (src tree $PINNED_SRC_TREE, crates digest and manifest digest pinned); working tree clean"

# 1. The tracked files of the repository (formal/ is not needed for the translation).
command -v rsync >/dev/null || die "rsync not found"
git -C "$ROOT" ls-files -z -- . ':!:formal' | rsync -a --from0 --files-from=- "$ROOT/" "$SCR/src/" \
  || die "copying the tracked files failed (a tracked file missing from the working tree?)"
log "copied the tracked files of $ROOT (without formal/) to $SCR/src"

# 2. Rewrite the copy's [package.metadata.charon].
python3 -I - "$SCR/src/crates/rmcp/Cargo.toml" <<'PY'
import json, re, sys, tomllib
path = sys.argv[1]
text = open(path, encoding="utf-8").read()
meta = tomllib.loads(text)["package"]["metadata"]["charon"]
unknown = set(meta) - {"start_from", "exclude", "opaque", "hide_marker_traits"}
if unknown:
    sys.exit(f"[package.metadata.charon] has keys the rewrite does not handle: {sorted(unknown)}")
phase1 = {"rmcp::model::request_state", "rmcp::model::request_state_wire"}
if not phase1 <= set(meta["start_from"]):
    sys.exit("start_from lacks the Phase 1 modules rmcp::model::request_state{,_wire}")
# Skills start points whose targets need translation patch 04 (K05-K07, K13-K16); the other
# skills start points (K01-K04, K08-K12, K17-K20) are ORIGINAL (human decision 2026-11-25).
patch04 = {"rmcp::model::skill::_::from_bytes", "rmcp::model::skill::_::verify",
           "rmcp::model::skill::sha256_digest", "rmcp::model::skill::_::validate",
           "rmcp::model::skill::skill_name_from_uri", "rmcp::model::skill::is_sha256_digest",
           "rmcp::model::skill::validate_skills"}
if not patch04 <= set(meta["start_from"]):
    sys.exit(f"start_from lacks the patch-04 skills start points {sorted(patch04 - set(meta['start_from']))}")
# metadata_resolver.rs start points whose targets need translation patch 05 (N03-N07, N09-N11 and
# the patch-05 helpers); N01 and N08 are ORIGINAL.
mr = "rmcp::transport::auth::metadata_resolver::"
patch05 = {mr + "_::new", mr + "_::with_base_url", mr + "_::allowed_addresses",
           mr + "_::with_proxy_hosts", mr + "_::allowing_private_addresses", mr + "_::allows_url",
           mr + "literal_ip", mr + "proxy_host", mr + "normalize_host"}
if not patch05 <= set(meta["start_from"]):
    sys.exit(f"start_from lacks the patch-05 start points {sorted(patch05 - set(meta['start_from']))}")
# auth.rs start points of translation patch 06 (A04-A10); none is ORIGINAL.
au = "rmcp::transport::auth::_::"
patch06 = {au + n for n in (
    "is_http_url", "is_disallowed_metadata_host", "is_allowed_metadata_url",
    "resolve_resource_metadata_url", "check_authorization_response_issuer",
    "check_authorization_metadata_issuer", "check_resource_metadata_resource")}
if not patch06 <= set(meta["start_from"]):
    sys.exit(f"start_from lacks the patch-06 start points {sorted(patch06 - set(meta['start_from']))}")
# mcp_headers.rs start points of translation patch 07 (G01-G04); none is ORIGINAL.
mh = "rmcp::transport::common::mcp_headers::"
patch07 = {mh + n for n in (
    "requires_base64", "is_tchar", "encode_header_value", "decode_header_value")}
if not patch07 <= set(meta["start_from"]):
    sys.exit(f"start_from lacks the patch-07 start points {sorted(patch07 - set(meta['start_from']))}")
# elicitation_schema.rs start points of translation patch 08 (X29, X32, X33, X35-X38, X40, X74, X75;
# the `Type::method` patterns `with_default` and `build` of EnumSchemaBuilder each match the
# SingleSelect and the MultiSelect method). X75 build_unchecked is in no hunk but calls X74.
es = "rmcp::model::elicitation_schema::"
patch08 = {es + n for n in (
    "EnumSchemaBuilder::enum_titles", "EnumSchemaBuilder::with_default",
    "EnumSchemaBuilder::min_items", "EnumSchemaBuilder::max_items", "EnumSchemaBuilder::build",
    "ElicitationSchema::new",
    "ElicitationSchemaBuilder::build", "ElicitationSchemaBuilder::build_unchecked")}
if not patch08 <= set(meta["start_from"]):
    sys.exit(f"start_from lacks the patch-08 start points {sorted(patch08 - set(meta['start_from']))}")
start = [s for s in meta["start_from"]
         if s not in phase1 and s not in patch04 and s not in patch05 and s not in patch06
         and s not in patch07 and s not in patch08]
if not start:
    sys.exit("start_from has no Phase 2 entries")
opaque = [o for o in meta["opaque"] if o not in (
    "rmcp::model::request_state_wire::prim", "rmcp::model::request_state::_::now_ms",
    "rmcp::model::skill::prim", "rmcp::transport::auth::metadata_resolver::Lookup",
    "rmcp::transport::auth::metadata_resolver::prim", "rmcp::transport::auth::prim",
    "rmcp::transport::common::mcp_headers::prim", "rmcp::model::elicitation_schema::prim")]
exclude = [e for e in meta["exclude"] if not e.startswith("rmcp::model::request_state")]
hide = meta.get("hide_marker_traits", False)
def arr(xs):
    return "[\n" + "".join(f"  {json.dumps(x)},\n" for x in xs) + "]"
block = ("[package.metadata.charon]\n"
         "# Rewritten by scripts/check-original-linkage.sh (unmodified source, Phase 2 only).\n"
         f"start_from = {arr(start)}\nhide_marker_traits = {'true' if hide else 'false'}\n"
         f"exclude = {arr(exclude)}\nopaque = {arr(opaque)}\n")
m = re.search(r"^\[package\.metadata\.charon\]\n.*?(?=^\[)", text, re.S | re.M)
if not m:
    sys.exit("no [package.metadata.charon] table followed by another table")
new = text[:m.start()] + block + "\n" + text[m.end():]
# The SDK-side settings the Phase 2 translation was reviewed with (plan Section 19): the only
# opaque SDK item is the type AuthorizationManager (no body), nothing of the SDK is excluded,
# marker traits hidden. Any change needs the affected records reassessed (a new opaque or
# excluded SDK item hides its body from this check) and an edit of this list in a reviewed PR.
# exclude is ["serde"] since serde_core became opaque for open_json/open_json_with (translation
# patch 03; lead decision 2026-11-24 on the human decision of targets R09-R15).
SDK_OPAQUE = ["rmcp::transport::auth::AuthorizationManager"]
# The external crates that are opaque (signatures only), exactly and in this order. serde_core is
# opaque instead of excluded since translation patch 03 (lead decision 2026-11-24 on the human
# decision of targets R09-R15): it must stay in this list, and no other crate may be added to or
# removed from it (a crate leaving the list would be translated or excluded, a new one would hide
# bodies) without a reviewed edit here.
EXTERNAL_OPAQUE = [
    "zeroize", "base64", "hmac", "sha2", "thiserror", "chrono", "serde_json",
    "serde_core",
    "http", "tokio", "tokio_util", "tracing", "tracing_core", "futures", "futures_util",
    "futures_core", "bytes", "sse_stream", "hyper", "tower_service", "uuid", "schemars",
    "pin_project_lite", "tokio_stream", "http_body", "http_body_util", "rand", "async_trait",
    "pastey", "oauth2", "reqwest", "url::Url",
]
external_opaque = [o for o in opaque if not o.startswith("rmcp::")]
if [o for o in opaque if o.startswith("rmcp::")] != SDK_OPAQUE or exclude != ["serde"] \
        or external_opaque != EXTERNAL_OPAQUE or hide is not True:
    sys.exit(f"[package.metadata.charon] SDK-side settings differ from the reviewed ones "
             f"(opaque SDK items {[o for o in opaque if o.startswith('rmcp::')]}, exclude {exclude}, "
             f"opaque external crates {external_opaque}, hide_marker_traits {hide}); reassess the "
             "Phase 2 records (plan Section 19) and update SDK_OPAQUE/EXTERNAL_OPAQUE in "
             "scripts/check-original-linkage.sh in a reviewed PR")
check = tomllib.loads(new)["package"]["metadata"]["charon"]   # the rewrite must parse back
assert (check["start_from"] == start and check["opaque"] == opaque and check["exclude"] == exclude
        and check["hide_marker_traits"] == hide)
open(path, "w", encoding="utf-8").write(new)
print(f"[linkage] start_from: {len(start)} Phase 2 entries; exclude: {exclude}; "
      f"opaque: {len(opaque)} entries; hide_marker_traits = {hide}")
PY

# 3. Translate the unmodified copy with the real translation script.
log "translating the unmodified source (RMCP_NO_PATCHES=1, RMCP_TARGET_SET=phase2)"
RMCP_SOURCE_ROOT="$SCR/src" RMCP_LLBC_DIR="$SCR/llbc" RMCP_TRANSLATION_DEST="$SCR/out" \
  RMCP_NO_PATCHES=1 RMCP_TARGET_SET=phase2 "$ROOT/scripts/aeneas-translate.sh" \
  || die "translation of the unmodified source failed"

# 4. Compare with the committed translation. The two External templates are git-ignored files of
# formal/translation/Rmcp/ written by aeneas-translate.sh (in CI by the regeneration step just
# before; locally by the last run).
rm -f "$SCR/instance-fields.json"
python3 -I - "$SCR/out/Rmcp" "$ROOT/formal/translation/Rmcp" "$SCR/instance-fields.json" <<'PY'
import os, re, sys
scratch, committed, widened_out = sys.argv[1:]
src = re.compile(r"Source: '([^']*)', lines [0-9:-]+")
macro_src = re.compile(r"macro invocation at: '([^']*)', lines [0-9:-]+")
ALLOWED_SRC = ("crates/rmcp/src/", "/rustc/", "/cargo/registry/")
# A header block: every code line (comments and docstrings blanked) is exactly one of these
# commands; `open … in`, `open … renaming/hiding`, a command after a comment on the same line, or
# any other command is not a header (fail closed; round-4 records review, 2026-11-26).
HEADER = re.compile(r"^(module|(?:public )?import \S+|@\[expose\] public section|"
                    r"open(?!.*\b(?:in|renaming|hiding)\b)(?: [A-Za-z_][A-Za-z0-9_.]*)+|"
                    r"set_option \S+ \S+|namespace \S+|end(?: \S+)?|noncomputable section|section)$")
def blocks(path):
    raw = open(path, encoding="utf-8").read()
    # Aeneas >= nightly-2026.11.24 adds "this code is generated from a macro invocation at: '…',
    # lines …" to the Source field; its line numbers shift with patch 01 like the Source lines.
    norm = macro_src.sub("macro invocation at: <normalised>", src.sub("Source: <normalised>", raw))
    return raw, [b for b in norm.split("\n\n") if b.strip()]
# Identifiers follow Lean's rules (Lean.isIdFirst/isIdRest/isLetterLike/isSubScriptAlnum):
# ASCII letters, `_` and the letter-like ranges (Greek except λ Π Σ, Coptic, polytonic Greek,
# the Letterlike Symbols block, mathematical alphanumerics) start a segment; digits, `'`, `!`, `?`
# and subscripts may follow; a segment may also be «…». Names are compared without guillemets,
# since `«x»` and `x` denote the same name (reviews a3-1, b3-1, a4-1, b4-1).
def letter_like(c):
    o = ord(c)
    return ((0x3B1 <= o <= 0x3C9 and o != 0x3BB) or (0x391 <= o <= 0x3A9 and o not in (0x3A0, 0x3A3))
            or 0x3CA <= o <= 0x3FB or 0x1F00 <= o <= 0x1FFE or 0x2100 <= o <= 0x214F
            or 0x1D49C <= o <= 0x1D59F)
def sub_alnum(c):
    o = ord(c)
    return 0x2080 <= o <= 0x2089 or 0x2090 <= o <= 0x209C or 0x1D62 <= o <= 0x1D6A or o == 0x2C7C
def id_start(c):
    return ("a" <= c <= "z") or ("A" <= c <= "Z") or c == "_" or letter_like(c)
def id_rest(c):
    return id_start(c) or ("0" <= c <= "9") or c in "'!?" or sub_alnum(c)
class Unscannable(Exception):
    pass
LL = "".join(chr(o) for o in range(0x80, 0x10000) if letter_like(chr(o)) or sub_alnum(chr(o)))
LL_RE = re.escape(LL)
SEG = rf"(?:«[^»\n]*»|[A-Za-z_{LL_RE}][A-Za-z0-9_'!?{LL_RE}]*)"
NAME = rf"{SEG}(?:\.{SEG})*"
def canon(n):
    return re.sub(r"«([^»\n]*)»", r"\1", n)
# A declaration head: attributes, the modifiers the scan knows, a keyword and the full name. Any
# other modifier or command (protected, scoped, nonrec, public, notation, macro, irreducible_def,
# …) gives no head, and a block without a head that is not a header line fails on both sides
# (fail closed; review a4-1).
head = re.compile(rf"^(?:@\[.*?\]\s*)*(?:(?:noncomputable|private|partial|unsafe)\s+)*"
                  rf"(def|theorem|axiom|opaque|structure|inductive|class|instance|abbrev|impl_def)\b"
                  rf"\s*({NAME})?", re.M | re.S)
def heads(b):
    return [canon(h[1]) if h[1] else "?" for h in head.findall(b)]
def lex(s, ends=None):
    """Tokens of a block: identifiers (canonical, with their dotted segments) and punctuation.
    If ENDS is a list, the offset in S reached when each token was read is appended to it (the
    end of an identifier, string or char literal; the start of a punctuation token), so that a
    newline in s[ends[j-1]:ends[j]] means that the identifier j is the first token of its line.
    One left-to-right pass drops string literals (also raw r#"…"#), char literals, `--` line
    comments and nested `/- … -/` comments, so that none of them can hide or fake code
    (reviews a2-1, b2-1, a3-1, b3-1). An interpolated string (`s!"…"`, `m!"…"`, …, whose `{…}`
    holds code) or a non-ASCII letter Lean does not accept raises Unscannable (review a4-1, b4-1)."""
    out, i, n = [], 0, len(s)
    if ends is not None:
        class Toks(list):
            def append(self, t):
                list.append(self, t); ends.append(i)
        out = Toks()
    def prev_is_id(k):
        return k > 0 and (id_rest(s[k - 1]) or s[k - 1] == "»")
    while i < n:
        c = s[i]
        if s.startswith("--", i):
            j = s.find("\n", i); i = n if j < 0 else j; continue
        if s.startswith("/-", i):
            d, i = 1, i + 2
            while i < n and d:
                if s.startswith("/-", i): d += 1; i += 2
                elif s.startswith("-/", i): d -= 1; i += 2
                else: i += 1
            continue
        if c == "r" and not prev_is_id(i):
            m = re.match(r'r(#*)"', s[i:])
            if m:
                close = '"' + m.group(1)
                j = s.find(close, i + len(m.group(0)))
                i = n if j < 0 else j + len(close); out.append(("str", "")); continue
        if c == '"':
            if re.search(r"!\s*(?:r#*)?$", s[max(0, i - 64):i]):   # s!"…", s! "…", s!r"…" (a5-4)
                raise Unscannable("interpolated string")
            i += 1
            while i < n and s[i] != '"':
                i += 2 if s[i] == "\\" else 1
            i += 1; out.append(("str", "")); continue
        if c == "'" and not prev_is_id(i):
            if i + 1 < n and s[i + 1] == "\\":
                j = s.find("'", i + 3)
                if j > 0: i = j + 1; out.append(("chr", "")); continue
            elif i + 2 < n and s[i + 2] == "'":
                i += 3; out.append(("chr", "")); continue
        if id_start(c) or c == "«":
            segs = []
            while True:
                if i < n and s[i] == "«":
                    j = s.find("»", i)
                    if j < 0: raise Unscannable("unterminated «")
                    segs.append(s[i + 1:j]); i = j + 1
                else:
                    j = i + 1
                    while j < n and id_rest(s[j]): j += 1
                    segs.append(s[i:j]); i = j
                if i < n and ord(s[i]) > 127 and s[i].isalnum():
                    raise Unscannable(f"character {s[i]!r} in an identifier")
                if i + 1 < n and s[i] == "." and (id_start(s[i + 1]) or s[i + 1] == "«"):
                    i += 1; continue
                break
            out.append(("id", canon(".".join(segs)))); continue
        if ord(c) > 127 and c.isalnum():
            raise Unscannable(f"character {c!r} that Lean does not read as a letter")
        if c.isdigit():
            while i < n and (s[i].isalnum() or s[i] == "_" or (s[i] == "." and i + 1 < n and s[i + 1].isdigit())):
                i += 1
            continue
        if s.startswith(":=", i) or s.startswith("::", i):
            out.append(("p", s[i:i + 2])); i += 2; continue
        if not c.isspace():
            out.append(("p", c))
        i += 1
    return list(out)
def code_lines(s):
    """The block with comments and literals blanked (newlines and columns kept)."""
    out, i, n = list(s), 0, len(s)
    def blank(a, b):
        for k in range(a, min(b, n)):
            if out[k] != "\n": out[k] = " "
    while i < n:
        if s.startswith("--", i):
            j = s.find("\n", i); j = n if j < 0 else j; blank(i, j); i = j; continue
        if s.startswith("/-", i):
            a, d, i = i, 1, i + 2
            while i < n and d:
                if s.startswith("/-", i): d += 1; i += 2
                elif s.startswith("-/", i): d -= 1; i += 2
                else: i += 1
            blank(a, i); continue
        if s[i] == '"':
            a = i; i += 1
            while i < n and s[i] != '"':
                i += 2 if s[i] == "\\" else 1
            i += 1; blank(a + 1, i - 1); continue
        i += 1
    return "".join(out).split("\n")
def is_header(b):
    return all(not l.strip() or HEADER.match(l.strip()) for l in code_lines(b))
def head_first(b):
    """A block with a declaration starts with it: every code line before the head's first line
    (attributes included in the head) is blank, i.e. only docstrings or comments precede it."""
    m = head.search(b)
    return m is not None and not any(l.strip() for l in code_lines(b[:m.start()]))
FIELD = re.compile(rf"^([ \t]+)((?:{SEG}[ \t]+)*{SEG})[ \t]*:(?![:=])")
CTOR_NAME = re.compile(rf"^([ \t]+)({SEG})[ \t]*::[ \t]*$")
CTOR = re.compile(rf"^([ \t]*)\|[ \t]*({SEG})[ \t]*(?::(?!=)[^|]*)?$")
def type_members(b, kind, n):
    """Fields and constructor of a structure/class, constructors of an inductive, read line by
    line after `where`. Only the layout Aeneas emits is read: `where` ends the head (alone on its
    line or at its end), every member line at the member indent is `  f g : T` / `  C ::` resp.
    `| C : T` / `| C`, deeper lines continue a member. Anything else (one-line declarations,
    fields with binders, several constructors on a line, …) raises Unscannable (fail closed;
    reviews a4-1, b4-1)."""
    lines = code_lines(b)
    k = next((j for j, l in enumerate(lines) if re.match(rf"^(?:@\[.*\]\s*)*{kind}\b", l.strip())), None)
    if k is None:
        raise Unscannable(f"{kind} {n}: head line not found")
    w = next((j for j in range(k, len(lines)) if re.search(r"(^|\s)where\s*$", lines[j])), None)
    if w is None or any(re.search(r"(^|\s)where(\s|$)", l) for l in lines[k:w]):
        raise Unscannable(f"{kind} {n}: `where` must end a line of the head")
    if any(re.search(r"(^|\s)extends(\s|$)", l) for l in lines[k:w + 1]):
        raise Unscannable(f"{kind} {n}: `extends` (its generated parent projections are not read)")
    body = [l for l in lines[w + 1:] if l.strip()]
    if not body:
        return []
    ind = min(len(l) - len(l.lstrip()) for l in body)
    members = []
    for l in body:
        if len(l) - len(l.lstrip()) > ind:
            continue
        if kind == "inductive":
            m = CTOR.match(l)
            if not m:
                raise Unscannable(f"inductive {n}: constructor line not read: {l.strip()[:60]!r}")
            members.append(("ctor", m.group(2)))
        else:
            m = FIELD.match(l) or CTOR_NAME.match(l)
            if not m:
                raise Unscannable(f"{kind} {n}: field line not read: {l.strip()[:60]!r}")
            if m.re is CTOR_NAME:
                members.append(("ctor", m.group(2)))
            else:
                members.extend(("field", f) for f in re.findall(SEG, m.group(2)))
    return members
def auto_names(b):
    # Names Lean generates for a declared structure or inductive (constructor, field projections,
    # recursors): a committed-only type brings these too, and an unmodified block's identifier
    # could resolve to them (reviews a1-2, a3-1, b3-1, a4-1, b4-1).
    out = set()
    for kind, n in head.findall(b):
        n = canon(n)
        if kind in ("structure", "inductive", "class") and n:
            out.update(n + "." + x for x in ("mk", "mk.injEq", "mk.inj", "rec", "recOn", "casesOn",
                                              "noConfusion", "noConfusionType", "below", "brecOn",
                                              "ctorIdx", "toCtorIdx"))
            for what, x in type_members(b, kind, n):
                x = canon(x)
                if what == "field":
                    out.add(n + "." + x)
                else:
                    out.update((n + "." + x, n + "." + x + ".injEq", n + "." + x + ".inj"))
    return out
OPEN, CLOSE = "({[⦃⟨", ")}]⦄⟩"
DECL = ("def", "theorem", "abbrev", "instance", "opaque", "impl_def", "axiom")
def signature_params(toks):
    """Parameters of the declaration's own signature: the binder groups at bracket depth 0 after
    the declared name and before the type colon `:` at depth 0, and only when a depth-0 `:=`
    follows (a declaration by equations exempts nothing; binders in the result type are not
    exempted; review b3-1). Returns ({name: index of the token closing its group}, indices of the
    binding occurrences). A parameter is in scope only after its group closes: in later binder
    types, the result type and the body, not in earlier binders, its own type or its default
    value (reviews a4-1, b4-2)."""
    k = next((j for j, t in enumerate(toks) if t[0] == "id" and t[1] in DECL), None)
    if k is None:
        return {}, set()
    k += 1
    if k < len(toks) and toks[k][0] == "id":
        k += 1
    params, binders, depth, in_group, before_colon, grp = {}, set(), 0, False, True, []
    pending = []
    for j in range(k, len(toks)):
        kind, t = toks[j]
        if kind == "p" and t in OPEN:
            if depth == 0 and before_colon: in_group, grp = True, []
            depth += 1; continue
        if kind == "p" and t in CLOSE:
            depth -= 1
            if depth == 0:
                for name, idx in pending:
                    params[name] = j; binders.add(idx)
                pending, in_group = [], False
            continue
        if depth == 0 and kind == "p" and t == ":=":
            return params, binders
        if depth == 0 and kind == "p" and t == ":":
            before_colon = False; continue
        if depth == 1 and in_group and kind == "id":
            grp.append((t, j))
        if depth == 1 and in_group and kind == "p" and t == ":":
            pending, in_group = grp, False
    return {}, set()
def assign_binders(s):
    """Indices (into lex(s)) of the identifiers that are binders or field names, not lookups
    (human decision XD2, 2026-11-28): a one-segment identifier directly before a `:=` after the
    declaration's own depth-0 `:=` (in the body), that follows `let`, `let mut` or `have` (a
    binder), or `(` (a named argument), or is a structure-instance field name: its innermost
    open bracket is `{`, no `:` came before it inside that brace at the brace's depth (so it is
    no type in `let x : T :=` or `{ x : T // p }`), and it follows `{`, `,` or `with` or is the
    first token of its line (Aeneas puts instance fields one per line; `calc _ = c := p` is
    excluded). Everything else before a `:=` stays a lookup: the result type of the signature,
    a binder's type before a default value, dotted names (fail closed)."""
    ends = []
    toks = lex(s, ends)
    out, stack, body = set(), [], None
    for j, (kind, t) in enumerate(toks):
        if kind == "p" and t in OPEN:
            stack.append([t, False]); continue
        if kind == "p" and t in CLOSE:
            if stack: stack.pop()
            continue
        if kind == "p" and t == ":" and stack:
            stack[-1][1] = True
        if kind == "p" and t == ":=" and not stack and body is None:
            body = j
        if (kind != "id" or body is None or j <= body or "." in t or j + 1 >= len(toks)
                or toks[j + 1] != ("p", ":=")):
            continue
        prev = toks[j - 1]
        if prev in (("id", "let"), ("id", "have")) or (prev == ("id", "mut") and toks[j - 2] == ("id", "let")):
            out.add(j)
        elif prev == ("p", "("):
            out.add(j)
        elif stack and stack[-1][0] == "{" and not stack[-1][1] and (
                prev in (("p", "{"), ("p", ","), ("id", "with")) or "\n" in s[ends[j - 1]:ends[j]]):
            out.add(j)
    return out
# A std trait-instance block (human decision XD2, 2026-11-28): Aeneas output of the layout
#   /-- Trait implementation: [...] Source: '/rustc/…' … -/
#   @[reducible, rust_trait_impl "…"]
#   def|impl_def <name> : <type> := {
#     <field> := <value>          (one per line at indent 2; deeper lines continue it)
#   }
STD_SRC = re.compile(r"Source: '/rustc/")
INST_ATTR = re.compile(r"^@\[reducible, rust_trait_impl\b", re.M)
INST_FIELD = re.compile(rf"^  ({SEG}) :=(?: .*)?$")
def std_instance(raw, b):
    """(keyword, head text, [(field, text)]) of a std trait-instance block B (normalised; RAW is
    the same block before normalisation), or None for any other block or layout."""
    hs = head.findall(b)
    if len(hs) != 1 or hs[0][0] not in ("def", "impl_def") or not STD_SRC.search(raw) \
            or not INST_ATTR.search(b):
        return None
    lines = b.rstrip("\n").split("\n")
    k = next((j for j, l in enumerate(lines) if l.endswith(":= {")), None)
    if k is None or lines[-1] != "}":
        return None
    fields = []
    for l in lines[k + 1:-1]:
        m = INST_FIELD.match(l)
        if m:
            fields.append([canon(m.group(1)), l])
        elif l.startswith("    ") and fields:
            fields[-1][1] += "\n" + l
        else:
            return None
    return hs[0][0], "\n".join(lines[:k + 1]), [tuple(f) for f in fields]
def std_instances(path):
    """{declared name: std_instance(...)} of the std trait-instance blocks of PATH."""
    raw = open(path, encoding="utf-8").read()
    _, bs = blocks(path)
    rbs = [x for x in raw.split("\n\n") if x.strip()]
    if len(rbs) != len(bs):
        sys.exit(f"[linkage] error: cannot be scanned: {path}: blocks changed by normalisation")
    out = {}
    for r, b in zip(rbs, bs):
        i = std_instance(r, b)
        if i is not None:
            out[heads(b)[0]] = i
    return out
def instance_extra(name, mine, theirs):
    """The fields only the committed std trait-instance block THEIRS sets, if MINE (the
    unmodified-source block of the same name) equals THEIRS up to them: the same head (`def`
    may become `impl_def` only if an extra field names the instance itself), every field of MINE
    with the same text and in the same order in THEIRS, at least one extra field. Else None."""
    (kw0, h0, f0), (kw1, h1, f1) = mine, theirs
    extra = [f for f, _ in f1 if f not in {g for g, _ in f0}]
    if not extra or [x for x in f1 if x[0] not in extra] != list(f0):
        return None
    if (kw0, h0) != (kw1, h1):
        selfref = any(re.search(rf"(?<![\w.]){re.escape(name)}(?![\w.])", t) for f, t in f1 if f in extra)
        if not (kw0 == "def" and kw1 == "impl_def" and selfref
                and re.sub(r"^impl_def ", "def ", h1, count=1, flags=re.M) == h0):
            return None
    return extra
FILES = ("Funs.lean", "Types.lean", "FunsExternal_Template.lean", "TypesExternal_Template.lean")
all_theirs, all_mine = set(), set()
for fname in FILES:
    for d, acc in ((committed, all_theirs), (scratch, all_mine)):
        p = os.path.join(d, fname)
        if os.path.exists(p):
            for b in blocks(p)[1]:
                hs = heads(b)
                # Both sides: one declaration per block, or a header/footer block (fail closed:
                # a committed-only declaration the head pattern cannot read would be missing from
                # EXTRA; review a4-1).
                if len(hs) > 1 or (not hs and not is_header(b)) or (hs and not head_first(b)):
                    sys.exit(f"[linkage] error: cannot be scanned: a block of {p} holds "
                             f"{len(hs)} declarations the scan reads ({', '.join(hs) or 'none'}), not "
                             f"first in the block, or is not a header: {b.strip().splitlines()[-1][:100]!r} "
                             "(plan Section 19)")
                try:
                    if any(not n and kind != "instance" for kind, n in head.findall(b)):
                        raise Unscannable("declaration name not read")
                    if hs and hs[0] != "?":
                        toks = lex(b)
                        kw = next((t for kind, t in toks if kind == "id" and t in DECL), None)
                        # auxiliary declarations (`where`, `let rec`) declare <name>.<aux>
                        if kw in ("def", "theorem", "abbrev", "opaque", "impl_def") and any(
                                t == ("id", "where") or (t == ("id", "rec") and i > 0 and toks[i - 1] == ("id", "let"))
                                for i, t in enumerate(toks)):
                            raise Unscannable("auxiliary declaration (`where` or `let rec`)")
                    acc.update(hs)
                    acc.update(auto_names(b))
                except Unscannable as e:
                    sys.exit(f"[linkage] error: cannot be scanned: in {p}, {hs[0] if hs else '?'}: {e} "
                             "(plan Section 19)")
EXTRA = all_theirs - all_mine   # declared (or generated) only in the committed (patched) translation, any file
# Committed-only std trait-instance blocks (XD2), and the std trait instances of both sides that
# differ only by committed-only fields (filled below, read by step 5).
STD_INST_EXTRA = {}
for fname in FILES:
    if not os.path.exists(os.path.join(committed, fname)):
        continue   # reported below
    for n, i in std_instances(os.path.join(committed, fname)).items():
        if n in EXTRA:
            STD_INST_EXTRA[n] = i
widened = {}
bad = 0
for fname in FILES:
    mine_path, theirs_path = os.path.join(scratch, fname), os.path.join(committed, fname)
    for p in (mine_path, theirs_path):
        if not os.path.exists(p):
            sys.exit(f"[linkage] error: {p} missing (the templates: run scripts/aeneas-translate.sh first)")
    raw, mine = blocks(mine_path)
    for path in src.findall(raw) + macro_src.findall(raw):   # both cited paths (N13)
        if "Template" in fname and path.startswith("crates/rmcp/src/"):
            sys.exit(f"[linkage] error: {fname} of the unmodified source declares an SDK item as "
                     f"external ({path!r}): its body is hidden from this check; reassess the Phase 2 "
                     "records (plan Section 19)")
        if not path.startswith(ALLOWED_SRC):
            sys.exit(f"[linkage] error: {fname} of the unmodified source cites the source path {path!r}, "
                     f"outside {ALLOWED_SRC}")
    _, theirs = blocks(theirs_path)
    mine_headers = {b for b in mine if not heads(b)}
    for b in theirs:
        if not heads(b) and b not in mine_headers:
            sys.exit(f"[linkage] error: cannot be scanned: the committed {fname} has a header block "
                     f"the unmodified source does not have: {b.strip().splitlines()[0][:100]!r} "
                     "(an `open`/`namespace`/`set_option` changes name resolution; plan Section 19)")
    have, names = set(theirs), set()
    for b in theirs:
        names.update(heads(b))
    extra = EXTRA
    inst_mine, inst_theirs = std_instances(mine_path), std_instances(theirs_path)
    # Lean resolves an identifier inside `def a.b.c.f` against the namespaces a.b.c, a.b, a and
    # the root: a committed-only declaration named <prefix>.<identifier> could change what an
    # unmodified block means while its text stays the same (plan Section 19). Fail on any such
    # candidate (token-based, so conservative).
    for b in mine:
        hs = heads(b)
        if not hs:
            continue
        parts = hs[0].split(".")
        prefixes = [".".join(parts[:k]) for k in range(len(parts) - 1, 0, -1)] + [""]
        # Strings, char literals and comments are no lookups (lex drops them in one pass); a
        # parameter of the declaration's own signature resolves before any global once its binder
        # group has closed, so a later token whose first segment is one of them is no lookup (e.g. the parameter `base_classes` of
        # is_allowed vs the committed-only projection MetadataAddressResolver.base_classes;
        # review a1-2). `fun`, `let` and match binders are not exempted (their scope is not
        # tracked; this only makes the scan more conservative).
        try:
            toks = lex(b)
        except Unscannable as e:
            sys.exit(f"[linkage] error: cannot be scanned: in {fname}, {hs[0]}: {e} (plan Section 19)")
        bound, binders = signature_params(toks)
        assign = assign_binders(b)
        seen = set()
        for idx, (kind, tok) in enumerate(toks):
            if kind != "id" or idx in binders or idx in assign or tok in seen:
                continue
            if tok == hs[0]:
                continue   # the block's own declared name (and recursive calls) is no lookup
            first = tok.split(".")[0]
            if first in bound and idx > bound[first]:
                continue   # a parameter, after its binder group closed
            seen.add(tok)
            segs = tok.split(".")
            # an identifier a.b.c can resolve to a declaration named <pre>.a, <pre>.a.b or
            # <pre>.a.b.c (a shorter one followed by field access), for each enclosing namespace
            for k in range(1, len(segs) + 1):
                for pre in prefixes:
                    cand = ".".join(([pre] if pre else []) + segs[:k])
                    if (cand in extra and not pre and k == len(segs) - 1 and cand in STD_INST_EXTRA
                            and (segs[-1], f"  {segs[-1]} := {tok}") in STD_INST_EXTRA[cand][2]):
                        print(f"[linkage] `{tok}` in {hs[0]}: the field `{segs[-1]} := {tok}` of the "
                              f"committed-only std trait instance `{cand}` names the same function")
                        continue
                    if cand in extra:
                        sys.exit(f"[linkage] error: in {fname}, `{tok}` in {hs[0]} may resolve to the "
                                 f"committed-only declaration `{cand}` (name shadowing by patched "
                                 "code; plan Section 19)")
    same = wide = 0
    for b in mine:
        hs = heads(b)
        if len(hs) > 1:
            sys.exit(f"[linkage] error: a block of the unmodified-source {fname} holds {len(hs)} "
                     f"declarations ({', '.join(hs)}); the comparison needs one per block")
        if not hs and not is_header(b):
            sys.exit(f"[linkage] error: a block of the unmodified-source {fname} has no declaration "
                     f"and is not a header or footer: {b.splitlines()[0][:100]!r}")
        if b in have:
            same += 1
            continue
        if hs and hs[0] in inst_mine and hs[0] in inst_theirs:
            x = instance_extra(hs[0], inst_mine[hs[0]], inst_theirs[hs[0]])
            if x is not None:
                widened[f"rmcp.{hs[0]}"] = x
                print(f"[linkage] std trait instance {hs[0]} in committed {fname}: equal up to the "
                      f"fields {', '.join(x)} that only the committed block sets"
                      + (" (impl_def)" if inst_theirs[hs[0]][0] != inst_mine[hs[0]][0] else ""))
                wide += 1
                continue
        bad += 1
        n = hs[0] if hs else b.splitlines()[0][:100]
        print(f"[linkage] {'DIFFERS' if hs and n in names else 'MISSING'} in committed {fname}: {n}")
    print(f"[linkage] {fname}: {len(mine)} blocks from the unmodified source, {same} identical"
          + (f", {wide} std trait instance(s) equal up to committed-only fields" if wide else ""))
if bad:
    sys.exit(f"[linkage] error: {bad} block(s) of the unmodified-source translation differ or are "
             "missing; the Phase 2 linkage is not ORIGINAL (plan Section 19)")
import json
with open(widened_out, "w", encoding="utf-8") as f:
    json.dump(widened, f, sort_keys=True)
print("[linkage] text comparison OK")
PY

# 5. Elaborated comparison (human decisions 2026-11-26, after reviews a3-1, b3-1, a4-1, b4-1,
# a5-1, a5-2, a5-3, a6-1, a6-2). The text scan above reads only the layout Aeneas emits; this step
# decides. Build two Lean environments the same way, each with its own generated External
# templates as the externals (the one known template printing bug, a fn item as FnOnce, repaired
# identically on both sides by scripts/linkage/repair_template.py; a wrong rewrite stops the
# build): env0 from the unmodified-source translation, env1 from the committed one. Then
# (scripts/linkage/Dump.lean, compare_env.py):
#  - every non-auxiliary constant of Rmcp.Types/Rmcp.Funs of env0 exists in env1 with the same
#    module, kind, universe parameters, type and value (inductives, constructors and recursors by
#    their structure), in a canonical form without binder names, hygiene or metadata and with
#    auxiliary constants (`_proof_N`, `match_N`, theorems) replaced by their content; except
#    (human decision XD2, 2026-11-28) the std trait instances that step 4 found equal up to
#    committed-only fields ($SCR/instance-fields.json): their values must be the same structure
#    constructor with the same binders, levels and parameters, differing only at those fields,
#    and (review finding TR4; scripts/linkage/Widen.lean, env2 = the committed translation with
#    the hand-written externals of formal/trusted/Rmcp) each such field must either hold a
#    committed value that the kernel finds definitionally equal, in env2, to the default the
#    unmodified side gets (the env0 value, transported exactly), or be projected (projection
#    function, `Expr.proj` at its index, or the structure's recursor) by no definition reachable
#    from env0's four modules and none reachable from the hand-written externals; otherwise the
#    check fails. Stated limit: code outside both environments (formal/specs, formal/proofs,
#    downstream users) is not inspected; it sees the committed values;
#  - every external of env0 has the same universe parameters and type in env1;
#  - what Rmcp.Types and Rmcp.Funs export besides constants differs only as new declarations make
#    it differ: env0's instance entries unchanged (name, priority, scoped or global, class,
#    argument), new ones only the default-priority global SizeOf and @[discriminant] instances
#    generated in Rmcp.Types for a committed-only type (by class and argument); reducibility of
#    env0's non-auxiliary constants unchanged, new entries only for new constants of the same
#    module; and the entry count of every other environment extension unchanged, except the
#    extensions measured to grow with new declarations (compiler data, ranges, docstrings,
#    structure data, simp/grind/inline/implemented_by/elab_as_elim sets, Aeneas tables). Notation,
#    macros, syntax, `export`, unification hints and any unknown extension may not grow; the
#    growth list is per module (review a7-3);
#  - every constant only env1's translation modules declare, auxiliary ones included, is under
#    `rmcp.` or is a generated root `instDiscriminant…` instance (review a7-2).
# Gates step 5 relies on (review a7-1): scripts/lean-guard.sh sources, run first below (step 5
# runs Lean on committed code, so code acting at build time, such as `initialize` or `run_cmd`,
# could forge what it reads), and the CI stale-translation check. Under them a committed-only
# change can alter an unmodified block only by changing what it elaborates to, and downstream code
# only through what the modules export or the names they add; all are compared. Not covered: the
# hand-written formal/trusted/Rmcp/*.lean (the trusted base; both environments use the
# templates), and entries of the growing extensions above that committed code attaches to existing
# constants (`attribute [simp]`, `[inline]`, `[implemented_by]`, `[elab_as_elim]` …), which change
# proof automation, compilation or downstream elaboration hints, not what any constant is.
# Reads the Lean packages already built in formal/.lake/packages (see above); builds only the four
# translation modules, in <scratch-dir>/env0 and env1 (and env2, see below).
# Step 5 runs Lean on the committed translation and reads it through Lean, so its result means
# something only for code that cannot act at build time: first the source rules of
# scripts/lean-guard.sh (no initialize, run_cmd, #eval, macro_rules, IO, implemented_by or
# attributes outside ATTR_ALLOWED in generated modules beyond the pinned lines; review a7-1). The
# CI stale-translation check (the committed translation is exactly Aeneas output) is the other gate.
"$ROOT/scripts/lean-guard.sh" sources >/dev/null \
  || die "scripts/lean-guard.sh sources fails: step 5 needs the committed translation to pass it"
LIN="$ROOT/scripts/linkage"
for e in 0 1 2; do rm -rf "$SCR/env$e"; done
rm -f "$SCR/widen-export.json" "$SCR/widen-committed.json"
python3 -I "$LIN/make_env.py" "$ROOT" "$SCR/env0" "$SCR/out/Rmcp/Types.lean" "$SCR/out/Rmcp/Funs.lean" \
  "$SCR/out/Rmcp/TypesExternal_Template.lean" "$SCR/out/Rmcp/FunsExternal_Template.lean"
python3 -I "$LIN/make_env.py" "$ROOT" "$SCR/env1" "$ROOT/formal/translation/Rmcp/Types.lean" \
  "$ROOT/formal/translation/Rmcp/Funs.lean" "$ROOT/formal/translation/Rmcp/TypesExternal_Template.lean" \
  "$ROOT/formal/translation/Rmcp/FunsExternal_Template.lean"
for e in 0 1; do
  python3 -I "$LIN/repair_template.py" "$SCR/env$e/src/Rmcp/FunsExternal.lean"
  (cd "$SCR/env$e" && lake build Rmcp) > "$SCR/env$e/build.log" 2>&1 \
    || { tail -20 "$SCR/env$e/build.log" >&2; die "env$e: the translation does not build (log $SCR/env$e/build.log)"; }
  (cd "$SCR/env$e" && lake env lean --run "$LIN/Dump.lean" "$SCR/env$e/dump.jsonl") \
    || die "env$e: could not read the elaborated constants"
done
# The committed-only fields of the std trait instances (review finding TR4): env2 is the committed
# translation with the hand-written externals of formal/trusted/Rmcp (as `lake build Rmcp
# RmcpExternal` builds it); scripts/linkage/Widen.lean exports each field's env0 value and the env0
# definitions projecting it, then checks in env2 whether the committed value is definitionally
# equal to it and which definitions of the external models project it. Built only when step 4
# listed a field.
widen=()
if python3 -I -c 'import json, sys; sys.exit(0 if any(json.load(open(sys.argv[1])).values()) else 1)' \
    "$SCR/instance-fields.json"; then
  python3 -I "$LIN/make_env.py" "$ROOT" "$SCR/env2" "$ROOT/formal/translation/Rmcp/Types.lean" \
    "$ROOT/formal/translation/Rmcp/Funs.lean" "$ROOT/formal/trusted/Rmcp/TypesExternal.lean" \
    "$ROOT/formal/trusted/Rmcp/FunsExternal.lean"
  (cd "$SCR/env2" && lake build Rmcp) > "$SCR/env2/build.log" 2>&1 \
    || { tail -20 "$SCR/env2/build.log" >&2; die "env2: the committed translation with the hand-written externals does not build (log $SCR/env2/build.log)"; }
  (cd "$SCR/env0" && lake env lean --run "$LIN/Widen.lean" export "$SCR/instance-fields.json" "$SCR/widen-export.json") \
    || die "env0: could not export the committed-only fields"
  (cd "$SCR/env2" && lake env lean --run "$LIN/Widen.lean" committed "$SCR/widen-export.json" "$SCR/widen-committed.json") \
    || die "env2: could not check the committed-only fields"
  widen=("$SCR/widen-export.json" "$SCR/widen-committed.json")
fi
python3 -I "$LIN/compare_env.py" "$SCR/env0/dump.jsonl" "$SCR/env1/dump.jsonl" "$SCR/instance-fields.json" \
  ${widen[@]+"${widen[@]}"}
log "OK: the Phase 2 translation does not depend on any translation patch"
