# Contributing to the formal verification

This guide covers the formal verification work in this fork of the Rust MCP SDK (`rmcp`): the Lean
4 project in `formal/`, the scripts under `scripts/`, the Charon settings in
`crates/rmcp/Cargo.toml`, and the CI workflows. The Rust code is translated to Lean by
[Charon](https://github.com/AeneasVerif/charon) and [Aeneas](https://github.com/AeneasVerif/aeneas);
we state specifications for the public API and prove them against the translation. The crate is
translated for **a single target** (for the multi-target version, where several configurations are
translated and merged, see `curve25519-dalek-fork`).

Ordinary SDK changes follow the [contribution guide](../docs/CONTRIBUTE.MD). Results are recorded
in the guarantee index [`specs/README.md`](specs/README.md) and in the "Results" section of
[`README.md`](README.md). The older extraction under `verification/host_origin/` keeps its own
README and its recorded hand edit; it is not part of `formal/`, and the rules below do not apply to
it retroactively.

Citations of the form "plan Section N", and documents cited by path that are no longer in the tree,
refer to git history at commit 9047c72.

## Contents

1. [Process](#process)
2. [Layout](#layout)
3. [Toolchain and translation](#toolchain-and-translation)
4. [Specifications](#specifications)
5. [Proofs](#proofs)
6. [Building and checking](#building-and-checking)
7. [PR workflow and format](#pr-workflow-and-format)
8. [Review and sign-off](#review-and-sign-off)
9. [AI contributions](#ai-contributions)
10. [Review checklist (AI and human reviewers)](#review-checklist-ai-and-human-reviewers)

## Process

**Scope first.** Before translating anything, decide which part of the crate is worth verifying and
which part Aeneas can handle. Aeneas works well on pure, sequential, safe Rust: data structures,
parsing, encoding, arithmetic. It does not handle I/O, threads and synchronisation, interior
mutability or `unsafe` code well. Code that is mostly about those is usually excluded rather than
patched, and the verification concentrates on the logic underneath it. Write the scope decision
down, since it determines what the final result does and does not cover. Excluding a target from
the project needs the user's decision (plan Section 2.3).

Work then runs in three phases (plan Section 8):

1. **Phase A, once for the whole crate:** scope, translate, review the trusted part of the
   translation (exclusions, opaque items, patches, external models), turn on CI.
2. **Phase B, per function, pipelined in call-graph batches:** spec draft, at least two independent
   agent reviews, human sign-off, proof, restated `theorem` in the spec file. The rule is
   **complete first**: get every spec proved with no `sorry`, by whatever works.
3. **Phase C, once after every proof is checked:** **improve later**. Go back over the proofs to
   make them shorter, more robust to translation changes and Aeneas upgrades, and better factored
   into reusable lemmas. Spec statements are frozen during this phase.

A proof starts only after its own spec is signed off, and after the external models it uses are
signed off.

The commands are in [Translating](#translating) and [Building and checking](#building-and-checking).

## Layout

Everything about the verification lives under `formal/`, organised by what an auditor does with
each part. Only the Charon settings, the scripts and the CI workflows live outside it.

```
crates/rmcp/Cargo.toml     [package.metadata.charon]: start_from, exclude, opaque
scripts/                   aeneas-install.sh   downloads the pinned charon + aeneas into .aeneas/
                           apply-patches.sh    copies the crate into .llbc/work/, applies patches
                           aeneas-translate.sh calls apply-patches.sh, then translates the copy
                           llbc-dir-guard.sh   work-directory guard
                           lean-guard.sh, lean_guard.py, lean-axiom-audit.lean   CI guard
                           check-original-linkage.sh, linkage/   ORIGINAL linkage check
.github/workflows/         aeneas-translation.yml, lean-build.yml, patched-tests.yml
formal/
  README.md                where each part lives, what must be trusted, Results
  CONTRIBUTING.md          this guide
  lakefile.toml            the Lean project (Lake root); pins Aeneas (single source of truth)
  lean-toolchain           copied from the pinned Aeneas release by the install script
  lake-manifest.json       Lean dependencies pinned by commit
  trusted/                 READ ALL OF IT: everything taken on trust
    patches/*.patch        local Rust edits that work around translation problems
    Rmcp/                  hand-written TypesExternal.lean, FunsExternal.lean (external models)
    evidence/              README.md: the tests backing the models
    aeneas-bundle.sha256   digests of the Aeneas release assets
    axioms.lock            trusted axioms (empty)
    native-axioms.lock     accepted native-code axioms (Aeneas toStr side conditions; empty)
    translation-pins.txt   pinned lines excused from the metaprogramming rule in generated files
    issues/                Aeneas/Charon problems met while translating: reproducers and draft
                           upstream issues (not trust items; they explain the patches)
  specs/                   READ ALL OF IT: what is claimed (top-level public API only)
    README.md              plain-English index of every guarantee; start here
    Defs/ Defs.lean        definitions needed to state the public specs
    Specs/ Specs.lean      one spec file per Rust file: top-level public statements + axioms
    Drafts/                draft statements; in no library, never built
  translation/             generated by Aeneas, never edited
    Rmcp/                  Types.lean, Funs.lean (Aeneas generates no Rmcp.lean)
    translation.json
  proofs/                  checked by Lean
    Proofs/ Proofs.lean    the proofs
    Proofs/External/       laws of the external models
    Proofs/Internal/       internal spec files (intermediate public functions, private API,
                           model laws)                                     READ for internals
    Proofs/Defs/           definitions used only by internal statements    READ for internals
    Proofs/Consistency/    consistency models (only if a trusted axiom is added again)
```

An auditor reads all of `formal/trusted/` and `formal/specs/` (start at `specs/README.md`), plus
`proofs/Proofs/Internal/` and `proofs/Proofs/Defs/` for the guarantees about intermediate public and
private functions, and none of `formal/translation/` (regenerated and checked by CI) or the rest of
`formal/proofs/` (checked by Lean). `formal/specs/` holds only the top-level public rmcp API
(functions `pub` in upstream rmcp that no other verified function calls; human decision 2026-11-28);
intermediate public functions (called by a top-level one), private, crate-internal (`pub(crate)`)
and patch-only functions and the model laws are specified in `proofs/Proofs/Internal/` (human
decision).

Lean commands (`lake build`, `lake exe cache get`) run in `formal/`. `.aeneas/` and `.llbc/` stay at
the repository root.

### What is committed

- **Committed:** the generated translation (`Funs.lean`, `Types.lean`, `translation.json`), the
  hand-written `FunsExternal.lean` and `TypesExternal.lean`, `lake-manifest.json`, and
  `lean-toolchain`. The stale-translation check in CI needs the generated files to be in git.
- **Git-ignored:** `.aeneas/`, `.llbc/` and `formal/.lake/` (build outputs), `Cargo.lock`, and
  `formal/translation/Rmcp/*External_Template.lean` (regenerated on every run; Aeneas writes them
  next to `Funs.lean`, never over the hand-written files in `formal/trusted/`).
- **Never edited by hand:** the generated files; see
  [Generated files are never edited](#generated-files-are-never-edited).

### Library layering

`formal/lakefile.toml` declares five libraries (plan Section 5). Each has its own `srcDir` and
explicit `roots` (no `globs`: `scripts/lean-guard.sh` allows only `name`, `srcDir`, `roots` and
`leanOptions`), so every module belongs to exactly one library and module names do not mention the
folders (`Rmcp.Funs`, `Defs.*`, `Specs.*`, `Proofs.*`). The import directions are fixed:

| Library | `srcDir` | Contents | May import |
| --- | --- | --- | --- |
| `Rmcp` | `translation` | Generated `Rmcp.Types`, `Rmcp.Funs` | Aeneas, `RmcpExternal` |
| `RmcpExternal` | `trusted` | Hand-written `Rmcp.TypesExternal`, `Rmcp.FunsExternal`: external models (definitions, structures, `opaque` constants; no axiom) | Aeneas, `Rmcp.Types` (the generated `FunsExternal` template imports it) |
| `Defs` | `specs` | Pure definitions used by public statements (`Defs.Bytes`, `Defs.IntParse`, `Defs.JsonRpc`, `Defs.Wire`, `Defs.CodecState`, `Defs.RequestState`, ...) | Aeneas, Mathlib, `Rmcp`, `RmcpExternal` |
| `Proofs` | `proofs` | Spec theorems about the translated functions and their support lemmas; laws of the external models (`Proofs/External/`); internal spec files (`Proofs/Internal/`) and their definitions (`Proofs/Defs/`, module `Proofs.Defs.X`, Lean namespace `Defs.X`); consistency models only if a trusted axiom is added again | `Rmcp`, `RmcpExternal`, `Defs` |
| `Specs` | `specs` | One spec file per Rust source file with top-level public API: each accepted statement about a top-level public function (or a composition of them) restated as a `theorem` in `Theorems`, and its axioms | `Defs`, `Rmcp.Funs` (publicly); `Proofs` (privately: `import`, not `public import`) |

- `Proofs` never imports `Specs`, and nothing imports `Specs`.
- A spec file imports `Defs` and `Rmcp.Funs` with `public import` (its statements are phrased
  with them) and the `Proofs` modules that prove them with a plain `import`, so that a Lean
  `module` importing `Specs` sees the restated theorems but no proof module (a non-`module` file
  still sees the privately imported `Proofs.Model.*`). Keep the `Proofs` imports private.
- A statement is phrased only with `Defs` definitions (and the translated function), so that its
  meaning never depends on a proof-private definition. Signed-off definitions used only by internal
  statements live in `proofs/Proofs/Defs/` (modules `Proofs.Defs.*`, Lean names `Defs.*`); they
  count as `Defs` for this rule, and a change to them is a specification change.
- Proof-only helpers stay in `Proofs`. Promote a helper to `Defs` only if a statement needs it.
- `formal/specs/Drafts/` belongs to no library. Draft statements live there until their proofs are
  complete.

Which libraries are default targets, and how `Rmcp`/`RmcpExternal` get built and audited, is in
[README "Layout"](README.md#layout); making them default targets is a `lakefile.toml` change by the
lead.

### Library roots

`specs/Defs.lean`, `specs/Specs.lean` and `proofs/Proofs.lean` are maintained by hand and list only
accepted modules:

- add a module to `Defs.lean` when its definitions are signed off;
- add a proof module to `Proofs.lean` when its proof is complete;
- add a statement to a spec file under `Specs/` (top-level public API) or `proofs/Proofs/Internal/`
  (intermediate public functions, private API and model laws) (as a `theorem Theorems.…` proved by
  the spec theorem, with its `#guard_msgs` axiom check) only when its proof is complete and its spec
  is `REVIEWED`, and add its row to the matching table of `specs/README.md`;
- definitions used only by internal statements go to `proofs/Proofs/Defs/` (imported from
  `Proofs.lean`), the others to `specs/Defs/`. Exception (human decision 2026-11-28):
  `TranscriptV1Fits` and `TranscriptV2Fits` stay in `specs/Defs/CodecState.lean`, signed off there,
  although since the intermediate public functions R08 and R14 moved to
  `proofs/Proofs/Internal/Model/RequestState.lean` only internal statements use them; moving them
  would be a `Defs` change that reopens their review.

Statements awaiting proofs stay in `specs/Drafts/`. A proof with `sorry` is never merged: every
library sets `warningAsError`, and CI fails on any warning in this project's files.

## Toolchain and translation

### Pinned toolchain

The only pin is the Aeneas release tag in `formal/lakefile.toml`:

```toml
[[require]]
name = "aeneas"
git = "https://github.com/AeneasVerif/aeneas.git"
subDir = "backends/lean"
rev = "nightly-YYYY.MM.DD-<hash>"   # must be a GitHub release tag
```

This one `rev` (at the time of writing `nightly-2026.11.24-fb44cb4`) is the single source of truth
for the Aeneas version. Both scripts read it, so the binaries that translate the code always match
the Lean library the proofs build against. `scripts/aeneas-install.sh` installs the matching
Charon, Aeneas, Rust nightly and Lean toolchain; do not install them any other way.

Changing the `rev` is its own PR. That PR changes the `rev`, re-runs both scripts, re-translates all
targets, rebuilds all proofs, fixes whatever breaks, adds the new tag's entries to
`trusted/aeneas-bundle.sha256`, updates the manifest package list (below), and records the result
in its PR body and in the "Results" section of [`README.md`](README.md).

- **Release digests.** `formal/trusted/aeneas-bundle.sha256` holds the sha256 of every Aeneas
  release asset used (release bundles and `lean-build-aeneas` archives, keyed by `<tag>/<asset>`);
  the install script and `lean-guard.sh aeneas-archive` fail on a mismatch or a missing entry
  ([README "Tools"](README.md#tools)).
- **Lean dependencies, Lean toolchain and Rust toolchain** are pinned and checked as described in
  [README "Toolchain"](README.md#toolchain) and
  [README "Translated configuration"](README.md#translated-configuration) (`MANIFEST_PACKAGES` and
  `LEAN_TOOLCHAIN` in `scripts/lean_guard.py`; the pinned `rustc -vV` lines). A `rev` bump PR
  updates those lists. A fake `rustc` that prints exactly the pinned lines is not caught.
- **Dependency versions the external models rely on** are pinned in `PINNED_DEPS` of
  `scripts/aeneas-translate.sh`; the list, the crates.io-only rule and the rule for which version
  counts (the one `rmcp` itself uses, human decision) are in
  [README "Toolchain"](README.md#toolchain). Pin any new dependency a model relies on there.
- **Build script.** The translate script pins `crates/rmcp/build.rs` by sha256 (`BUILD_RS_SHA256`).
  A PR that changes `build.rs` must update that digest in the same PR, after checking that the
  build script still emits nothing (no `cargo:` directive).

### Install

`scripts/aeneas-install.sh`:

1. Reads the Aeneas `rev` from `formal/lakefile.toml`.
2. If `.aeneas/aeneas -version` doesn't already report that tag, downloads the matching release
   bundle (charon, charon-driver, aeneas, the Lean backend) for the current platform from GitHub
   into `.aeneas/`, and verifies it against `trusted/aeneas-bundle.sha256`.
3. Installs the Rust nightly toolchain that `charon-driver` was built against, from the bundle's
   `rust-toolchain` file.
4. Copies the bundle's `backends/lean/lean-toolchain` to `formal/lean-toolchain`, so Lean matches
   too, and seeds `formal/.lake/packages/aeneas` with the bundle's prebuilt Aeneas Lean library.

Running it again does nothing if the right version is already installed.

### Charon settings

What gets translated is set in `crates/rmcp/Cargo.toml`, not in the script:

```toml
[package.metadata.charon]
start_from = ["my_crate"]
# Items we will never verify: not translated at all.
exclude = [
  "my_crate::some_module::{impl core::fmt::Debug for _}",
]
# Items verification relies on but which we deliberately do not translate.
opaque = []
```

- **`exclude`** is for things we have no interest in verifying, such as `Debug` and `Hash` impls,
  marker-trait impls, and other code outside the scope of the specs. Excluded items are not
  translated, and nothing we verify may depend on them.
- **`opaque`** is almost never used. An item is made opaque only when it **cannot be translated and
  there is no useful Rust model** we could patch in. Its Lean signature is then generated without a
  body, and we state its behaviour in `formal/trusted/Rmcp/FunsExternal.lean`, as a definition (an
  exact model, or `ok` of an `opaque` value). Every opaque item adds to the trusted base, so it
  needs a strong justification and the same review as an external model. The default answer to a
  translation problem is a patch, not `opaque`.

Each entry has a comment saying why it is there. Entries are Charon name patterns, such as
`my_crate::module::Type::method` or `my_crate::module::{impl core::fmt::Debug for _}` (every `Debug`
impl in a module). For the full pattern syntax and the other options, see the
[Charon documentation](https://github.com/AeneasVerif/charon) and `charon cargo --help` for the
pinned version.

### Translating

From the repository root:

```bash
scripts/aeneas-install.sh      # once, and after bumping the Aeneas rev
scripts/aeneas-translate.sh    # after any change to src/, patches, or Charon settings
```

`scripts/aeneas-translate.sh`:

1. Checks that `.aeneas/` matches the `rev` in `formal/lakefile.toml` (otherwise asks you to run the
   install script).
2. Runs `scripts/apply-patches.sh`, which `rsync`s the crate into `.llbc/work/` (leaving out
   `target/`, `formal/`, `.aeneas/`, `.llbc/`, `.git`, `.claude/`) and applies every
   `formal/trusted/patches/*.patch` **one after the other**, in the order of its number prefix,
   without fuzz (`patch -p1 -F 0`), stopping if any patch fails. It is a separate script so CI can
   build the same copy to run the crate's tests without charon or aeneas.
3. Runs `charon cargo --preset=aeneas` on the patched copy for the single target and features we
   verify, writing `.llbc/<crate>.llbc`. Charon reads its settings from `Cargo.toml`.
4. Runs `aeneas -backend lean -split-files -emit-json` on the LLBC, writing the generated Lean
   (`Rmcp/Types.lean`, `Rmcp/Funs.lean`) and `translation.json` (needed if another crate later
   reuses this translation with `-extern-crate`).

**Configuration.** The target triple, the cargo features and the `--config` options (overflow
checks and debug assertions on) are fixed in the script; **the proofs hold only for that
configuration**. They are listed in
[README "Translated configuration"](README.md#translated-configuration) and stated in the module
docstring of every spec file. So that nothing else changes the build, the script refuses build-
changing environment variables, an unpinned `rustc`, `.cargo/config` files and `[profile]`/
`[patch]`/`[replace]`/`cargo-features` in the manifests, and it fails on any deviation in the
output (non-crates.io dependency, unpinned `build.rs`, Charon or Aeneas errors, an item that
breaks the `exclude`/`opaque`/`start_from` lists, a `_` glob of `start_from` not matching exactly
one item except the `MULTI` entries, a missing target, `sorry`, a version mismatch). The exact
lists are in [README "Translated configuration"](README.md#translated-configuration) and the header
of `scripts/aeneas-translate.sh`. Do not work around a refusal; fix its cause.

**Scratch runs.** Aeneas writes into `$RMCP_LLBC_DIR/out` and the script copies the output to
`formal/translation/` (or `$RMCP_TRANSLATION_DEST`) only after the checks pass. For a scratch run,
set `RMCP_SOURCE_ROOT`, `RMCP_LLBC_DIR` and `RMCP_TRANSLATION_DEST` together and use a new or empty
work directory; the directory rules of `scripts/llbc-dir-guard.sh` are in
[README "Commands"](README.md#commands).

**Translate carefully.** The goal is to translate everything possible. Work through the Charon and
Aeneas output item by item, and don't accept silent losses: after every run, check that every
target (every public item we care about) appears in `Funs.lean` with a real body. Rerun the
translation after each change and commit the regenerated output together with the patches and
settings that produced it. To learn how Aeneas translates Rust into Lean, see the
[Aeneas documentation](https://github.com/AeneasVerif/aeneas/tree/main/documentation).

### Generated files are never edited

**Never edit** anything under `formal/translation/` by hand (`Rmcp/Types.lean`, `Rmcp/Funs.lean`,
`translation.json`). There are no exceptions: the translation CI regenerates them and fails on any
difference. To change them, change one of:

- the Rust source (its own PR; see below),
- a translation patch in `formal/trusted/patches/`,
- the Charon settings in `crates/rmcp/Cargo.toml`,

and re-run `scripts/aeneas-translate.sh`. Commit the regenerated output together with the change
that produced it. A source change changes the translation; the translation CI forces the
regenerated files into the same PR, and the Lean build re-checks every proof against them.

Aeneas regenerates `Funs.lean` and `Types.lean` on every run. It also emits
`*External_Template.lean` files (next to `Funs.lean`, git-ignored) listing the signatures of
anything it needs from outside (std functions it doesn't model, opaque items).
`formal/trusted/Rmcp/TypesExternal.lean` and `FunsExternal.lean` are started once from these
templates and then maintained by hand; Aeneas never writes there. The templates contain
`set_option linter.dupNamespace false`, `linter.hashCommand false` and
`linter.unusedVariables false`, which `scripts/lean-guard.sh sources` rejects in `trusted/`; remove
these lines when starting the externals from the templates. For how the template files,
`-split-files` and the `rust_fun`/`rust_type` attributes work, see the Aeneas docs:
[Adding models of Rust definitions to the Lean backend](https://github.com/AeneasVerif/aeneas#adding-models-of-rust-definitions-to-the-lean-backend).

### Rust source changes

Never modify an SDK `*.rs` file in a verification PR; Rust changes needed for verification go into
translation patches. In particular:

- **Never change** production code in `crates/rmcp/src/model/request_state.rs` or
  `crates/rmcp/src/model/request_state_wire.rs` as part of a verification PR. The only exceptions
  are the reviewed `request_state_wire` refactor of plan Section 9 as its own PR (plan step S04a;
  it is carried instead by translation patch 01), and new Rust tests inside either file's private
  `mod tests` (plan step S16).
- **Phase 2** (plan Part II) changes **no** SDK `*.rs` file at all, tests included: its targets are
  verified on the unmodified upstream source (plan Sections 13 and 19). Boundary tests come from the
  existing upstream tests; a case they do not cover may get tests only through the test-only
  translation patch `02-phase2-tests.patch` (`#[cfg(test)]` code only; human decision H3).
- For new public wire functions, prefer following the Aeneas-safe coding rules of plan Section 2.1
  in the source itself (free functions, byte slices, no nested borrows, no HMAC or `Engine` types in
  signatures, error enums instead of string literals, no Lean keyword identifiers, documentation,
  `#[non_exhaustive]` on enums and structs).

### When translation fails

Do not work around a translation problem in generated Lean. For each error or skipped item:

1. **Out of scope:** add it to `exclude` in `[package.metadata.charon]`, with a comment giving the
   reason. Nothing verified may depend on an excluded item.
2. **In scope:** write a translation patch (below), or fix the problem upstream in Charon or Aeneas.
3. **Last resort:** `opaque`, only when the item cannot be translated and there is no useful Rust
   model to patch in. Its behaviour then becomes an external model in `FunsExternal.lean`, so it
   needs a strong justification and the same review as an external model.

If no change within the project's scope resolves the blocker, record it with a minimal reproducer
as an open item in the "Results" section of [`README.md`](README.md) (or an issue). Excluding a
target from the project needs the user's decision (plan Section 2.3); re-adding an excluded
function needs a recorded requirement change and a translation run showing the blocker resolved.

### Translation patches

Aeneas can't translate every Rust construct (for example, iterator adaptors like `fold` when only
`Iterator::next` is modelled). Rather than give up on the item, we make a small,
behaviour-preserving edit to the Rust source so that it translates. Each workaround is one patch
file in `formal/trusted/patches/`, kept **local to this repo** (never fetched from elsewhere). The
patches are applied only to the copy of the crate in `.llbc/work/` at translation time; the real
source is never patched, so merging new upstream code stays easy. The current patches and the
targets that depend on them are listed in [`specs/README.md`](specs/README.md) ("What you must
trust") and `README.md` ("Trusted base").

Each patch starts with a header:

```
Translation patch: <EdwardsPoint as Sum<T>>::sum

Change: `iter.fold(..)` becomes a `for item in iter` loop.
Why: Aeneas only models `Iterator::next` (aeneas#1057).
Behaviour: identical for iterators whose `fold` agrees with `next` (all std/lawful iterators).

diff --git a/src/... b/src/...
...
```

A patch changes the code that is verified, so it is part of the trusted base:

- Keep each patch minimal, with one concern per file.
- The header states the change, why it is needed (link the upstream Aeneas/Charon issue if there is
  one), and why the behaviour is unchanged.
- Each patch is reviewed like an external model: by at least two independent agents for behaviour
  preservation, then by a human (see [Review and sign-off](#review-and-sign-off)).
- CI runs the crate's own test suite on the patched copy (`patched-tests.yml`), so a patch that
  changes behaviour the tests cover is caught automatically.
- Every target whose translation depends on a patch has linkage `patch-NN` (for patch 01,
  `patch-01`). Exception (human decision H3): the test-only patch `02-phase2-tests.patch` holds only
  `#[cfg(test)]` code, is not needed for any item to translate, cannot change the translation, and
  affects no target's linkage.
- Phase 2 targets need no patch; their `ORIGINAL` linkage holds only while
  `scripts/check-original-linkage.sh` passes (plan Section 19).
- When an Aeneas upgrade fixes the underlying limitation, delete the patch.

To write a patch:

1. Run `scripts/apply-patches.sh` (or the translate script), so that `.llbc/work/` holds the patched
   copy of the crate.
2. Make the edit in `.llbc/work/`.
3. Save it with `git diff` into `formal/trusted/patches/NN-short-name.patch`, numbered so the order
   they apply in is clear, and add the header.
4. Re-run the translate script and check that the item now translates.

After an upstream merge a patch may stop applying. Then the script stops, and the patch has to be
regenerated against the new code and reviewed again.

### Calls into other crates

Aeneas only translates the crate itself. Anything it calls from outside (the opaque
`request_state_wire::prim` functions, `now_ms`, standard-library operations without an Aeneas
model, functions from other crates, opaque items) has no Lean body and needs an external model
([External models](#external-models)). Calls into other crates can be handled in two ways:

- Leave them as externals with models. This is cheap, but every function adds to what must be
  trusted.
- Translate the dependency too, and reuse its translation with `-extern-crate NAME=PATH` (see the
  Aeneas README section
  [Translating crates which depend on each other](https://github.com/AeneasVerif/aeneas#translating-crates-which-depend-on-each-other)).
  This is more work, but the calls are then verified rather than assumed.

Decide this per dependency, based on how much of the crate's behaviour flows through it. Where a
model is generally useful (most std functions), prefer adding it to the Aeneas standard library
upstream, so it stops being an external model here.

## Specifications

### What a statement means

Aeneas translates each function into the `Result` monad, where panics, arithmetic overflow and
out-of-bounds indexing become failure. A spec of the form `f x ⦃ r => P r ⦄` therefore says that
`f x` **terminates without panicking** and that its result satisfies `P` (plan Section 3).
Preconditions (hypotheses on the inputs) say when the function is guaranteed not to panic. A weaker
precondition gives a stronger result.

### Deciding the public API specs

Once the translation is complete, we decide which public API items we care about and what each one
should guarantee. The spec statements are the part that has to be trusted, so they are reviewed
before any proof work starts:

1. Draft the statements (and the definitions they need in `specs/Defs/`), in `specs/Drafts/`.
2. **At least two agents review them independently.** Is each one faithful to the Rust source and
   documentation and the intended behaviour? Is it strong enough to be useful? Does it accidentally
   assume what it should prove?
3. **A human then checks** and signs off on the statements.

A specification is signed off before it is proved. Any change to a signed-off statement re-opens
its review. A proof worker that finds a signed-off specification false returns a counterexample; it
does not weaken the statement, and the spec returns to `DRAFT`.

What a good statement looks like:

- It describes the pinned Rust behaviour, including the `Ok` case and every `Err` variant, in the
  Rust order of checks, with exact boundaries.
- It gives the later steps what they need (transcripts, exact output format, error results), but
  need not go further. Functions that may be called from outside the known call sites have
  specifications that make no assumptions about their callers.
- It does not simply restate the implementation (except for very trivial functions): a
  specification that mirrors the translated code proves nothing beyond translation. Use
  mathematical abstractions rather than implementation primitives. For example, state a MAC
  transcript as a byte-list concatenation (`DOMAIN_V1 ++ be64 (len ad) ++ ad ++ body`) rather than
  as a sequence of `update` calls, and state expiry decoding as a signed big-endian integer rather
  than as `from_be_bytes` on a slice.
- Weaker specifications are often easier to prove, for people and the machine, and the difference
  can affect build time. If a proof is particularly expensive, check whether a weaker statement
  would still serve its callers.

### Definitions (`Defs`)

`formal/specs/Defs/` holds the definitions that public statements are written in (`Bytes`,
`IntParse`, `JsonRpc`, `Wire`, `CodecState`, `RequestState`, ...); those used only by internal
statements are in `proofs/Proofs/Defs/` (human decision). Exception (human decision 2026-11-28):
`TranscriptV1Fits` and `TranscriptV2Fits` stay in `specs/Defs/CodecState.lean`, signed off there,
although since the intermediate public functions R08 and R14 moved to
`proofs/Proofs/Internal/Model/RequestState.lean` only internal statements use them; moving them
would be a `Defs` change that reopens their review. For example:

- `Defs/Wire.lean`: `splitOn` components, `be64`, transcripts, framing and expiry.
- `Defs/RequestState.lean`: codec outputs and error predicates.
- `Defs/CodecState.lean`: the codec-state predicate `CodecValid` enforced by the keyring
  constructors (single-key codecs unconstrained; key ids pairwise distinct), its clauses, key
  lookup, and the expected results of the opening functions E09–E11.

Rules:

- Each definition has a docstring that says what it denotes, and the Rust lines (at the pinned
  commit) or plan section it models.
- Prefer mathematical objects (`List UInt8`/`List U8`, `Nat`, `Int`) over machine types, except
  where the machine width is part of the claim. State conversions explicitly, e.g. signed
  big-endian decoding of 8 bytes.
- Do not restate the implementation step by step.
- `Defs` contains no axioms. Anything taken on trust belongs in `formal/trusted/`.

### External models

`formal/trusted/Rmcp/FunsExternal.lean` and `TypesExternal.lean` declare everything Aeneas does not
translate (plan Section 4). Organise `FunsExternal.lean` in sections: HMAC, Base64, standard
library, clock, and the Phase 2 sections (strings and `Arc`; `Option`, `Result`, slices and ranges;
integer parsing; IP addresses), plus later sections for later targets.

- **No `axiom` in `trusted/`** (human decision). Each external function is a `def` with the
  generated name and signature, and each external type a `structure` (or an `inductive` where Rust
  has a union or enum, e.g. `MaybeUninit`, `IntErrorKind`), keeping the template's `@[rust_fun]` or
  `@[rust_type]` attribute where it has one (the template gives none to the opaque `rmcp`
  functions, `prim` and `now_ms`). What a model cannot compute is an `opaque` constant in the
  namespace `ExtModel` (for example `hmacSha256`, `sipHash13`, `nowMs`, `randomState`,
  `serdeJsonFromSlice`), which adds no axiom; a function external returns `ok` of it, and an
  external type may be defined as one (`SerdeJsonValue`). `trusted/axioms.lock` stays empty. Adding
  an axiom again is a human decision.
- **Never a bare `Result` axiom.** Do not write `axiom f : … → Result T`; it asserts nothing
  returns, so proofs through it get stuck. Give an exact model as a definition, or `ok` of an
  opaque value: `def hmac_sha256 k m := ok (hmacSha256 k m)` with `opaque hmacSha256`.
- **No models on merged types.** Do not model or axiomatise a function whose Lean type merges
  distinct Rust types (for example `size_of`, where `T` and `&T` share a Lean type); state the fact
  as a hypothesis on the spec instead. Exception (lead decision, patch 07): a model whose value does
  not depend on which of the merged Rust types is meant is allowed, e.g. the identity model of
  `Option::copied` (`Option<&T>` and `Option<T>` share a Lean type).
- **Own terms.** Each model describes its primitive on its own terms, never by referring to a target
  function, and never assumes that a target function is correct.
- **As few and as weak as possible.** State only what the proofs need.
- **Laws are theorems.** Laws about the models (such as the Base64 round trip
  `b64Decode (b64 x) = some x`) are theorems in `proofs/Proofs/External/`, not assumptions.
- **Justify and record.** Each model's docstring cites the Rust source it encodes (pinned crate or
  `rust-src` file and lines) and states its exceptions (panics or behaviour it does not model). The
  model is listed in the trust items of [`specs/README.md`](specs/README.md) ("What you must
  trust"), and `formal/trusted/evidence/README.md` names the Rust tests that check it (concrete
  vectors from the real crates, in `mod tests`). For example:

  ```lean
  /-- [rmcp::model::request_state_wire::prim::b64_decode]: ...

  **Model:** `ok (b64Decode input)`. `URL_SAFE_NO_PAD` (`base64-0.23.1`,
  `src/engine/general_purpose/mod.rs` line 472) decodes strictly: padding, foreign bytes,
  a length `≡ 1 (mod 4)` and non-zero trailing bits are errors. -/
  def model.request_state_wire.prim.b64_decode (input : Slice Std.U8) :
      Result (Option (alloc.vec.Vec Std.U8)) := ...
  ```

- **Pin dependencies.** Pin any dependency version a model relies on in `PINNED_DEPS` of
  `scripts/aeneas-translate.sh` ([Pinned toolchain](#pinned-toolchain)).
- **Consistency.** Not needed while `trusted/` declares no axiom (a definition or an `opaque`
  constant cannot prove `False`). An axiom added again needs a consistency model in
  `proofs/Proofs/Consistency/<Group>.lean`, instantiating the opaque functions with a concrete model
  and proving every axiom of the group for it.
- **Not visible in axiom lists.** `#print axioms`, the `#guard_msgs` lists and `axioms.lock` show
  axioms only: the external models (definitions, structures, `opaque` constants) do not appear
  there, so a change to a model is caught only by review of `formal/trusted/`. A proof may use a
  model only once it is signed off.

### Native-code axioms and compiler-trusting tactics

`native_decide` and `bv_decide` (and `decide +native`) may be used while developing a proof, never
in a merged one: `lean-guard.sh sources` rejects the words, and the axioms they add fail the
`axioms` audit and the `#guard_msgs` checks. Remove them before sign-off.

The one exception is generated code: the Aeneas `toStr` side condition of a string literal declared
in `Rmcp.Types`/`Rmcp.Funs` (human decision). Each such axiom that a `Defs`/`Proofs`/`Specs`
constant depends on needs a reviewed entry in `formal/trusted/native-axioms.lock`, so a new string
literal in a target may need one. The pinned Aeneas declares none, and the lock is empty. The exact
audit rule is in [README "Commands"](README.md#commands).

### What must be trusted

A proved spec says something about the Rust code only if all of the following are right:

- **Tools:** Charon and Aeneas translate the Rust faithfully, and Lean's kernel checks proofs
  correctly.
- **Configuration:** the target and features chosen in the translate script. Other configurations
  are not covered.
- **Translation patches** (`formal/trusted/patches/`): each one preserves behaviour.
- **External models and axioms:** in `formal/trusted/Rmcp/FunsExternal.lean` and
  `TypesExternal.lean` (external and opaque items), and any axioms listed in the spec files.
- **Statements:** the definitions in `specs/Defs/` (and `proofs/Proofs/Defs/`) and the statements
  in `specs/Specs/` (and `proofs/Proofs/Internal/`) say what we mean.
- **Exclusions:** excluded items are not verified at all, and neither is anything outside the
  scope decided at the start.

The proofs themselves don't need to be read or trusted: Lean checks them. Record every trust item
(patch, model, `exclude`/`opaque` entry, accepted axiom) in [`specs/README.md`](specs/README.md),
"What you must trust", in the PR that adds or changes it.

### Spec files

**Public and internal** (human decision). `formal/specs/Specs/` holds only statements about the
**top-level** public rmcp API: functions `pub` in upstream rmcp that no other verified function
calls (human decision 2026-11-28). A public function that a top-level one calls (directly or through
helpers) is an **intermediate** function: it is verified as well, but its statement, like the
consequences of a `Defs` model that call no Rust function, goes to `proofs/Proofs/Internal/<Rust
path>.lean`, and so do the compositions that mention an intermediate function. Compositions of
top-level functions stay in `Specs/`. Statements about private, crate-internal (`pub(crate)`) and
patch-only functions, and the laws of the external models, are restated in the same format in
`proofs/Proofs/Internal/<Rust path>.lean` (the model laws in
`proofs/Proofs/Internal/External.lean`). Each file's module docstring starts with a summary table
(ID, function, guarantee, assumptions), and `specs/README.md` indexes every guarantee in plain
English.

There is one spec file per Rust source file, mirroring its module path:
`Specs/Model/RequestStateWire.lean`, `Specs/Model/RequestState.lean` (Phase 1); `Specs/Model.lean`,
`Specs/Model/Task.lean`, `Specs/Transport/Common/ClientSideSse.lean`,
`Specs/Transport/AsyncRw.lean`, `Specs/Transport/StreamableHttpServer/Tower.lean` and
`Specs/Transport/Auth.lean` (Phase 2, plan Section 20); and so on for later targets. The spec file
is everything a reader needs to trust the result: what is claimed and what each claim rests on.

- The module docstring states the translated configuration (`x86_64-unknown-linux-gnu`, the
  feature list of plan Section 15, human decision H1), names the `Defs` the statements use, and
  lists the items of that Rust file that were not translated (plan Section 2.3).
- Statements appear in Rust source order, composition theorems last. Exception (spec owner; widened
  by human decision 2026-11-28): `Specs/Model/RequestState.lean` lists its statements (R01–R15
  without R05, R08, R10, R14) in ID order, with the Rust source order given in its module docstring,
  and the section "Intermediate public functions" of
  `proofs/Proofs/Internal/Model/RequestState.lean` lists R05, R08, R10, R14 in the same ID order, as
  the last section of that file (after the section "R10a, R10b and the model round trip").
- Each statement is restated as a `theorem` in the `Theorems` namespace (as in the
  curve25519-dalek fork's `ForHumans/Theorems`), with the statement text of the signed-off spec,
  proved by the spec theorem it restates (so Lean checks the restated type against the proved one).
  It has a docstring giving the plan ID and a one-line summary, and is followed by its axioms,
  checked by `#print axioms`. If a proof starts using a new axiom, the check fails the build, so the
  change must appear as a diff of the spec file and in the PR footer.
- Names: `Theorems.<last module segment>.<Type>.<function>` without `_spec` (`<Type>.` only for
  methods; free functions are `Theorems.<last module segment>.<function>`), e.g.
  `Theorems.request_state_wire.parse_rs1`, `Theorems.request_state.RequestStateCodec.open_at`,
  `Theorems.model.JsonRpcMessage.into_request`, `Theorems.async_rw.is_standard_method`. The laws of
  the external models are `Theorems.External.<original name>`, keeping the original name, because a
  shorter one could shadow a Rust function name that the statements mention. Failing-case
  companions, joint lemmas and compositions are named after their statement.
- Exception (spec owner; widened by human decision 2026-11-28): the public statements of
  `Specs/Model/RequestState.lean` and of the section "Intermediate public functions" of
  `proofs/Proofs/Internal/Model/RequestState.lean` (R05, R08, R10, R14, moved there verbatim) use
  the abbreviations of `Defs.CodecState` and readable binder names, so their text differs from the
  spec theorems in `proofs/Proofs/Model/RequestState/` (the binder renaming map is in the "Proofs"
  paragraph of `Specs/Model/RequestState.lean`); Lean still checks each restated type against the
  proved one, and each was checked definitionally equal (`rfl`) to its signed-off text.
- Add a statement here only when its proof has no `sorry` and its specification is `REVIEWED`.

```lean
open rmcp.model.request_state_wire  -- for `Rs1Parts`; the function is still named in full

/-- W08 `parse_rs1`: `Some {body, tag}` iff the token splits on `.` into
`["rs1", body, tag]`. -/
theorem Theorems.request_state_wire.parse_rs1 (s : Slice U8) :
    rmcp.model.request_state_wire.parse_rs1 s ⦃ (r : Option Rs1Parts) =>
      r = Defs.parseRs1 s.val ⦄ :=
  rmcp.model.request_state_wire.parse_rs1_spec s

/--
info: 'Theorems.request_state_wire.parse_rs1' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.request_state_wire.parse_rs1
```

Use exactly this form: a bare `#guard_msgs in` (no options such as `drop`, `whitespace` or
`substring`) followed by one `#print axioms` line; `scripts/lean-guard.sh` rejects any other. The
docstring therefore matches the complete message, which prints the full name of the theorem.
Expected builtin axioms are `propext`, `Classical.choice` and `Quot.sound`; any other axiom in a
list must be a recorded trust item.

### Status vocabulary

Results use the status vocabulary of plan Section 6, with four independent fields per function:
`translation`, `spec` (`DRAFT`, `REVIEWED`), `linkage` (`ORIGINAL`, or `patch-NN` when the
translation depends on translation patch NN), and `proof` (`CHECKED` when Lean checks it without
`sorry`). A function is called **verified** only when `proof: CHECKED`, `spec: REVIEWED`,
`linkage: ORIGINAL`, and its axioms are all in the trusted base. For a Phase 2 target (`Mxx`, `Txx`,
`Axx`) and any other target claimed `ORIGINAL`, `ORIGINAL` additionally requires
`scripts/check-original-linkage.sh` to pass on the head commit (plan Section 19); while that check
has not run in CI, `ORIGINAL` is only pending.

Only a human may set `spec: REVIEWED` or accept a task. A deadline never changes a status, and an
accepted blocker report closes the task of reporting, never the function's proof.

## Proofs

Proofs are added for everything else: the public specs, plus whatever lemmas about internal
functions they need. Proofs need no trust review (Lean checks them); they are reviewed for style,
layering and build time. A proof is never merged with `sorry`; a statement whose proof is not
finished stays in `specs/Drafts/`, with an issue open for it. Where available, a Lean LSP / Beam MCP
(goals at a point, run a tactic, `#print axioms`) speeds this work; it is an optional aid.

### Proof files

Phase 1 has one proof file per Rust item, under `proofs/Proofs/Model/RequestStateWire/` for `Wxx`
and `proofs/Proofs/Model/RequestState/` for `Exx`. Phase 2 (plan Part II) instead uses one file per
Rust type or module, holding several targets: `Proofs/Model/{JsonRpcMessage,NumberOrString,Task,SamplingContent,Reference}.lean`
for `Mxx` and `Proofs/Transport/{ClientSideSse,AsyncRw,Tower,Auth}.lean` for `Txx`/`Axx` (plan
Section 20). Other translated code mirrors the Rust module path below `Proofs/Model/`, for example
`Proofs/Model/Transport/StreamableHttpServer/Tower/HostIsAllowed.lean`.

- The file holds the function's spec theorem together with any lemmas needed only for its proof.
  Lemmas usable elsewhere go in a shared file (e.g. `Proofs/Model/RequestState/Common.lean`); shared
  lemmas about `b64`, `dot` or the HMAC model are not duplicated per function.
- The file is named after the function (Phase 2: the type or module) in UpperCamelCase: for
  `open_rs1_at` the file is `OpenRs1At.lean`. File names are fixed by the table in plan Section 5
  (Phase 1) and the tree in plan Section 20 (Phase 2).
- The file contains a module docstring immediately after the imports. It explains the function
  concisely, and gives the plan ID, the Rust source path, and the line at the pinned commit (for a
  patched target: the line in the patched copy; for an unmodified target: the line at upstream
  `7caec76`):

  ```lean
  /-!
  # Spec theorem for `open_rs1_at` (E09)

  Opens an `rs1` token: parses three `.`-separated parts, decodes body and tag, verifies the tag
  against the configured keys, then checks expiry.

  Source: "crates/rmcp/src/model/request_state.rs", line 620 at `<pinned commit>`
  -/
  ```

- Further details or an overview of the proof can go in other comments if useful. Docstrings explain
  the statement, the Rust lines it covers, and its assumptions; they do not narrate proof
  development.
- Laws about the external models are theorems in `Proofs/External/<Group>.lean`; consistency models
  (only if an axiom is added again) go in `Proofs/Consistency/<Group>.lean`.

### Spec theorem style

State every function spec theorem with the Aeneas `⦃ ... ⦄` WP syntax of the pinned Aeneas library.
The canonical layout is below; the argument types are illustrative, so use the generated signature
from `formal/translation/Rmcp/Funs.lean`:

```lean
/-- **Spec theorem for `rmcp::model::request_state::RequestStateCodec::open_rs1_at`**

Concise natural language description of the spec, including its arithmetic domain and target
width where relevant. -/
@[step]
theorem open_rs1_at_spec (self : RequestStateCodec) (sealed : Str)
    (associated_data : Slice U8) (now_ms : I64) (h : CodecFallbacksKnown self) :
    open_rs1_at self sealed associated_data now_ms ⦃ (result : Result (Vec U8) Error) =>
      post_condition_1 ∧
      post_condition_2 ⦄ := by
  ...
```

- The theorem is about the translated definition in `Rmcp/Funs.lean` (or the external in
  `FunsExternal.lean`), with its current full generated name, not a local copy.
- Add the attribute `@[step]` so that the Aeneas `step` tactic can use the theorem in callers. Start
  a new line after the attributes.
- Name the theorem after the function with the suffix `_spec`; its identifier must be the **full
  generated name** of the function with that suffix. The failure-case companion is
  `<generated name>_fail`.
- Open namespaces so that the identifier prefix does not clutter the statement while the theorem
  identifier is still the full name. For a spec theorem for
  `rmcp.model.request_state.RequestStateCodec.open_rs1_at`, open
  `namespace rmcp.model.request_state.RequestStateCodec` earlier in the file and `end` it later.
- Put arguments and preconditions (`(a : argType)`, `(h : pre_condition)`, ...) after the name and
  on following lines. Name the arguments exactly like the parameters of the Rust function.
- Immediately after the main `:` of the theorem, start a new line with the function application and
  the WP binder: `fun_name a b ⦃ (result : resultType) =>`.
- Always give `result` its type; this needs brackets to parse.
- Write postconditions as a conjunction `post_condition_1 ∧ post_condition_2 ∧ ...` inside
  `⦃ ... ⦄`. When the function returns a Rust `Result`, cover the `Ok` case and every `Err` case,
  for example with a `match result with` whose arms are listed in the Rust order of checks.
- Indentation:
  - `@[step]` tag and `theorem fun_name_spec` line: 0 spaces
  - arguments, preconditions, and the line with the function application: 4 spaces
  - postconditions `post_condition_i ∧`: 6 spaces
  - proof body: 2 spaces

A draft in `specs/Drafts/` uses the same layout, with the proof replaced by `sorry`; it is never
built.

### Hypothesis conventions

- Write a no-overflow domain as a named hypothesis (e.g.
  `(h_no_overflow : 4 * ((n + 2) / 3) ≤ Usize.max)`), and mention it in the docstring, together with
  the fact that it matches debug-build semantics. (Aeneas models overflow as failure, matching
  debug builds only; release builds wrap.)
- Write a target-width assumption as a named hypothesis (e.g.
  `(h64 : System.Platform.numBits = 64)`), used only where the claim depends on it.
- Take the codec-state invariant as a hypothesis built from the definitions in
  `Defs/CodecState.lean`, and only the clauses the function needs: `CodecFallbacksKnown self` for
  E09/E11, `FallbacksKnown keys rs1_fallbacks` for E09a, none for E10 (spec-owner decision).
  Composition theorems may take the whole predicate `CodecValid self`, which implies each clause.
  Do not restate a clause inline.

### Composition theorems

Round-trip and dispatch theorems that span several functions are proved in
`proofs/Proofs/Model/RequestState/Roundtrip.lean` (`frame_roundtrip` in
`Proofs/Model/RequestStateWire/Frame.lean`), and restated at the end of the spec file of the
corresponding Rust file. Phase 2's C01–C05 are proved in the proof file of the targets they combine
(plan Section 20, e.g. C03 in `Proofs/Model/JsonRpcMessage.lean`) and restated at the end of that
Rust file's spec file.

- Theorem names say what the result is, following the Mathlib naming guidelines and the names of
  plan Section 5 (`rs1_roundtrip`, `open_at_roundtrip_rs2`, ...) or plan Section 16.4 for Phase 2
  (`SseEventSizeLimiter.observe_append`,
  `AuthorizationManager.is_disallowed_metadata_ipv6_eq_of_embedded_ipv4_eq_ok_some`, ...), rather
  than `<function>_spec`; round-trip theorems may be named `<function>_roundtrip`. They are not
  tagged `@[step]`.
- The docstring lists every premise of the round trip in words (body length, expiry, same
  associated data, key or kid conditions), and says which translated functions the theorem is
  about.
- A theorem that takes successful calls as hypotheses (`f args = ok r`) says in its docstring that it
  covers only successful calls and does not show that any call succeeds.

### Lean style

This applies to hand-written Lean in `formal/` (`trusted/`, `specs/`, `proofs/`). Generated files
under `formal/translation/` are not subject to it. Rust code follows the repository's
`rustfmt.toml`, `clippy.toml`, and the [contribution guide](../docs/CONTRIBUTE.MD). We follow the
[Mathlib style guide][mathlib-style], with the additions below.

**Header and imports.** File headers of hand-written Lean files have the form:

```lean
/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joe Cool
-/
```

- The copyright holder is the author or their current employer.
- Add anyone who has made significant contributions to the file to the author list, in the order in
  which they first edited it. There are no strict rules on what qualifies: list the people we would
  ask about the design or development of the file.
- AI tools are never listed as authors, including when they drafted the specification or proof;
  disclose AI drafting in the PR instead ([AI contributions](#ai-contributions)).
- List imports immediately after the file header, without empty lines.

**Flexible tactics.** Flexible (non-terminal) tactics make proofs fragile and harder to maintain.
Avoid them as much as possible:

- **`simp`**: use `simp?` to obtain the explicit lemma list, then replace it with `simp only [...]`.
  This makes the proof deterministic and resistant to changes in the simp set.
- **`simp_all`**: same rule; use `simp_all?` to obtain `simp_all only [...]`.
- **`grind`**: prefer more targeted alternatives (`omega`, `decide`, `bv_omega`, explicit
  rewriting) where feasible.
- **`exact?`** / **`apply?`**: use these *interactively* to discover the right lemma, then replace
  them with the explicit `exact` or `apply` call.

When a flexible tactic is genuinely the best option (e.g. a `simp` that closes a goal and whose
lemma list would be impractically long), document why in a short comment. These rules are the
target for merged proofs; during phase B a working proof that uses flexible tactics is acceptable,
and phase C replaces them without changing any statement. Prefer an existing Aeneas, Mathlib or
local lemma to rebuilding infrastructure, and do not add unused helpers.

**Linters and banned words.** Resolve linter warnings rather than suppressing them: every warning
fails the build. Do not leave `#check`/`#eval` leftovers. The only `#print` allowed is
`#print axioms` under a bare `#guard_msgs in` in spec files. The full list of words and constructs
that `scripts/lean-guard.sh sources` rejects is in [README "Commands"](README.md#commands); the
contributor-facing summary is in [Guard rules for hand-written Lean](#guard-rules-for-hand-written-lean). The check is
textual, so these words are rejected in comments and docstrings too: write "placeholder" or
"unproved" for sorry, "assumption" or "postulate" for axiom, "foreign" for extern, "unchecked" for
unsafe, "grammar" or "notation" for syntax, "set up" for initialize and "input/output" for IO in
prose. Only `#guard_msgs` may be written as prose in backticks (`` `#guard_msgs` ``).

**Heartbeats.** Keep `set_option maxHeartbeats` increases to the minimum needed, and scope them to a
single declaration with `set_option ... in`. Use multiples of **200000** as the standard increment
(e.g. 400000, 800000). If a proof needs a very large budget, split it into helper lemmas.

**Formatting.**

- Limit all lines to 100 characters. Exempt: header lines copied verbatim from the Aeneas templates
  (`/-- [<rust name>]:`, `Name pattern: [...]`) and Markdown table rows, which cannot be wrapped.
- In multi-line comments, wrap only when necessary: use as much of the 100-character limit as
  possible before breaking.

**Naming.** Name definitions and theorems (except function spec theorems) following the
[Mathlib naming guidelines][mathlib-naming]: theorems snake_case named after their statement,
definitions lowerCamelCase (also when `Bool`-valued), types, structures and `Prop`-valued
definitions UpperCamelCase; constructors and `≠` are written in lower case inside theorem names
(`map_err_ok`, `ne_dot_of_mem_b64`). Acronyms are written as words, as in the Rust names
(`ipv4Value`, `embeddedIpv4`, `utf8Bytes`, `parseI64`, `previousWasCr`; human decision). Project
conventions kept beside Mathlib's (human decision): a function spec theorem is
`<generated name>_spec` and its failure-case companion `<generated name>_fail`; round-trip theorems
may be named `<function>_roundtrip`. Generated Aeneas names are never renamed.

## Building and checking

```bash
cd formal
../scripts/lean-guard.sh sources            # lakefile, manifest pins, banned words and constructs
lake exe cache get
set -o pipefail; lake build --wfail 2>&1 | tee .lake/build.log    # .lake/ is git-ignored
../scripts/lean-guard.sh build-log .lake/build.log  # no warning or error line
../scripts/lean-guard.sh axioms             # only after a successful build: axioms, kernel replay
../scripts/lean-guard.sh aeneas-archive     # Aeneas archive and installed build match the digest
```

Stale `.lake` artifacts can hide a missing import or an unbuilt module. When in doubt, build the
changed module explicitly, for example `lake build Proofs.Model.RequestState.OpenAt`.

For Rust-side changes:

```bash
cargo test -p rmcp --no-default-features --features request-state,server,client,client-side-sse,transport-streamable-http-server,transport-streamable-http-client,auth,macros --lib   # macros: upstream tests need it
cargo clippy -p rmcp --no-default-features --features request-state --lib -- -D warnings   # clippy stays on request-state: with the widened features, upstream helpers are unused (dead_code)
cargo +nightly fmt --check
just fix                   # fmt and clippy fixes, see CONTRIBUTE.MD
```

### Build gate

Every `[[lean_lib]]` sets `leanOptions = { warningAsError = true }` (human decision); `Rmcp`, the
generated translation, and `RmcpExternal`, the trusted models, also set `autoImplicit = false`
(human decisions XD3, XD9), so that an undefined name is a build error instead of a silently
auto-bound variable. CI runs `lake build --wfail`, so any warning (including `sorry`, and warnings
replayed from dependencies) fails the build; the `#guard_msgs` checks run as part of the build.
`scripts/lean-guard.sh` adds the `sources`, `build-log`, `axioms` and `aeneas-archive` checks,
because a file could switch the option off, hide messages, add declarations without a kernel check,
or run code during the build. What each check does, and its limits, is in [README
"Commands"](README.md#commands); run `axioms` only after a successful `lake build`.

### Guard rules for hand-written Lean

The rules you will meet as a contributor (`sources` is textual, so comments and docstrings count;
see [Lean style](#lean-style) for the prose replacements):

- No `sorry`, `admit`, `native_decide`, `bv_decide`, `decide +native`, `implemented_by`, `extern`,
  `unsafe`, `warningAsError`, `debug.` options, or `set_option linter.<name> false` anywhere outside
  `translation/` (`trusted/` included), and no `axiom` outside `trusted/`. The one linter exception
  (human decision): exactly one `set_option linter.dupNamespace false in` in
  `trusted/Rmcp/FunsExternal.lean`, directly before the docstring, attributes and `def` of
  `zeroize.Zeroize.Blanket.zeroize`, whose Aeneas name repeats `zeroize`.
- `set_option autoImplicit` / `relaxedAutoImplicit` only with the value `false` (quoted or not,
  `… in` form included); in `translation/` these option names may not occur at all (human decision
  XD3: the generated `Rmcp` library sets `autoImplicit = false`, as does `RmcpExternal` (XD9), so
  an undefined name is an error).
  No comment between `set_option` and its value, and the linter rule also catches `«…»`-quoted
  name components (`set_option «linter».x false`).
- Nothing that runs or registers a metaprogram during the build (`#eval`, `run_cmd`, `elab`,
  `macro`, `syntax`, `initialize`, `simproc`, the metaprogramming monads, metaprogram attributes,
  ...). `notation`, `infix`, local instances and `simp` attributes are allowed. Write a custom tactic
  out inline; a separately reviewed tactic module would be a human decision (the ban stays
  everywhere).
- `#guard_msgs` only in `specs/Specs.lean`, `specs/Specs/` and `proofs/Proofs/Internal/`, and only
  as a bare `#guard_msgs in` followed, on the same or the next line, by exactly one
  `#print axioms <name>` that ends the line. Written in backticks on both sides it is prose and
  skipped; this covers only `#guard_msgs`, not the banned words.
- No identifier in the namespace `rmcp` and no `export` in `trusted/`
  ([README "Namespace rule for `trusted/`"](README.md#namespace-rule-for-trusted)).
- No symlinks under `formal/`.
- Generated files get the same rules, with two exceptions: a word excused at a line pinned in
  `trusted/translation-pins.txt` (only while the file has the pinned sha256; review reads each
  pinned line in context), and (human decision) the word `macro` inside the exact Aeneas phrase
  "this code is generated from a macro invocation at:" on a line that is exactly an Aeneas
  `Source: '…', lines …; this code is generated from a macro invocation at: '…', lines …` docstring
  line. In `translation/`, Aeneas's `set_option linter.* false` is allowed, `#guard_msgs` is banned,
  and `axiom` is banned except in the unbuilt `*_Template.lean` files, which are exempt.
- `sources` first runs `lean_guard.py selftest`, which checks these exact exemptions.

Axiom locks: every trusted or native-code axiom reachable from a `Defs`/`Proofs`/`Specs` constant
must be in `trusted/axioms.lock` or `trusted/native-axioms.lock` with its statement hash. A lock
entry for a declared but unused axiom is reported as "unused (allowed)" (a reviewed model may be
locked early); an entry for an axiom no longer declared, or with a different statement hash, fails.
An unused, unlocked axiom is not checked, so reviewers of `trusted/` read such changes in the
diff.

The guard is defence in depth, not complete: its rules are textual, the metaprogramming list cannot
be exhaustive, and only the import closure of the default targets is built and audited. Reviewers
still check for metaprogramming and review `trusted/` by hand.

### CI

Three workflows run on every relevant PR, and a PR is ready only when all three pass:
`aeneas-translation.yml` (the committed translation equals a fresh one, so stale translations and
hand edits fail; then the ORIGINAL linkage check), `lean-build.yml` (build in one job, `sources`
before any project Lean code runs; `build-log`, `axioms` and `aeneas-archive` on the uploaded
output in a second, fresh job), and `patched-tests.yml` (the crate's library tests on the patched
copy, with `register_tool` for the patches' `#[verify::…]` attributes: evidence that the patches
preserve behaviour). Together they guarantee that what is proved is the translation of the Rust
code in the repo, and that the patches don't change its behaviour.

`scripts/check-original-linkage.sh` decides whether a record may say `linkage: ORIGINAL`: it
translates the unpatched source and requires the result to elaborate identically to the committed
translation for those targets (plan Section 19). Its steps and stated limits are in
[README "Commands"](README.md#commands) ("The linkage check").

Trigger paths, the two-job design of `lean-build.yml`, and the residual limits CI accepts (build-time
code can forge the artifact; models are invisible to the locks; `Specs` imports `Proofs`; Mathlib
oleans are not digest-checked; a fake `rustc`; crafted `.olean` files) are in
[README "What CI checks"](README.md#what-ci-checks). Review is the barrier for what CI cannot see.

## PR workflow and format

### Scope of a PR

All verification PRs must advance a step (`Sxx`) of the plan, or close an open issue in the
project, unless special circumstances are justified. Whenever possible, a PR covers exactly one
step and one function (`Wxx`, `Exx`, or Phase 2 `Mxx`, `Txx`, `Axx`; likewise later IDs). Keep its
scope as small as possible, ideally not exceeding ~500 LOC of hand-written Lean and Rust.
Regenerated translation output, refactoring, and documentation do not count towards that limit.

Keep these kinds of change in separate PRs:

- a source refactor or Aeneas `rev` bump,
- a change to the Charon settings or a translation patch, with the regenerated translation,
- an external model (or axiom),
- a specification,
- a proof of an already signed-off specification.

A specification and its proof may share a PR only if the specification was signed off in an
earlier review round on that PR, and was not changed afterwards to make the proof go through.

Discuss with the others working on the project before starting a PR, to avoid duplicate work.

PRs are reviewed when marked as ready (not a draft) and all checks have passed. After the PR is
created (or marked as ready), hold off on meaningful changes until after the review, so that
reviewers do not look at outdated code. After review the author is responsible for merging the
accepted PR, and is expected to do so promptly.

### Recording results

Every PR that advances a step records its result in the same PR:

- **[`specs/README.md`](specs/README.md)**, the guarantee index: a row for every statement added to
  a spec file, and the "What you must trust" section whenever a patch, external model, axiom,
  exclusion or opaque item is added, removed or changed.
- **The "Results" section of [`README.md`](README.md)**: status (with the vocabulary of
  [Status vocabulary](#status-vocabulary)), bugs found, and open items, including blockers with a
  minimal reproducer. It lists only actual results and names open, blocked and patched functions as
  such.
- **The commit message and PR body** carry the review and sign-off record: who drafted (human, or
  AI tool and model), who reviewed (each independent review), and who signed off; the exact
  commands run on the head commit with their exit status; the Aeneas tag and the commit translated;
  axioms and models added or changed; and the reviewer decision.

Only a human may set `spec: REVIEWED` or accept a task ([AI contributions](#ai-contributions)).

### PR format

**Title:** verification PRs name the step, function ID, and Rust function, for example
"S07 E01: specify and prove `open_authenticated_body` in `request_state.rs`". Other PR titles use
imperative present tense ("add" not "added") and no trailing period.

**Body:**

- The first paragraph must start with "This PR". Use imperative present tense.
- Include motivation, and contrast with previous behaviour where relevant.
- Do NOT use markdown headings (## Summary, ## Test plan, etc.) in PR bodies.
- Include the full Rust name of each function the PR concerns (e.g.
  `rmcp::model::request_state::RequestStateCodec::open_rs1_at`) so that automation can find it.
- State the commands run on the head commit and their results.
- Report the build time of changed proof files when it exceeds a few seconds, and justify
  regressions. All PRs are expected to consider their impact on verification and CI time.

**Footer:** mandatory, and must contain:

- **Breaking changes (if any):** changes to a signed-off specification, `Defs` definition, axiom,
  exclusion, or theorem name, each with justification and the consumers it affects.
- **Trust changes (if any):** every axiom, external model, patch, `exclude`, or `opaque` entry
  added, removed, or changed, and every `#guard_msgs` axiom list that changed.
- **AI disclosure:** one line per AI-drafted or AI-reviewed artifact; see
  [AI contributions](#ai-contributions).
- **Referencing issues:** closed issues on a separate line prefixed with `Closes`, e.g.
  `Closes #123, #456`.

**Labels:** PRs are encouraged, but not required, to use the same labels as the issues they close.

## Review and sign-off

Specifications, `Defs` definitions, external models and axioms, patches, `opaque`/`exclude` entries
and Charon setting changes are all part of what must be trusted. Each one gets:

1. **at least two independent agent reviews** (`mcp-review`, in separate sessions, with no access to
   each other's reports), using the [review checklist](#review-checklist-ai-and-human-reviewers),
   recorded in the PR (commit message and PR body); then
2. **sign-off by the named human spec owner**, using the same checklist.

Agent agreement alone never accepts anything; an AI review with no findings does not count as
acceptance. Proofs need no separate trust review: Lean checks them. They are reviewed for style,
layering and build time. The generated translation needs no trust review either: the translation
CI regenerates it.

## AI contributions

AI tools, including the Claude agent roles of plan Section 10, may draft specifications, proofs,
external models, patches, tests, and records, and may review them. The human submitting the PR is
responsible for all of its contents.

**Specifications.** AI-drafted specifications are allowed, under these conditions:

1. **Disclosure.** The PR footer lists each AI-drafted artifact, for example
   `AI-drafted: open_rs2_at_spec statement; Base64 model in FunsExternal.lean`. Record the tool and
   model in the PR body and commit message.
2. **Grounding.** Each drafted clause cites the Rust lines at the pinned commit, or the section of
   plan Section 3 or 4, that it encodes. A clause with no source is a defect, not a design choice.
3. **No self-acceptance.** An AI may not set `spec: REVIEWED`, accept a task, or approve a PR. Every
   AI-drafted specification gets the independent reviews and human sign-off of
   [Review and sign-off](#review-and-sign-off) before any proof of it starts.
4. **Separation of roles.** The agent that drafted a specification may not prove it, and may not be
   one of its reviewers. A proof worker that finds a signed-off specification false returns a
   counterexample; it does not weaken the statement, and the spec returns to `DRAFT`.
5. **Models, patches, and exclusions.** AI-drafted axioms, external models, patches, and Charon
   setting changes follow the same rules, and each needs explicit approval from the spec owner in
   the PR review.

**Proofs.** AI-generated proofs are welcome if they comply with this guide. In phase B any working
proof is acceptable; refinement waits for phase C. The proof worker (`mcp-lean`) edits only its
assigned file under `formal/proofs/Proofs/` and the statement's restated theorem entry in the spec
file. It may not change statements, `Defs`, generated files, or anything under `formal/trusted/`,
and may not add axioms, `sorry`, `native_decide`, or `bv_decide`.

**Authorship.** AI tools are never listed as authors in Lean file headers. Use the commit trailer
convention of the repository for attribution.

## Review checklist (AI and human reviewers)

Each independent agent review follows this checklist, and the human spec owner uses it for
sign-off. Review ensures, as far as possible, that every specification (or its proof) meets:

- **Correctness:** specifications _must_ be counterexample free and describe the pinned Rust
  behaviour, including every error result and the order in which errors are checked. A proof does
  not settle this: it shows only that the code meets the statement. For external models there are
  no such guardrails at all.
- **Simplicity:** all else being equal, a simple formulation is preferable (it also reads better).
- **Readability and maintainability:** comments, deliberate whitespace, and concise statements help
  readers understand a specification beyond what its proof establishes.
- **Verification performance:** among equivalent proofs, prefer the one with the lowest build time.

A passing proof establishes its formal statement under its assumptions; review must also assess
whether those assumptions and that statement describe the pinned Rust implementation. Answer from
the current diff, the Rust source at the pinned commit, statements, generated Lean, external models,
patches, Charon settings, the result records, and validation results; ask the author only when a
material question remains open after that. Run each agent review in its own session, without
reading the other reviews first. The checklist supports review; it accepts nothing. Human
reviewers read the agent reports, but their agreement is not acceptance: the sign-off is yours.
Extend the checks when new evidence exposes a gap. Paths are relative to the repository root. When
a procedure step depends on a file that the PR's base does not contain, say so in the `Unverified`
line rather than skipping it silently.

### Procedure

Perform these steps first; they produce the evidence the questions refer to.

1. **Fix the revision.** Record the base and head commits and review exactly that diff:

   ```bash
   git fetch origin main pull/<N>/head:pr-<N>
   git merge-base origin/main pr-<N>          # base commit
   git rev-parse pr-<N>                       # head commit
   git diff <base>...pr-<N> --stat
   git diff <base>...pr-<N>
   ```

   If the author pushes after the review starts, re-record the head and re-read the changed hunks.
2. **Read the PR metadata and earlier reviews.** Check title, body and footer against
   [PR format](#pr-format), roughly 500 LOC, no meaningful pushes after the PR was marked ready,
   and that the diff stays inside the files the plan assigns to that step. For each earlier finding,
   check whether the current code fixes it, leaves it present, or shows it was mistaken; re-run the
   original counterexample against the revised statement. An author reply or resolved thread alone
   does not establish a fix.
3. **Check the source and the translation inputs** against the base:

   ```bash
   git diff <base>...pr-<N> -- crates/rmcp/src/model/request_state.rs \
     crates/rmcp/src/model/request_state_wire.rs crates/rmcp/Cargo.toml \
     crates/rmcp/build.rs Cargo.toml formal/lakefile.toml formal/trusted/ scripts/
   ```

   A source change is a defect if it breaks [Rust source changes](#rust-source-changes), if the
   regenerated translation is not in the same PR, or if a Charon setting, patch, or Aeneas `rev`
   changed without the review this guide requires.
4. **Re-translate when translation inputs change** (production code in the target files,
   `[package.metadata.charon]`, `crates/rmcp/build.rs`, the root `Cargo.toml`,
   `formal/trusted/patches/`, the scripts, `formal/lakefile.toml`, `formal/translation/`), in a
   separate working tree, as `aeneas-translation.yml` does:

   ```bash
   scripts/aeneas-install.sh
   scripts/aeneas-translate.sh
   git status --porcelain
   ```

   Any difference means the committed translation is stale or hand-edited; both are blocking.
5. **Build the head** with the commands of [Building and checking](#building-and-checking). CI runs
   the checks on uploaded build output, which cannot show it was compiled from these sources, so
   check hand-written Lean for metaprogramming yourself. Confirm that `Defs.lean`, `Specs.lean` and
   `Proofs.lean` list exactly the modules the PR intends to accept, and that drafts stay in
   `formal/specs/Drafts/`.
6. **Audit the trust base on base and head.** Compare the `#guard_msgs` axiom lists in
   `formal/specs/Specs/**` and `formal/proofs/Proofs/Internal/**`, and the diff of
   `formal/trusted/`. Every axiom other than `propext`, `Classical.choice` and `Quot.sound` must be
   a recorded trust item; `sorryAx` or `native_decide`/`bv_decide` axioms are trust changes (core
   question 6). The models do not appear in these lists; audit them through the diff of
   `formal/trusted/`. Check that no `#guard_msgs` check was loosened (a bare `#guard_msgs in`, one
   `#print axioms` line, the complete list in its docstring). An unchanged count of `axiom` or
   `sorry` is not a base audit: imports, models and generated bodies can change the trust base
   without those keywords. If reusing an earlier audit, name its exact revision; otherwise mark the
   comparison unverified.
7. **Run the Rust checks** of [Building and checking](#building-and-checking) for changes to
   `request_state.rs`, its tests, or contracts checked by test vectors. For a diff that claims to
   touch only `mod tests`, confirm that from the diff itself.
8. **Read the records:** PR body and commit messages, the changed rows of `formal/specs/README.md`,
   and the "Results" section of `formal/README.md`. Compare each recorded command, exit status and
   Aeneas tag with what you ran. Plan Section 7 lists what acceptance evidence must contain.

### Which sections apply

Answer the eight core questions on every PR, then each topic section that matches a kind of change
in it.

| Kind of change | Typical files | Sections to apply |
| --- | --- | --- |
| Specification | `specs/Drafts/`, `specs/Defs/`, `proofs/Proofs/Defs/`, a statement or docstring in `specs/Specs/**` or `proofs/Proofs/Internal/**`, `specs/README.md` | Specification strength; Results and records |
| Proof | `proofs/Proofs/Model/**`, `proofs/Proofs/Transport/**`, restated in `specs/Specs/**` or `proofs/Proofs/Internal/**` | Specification strength; Proof maintainability; Validation |
| Refactor, source change, Aeneas `rev` bump | `crates/rmcp/src/**`, `formal/lakefile.toml` | Translation and linkage; Validation |
| Translation, Charon settings, patch | `crates/rmcp/Cargo.toml`, `trusted/translation-pins.txt`, `trusted/patches/`, `translation/**` | Translation and linkage; External models |
| External model or axiom | `trusted/Rmcp/*External.lean`, `trusted/evidence/`, `proofs/Proofs/External/` (`Proofs/Consistency/` if an axiom is added again), trust items in `specs/README.md` | External models |
| Transcript, encoding, round trip | `RequestStateWire/TranscriptV{1,2}.lean`, `SealRs1/SealRs2`, `RequestState/Roundtrip.lean` | Transcripts and round trips; External models |
| Rust boundary tests | `mod tests` in `request_state{,_wire}.rs` (Phase 1, in patch 01); Phase 2: only `trusted/patches/02-phase2-tests.patch` (H3) | Validation; core question 8 |
| Results and records only | `specs/README.md`, `README.md` "Results" | Results and records |
| CI, scripts, agents, docs | `.github/workflows/`, `scripts/` (incl. `lean-guard.sh`, `check-original-linkage.sh`), `trusted/aeneas-bundle.sha256`, `CLAUDE.md`, `.claude/agents/`, `docs/`, `formal/README.md`, this guide | Validation; core question 8 |
| Other extractions | `verification/host_origin/**` and similar | Translation and linkage; External models |

(`formal/` prefixes omitted in the table.)

### Core questions (every PR)

1. **What exact claim does this PR establish?** Identify the step, function ID, Rust symbol and line
   at the pinned commit, changed theorem, and intended observable behaviour. Do title, body and
   records match the code? A function translated to compile is not a function verified; a generated
   file is not a specification; an extraction is not a proof.
2. **Am I reviewing the right revision?** Use the base and head of step 1, inspect the complete
   diff, and separate new changes from inherited problems. Have later commits changed the source,
   the generated Lean, or contracts covered by an earlier approval or build?
3. **Could a plausible wrong implementation satisfy the postcondition?** Try the wrong error
   variant, a different error order, accepting `now == expiry` the wrong way, dropping the length
   prefix from a MAC transcript, swapping token parts, stopping at the first matching fallback key,
   or ignoring the associated data. Name the clause that excludes each relevant counterexample.
4. **Are the premises satisfiable and justified at the call sites?** Look for no-overflow domains
   that exclude realistic inputs, codec-state hypotheses stronger than the constructors enforce, a
   64-bit hypothesis used for more than the `usize → u64` cast, and assumptions equivalent to the
   conclusion.
5. **Does the Lean model faithfully represent the Rust?** The theorem must be about the translated
   definition in `formal/translation/Rmcp/Funs.lean` (or the external in `FunsExternal.lean`), with
   its current full generated name, not a local copy. Check success, each error variant, panics,
   arithmetic and external calls against the Rust source. Library models can be wrong too.
6. **What changed in the trust assumptions?** From the step 6 audit: direct and transitive `sorry`,
   axioms not recorded as trust items, changed models, new patches or `exclude`/`opaque` entries,
   hand edits to generated files. Did an apparent reduction in axioms merely move assumptions into
   model definitions? A workaround moves the trust boundary; it does not remove it.
7. **Can callers use this result?** Can the dependent proofs (e.g. E09–E11, the round trips) and
   every target or composition theorem that uses it consume it as stated? Does the postcondition
   expose the transcript, error and output facts the next step needs? Is the spec-file statement
   phrased only with `Defs` definitions?
8. **What validation supports my conclusion?** Report the procedure commands that actually ran on
   the head and their results. Separate command results from claims in the PR body or records, and
   a successful build from a passing audit. A green build against another library revision does
   not establish the pinned build.

### Specification strength and error order

Compare the statement with the Rust source at the pinned commit (for a patched target, the patched
copy in `.llbc/work/`; `request_state_wire.rs` exists only there) and with plan Section 3. You may
spend less effort on proof details when the proof is `sorry`-free; never skip the statement check.

- Does the theorem cover success and every error result, not only the success path? Does it
  distinguish an application-level `Err(RequestStateError::…)` from an Aeneas failure or panic?
- For E09 and E10, is the complete error order of plan Section 3 fixed? Test an input wrong in two
  ways (an over-long encoded kid that is also bad Base64) and check which error the theorem implies.
- Is each error variant pinned with its fields where they matter (`KeyTooShort { minimum: 32,
  actual: len }`, the two distinct `InvalidKeyring` messages of E04)?
- Are boundaries exact? `now_ms == expiry` is accepted, expiry `0` means no expiry, a negative
  nonzero expiry is compared as a signed value; expiry is signed big-endian decoding of the first 8
  bytes.
- Does the specification add a restriction the Rust lacks? E04 accepts any nonempty UTF-8 kid of at
  most 255 bytes (an alphabet restriction would be unfaithful); `seal_rs2` accepts any kid
  (validity belongs in the round-trip premise, not E08's precondition).
- Is the arithmetic domain written into the theorem, and no stronger than needed? Release builds
  wrap while Aeneas models overflow as failure, so a theorem about E02 or the `with_capacity` sums in
  E07/E08 states its no-overflow domain and says it matches debug-build semantics there.
- Is a `usize` statement correct for the pinned 64-bit width, with the width hypothesis explicit and
  used only where needed?
- For E09 ring codecs, does the specification say "some configured fallback key verifies the tag"
  without asserting which key or implying early exit? It says nothing about timing; its
  documentation must not suggest otherwise.
- Is the abstraction (byte lists, `b64`, abstract HMAC state) clearer than the implementation steps,
  without erasing a detail callers need, such as part order? Is the level of abstraction right
  ([Deciding the public API specs](#deciding-the-public-api-specs))? For example, `r > 1`,
  `r != 0 /\ r % 2 = 0` and `r = 42` are all correct for a function returning `42`, each stronger
  than the previous; choose by what the known later steps need (e.g. E09–E11 build on W07–W11 and
  E01, the round trips of S15 on E07–E11) and by ease of proof.
- Are existential witnesses constrained enough? An existential is not weak by itself: check whether
  its predicate determines the relevant values before asking for a rewrite.
- **AI-drafted specifications** (listed in the footer): every clause must cite the Rust lines or plan
  section it encodes, and the source must say what the clause says; otherwise it is blocking. Look
  for clauses that mirror the code, hypotheses never used or excluding valid inputs, and
  postconditions that are vacuous or follow from the types. Was the statement weakened after an
  earlier round (compare with the accepted version)? Did the same agent draft and prove or review
  it? Does the review record show at least two independent agent reviews, none by the drafter?

### Translation and linkage

- Was the translation regenerated by `scripts/aeneas-translate.sh` from the pinned `rev`, Charon
  settings and patches, with no hand edit under `formal/translation/` and the translation CI
  passing?
- Does every target appear in `Funs.lean` with a real body, and no `sorry` anywhere in the generated
  files? Aeneas exits 0 with the plan's exclusions; a run that needs out-of-scope bodies to fail
  means an exclusion is missing. An exit code alone does not say which items failed.
- For a refactor: does each row of the plan's refactor table hold (same bytes MACed, same errors in
  the same order, every fallback still tried, empty-fallback check still before decoding,
  `u64::from_be_bytes(..) as i64` bit-identical to `i64::from_be_bytes`)? Is the only public API
  change the addition of `rmcp::model::request_state_wire`? Is token byte-identity shown by a
  committed regression test for one rs1 and one rs2 token, and do the tests cover `Expired` and
  `InvalidKeyId`? Check the stated coverage of any equivalence evidence.
- Does every new public wire item follow the Aeneas-safe coding rules of plan Section 2.1, carry
  documentation, and use `#[non_exhaustive]` on enums and structs?
- Does the recorded linkage match the decision taken? A refactor carried as a patch makes every
  dependent target `patch-NN` (all Phase 1 W/E targets are `patch-01`); `ORIGINAL` holds only while
  `scripts/check-original-linkage.sh` passes on the head (plan Section 19).
- For a patch: does the header state the change, why, and why behaviour is unchanged? Is it minimal,
  one concern? Does `patched-tests.yml` pass, and do the tests exercise the changed behaviour?
- Does the PR reintroduce an excluded function (plan Section 2.3) as a target, a callee, or by
  dropping its `exclude` entry, without a recorded requirement change and a translation run showing
  the blocker resolved?
- Is each new `exclude`/`opaque` entry commented and are its consequences visible? An excluded item
  must be outside the target closure; an opaque item must truly be untranslatable with no useful
  Rust model, and gets a reviewed model in `formal/trusted/`.
- Does a proposed change to the Rust, a patch or a Charon setting match the intended Rust
  behaviour, or is the problem in a premise or a library model? Check the source before changing
  translation inputs to make a proof work.
- For extractions outside `formal/` (e.g. `verification/host_origin/`), is the README precise about
  what is extracted, what is opaque, any recorded hand edit, and that no property has been proved?

### External models and the trust boundary

Inspect the cited sources (RFC, crate documentation, pinned crate source) to make sure they are
legitimate and correctly transcribed: this review is the only check of a changed model.

- Does every model follow the rules of [External models](#external-models): no `axiom` in `trusted/`
  (an axiom added again needs a human decision and a consistency model), no bare `Result` axiom, no
  model on merged types, described on its own terms without referring to or assuming a target
  function, docstring with source lines at the pinned version and exceptions, listed as a trust item
  in `formal/specs/README.md`, dependency pinned in `PINNED_DEPS` and matching the cited source?
- If `formal/trusted/translation-pins.txt` changes: does its sha256 equal the `Funs.lean` that the
  translate script regenerates (and `aeneas-translation.yml` reproduces)? Is each pinned line, read
  in context, one where Lean reads the pinned word inside a string literal (no open string or
  comment before it)? Is every new entry needed (a word the translation really emits)?
- HMAC (plan Section 4): `prim.hmac_sha256 k m` always succeeds with the opaque `hmacSha256 k m`, and
  `prim.hmac_sha256_verify k m t` holds iff `t = hmacSha256 k m` as byte lists. Does `verify` reject
  short or long tags?
- Base64: does the model match `URL_SAFE_NO_PAD`, rejecting padding and non-canonical trailing bits?
  Its laws (`b64Decode (b64 x) = some x`, `b64Decode s = some y ↔ b64 y = s`, alphabet, length) are
  theorems in `formal/proofs/Proofs/External/Base64.lean`; does a proof rely on any other Base64
  fact?
- Do W06–W09, stated with `List.splitOn '.'`, agree with `str::split('.')` on the empty string, no
  `.`, leading and trailing dots, and consecutive dots? Do E09–E11's part counts follow?
- Are standard-library models (`str::len`, `str::as_bytes`, `String::from_utf8`, `Option::ok_or`,
  `HashMap::get`, `Zeroizing` deref) value-correct for the operations used, without hidden
  assumptions about hashing or allocation? Is allocation failure an explicit assumption rather than
  a silent no-panic claim?
- Is the codec-state invariant no stronger than the constructors enforce? Every clause must be
  checkable against the constructor source (constructor correctness is out of scope).
- Is each model checked against concrete vectors from the real crates (RFC 4231 for HMAC, known
  Base64url values, split behaviour) in `mod tests`, listed in `formal/trusted/evidence/README.md`,
  existing and passing? Such tests catch a mismatched model; they are not a consistency proof.
- If an external became a concrete definition, where is the argument that the Rust function computes
  it? A concrete body can make correspondence lemmas reflexive while hiding the assumption from the
  axiom count; it is still part of `formal/trusted/`.
- Does any statement or docstring claim more than the plan's scope: HMAC unforgeability,
  constant-time behaviour, correctness of the `hmac`, `sha2`, `base64` or `zeroize` crates, or
  coverage of the public wrappers?
- Is the hand-written Lean (`proofs/`, `specs/`, `trusted/`) free of metaprogramming (`run_cmd`,
  `run_tac`, `#eval`, `elab`, `macro`, `syntax`, `initialize`, `addDecl`, `modifyEnv`, `simproc`,
  metaprogram attributes such as `tactic`, `init`, `delab`) and of indirect routes to it (e.g. an
  Aesop rule that runs a tactic definition)? The `sources` ban is textual and incomplete, and code
  run during `lake build` could forge the output CI audits. A custom tactic is written out inline.
- Every axiom in a changed `#guard_msgs` list beyond `propext`, `Classical.choice`, `Quot.sound` is
  a recorded trust item and named in the footer; a diff of `formal/trusted/` is a trust change too;
  a proof may use a model only once it is signed off.

### Transcripts, encoding, and round trips

- Does the W10/W11 theorem state the transcript bytes exactly (domain separator, big-endian 8-byte
  length prefixes, field order)? Would a transcript without a length prefix, or with kid and ad
  swapped, also satisfy it? Do E07–E10 use these theorems rather than restating the transcript?
- Does E07/E08 fix the version prefix, part order and `.` delimiters, and tie the tag to the
  transcript of the same key, ad and body?
- Are round trips stated with exactly the plan's conditions: body of at least 8 bytes, expiry `0` or
  `now ≤ expiry`, the same associated data, an rs1 opening codec that is the same single key or a
  ring whose `rs1_fallbacks` include the signing key, and an rs2 kid that is valid UTF-8 of 1–255
  bytes mapped by the ring to the signing key? Is a condition missing, or does an extra one exclude
  valid tokens?
- Does a round trip state that opening returns `body[8..]`, not the whole body or a payload?
- Do encoder postconditions establish the opening function's premises (the 340-byte encoded-kid
  bound of E10 against a 255-byte kid under `b64`)?
- Is each round trip about the translated `seal_*` and `open_*` functions, not only pure models?

### Results and records

- Do the records use the [status vocabulary](#status-vocabulary) exactly, with independent fields,
  and call a function verified only under the conditions stated there? Does anything overstate the
  result?
- Was `spec: REVIEWED` set by a named human spec owner after at least two independent agent reviews,
  none by the drafter, recorded in the PR (plan Section 6)? Are AI drafting and review disclosed in
  the footer, with tool and model in the PR body or commit message?
- Does the "Results" section of `formal/README.md` reflect the real state, follow the plan's results
  template, list only actual results, and name open, blocked and patched functions as such? (An
  accepted blocker report closes the reporting task, never the proof; a deadline never changes a
  status.)
- Does the PR record the exact commands, exit status, Aeneas tag and commit translated, models and
  axioms changed, and reviewer decision, and do they match what you ran?
- Does "What you must trust" in `formal/specs/README.md` match `formal/trusted/` and the
  `exclude`/`opaque` lists? Does every new spec-file statement have its row in the index?

### Proof maintainability and library layering

- Do the import directions of [Library layering](#library-layering) hold (nothing imports `Specs`;
  `Proofs` never does)? Does a draft with `sorry` stay in `formal/specs/Drafts/`?
- Is the spec-file statement phrased only with `Defs` (public: `specs/Defs/`; internal: also
  `proofs/Proofs/Defs/`)? Does its restated `theorem Theorems.…` carry the signed-off text, is it
  proved by the spec theorem, in Rust source order, with its `#guard_msgs` check?
- Is the file at the path the plan assigns ([Proof files](#proof-files)), with the plan's theorem
  name (`<function>_spec`, `rs1_roundtrip`, …) or a recorded replacement?
- Does an existing Aeneas, Mathlib or local lemma avoid rebuilding infrastructure? Is each new helper
  used? Are shared lemmas (`b64`, `dot`, HMAC model) in a shared file, not duplicated?
- Are flexible tactics replaced where practical (non-blocking in phase B unless fragile enough to
  break CI)? Are heartbeat increases justified and local?
- Do docstrings explain the statement, the Rust lines and the assumptions (arithmetic domain, target
  width), rather than narrate proof development?
- Did a proof worker stay inside its assigned file and restated theorem
  ([AI contributions](#ai-contributions))?

### Validation and CI

- Did checks use the PR's current sources and the toolchain of `scripts/aeneas-install.sh`, with no
  stale artifacts masking a missing import or unbuilt module, and the generated Lean built in
  `formal/`, not against an unrelated Aeneas build?
- Do the three workflows run on the paths of [CI](#ci), for fork and branch PRs, and keep failing
  exit codes through pipes? Does every `[[lean_lib]]` set `warningAsError`, and does
  `lean-build.yml` run `lake build --wfail` with `pipefail` and the four lean-guard checks? Has each
  check been shown to fail once: on a hand edit to `Funs.lean`, a new axiom, a `sorry`, and a
  failing patched test (plan S17)?
- Does a fresh clone reproduce install, translation and build with `git status` clean (plan S18)?
- Do the Rust boundary tests cover each case of the plan's Section 7 table (Phase 2: Section 22)?
  A test asserting only `is_err()` does not check which error variant is returned.
- For agent-driven workflows, are trigger conditions and edit limits enforced by permission
  settings, not only by role prompts?
- **Performance.** Compare the build time of changed proof files with the base when shared files
  changed. Does the cost come from repeated arguments, broad imports, or expensive automation a
  symbolic argument could replace? Decide whether to accept as is, accept and open an issue to
  revisit, or block until fixed.

### Other comments

Comment freely: requests to add or change comments, new `Defs` definitions, generalizing proof
chunks into shared lemmas, reusing existing spec code or models, style issues. These are generally
non-blocking and the author may act at their discretion; they may be made blocking if the problem is
particularly serious, especially for generalization and reuse. In phase B, proof-style comments are
non-blocking unless the proof is fragile enough to break CI. On GitHub, even when only commenting,
use "Submit review > Comment" rather than single comments.

### Reporting the review

The questions are the investigation checklist, not the outline of the report. The report lists only
problems: do not answer the questions one by one, restate what the PR does, or list passed checks
except in the validation footer. A reader should see the verdict and every finding, grouped by
severity, without reading anything else.

**Severity groups,** in this order; omit an empty heading:

- **Blocking:** a demonstrated counterexample to a specification, an unsatisfiable or
  question-begging premise, an unfaithful model of the Rust, a refactor that alters behaviour, an
  unjustified or unapproved change to the trust base, a record that overstates the result, or
  validation that did not pass on the head. Correctness comments are blocking.
- **Judgment (blocking or non-blocking):** level of abstraction, usability by later steps,
  composition gaps, test coverage of boundary cases, build-time regressions, in proportion to their
  impact.
- **Non-blocking:** naming, placement, reuse, comments, PR format and style, unless the plan makes
  the point mandatory or the problem is pervasive.

A keyword match or a difference from an earlier extraction is a prompt to investigate, not a finding.
State the group explicitly so the human can override it; say whether a judgment finding blocks, and
count it in the verdict if it does. When a new theorem inherits a weak shared contract, locate the
new caller-facing consequence and separate it from the root cause. Do not call a missing guarantee
an implementation bug without evidence for that stronger claim.

**Category tags.** Tag each finding with one category, naming the section that produced it:

| Tag | Source |
| --- | --- |
| `spec` | Specification strength and error order; core question 3 |
| `premise` | Core question 4 |
| `model` | Core question 5; Translation and linkage |
| `linkage` | Refactor and patch behaviour, source pin, linkage status |
| `trust` | Core question 6; External models and the trust boundary |
| `usability` | Core question 7; Transcripts, encoding, and round trips |
| `status` | Results and records |
| `validation` | Core question 8; Validation and CI |
| `maintainability` | Proof maintainability and library layering |
| `format` | Core questions 1 and 2; PR title, body, revision |

**Finding format:**

```text
- [`tag`] `path/to/File.lean:LINE` `theorem_name` — one-sentence defect.
  Evidence: counterexample, dependency argument, or Rust lines that define the intended behaviour.
  Consequence: what later steps, proof meaning, or verification scope lose.
  Ask: the focused question or requested correction, and what evidence would resolve it.
```

Keep the first line short. Put the head commit once in the footer. Report a defect found at several
places once, listing the locations. Cite Rust lines at the pinned commit and say which pin you used.

**What an AI review may propose:** replacement statements, postcondition clauses or contract
definitions in Lean, proof text, patches and Rust test cases. Each proposal must be labelled as an
AI-drafted proposal (so adopting it triggers the disclosure rule), cite the Rust lines or plan
section each clause encodes, come with the counterexample or gap it fixes, and leave acceptance to
the human spec owner. A review may not mark a specification accepted, and an AI reviewer may not
propose a statement for a specification it drafted. When the right formulation depends on a design
choice the plan does not settle, name the missing property in words and ask the author or spec
owner to choose. Examples of useful questions:

- "An rs2 token with a 341-byte encoded kid that is also invalid Base64 should return
  `InvalidKeyId`. Which clause rules out `InvalidEncoding` here?"
- "This transcript statement also holds without the length prefix. Which clause fixes it?"
- "This external became a definition and its axiom disappeared from the `#guard_msgs` list. Where is
  the argument that the Rust function computes it?"
- "The round-trip premise requires a nonempty ad. Is that intended? `seal_rs1` accepts an empty ad."
- "The record says `linkage: ORIGINAL`, but the translation depends on a patch. Which patch should it
  name (e.g. `patch-01`)?"
- "`git status --porcelain` shows a diff in `Funs.lean` after re-running the translate script. Was
  the translation regenerated after the last Charon setting change?"

**Report layout:**

```text
Verdict: <no blocking finding | N blocking finding(s)> on <head commit> (base <base commit>).

Blocking
- ...

Judgment
- ...

Non-blocking
- ...

Validation: <commands from the procedure that ran on the head, each with pass/fail>.
Unverified: <material boundaries not checked, or "none">.
```

The verdict comes first. If no blocking problem is demonstrated, say so without claiming
cryptographic security or full protocol verification. The validation line names the commands that
actually ran and their results, not the PR body or records. Recheck claimed fixes against the
updated diff rather than accepting an author reply. An AI review remains assistance for the
responsible human reviewer.

[mathlib-style]: https://leanprover-community.github.io/contribute/style.html
[mathlib-naming]: https://leanprover-community.github.io/contribute/naming.html
