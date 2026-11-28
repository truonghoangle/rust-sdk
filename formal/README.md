# Formal verification of selected rmcp SDK functions

## What this is

This directory is a Lean 4 project that proves functional correctness of selected functions of
the Rust MCP SDK `rmcp` (`crates/rmcp/`). The Rust code is translated to Lean with
[Charon](https://github.com/AeneasVerif/charon) and [Aeneas](https://github.com/AeneasVerif/aeneas);
each guarantee is a Lean theorem about the translated function: the call does not panic (no
failure, overflow or out-of-bounds access) and its result satisfies the stated postcondition. The
proofs hold for one pinned upstream commit, one translated configuration and the trusted base
listed below.

Start with [`specs/README.md`](specs/README.md), the plain-English index of every guarantee. To
contribute (workflow, style, PR format, review checklist), read [`CONTRIBUTING.md`](CONTRIBUTING.md).

## Results

All results are about upstream `rmcp` commit `7caec762799bece6fba38e4298b8ca7db8bac12c`
(`origin/main`; every SDK `*.rs` file in this repository is byte-identical to it), translated in
the configuration below. *Linkage* says what was translated: `ORIGINAL` means the unmodified
upstream source (checked by `scripts/check-original-linkage.sh`, see "Commands"); `patch-0N`
means the copy with translation patches 01 to 0N applied (see "Trusted base"). Every listed
function has a signed-off specification and a checked proof, restated as `theorem Theorems.…`
in a spec file with a `#guard_msgs` axiom check.

| Group | IDs | Rust functions | Linkage |
|---|---|---|---|
| Request-state wire format and codec (Phase 1) | W01–W15, E01–E04, E07–E11, E09a | `model::request_state_wire::{b64_len, key_length_ok, check_kid_len, bytes_eq, next_dot, component_count, version_of, parse_rs1, parse_rs2, transcript_v1, transcript_v2, decode_expiry, is_expired, open_frame, frame}`; `RequestStateCodec::{open_authenticated_body, b64_len, validate_key_length, validate_config_kid, seal_rs1, seal_rs2, open_rs1_at, rs1_fallbacks_verify, open_rs2_at, open_at}`; round trips `frame_roundtrip`, `rs1_roundtrip`, `rs2_roundtrip`, `open_at_roundtrip_rs1`, `open_at_roundtrip_rs2` | `patch-01` |
| JSON-RPC model (Phase 2) | M01–M14 | `JsonRpcMessage::{into_request, into_response, into_notification, into_error, into_result}`, `NumberOrString::{numeric_string_value, matches_response_id}`, `TaskStatus::is_terminal`, `SamplingContent::{into_vec, is_empty, len, first}`, `Reference::{as_prompt_name, as_resource_uri}` | `ORIGINAL` |
| Transports (Phase 2) | T01–T08 | `SseEventSizeLimiter::{check_limit, finish_line, observe}`, `async_rw::{without_carriage_return, is_standard_notification, is_standard_method}`, `tower::{default_port, AllowedPort::matches}` | `ORIGINAL` |
| Metadata-address checks (Phase 2) | A01–A03 | `AuthorizationManager::{embedded_ipv4, is_disallowed_metadata_ipv4, is_disallowed_metadata_ipv6}` | `ORIGINAL` |
| Compositions (Phase 2) | C01–C05 | SSE chunk append (C01), SSE bound at chunk boundaries (C02), `into_result` from `into_response`/`into_error` (C03), no SSRF bypass through embedded IPv4 (C04), every standard notification is a standard method (C05), plus the joint lemmas | `ORIGINAL` |
| Public `request_state.rs` API | R01–R08 | `SealOptions::{new, associated_data, ttl}`, `RequestStateCodec::{new, new_unchecked, try_new, open, open_with}` | `patch-01` |
| | R09–R15 (and internal R10a, R10b) | `seal`, `seal_with`, `with_rs1_signing`, `with_rs1_fallback`, `open_json`, `open_json_with`, `new_with_keyring`; R10a the private `seal_at` at an explicit time, R10b `seal_at` then `open_at` | `patch-03` |
| Public `skill.rs` API | K01–K20 (51 statements) | all twenty public functions of `model/skill.rs` | K01–K04, K08–K12, K17–K20 `ORIGINAL`; K05–K07, K13–K16 `patch-04` |
| Metadata address resolver | N01, N03–N11 (64 statements) | `AddressClass::of` (N01), `MetadataAddressResolver::{new, with_lookup, with_proxy_hosts, allowing_private_addresses, allows_url, is_allowed}`, its `Resolve::resolve` (address filtering part), `literal_ip`, `normalize_host` (N11), and `AuthorizationManager::is_loopback_metadata_host` | N01, N08 `ORIGINAL`; the others `patch-05` |
| OAuth metadata-URL and issuer checks | A04–A10 (81 statements) | `AuthorizationManager::{is_http_url, is_disallowed_metadata_host, is_allowed_metadata_url, resolve_resource_metadata_url}`, the checks of `validate_authorization_response_issuer`, `validate_authorization_metadata_issuer`, `validate_resource_metadata_resource` (as the patch-06 helpers `check_*`; the one-line `validate_*` wrappers are not verified), with their callees | `patch-06` |
| SEP-2243 header-value encoding | G01–G04 (39 statements) | `transport::common::mcp_headers::{requires_base64, is_tchar, encode_header_value, decode_header_value}`, with the round trip (decode after encode gives the value back) and header safety of every encoded value | `patch-07` |

Statements about top-level public functions (`pub` and called by no other verified function; human
decision 2026-11-28) are in `specs/Specs/`; the statements about intermediate public functions (R05,
R08, R10, R14, K04, K07, K12–K15, called by a top-level one), private, crate-internal and patch-only
functions (including M06, M07, T01–T08, A01–A10, G01–G04 and the N group) and the laws of the
external models are in `proofs/Proofs/Internal/` (see "Layout"). E05 and E06 are unassigned IDs
(they belonged to `mac_v1`/`mac_v2`, which patch 01 deletes).

**What `patch-0N` means for the claim.** The `patch-01` results are about upstream plus the
`request_state_wire` refactor of translation patch 01 (rule **D2**, the "D2 fallback": the refactor
did not land in the SDK source, so it is a translation patch applied only to the translated copy).
The link between the patched and the unpatched code is tested, not proved: the patch's byte-identity
regression tests run on the patched copy (`patched-tests.yml`), and a differential run of upstream
against the patched copy found no difference. If the refactor lands upstream, patch 01 can be
deleted and these targets can become `ORIGINAL`. Patches 03, 04, 05, 06, 07 and 08 are small
behaviour-preserving rewrites (each hunk is explained in the patch header).

**Axioms.** Every `#print axioms` list is within `[propext, Classical.choice, Quot.sound]` (Lean's
standard axioms; some lists are shorter). `trusted/axioms.lock` and `trusted/native-axioms.lock`
are empty: the project declares no trusted axiom, and no constant depends on a native-code axiom.
`scripts/lean-guard.sh axioms` checks this over every project constant (see "Commands").

### Bugs found

Twelve bugs, all in upstream `7caec76`, none **reported upstream yet** (reporting needs the project
owner's go-ahead; H9 is to be reported privately first). The statements describe the code as it
is. H9–H16 were found in the A04–A10 specification cycle of `auth.rs` (human decisions
2026-11-27); their statements were signed off and proved on 2026-11-27
(`proofs/Proofs/Internal/Transport/Auth/AuthMetadata.lean`). H17–H18 (low severity) were found in
the G01–G04 specification cycle of `transport/common/mcp_headers.rs` (human decisions 2026-11-27);
their statements were signed off and proved on 2026-11-28
(`proofs/Proofs/Internal/Transport/Common/McpHeaders.lean`).

- **H7: the `async_rw` method lists miss six core MCP names.** `is_standard_method` /
  `is_standard_notification` (`crates/rmcp/src/transport/async_rw.rs` lines 396–433) do not list
  `tasks/get`, `tasks/result`, `tasks/cancel`, `tasks/list`, `notifications/tasks/status` and
  `notifications/elicitation/complete`, which are in the core MCP schemas. When a line fails to
  deserialize (`try_parse_with_compatibility`, lines 468–485; `should_ignore_notification`, lines
  437–457) but parses as JSON with a string `method`, a line with one of these names is silently
  dropped (`Ok(None)`) instead of returned as a `Serde` error: always for the two notifications,
  and for the four `tasks/*` requests when the message has no `id`.
- **H8: `is_disallowed_metadata_ipv4` does not block `240.0.0.0/4`.**
  `AuthorizationManager::is_disallowed_metadata_ipv4` (`crates/rmcp/src/transport/auth.rs` lines
  1343–1354) accepts the reserved block `240.0.0.0/4` except `255.255.255.255`. Such a metadata
  URL passes the SSRF check, and a resolved address in it is classed `Public` by
  `AddressClass::of` (`auth/metadata_resolver.rs` lines 42–74), although the module doc (lines 8–9)
  says reserved addresses are never allowed.
- **H9: a recorded issue in the authorization-server metadata issuer check (A09), under private
  disclosure; details withheld until it is reported.**
- **H10: with private addresses allowed, cloud metadata endpoints in private ranges pass.**
  `is_allowed_metadata_url` (A06) with `allow_private`, and the resolver whenever it grants
  `Private`, accept e.g. `100.100.100.200` (100.64/10) and `fd00:ec2::254` (fc00::/7).
- **H11: some special-purpose IPv6 and IPv4 forms are `Public`.** The IPv4-translated range
  `::ffff:0:0:0/96` (RFC 2765), `100::/64` and `192.0.0.192` are neither rejected by A05 nor
  filtered by the resolver.
- **H12: the URL check (A06) falsely refuses targets the resolver policy accepts.** For some
  targets (IP literals, and a `localhost` name from a base that is an IPv6 embedding of 127/8) A06
  refuses what the resolver allows, e.g. a private authorization server from a private base
  without `allow_private`; it is never looser for IP-literal targets. (Context: the doc of
  `AuthorizationManager::new` describes the resolver's policy and gives only a necessary condition.)
- **H13: the resource-identifier check is looser than RFC 9728 §3.3.**
  `is_resource_identifier_valid` (A10) accepts an ancestor path, a different query and different
  user information. Upstream chose this: the query rule is commented at line 3013 and the ancestor
  rule is asserted by the test at lines 7148–7215.
- **H14: the resolver allows a blocked base literal's own address.** `allows_url`
  (`auth/metadata_resolver.rs` line 167) allows the base URL's own IP literal even when it is
  link-local or reserved (e.g. `169.254.1.1`, `0.0.0.0`), contradicting the module doc and the doc
  of `new` ("always rejected"); the method doc of `allows_url` (lines 162–163) states the exemption
  on purpose, so the client can reach the base itself.
- **H15: the issuer comparison tolerates a root trailing `/`.** `issuer_identifiers_match` treats
  `https://as.example` and `https://as.example/` (and a `/` ending a query or fragment) as equal,
  while RFC 8414 §3.3 requires identical issuers; an upstream test asserts the tolerance.
- **H16: the cloud-metadata host-name list has three names.** Names such as `instance-data` or
  `metadata.goog` are not rejected by A05; this matters with a custom HTTP client or a proxy, where
  the name check is the only guard.
- **H17: `decode_header_value` is not the exact inverse of `encode_header_value`.** The decoder
  (`transport/common/mcp_headers.rs` lines 256–268) accepts a Base64 sentinel around a value that
  needs no wrapping (CD1: `=?base64?dXMtd2VzdDE=?=` and `us-west1` both decode to `us-west1`). A
  second cause, recorded as a note (CD2), is that it also passes through a bare value the encoder
  (lines 62–77, 242–252) would wrap (`a⇥b` and `=?base64?YQli?=` both decode to `a⇥b`, ⇥ = HTAB).
  rmcp compares the decoded header with the request body, so the server itself is consistent, but
  an intermediary that filters on the raw, undecoded `Mcp-Name` or `Mcp-Param-*` value can be
  bypassed by the wrapped form. SEP-2243 (final text in `modelcontextprotocol/modelcontextprotocol`,
  `seps/2243-http-standardization.md`, and the 2026-07-28 Streamable HTTP page, read 2026-11-27)
  does not forbid an unneeded wrap and says that servers and intermediaries that inspect these
  values MUST decode them. Rejecting both forms makes decoding the exact inverse of encoding on
  UTF-8 values; either rejection alone does not (`requires_base64` would have to be built for the
  server too, it is `client-side-sse` only, line 61).
- **H18: list characters travel bare.** `,` and `"` do not by themselves make `requires_base64`
  true (lines 62–77), so a value such as `a, b` is sent unwrapped. This follows SEP-2243's encoding
  rule, which does not list them, so it is a candidate for both the SDK and the SEP. A proxy may
  combine duplicate field lines joined by `, ` (RFC 9110 §5.3); a merged duplicate pair cannot be
  told apart from a single bare value containing `, `, and `header_str` (lines 394–413) rejects
  duplicates only before such a merge.

- **H19–H23 (suspected, `model/elicitation_schema.rs`; decision XD4).** Found by probes on the Rust
  code in the translation stage of the elicitation schema builders (2026-11-28); their statements
  are pending (specification stage), which will state the actual behaviour. H19:
  `ElicitationSchemaBuilder::build` returns `Ok` for a schema with no property, although its
  documentation lists an empty schema as an error. H20: `required` can hold the same name several
  times (`required_string("a")` twice, `mark_required("a")`), which JSON Schema forbids. H21: the
  single setters accept `min_length > max_length`, `minimum > maximum` and a default outside the
  range, while `with_length`/`with_range` reject the bounds. H22: a multi-select enum accepts
  `min_items` greater than the number of values and duplicate defaults. H23: the documentation of
  `string_property` says "(required)", but the property is not required.

No bug was found in the request-state codec or `skill.rs`. Recorded
behaviours, not bugs: a single-key codec built with `new_unchecked` or the deprecated `new`
accepts a key of any length (only `try_new` checks it); `rs1_fallbacks_verify` panics (`expect`)
if an rs1 fallback id is not a key, which the keyring constructors prevent.

### Not covered

- `seal_json`, `seal_json_with` (R16–R17): excluded, blocked upstream (Aeneas does not support the
  mutually recursive `serde_core::ser` traits; they would also need the variant-constructor
  workaround of patch 03 hunk 2). Also excluded: `Error` for `RequestStateError`, the
  `Debug`/`Display` impls of `RequestStateError` and `RequestStateCodec`, and the derived `Debug`
  impls (the Charon `exclude` list of `crates/rmcp/Cargo.toml`, each with its reason).
- N02 `SystemResolver::resolve` (dropped, not a target); the async shells of `resolve` and
  `with_lookup`; the bodies of `prim::system_lookup` and `prim::proxy_env_values`; the derived
  `Clone` impls; URL parsing.
- The callers of the verified functions, URL and HTTP parsing, `async` code, DNS resolution; the
  full MCP protocol (the method lists are core protocol only, extensions are out of scope).
- Cryptographic security (HMAC unforgeability), constant-time behaviour, the correctness of the
  `hmac`, `sha2`, `base64`, `zeroize`, `unicode-normalization`, `unicode-general-category`,
  `percent-encoding` and `url` crates; negative round trips (a tampered token is rejected: needs a
  no-collision premise on the opaque HMAC model, deferred).
- Statements relating two clock or environment readings (the clock rule, "Trusted base").
- The codec-state invariant (`CodecValid`, `CodecFallbacksKnown`, `FallbacksKnown` in
  `specs/Defs/CodecState.lean`) is a premise of the internal statements; it is derived for the
  codecs the verified constructors build (R04–R06, R15; R11/R12 preserve it).
- Allocation failure and the inputs of "Stated exceptions of the external models".
- Any configuration other than the one below.

### Open items

- **Elicitation schema builders (X01–X75)**: translated (patch 08, 65 `ORIGINAL`, 10
  `patch-08`); specification and proofs pending. Draft upstream Aeneas issues (undefined float
  types, `keys().cloned().collect()`, `Cow<'static>` in a loop, generated `Map`/`Zip` iterator
  fields) are in `trusted/issues/aeneas-elicitation-schema.md`, not filed; its issue 6 (an
  internal error on the original `with_default` loop) is not reduced to a small reproducer.
- **CI has not run on GitHub** (nothing pushed yet). The three workflows (`lean-build.yml`,
  `aeneas-translation.yml`, `patched-tests.yml`) were checked locally only. Every `ORIGINAL`
  linkage (Phase 2, the 13 ORIGINAL `skill.rs` targets, N01, N08) rests on local runs of
  `scripts/check-original-linkage.sh` until its first CI run. Still to do after the push: show
  each CI check failing once on a throwaway branch, and reproduce the results from a fresh clone.
- **Project owner and budget (H5)**: not named. The spec owner is Hoang Le Truong.
- **Upstream reports of H7 and H8**: need the owner's go-ahead.
- **No shared verification lockfile**: `Cargo.lock` is not committed, so `aeneas-translation.yml`
  and `patched-tests.yml` each resolve their own. Pinned crates and sources are identical by
  check; unpinned transitive crates could differ. Committing a shared lockfile is a human
  decision.
- **Mathlib oleans** are not digest-checked (open scope question, see "Toolchain").
- **`external_code` in `scripts/lean_guard.py`** does not treat `«…»` identifiers as one unit, so a
  `«"»` can shift its view of literals in `trusted/` (layer (1) of the `rmcp`-namespace rule;
  layer (2) is authoritative). Fixing it is a follow-up.
- **Clippy with the widened features** fails on unused upstream helpers (`dead_code`); run clippy
  with `--features request-state`.
- **Candidate lemma** (not a signed-off statement): `∀ cap ≥ 1, Defs.Sse.observe cap (init m) h =
  historyOutcome cap m h`, checked only on finite cases in `Defs/Sse.lean`.
- **Linkage pre-check**: an expected outcome per text negative-control case (review finding a5-5)
  is deferred.
- **Accepted limits** listed under "What CI checks" (build-time code, `Specs` importing `Proofs`,
  no lock over the external models, unenforced `RmcpExternal` imports).
- `Rmcp` and `RmcpExternal` are not default targets (see "Layout").

## Translated configuration

`scripts/aeneas-translate.sh` fixes it:

```
--target x86_64-unknown-linux-gnu --no-default-features
--features request-state,server,client,client-side-sse,transport-streamable-http-server,transport-streamable-http-client,auth --lib
--config profile.dev.overflow-checks=true --config profile.dev.debug-assertions=true
```

The feature list is human decision **H1** (one configuration for all targets). Local runs on
macOS with the bundle's binaries need `DYLD_FALLBACK_LIBRARY_PATH=/usr/lib` (the bundle links
`libiconv` from a Nix store path); CI on Linux does not.

The two `--config` options are passed to every cargo call (also through Charon; command-line
`--config` has the highest precedence). Arithmetic is checked and panics on overflow, which is
what Aeneas models as failure (with `overflow-checks=false`, `i + 1#usize` would become
`Std.Usize.wrapping_add`). Nothing else may change the build, so the script refuses to run when:

- a variable that changes how cargo or rustc build is set: `RUSTFLAGS`, `RUSTC*`, `RUSTDOC*`,
  `CHARON_*`, `AENEAS_*`, every `CARGO_*` except `CARGO_HOME`, `CARGO_TARGET_DIR` (overridden),
  `CARGO_TERM_*`, `CARGO_NET_*`, `CARGO_HTTP_*`, `CARGO_INCREMENTAL`,
  `CARGO_REGISTRIES_CRATES_IO_PROTOCOL`, and every `RUSTUP_*` except `RUSTUP_TOOLCHAIN` (set by
  the script) and `RUSTUP_HOME`;
- the selected toolchain is not the pinned nightly: with `RUSTUP_TOOLCHAIN` set to the bundle's
  channel, `rustc -vV` (whose sysroot provides the `librustc_driver` that `charon-driver` loads)
  must report commit-hash `923c95cdf5ba65cea505aa2ea829f578e1506ed8`, commit-date `2026-09-16`,
  release `1.100.0-nightly`, and `charon toolchain-version` must print the bundle's channel;
- a `.cargo/config` or `.cargo/config.toml` exists in the source, the work copy or any ancestor
  of the work directory (`apply-patches.sh` never copies `.cargo/` and refuses any `.cargo` entry,
  symlinks included, in `.llbc/work/`). Cargo runs with an isolated `CARGO_HOME`
  (`.llbc/cargo-home`) holding only symlinks to the real registry and git caches, so
  `~/.cargo/config.toml` is not read;
- the workspace or `crates/rmcp` manifest has `[profile]`, `[patch]`, `[replace]` or
  `cargo-features`;
- a dependency of `rmcp` does not come from crates.io, or a pinned crate resolves to another
  version (see "Toolchain");
- `crates/rmcp/build.rs` does not have the pinned sha256, or its output is not empty (it prints no
  `cargo:` directive);
- after Aeneas, a target has no `def` in `Funs.lean`, a `_` glob of `start_from` does not match
  exactly one Rust item in `translation.json` (exception: `rmcp::model::skill::_::new` and
  `…::_::with_meta` must match exactly the `rust_name`s listed in `MULTI`, five and two methods),
  or a generated file contains `sorry`.

The Charon settings (`start_from`, `exclude`, `opaque`) are in `[package.metadata.charon]` of
`crates/rmcp/Cargo.toml`, each entry with its reason; the pinned Charon reads them itself. The
script fails if that table has any other key (Charon ignores a misspelt key and accepts keys such
as `include` or `rustc.flags` that widen the translation) or an empty list, or if the LLBC was
produced for another target. Charon `0.1.324` no longer records its options in the LLBC (lead
decision **N1**), so the script requires the preset `Aeneas` and
`runtime_checks.overflow_checks = true` in the LLBC and checks `translation.json` against the
lists: no item matches an `exclude` pattern; every function matching an `opaque` pattern has no
body and every local function without a body matches one; every type or global matching an
`opaque` pattern is emitted into an `*External_Template.lean` file and every local one emitted
there matches one; every `start_from` pattern matches an item.

## Toolchain

The toolchain pin is the Aeneas release tag in `lakefile.toml` (`rev`); the bundle components
follow from it. The Lean dependencies are pinned by commit in `lake-manifest.json`, and
`scripts/lean-guard.sh sources` fails unless the manifest lists exactly the recorded packages at
the recorded commits: Aeneas at `fb44cb400eb6bfe7dce97422ebe8fa748b7e4f9b` with `url`, `inputRev`
and `subDir` equal to the lakefile's `git`, `rev` and `subDir`; Mathlib at
`fc4f59e577feb1a4956671bc04ac18aaaf8cd842` (`v4.36.0`); and the eight packages Mathlib brings in
(`MANIFEST_PACKAGES` in `scripts/lean_guard.py`, updated in the same PR as the Aeneas rev); and
unless `lean-toolchain` is exactly `leanprover/lean4:v4.36.0` (`LEAN_TOOLCHAIN`, same rule).
Whether the Mathlib pin and its prebuilt oleans belong to the trusted base, and how they are
checked, is an open scope question for the human.

| Component | Version | Source |
|---|---|---|
| Aeneas | `nightly-2026.11.24-fb44cb4` (commit `fb44cb40`) | `rev` in `lakefile.toml` |
| Charon | `0.1.324` (commit `695be3d6`) | release bundle |
| Rust | `nightly-2026-09-17` | the bundle's `rust-toolchain` |
| Lean | `v4.36.0` (Mathlib `v4.36.0`) | the bundle's `backends/lean/lean-toolchain`, copied to `lean-toolchain` |

The release assets are checked against the sha256 values in `trusted/aeneas-bundle.sha256` (see
"Tools").

Dependency versions the external models rely on are pinned in `scripts/aeneas-translate.sh`
(`PINNED_DEPS`): `hmac 0.13.0`, `sha2 0.11.2`, `base64 0.23.1`, `digest 0.11.3`, `zeroize 1.9.2`,
`chrono 0.4.45`, `serde_json 1.0.154`, `serde_core 1.0.229` (traits translated opaque),
`percent-encoding 2.3.2`, `unicode-normalization 0.1.26`, `unicode-general-category 1.1.0` (the
skills models) and `url 2.5.9` (`url::host::Host` and `url::parser::ParseError` are translated
from its source; the `Url` models cite it). The script fails on a source other than crates.io or
another version of a pinned crate. The version that counts is the one `rmcp` itself uses: a
version reached, in the normal-edge tree of `rmcp` for the translated configuration
(`cargo tree`), through edges whose intermediate packages are all pinned crates (`rmcp` -> `hmac`
-> `digest` counts; `rmcp` -> `oauth2` -> `sha2` does not). It must be unique and equal the pin;
other versions used only by other crates (`oauth2` brings `sha2 0.10`, `digest 0.10`,
`base64 0.22`) are logged and allowed. `Cargo.lock` is git-ignored and `scripts/apply-patches.sh`
never copies it into `.llbc/work/`, so every run resolves the dependencies afresh (this needs the
crates.io index).

## Commands

From the repository root:

```bash
scripts/aeneas-install.sh      # bundle into .aeneas/<tag>/, Rust nightly, Lean toolchain
scripts/aeneas-translate.sh    # copy + patches (.llbc/work/), version check, Charon, Aeneas,
                               # target, glob and sorry checks, then formal/translation/
scripts/check-original-linkage.sh <scratch-dir>   # ORIGINAL linkage check
```

**The linkage check.** `scripts/check-original-linkage.sh` decides whether a record may say
`linkage: ORIGINAL`. It copies the tracked files into `<scratch-dir>` (outside the repository),
drops from the copy's Charon settings the start points that need a translation patch
(`rmcp::model::request_state{,_wire}`; K05–K07, K13–K16; N03, N05–N07, N10, N11 and the helpers
`with_base_url`, `proxy_host`, `allowed_addresses`; X29, X32, X33, X35–X38, X40, X74, X75) and the
opaque entries that exist only in the patched copy (`…::request_state_wire::prim`,
`…::request_state::_::now_ms`, `rmcp::model::skill::prim`, `rmcp::model::elicitation_schema::prim`,
`rmcp::transport::auth::metadata_resolver::{Lookup, prim}`), and translates it with
`aeneas-translate.sh` under `RMCP_NO_PATCHES=1` and `RMCP_TARGET_SET=phase2` (no patch; only
ORIGINAL targets checked; the translate script then also fails if a target in `PATCH04_TARGETS`,
`PATCH05_TARGETS` or `PATCH08_TARGETS` translates from the unmodified source, which would mean the
patch list disagrees with the call graph). These switches are refused unless the output goes to a
scratch directory outside the repository. Then:

- **(a) source pinning**: the `crates/rmcp/src` tree id, a digest of every other tracked file under
  `crates/` plus the root `Cargo.toml`, and a digest of `crates/rmcp/Cargo.toml` without its Charon
  table equal those of upstream `7caec76`, and `crates/`, `Cargo.toml` and `formal/translation/`
  are clean. A patch to the body of an `opaque` SDK item would be invisible, so the SDK-side opaque
  list must be exactly `AuthorizationManager` (a type, **H4**) and the SDK-side `exclude` list
  (without the `rmcp::model::request_state` entries) exactly `["serde"]`.
- **Step 4, text pre-check** (fail-closed, not the guarantee): every block of the unpatched
  translation equals the committed one up to the `Source:` field, and no committed-only declaration,
  nor a name Lean generates for a committed-only structure, inductive or class (`mk`, `rec`,
  `casesOn`, `noConfusion`, projections, …), shadows an identifier of an ORIGINAL block. The scan
  reads only the layout Aeneas emits and stops with "cannot be scanned" on anything else (unknown
  header commands, `where`/`let rec`, `extends`, interpolated strings, unusual structure layouts,
  non-ASCII letters, …). It does not read names resolved through the type of a term (field notation,
  leading dot) or other generated names; step 5 covers them. Since patch 08 (decisions XD2, XD5): an
  identifier directly before `:=` that is a binder (`let`, `have`, a named argument) or a
  structure-instance field is not read as a lookup; a standard-library trait-instance block (e.g.
  `String`'s `Eq`, `Ord`, `Clone`) may differ from the committed one only by fields that only the
  committed block sets, because other committed code uses more of that trait; and `P.m` is accepted
  when `P` is such a committed-only instance whose field is literally `m := P.m` (both readings name
  the same function).
- **Step 5, the elaborated comparison** (decides `ORIGINAL`). `scripts/linkage/make_env.py` builds
  two Lean environments the same way, `<scratch-dir>/env0` (unmodified-source translation) and
  `env1` (committed), each with its own generated External templates as externals
  (`scripts/linkage/repair_template.py` repairs the one known template printing bug, a fn item as
  `FnOnce` printed `A → R → A → R`, identically on both sides), reusing `formal/.lake/packages`.
  It fails unless `Aeneas.olean` and `Mathlib.olean` are already built there (run
  `lake exe cache get && lake build Aeneas` in `formal` first), so it writes only inside
  `<scratch-dir>`. `scripts/linkage/Dump.lean` and `compare_env.py` then require: every
  non-auxiliary constant of `Rmcp.Types`/`Rmcp.Funs` of env0 exists in env1 with the same module,
  kind, universe parameters, canonical type and canonical body (binder names, hygiene and metadata
  dropped; auxiliary constants and theorems replaced by their content); every external of env0
  has the same type in env1; instance and reducibility entries of env0 are unchanged (a new
  instance only a generated `SizeOf` (`<T>._sizeOf_inst`) or `Aeneas.Std.Discriminant`
  (`instDiscriminant…`) instance of a committed-only inductive, default priority, global, in
  `Rmcp.Types`); no persistent environment extension grows except those measured to grow with new
  declarations (`GROW_OK`, per module), so notation, macros, syntax, `export` and unification
  hints may not; every constant only env1 declares is under `rmcp.` or is such an instance. Step 5
  first runs `scripts/lean-guard.sh sources` and stops if it fails (it runs Lean on committed
  code); the CI stale-translation check is its other gate. Stated limits: (1) the hand-written
  `trusted/Rmcp/*.lean` (both sides use the templates); (2) attributes that committed code attaches
  to existing constants (`simp`, `inline`, `grind`, `elab_as_elim`; `implemented_by` is banned),
  which change proof automation or compilation hints, not what any constant is. Dependency
  resolution beyond `PINNED_DEPS` is shared by both sides, not pinned by the check. A widened
  standard-library instance (step 4) passes step 5 only if each committed-only field is
  definitionally equal, with the hand-written models, to the value the unmodified side gets, or
  is projected by no definition reachable from the unmodified-source translation or the models
  (`scripts/linkage/Widen.lean`); code outside both environments (`specs/`, `proofs/`,
  downstream users) is not inspected. The controls of the elicitation-stage rules run with
  `scripts/linkage/controls.py`.

The negative controls of steps 4 and 5 are archived (see "Archive"). `aeneas-translation.yml` runs
the check after the stale-translation check, with `formal/.lake/packages` cached under the key of
`lean-build.yml` (a stated residual risk; the cache-free `check` job of `lean-build.yml` is the
clean build).

**Scratch runs.** For a scratch source, set `RMCP_SOURCE_ROOT`, `RMCP_LLBC_DIR` and
`RMCP_TRANSLATION_DEST` together. Paths are canonicalised; the scripts refuse an output directory
inside the repository for a scratch source, one that contains the repository, or one that holds
anything but an earlier output (`Rmcp/`, `translation.json`). Because the work directory gets
`rsync --delete` and `rm -rf`, they refuse an `RMCP_LLBC_DIR` that is `/`, `$HOME`, the repository
or contains one of them, contains the source or lies inside it (except `<source>/.llbc`), has a
symlinked `work/`, `out/`, `cargo-home/` or `target/`, or is non-empty without the marker file
`.rmcp-llbc-dir`. Use a new or empty directory (`scripts/llbc-dir-guard.sh`).

In `formal/`:

```bash
lake exe cache get
../scripts/lean-guard.sh sources
set -o pipefail; lake build --wfail 2>&1 | tee .lake/build.log    # .lake/ is git-ignored
../scripts/lean-guard.sh build-log .lake/build.log
../scripts/lean-guard.sh axioms            # only after a successful lake build
../scripts/lean-guard.sh aeneas-archive
```

`../scripts/lean-guard.sh fresh` is for CI only (first step after checkout): it fails when
`formal/.lake` exists, which is normal locally.

Run `axioms` only after a `lake build` that succeeded: it audits the `.olean` files as they are.
It fails if a project module's source changed after its `.olean` was built (it compares the source
hash in Lake's `.trace` file), but an `.olean` left from an earlier build of a module the roots no
longer import is not audited, and a failed build can leave older `.olean` files.

**Build gate.** Every library sets `warningAsError`, and CI runs `lake build --wfail`, which fails
on any warning in this project's modules, including `sorry`, and on any warning replayed from a
dependency. The Aeneas library builds without warnings, so the build-log allowlist is empty (lead
decision **N10**).

A file could switch `warningAsError` off, hide messages (`#guard_msgs (drop all) in`) or use a
construct the kernel does not check, so `scripts/lean-guard.sh` (run by CI; checks in
`scripts/lean_guard.py`, Python 3.11 or later, and `scripts/lean-axiom-audit.lean`) also fails if:

- `lakefile.toml` is not exactly the five libraries (`Rmcp` in `translation/`, `RmcpExternal` in
  `trusted/`, `Defs` and `Specs` in `specs/`, `Proofs` in `proofs/`, fixed roots), each with
  exactly `name`, `srcDir`, `roots` and `leanOptions = { warningAsError = true }` (for `Rmcp`
  and `RmcpExternal` exactly `{ warningAsError = true, autoImplicit = false }`, human decisions
  XD3 and XD9, so that an undefined name in the generated translation or a trusted model is a
  build error); the package
  sets anything but `name`, `defaultTargets`, one `[[require]]` (aeneas) and the libraries; or
  `lakefile.lean` exists;
- `lake-manifest.json` or `lean-toolchain` differ from the recorded values (see "Toolchain"; elan
  runs whatever toolchain the file names, so CI checks it before installing elan); git tracks
  anything under a `.lake` directory (Lake loads a committed `lakefile.olean` as code); a `.lake`
  directory other than `formal/.lake` exists; a file is named with a case variant of `.lean`; or
  a symlink exists under `formal/`;
- a `.lean` file under `formal/` (except `.lake/` and `specs/Drafts/`; generated files included)
  contains, as a whole token (no letter, digit, `_`, `'`, `!` or `?` directly before or after):
  - `warningAsError`, `sorry`, `sorryAx`, `admit`, `native_decide`, `bv_decide`, `skipKernelTC`,
    `proofAsSorry`, `implemented_by`, `extern`, `unsafe`, `ofReduceBool`, `ofReduceNat`,
    `trustCompiler`; the `native` option of `decide`; any `debug.` option;
    `set_option linter.<name> false` (allowed in `translation/`; also caught with `«…»`-quoted
    name components); `axiom` outside `trusted/`;
  - in `translation/`, the option names `autoImplicit` and `relaxedAutoImplicit` at all (decision
    XD3); elsewhere, `set_option` of either with any value but `false` (quoted or not, the `… in`
    form included); in every file, a comment between `set_option` and its value;
  - a keyword or name that runs code during the build (`META_WORDS` in `scripts/lean_guard.py`:
    `run_cmd`, `run_tac`, `elab`, `macro`, `syntax`, `initialize`, `simproc`, `eval%`, `trace`,
    `addDecl`, `modifyEnv`, the metaprogramming monads `IO`, `CoreM`, `MetaM`, `TacticM`, … and
    `Elab`), derived from the pinned toolchain and packages: every syntax whose elaborator or macro
    reaches an evaluation primitive or builds such syntax;
  - any `#` command except `#check`, `#print` and `#guard_msgs`; `#guard_msgs` only in
    `specs/Specs.lean`, `specs/Specs/` and `proofs/Proofs/Internal/`, and only as `#guard_msgs in`
    followed by one `#print axioms <name>` line;
  - an attribute not in `ATTR_ALLOWED` (what Aeneas emits, and lemma tags, simp sets,
    reducibility, compiler and documentation flags such as `simp`, `instance`, `ext`, `grind`,
    `step`, `progress`, `inline`). Any other attribute can hand its declaration to code the build
    runs; extending the list is a reviewed change of `scripts/lean_guard.py`.

  `notation`, `infix`, `prefix`, `postfix` stay allowed (their macro only substitutes text checked
  by the same rules); `macro`/`syntax` are banned because a macro can build any syntax node without
  its keyword in the text. A custom tactic is written out inline; a reviewed tactic module would
  be a human decision.

  The check is textual: **comments and docstrings count**. Prose must avoid "axiom", "admit",
  "extern", "unsafe", "sorry", "syntax", "macro", "elab", "initialize", "IO", "simproc", "trace",
  "plausible"; write "assumption" or "trusted statement", "placeholder" or "unproved", "foreign",
  "unchecked", "grammar" or "notation", "set up" or "create", "input/output", "follow" or
  "record". One exception: a banned word in a generated file is excused only at a line pinned,
  with the word and the line's exact text, in the trusted file `trusted/translation-pins.txt`, and
  only while the file has the sha256 pinned there (one entry today: the T06 comparison with the
  MCP method name "initialize"). An edit together with an updated pin is caught only by the
  byte-for-byte regeneration in `aeneas-translation.yml` and by review, which reads each pinned
  line in context;
- a file under `trusted/` contains an `rmcp`-namespace identifier or `export` (see "Namespace rule
  for `trusted/`");
- the `lake build` log has any line with `warning:` or `error:` (the allowlist is empty), or no
  "Build completed successfully" line;
- (`axioms`) `.lake/build/lib/lean` holds modules outside `Rmcp`, `Defs`, `Proofs`, `Specs`; a
  project `.olean` is stale; a project constant reached from the default targets depends on an
  axiom other than `propext`, `Classical.choice`, `Quot.sound`, the axioms declared in the roots of
  `RmcpExternal` and locked native-code axioms (one order-independent walk over all constants,
  through types, values and whole inductive blocks: a superset of `#print axioms`, which can miss
  axioms reached through inductive/constructor cycles); a root of `RmcpExternal` declares a name
  in the namespace `rmcp` or adds an alias; or the kernel rejects a project constant when all are
  replayed (`Lean.Kernel.Environment.replay`, as `leanchecker` does; lead decision **N11**) onto
  the modules they import, which catches declarations added without a kernel check and altered
  `.olean` files. The audit runs no code from the `.olean` files (`loadExts := false`) and uses the
  toolchain's own `lean`, not `lake env`;
- (`axioms`, `trusted/axioms.lock`) a *used* trusted axiom is not locked, an entry names no
  declared axiom (stale), or the sha256 of a declared axiom's canonical statement (a structural
  text of its `Expr`) differs from its entry. *Used* (human decision 2026-11-23): reachable from a
  constant of a `Defs`, `Proofs` or `Specs` module. An unused, unlocked trusted axiom can therefore
  change or vanish without CI noticing; review of `trusted/` is the barrier there. The
  allowed-axiom check, replay and namespace check cover every project constant;
- (`axioms`, `trusted/native-axioms.lock`, human decision 2026-11-22) a native-code axiom (a
  `_native` name or `Lean.trustCompiler`) is reached that is not exactly the Aeneas `toStr` side
  condition `decide ("…".toByteArray.size ≤ Aeneas.Std.U32.max) = true` for one literal declared
  in `Rmcp.Types` or `Rmcp.Funs`, or a used one is not listed as `<name> <module>
  sha256:<hash>`, or an entry is stale or names another module. The
  lock is **empty** (lead decision **N5**: the `toStr` of `nightly-2026.11.24-fb44cb4` proves the
  side condition in the kernel); the rule applies to any native-code axiom that appears again;
- the Aeneas Lean-library archive does not match its committed sha256, the installed Aeneas build
  and the archive differ in any regular file (except `*.hash`, `*.trace`), or the library is built
  without an archive (unless `LEAN_GUARD_AENEAS_FROM_SOURCE=1` marks a build from source).

### What CI checks

Three workflows: `lean-build.yml` (build and audit, below); `aeneas-translation.yml`
(regenerates the translation with the pinned bundle and fails if the tree then differs from the
commit, which catches a Rust change, a patch, a Charon setting or an Aeneas bump committed
without regenerating `formal/translation/`, and any hand edit to it; then runs the linkage
check); `patched-tests.yml` (applies the patches with `aeneas-translate.sh --check-deps` and runs
the crate's library tests on the patched copy).

`lean-build.yml` has two jobs, because `lake build` elaborates the project, and elaboration can
run code that rewrites files of the runner (a `#eval` writing `scripts/lean-guard.sh`, say)
before a later step of the same job.

- `build`: checkout; `lean-guard.sh fresh` and `lean-guard.sh sources`, both plain Python before
  elan is installed and before any `lean` or `lake` command; pinned elan, and the Lean toolchain
  installed by its name (`leanprover/lean4:v4.36.0`, not read from the file);
  `lake exe cache get`, `lake build --wfail` into `.lake/build.log`, then `.lake/build` and the
  log are uploaded as one tar file. Only this job restores the `.lake/packages` cache;
  `.lake/build` is never cached.
- `check` (`needs: build`): a fresh runner and checkout, so the scripts come from git; `fresh` and
  `sources` again before elan; pinned elan and the named toolchain installed afresh; Mathlib cache
  and the Aeneas release archive fetched afresh (`lake exe cache get`, `lake build Aeneas`; no
  cache) and `aeneas-archive`; then the artifact is unpacked (`unpack-build`: only `build/` and
  `build.log`, no links, no `..`) and `build-log` and `axioms` run. No Lake command runs after the
  unpack, and the audit runs no code from the `.olean` files, so no project code runs in this job.

What job `check` detects in the artifact: a constant that depends on a disallowed axiom
(`sorryAx`, `Lean.ofReduceBool`, an axiom outside the `RmcpExternal` roots), a constant the kernel
rejects on replay, a lock violation, a module outside the project names, unexpected warnings or
errors in the build log, and an `.olean` older than its source by the trace hash (which a forger
can fake). It does not detect that the artifact was compiled from other sources: statements are
not re-elaborated in `check`, so a forged artifact can contain a different, kernel-correct project
(for example a theorem with the reviewed name and a weaker statement), as long as its
`Defs`/`Proofs`/`Specs` constants use no trusted axiom outside the lock.

Accepted residual limits (human decision, 2026-11-22):

- **Build-time code execution cannot be fully excluded by text bans.** The barriers are the ban
  list of `sources` and human review of every Lean file of every PR. Code run by `lake build` can
  forge the uploaded artifact, which `check` then accepts within the limits above. Known ways
  around the list: a command assembled from string pieces, parsed with
  `Parser.runParserCategory` and run with `elabCommand`; configuration terms and rule clauses of
  tactics that compile and run them (`linarith`, `nlinarith`, `aesop`, `saturate`/`forward`,
  Aeneas `step`/`progress`; a `linarith` discharger given as a `do` block ran during the build);
  gluing a banned token to a preceding literal or `)`; constructs in packages not yet seen.
- The locks cover axioms only. The external models are definitions, structures and `opaque`
  constants, invisible to `#print axioms` and the locks: a changed model is caught only by review
  of `trusted/` (a hash lock over `RmcpExternal` was offered and deferred). `axioms.lock` locks
  referenced constants by name only (moot while empty).
- `Specs` imports `Proofs`, so a global instance, notation, coercion or attribute in `proofs/` can
  change what a reviewed spec statement means (e.g.
  `instance (priority := high) : OfNat Nat 2 := ⟨1⟩` makes `theorem spec : (1 : Nat) = 2`
  provable, and every gate passes). An auditor must read `proofs/` for such declarations; no
  structural fix is decided.
- The Mathlib oleans come from Mathlib's cache server and are not digest-checked.
- A fake `rustc` that prints exactly the pinned `rustc -vV` lines is not caught by asking it.
- The `.olean` files are memory images that Lean maps without validating them; a crafted file
  could crash the audit or worse. The job has read-only permissions and no secrets, so the worst
  outcome is a wrong check result.

## Layout

| Path | Library | Contents |
|---|---|---|
| `README.md` | — | this file: results, configuration, commands, trusted base |
| `CONTRIBUTING.md` | — | how to contribute: workflow, style, PR format, review checklist |
| `translation/` | `Rmcp` | generated by Aeneas, never edited by hand |
| `trusted/` | `RmcpExternal` | `patches/` (translation patches 01, 03, 04, 05, 06, 07, 08 and the test-only patch 02); `Rmcp/` (hand-written external models: definitions, structures and `opaque` constants, no axiom); `evidence/README.md` (justification of each external model, its Rust sources and tests, and the map of upstream tests); `aeneas-bundle.sha256` (expected digests of the Aeneas release assets); `axioms.lock`, `native-axioms.lock` (both empty); `translation-pins.txt` |
| `specs/` | `Defs`, `Specs` | the top-level public API only (public functions called by no other verified function): `README.md` (index of every guarantee), the definitions used by public statements (`Defs/`), the public spec files (`Specs/`); `Drafts/` is in no library |
| `proofs/` | `Proofs` | proofs; laws of the external models (`Proofs/External/`); internal spec files for intermediate public functions (called by a top-level one), private, crate-internal and patch-only functions and the model laws (`Proofs/Internal/`, same format as `specs/Specs/`); definitions used only by them (`Proofs/Defs/`) |

`formal/specs/` holds only specifications of top-level public functions: `pub` in upstream rmcp
(human decision 2026-11-24) and called by no other verified function (human decision 2026-11-28).
Everything else, including the public functions that a top-level one calls, is specified in
`proofs/Proofs/Internal/`.

`Rmcp` and `RmcpExternal` are declared in `lakefile.toml` but are not default targets
(`lake build Rmcp RmcpExternal` builds them); `lake build` builds `Defs`, `Proofs` and `Specs`.
The proof modules import `Rmcp.Funs` (and so `Rmcp.FunsExternal`), so `lake build` builds both
and the `axioms` check audits both through that import. Making them default targets is a change
of `lakefile.toml` by the lead; nothing blocks it.

## Trusted base

An auditor reads all of `trusted/` (including `axioms.lock` and `native-axioms.lock`), `specs/`
(the public promises) and, for the guarantees about private functions, `proofs/Proofs/Internal/`
and `proofs/Proofs/Defs/`, the Charon settings in `crates/rmcp/Cargo.toml` and the configuration
in `scripts/aeneas-translate.sh`. While `Specs` imports `Proofs`, that is not sufficient: the
auditor also reads `proofs/` for instances, notation, coercions and attributes that change what a
spec statement means (see "What CI checks").

Summary: Charon, Aeneas and Lean (see "Tools"); the translated configuration; the translation
patches; the external models; the codec-state premises; the statements in `specs/` and
`proofs/Proofs/Internal/`; the exclusions. **0 trusted axioms, 0 native-code axioms, 26 `opaque`
constants.**

**Patches** (`trusted/patches/`, applied by `scripts/apply-patches.sh` with `patch -p1 -F 0` in
file-name order to the copy in `.llbc/work/` only; the repository's SDK `*.rs` files stay
upstream):

- `01-request-state-wire.patch` (rule D2): the `request_state_wire` refactor of
  `RequestStateCodec` and its byte-identity regression tests (non-test lines equal those of the
  original refactor commit `f8fb6a7`).
- `02-phase2-tests.patch` (test only, **H3**): 71 `#[cfg(test)]` boundary tests (34 for Phase 2
  boundary cases no upstream test covers, 12 for R09–R12 and R15, 13 for the paths of patch 06, 5
  for patch 07 and 7 for patch 08). It changes no translated item (the re-translation is
  byte-identical); 872 library tests pass on the patched copy.
- `03-request-state-public.patch` (+6/−2 lines of `request_state.rs`): `let ttl = options.ttl;`
  before the `match` in `seal_at` (matching on a field read through a shared reference stops
  Aeneas with "Unreachable"; the value is `Copy`), and an explicit `match` in place of
  `.map_err(RequestStateError::Deserialization)` in `open_json_with` (Aeneas: "Arrow types are not
  supported yet"). With it, and with `serde_core` moved from `exclude` to `opaque`, `seal`,
  `seal_with`, `seal_at`, `with_rs1_signing`, `with_rs1_fallback`, `open_json`, `open_json_with`
  and `new_with_keyring` translate with real bodies.
- `04-skill-public.patch` (hunks H1–H9 on `model/skill.rs`): the private module `prim` of twelve
  one-line wrappers of the original expressions (SHA-256, `str` patterns, percent-encoding, NFKC;
  opaque), and nine functions rewritten to use them or loops without an early return. Two
  patch-induced premises, unreachable in practice: H2/H4 collect the NFKC form into a
  `Vec<char>` (K13: `NfkcFits`, the length bound of `nfkc_spec`); `prim::split_slash`/
  `split_percent` (H5, H6) collect into a `Vec<String>`, panicking at `24 * parts > isize::MAX`
  (K13, K16: premise `hlen`; impossible on x86_64, where a `&str` has fewer than 2^57 bytes).
- `05-metadata-resolver.patch` (hunks H1–H9 on `transport/auth/metadata_resolver.rs` and
  `transport/auth.rs`): the module `prim` (`trim_end_dots`, `ends_with`, `contains`,
  `system_lookup`, `proxy_env_values`) and the newtype `Lookup(Arc<dyn Resolve>)`, both opaque;
  private helpers `with_base_url`, `proxy_host`, `allowed_addresses` split out of `with_lookup`,
  `with_proxy_hosts` and `resolve`; rewrites of `new`, `allowing_private_addresses`,
  `normalize_host`, `is_loopback_metadata_host`, and parameter renames in
  `literal_ip`/`allows_url`. The Charon `opaque` entry `url` is narrowed to `url::Url`.
- `06-auth-metadata.patch` (hunks prim, H1–H10 on `transport/auth.rs`): the opaque module
  `auth::prim` (string helpers, `str::trim`, the issuer-URL rewrite, and the four tracing events
  of `resolve_resource_metadata_url`, with their original `target`); the constant
  `CLOUD_METADATA_HOSTS` inlined; parameter renames (`url` shadows the crate in Lean); private
  helpers `is_allowed_disallowed_host`, `trim_root_slash`, `is_root_url`; and the checks of
  A08–A10 moved into helpers `check_authorization_response_issuer`,
  `check_authorization_metadata_issuer`, `check_resource_metadata_resource`. A08/A09 return a
  private `IssuerError` with the three `AuthError` variants they produce, because `AuthError`
  (a `Box<dyn Error>` field) cannot be translated; the one-line `validate_*` wrappers that map
  back to `AuthError`, or read `&self`, are not verified. `a != b` is written `!(a == b)` (with
  `#[allow(clippy::nonminimal_bool)]`), so that Aeneas does not regenerate every `PartialEq`
  instance.
- `07-mcp-headers.patch` (hunks prim, M1–M4 on `transport/common/mcp_headers.rs`): the opaque
  module `mcp_headers::prim` (the control/non-ASCII test, `str` prefix/suffix helpers, the
  `format!` of the Base64 sentinel, `BASE64_STANDARD` encode/decode, each the original expression)
  and rewrites of `requires_base64` (G01), `is_tchar` (G02, the quote written
  `c == char::from(b'\'')` to avoid an Aeneas printing defect), `encode_header_value` (G03) and
  `decode_header_value` (G04).
- `08-elicitation-schema.patch` (hunks prim, E1–E8 on `model/elicitation_schema.rs`, decision XD1):
  the opaque module `elicitation_schema::prim` (`titles_mismatch_message`, the original `format!`;
  `sorted_keys`, the original `keys().cloned().collect()`), error literals built with `.to_owned()`
  instead of `.to_string()`, the `for` loops with an early return rewritten with `iter().all`, and
  the `zip`/`map`/`collect` chain of the enum `build`s replaced by a translated helper
  `const_titles`. It changes X29, X32, X33, X35–X38, X40, X74 and X75; the other 65 elicitation
  targets are `ORIGINAL`. Not observable in returned values: `ElicitationSchemaBuilder::build`
  computes the key list before its check (one more allocation on the error path; in the model the
  list is `collectVec`, so the error path too needs `24 * len ≤ isize::MAX`, true of every Rust
  map), and the `one_of`/`any_of` vectors may get another capacity (visible only through
  `Vec::capacity`; capacity is not modelled).

Each patch header explains every hunk: the error it avoids and why the computed values are
unchanged. Patches 03–08 add and change no test; patch 02 holds the boundary tests of patches 06,
07 and 08.

**Charon settings** (`[package.metadata.charon]` of `crates/rmcp/Cargo.toml`). Opaque (signature
kept, contract given by a model): `rmcp::model::request_state_wire::prim` (HMAC and base64 `Engine`
types), `rmcp::model::skill::prim`, `rmcp::model::elicitation_schema::prim`,
`rmcp::transport::auth::metadata_resolver::{prim, Lookup}`,
`rmcp::model::request_state::_::now_ms` (system clock), the type
`rmcp::transport::auth::AuthorizationManager` (H4; it appears in no generated file), and the
external crates `zeroize`, `base64`, `hmac`, `sha2`, `thiserror`, `chrono`, `serde_json`,
`serde_core` (signatures and trait declarations), `http`, `tokio`, `tokio_util`, `tracing`,
`tracing_core`, `futures`, `futures_util`, `futures_core`, `bytes`, `sse_stream`, `hyper`,
`tower_service`, `uuid`, `schemars`, `pin_project_lite`, `tokio_stream`, `http_body`,
`http_body_util`, `rand`, `async_trait`, `pastey`, `oauth2`, `reqwest` and the type `url::Url`.
Excluded: crate `serde` and the functions under "Not covered".

**Translation pin.** `trusted/translation-pins.txt` records the sha256 of
`translation/Rmcp/Funs.lean` and the one line where `lean-guard.sh sources` excuses a
metaprogramming word (see "Commands"). The guard cannot see lexical context, so a pin updated
together with an edited `Funs.lean` excuses whatever stands at the pinned line; a legitimate
re-translation updates it in a reviewed PR.

**Codec-state premises.** `specs/Defs/CodecState.lean` defines `CodecValid` (keyring clauses;
single-key codecs unconstrained; pairwise distinct key ids), `CodecFallbacksKnown` (every rs1
fallback id is a key id) and `FallbacksKnown`. They are premises, not axioms: E09, E11 and the rs1
round trips assume `CodecFallbacksKnown`, E09a `FallbacksKnown`, E10 and rs2 nothing.

**External models** (`trusted/Rmcp/FunsExternal.lean`, `TypesExternal.lean`; sources and tests
per model in [`trusted/evidence/README.md`](trusted/evidence/README.md)). Each external type is a
`structure` (or an abstract type over an `opaque` carrier), each external function a definition
with the generated name and signature (keeping the template's `@[rust_type]`/`@[rust_fun]`
attribute where it has one). They declare **no axiom** (human decision 2026-11-23). What a model
cannot compute is one of 26 `opaque` constants, which add no axiom:

| Area | Models | `opaque` constants |
|---|---|---|
| Request state (Phase 1) | HMAC-SHA256 (`prim.hmac_sha256`, `_verify`, always succeed), Base64url without padding (`ExtModel.b64`, `b64Decode`, strict), standard library (`Option`, `Result`, `str`, `String`, `Clone`, `Hash`, `RandomState`, `DefaultHasher`, `HashMap` as an association list, `Duration`, `FromUtf8Error`), `zeroize`, the clock `now_ms`, `serde_json::Error` | `hmacSha256`, `sipHash13`, `nowMs`, `SerdeJsonErrorImplCarrier : NonemptyType` (`SerdeJsonErrorImpl` is an abstract `def` over it) |
| Phase 2 | strings, `Arc`, `Option`, `Result`, slices, ranges, `MaybeUninit`; `i64::from_str`, `ParseIntError` (all six `IntErrorKind`s); `Ipv4Addr` (4 octets), `Ipv6Addr` (8 segments) | `SerdeJsonValue` (only moved) |
| Patch 03 | 14 functions (`Duration::as_millis`, `str::to_owned`, `HashMap::{contains_key, is_empty, new, entry}`, `VacantEntry::insert`, `Hash for str`, `Borrow<str>`/`PartialEq<str>` for `String`, `slice::Iter::any`, `Iterator::any`, `serde_json::from_slice`, `Error::source`); types `OccupiedEntry`, `VacantEntry` | `randomState`, `serdeJsonFromSlice` |
| Patch 04 | the 12 `skill::prim` wrappers; 28 `core`/`alloc`/`std`/`serde_json`/`unicode-general-category` functions; types `array::IntoIter`, `str::Bytes`, `HashSet` (element list), `serde_json::Map` (the `BTreeMap` entries ascending by key) | `sha256`, `nfkc`, `generalCategory` |
| Patch 05 | the 5 `metadata_resolver::prim` functions, `url::Url::{parse, host, host_str}`, 8 `core`/`alloc` functions; structures `SocketAddrV4`, `SocketAddrV6`; abstract `url::Url`, `Lookup` | `UrlCarrier`, `LookupCarrier : NonemptyType`, `urlParse`, `urlHost`, `urlHostStr`, `systemLookup`, `proxyEnvValues` |
| Patch 06 | the `auth::prim` functions (exact byte models; `trim` as Unicode `White_Space`; the log events `ok ()`), `url::Url::{scheme, path, fragment, join, port_or_known_default, clone, eq}`, `Option::zip`, `str::eq_ignore_ascii_case` | `urlScheme`, `urlPath`, `urlFragment`, `urlJoin`, `urlSerialization`, `urlPort`, `issuerUrl` |
| Patch 07 | the 8 `mcp_headers::prim` functions (the control test byte-level on every string; standard padded Base64 as the reviewed URL-safe `b64`/`b64Decode` with the alphabet renamed, decoder with Rust's buffer-size guard), `char::is_ascii_alphanumeric`, `slice::last`, `Option::copied` | none |
| Patch 08 | the 2 `elicitation_schema::prim` functions; `BTreeMap` (entries ascending by key, distinct keys), its `Default` and `insert` (linear walk with the caller's `Ord` in Rust's comparison orientation, the stored key kept on `Equal`); `Ord`/`PartialOrd` for `String` (byte order, `ExtModel.bytesCmp`); `Default` for `Vec`; `slice::Iter::all`; `<str as Debug>::fmt` (total, see below) | none |
| Floats (XD3) | root types `F64`, `F32`, which the translation names but no target creates or inspects | `F64Carrier`, `F32Carrier : NonemptyType` |

`Borrow::borrow` (blanket), `Option::ok_or`, `Result::map_err` and `Vec::is_empty` are defined in
the Aeneas library and belong to the Aeneas trust item (lead decision **N8**). The model citations
of `core`/`alloc` were re-checked against nightly-2026-09-17 (lead decision **N9**). The laws of
the models are proved in `proofs/Proofs/External/` and restated in
`proofs/Proofs/Internal/External.lean`. The placeholder values of `sha256`, `nfkc` and
`generalCategory` (32 zero bytes, the identity, `Unassigned`) are what compiled evaluation
returns, so evaluating or differentially testing anything that reaches them is meaningless. What
an auditor trusts is that each definition describes its Rust function, with the exceptions below
and in its docstring.

### Stated exceptions of the external models

The complete list of behaviours the external models do not capture. For these inputs a statement
may promise a result where Rust panics or behaves otherwise.

- **Size convention.** Inputs of `2^61` bytes or more are not modelled: SHA-256's `u64` bit-length
  counter (`sha2-0.11.2/src/block_api.rs` line 66) overflows for a message of at least
  `2^61 − 64` bytes or an HMAC key of at least `2^61` bytes (K05–K07 and the compositions that hash
  are not covered there), and a `Vec` above `isize::MAX` (the x86_64 address space is at most
  `2^57` bytes).
- **Allocation failure** is not modelled: `ok` from a `String`/`Vec` model means "returns, or
  aborts or panics for memory reasons". `HashSet::with_capacity` does not model hashbrown's
  capacity-overflow panic.
- **Clock.** `Utc::now` is opaque (`nowMs`); it panics if the clock is before 1970 or outside
  chrono's range, which is not modelled.
- **`Arc`**: the model's `PartialEq` has no pointer-equality fast path (the only instance used is
  `str`, where the result is the same).
- **`Ipv6Addr`** is stored as eight segments instead of sixteen octets.
- **`MaybeUninit`** partial initialisation is not modelled.
- **`Str`** may hold non-UTF-8 bytes in the model; `push_str` of such bytes is `fail undef`, and
  `to_ascii_lowercase` fails on them (`to_ascii_lowercase_eq_fail`); so does the `format!` model
  `mcp_headers::prim::wrap_sentinel` (patch 07).
- **`HashMap::get`, `contains_key`, `entry`** assume `Hash` and `Eq` agree and do not fail (only
  `String` keys with `str`/`String` queries occur).
- **`BTreeMap::insert`** (patch 08) assumes the entries are sorted by key with distinct keys and
  that `Ord` is total and does not fail (only `String` keys occur, for which
  `btreeInsert_stringOrd_eq_ok` shows it equals the reviewed `mapInsert`). The `BTreeMap` type
  itself does not carry the sortedness invariant, so statements about a map the caller supplies
  assume it.
- **`<str as Debug>::fmt`** (patch 08) is total, not exact (it writes nothing); it is reached only
  through `Result::expect` in `build_unchecked`, whose Aeneas model never calls it.
- **`elicitation_schema::prim::sorted_keys`** is `collectVec`, which fails when
  `24 * len > isize::MAX`; no Rust map is that large.
- **`F64`, `F32`** (decision XD3) are opaque carrier types: no float value is modelled.
- **`serde_json::from_slice`**: a `Deserialize` impl that panics, aborts or does not terminate, or
  that is non-deterministic or has side effects (global or thread-local state, a random number
  generator), is not modelled.
- **`<ParseIntError as Debug>::fmt`** is a total, not exact, model: `Ok(())` and the formatter
  unchanged (`core::fmt::Formatter` is opaque in the Aeneas library; its only caller is an
  `expect` whose panic path two checked hexadecimal digits never take).
- **Default `Iterator::all`** is the `next` loop; an iterator that overrides `try_fold` is not
  modelled (no generated definition calls one).
- **`HashSet`** stores `randomState`; its iteration order (and so the random source) is not
  modelled, and statements do not depend on element order (K13, K16).
- **`serde_json::Map`** is the `BTreeMap` without the `preserve_order` feature (K09 order clauses).
- **`url::Url::{parse, host, host_str}`** are assumed to return and not to panic; so are
  `Url::join` and the setters inside `auth::prim::issuer_url` (patch 06). Exception for the setters of
  `issuer_url`: for a discovery URL of more than `u32::MAX` bytes with no query and no fragment
  (which `Url::parse` accepts), they can panic (`to_u32(..).unwrap()`, url-2.5.9 `src/lib.rs`
  1768); A09 statements take a premise bounding the URL (decision AD7). Exception for
  `Url::join`: with debug assertions on (the translated configuration), it can panic at
  url-2.5.9 `src/parser.rs` 1304 for a `file:` base whose last path segment is a normalized
  Windows drive letter, joined with an input whose first segment is `..` or a percent-encoded
  double dot; A07 statements assume the base URL's scheme is `http` or `https` (decision AD8).
- **Tracing events** (`auth::prim` log functions, patch 06) are `ok ()`: the logging side effect
  is not modelled.
- **Caller code**: caller conversions or closures with side effects outside their state are not
  covered (K04, K05, K08–K10; key (I) of `specs/README.md` for R04–R06, R11, R12, R15).
- **Patch-induced premises** of K13/K16 (`NfkcFits`, `hlen`), under "Patches" above.

None of these changes a result of the translated targets within the premises of their statements.

### Review rules

These rules bound what a statement may say about the `opaque` constants. They are checked by
review; other files cite them by name.

- **The clock rule.** `nowMs` is one constant, so every reader of the clock is pure in the model.
  No statement mentions `rmcp.model.request_state.RequestStateCodec.now_ms`, `…open`,
  `…open_with`, `…open_json`, `…open_json_with`, `…seal` or `…seal_with` (a variable named
  `now_ms`, such as the time parameter of E01, is not covered); opening is specified through
  `open_at` and sealing through `seal_at` (or its `Defs` model `sealAt`), with an explicit time.
  Exceptions (human decisions 2026-11-24/25): only the spec theorems of `open`, `open_with`,
  `open_json`, `open_json_with`, `seal`, `seal_with`, their `Theorems.*` restatements and the
  corollaries `open_with_spec_of_length_le`, `seal_with_spec_of_length_le`,
  `seal_spec_of_length_le` (and restatements) may name these functions and `ExtModel.nowMs`, and
  only with these postconditions:
  - `open`/`open_with`: `resultBytes result = openAt … ExtModel.nowMs.val`;
  - `open_json`/`open_json_with`: if `openAt … ExtModel.nowMs.val` is an error, the result is that
    error unchanged; otherwise the `ExtModel.serdeJsonFromSlice` outcome for the opened payload,
    with `Ok value ↦ Ok value` and `Err error ↦ Err (Deserialization error)`;
  - `seal`/`seal_with`: `sealAt … ExtModel.nowMs.val = some (ExtModel.utf8 result)`, where
    `sealAt` (`Defs.CodecState`) models the private `seal_at`; no statement equates `seal_with`
    with the translated `seal_at`.

  Their docstrings state the one-reading caveat and the inherited exceptions. Besides these, only
  `model.request_state.RequestStateCodec.now_ms_spec` (`result = ExtModel.nowMs`) names `now_ms`
  and `nowMs`. No statement has a premise or conclusion about the value of `nowMs`, and none
  relates two clock readings. R10a and R10b use explicit times.
- **`randomState`.** No statement has a premise or conclusion about its value or about the
  `hash_builder` of a map built by `HashMap::new`, and none states or relies on the equality (or
  inequality) of maps, or codecs containing them, built by distinct `HashMap::new` calls (e.g. two
  results of `new_with_keyring`): in Rust their keys differ (`std/src/hash/random.rs` lines
  71–75), and the `hash_builder` is unobservable through the modelled API.
- **`serdeJsonFromSlice`.** A statement may only say that the result of
  `open_json`/`open_json_with` is this outcome for the opened payload, mapped as the Rust code
  maps it; no statement relates two calls of `open_json`/`open_json_with` or
  `serde_json::from_slice`.
- **`sha256`, `nfkc`, `generalCategory`** (human decision 2026-11-25: their laws are premises).
  They appear in conclusions only unopened. A fact about them enters a statement only as an
  explicit premise true of the real function on every input it quantifies over (source cited),
  never as an axiom; a premise false of the real function is a review defect. `sha256`: only
  (in)equalities of digests of the statement's specific inputs, no universal law, never
  injectivity. `nfkc`: the NFKC-length domain (`4 * (ExtModel.nfkc cs).length ≤ maxStringBytes`
  for the statement's `cs`) and UAX #15 facts about the specific input (ASCII input is its own
  NFKC form, idempotence); no premise equating the NFKC forms of two inputs unless the Rust code
  tests that. `generalCategory`: facts about specific or ASCII characters matching
  `UnicodeData.txt`, or a cited Unicode stability guarantee. Each premise is either a **law** in
  implication form (e.g. ASCII-only `cs` → `nfkc cs = cs`) or a **domain restriction** (an
  unconditional fact about the statement's own input), declared as such in the docstring and the
  "Assumptions" column of `specs/README.md`. A fact from UAX #15, FIPS 180-4 or `UnicodeData.txt`
  also cites evidence that the pinned crate conforms on those inputs (NormalizationTest
  conformance of `unicode-normalization 0.1.26`, or a Rust vector of the pinned crate).
- **`HashSet` order.** No statement depends on the order of the `elements` list; `serde_json::Map`
  entries are sorted by key, and statements may rely on that.
- **Rule T4: the clock rule extended to the environment** (`proxyEnvValues`, human decision
  2026-11-25). No statement has a premise or conclusion about the value of
  `ExtModel.proxyEnvValues` or relates two environment readings. A statement may name
  `ExtModel.proxyEnvValues`, `transport.auth.metadata_resolver.prim.proxy_env_values` or
  `transport.auth.metadata_resolver.MetadataAddressResolver.new` only to say that `new` passes the
  values read to `with_proxy_hosts` (so that it holds for every environment), besides the model's
  own spec `prim.proxy_env_values_spec`. It may also state a fact about `new` that does not depend
  on the proxy environment (e.g. `base_ip`, `base_classes`, `lookup` equal those of
  `with_base_url u` with the lookup `ExtModel.systemLookup`), proved for every environment.
  - **P1** (extension of T4): for `new u = ok r`, with no premise on `proxyEnvValues`, a statement
    may conclude (1) that `r.unfiltered_hosts` (as bytes) equals
    `ExtModel.proxyEnvValues.val.filterMap (fun p => Defs.MetadataResolver.proxyHost
    (Defs.utf8Bytes p))` (`proxyHost` is defined in `proofs/Proofs/Defs/MetadataResolver.lean`);
    (2) that every unfiltered host of `new`'s result is a normalized host; (3) production security
    theorems about resolvers built by `new` (e.g. a filtered host's returned addresses are Public
    for a non-localhost domain base).
  - **R1**: for `new u = ok r`, statements `host ∈ r.unfiltered_hosts ↔ Defs.utf8Bytes host ∈
    ExtModel.proxyEnvValues.val.filterMap (Defs.MetadataResolver.proxyHost ∘ Defs.utf8Bytes)` and
    premises `host ∉ r.unfiltered_hosts` in production theorems count as restatements of P1.
  - **T1**: premises `Defs.utf8Bytes host ∈ ExtModel.proxyEnvValues.val.filterMap
    (Defs.MetadataResolver.proxyHost ∘ Defs.utf8Bytes)` (the host is a configured proxy host; used
    by `MetadataAddressResolver.allowed_addresses_eq_ok_some_of_new_eq_ok_of_mem_proxyHosts`) also
    count as restatements of P1.
- **`urlParse`, `urlHost`, `urlHostStr`.** They appear in conclusions only unopened; a fact about
  them (such as the agreement of `host` and `host_str`, or the host of a given URL string) enters a
  statement only as an explicit premise true of `url 2.5.9` on the inputs it quantifies over.
- **UTF-8 premise.** A statement may assume that a `Str` is valid UTF-8 (the Rust `&str`
  invariant) (i) only as the premise `ExtModel.IsUtf8 s.val` (`ExtModel.IsUtf8 l := ∃ t : String,
  l = ExtModel.utf8 t`, a definition in `trusted/Rmcp/FunsExternal.lean`; nothing asserts it), and
  (ii) only for (a) a `&str` argument of the function the statement is about, or a `&str` carried
  by an argument (such as the domain `d` of `host : Host<&str>` of
  `AuthorizationManager::is_loopback_metadata_host`, `host = url.host.Host.Domain d`), and (b) the
  hosts the opaque `url` functions return (`ExtModel.IsUtf8 d.val` for `ExtModel.urlHost u = some
  (url.host.Host.Domain d)`, `ExtModel.IsUtf8 h.val` for `ExtModel.urlHostStr u = some h`). That a
  `Str` computed from such values is UTF-8 is proved (`isUtf8_dropTrailingDots`,
  `isUtf8_map_asciiLowercase` in `Proofs.External.MetadataResolver`).
  Approved exception (spec owner, 2026-11-27): G04 `decode_header_value` assumes the conditional
  form `Defs.McpHeaders.sentinelInner? value.val = none → ExtModel.IsUtf8 value.val` (UTF-8 only on
  the non-sentinel path, where it is needed), which is weaker than `ExtModel.IsUtf8 value.val` and
  shown exact by `Theorems.mcp_headers.decode_header_value_fail_undef`.
- `systemLookup` is only stored; no rule is needed.
- **The float rule** (decision XD3). No statement inspects, compares or constructs a value of `F64`
  or `F32` (the number fields of `NumberSchema` and `Annotations.priority`); they are opaque
  carriers, and the translated targets only move them.

### Namespace rule for `trusted/`

Names in the namespace `rmcp` are banned in `trusted/`: the generated code works inside
`namespace rmcp` and names the root-level externals and the Aeneas library functions unqualified,
so a name `rmcp.<x>` from `trusted/` would silently take precedence. Two layers. (1)
`lean-guard.sh sources`, on every file under `trusted/`: after comments, string and character
literals are blanked, any identifier whose first component is `rmcp` (also after `_root_.`, and
quoted `«rmcp»`) fails, and so does the keyword `export`; the only exception is a line that is
exactly `open rmcp`, which `FunsExternal.lean` keeps from the Aeneas template because its
signatures name trait structures of `Rmcp.Types` and which declares nothing. This layer is a
best-effort lexer (it does not skip `«…»` identifiers; see "Open items"). (2) `lean-guard.sh
axioms`, on the build output (authoritative): a constant of a root of `RmcpExternal` whose name
(private prefix removed) starts with `rmcp`, including auxiliary ones, or any alias added by such
a module, fails. Not enforced: a shadowing `rmcp.<x>` declared in another project module that a
trusted root imports passes both layers (`RmcpExternal` should import only `Aeneas` and
`Rmcp.Types`, which its roots do today), and global `notation`/`infix` or a high-priority
`instance` in `trusted/` can redirect generated code without any `rmcp` name. Reviewers of
`trusted/` check imports, notation and instances by hand.

### Human decisions cited elsewhere

| ID | Decision |
|---|---|
| D2 | The `request_state_wire` refactor is translation patch 01 on upstream, not a change of the SDK source; Phase 1 linkage is `patch-01`. |
| H1 | One translated configuration with the widened feature list. |
| H2 | Aeneas `toStr` native-code axioms allowed when locked (none remain since the Aeneas upgrade). |
| H3 | Boundary tests from upstream tests; a test-only patch 02 for uncovered cases. |
| H4 | `opaque` entry for the type `rmcp::transport::auth::AuthorizationManager`. |
| H5 | Project owner and budget: **open**. |
| H6 | The T05/T06 method lists are the union of the method names in the official MCP `schema.ts` of the five known versions; core protocol only (extensions out of scope). |
| H7 | T05/T06 are stated as "in the core list and not in `codeOmits`"; the gap is a bug. |
| H8 | A01–A03: blocking all of `64:ff9b:1::/48` is intended; `240.0.0.0/4` not blocked is a bug; other special-purpose ranges were a scope note, now partly recorded as H11. |
| H9–H16 | Bugs recorded in the A04–A10 specification cycle (2026-11-27), see "Bugs found"; H9 to be reported privately before publication. |
| H17–H18 | Bugs recorded in the G01–G04 specification cycle (2026-11-27), see "Bugs found"; low severity, may be public. |
| T4, P1, R1, T1 | The `proxyEnvValues` rules under "Review rules". |
| AD1–AD8 | Translation patch 06 (`auth.rs` A04–A10, 2026-11-26 and 2026-11-27): the `check_*` helpers and the private `IssuerError` mirror are the verified targets, the `validate_*` wrappers unverified glue, A04 linkage `patch-06` (AD1); the moved tracing events keep `target: "rmcp::transport::auth"` (AD2); `#[allow(clippy::nonminimal_bool)]` for `!(a == b)` (AD3); seven new `opaque` constants, `str::trim` exact (AD4); boundary tests for the rewritten paths in patch 02 (AD5); `#[allow(clippy::enum_variant_names)]` on `IssuerError` (AD6); the `issuer_url` panic above `u32::MAX` bytes stays a stated exception, with a premise in A09 (AD7); the `Url::join` drive-letter panic likewise, with an `http`/`https` base premise in A07 (AD8). |
| GD1–GD3 | Translation patch 07 (`mcp_headers.rs` G01–G04, 2026-11-27): adopted as drafted with an opaque `prim` module and the quote workaround (GD1); exact models: byte-level control test, Base64 by alphabet renaming, buffer guard kept (GD2); boundary tests in patch 02 (GD3); lead decision: the identity model of `Option::copied` is allowed although its Lean type merges `Option<&T>` and `Option<T>` (its value does not depend on which). |
| XD1–XD8 | Translation patch 08 (`elicitation_schema.rs` X01–X75, 2026-11-28): adopted as drafted with an opaque `prim` module, the `BTreeMap`, `String` order, `Vec` default and `Iter::all` models, and `<str as Debug>::fmt` as a total model (XD1); the linkage check extended so that targets no hunk touches are `ORIGINAL` (XD2, XD5–XD7; see "The linkage check"); `F64`/`F32` as opaque carriers and `autoImplicit = false` for `Rmcp` (XD3); the suspected Rust bugs recorded as H19–H23 (XD4); 7 boundary tests in patch 02 (XD8). |
| XD9 | `autoImplicit = false` also for `RmcpExternal`, the hand-written trusted models (2026-11-28), raised by the final translation review. |
| G spec | G01–G04 specification cycle (2026-11-27 and 2026-11-28): the main specs keep the exact premises (E), (U), (D) with plain corollaries, and the conditional UTF-8 premise (U) of G04 is an approved exception to the UTF-8 rule (i) (see "Review rules"); CD1 (unneeded wrap accepted) is H17, CD7 (list characters bare) is H18; CD2 (bare value the encoder would wrap accepted) is a note, recorded in H17 as its second cause; CD3 (encoder stricter than RFC 9110) and CD4 (case-sensitive sentinel, strict padded standard Base64) are intended, matching SEP-2243; CD5 (error text "not valid Base64" for a non-UTF-8 payload) and CD6 (empty value sent as an empty header) are notes. Signed off 2026-11-28. |
| N1, N5, N8, N9, N10, N11 | Lead decisions of the Aeneas upgrade: Charon options checked through `translation.json` (N1), native lock empty (N5), four std models moved to the Aeneas library (N8), model citations re-checked (N9), `--wfail` build gate with an empty allowlist (N10), kernel replay with `Lean.Kernel.Environment.replay` (N11). |

### Tools

- Charon, Aeneas and charon-driver: the binaries of the Aeneas release bundle for the pinned tag,
  checked by `scripts/aeneas-install.sh` against `trusted/aeneas-bundle.sha256`; not built from
  source.
- Aeneas Lean library: its oleans are **prebuilt**. Lake downloads the release archive
  `lean-build-aeneas-<platform>.tar.gz` (the Aeneas package sets `preferReleaseBuild`) and does
  not check a digest; `scripts/lean-guard.sh aeneas-archive` checks it against
  `trusted/aeneas-bundle.sha256` and checks that the installed oleans are those of the archive.
  The library's sources are pinned by the commit in `lake-manifest.json`, but the oleans are not
  rebuilt from them.
- Mathlib: its oleans are **prebuilt**, fetched by `lake exe cache get`, and not rebuilt from
  source.
- Lean (`lean-toolchain`) and the Rust nightly come from elan and rustup; CI installs a pinned
  elan binary checked by sha256 and the Lean toolchain by its name
  (`.github/workflows/lean-build.yml`).
- The macOS release bundle links `/nix/store` libraries; locally use
  `DYLD_FALLBACK_LIBRARY_PATH=/usr/lib` (not reported upstream).

## Archive

The project's history documents were removed from the tree and remain in git history at commit
`9047c72`. Read one with `git show 9047c72:<path>` (or list a directory with
`git ls-tree -r --name-only 9047c72 <path>`):

- `docs/MCP_SDK_Verification_Master_Plan_EN.md`: the master plan;
- `formal/docs/STATUS.md`: the dated status log (per-step results, review rounds, decisions);
- `formal/docs/board.yaml`: the task board;
- `formal/docs/functions/*.yaml`: the per-function records (translation, spec, linkage, proof);
- `formal/trusted/evidence/differential/`: the differential checks (`rdiff`, `metadata-resolver`);
- `formal/trusted/evidence/linkage-scan/` and `formal/trusted/evidence/linkage-elab/`: the
  negative controls of the linkage check (steps 4 and 5);
- `formal/trusted/issues/`: issue notes (e.g. `aeneas-serde-ser-mutual-traits.md`, the R16–R17
  blocker).

The contributor guides formerly in `docs/` (`VERIFICATION.md`, `WORKFLOW_AND_PR_GUIDE.md`,
`STYLE_GUIDE.md`, `REVIEWER_GUIDE.md`, `AI_PR_REVIEW_QUESTIONS.md`) are merged into
[`CONTRIBUTING.md`](CONTRIBUTING.md); the originals are at the same commit. Citations elsewhere of
the form "plan Section N", "STATUS.md "…"", a step ID (S01–S37) or an evidence file "(git history
at 223ff12)" refer to these archived documents (older evidence is at commit `223ff12`).
