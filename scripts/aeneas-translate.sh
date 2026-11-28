#!/usr/bin/env bash
# Translate the verification targets of rmcp (Phase 1 request-state, Phase 2 protocol,
# transport and SSRF foundations) to Lean with the pinned Charon and Aeneas (plan Section 9,
# "Charon settings", and Section 15), into formal/translation/.
#
# What is translated is set in [package.metadata.charon] of crates/rmcp/Cargo.toml,
# which the pinned Charon reads itself; this script fixes only the configuration.
# It fails on:
#   - an environment variable that changes how cargo or rustc build the crate (RUSTFLAGS,
#     RUSTC*, RUSTDOC*, CARGO_* other than a short allowlist, RUSTUP_* other than
#     RUSTUP_TOOLCHAIN and RUSTUP_HOME, CHARON_*, AENEAS_*), see check_environment below;
#   - a selected toolchain whose `rustc -vV` is not the pinned nightly (RUSTC_VV_PINNED),
#     or a Charon whose toolchain-version is not the bundle's channel; see
#     check_environment below,
#   - a cargo configuration file (.cargo/config or .cargo/config.toml) in the work copy or in
#     any ancestor directory of it; cargo runs with an isolated CARGO_HOME that has no
#     configuration file (only the registry and git caches of the real one, by symlink),
#   - [profile], [patch], [replace] or cargo-features in the workspace or rmcp manifest,
#   - a build script of rmcp other than the pinned crates/rmcp/build.rs, or one that emits
#     anything (its output file must be empty),
#   - a scratch source (RMCP_SOURCE_ROOT) combined with an output directory inside the
#     repository, or an output directory that contains the repository (both canonicalised),
#   - a work directory (RMCP_LLBC_DIR) that is /, $HOME, the repository or contains one of
#     them, contains or lies inside the source (except <source>/.llbc), or exists, is not
#     empty and has no marker file .rmcp-llbc-dir from an earlier run (the repository's own
#     .llbc excepted); see scripts/llbc-dir-guard.sh,
#   - a pinned crate (PINNED_DEPS) whose version on rmcp's own edges, in the translated
#     configuration, differs from its pin (since S21; see the check below) (Cargo.lock is
#     git-ignored and never copied into .llbc/work/, so the dependencies are resolved
#     afresh on every run and this is what catches drift; plan Section 4), or any
#     dependency of rmcp in the translated configuration that does not come from the
#     crates.io registry (a path, git or other-registry source, e.g. through [patch]),
#   - a nonzero Charon exit, or an LLBC file flagged with errors,
#   - [package.metadata.charon] with a key other than start_from, hide_marker_traits,
#     exclude, opaque, or with an empty or missing start_from/exclude/opaque list,
#   - an LLBC whose preset is not Aeneas, without overflow checks, or for a target other than
#     TARGET_TRIPLE (Charon >= 0.1.324 no longer records its options in the LLBC; the lists of
#     [package.metadata.charon] are checked on the translation instead, below),
#   - a translated item (translation.json) that matches an exclude pattern, a function, type or
#     global that matches an opaque pattern but has a body, a local (rmcp) item without a body
#     that matches no opaque pattern, a start_from pattern that matches no translated item, or
#     a `Type::method` start_from pattern naming other than exactly one local function (or the
#     functions of its TYPE_MULTI entry) or also matching an item by its own path (the logged
#     count, 73 or 65 in the phase2 set, is a consistency check; these per-pattern checks are what
#     enforce it) (widening options cannot be set: the metadata keys are restricted as above, the
#     command line is fixed here and CHARON_* variables are refused),
#   - a nonzero Aeneas exit,
#   - a target missing from Funs.lean, a Phase 2 `_` glob matching other than exactly one
#     definition, or any `sorry` in the generated files.
# formal/translation/ is replaced only when every check passes.
#
# Usage:
#   scripts/aeneas-translate.sh            full run: patch, check, translate, check, install
#   scripts/aeneas-translate.sh --check D  only the output checks on an existing output
#                                          directory D (containing Rmcp/Funs.lean)
#   scripts/aeneas-translate.sh --check-deps
#                                          dependency checks only: the environment and
#                                          pinned-rustc checks, apply-patches.sh, the cargo
#                                          configuration and manifest refusals, the crates.io
#                                          source and PINNED_DEPS checks and the build.rs
#                                          digest, exactly as in a full run (same code); then
#                                          it stops before Charon, leaving the checked
#                                          resolution in <work>/Cargo.lock and the isolated
#                                          CARGO_HOME in <llbc>/cargo-home. It needs no Aeneas
#                                          bundle (the toolchain is RUSTUP_TOOLCHAIN, which
#                                          must be unset or the pinned nightly) and writes no
#                                          translation. patched-tests.yml runs it, then
#                                          `cargo test --locked` on that Cargo.lock.
# Every cargo call after the dependency check (cargo metadata, and cargo build through
# Charon) gets --locked, so the translation uses exactly the resolution that was checked.
# The overflow mode is fixed explicitly: every cargo call gets
#   --config profile.dev.overflow-checks=true --config profile.dev.debug-assertions=true
# (command-line --config has the highest precedence in cargo). Aeneas models overflow as
# failure, which is the meaning of the checked arithmetic of this mode.
#
# Environment (default to the repository; used for scratch runs):
#   RMCP_SOURCE_ROOT        workspace to translate (passed to apply-patches.sh)
#   RMCP_TARGET_SET         all (default) or phase2 (scripts/check-original-linkage.sh)
#   RMCP_NO_PATCHES         1: no translation patch applied (passed to apply-patches.sh)
#   RMCP_LLBC_DIR           work directory (default: <repo>/.llbc)
#   RMCP_TRANSLATION_DEST   output directory (default: <repo>/formal/translation);
#                           required when RMCP_SOURCE_ROOT is not the repository
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
LLBC="${RMCP_LLBC_DIR:-$ROOT/.llbc}"
DEST="${RMCP_TRANSLATION_DEST:-$ROOT/formal/translation}"
WORK="$LLBC/work"
CRATE_DIR="$WORK/crates/rmcp"

# The translated configuration. The proofs hold only for it (plan Section 1).
TARGET_TRIPLE="x86_64-unknown-linux-gnu"
# Fixed profile settings, passed to every cargo call (also through Charon).
CONFIG_ARGS=(--config 'profile.dev.overflow-checks=true' --config 'profile.dev.debug-assertions=true')
# Phase 2 widened the feature list (plan Section 15, human decision H1); the Phase 1 output is
# byte-identical under it.
FEATURES="request-state,server,client,client-side-sse,transport-streamable-http-server,transport-streamable-http-client,auth"
FEATURE_ARGS=(--target "$TARGET_TRIPLE" --no-default-features --features "$FEATURES")
CARGO_ARGS=("${CONFIG_ARGS[@]}" "${FEATURE_ARGS[@]}" --lib)

# crates/rmcp/build.rs (installs git hooks; prints no cargo: directive, so it adds no cfg,
# flag or environment variable to the build; in .llbc/work/ there is no .git, so it does
# nothing). Any change to it must be reviewed and this digest updated.
BUILD_RS_SHA256="31b905abf91292bab290271e993e347e06a1944e6305f742f69dbd01e6b89349"

# Dependency versions the external models of plan Section 4 rely on: hmac, sha2, base64
# resolved at S03; digest, zeroize, chrono, serde_json added at S08-S09, whose models cite their
# sources (formal/trusted/evidence/README.md); serde_core added with translation patch 03
# (2026-11-24: opaque crate whose trait declarations, e.g. DeserializeOwned, are translated).
PINNED_DEPS=(
  "hmac 0.13.0"
  "sha2 0.11.2"
  "base64 0.23.1"
  "digest 0.11.3"
  "zeroize 1.9.2"
  "chrono 0.4.45"
  "serde_json 1.0.154"
  "serde_core 1.0.229"
  # Skills targets K01-K20 (translation patch 04): the models of prim::{percent_encode_controls,
  # percent_decode_utf8, nfkc} and of get_general_category cite these crates; the enum
  # GeneralCategory is translated from unicode-general-category's source.
  "percent-encoding 2.3.2"
  "unicode-normalization 0.1.26"
  "unicode-general-category 1.1.0"
  # metadata_resolver.rs targets N01-N11 (translation patch 05): the enums url::host::Host and
  # url::parser::ParseError are translated from url's source; the models of Url::{parse, host,
  # host_str} cite this crate.
  "url 2.5.9"
)

# Lean names of the targets (plan Section 2): each needs a `def` in Funs.lean.
TARGETS=(
  model.request_state_wire.b64_len                          # W01
  model.request_state_wire.key_length_ok                    # W02
  model.request_state_wire.check_kid_len                    # W03
  model.request_state_wire.bytes_eq                         # W04
  model.request_state_wire.next_dot                         # W05
  model.request_state_wire.component_count                  # W06
  model.request_state_wire.version_of                       # W07
  model.request_state_wire.parse_rs1                        # W08
  model.request_state_wire.parse_rs2                        # W09
  model.request_state_wire.transcript_v1                    # W10
  model.request_state_wire.transcript_v2                    # W11
  model.request_state_wire.decode_expiry                    # W12
  model.request_state_wire.is_expired                       # W13
  model.request_state_wire.open_frame                       # W14
  model.request_state_wire.frame                            # W15
  model.request_state.RequestStateCodec.open_authenticated_body  # E01
  model.request_state.RequestStateCodec.b64_len             # E02
  model.request_state.RequestStateCodec.validate_key_length # E03
  model.request_state.RequestStateCodec.validate_config_kid # E04
  model.request_state.RequestStateCodec.seal_rs1            # E07
  model.request_state.RequestStateCodec.seal_rs2            # E08
  model.request_state.RequestStateCodec.open_rs1_at         # E09
  model.request_state.RequestStateCodec.rs1_fallbacks_verify  # E09a
  model.request_state.RequestStateCodec.open_rs2_at         # E10
  model.request_state.RequestStateCodec.open_at             # E11
  # Phase 2 (plan Section 16): existing upstream functions, unmodified.
  model.JsonRpcMessage.into_request                         # M01
  model.JsonRpcMessage.into_response                        # M02
  model.JsonRpcMessage.into_notification                    # M03
  model.JsonRpcMessage.into_error                           # M04
  model.JsonRpcMessage.into_result                          # M05
  model.NumberOrString.numeric_string_value                 # M06
  model.NumberOrString.matches_response_id                  # M07
  model.task.TaskStatus.is_terminal                         # M08
  model.SamplingContent.into_vec                            # M09
  model.SamplingContent.is_empty                            # M10
  model.SamplingContent.len                                 # M11
  model.SamplingContent.first                               # M12
  model.Reference.as_prompt_name                            # M13
  model.Reference.as_resource_uri                           # M14
  transport.common.client_side_sse.SseEventSizeLimiter.check_limit  # T01
  transport.common.client_side_sse.SseEventSizeLimiter.finish_line  # T02
  transport.common.client_side_sse.SseEventSizeLimiter.observe      # T03
  transport.async_rw.without_carriage_return                # T04
  transport.async_rw.is_standard_notification               # T05
  transport.async_rw.is_standard_method                     # T06
  transport.streamable_http_server.tower.default_port       # T07
  transport.streamable_http_server.tower.AllowedPort.matches  # T08
  transport.auth.AuthorizationManager.embedded_ipv4         # A01
  transport.auth.AuthorizationManager.is_disallowed_metadata_ipv4  # A02
  transport.auth.AuthorizationManager.is_disallowed_metadata_ipv6  # A03
  # Skills (SEP-2640), translation patch 04.
  model.skill.Resource.is_directory                         # K01
  model.skill.SkillsCapability.new                          # K02
  model.skill.SkillsCapability.with_directory_read          # K03
  model.skill.SkillResource.new                             # K04
  model.skill.SkillResource.from_bytes                      # K05
  model.skill.SkillResource.verify                          # K06
  model.skill.sha256_digest                                 # K07
  model.skill.SkillFrontmatter.new                          # K08
  model.skill.SkillFrontmatter.with_field                   # K09
  model.skill.Skill.new                                     # K10
  model.skill.Skill.with_meta                               # K11
  model.skill.Skill.name                                    # K12
  model.skill.Skill.validate                                # K13
  model.skill.is_valid_skill_name                           # K13 (private helper)
  model.skill.manifest_resource_key                         # K13 (private helper)
  model.skill.normalize_percent_encoding                    # K13 (private helper)
  model.skill.skill_name_from_uri                           # K14
  model.skill.is_sha256_digest                              # K15
  model.skill.validate_skills                               # K16
  model.skill.GetSkillResult.new                            # K17
  model.skill.GetSkillResult.with_ttl_ms                    # K18
  model.skill.GetSkillResult.with_cache_scope               # K19
  model.skill.GetSkillResult.with_meta                      # K20
  # metadata_resolver.rs (OAuth metadata address policy), translation patch 05.
  transport.auth.metadata_resolver.AddressClass.of          # N01
  transport.auth.metadata_resolver.MetadataAddressResolver.new  # N03 (patch 05)
  transport.auth.metadata_resolver.MetadataAddressResolver.with_base_url  # N04 (patch 05 helper)
  transport.auth.AuthorizationManager.is_loopback_metadata_host  # N04 (callee, patch 05)
  transport.auth.metadata_resolver.MetadataAddressResolver.with_proxy_hosts  # N05
  transport.auth.metadata_resolver.proxy_host               # N05 (patch 05 helper)
  transport.auth.metadata_resolver.MetadataAddressResolver.allowing_private_addresses  # N06
  transport.auth.metadata_resolver.MetadataAddressResolver.allows_url  # N07
  transport.auth.metadata_resolver.MetadataAddressResolver.is_allowed  # N08
  transport.auth.metadata_resolver.MetadataAddressResolver.allowed_addresses  # N09 (patch 05 helper)
  transport.auth.metadata_resolver.literal_ip               # N10
  transport.auth.metadata_resolver.normalize_host           # N11
  # auth.rs OAuth metadata URL and issuer checks, translation patch 06.
  transport.auth.AuthorizationManager.is_http_url           # A04
  transport.auth.AuthorizationManager.is_disallowed_metadata_host  # A05
  transport.auth.AuthorizationManager.is_disallowed_metadata_hostname  # A05 (callee)
  transport.auth.AuthorizationManager.is_allowed_metadata_url  # A06
  transport.auth.AuthorizationManager.is_allowed_disallowed_host  # A06 (patch 06 helper)
  transport.auth.AuthorizationManager.resolve_resource_metadata_url  # A07
  transport.auth.AuthorizationManager.is_same_origin        # A07 (callee)
  transport.auth.AuthorizationManager.check_authorization_response_issuer  # A08 (patch 06 helper)
  transport.auth.AuthorizationManager.check_authorization_metadata_issuer  # A09 (patch 06 helper)
  transport.auth.AuthorizationManager.expected_issuer_for_authorization_metadata_url  # A09 (callee)
  transport.auth.AuthorizationManager.issuer_identifiers_match  # A09 (callee)
  transport.auth.AuthorizationManager.trim_root_slash       # A09 (patch 06 helper)
  transport.auth.AuthorizationManager.is_root_url           # A09 (patch 06 helper)
  transport.auth.AuthorizationManager.check_resource_metadata_resource  # A10 (patch 06 helper)
  transport.auth.AuthorizationManager.is_resource_identifier_valid  # A10 (callee)
  # mcp_headers.rs header-value encoding, translation patch 07.
  transport.common.mcp_headers.requires_base64              # G01
  transport.common.mcp_headers.is_tchar                     # G02
  transport.common.mcp_headers.encode_header_value          # G03
  transport.common.mcp_headers.decode_header_value          # G04
  # elicitation_schema.rs builders (X01-X75); X29, X32, X33, X35-X38, X40, X74, X75 need patch 08.
  model.elicitation_schema.StringSchema.new  # X01
  model.elicitation_schema.StringSchema.email  # X02
  model.elicitation_schema.StringSchema.uri  # X03
  model.elicitation_schema.StringSchema.date  # X04
  model.elicitation_schema.StringSchema.date_time  # X05
  model.elicitation_schema.StringSchema.impl.title  # X06
  model.elicitation_schema.StringSchema.impl.description  # X07
  model.elicitation_schema.StringSchema.with_length  # X08
  model.elicitation_schema.StringSchema.length  # X09
  model.elicitation_schema.StringSchema.impl.min_length  # X10
  model.elicitation_schema.StringSchema.impl.max_length  # X11
  model.elicitation_schema.StringSchema.impl.format  # X12
  model.elicitation_schema.StringSchema.with_default  # X13
  model.elicitation_schema.IntegerSchema.new  # X14
  model.elicitation_schema.IntegerSchema.with_range  # X15
  model.elicitation_schema.IntegerSchema.range  # X16
  model.elicitation_schema.IntegerSchema.impl.minimum  # X17
  model.elicitation_schema.IntegerSchema.impl.maximum  # X18
  model.elicitation_schema.IntegerSchema.impl.title  # X19
  model.elicitation_schema.IntegerSchema.impl.description  # X20
  model.elicitation_schema.IntegerSchema.with_default  # X21
  model.elicitation_schema.BooleanSchema.new  # X22
  model.elicitation_schema.BooleanSchema.impl.title  # X23
  model.elicitation_schema.BooleanSchema.impl.description  # X24
  model.elicitation_schema.BooleanSchema.with_default  # X25
  model.elicitation_schema.EnumSchemaBuilder.impl.title  # X26
  model.elicitation_schema.EnumSchemaBuilder.impl.description  # X27
  model.elicitation_schema.EnumSchemaBuilder.untitled  # X28
  model.elicitation_schema.EnumSchemaBuilder.impl.enum_titles  # X29 (patch 08)
  model.elicitation_schema.EnumSchemaBuilderSingleSelect.new  # X30
  model.elicitation_schema.EnumSchemaBuilderSingleSelect.multiselect  # X31
  model.elicitation_schema.EnumSchemaBuilderSingleSelect.with_default  # X32 (patch 08)
  model.elicitation_schema.EnumSchemaBuilderSingleSelect.build  # X33 (patch 08)
  model.elicitation_schema.EnumSchemaBuilderMultiSelect.single_select  # X34
  model.elicitation_schema.EnumSchemaBuilderMultiSelect.with_default  # X35 (patch 08)
  model.elicitation_schema.EnumSchemaBuilderMultiSelect.min_items  # X36 (patch 08)
  model.elicitation_schema.EnumSchemaBuilderMultiSelect.max_items  # X37 (patch 08)
  model.elicitation_schema.EnumSchemaBuilderMultiSelect.build  # X38 (patch 08)
  model.elicitation_schema.EnumSchema.builder  # X39
  model.elicitation_schema.ElicitationSchema.new  # X40 (patch 08)
  model.elicitation_schema.ElicitationSchema.with_required  # X41
  model.elicitation_schema.ElicitationSchema.with_title  # X42
  model.elicitation_schema.ElicitationSchema.with_description  # X43
  model.elicitation_schema.ElicitationSchema.with_schema  # X44
  model.elicitation_schema.ElicitationSchema.builder  # X45
  model.elicitation_schema.ElicitationSchemaBuilder.new  # X46
  model.elicitation_schema.ElicitationSchemaBuilder.property  # X47
  model.elicitation_schema.ElicitationSchemaBuilder.required_property  # X48
  model.elicitation_schema.ElicitationSchemaBuilder.string_property  # X49
  model.elicitation_schema.ElicitationSchemaBuilder.required_string_property  # X50
  model.elicitation_schema.ElicitationSchemaBuilder.integer_property  # X51
  model.elicitation_schema.ElicitationSchemaBuilder.required_integer_property  # X52
  model.elicitation_schema.ElicitationSchemaBuilder.bool_property  # X53
  model.elicitation_schema.ElicitationSchemaBuilder.required_bool_property  # X54
  model.elicitation_schema.ElicitationSchemaBuilder.required_string  # X55
  model.elicitation_schema.ElicitationSchemaBuilder.optional_string  # X56
  model.elicitation_schema.ElicitationSchemaBuilder.required_email  # X57
  model.elicitation_schema.ElicitationSchemaBuilder.optional_email  # X58
  model.elicitation_schema.ElicitationSchemaBuilder.required_string_with  # X59
  model.elicitation_schema.ElicitationSchemaBuilder.optional_string_with  # X60
  model.elicitation_schema.ElicitationSchemaBuilder.required_integer  # X61
  model.elicitation_schema.ElicitationSchemaBuilder.optional_integer  # X62
  model.elicitation_schema.ElicitationSchemaBuilder.required_integer_with  # X63
  model.elicitation_schema.ElicitationSchemaBuilder.optional_integer_with  # X64
  model.elicitation_schema.ElicitationSchemaBuilder.required_bool  # X65
  model.elicitation_schema.ElicitationSchemaBuilder.optional_bool  # X66
  model.elicitation_schema.ElicitationSchemaBuilder.required_bool_with  # X67
  model.elicitation_schema.ElicitationSchemaBuilder.optional_bool_with  # X68
  model.elicitation_schema.ElicitationSchemaBuilder.required_enum_schema  # X69
  model.elicitation_schema.ElicitationSchemaBuilder.optional_enum_schema  # X70
  model.elicitation_schema.ElicitationSchemaBuilder.mark_required  # X71
  model.elicitation_schema.ElicitationSchemaBuilder.impl.title  # X72
  model.elicitation_schema.ElicitationSchemaBuilder.impl.description  # X73
  model.elicitation_schema.ElicitationSchemaBuilder.build  # X74 (patch 08)
  model.elicitation_schema.ElicitationSchemaBuilder.build_unchecked  # X75 (patch 08)
)


# RMCP_TARGET_SET=phase2 (used only by scripts/check-original-linkage.sh, plan Section 19): check
# only the targets of ORIGINAL linkage: the Phase 1 targets (model.request_state*) exist only with
# patch 01, and the skills targets K05-K07, K13-K16 (with the private helpers of K13) only with
# patch 04 (human decision 2026-11-25: the other 13 skills targets are ORIGINAL).
PATCH04_TARGETS=" model.skill.SkillResource.from_bytes model.skill.SkillResource.verify
  model.skill.sha256_digest model.skill.Skill.validate model.skill.is_valid_skill_name
  model.skill.manifest_resource_key model.skill.normalize_percent_encoding
  model.skill.skill_name_from_uri model.skill.is_sha256_digest model.skill.validate_skills "
# Likewise the metadata_resolver.rs targets and helpers that need translation patch 05 (N01 and
# N08 are ORIGINAL).
PATCH05_TARGETS=" transport.auth.metadata_resolver.MetadataAddressResolver.new
  transport.auth.metadata_resolver.MetadataAddressResolver.with_base_url
  transport.auth.AuthorizationManager.is_loopback_metadata_host
  transport.auth.metadata_resolver.MetadataAddressResolver.with_proxy_hosts
  transport.auth.metadata_resolver.proxy_host
  transport.auth.metadata_resolver.MetadataAddressResolver.allowing_private_addresses
  transport.auth.metadata_resolver.MetadataAddressResolver.allows_url
  transport.auth.metadata_resolver.MetadataAddressResolver.allowed_addresses
  transport.auth.metadata_resolver.literal_ip transport.auth.metadata_resolver.normalize_host "
# Likewise the auth.rs targets and helpers of translation patch 06 (all of A04-A10; is_same_origin
# translates unmodified but is reached only from A07).
PATCH06_TARGETS=" transport.auth.AuthorizationManager.is_http_url
  transport.auth.AuthorizationManager.is_disallowed_metadata_host
  transport.auth.AuthorizationManager.is_disallowed_metadata_hostname
  transport.auth.AuthorizationManager.is_allowed_metadata_url
  transport.auth.AuthorizationManager.is_allowed_disallowed_host
  transport.auth.AuthorizationManager.resolve_resource_metadata_url
  transport.auth.AuthorizationManager.is_same_origin
  transport.auth.AuthorizationManager.check_authorization_response_issuer
  transport.auth.AuthorizationManager.check_authorization_metadata_issuer
  transport.auth.AuthorizationManager.expected_issuer_for_authorization_metadata_url
  transport.auth.AuthorizationManager.issuer_identifiers_match
  transport.auth.AuthorizationManager.trim_root_slash transport.auth.AuthorizationManager.is_root_url
  transport.auth.AuthorizationManager.check_resource_metadata_resource
  transport.auth.AuthorizationManager.is_resource_identifier_valid "
# Likewise the mcp_headers.rs targets of translation patch 07 (all of G01-G04).
PATCH07_TARGETS=" transport.common.mcp_headers.requires_base64
  transport.common.mcp_headers.is_tchar transport.common.mcp_headers.encode_header_value
  transport.common.mcp_headers.decode_header_value "
# Likewise the elicitation_schema.rs targets of translation patch 08 (X29, X32, X33, X35-X38,
# X40, X74, X75; the other 65 of X01-X75 are ORIGINAL).
PATCH08_TARGETS=" model.elicitation_schema.EnumSchemaBuilder.impl.enum_titles
  model.elicitation_schema.EnumSchemaBuilderSingleSelect.with_default
  model.elicitation_schema.EnumSchemaBuilderSingleSelect.build
  model.elicitation_schema.EnumSchemaBuilderMultiSelect.with_default
  model.elicitation_schema.EnumSchemaBuilderMultiSelect.min_items
  model.elicitation_schema.EnumSchemaBuilderMultiSelect.max_items
  model.elicitation_schema.EnumSchemaBuilderMultiSelect.build
  model.elicitation_schema.ElicitationSchema.new
  model.elicitation_schema.ElicitationSchemaBuilder.build
  model.elicitation_schema.ElicitationSchemaBuilder.build_unchecked "
case "${RMCP_TARGET_SET:-all}" in
  all) ;;
  phase2)
    phase2=()
    for t in "${TARGETS[@]}"; do
      [[ "$t" == model.request_state* || "$(printf '%s' "$PATCH04_TARGETS$PATCH05_TARGETS$PATCH06_TARGETS$PATCH07_TARGETS$PATCH08_TARGETS" | tr '\n' ' ')" == *" $t "* ]] \
        || phase2+=("$t")
    done
    TARGETS=("${phase2[@]}")
    ;;
  *) printf '[aeneas-translate] error: RMCP_TARGET_SET must be all or phase2\n' >&2; exit 1 ;;
esac

log() { printf '[aeneas-translate] %s\n' "$*"; }
die() { printf '[aeneas-translate] error: %s\n' "$*" >&2; exit 1; }

# Output checks on a directory holding Rmcp/Funs.lean: every target has a `def`
# (a real body, not an opaque declaration), and no generated file mentions `sorry`.
check_output() {
  local out="$1" funs="$1/Rmcp/Funs.lean" missing=() t pat sorries f rc hit defs
  [[ -f "$funs" ]] || die "no Rmcp/Funs.lean in $out"
  # Aeneas puts a long name on the line after a bare `def` (e.g. allowing_private_addresses, N06);
  # join such a line with the next one before matching.
  defs="$(awk '/^(noncomputable )?(private )?def$/ { d = $0; getline; sub(/^[[:space:]]+/, ""); print d " " $0; next } { print }' "$funs")"
  for t in "${TARGETS[@]}"; do
    pat="^(noncomputable )?(private )?def ${t//./\\.}([[:space:]]|$)"
    grep -Eq "$pat" <<<"$defs" || missing+=("$t")
  done
  if [[ ${#missing[@]} -gt 0 ]]; then
    printf '[aeneas-translate] missing target: %s\n' "${missing[@]}" >&2
    die "${#missing[@]} target(s) have no definition in Funs.lean"
  fi
  # In the linkage run, the patch-04 targets must be absent: the unmodified copy starts from no
  # patch-04 entry point, so a patch-04 target that is still translated is reached from an ORIGINAL
  # target, i.e. PATCH04_TARGETS (here) and `patch04` (scripts/check-original-linkage.sh) disagree
  # with the call graph, and the ORIGINAL claim would silently skip checking it.
  if [[ "${RMCP_TARGET_SET:-all}" == phase2 ]]; then
    for t in $PATCH04_TARGETS $PATCH05_TARGETS $PATCH06_TARGETS $PATCH07_TARGETS $PATCH08_TARGETS; do
      pat="^(noncomputable )?(private )?def ${t//./\\.}([[:space:]]|$)"
      ! grep -Eq "$pat" <<<"$defs" || die "patch-04/05/06/07/08 target $t is translated from the unmodified source; update PATCH04_TARGETS/PATCH05_TARGETS/PATCH06_TARGETS/PATCH07_TARGETS/PATCH08_TARGETS and check-original-linkage.sh"
    done
  fi
  # Each `_` glob in [package.metadata.charon].start_from matches exactly one Rust item (plan
  # Section 15, rule 3): counted as distinct local `rust_name`s in translation.json that match the
  # glob segment by segment (`_` = any one path element; `{...}`, `<...>` nest). More than one means
  # the glob also caught another (e.g. a new upstream) item; none means it caught nothing.
  local manifest="${2:-$ROOT/crates/rmcp/Cargo.toml}" globs
  [[ -f "$out/translation.json" ]] || die "no translation.json in $out"
  globs="$(python3 -I - "$manifest" "$out/translation.json" <<'PY'
import json, sys, tomllib
manifest, tj = sys.argv[1], sys.argv[2]
start = tomllib.load(open(manifest, "rb"))["package"]["metadata"]["charon"]["start_from"]
def segs(path):
    out, depth, cur, i = [], 0, "", 0
    while i < len(path):
        c = path[i]
        if c == ">" and i > 0 and path[i - 1] == "-":
            pass  # the `->` of a fn type is no closing bracket
        elif c in "{<([":
            depth += 1
        elif c in "}>)]":
            depth -= 1
        if depth == 0 and path.startswith("::", i):
            out.append(cur); cur = ""; i += 2; continue
        cur += c; i += 1
    return out + [cur]
def canon(name):
    # An inherent impl written in another module than its type (`impl Resource` in
    # rmcp::model::skill) is named by Charon after the module of the impl, but its `start_from`
    # glob resolves through the module of the type: compare with the impl element moved under
    # the module of the type (identity when both modules agree). Only a braced element that is an rmcp
    # type path (`{rmcp::…}`) is moved; `{closure}`, `{[T]}`, `{dyn …}` and `{impl …}` elements are kept.
    s = segs(name)
    for i, e in enumerate(s):
        if e.startswith("{rmcp::"):
            ty = segs(e[1:-1].split("<", 1)[0])
            return "::".join(ty[:-1] + s[i:])
    return name
# `_` globs that are meant to reach several inherent methods of the same name, each listed.
MULTI = {
    "rmcp::model::skill::_::new": [
        "rmcp::model::skill::{rmcp::model::skill::GetSkillResult}::new",
        "rmcp::model::skill::{rmcp::model::skill::SkillFrontmatter}::new",
        "rmcp::model::skill::{rmcp::model::skill::SkillResource}::new",
        "rmcp::model::skill::{rmcp::model::skill::SkillsCapability}::new",
        "rmcp::model::skill::{rmcp::model::skill::Skill}::new"],
    "rmcp::model::skill::_::with_meta": [
        "rmcp::model::skill::{rmcp::model::skill::GetSkillResult}::with_meta",
        "rmcp::model::skill::{rmcp::model::skill::Skill}::with_meta"],
}
names = {f["rust_name"] for f in json.load(open(tj))["functions"] if f.get("is_local")}
bad = 0
for g in start:
    gs = segs(g)
    if "_" not in gs:
        continue
    hits = sorted(n for n in names
                  if len(segs(canon(n))) == len(gs)
                  and all(a == "_" or a == b for a, b in zip(gs, segs(canon(n)))))
    if g in MULTI:
        if hits != sorted(MULTI[g]):
            bad += 1
            print(f"BAD {g}: {hits}, expected {sorted(MULTI[g])}")
        else:
            print(f"OK {g}")
        continue
    if len(hits) != 1:
        bad += 1
        print(f"BAD {g}: {len(hits)} Rust items: {hits}")
    else:
        print(f"OK {g}")
sys.exit(1 if bad else 0)
PY
)" || { printf '%s\n' "$globs" | grep '^BAD' >&2; die "a Phase 2 \`_\` glob does not match exactly one Rust item (plan Section 15)"; }
  log "$(grep -c '^OK' <<<"$globs") \`_\` globs of start_from match their expected Rust items (exactly one each, or the MULTI list)"
  # grep: exit 0 = match, 1 = no match, anything else = error (not swallowed).
  sorries=""
  while IFS= read -r -d '' f; do
    rc=0
    hit="$(grep -HnwE 'sorry|sorryAx' "$f")" || rc=$?
    case $rc in
      0) sorries+="$hit"$'\n' ;;
      1) ;;
      *) die "grep failed on $f (exit $rc)" ;;
    esac
  done < <(find "$out" -name '*.lean' -print0)
  if [[ -n "$sorries" ]]; then
    printf '%s' "$sorries" >&2
    die "generated files contain sorry"
  fi
  log "all ${#TARGETS[@]} targets defined in Funs.lean; no sorry"
}

# The linkage-check switches are for a full scratch translation only (see below); in --check
# mode RMCP_TARGET_SET would silently shrink the target list.
if [[ "${1:-}" == "--check" && ( -n "${RMCP_NO_PATCHES:-}" || "${RMCP_TARGET_SET:-all}" != all ) ]]; then
  die "RMCP_NO_PATCHES / RMCP_TARGET_SET are for a full scratch translation only"
fi
MODE=full
if [[ "${1:-}" == "--check" ]]; then
  [[ $# -eq 2 ]] || die "usage: $0 --check <output-dir>"
  check_output "$2"
  exit 0
elif [[ "${1:-}" == "--check-deps" ]]; then
  [[ $# -eq 1 ]] || die "usage: $0 --check-deps"
  MODE=deps
else
  [[ $# -eq 0 ]] || die "usage: $0 [--check <output-dir> | --check-deps]"
fi

# Environment variables that change what cargo or rustc build are refused (not unset), so
# that a CI log shows why a run stopped. Allowed: CARGO_HOME (its configuration is not used,
# see below), CARGO_TARGET_DIR (overridden), CARGO_TERM_*, CARGO_NET_*, CARGO_HTTP_*,
# CARGO_INCREMENTAL, CARGO_REGISTRIES_CRATES_IO_PROTOCOL (how crates.io is fetched; the
# source check below still requires crates.io). Everything else named CARGO_* (config keys
# such as CARGO_PROFILE_*, CARGO_BUILD_*, CARGO_TARGET_<triple>_*, CARGO_ENCODED_RUSTFLAGS,
# CARGO_UNSTABLE_*), RUSTFLAGS, RUSTC* (RUSTC, RUSTC_WRAPPER, RUSTC_WORKSPACE_WRAPPER,
# RUSTC_BOOTSTRAP, ...), RUSTDOC*, CHARON_*, AENEAS_* and RUSTUP_* other than RUSTUP_TOOLCHAIN
# and RUSTUP_HOME (e.g. RUSTUP_DIST_SERVER, another source of toolchains) is refused.
# RUSTUP_TOOLCHAIN is overridden below. RUSTUP_HOME is allowed (container images set it);
# the toolchain it yields is checked below (`rustc -vV` must report the pinned nightly).
# RUST_LOG and RUST_BACKTRACE only affect logging.
check_environment() {
  local v bad=()
  while IFS= read -r v; do
    case "$v" in
      CARGO_HOME|CARGO_TARGET_DIR|CARGO_INCREMENTAL|CARGO_REGISTRIES_CRATES_IO_PROTOCOL) ;;
      CARGO_TERM_*|CARGO_NET_*|CARGO_HTTP_*) ;;
      RUSTUP_TOOLCHAIN|RUSTUP_HOME) ;;
      CARGO*|__CARGO*|RUSTFLAGS*|RUSTC*|RUSTDOC*|RUSTUP_*|CHARON_*|AENEAS_*) bad+=("$v") ;;
    esac
  done < <(compgen -e)
  if [[ ${#bad[@]} -gt 0 ]]; then
    printf '[aeneas-translate] refused environment variable: %s\n' "${bad[@]}" >&2
    die "unset the variable(s) above: they change how the crate is built (see check_environment)"
  fi
}
check_environment

# canon_path, within, check_llbc_dir.
# shellcheck source=scripts/llbc-dir-guard.sh
. "$ROOT/scripts/llbc-dir-guard.sh"

# The output directory is replaced with rsync --delete. It must never contain the
# repository (e.g. RMCP_TRANSLATION_DEST=<repo>/formal would delete formal/), and with a
# scratch source it must lie outside the repository, so that a scratch translation never
# overwrites formal/translation/ (paths canonicalised: symlinks, `.`, `..`).
# (--check-deps writes no output, so it skips these checks.)
ROOT_C="$(canon_path "$ROOT")"
if [[ "$MODE" == full ]]; then
  DEST_C="$(canon_path "$DEST")"
  REPO_DEST_C="$(canon_path "$ROOT/formal/translation")"
  within "$ROOT_C" "$DEST_C" && die "RMCP_TRANSLATION_DEST ($DEST_C) contains the repository"
  if [[ -n "${RMCP_SOURCE_ROOT:-}" && "$(canon_path "$RMCP_SOURCE_ROOT")" != "$ROOT_C" ]]; then
    within "$DEST_C" "$ROOT_C" \
      && die "RMCP_SOURCE_ROOT is not this repository; set RMCP_TRANSLATION_DEST to a scratch directory outside the repository (got $DEST_C)"
  elif [[ "$DEST_C" != "$REPO_DEST_C" ]] && within "$DEST_C" "$ROOT_C"; then
    die "RMCP_TRANSLATION_DEST ($DEST_C) is inside the repository but is not formal/translation"
  fi
fi
# The linkage-check switches (RMCP_NO_PATCHES, RMCP_TARGET_SET) only ever translate into a
# scratch directory outside the repository; never into formal/translation/.
if [[ -n "${RMCP_NO_PATCHES:-}" || "${RMCP_TARGET_SET:-all}" != all ]]; then
  [[ "$MODE" == full ]] || die "RMCP_NO_PATCHES / RMCP_TARGET_SET are for a full scratch translation only"
  within "$DEST_C" "$ROOT_C" \
    && die "RMCP_NO_PATCHES / RMCP_TARGET_SET need RMCP_TRANSLATION_DEST outside the repository (got $DEST_C)"
fi

# The work directory gets rsync --delete (work/) and rm -rf (out/, cargo-home/); see
# scripts/llbc-dir-guard.sh for what is refused. On success it holds the marker file.
LLBC="$(check_llbc_dir "$ROOT" "$LLBC" "${RMCP_SOURCE_ROOT:-$ROOT}")" || die "refused RMCP_LLBC_DIR (see above)"
export RMCP_LLBC_DIR="$LLBC"
WORK="$LLBC/work"
CRATE_DIR="$WORK/crates/rmcp"

# The pinned bundle (installed by aeneas-install.sh from the rev in formal/lakefile.toml).
# Every table header starts a new block and clears `name`/`rev` (same awk as aeneas-install.sh).
# --check-deps does not use the bundle: its channel is RUSTUP_TOOLCHAIN (default: the pinned
# nightly), checked against the same pin below.
if [[ "$MODE" == full ]]; then
  TAG="$(awk '
    /^[[:space:]]*\[/ { in_req = ($0 ~ /^[[:space:]]*\[\[require\]\]/); is_aeneas = 0; rev = ""; next }
    in_req && /^[[:space:]]*name[[:space:]]*=[[:space:]]*"aeneas"[[:space:]]*(#.*)?$/ { is_aeneas = 1 }
    in_req && /^[[:space:]]*rev[[:space:]]*=/ { rev = $0 }
    in_req && is_aeneas && rev != "" { sub(/^[^"]*"/, "", rev); sub(/".*$/, "", rev); print rev; exit }
  ' "$ROOT/formal/lakefile.toml")"
  BUNDLE="$ROOT/.aeneas/$TAG"
  [[ -n "$TAG" && -f "$BUNDLE/.installed" ]] || die "bundle ${TAG:-?} not installed; run scripts/aeneas-install.sh"
  CHARON="$BUNDLE/charon"
  AENEAS="$BUNDLE/aeneas"
  RUST_CHANNEL="$(sed -n 's/^channel[[:space:]]*=[[:space:]]*"\(.*\)"/\1/p' "$BUNDLE/rust-toolchain")"
  CHANNEL_FROM="bundle channel"
else
  RUST_CHANNEL="${RUSTUP_TOOLCHAIN:-nightly-2026-09-17}"
  CHANNEL_FROM="RUSTUP_TOOLCHAIN"
fi
export RUSTUP_TOOLCHAIN="$RUST_CHANNEL"
# The toolchain actually selected (RUSTUP_HOME may point at any rustup home): the `rustc` on
# PATH, which cargo runs and whose sysroot provides the librustc_driver that charon-driver
# loads, must report the pinned nightly; Charon must have been built for the same channel.
# RUSTC_VV_PINNED is the `rustc -vV` of nightly-2026-09-17 (commit date 2026-09-16); it
# changes with the Aeneas rev ("Pinned toolchain").
[[ "$RUST_CHANNEL" == "nightly-2026-09-17" ]] \
  || die "$CHANNEL_FROM $RUST_CHANNEL, but RUSTC_VV_PINNED is for nightly-2026-09-17 (update it with the Aeneas rev)"
RUSTC_VV_PINNED="commit-hash: 923c95cdf5ba65cea505aa2ea829f578e1506ed8 commit-date: 2026-09-16 release: 1.100.0-nightly"
command -v rustc >/dev/null 2>&1 || die "rustc not found"
rustc_vv="$(rustc -vV)" || die "rustc -vV failed for toolchain $RUST_CHANNEL${RUSTUP_HOME:+ (RUSTUP_HOME=$RUSTUP_HOME)}"
got_vv="$(awk -F': ' '$1 == "release" || $1 == "commit-hash" || $1 == "commit-date" { printf "%s%s: %s", (n++ ? " " : ""), $1, $2 }' <<<"$rustc_vv")"
[[ "$got_vv" == "$RUSTC_VV_PINNED" ]] \
  || die "the selected rustc reports '$got_vv', expected '$RUSTC_VV_PINNED' (toolchain $RUST_CHANNEL${RUSTUP_HOME:+, RUSTUP_HOME=$RUSTUP_HOME})"
export CARGO_TARGET_DIR="$LLBC/target"
command -v jq >/dev/null 2>&1 || die "jq not found"
if [[ "$MODE" == full ]]; then
  # The bundle's macOS binaries reference libiconv/zlib under /nix/store; the same
  # libraries exist in /usr/lib (see aeneas-install.sh).
  if [[ "$(uname -s)" == "Darwin" ]]; then
    export DYLD_FALLBACK_LIBRARY_PATH="/usr/lib${DYLD_FALLBACK_LIBRARY_PATH:+:$DYLD_FALLBACK_LIBRARY_PATH}"
  fi
  charon_tc="$("$CHARON" toolchain-version)" || die "charon toolchain-version failed"
  [[ "$charon_tc" == "$RUST_CHANNEL" ]] || die "charon was built for $charon_tc, the bundle pins $RUST_CHANNEL"
  log "aeneas $TAG, charon $("$CHARON" version), rust $RUST_CHANNEL (rustc $got_vv)"
else
  log "dependency check only (--check-deps), rust $RUST_CHANNEL (rustc $got_vv)"
fi

# 1. Fresh copy of the workspace with the translation patches applied (apply-patches.sh
# refuses a source with a .cargo/config* file and never copies .cargo/).
"$ROOT/scripts/apply-patches.sh"
cd "$CRATE_DIR"

# Cargo configuration. Cargo reads .cargo/config{,.toml} in the working directory and every
# ancestor, then $CARGO_HOME/config{,.toml}. Any such file in the work copy or an ancestor of
# the crate directory is refused; $CARGO_HOME is replaced by an isolated directory that
# holds only symlinks to the registry and git caches of the real one (no configuration, no
# credentials), so a ~/.cargo/config.toml is not read either.
cfg_hits="$(find "$WORK" -type d -name .cargo -print)"
[[ -z "$cfg_hits" ]] || die "cargo configuration directory in the work copy: $cfg_hits"
d="$(pwd -P)"
while :; do
  for f in "$d/.cargo/config" "$d/.cargo/config.toml"; do
    [[ ! -e "$f" ]] || die "cargo configuration file $f would apply to the translation; remove it or move the work directory (RMCP_LLBC_DIR)"
  done
  [[ "$d" != "/" ]] || break
  d="$(dirname "$d")"
done
REAL_CARGO_HOME="${CARGO_HOME:-$HOME/.cargo}"
ISO_CARGO_HOME="$LLBC/cargo-home"
rm -rf "$ISO_CARGO_HOME"
mkdir -p "$ISO_CARGO_HOME" "$REAL_CARGO_HOME/registry" "$REAL_CARGO_HOME/git"
ln -s "$REAL_CARGO_HOME/registry" "$ISO_CARGO_HOME/registry"
ln -s "$REAL_CARGO_HOME/git" "$ISO_CARGO_HOME/git"
export CARGO_HOME="$ISO_CARGO_HOME"
log "cargo: no configuration file in the work copy or its ancestors; isolated CARGO_HOME $ISO_CARGO_HOME"

# Manifests: no [profile] (it could change overflow-checks for rmcp through a package
# override), no [patch]/[replace] (dependency sources) and no cargo-features (unstable
# manifest keys such as profile rustflags), in the workspace and the rmcp manifest.
command -v python3 >/dev/null 2>&1 || die "python3 not found"
python3 -I -c '
import sys
if sys.version_info < (3, 11): sys.exit("python3 >= 3.11 needed (tomllib)")
import tomllib
bad = []
for path in sys.argv[1:]:
    with open(path, "rb") as f: m = tomllib.load(f)
    bad += [f"{path}: [{k}]" for k in ("profile", "patch", "replace", "cargo-features") if k in m]
if bad: sys.exit("refused manifest key(s): " + ", ".join(bad))
' "$WORK/Cargo.toml" "$CRATE_DIR/Cargo.toml" || die "manifest check failed"
log "manifests: no [profile], [patch], [replace] or cargo-features"

# 2. Dependencies, resolved for the translated configuration: every dependency of rmcp
# must come from crates.io (`cargo tree` prints a source only for a path, git or
# other-registry package), and the pinned crates must have the pinned versions. This
# `cargo tree` writes <work>/Cargo.lock (the copy has none); every later cargo call uses it
# with --locked.
[[ ! -e "$WORK/Cargo.lock" ]] || die "$WORK/Cargo.lock exists before resolution (apply-patches.sh never copies one)"
tree="$(cargo tree --color never "${CONFIG_ARGS[@]}" "${FEATURE_ARGS[@]}" -e normal --prefix none --format '{p}' \
  | sed -e 's/ (\*)$//' -e 's/ (proc-macro)$//' | sort -u)"
foreign="$(awk -v root="rmcp" '$1 != root && / \(/' <<<"$tree")"
if [[ -n "$foreign" ]]; then
  printf '%s\n' "$foreign" >&2
  die "dependencies not from crates.io (path, git or other registry)"
fi
# The same source check over build and dev dependencies too: cargo test (patched-tests.yml)
# also builds the dev-dependencies, so none of them may come from a path, git or other
# registry either (review of PR #9).
alltree="$(cargo tree --color never "${CONFIG_ARGS[@]}" "${FEATURE_ARGS[@]}" -e normal,build,dev --prefix none \
  --format '{p}' | sed -e 's/ (\*)$//' -e 's/ (proc-macro)$//' | sort -u)"
foreign="$(awk -v root="rmcp" '$1 != root && / \(/' <<<"$alltree")"
if [[ -n "$foreign" ]]; then
  printf '%s\n' "$foreign" >&2
  die "build or dev dependencies not from crates.io (path, git or other registry)"
fi
rootline="$(awk '$1 == "rmcp"' <<<"$tree")"
[[ "$rootline" == "rmcp v"*" ($(pwd -P))" ]] || die "unexpected rmcp package(s) in the tree: $rootline"
# Pinned versions are checked on rmcp's own edges (human decision 2026-11-23, S21), in the
# translated configuration: the graph is the normal-edge dependency tree of rmcp for
# FEATURE_ARGS (`cargo tree --prefix depth`, the configuration Charon builds; `cargo metadata` would
# give the workspace-unified graph, with features only other members enable). The version that
# counts is one rmcp reaches through edges whose intermediate packages are all pinned crates
# (rmcp -> hmac -> digest counts; rmcp -> oauth2 -> sha2 does not). Each pinned crate must have
# exactly one such version, equal to the pin (so it must be present). Other versions used only by
# other crates (the Phase 2 features bring oauth2 with sha2 0.10, digest 0.10, base64 0.22) are
# logged and allowed: no translated target calls them, and the models describe only the versions
# rmcp uses.
deptree="$(cargo tree --color never --locked "${CONFIG_ARGS[@]}" "${FEATURE_ARGS[@]}" -e normal \
  --prefix depth --format '{p}')" || die "cargo tree (depth) failed"
pin_report="$(PINS="${PINNED_DEPS[*]}" python3 -I -c '
import os, re, sys
words = os.environ["PINS"].split(" ")
pins = {words[i]: words[i + 1] for i in range(0, len(words), 2)}
line_rx = re.compile(r"^(\d+)(\S+) v(\S+)")
children, stack, root, allv = {}, [], None, {}
for line in sys.stdin.read().splitlines():
    m = line_rx.match(line)
    if not m:
        sys.exit("unparsed cargo tree line: " + line)
    depth, node = int(m.group(1)), (m.group(2), m.group(3))
    allv.setdefault(node[0], set()).add(node[1])
    del stack[depth:]
    if depth == 0:
        if root is not None or node[0] != "rmcp":
            sys.exit("unexpected root in cargo tree: " + line)
        root = node
    else:
        children.setdefault(stack[-1], set()).add(node)
    stack.append(node)
reach, todo = set(), [root]
while todo:
    for dep in children.get(todo.pop(), ()):
        if dep[0] in pins and dep not in reach:
            reach.add(dep)
            todo.append(dep)
ownv = {}
for name, ver in reach:
    ownv.setdefault(name, set()).add(ver)
bad, none, sep = 0, ["none"], ", "
for name, want in pins.items():
    own = sorted(ownv.get(name, ()))
    other = sorted(allv.get(name, set()) - set(own))
    if own != [want]:
        print(f"BAD {name} on rmcp edges resolves to {own or none}, pinned {want}")
        bad += 1
    else:
        print(f"OK {name} {want}" + (f" (other versions used only by other crates: {sep.join(other)})" if other else ""))
sys.exit(1 if bad else 0)
' <<<"$deptree")" || { printf '%s\n' "$pin_report" >&2; die "pinned dependency check failed"; }
while IFS= read -r line; do
  log "dependency ${line#OK } from crates.io (pinned, on rmcp's own edges)"
done <<<"$pin_report"

# 3. [package.metadata.charon], checked before Charon runs. It may hold only the four
# documented keys, and the three lists must be present and non-empty. The pinned
# Charon's TomlConfig ignores unknown keys (a misspelt key would be dropped silently)
# and also accepts keys that widen the translation (include, start_from_pub,
# extract_opaque_bodies, start_from_if_exists, start_from_attribute, rustc.flags);
# none of them is allowed here.
pkg="$(cargo metadata "${CONFIG_ARGS[@]}" --locked --format-version 1 --no-deps \
  | jq -c '[.packages[] | select(.name == "rmcp")] | if length == 1 then .[0] else error("rmcp package count \(length)") end')"
# Build script: exactly crates/rmcp/build.rs, with the pinned digest.
builds="$(jq -r '[.targets[] | select(.kind | index("custom-build")) | .src_path] | join(" ")' <<<"$pkg")"
[[ "$builds" == "$(pwd -P)/build.rs" || "$builds" == "$CRATE_DIR/build.rs" ]] \
  || die "rmcp build script(s) '$builds', expected crates/rmcp/build.rs"
if command -v sha256sum >/dev/null 2>&1; then got_sha="$(sha256sum build.rs | awk '{print $1}')"
else got_sha="$(shasum -a 256 build.rs | awk '{print $1}')"; fi
[[ "$got_sha" == "$BUILD_RS_SHA256" ]] \
  || die "crates/rmcp/build.rs has sha256 $got_sha, pinned $BUILD_RS_SHA256 (review it, then update BUILD_RS_SHA256)"
log "build script crates/rmcp/build.rs (pinned sha256)"
if [[ "$MODE" == deps ]]; then
  log "dependency checks passed; checked resolution in $WORK/Cargo.lock (use cargo --locked), CARGO_HOME $ISO_CARGO_HOME"
  exit 0
fi
meta="$(jq -c '.metadata.charon' <<<"$pkg")"
[[ "$meta" != "null" && -n "$meta" ]] || die "no [package.metadata.charon] in crates/rmcp/Cargo.toml"
extra="$(jq -c '(keys - ["start_from", "hide_marker_traits", "exclude", "opaque"])' <<<"$meta")"
[[ "$extra" == "[]" ]] || die "[package.metadata.charon] has unexpected key(s) $extra"
for key in start_from exclude opaque; do
  jq -e --arg k "$key" '(.[$k] | type) == "array" and (.[$k] | length) > 0 and all(.[$k][]; type == "string")' \
    <<<"$meta" >/dev/null || die "[package.metadata.charon].$key is missing, empty or not a list of strings"
done
jq -e '(.hide_marker_traits // true) | type == "boolean"' <<<"$meta" >/dev/null \
  || die "[package.metadata.charon].hide_marker_traits is not a boolean"

# 4. Charon. It reads [package.metadata.charon] from ./Cargo.toml.
mkdir -p "$LLBC"
LLBC_FILE="$LLBC/rmcp.llbc"
rm -f "$LLBC_FILE"
set +e
"$CHARON" cargo --preset=aeneas --dest-file "$LLBC_FILE" -- "${CARGO_ARGS[@]}" --locked
rc=$?
set -e
[[ $rc -eq 0 ]] || die "charon exited with $rc"
[[ "$(jq -r '.has_errors' "$LLBC_FILE")" == "false" ]] || die "charon reported errors in $LLBC_FILE"
# The build script ran for the target and printed nothing (no cfg, flag or env directive).
# Old cargo layout: build/rmcp-<hash>/output; the build-dir layout of cargo 1.100
# (nightly-2026-09-17): build/rmcp/<hash>/run/stdout.
outs=()
while IFS= read -r f; do outs+=("$f"); done \
  < <(find "$CARGO_TARGET_DIR/$TARGET_TRIPLE" \( -path '*/build/rmcp-*/output' -o -path '*/build/rmcp/*/run/stdout' \) -type f 2>/dev/null | sort)
[[ ${#outs[@]} -gt 0 ]] || die "no build-script output of rmcp under $CARGO_TARGET_DIR/$TARGET_TRIPLE"
for f in "${outs[@]}"; do
  [[ ! -s "$f" ]] || { cat "$f" >&2; die "rmcp build script emitted directives ($f)"; }
done

# Charon >= 0.1.324 no longer records its options in the LLBC (translated.options); it keeps only
# the preset and the runtime checks. Charon reads its options from [package.metadata.charon]
# (whose keys are restricted above to start_from, hide_marker_traits, exclude and opaque, so no
# widening option such as include, start_from_pub or extract_opaque_bodies can be set there),
# from the command line fixed by this script, and from no environment variable (CHARON_* is
# refused). That Charon applied the three lists is checked on the translated items after Aeneas
# (step 6, check_charon_settings, lead decision N1 of the Aeneas upgrade). Here: the preset and
# the overflow checks recorded in the LLBC ...
[[ "$(jq -r '.translated.preset' "$LLBC_FILE")" == "Aeneas" ]] \
  || die "LLBC preset is $(jq -c '.translated.preset' "$LLBC_FILE"), expected \"Aeneas\""
jq -e '.translated.runtime_checks.overflow_checks == true' "$LLBC_FILE" >/dev/null \
  || die "LLBC runtime_checks: overflow_checks is not true ($(jq -c '.translated.runtime_checks' "$LLBC_FILE"))"
# ... and for the fixed target only.
targets="$(jq -c '[.translated.target_information[].key]' "$LLBC_FILE")"
[[ "$targets" == "[\"$TARGET_TRIPLE\"]" ]] || die "LLBC target information is $targets, expected [\"$TARGET_TRIPLE\"]"
log "LLBC: preset Aeneas, overflow checks on, target $TARGET_TRIPLE"

# 5. Aeneas, into a scratch directory; formal/translation/ is replaced only on success.
OUT="$LLBC/out"
rm -rf "$OUT"
mkdir -p "$OUT"
set +e
"$AENEAS" -backend lean -split-files -emit-json -no-progress-bar \
  -dest "$OUT" -subdir Rmcp "$LLBC_FILE"
rc=$?
set -e
[[ $rc -eq 0 ]] || die "aeneas exited with $rc"

# 5b. Charon applied [package.metadata.charon] (lead decision N1): checked on every item of the
# translation, by its Rust name in translation.json (Aeneas's record of the LLBC items, in
# Charon's name-pattern syntax). A pattern matches a name with the same leading path elements
# (`_` matches any one element), i.e. the item itself and the items below it, as in Charon.
#  - exclude: no translated item matches an exclude pattern;
#  - opaque: every function matching an opaque pattern has no body (is_opaque), and every local
#    (rmcp) function without a body matches an opaque pattern (no body is silently dropped); the
#    same for types and globals, whose opacity is their file (an *External_Template.lean);
#  - start_from: every pattern matches at least one translated item; a `Type::method` pattern
#    (one that reaches items only through the type path of an inherent impl) names exactly one
#    local function, or exactly the functions listed in TYPE_MULTI (review finding TR9); every
#    `module::Type::method` pattern of start_from is such a pattern and no other is (TR16).
python3 -I - "$OUT/translation.json" "$meta" <<'PY' || die "Charon settings check on the translation failed"
import json, sys
meta = json.loads(sys.argv[2])
tr = json.load(open(sys.argv[1], encoding="utf-8"))
def elems(name):
    out, depth, cur, i = [], 0, "", 0
    while i < len(name):
        if name.startswith("::", i) and depth == 0:
            out.append(cur); cur = ""; i += 2; continue
        c = name[i]
        depth += (c in "{<[(") - (c in "}>])")
        cur += c; i += 1
    out.append(cur)
    return out
def matches(pat, name):
    p, n = elems(pat), elems(name)
    return len(n) >= len(p) and all(a == "_" or a == b for a, b in zip(p, n))
items = [(k, d) for k in ("functions", "types", "globals", "trait_decls", "trait_impls") for d in tr.get(k, [])]
errs = []
for d_kind, d in items:
    for pat in meta["exclude"]:
        if matches(pat, d["rust_name"]):
            errs.append(f"excluded by {pat!r} but translated: {d['rust_name']}")
for d in tr.get("functions", []):
    op = [p for p in meta["opaque"] if matches(p, d["rust_name"])]
    if op and not d.get("is_opaque"):
        errs.append(f"opaque by {op[0]!r} but has a body: {d['rust_name']}")
    if d.get("is_local") and d.get("is_opaque") and not op:
        errs.append(f"local function without a body, not in opaque: {d['rust_name']}")
# Types and globals carry no is_opaque: Aeneas emits an opaque one into an External template.
for k in ("types", "globals"):
    for d in tr.get(k, []):
        op = [p for p in meta["opaque"] if matches(p, d["rust_name"])]
        ext = d.get("lean_file", "").endswith("External_Template.lean")
        if op and not ext:
            errs.append(f"opaque by {op[0]!r} but translated with a definition: {d['rust_name']}")
        if d.get("is_local") and ext and not op:
            errs.append(f"local {k[:-1]} emitted as external, not in opaque: {d['rust_name']}")
def canon(name):
    # As in check_output: an inherent impl written in another module than its type.
    e = elems(name)
    for i, x in enumerate(e):
        if x.startswith("{rmcp::"):
            ty = elems(x[1:-1].split("<", 1)[0])
            return "::".join(ty[:-1] + e[i:])
    return name
def typepath(name):
    # `module::Type::method` form of an inherent method `module::{module::Type<..>}::method` of a
    # local type (Charon resolves such a start_from pattern through the type; X01-X75).
    e = elems(name)
    for i, x in enumerate(e):
        if x.startswith("{rmcp::"):
            return "::".join(elems(x[1:-1].split("<", 1)[0]) + e[i + 1:])
    return name
for pat in meta["start_from"]:
    if not any(matches(pat, d["rust_name"]) or matches(pat, canon(d["rust_name"]))
               or matches(pat, typepath(d["rust_name"])) for _, d in items):
        errs.append(f"start_from {pat!r} matches no translated item")
# `Type::method` start points (review finding TR9): a pattern that reaches items only through
# typepath must name exactly the expected inherent methods: as many local functions whose typepath
# is the pattern itself as listed in TYPE_MULTI (the methods of the same name of several
# instantiations of a generic type, each listed), else exactly one. Another count means the
# pattern also caught another (e.g. a new upstream) method, or none.
es = "rmcp::model::elicitation_schema::"
TYPE_MULTI = {
    es + "EnumSchemaBuilder::with_default": [
        es + "{" + es + "EnumSchemaBuilder<" + es + "SingleSelect>}::with_default",
        es + "{" + es + "EnumSchemaBuilder<" + es + "MultiSelect>}::with_default"],
    es + "EnumSchemaBuilder::build": [
        es + "{" + es + "EnumSchemaBuilder<" + es + "SingleSelect>}::build",
        es + "{" + es + "EnumSchemaBuilder<" + es + "MultiSelect>}::build"],
}
# The `Type::method` patterns are derived from the start_from list itself (review finding TR16):
# no `_` element and a path element before the last that starts with an upper-case ASCII letter
# (a Rust type; modules are lower case). Each must reach items only through typepath: a pattern
# that also matches an item name directly (e.g. a new upstream item of that path) is an error, not
# silently skipped, and so is a pattern that reaches items through typepath only without having
# this form. The count is logged (73 for the full set, 65 for the phase2 set).
def is_type_method(pat):
    e = elems(pat)
    return "_" not in e and len(e) >= 3 and e[-2][:1].isascii() and e[-2][:1].isupper()
expected_type = [p for p in meta["start_from"] if is_type_method(p)]
local_fns = sorted({d["rust_name"] for d in tr.get("functions", []) if d.get("is_local")})
n_type = 0
for pat in meta["start_from"]:
    direct = any(matches(pat, d["rust_name"]) or matches(pat, canon(d["rust_name"])) for _, d in items)
    if direct and is_type_method(pat):
        errs.append(f"start_from {pat!r} (Type::method) also matches a translated item by its own path")
        continue
    if direct:
        continue
    if not any(matches(pat, typepath(d["rust_name"])) for _, d in items):
        continue   # reported above
    if not is_type_method(pat):
        errs.append(f"start_from {pat!r} reaches items only through the type of an inherent impl "
                    "but is not of the `module::Type::method` form")
        continue
    n_type += 1
    hits = [n for n in local_fns if elems(typepath(n)) == elems(pat) and n != pat]
    if pat in TYPE_MULTI:
        if hits != sorted(TYPE_MULTI[pat]):
            errs.append(f"start_from {pat!r} (Type::method) matches {hits}, expected {sorted(TYPE_MULTI[pat])}")
    elif len(hits) != 1:
        errs.append(f"start_from {pat!r} (Type::method) matches {len(hits)} local functions, expected exactly one: {hits}")
for pat in TYPE_MULTI:
    if pat in meta["start_from"] and not any(matches(pat, typepath(d["rust_name"])) for _, d in items):
        errs.append(f"start_from {pat!r} is listed in TYPE_MULTI but matches no translated item")
if n_type != len(expected_type):
    errs.append(f"{n_type} start_from patterns reach their methods through the type path, expected "
                f"{len(expected_type)} (the `module::Type::method` patterns of start_from)")
for e in errs:
    print(f"[aeneas-translate] {e}", file=sys.stderr)
if errs:
    sys.exit(1)
print(f"[aeneas-translate] charon settings applied: {len(items)} translated items; none excluded, "
      f"opaque items bodiless, {len(meta['start_from'])} start_from patterns matched; {n_type} of "
      f"{len(expected_type)} Type::method patterns of start_from name their expected methods "
      "(exactly one each, or the TYPE_MULTI list)")
PY

# 6. Output checks, then install. rsync --delete replaces DEST; as a second guard (besides the
# path checks at the top) DEST must be absent, empty, or hold only an earlier output
# (Rmcp/ and translation.json), so that a wrong path can never delete anything else.
check_output "$OUT" "$CRATE_DIR/Cargo.toml"
if [[ -d "$DEST_C" ]]; then
  others="$(find "$DEST_C" -mindepth 1 -maxdepth 1 ! -name Rmcp ! -name translation.json -print | head -5)"
  [[ -z "$others" ]] || die "RMCP_TRANSLATION_DEST ($DEST_C) holds files that are not a translation output: $others"
elif [[ -e "$DEST_C" ]]; then
  die "RMCP_TRANSLATION_DEST ($DEST_C) is not a directory"
fi
mkdir -p "$DEST_C"
rsync -a --delete --checksum "$OUT/" "$DEST_C/"
log "translation written to $DEST"
# The metaprogramming-word pin of lean_guard.py (formal/trusted/translation-pins.txt; S21) is tied
# to the sha256 of Funs.lean. Report whether the new output still matches it: a mismatch is not an
# error here, but lean-guard.sh sources will apply the strict rule until the pin is updated in a
# reviewed PR.
pins="$ROOT/formal/trusted/translation-pins.txt"
[[ -z "${RMCP_NO_PATCHES:-}" && "${RMCP_TARGET_SET:-all}" == all ]] || pins=/dev/null/none  # linkage run: no pin note
dest_c="$(canon_path "$DEST")"
if [[ -f "$pins" && -f "$dest_c/Rmcp/Funs.lean" ]]; then
  want="$(awk '$1 == "file" && $2 == "translation/Rmcp/Funs.lean" { print $4 }' "$pins")"
  got="$(sha256sum "$dest_c/Rmcp/Funs.lean" 2>/dev/null || shasum -a 256 "$dest_c/Rmcp/Funs.lean")"
  got="${got%% *}"
  if [[ "$want" == "$got" ]]; then
    log "Funs.lean matches its pin in formal/trusted/translation-pins.txt"
  else
    log "note: Funs.lean sha256 $got differs from the pin ($want); update formal/trusted/translation-pins.txt in a reviewed PR"
  fi
fi
