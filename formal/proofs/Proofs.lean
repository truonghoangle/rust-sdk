/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
module
public import Defs
public import Proofs.Model.RequestStateWire.Common
public import Proofs.Model.RequestStateWire.B64Len
public import Proofs.Model.RequestStateWire.KeyLengthOk
public import Proofs.Model.RequestStateWire.CheckKidLen
public import Proofs.Model.RequestStateWire.BytesEq
public import Proofs.Model.RequestStateWire.NextDot
public import Proofs.Model.RequestStateWire.ComponentCount
public import Proofs.Model.RequestStateWire.VersionOf
public import Proofs.Model.RequestStateWire.ParseRs1
public import Proofs.Model.RequestStateWire.ParseRs2
public import Proofs.Model.RequestStateWire.TranscriptV1
public import Proofs.Model.RequestStateWire.TranscriptV2
public import Proofs.Model.RequestStateWire.DecodeExpiry
public import Proofs.Model.RequestStateWire.IsExpired
public import Proofs.Model.RequestStateWire.OpenFrame
public import Proofs.Model.RequestStateWire.Frame
public import Proofs.External.Base64
public import Proofs.External.String
public import Proofs.External.Option
public import Proofs.External.Net
public import Proofs.External.IntParse
public import Proofs.External.Prim
public import Proofs.External.Skill
public import Proofs.External.MetadataResolver
public import Proofs.External.Auth
public import Proofs.External.Base64Std
public import Proofs.External.ElicitationSchema
public import Proofs.External.Std
public import Proofs.External.Iter
public import Proofs.External.Byte
public import Proofs.External.WP
public import Proofs.Model.RequestState.Common
public import Proofs.Model.RequestState.OpenAuthenticatedBody
public import Proofs.Model.RequestState.ValidateKeyLength
public import Proofs.Model.RequestState.ValidateConfigKid
public import Proofs.Model.RequestState.B64Len
public import Proofs.Model.RequestState.OpenAt
public import Proofs.Model.RequestState.SealRs1
public import Proofs.Model.RequestState.SealRs2
public import Proofs.Model.RequestState.OpenRs1At
public import Proofs.Model.RequestState.Rs1FallbacksVerify
public import Proofs.Model.RequestState.OpenRs2At
public import Proofs.Model.RequestState.Roundtrip
public import Proofs.Model.RequestState.Public
public import Proofs.Model.RequestState.Keyring
public import Proofs.Model.RequestState.Seal
public import Proofs.Model.RequestState.OpenJson
public import Proofs.Model.RequestState.NewWithKeyring
public import Proofs.Model.JsonRpcMessage
public import Proofs.Model.NumberOrString
public import Proofs.Model.Task
public import Proofs.Model.SamplingContent
public import Proofs.Model.Reference
public import Proofs.Model.Skill.Common
public import Proofs.Model.Skill.Basic
public import Proofs.Model.Skill.Verify
public import Proofs.Model.Skill.Model
public import Proofs.Model.Skill.ValidateHelpers
public import Proofs.Model.Skill.Validate
public import Proofs.Model.ElicitationSchema.Common
public import Proofs.Model.ElicitationSchema.Primitive
public import Proofs.Model.ElicitationSchema.Enum
public import Proofs.Model.ElicitationSchema.Schema
public import Proofs.Transport.ClientSideSse
public import Proofs.Transport.AsyncRw
public import Proofs.Transport.Tower
public import Proofs.Transport.Auth
public import Proofs.Transport.MetadataResolver.Common
public import Proofs.Transport.MetadataResolver
public import Proofs.Transport.AuthMetadata.Common
public import Proofs.Transport.AuthMetadata
public import Proofs.Transport.McpHeaders.Common
public import Proofs.Transport.McpHeaders
public import Proofs.Defs.Sse
public import Proofs.Defs.Net
public import Proofs.Defs.MetadataResolver
public import Proofs.Defs.AuthMetadata
public import Proofs.Defs.McpHeaders
public import Proofs.Defs.Methods
public import Proofs.Defs.Tower
public import Proofs.Defs.ElicitationSchema
public import Proofs.Internal.External
public import Proofs.Internal.Model
public import Proofs.Internal.Model.RequestState
public import Proofs.Internal.Model.RequestStateWire
public import Proofs.Internal.Model.Skill
public import Proofs.Internal.Model.ElicitationSchema
public import Proofs.Internal.Transport.Common.ClientSideSse
public import Proofs.Internal.Transport.AsyncRw
public import Proofs.Internal.Transport.StreamableHttpServer.Tower
public import Proofs.Internal.Transport.Auth
public import Proofs.Internal.Transport.Auth.MetadataResolver
public import Proofs.Internal.Transport.Auth.AuthMetadata
public import Proofs.Internal.Transport.Common.McpHeaders

@[expose] public section

/-!
# Proofs

Root of the `Proofs` library: spec theorems and the laws of the external models (plan Section 5).
Maintained by hand; a proof module is added here only once its proof is complete
(formal/CONTRIBUTING.md, "Library roots"). Imports the `request_state_wire`
proofs (S06, S10): `Common` and the 15 target modules; the laws of the
external models (S08, S09: `Proofs.External.*`); and the `request_state` proofs of E01–E04
(S07), E07/E08 (S11), E09a/E09/E10 (S13), E11 (S14) and the round trips (S15, `Roundtrip`), with the
slice-iterator helper `Proofs.External.Iter`.

Phase 2 (2026-11-24, S28–S32): `Proofs.Model.{JsonRpcMessage, NumberOrString, Task,
SamplingContent, Reference}` (M01–M14, the joint lemmas, C03), `Proofs.Transport.{ClientSideSse,
AsyncRw, Tower, Auth}` (T01–T08, A01–A03, C01, C02, C04, C05); the S27 law relating the integer
parser model to `Defs.parseI64` is in `Proofs.External.IntParse`.

Skills (2026-11-25): `Proofs.Model.Skill.{Common, Basic, Verify, Model, ValidateHelpers,
Validate}` (K01–K20 of `skill.rs`, their corollaries, compositions and model consequences; specs
and proofs signed off / reviewed 2026-11-25), with the external-model laws in
`Proofs.External.Skill`.

OAuth metadata address policy (2026-11-26): `Proofs.Transport.MetadataResolver.Common` and
`Proofs.Transport.MetadataResolver` (N01, N03–N11 of `transport/auth/metadata_resolver.rs`, the
laws of `Defs.MetadataResolver` and the compositions; statements signed off 2026-11-26), restated
in `Proofs.Internal.Transport.Auth.MetadataResolver`.

OAuth metadata URL and issuer checks (2026-11-27): `Proofs.Transport.AuthMetadata.Common` and
`Proofs.Transport.AuthMetadata` (A04–A10 of `transport/auth.rs` through patch 06, the laws of
`Defs.AuthMetadata` and the compositions; statements signed off 2026-11-27), restated in
`Proofs.Internal.Transport.Auth.AuthMetadata`, with their definitions in
`Proofs.Defs.AuthMetadata`; the law `trimWhitespace_utf8Bytes` of the `str::trim` model is in
`Proofs.External.Auth`, restated in `Proofs.Internal.External`.

SEP-2243 header-value encoding (2026-11-28): `Proofs.Transport.McpHeaders.Common` and
`Proofs.Transport.McpHeaders` (G01–G04 of `transport/common/mcp_headers.rs` through patch 07, the
laws of `Defs.McpHeaders` and the compositions; statements signed off 2026-11-28), restated in
`Proofs.Internal.Transport.Common.McpHeaders`, with their definitions in `Proofs.Defs.McpHeaders`;
the laws of the Base64 and string models are in `Proofs.External.Base64Std`.

Elicitation schema builders (2026-11-28): `Proofs.Model.ElicitationSchema.{Common, Primitive,
Enum, Schema}` (X01–X75 of `model/elicitation_schema.rs`, 65 of them `ORIGINAL` and 10 through
patch 08, the `Default` impl of `EnumSchemaBuilder<SingleSelect>`, the builder invariants, the
consistency of built schemas and the laws of `Defs.ElicitationSchema`; statements signed off
2026-11-28), with the external-model laws in `Proofs.External.ElicitationSchema`. The 86
top-level statements are restated in `Specs.Model.ElicitationSchema`, the 23 others in
`Proofs.Internal.Model.ElicitationSchema`, with their internal-only definitions in
`Proofs.Defs.ElicitationSchema`.

Since 2026-11-24 it also imports the definitions used only by internal statements
(`Proofs.Defs.*`) and the internal spec files (`Proofs.Internal.*`: statements about intermediate
public functions (called by a top-level one; since 2026-11-28), private, crate-internal and
patch-only functions and the model laws, in the format of `formal/specs/Specs/`).
-/
