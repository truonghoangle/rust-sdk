# What is verified: index of the guarantees

> **At a glance.** Lean proves, for 25 Phase 1 and 25 Phase 2 Rust functions of `rmcp`, 15 public
> functions of `request_state.rs` (R01–R15) and the 20 public functions of `skill.rs` (K01–K20),
> that the translated call does not panic and returns what the statement says. Phase 2 and 13 of the
> `skill.rs` functions are upstream `7caec76` unmodified; Phase 1 and R01–R08 are about a patched
> copy (translation patch 01), R09–R15 about the copy with translation patches 01 and 03, and the
> other 7 `skill.rs` functions (K05–K07, K13–K16) about the copy with translation patch 04. 52
> guarantees are about the top-level public API (`Specs/`: 31 before the skills API, 21 for it;
> public functions that no other verified function calls), 36 about the intermediate public
> functions that a top-level one calls (with their corollaries and compositions) and the skills
> model, 53 about private, crate-internal or patch-only functions and 116 are laws of the trusted
> models (these three in `../proofs/Proofs/Internal/`): 257 restated theorems (the lemmas about the
> patch-04 models, `../proofs/Proofs/External/Skill.lean`, are proved but not restated). The public
> `request_state.rs` API is covered except 2 of its 17 public functions (R16–R17 `seal_json*`,
> excluded, blocked upstream); R09–R15 were signed off by the spec owner on 2026-11-25; the
> `skill.rs` API is covered completely, signed off by the spec owner on 2026-11-25. Main trust
> items: Charon/Aeneas/Lean, the translated configuration, patches 01, 03 and 04, the hand-written
> models (including the one clock reading of `open`, `open_json` and `seal`, and the opaque SHA-256,
> NFKC and General_Category functions); no native-code assumption remains (35 were locked until the
> Aeneas upgrade of 2026-11-24, which is reviewed and re-signed by the spec owner 2026-11-24). Two
> bugs found: H7 (`async_rw` method lists) and H8 (`240.0.0.0/4` not blocked); none in `skill.rs`.

**What, against what.** Each guarantee below is a Lean theorem about the
[Aeneas](https://github.com/AeneasVerif/aeneas) translation of the Rust code of `rmcp` (Charon
`0.1.324`, Aeneas `nightly-2026.11.24-fb44cb4`, Lean `v4.36.0`; until 2026-11-24 Charon
`0.1.235`, Aeneas `nightly-2026.08.20-5d08da4`, Lean `v4.31.0`). Phase 2 (IDs M, T, A, C) and
the skills functions K01–K04, K08–K12, K17–K20 are about upstream rmcp commit `7caec76`,
**unmodified**. This rests on
`scripts/check-original-linkage.sh`, which checks that the committed translation, generated from
the patched copy, equals block for block the translation of unmodified `7caec76` for these
targets (and that K05–K07, K13–K16, which need translation patch 04, do not translate from the
unmodified source); it passes locally, and its CI run (step S22) is pending (the records say "pending S22").
Phase 1 (IDs W, E, S15) and the public `request_state.rs` statements (IDs R; R01–R15 except
`seal_at` and `open_json_with` have the same text upstream, ten lines lower) are about a
**patched copy**: `7caec76` plus translation patch 01
([`../trusted/patches/01-request-state-wire.patch`](../trusted/patches/01-request-state-wire.patch)),
which refactors `RequestStateCodec` onto a new module `request_state_wire`, and for R09–R15
translation patch 03
([`../trusted/patches/03-request-state-public.patch`](../trusted/patches/03-request-state-public.patch),
+6/−2 lines in `seal_at` and `open_json_with` so that they translate); their link to the
unpatched code is tested, not proved. **How to read a statement.** `f x ⦃ r => P r ⦄` means
"the call `f x` does not panic (no failure, overflow or out-of-bounds access) and its result `r`
satisfies `P`"; the premises (`h_…`) are the assumptions; a statement `f x = (do …)` says that
two computations of the translated code are equal, failure included. Theorems about one function
are named `Theorems.<module>.<Type>.<function>` and most are proved by its `…_spec` theorem in
[`../proofs/`](../proofs/); the failing-case companions (`…_fail`), the joint lemmas and the
compositions are named after their statement (e.g. `Theorems.model.into_result_eq`) and proved by
the lemma of the same name. Under each theorem, `#guard_msgs in #print axioms` pins the logical
assumptions it uses: Lean's standard `propext`, `Classical.choice`, `Quot.sound` and nothing
else (until the Aeneas upgrade of 2026-11-24 some statements also listed native-code assumptions,
see "What you must trust"). Status and results: [`../README.md`](../README.md), "Results".

This directory holds only the **top-level public API** (functions `pub` in upstream rmcp that no
other verified function calls; human decisions 2026-11-24, 2026-11-28); guarantees about the
intermediate public functions that a top-level one calls, and about private, crate-internal and
patch-only functions, are in [`../proofs/Proofs/Internal/`](../proofs/Proofs/Internal/). Every
guarantee assumes the translated configuration and the trusted models listed at the end.

## Public guarantees

These are the **top-level** public functions (human decision 2026-11-28): `pub` in upstream rmcp
and called by no other verified function. The public functions that a top-level one calls are
verified too; their statements are under "Internal guarantees", "Intermediate public functions".

File [`Specs/Model.lean`](Specs/Model.lean) (`crates/rmcp/src/model.rs`) unless noted. The only
premises in this first table are the size premises of M13/M14 (met by every Rust `String`) and
of their failing-case companions; the request-state and skills tables below have their own.

| ID | Rust function | Guarantee | Assumptions | Lean theorem |
|---|---|---|---|---|
| M01 | `JsonRpcMessage::into_request` | Returns `Some((req, id))` exactly when the message is the request `req` with id `id`, `None` for every other kind. | none | [`Theorems.model.JsonRpcMessage.into_request`](Specs/Model.lean) |
| M02 | `JsonRpcMessage::into_response` | Returns `Some((resp, id))` exactly when the message is the response `resp` with id `id`, `None` otherwise. | none | [`Theorems.model.JsonRpcMessage.into_response`](Specs/Model.lean) |
| M03 | `JsonRpcMessage::into_notification` | Returns `Some(n)` exactly when the message is the notification `n`, `None` otherwise. | none | [`Theorems.model.JsonRpcMessage.into_notification`](Specs/Model.lean) |
| M04 | `JsonRpcMessage::into_error` | Returns `Some((err, id))` exactly when the message is the error `err` with optional id `id`, `None` otherwise. | none | [`Theorems.model.JsonRpcMessage.into_error`](Specs/Model.lean) |
| M05 | `JsonRpcMessage::into_result` | Returns `Some((Ok(resp), Some(id)))` for a response, `Some((Err(err), id))` for an error, `None` for a request or a notification; never `Some((Ok(_), None))`. | none | [`Theorems.model.JsonRpcMessage.into_result`](Specs/Model.lean) |
| M09 | `SamplingContent::into_vec` | `Single(x)` gives `vec![x]`; `Multiple(v)` gives `v`. | none | [`Theorems.model.SamplingContent.into_vec`](Specs/Model.lean) |
| M10 | `SamplingContent::is_empty` | `false` for `Single`; for `Multiple(v)`, `true` exactly when `v` is empty. | none | [`Theorems.model.SamplingContent.is_empty`](Specs/Model.lean) |
| M11 | `SamplingContent::len` | 1 for `Single`; `v.len()` for `Multiple(v)`. | none | [`Theorems.model.SamplingContent.len`](Specs/Model.lean) |
| M12 | `SamplingContent::first` | `Some(x)` for `Single(x)`; the first element of `v` (`None` if `v` is empty) for `Multiple(v)`. | none | [`Theorems.model.SamplingContent.first`](Specs/Model.lean) |
| M13 | `Reference::as_prompt_name` | For a prompt reference, `Some(s)` where `s` has the UTF-8 bytes of the prompt's name; `None` for a resource reference. | name of at most `usize::MAX` bytes | [`Theorems.model.Reference.as_prompt_name`](Specs/Model.lean) |
| M13 | (failing case) | A Lean string over `usize::MAX` bytes makes the translated call fail; this describes the Lean model only (no Rust `String` is that long). | name over `usize::MAX` bytes | [`Theorems.model.Reference.as_prompt_name_fail`](Specs/Model.lean) |
| M14 | `Reference::as_resource_uri` | For a resource reference, `Some(s)` where `s` has the UTF-8 bytes of its URI; `None` for a prompt reference. | URI of at most `usize::MAX` bytes | [`Theorems.model.Reference.as_resource_uri`](Specs/Model.lean) |
| M14 | (failing case) | As for M13, for a URI over `usize::MAX` bytes (Lean model only). | URI over `usize::MAX` bytes | [`Theorems.model.Reference.as_resource_uri_fail`](Specs/Model.lean) |
| joint lemma | `is_empty`, `len` | `is_empty()` is the same computation as `len() == 0`. | none | [`Theorems.model.SamplingContent.is_empty_eq_len_eq_zero`](Specs/Model.lean) |
| joint lemma | `first`, `into_vec` | `first()` is the same computation as the head of `into_vec()`. | none | [`Theorems.model.SamplingContent.first_eq_head?_into_vec`](Specs/Model.lean) |
| joint lemma | `len`, `into_vec` | `len()` is the same computation as `into_vec().len()`. | none | [`Theorems.model.SamplingContent.len_eq_len_into_vec`](Specs/Model.lean) |
| joint lemma | `into_request` … `into_error` | On every message the four calls succeed and exactly one of them returns `Some`. | none | [`Theorems.model.JsonRpcMessage.exactly_one_some`](Specs/Model.lean) |
| C03 | `into_result`, `into_response`, `into_error` | `into_result` is the same computation as `into_response` mapped to `(Ok(r), Some(id))`, or else `into_error` mapped to `(Err(e), id)`. | none | [`Theorems.model.into_result_eq`](Specs/Model.lean) |
| M08 | `rmcp::model::TaskStatus::is_terminal` (in `model/task.rs`, re-exported by `pub use task::*`) | `true` exactly for `Completed`, `Failed` and `Cancelled`. | none | [`Theorems.task.TaskStatus.is_terminal`](Specs/Model/Task.lean) |

"Same computation" rows are equations of the translated code: equal results and equal failure.
"Joint lemma" rows are the joint lemmas of plan Section 16.1.

**Request-state codec, top-level public API** —
[`Specs/Model/RequestState.lean`](Specs/Model/RequestState.lean)
(`crates/rmcp/src/model/request_state.rs`, patched copy; R01–R04, R06, R07, R09, R11–R13, R15 and
the corollary of R09; the intermediate R05, R08, R10, R14 are under "Internal guarantees").
Rust functions are `rmcp::model::request_state::…`. Premise keys (the same in the file's
docstring): **`h_into`** the caller's `Into<Vec<u8>>` conversion of `key` returns the vector `v`
(user code, which may panic); **(F)** for a token whose first `.`-component is `rs1`, every rs1
fallback id of the codec is a key id (`CodecFallbacksKnown`; sufficient, not necessary, for the
code's `expect` not to panic);
**(S)** the seal-mode key id is a key id (`CodecSealKeyKnown`; else the code's `expect` panics);
**(D)** the Lean-model domain of sealing (`SealFits`: transcript within `usize::MAX`, `with_capacity`
sum within `isize::MAX`); **(Ls)** `ad.len() + 2 * payload.len() + 512 ≤ isize::MAX`; **(R)** the
Lean-model domain of the keyring builders (`KeyringFits`: key ids within `usize::MAX` bytes, fewer
than `usize::MAX` fallbacks; met by every Rust value); **(U)** the converted key ids of
`new_with_keyring` have at most `usize::MAX` bytes (met by every Rust `String`); **caller code**
(`as_ref`, `into`, the caller's iterator) returns the named values.
`ad` is the associated data; "exactly `openAt`" means the result is `Ok` of the bytes, or the
error, that `Defs.CodecState.openAt` gives (the expected result of E11 `open_at`, internal table
below); "`sealAt`" means the token's UTF-8 bytes are those `Defs.CodecState.sealAt` gives (the
expected result of the private `seal_at`, R10a below). R07, R09, R13 and the corollary are
specified at the clock reading `ExtModel.nowMs`, one opaque
`i64`: each statement holds for that one reading and says nothing about two calls (in Rust two
calls read different times). Inherited exceptions, **not premises** (inputs where Rust panics but
the statement promises a result; "What you must trust"): **(K)** the system clock is before 1970
or outside chrono's range (`Utc::now` panics, even for a malformed token, as the clock is read
first); **(H)** HMAC's bit counter overflows for a transcript of at least `2^61 − 64` bytes or a
key of at least `2^61` bytes; **(J)** `open_json*`: the `serde_json::from_slice` model (a
`Deserialize` impl that panics, does not terminate, is non-deterministic or has side effects);
**(I)** R04–R06 (R05 internal), R11, R12, R15: a caller conversion or iterator (`Into`, `AsRef`,
`IntoIterator`) with side effects outside its argument or state (global or thread-local state,
input/output), which the premises do not describe; **(P)** a caller `Drop` impl that panics (R11,
R12, R15); **(N)** `HashMap::new` panics if the operating system's random source fails (R15).

| ID | Rust function | Guarantee | Assumptions | Lean theorem |
|---|---|---|---|---|
| R01 | `SealOptions::new` | Returns options with no associated data (empty) and no time-to-live (`None`). | none | [`Theorems.request_state.SealOptions.new`](Specs/Model/RequestState.lean) |
| R02 | `SealOptions::associated_data` | Returns the options with the associated data set to the argument and the time-to-live unchanged. | none | [`Theorems.request_state.SealOptions.associated_data`](Specs/Model/RequestState.lean) |
| R03 | `SealOptions::ttl` | Returns the options with the time-to-live set to `Some(ttl)` and the associated data unchanged. | none | [`Theorems.request_state.SealOptions.ttl`](Specs/Model/RequestState.lean) |
| R04 | `RequestStateCodec::new` (deprecated) | Returns the single-key codec of `v`, for a key of any length; it satisfies `CodecValid`. | `h_into`; inherited exception (I) | [`Theorems.request_state.RequestStateCodec.new`](Specs/Model/RequestState.lean) |
| R06 | `RequestStateCodec::try_new` | `Ok` of the single-key codec of `v` (satisfying `CodecValid`) exactly when `v` has at least 32 bytes, otherwise `KeyTooShort { minimum: 32, actual: v.len() }`. | `h_into`; inherited exception (I) | [`…RequestStateCodec.try_new`](Specs/Model/RequestState.lean) |
| R07 | `RequestStateCodec::open` | Returns exactly `openAt` of the token with no associated data at the clock reading (one reading; says nothing about two calls). | (F); inherited exceptions (K) clock range, (H) HMAC `2^61` | [`…RequestStateCodec.open`](Specs/Model/RequestState.lean) |
| R09 | `RequestStateCodec::seal` | Returns the token `sealAt` gives with no associated data and no time-to-live at the clock reading (the token does not depend on the reading, but the clock is read). | (S), (D); inherited exceptions (K), (H) | [`…RequestStateCodec.seal`](Specs/Model/RequestState.lean) |
| R09 | `seal` (corollary) | As R09, with `CodecValid` and `2 * payload.len() + 512 ≤ isize::MAX` in place of (S), (D). | `CodecValid`, (Ls); inherited exceptions (K), (H) | [`…RequestStateCodec.seal_of_length_le`](Specs/Model/RequestState.lean) |
| R11 | `RequestStateCodec::with_rs1_signing` | On a keyring, for a configured key id: `Ok` of the codec with the same keys, seal mode `Rs1 { key_id }` and the id appended to the rs1 fallbacks unless already there; preserves `CodecValid`. Otherwise `InvalidKeyring` with the exact message (single-key codec; unknown id). | caller code, (R); inherited exceptions (I), (P) | [`…RequestStateCodec.with_rs1_signing`](Specs/Model/RequestState.lean) |
| R12 | `RequestStateCodec::with_rs1_fallback` | On a keyring, for a configured key id: `Ok` of the codec with the same keys and seal mode and the id appended to the rs1 fallbacks unless already there; preserves `CodecValid`. Otherwise `InvalidKeyring` with the exact message (single-key codec; unknown id). | caller code, (R); inherited exceptions (I), (P) | [`…RequestStateCodec.with_rs1_fallback`](Specs/Model/RequestState.lean) |
| R13 | `RequestStateCodec::open_json` | If `openAt` of the token with no associated data at the clock reading is an error, that error; otherwise the `serde_json::from_slice` outcome of the payload, an error mapped to `Deserialization`. | (F); inherited exceptions (K), (H), (J) | [`…RequestStateCodec.open_json`](Specs/Model/RequestState.lean) |
| R15 | `RequestStateCodec::new_with_keyring` | `Err` exactly when the Rust checks reject the entries or the active id (`keyringCheck`), with the exact error of the first failure in the Rust order (per entry: empty id, id over 255 bytes, key under 32 bytes, duplicate id; then no entry, active id invalid, active id absent). Otherwise `Ok` of a keyring with exactly the configured keys (ids up to order), seal mode `Rs2 { key_id: active }`, no rs1 fallback, satisfying `CodecValid`. | caller code (iterator, conversions), (U); inherited exceptions (I), (P), (N) | [`…RequestStateCodec.new_with_keyring`](Specs/Model/RequestState.lean) |

**Skills, top-level public API** — [`Specs/Model/Skill.lean`](Specs/Model/Skill.lean)
(`crates/rmcp/src/model/skill.rs`, upstream `7caec76`; the 14 top-level functions K01–K03, K05,
K06, K08–K11, K16–K20 with 3 corollaries and 4 compositions: 21 theorems; the intermediate K04,
K07, K12–K15, their corollary and compositions, and the 18 consequences of the model are under
"Internal guarantees"). K01–K04, K08–K12 and K17–K20 are about the **unmodified** source (linkage
`ORIGINAL`, as Phase 2); K05–K07 and K13–K16 about the copy with translation patch 04
([`../trusted/patches/04-skill-public.patch`](../trusted/patches/04-skill-public.patch), hunks
H1–H9: the `str` pattern APIs, SHA-256, NFKC and percent-encoding behind a private module `prim`
of one-line wrappers, and loops without early return), signed off by the spec owner on
2026-11-25. Rust functions are `rmcp::model::skill::…` (K01 is an inherent method of
`rmcp::model::Resource` written in `skill.rs`). Expected results are definitions of
[`Defs/Skill.lean`](Defs/Skill.lean): `sha256Digest bytes` is `sha256:` followed by the
lowercase hex of the SHA-256 digest; `skillNameOfUri uri` the name segment of a URI
`…/<segment>/SKILL.md` without `?` or `#`; `isSha256Digest` the digest format; `validateResult s`
`Ok(())` or the first failing check of `Skill::validate` in the Rust order (URI names no skill,
invalid name, name does not match the segment, manifest without `SKILL.md`, then the first per-file
fault), with its payload; `validateSkillsResult` the same for a listing, plus `DuplicateSkill`
for the first repeated percent-normalised URI; `ValidSkill`, `ValidSkills` the `Ok` cases.

The assumptions of this table are written in words, because the letters of the spec file's own
glossary are local to it and differ from the request-state keys above. **Premises** (the caller
must ensure them; nothing is promised otherwise): **caller code** — the caller's `Into<String>` or
`Into<serde_json::Value>` conversion returns the value the statement names (the standard `From`
impls for `&str` and `String` do); **string fits** (`UsizeFits`) — the string has at most
`usize::MAX` UTF-8 bytes (every Rust `String` does); **skill fits** (`SkillFits`) — the skill's URI
and name fit, every manifest file's digest fits and its URI meets `24 * (n + 1) ≤ isize::MAX` for
its `n` bytes (every skill held in memory does); **URI fits** (`UriFits`) — the same bound for each
skill's URI in `validate_skills`; **NFKC fits** (`NfkcFits`), a **domain restriction induced by
patch 04** — the NFKC forms of the name and of the decoded URI segment have at most `isize::MAX / 4`
characters (the patched copy collects them into a `Vec<char>` and would panic above that; the
original streams them). It holds whenever the name and the URI have at most `isize::MAX / 72`
bytes (more than `2^56`), given that NFKC expands a character sequence at most 18-fold (the last row
of the internal skills table; Rust evidence in
[`../trusted/evidence/README.md`](../trusted/evidence/README.md), "NFKC expansion bound"). **Not
covered** (inherited exceptions, not premises: Rust may panic or behave otherwise while the
statement promises a result): **caller side effects** — a caller conversion with side
effects or reading global state, or a caller `Drop` that panics; **SHA-256 at `2^61` bytes** —
the bit counter of `sha2` overflows for an input of at least `2^61` bytes (K05, K07, K06 when the
length matches, and the statements built on them); **`HashSet` random source** — the random hash
keys of `HashSet::with_capacity` and a failing operating-system random source are not modelled;
the statements depend only on set membership (K13, K16); **`preserve_order`** — if a downstream
build enables the `serde_json` feature `preserve_order`, `serde_json::Map` keeps insertion order,
and the order clauses of K09 (not its lookups) no longer hold. The three opaque SHA-256, NFKC and
General_Category functions appear only unopened, as the values the Rust code computes.

| ID | Rust function | Guarantee | Assumptions | Lean theorem |
|---|---|---|---|---|
| K01 | `Resource::is_directory` | `true` exactly when the MIME type is `Some("inode/directory")`. | MIME type: string fits | [`Theorems.skill.Resource.is_directory`](Specs/Model/Skill.lean) |
| K02 | `SkillsCapability::new` | The capability with `directory_read = false`. | none | [`Theorems.skill.SkillsCapability.new`](Specs/Model/Skill.lean) |
| K03 | `SkillsCapability::with_directory_read` | `directory_read = true` (its only field). | none | [`…SkillsCapability.with_directory_read`](Specs/Model/Skill.lean) |
| K05 | `SkillResource::from_bytes` | The entry with the converted URI, digest `sha256Digest bytes` and size `bytes.len()`. | caller code; not covered: caller side effects, SHA-256 at `2^61` bytes | [`…SkillResource.from_bytes`](Specs/Model/Skill.lean) |
| K06 | `SkillResource::verify` | `Ok(())` exactly when the length is `size` and the digest matches; otherwise `Size` (the length is checked first), else `Digest`, with the expected and actual values. | none; not covered: SHA-256 at `2^61` bytes | [`…SkillResource.verify`](Specs/Model/Skill.lean) |
| K08 | `SkillFrontmatter::new` | The converted name and description, no extra field. | caller code; not covered: caller side effects | [`…SkillFrontmatter.new`](Specs/Model/Skill.lean) |
| K09 | `SkillFrontmatter::with_field` | `extra` with `key ↦ value` set, other keys and fields unchanged; still sorted by key if it was. | caller code; not covered: caller side effects, `preserve_order` | [`…SkillFrontmatter.with_field`](Specs/Model/Skill.lean) |
| K09 | `with_field` (corollary) | The entries of `extra` are those of the `BTreeMap` insertion of `key ↦ value`. | as K09 | [`…SkillFrontmatter.with_field_extra_entries_eq_mapInsert`](Specs/Model/Skill.lean) |
| K10 | `Skill::new` | The converted URI, the frontmatter and resources given, no `_meta`. | caller code; not covered: caller side effects | [`…Skill.new`](Specs/Model/Skill.lean) |
| K11 | `Skill::with_meta` | `_meta = Some(meta)`, other fields unchanged. | none | [`…Skill.with_meta`](Specs/Model/Skill.lean) |
| K16 | `validate_skills` | `validateSkillsResult skills`: the first skill's error, or `DuplicateSkill` for the first repeated normalised URI, else `Ok(())`. | for each skill: skill fits, URI fits, NFKC fits (patch-induced); not covered: `HashSet` random source | [`Theorems.skill.validate_skills`](Specs/Model/Skill.lean) |
| K16 | `validate_skills` (corollary) | `Ok(())` exactly when every skill is valid and the normalised URIs are distinct (`ValidSkills`). | as K16 | [`…validate_skills_eq_ok_iff`](Specs/Model/Skill.lean) |
| K17 | `GetSkillResult::new` | `result_type = Some(COMPLETE)`, the skill, no TTL, cache scope or `_meta`. | none | [`…GetSkillResult.new`](Specs/Model/Skill.lean) |
| K18 | `GetSkillResult::with_ttl_ms` | `ttl_ms = Some(ttl_ms)`, other fields unchanged. | none | [`…GetSkillResult.with_ttl_ms`](Specs/Model/Skill.lean) |
| K19 | `GetSkillResult::with_cache_scope` | `cache_scope = Some(cache_scope)`, other fields unchanged. | none | [`…GetSkillResult.with_cache_scope`](Specs/Model/Skill.lean) |
| K20 | `GetSkillResult::with_meta` | `_meta = Some(meta)`, other fields unchanged. | none | [`…GetSkillResult.with_meta`](Specs/Model/Skill.lean) |
| K05+K06 | `from_bytes`, then `verify` | An entry made from bytes verifies them: `Ok(())`. | caller code; not covered: caller side effects, SHA-256 at `2^61` bytes | [`…SkillResource.verify_from_bytes_self`](Specs/Model/Skill.lean) |
| K05+K06 | `from_bytes`, then `verify` | Against other bytes: `Ok(())` exactly when they have the same length and SHA-256 digest; else `Size` or `Digest`, with the values. | as above | [`…SkillResource.verify_from_bytes`](Specs/Model/Skill.lean) |
| K05 | `from_bytes` (same computation) | The same computation as `uri.into()` followed by the entry with digest `sha256Digest bytes` and size `bytes.len()`. | none; not covered: SHA-256 at `2^61` bytes | [`…SkillResource.from_bytes_eq`](Specs/Model/Skill.lean) |
| K05 | `from_bytes` (with the model) | The entry's digest is well-formed (`isSha256Digest`), so `validate` never reports it as `MalformedDigest`. | caller code; not covered: caller side effects, SHA-256 at `2^61` bytes | [`…SkillResource.isSha256Digest_from_bytes`](Specs/Model/Skill.lean) |
| K06 | `verify` (corollary) | `Ok(())` exactly when the length is `size` and `sha256Digest bytes` is the digest. | none; not covered: SHA-256 at `2^61` bytes | [`…SkillResource.verify_eq_ok_iff`](Specs/Model/Skill.lean) |

## Internal guarantees

Statements about functions that are not top-level public rmcp API. First the intermediate public
functions, whose callers are verified (next paragraph); then functions that are not public. For
those, "Used by" names the public functions or features whose code calls them (from
`crates/rmcp/src`, or the patched copy for Phase 1); those callers are **not** verified, so the
guarantee covers only the called function. Where one caller covers every row of a section, the
section says it once and the table has no "Used by" column. Every row about a call also says that it
does not panic.

**Intermediate public functions** (human decision 2026-11-28). `Specs/` states only the
**top-level** public functions: those that no other verified function calls. A public function
that a top-level one calls is verified as well, and its statement is here. Unlike the rows below,
its callers **are** verified: the top-level statement is proved from it.

*Request-state codec* —
[`Internal/Model/RequestState.lean`](../proofs/Proofs/Internal/Model/RequestState.lean), section
"Intermediate public functions" (`request_state.rs`, patched copy). Called by: R05 `new_unchecked`
by R04 `new`; R08 `open_with` by R07 `open` and R14 `open_json_with` (so by R13 `open_json` through
R14); R10 `seal_with` by R09 `seal`; R14 `open_json_with` by R13 `open_json`. Premise and exception
keys as in "Request-state codec, top-level public API" above, plus **(T)** the MAC transcript of the
decoded components and `ad` fits in `usize::MAX` bytes, **(L)** `ad.len() + sealed.len() + 36 ≤
usize::MAX` (implies (T)), and the inherited exception **(V)** the transcript `Vec` is modelled up
to `usize::MAX` bytes while Rust panics above `isize::MAX` (not with empty `ad`, nor under (Ls)).

| ID | Rust function | Guarantee | Assumptions | Lean theorem |
|---|---|---|---|---|
| R05 | `RequestStateCodec::new_unchecked` | Returns the single-key codec of `v`, for a key of any length; it satisfies `CodecValid`. | `h_into`; inherited exception (I) | [`…RequestStateCodec.new_unchecked`](../proofs/Proofs/Internal/Model/RequestState.lean) |
| R08 | `RequestStateCodec::open_with` | Returns exactly `openAt` of the token with associated data `ad` at the clock reading (one reading; says nothing about two calls). | (T), (F); inherited exceptions (K) clock range, (H) HMAC `2^61`, (V) `Vec` above `isize::MAX` | [`…RequestStateCodec.open_with`](../proofs/Proofs/Internal/Model/RequestState.lean) |
| R08 | `open_with` (corollary) | As R08, with the length premise (L) in place of (T). | (L), (F); inherited exceptions (K) clock range, (H) HMAC `2^61`, (V) `Vec` above `isize::MAX` | [`…RequestStateCodec.open_with_of_length_le`](../proofs/Proofs/Internal/Model/RequestState.lean) |
| R10 | `RequestStateCodec::seal_with` | Returns the token `sealAt` gives with the options' associated data and time-to-live at the clock reading (one reading; says nothing about two calls). | (S), (D); inherited exceptions (K), (H), (V) | [`…RequestStateCodec.seal_with`](../proofs/Proofs/Internal/Model/RequestState.lean) |
| R10 | `seal_with` (corollary) | As R10, with `CodecValid` and (Ls) in place of (S), (D). | `CodecValid`, (Ls); inherited exceptions (K), (H) | [`…RequestStateCodec.seal_with_of_length_le`](../proofs/Proofs/Internal/Model/RequestState.lean) |
| R14 | `RequestStateCodec::open_json_with` | As R13, with associated data `ad`. | (T), (F); inherited exceptions (K), (H), (V), (J) | [`…RequestStateCodec.open_json_with`](../proofs/Proofs/Internal/Model/RequestState.lean) |

*Skills* — [`Internal/Model/Skill.lean`](../proofs/Proofs/Internal/Model/Skill.lean)
(`skill.rs`). Called by: K04 `SkillResource::new` and K07 `sha256_digest` by K05 `from_bytes`
(K07 also by K06 `verify`); K13 `Skill::validate` by K16 `validate_skills`; K12 `Skill::name`,
K14 `skill_name_from_uri`, K15 `is_sha256_digest` by K13. With the corollary of K13, the 5
compositions that involve an intermediate function and the 18 consequences of the model
`Defs.Skill` (statements with no Rust call; `model` rows): 30 theorems. Keys as in "Skills,
top-level public API" above.

| ID | Rust function | Guarantee | Assumptions | Lean theorem |
|---|---|---|---|---|
| K04 | `SkillResource::new` | The entry with the converted URI and digest and the given size. | caller code; not covered: caller side effects | [`…SkillResource.new`](../proofs/Proofs/Internal/Model/Skill.lean) |
| K07 | `sha256_digest` | `sha256:` followed by the lowercase hex of the SHA-256 digest (`sha256Digest`). | none; not covered: SHA-256 at `2^61` bytes | [`Theorems.skill.sha256_digest`](../proofs/Proofs/Internal/Model/Skill.lean) |
| K12 | `Skill::name` | The bytes of the frontmatter name. | name: string fits | [`…Skill.name`](../proofs/Proofs/Internal/Model/Skill.lean) |
| K13 | `Skill::validate` | `validateResult self`: the first failing check in the Rust order, with its payload, else `Ok(())`. | skill fits, NFKC fits (patch-induced); not covered: `HashSet` random source | [`…Skill.validate`](../proofs/Proofs/Internal/Model/Skill.lean) |
| K13 | `validate` (corollary) | `Ok(())` exactly when the skill is valid (`ValidSkill`). | as K13 | [`…Skill.validate_eq_ok_iff`](../proofs/Proofs/Internal/Model/Skill.lean) |
| K14 | `skill_name_from_uri` | `skillNameOfUri uri`. | none | [`Theorems.skill.skill_name_from_uri`](../proofs/Proofs/Internal/Model/Skill.lean) |
| K15 | `is_sha256_digest` | `isSha256Digest digest`: `sha256:` followed by 64 lowercase hex digits. | none | [`Theorems.skill.is_sha256_digest`](../proofs/Proofs/Internal/Model/Skill.lean) |
| K07+K15 | `sha256_digest`, then `is_sha256_digest` | A computed digest is well-formed (`true`). | none; not covered: SHA-256 at `2^61` bytes | [`…is_sha256_digest_sha256_digest`](../proofs/Proofs/Internal/Model/Skill.lean) |
| K11+K13 | `Skill::with_meta`, then `validate` | `validate` ignores `_meta`: the result is `validateResult self`. | skill fits, NFKC fits for `self`; not covered: `HashSet` random source | [`…Skill.validate_with_meta`](../proofs/Proofs/Internal/Model/Skill.lean) |
| K13+K14 | `skill_name_from_uri`, `validate` | On the skill's URI, `None` exactly when `validate` returns `UriNotSkillMd(uri)`. | as K13 | [`…Skill.skill_name_from_uri_eq_none_iff_validate_eq_err`](../proofs/Proofs/Internal/Model/Skill.lean) |
| K13+K14 | `skill_name_from_uri`, `validate` | If `validate` returns `Ok(())`, `Some(segment)` with a segment that matches the name. | as K13 | [`…Skill.exists_skill_name_from_uri_eq_some_of_validate_eq_ok`](../proofs/Proofs/Internal/Model/Skill.lean) |
| K16+K13 | `validate_skills`, `validate` | On one skill, `validate_skills` returns what `validate` returns. | skill fits, URI fits, NFKC fits for the skill; not covered: `HashSet` random source | [`…validate_skills_singleton`](../proofs/Proofs/Internal/Model/Skill.lean) |
| model | — | What `skillNameOfUri` accepts: no `?`/`#`, and the URI is `dir ++ segment ++ "/SKILL.md"`. | none | [`…skillNameOfUri_eq_some_iff`](../proofs/Proofs/Internal/Model/Skill.lean) |
| model | — | Example: `billing/SKILL.md` names the skill `billing`. | none | [`…skillNameOfUri_billing`](../proofs/Proofs/Internal/Model/Skill.lean) |
| model | — | `sha256Digest` of any bytes is well-formed (71 ASCII bytes). | none | [`…isSha256Digest_sha256Digest`](../proofs/Proofs/Internal/Model/Skill.lean) |
| model | — | The name rule as words joined by single `-`. | none | [`…nameCharsValid_iff_words`](../proofs/Proofs/Internal/Model/Skill.lean) |
| model | — | `validateResult s = Ok` exactly when `ValidSkill s`. | none | [`…validateResult_eq_ok_iff`](../proofs/Proofs/Internal/Model/Skill.lean) |
| model | — | `UriNotSkillMd u` exactly when the URI names no skill, with `u` the URI. | none | [`…validateResult_eq_err_uriNotSkillMd_iff`](../proofs/Proofs/Internal/Model/Skill.lean) |
| model | — | `InvalidName n` exactly when the URI names a skill and the name `n` is invalid. | none | [`…validateResult_eq_err_invalidName_iff`](../proofs/Proofs/Internal/Model/Skill.lean) |
| model | — | `NameMismatch u n` exactly when the URI names a skill, the name is valid and does not match the segment, with the payloads. | none | [`…validateResult_eq_err_nameMismatch_iff`](../proofs/Proofs/Internal/Model/Skill.lean) |
| model | — | `MissingSkillMd u` exactly when checks 1–3 pass and `resources` is a manifest without the skill's URI. | none | [`…validateResult_eq_err_missingSkillMd_iff`](../proofs/Proofs/Internal/Model/Skill.lean) |
| model | — | A per-file error `e` exactly when checks 1–5 pass and `e` is the first file fault. | none | [`…validateResult_eq_err_iff_firstFileFault_eq_some`](../proofs/Proofs/Internal/Model/Skill.lean) |
| model | — | `validateResult` never gives `DuplicateSkill`. | none | [`…validateResult_ne_err_duplicateSkill`](../proofs/Proofs/Internal/Model/Skill.lean) |
| model | — | `validateResult` does not depend on `_meta`. | none | [`…validateResult_with_meta`](../proofs/Proofs/Internal/Model/Skill.lean) |
| model | — | Files with well-formed digests never give `MalformedDigest`. | none | [`…firstFileFault_ne_malformedDigest`](../proofs/Proofs/Internal/Model/Skill.lean) |
| model | — | `validateSkillsResult l = Ok` exactly when `ValidSkills l`. | none | [`…validateSkillsResult_eq_ok_iff`](../proofs/Proofs/Internal/Model/Skill.lean) |
| model | — | `validateSkillsResult [s] = validateResult s`. | none | [`…validateSkillsResult_singleton`](../proofs/Proofs/Internal/Model/Skill.lean) |
| model | — | A sublist (e.g. a prefix) of a valid listing is valid. | none | [`…ValidSkills.sublist`](../proofs/Proofs/Internal/Model/Skill.lean) |
| model | — | An error of a prefix is the error of the whole listing. | none | [`…validateSkillsResult_append_of_eq_err`](../proofs/Proofs/Internal/Model/Skill.lean) |
| model | — | NFKC fits follows from `72 * n ≤ isize::MAX` for the `n` bytes of the name and of the URI. | the law that NFKC expands a character sequence of length `m` to at most `18 * m` characters (a premise in law form about the opaque NFKC function; true of `unicode-normalization 0.1.26`, largest expansion U+FDFA) | [`…NfkcFits.of_utf8ByteSize_le`](../proofs/Proofs/Internal/Model/Skill.lean) |

"Model" rows are statements about the definitions of `Defs/Skill.lean` only (no Rust call); a
reader can use them to check that the expected results say what the Rust documentation says.

**Model, crate-internal** — [`Internal/Model.lean`](../proofs/Proofs/Internal/Model.lean)
(`model.rs`, `pub(crate)`).

| ID | Rust function | Guarantee | Assumptions | Lean theorem | Used by |
| --- | --- | --- | --- | --- | --- |
| M06 | `NumberOrString::numeric_string_value` | `None` for a numeric id; for a string id, the value that `Defs.parseI64` (the `i64::from_str` grammar: optional `+`/`-`, one or more ASCII digits, `i64` range) gives its bytes, `None` if rejected. | none | [`Theorems.model.NumberOrString.numeric_string_value`](../proofs/Proofs/Internal/Model.lean) | matching responses to pending requests in the service loop (`remove_pending_request`) and in the streamable HTTP client |
| M07 | `NumberOrString::matches_response_id` | `true` exactly when the ids are equal, or `self` is `Number(n)` and the response id is a string that `Defs.parseI64` reads as `n`. | none | [`Theorems.model.NumberOrString.matches_response_id`](../proofs/Proofs/Internal/Model.lean) | the client's check of the `initialize` response id |

**SSE event-size limiter** — [`Internal/Transport/Common/ClientSideSse.lean`](../proofs/Proofs/Internal/Transport/Common/ClientSideSse.lean)
(private struct `SseEventSizeLimiter`). `sat(a + b)` is addition saturating at `usize::MAX`;
"the model" is `Defs.Sse` (line ends CR, LF or CR LF; comment lines start with `:`; an empty
line ends the event). What the limit counts (`Defs.Sse`, "What is counted"): each completed
non-comment line of the current event counts its length + 1, the current line its length so
far; completed comment lines and the blank line that ends the event count 0. This is not the raw
byte size of the event (a CR LF counts 1). Used by (all rows): the SSE event-size limit
`max_sse_event_size` of the reqwest streamable HTTP client
(`transport/common/reqwest/streamable_http_client.rs`, lines 205 and 482) and of the Unix-socket
streamable HTTP client (`transport/common/unix_socket.rs`, lines 384 and 589, feature
`transport-streamable-http-client-unix-socket`), both through `bounded_sse_stream` and
`BoundedSseByteStream` (`async`, not translated).

| ID | Rust function | Guarantee | Assumptions | Lean theorem |
| --- | --- | --- | --- | --- |
| T03 | `observe` | The result and the new state are those of the model: the bytes of the chunk are processed one by one, stopping at the first byte whose step fails the bound check (an LF completing CR LF is not checked). | none | [`Theorems.client_side_sse.SseEventSizeLimiter.observe`](../proofs/Proofs/Internal/Transport/Common/ClientSideSse.lean) |
| T02 | `finish_line` | The new state is the model's `finishLine` of the old one, and the result is T01's verdict on the new state. | none | [`…SseEventSizeLimiter.finish_line`](../proofs/Proofs/Internal/Transport/Common/ClientSideSse.lean) |
| T01 | `check_limit` | `Err(())` exactly when `sat(retained_size + line_size) > max_size`, `Ok(())` otherwise. | none | [`…SseEventSizeLimiter.check_limit`](../proofs/Proofs/Internal/Transport/Common/ClientSideSse.lean) |
| C01 | `observe` on `a ++ b` | Same computation as `observe` on `a` followed, on `Ok(())`, by `observe` on `b` from the state reached; on `Err(())` the same error and state. | none | [`…SseEventSizeLimiter.observe_append`](../proofs/Proofs/Internal/Transport/Common/ClientSideSse.lean) |
| C01 | `observe` (plan form) | `observe` on `a ++ b` is `observe` on `b` from the state after `a`. | `observe` on `a` returned `Ok(())` | [`…SseEventSizeLimiter.observe_append_of_observe_eq_ok`](../proofs/Proofs/Internal/Transport/Common/ClientSideSse.lean) |
| C02 | `observe` | The bound `sat(retained_size + line_size) ≤ max_size` is kept and `max_size` is unchanged. | bound holds before; the call returned `Ok(())` | [`…SseEventSizeLimiter.max_size_eq_and_satAdd_le_of_observe_eq_ok`](../proofs/Proofs/Internal/Transport/Common/ClientSideSse.lean) |
| C02 | `observe` (prefix form) | `observe` on the prefix `a` returns `Ok(())` with a state that keeps `max_size` and the bound. | bound holds before; `observe` on `a ++ b` returned `Ok(())` | [`…exists_observe_eq_ok_and_max_size_eq_and_satAdd_le_of_observe_append_eq_ok`](../proofs/Proofs/Internal/Transport/Common/ClientSideSse.lean) |

**Line codec** — [`Internal/Transport/AsyncRw.lean`](../proofs/Proofs/Internal/Transport/AsyncRw.lean)
(private `fn`s of `async_rw.rs`). Used by (all rows): `AsyncRwTransport::receive` and the
`Decoder` of `JsonRpcMessageCodec`, i.e. the stdio and child-process transports (T04 on every
line; T05/T06 decide, in `should_ignore_notification`, whether a line that fails to deserialize
is dropped). "Core" names: the request and notification names of the official MCP schemas
(`Defs.Methods`, human decision H6), compared byte for byte.

| ID | Rust function | Guarantee | Assumptions | Lean theorem |
| --- | --- | --- | --- | --- |
| T04 | `without_carriage_return` | Drops exactly one trailing `\r` if there is one; otherwise returns the slice unchanged. | none | [`Theorems.async_rw.without_carriage_return`](../proofs/Proofs/Internal/Transport/AsyncRw.lean) |
| T06 | `is_standard_method` | `true` exactly for the core request and notification names, minus the six names the code omits (bug H7). | none | [`Theorems.async_rw.is_standard_method`](../proofs/Proofs/Internal/Transport/AsyncRw.lean) |
| T05 | `is_standard_notification` | `true` exactly for the core notification names, minus those the code omits (bug H7). | none | [`Theorems.async_rw.is_standard_notification`](../proofs/Proofs/Internal/Transport/AsyncRw.lean) |
| C05 | both | A name that `is_standard_notification` accepts, `is_standard_method` accepts. | the first call returned `true` | [`Theorems.async_rw.is_standard_method_of_is_standard_notification`](../proofs/Proofs/Internal/Transport/AsyncRw.lean) |

**Origin check** — [`Internal/Transport/StreamableHttpServer/Tower.lean`](../proofs/Proofs/Internal/Transport/StreamableHttpServer/Tower.lean)
(private `fn` and enum of `tower.rs`). Used by (all rows): `origin_is_allowed`, the `Origin`
check of the DNS-rebinding protection of `StreamableHttpService` (`allowed_origins` of
`StreamableHttpServerConfig`); the origin parsing is not verified.

| ID | Rust function | Guarantee | Assumptions | Lean theorem |
| --- | --- | --- | --- | --- |
| T07 | `default_port` | `Some(80)` for exactly `"http"`, `Some(443)` for exactly `"https"` (case-sensitive bytes), `None` otherwise. | none | [`Theorems.tower.default_port`](../proofs/Proofs/Internal/Transport/StreamableHttpServer/Tower.lean) |
| T08 | `AllowedPort::matches` | `Any` and `Unspecified` match everything; `Exact(p)` matches exactly when the explicit port, or else the scheme's default port (T07), is `p`. | none | [`Theorems.tower.AllowedPort.matches`](../proofs/Proofs/Internal/Transport/StreamableHttpServer/Tower.lean) |

**SSRF address guard** — [`Internal/Transport/Auth.lean`](../proofs/Proofs/Internal/Transport/Auth.lean)
(private associated functions of `AuthorizationManager`). Used by (all rows): the OAuth
metadata-URL SSRF check `is_allowed_metadata_url` (A06 below) and the resolved-address filter
`AddressClass::of` (`auth/metadata_resolver.rs`, N01).

| ID | Rust function | Guarantee | Assumptions | Lean theorem |
| --- | --- | --- | --- | --- |
| A02 | `is_disallowed_metadata_ipv4` | `true` exactly for addresses in `10/8`, `172.16/12`, `192.168/16`, `127/8`, `169.254/16`, `255.255.255.255`, `0.0.0.0`, `224/4`, `0/8`, `100.64/10`, `198.18/15`; `240.0.0.0/4` is not blocked (bug H8). | none | [`Theorems.auth.AuthorizationManager.is_disallowed_metadata_ipv4`](../proofs/Proofs/Internal/Transport/Auth.lean) |
| A01 | `embedded_ipv4` | `Some` of the IPv4 address carried in IPv4-mapped `::ffff:0:0/96`, NAT64 `64:ff9b::/96`, IPv4-compatible `::/96` (except `::`, `::1`) or 6to4 `2002::/16` form; `None` otherwise. | none | [`…AuthorizationManager.embedded_ipv4`](../proofs/Proofs/Internal/Transport/Auth.lean) |
| A03 | `is_disallowed_metadata_ipv6` | A02's verdict on the carried IPv4 address if A01 finds one; otherwise `true` exactly for `::1`, `::`, `ff00::/8`, `fe80::/10`, `fc00::/7`, `2001::/32`, `64:ff9b:1::/48`. | none | [`…AuthorizationManager.is_disallowed_metadata_ipv6`](../proofs/Proofs/Internal/Transport/Auth.lean) |
| C04 | A01, A03, A02 | `is_disallowed_metadata_ipv6(a)` is the same computation as `is_disallowed_metadata_ipv4(v)`. | `embedded_ipv4(a)` returned `Some(v)` | [`…is_disallowed_metadata_ipv6_eq_of_embedded_ipv4_eq_ok_some`](../proofs/Proofs/Internal/Transport/Auth.lean) |
| C04 | A03 (corollary) | An IPv6 address that writes a blocked IPv4 address in mapped, NAT64, compatible or 6to4 form is blocked. | the IPv4 address is blocked (A02 list); the form | [`…is_disallowed_metadata_ipv6_of_ipv4Disallowed`](../proofs/Proofs/Internal/Transport/Auth.lean) |

**OAuth metadata-URL and issuer checks (patch 06)** —
[`Internal/Transport/Auth/AuthMetadata.lean`](../proofs/Proofs/Internal/Transport/Auth/AuthMetadata.lean)
(private functions of `AuthorizationManager`; 81 statements, signed off and proved 2026-11-27;
readable model `Defs.AuthMetadata`). The main guarantee per target is below; the file also has the
failure companions (showing where each premise is needed), the laws of the model and the compositions
(e.g. every URL `resolve_resource_metadata_url` returns is HTTP(S) and same-origin or allowed by
A06, and never an `https` downgrade). Assumption keys as in the file: **(U)** string arguments are
UTF-8, **(B)/(T)/(C)** URL hosts are UTF-8, **(S)/(D)** strings fit in memory, **(R)** a received issuer is UTF-8 when one was recorded, **(H)** an
`http`/`https` base URL (decision AD8, no-failure statements only), **(AD7)** a discovery URL of
at most `u32::MAX` bytes (no-failure statements only). Bugs H9–H16: formal/README.md "Bugs found".

| ID | Rust function | Guarantee | Assumptions | Lean theorem |
| --- | --- | --- | --- | --- |
| A04 | `is_http_url` | `true` exactly for an `http`/`https` URL with a host. | none | [`…AuthorizationManager.is_http_url`](../proofs/Proofs/Internal/Transport/Auth/AuthMetadata.lean) |
| A05 | `is_disallowed_metadata_host` | `true` exactly for a cloud-metadata name (three names, H16), a `localhost` name, or an IP literal whose class (N01) is not `Public` (H11). | (U) | [`…AuthorizationManager.is_disallowed_metadata_host`](../proofs/Proofs/Internal/Transport/Auth/AuthMetadata.lean) |
| A06 | `is_allowed_metadata_url` | `false` unless HTTP(S) with a host; a disallowed host (A05) is allowed only if it is a `Private` literal with `allow_private` (H10) or a loopback host from a loopback base; any other host is allowed (H12: refuses some IP-literal targets, and a `localhost` name from an IPv6-embedded `127/8` base, that the resolver accepts; never looser for IP literals). | (T), (B) | [`…AuthorizationManager.is_allowed_metadata_url`](../proofs/Proofs/Internal/Transport/Auth/AuthMetadata.lean) |
| A07 | `resolve_resource_metadata_url` | `Some u` exactly for the trimmed value parsed (or joined to the base) to an HTTP(S) URL that is same-origin, or not an `https` downgrade and allowed by A06; else `None`. | (H), (B), (C) | [`…AuthorizationManager.resolve_resource_metadata_url`](../proofs/Proofs/Internal/Transport/Auth/AuthMetadata.lean) |
| A08 | `check_authorization_response_issuer` | The RFC 9207 check: `AuthorizationFailed` if no issuer was recorded but one is required or received; `MissingIssuer` if required and absent; `Mismatch` with both strings unless byte-identical. | (S), (R) | [`…AuthorizationManager.check_authorization_response_issuer`](../proofs/Proofs/Internal/Transport/Auth/AuthMetadata.lean) |
| A09 | `check_authorization_metadata_issuer` | Compares the metadata issuer with the explicit or derived (RFC 8414 / OIDC form) expected issuer up to a root `/` (H15): `MissingIssuer` if the metadata has none (unless `allow_missing_issuer`), `Mismatch` with both strings if they differ (H9: recorded issue under private disclosure). | (U), (S), (D), (AD7) | [`…AuthorizationManager.check_authorization_metadata_issuer`](../proofs/Proofs/Internal/Transport/Auth/AuthMetadata.lean) |
| A10 | `check_resource_metadata_resource` | `MissingResource`, `ResourceNotAUrl`, `ResourceHasFragment`, `ResourceMismatch` in that order; `Ok` iff it parses as a URL without fragment that is valid for the base (H13). | (S) | [`…AuthorizationManager.check_resource_metadata_resource`](../proofs/Proofs/Internal/Transport/Auth/AuthMetadata.lean) |

**SEP-2243 header-value encoding (patch 07)** —
[`Internal/Transport/Common/McpHeaders.lean`](../proofs/Proofs/Internal/Transport/Common/McpHeaders.lean)
(private functions of `transport/common/mcp_headers.rs`; 39 statements, signed off and proved
2026-11-28; readable model `Defs.McpHeaders`). The file also has the failure companions, the laws
of the model and the compositions (round trip, header safety, unchanged exactly when not wrapped,
the 77 `tchar`s, exactly which header values decode). Assumption keys as in the file: **(E)** the
wrapped value fits in `isize::MAX` bytes (corollary (E'): length at most `isize::MAX / 2`),
**(U)** a value that is not a Base64 sentinel is UTF-8 (approved conditional form; corollary
(U*): UTF-8), **(D)** the decode buffer fits (corollary (D'): length at most `isize::MAX`). Bugs
H17–H18: formal/README.md "Bugs found".

| ID | Rust function | Guarantee | Assumptions | Lean theorem |
| --- | --- | --- | --- | --- |
| G01 | `requires_base64` | `true` exactly for a non-empty value with a leading or trailing SP/HTAB, a byte outside printable ASCII, or the sentinel shape `=?base64?`…`?=`. | none | [`Theorems.mcp_headers.requires_base64`](../proofs/Proofs/Internal/Transport/Common/McpHeaders.lean) |
| G02 | `is_tchar` | `true` exactly for the 77 RFC 9110 `tchar`s (VCHAR minus the 17 delimiters). | none | [`Theorems.mcp_headers.is_tchar`](../proofs/Proofs/Internal/Transport/Common/McpHeaders.lean) |
| G03 | `encode_header_value` | the value unchanged if G01 is `false`, else `=?base64?` + padded standard Base64 + `?=`; never rejected by `HeaderValue::from_str`; injective; panics exactly when the wrapped value exceeds `isize::MAX` bytes. | (E) | [`Theorems.mcp_headers.encode_header_value`](../proofs/Proofs/Internal/Transport/Common/McpHeaders.lean) |
| G04 | `decode_header_value` | for a sentinel, `Some` of the decoded value if it is strict padded standard Base64 of UTF-8, else `None`; any other value unchanged; decoding an encoded value gives it back (H17: accepts more than the encoder produces). | (U), (D) | [`Theorems.mcp_headers.decode_header_value`](../proofs/Proofs/Internal/Transport/Common/McpHeaders.lean) |

**Request-state codec, Phase 1 (patched copy)** —
[`Internal/Model/RequestState.lean`](../proofs/Proofs/Internal/Model/RequestState.lean)
(private associated functions of `RequestStateCodec`; E09a `rs1_fallbacks_verify` exists only in
the patched copy: patch 01 moves the rs1 fallback loop of `open_rs1_at` into it). The callers in
"Used by" are the public wrappers `open`/`open_with` (through `open_at`; verified as R07, R08),
`try_new` (verified as R06), `seal`/`seal_with` (through the private `seal_at`, translated with
patch 03; verified as R09, R10 through R10a) and `new_with_keyring` (verified as R15).
Assumption keys (the same in the file's docstring): **(T)** the MAC transcript fits in
`usize::MAX` bytes; **(C)** the `with_capacity` sum of the token (version, dots, Base64 lengths)
is at most `isize::MAX` bytes, the largest Rust `String` (`ExtModel.maxStringBytes`); **(D)** the
token has fewer than `usize::MAX` dots; **(F)** every rs1 fallback id is a key id: of the codec
(`CodecFallbacksKnown`, a keyring invariant that the keyring constructors establish: R15, R11,
R12 preserve `CodecValid`) for E09 and
E11, of the arguments (`FallbacksKnown`) for E09a; **(R1)**, **(R2)** the round-trip premises in
the S15 rows. `ad` is the associated data. HMAC means HMAC-SHA256 under `key` (opaque model).

| ID | Rust function | Guarantee | Assumptions | Lean theorem | Used by |
| --- | --- | --- | --- | --- | --- |
| E11 | `open_at` | Exactly `Defs.CodecState.openAt`: a token whose first `.`-component is `rs1` goes to E09, `rs2` to E10, anything else gives `MalformedFormat`. | (T); (F) for `rs1` tokens | [`Theorems.request_state.RequestStateCodec.open_at`](../proofs/Proofs/Internal/Model/RequestState.lean) | `open`, `open_with` |
| E07 | `seal_rs1` | Returns `"rs1." + b64(body) + "." + b64(tag)`, `tag` the HMAC of `transcriptV1(ad, body)`. | (T), (C) | [`…RequestStateCodec.seal_rs1`](../proofs/Proofs/Internal/Model/RequestState.lean) | `seal`, `seal_with` |
| E08 | `seal_rs2` | Returns `"rs2." + b64(kid) + "." + b64(body) + "." + b64(tag)`, `tag` the HMAC of `transcriptV2(kid, ad, body)`; any kid is accepted. | (T), (C) | [`…RequestStateCodec.seal_rs2`](../proofs/Proofs/Internal/Model/RequestState.lean) | `seal`, `seal_with` |
| E09 | `open_rs1_at` | Exactly `openRs1`: `MalformedFormat`, `UnknownKeyId` (keyring without rs1 fallback), `InvalidEncoding`, `IntegrityCheckFailed`, in the error order of plan Section 3, then E01 on the body. | (D), (T), (F) | [`…RequestStateCodec.open_rs1_at`](../proofs/Proofs/Internal/Model/RequestState.lean) | `open`, `open_with` |
| E09a | `rs1_fallbacks_verify` (patch-only, no upstream counterpart) | `true` exactly when some rs1 fallback key verifies the tag over the transcript. | (F) (else the code's `expect` panics; not proved) | [`…RequestStateCodec.rs1_fallbacks_verify`](../proofs/Proofs/Internal/Model/RequestState.lean) | `open_rs1_at` (E09) in the patched copy, hence `open`, `open_with` |
| E10 | `open_rs2_at` | Exactly `openRs2` (malformed token, kid checks, unknown kid, encoding, integrity, in the error order of plan Section 3, then E01), for every codec. | (D), (T) | [`…RequestStateCodec.open_rs2_at`](../proofs/Proofs/Internal/Model/RequestState.lean) | `open`, `open_with` |
| E01 | `open_authenticated_body` | `MalformedFormat` below 8 bytes; otherwise `Expired` if the expiry (first 8 bytes, signed big-endian) is non-zero and `now_ms` is later; otherwise `Ok` of the bytes after the first 8. | none | [`…RequestStateCodec.open_authenticated_body`](../proofs/Proofs/Internal/Model/RequestState.lean) | `open`, `open_with` |
| E03 | `validate_key_length` | `Ok(())` exactly when the key has at least 32 bytes, otherwise `KeyTooShort { minimum: 32, actual: key.len() }`. | none | [`…RequestStateCodec.validate_key_length`](../proofs/Proofs/Internal/Model/RequestState.lean) | `try_new`, `new_with_keyring` |
| E04 | `validate_config_kid` | `Ok(())` exactly when the kid has 1 to 255 UTF-8 bytes; `InvalidKeyring` with `KID_EMPTY_MSG` for 0 bytes, with `KID_TOO_LONG_MSG` above 255. | none | [`…RequestStateCodec.validate_config_kid`](../proofs/Proofs/Internal/Model/RequestState.lean) | `new_with_keyring` |
| E02 | `b64_len` | Returns `4 * ((len + 2) / 3)`. | that value fits in `usize` | [`…RequestStateCodec.b64_len`](../proofs/Proofs/Internal/Model/RequestState.lean) | `seal`, `seal_with` |
| S15 | `rs1_roundtrip` | `seal_rs1(key, ad, body)` does not panic, and opening its token (any `str` with its bytes) with `open_rs1_at(self, ·, ad, now_ms)`, with the same associated data `ad`, gives `Ok(body[8..])`. | (R1): (T), (C), body ≥ 8 bytes and not expired at `now_ms`, `key` is the codec's single key or the key of one of its rs1 fallback ids, (F) | [`…RequestStateCodec.rs1_roundtrip`](../proofs/Proofs/Internal/Model/RequestState.lean) | `seal` then `open` |
| S15 | `rs2_roundtrip` | `seal_rs2(kid, key, ad, body)` does not panic, and opening its token (any `str` with its bytes) with `open_rs2_at(self, ·, ad, now_ms)`, with the same associated data `ad`, gives `Ok(body[8..])`. | (R2): (T), (C), body ≥ 8 bytes and not expired at `now_ms`, `kid` is UTF-8 of 1–255 bytes and the codec is a keyring that maps it to `key` | [`…RequestStateCodec.rs2_roundtrip`](../proofs/Proofs/Internal/Model/RequestState.lean) | `seal` then `open` |
| S15 | `open_at_roundtrip_rs1` | As `rs1_roundtrip`, opening with `open_at(self, ·, ad, now_ms)`, with the same associated data `ad`. | (R1) | [`…RequestStateCodec.open_at_roundtrip_rs1`](../proofs/Proofs/Internal/Model/RequestState.lean) | `seal` then `open` |
| S15 | `open_at_roundtrip_rs2` | As `rs2_roundtrip`, opening with `open_at(self, ·, ad, now_ms)`, with the same associated data `ad`. | (R2) | [`…RequestStateCodec.open_at_roundtrip_rs2`](../proofs/Proofs/Internal/Model/RequestState.lean) | `seal` then `open` |
| R10a | `seal_at` (private; translated with patch 03) | At an explicit time `now_ms`, the token's UTF-8 bytes are `Defs.CodecState.sealAt` of the payload, associated data and time-to-live (expiry `now_ms` plus the TTL in whole milliseconds, clamped to `i64`; `rs1` for a single key or an rs1 seal mode, `rs2` otherwise). | the seal-mode key id is a key id; `SealFits` (transcript within `usize::MAX`, capacity within `isize::MAX`); inherited exceptions (H), (V) | [`…RequestStateCodec.seal_at`](../proofs/Proofs/Internal/Model/RequestState.lean) | `seal`, `seal_with` |
| R10b | `seal_at_roundtrip` | `seal_at(self, payload, options, now)` does not panic, and opening its token (any `str` with its bytes) with `open_at(self, ·, ad, now')`, with the same associated data, gives `Ok(payload)`. | `CodecValid`; an rs1 seal-mode id is an rs1 fallback; `SealFits`; not expired at `now'`; inherited exceptions (H), (V) | [`…RequestStateCodec.seal_at_roundtrip`](../proofs/Proofs/Internal/Model/RequestState.lean) | `seal` then `open` |
| — | `openAt_eq_ok_of_sealAt_eq_some` (model round trip, no translated function) | `openAt` of a `sealAt` token with the same associated data at a time where it has not expired is `Ok(payload)`. | `CodecValid`; an rs1 seal-mode id is an rs1 fallback; not expired | [`Theorems.request_state.openAt_eq_ok_of_sealAt_eq_some`](../proofs/Proofs/Internal/Model/RequestState.lean) | — |

**Wire functions, Phase 1 (patch-only)** —
[`Internal/Model/RequestStateWire.lean`](../proofs/Proofs/Internal/Model/RequestStateWire.lean)
(`pub` only in the module `request_state_wire` that patch 01 adds; not upstream API). "Used by"
names the callers in the patched copy (patch 01); through them the wire functions serve seal and
open of request-state tokens. Theorem names are `Theorems.request_state_wire.<function>`.

| ID | Rust function | Guarantee | Assumptions | Lean theorem | Used by |
| --- | --- | --- | --- | --- | --- |
| W01 | `b64_len` | Returns `4 * ((len + 2) / 3)`. | that value fits in `usize` | [`Theorems.request_state_wire.b64_len`](../proofs/Proofs/Internal/Model/RequestStateWire.lean) | `b64_len` (E02): `seal_rs1`, `seal_rs2` (patched copy) |
| W02 | `key_length_ok` | `true` exactly when `len ≥ 32`. | none | [`Theorems.request_state_wire.key_length_ok`](../proofs/Proofs/Internal/Model/RequestStateWire.lean) | `validate_key_length` (E03): `try_new`, `new_with_keyring` (patched copy) |
| W03 | `check_kid_len` | `Err(Empty)` exactly for 0, `Err(TooLong)` exactly above 255, `Ok(())` otherwise. | none | [`Theorems.request_state_wire.check_kid_len`](../proofs/Proofs/Internal/Model/RequestStateWire.lean) | `open_rs2_at`, `validate_config_kid` (patched copy) |
| W04 | `bytes_eq` | `true` exactly when the two slices are equal byte lists. | none | [`Theorems.request_state_wire.bytes_eq`](../proofs/Proofs/Internal/Model/RequestStateWire.lean) | `version_of`, `parse_rs1`, `parse_rs2` (W07–W09) |
| W05 | `next_dot` | The least index `≥ start` holding `.`, or `s.len()` if there is none. | none | [`Theorems.request_state_wire.next_dot`](../proofs/Proofs/Internal/Model/RequestStateWire.lean) | `version_of`, `parse_rs1`, `parse_rs2` (W07–W09) |
| W06 | `component_count` | The number of `.`-separated components, one more than the number of `.` bytes. | fewer than `usize::MAX` dots | [`Theorems.request_state_wire.component_count`](../proofs/Proofs/Internal/Model/RequestStateWire.lean) | `parse_rs1`, `parse_rs2` (W08, W09) |
| W07 | `version_of` | `Some(V1)` exactly when the first component is `rs1`, `Some(V2)` when it is `rs2`, `None` otherwise. | none | [`Theorems.request_state_wire.version_of`](../proofs/Proofs/Internal/Model/RequestStateWire.lean) | `open_at` (E11, patched copy) |
| W08 | `parse_rs1` | `Some {body, tag}` exactly when the token splits on `.` into `["rs1", body, tag]`. | fewer than `usize::MAX` dots | [`Theorems.request_state_wire.parse_rs1`](../proofs/Proofs/Internal/Model/RequestStateWire.lean) | `open_rs1_at` (E09, patched copy) |
| W09 | `parse_rs2` | `Some {kid, body, tag}` exactly when the token splits on `.` into `["rs2", kid, body, tag]`. | fewer than `usize::MAX` dots | [`Theorems.request_state_wire.parse_rs2`](../proofs/Proofs/Internal/Model/RequestStateWire.lean) | `open_rs2_at` (E10, patched copy) |
| W10 | `transcript_v1` | Returns `DOMAIN_V1 ++ be64(len ad) ++ ad ++ body`. | result fits in `usize::MAX` bytes | [`Theorems.request_state_wire.transcript_v1`](../proofs/Proofs/Internal/Model/RequestStateWire.lean) | `seal_rs1`, `open_rs1_at` (E07, E09, patched copy) |
| W11 | `transcript_v2` | Returns `DOMAIN_V2 ++ be64(len kid) ++ kid ++ be64(len ad) ++ ad ++ body`. | result fits in `usize::MAX` bytes | [`Theorems.request_state_wire.transcript_v2`](../proofs/Proofs/Internal/Model/RequestStateWire.lean) | `seal_rs2`, `open_rs2_at` (E08, E10, patched copy) |
| W12 | `decode_expiry` | The signed (two's-complement) big-endian value of the 8 bytes. | none | [`Theorems.request_state_wire.decode_expiry`](../proofs/Proofs/Internal/Model/RequestStateWire.lean) | `open_frame` (W14) |
| W13 | `is_expired` | `true` exactly when `expiry ≠ 0` and `now_ms > expiry`. | none | [`Theorems.request_state_wire.is_expired`](../proofs/Proofs/Internal/Model/RequestStateWire.lean) | `open_frame` (W14) |
| W14 | `open_frame` | `TooShort` below 8 bytes; otherwise `Expired` if W13 holds for the first 8 bytes' value; otherwise `Ok(body[8..])`. | none | [`Theorems.request_state_wire.open_frame`](../proofs/Proofs/Internal/Model/RequestStateWire.lean) | `open_authenticated_body` (E01, patched copy) |
| W15 | `frame` | Returns `be64(expiry as u64) ++ payload`. | result fits in `usize::MAX` bytes | [`Theorems.request_state_wire.frame`](../proofs/Proofs/Internal/Model/RequestStateWire.lean) | `seal_at` (R10a; patched copy): `seal`, `seal_with` |
| — | `frame_roundtrip` | `open_frame(frame(expiry, payload), now_ms)` is `Ok(payload)`. | frame fits in `usize::MAX` bytes; `expiry` is 0 or `now_ms ≤ expiry` | [`Theorems.request_state_wire.frame_roundtrip`](../proofs/Proofs/Internal/Model/RequestStateWire.lean) | `seal_at` then `open_authenticated_body` (patched copy) |

**Laws of the trusted models** — [`Internal/External.lean`](../proofs/Proofs/Internal/External.lean)
(116 theorems `Theorems.External.*`). They state what the models in `formal/trusted/` compute
(Base64url round trip and canonicity, UTF-8, the HMAC/Base64 `prim` functions, `Option`,
`Result`, `str`, `String`, `HashMap`, `zeroize`, slices and ranges, `i64::from_str` equal to
`Defs.parseI64`, `Ipv4Addr`/`Ipv6Addr` predicates), so that a reviewer can compare them with the
Rust documentation. Used by: the proofs of all statements above.

## What you must trust

> - **Tools:** Charon `0.1.324`, Aeneas `nightly-2026.11.24-fb44cb4` and the Lean `v4.36.0`
>   kernel (since the Aeneas upgrade of 2026-11-24, reviewed and re-signed by the spec owner 2026-11-24);
>   the prebuilt Aeneas Lean library (archive digest checked) and Mathlib oleans (not
>   digest-checked).
> - **The translated configuration:** target `x86_64-unknown-linux-gnu`,
>   `--no-default-features --features request-state,server,client,client-side-sse,transport-streamable-http-server,transport-streamable-http-client,auth`,
>   `overflow-checks=true` and `debug-assertions=true` (overflow panics), Rust
>   `nightly-2026-09-17`, the Charon settings in `crates/rmcp/Cargo.toml`. Other targets,
>   features or release builds without overflow checks are not covered.
> - **Translation patch 01** (Phase 1 and R01–R08): the `request_state_wire` refactor on
>   `7caec76`, reviewed and signed off; its equivalence with the unpatched code is tested
>   (regression tests, about 2.9M differential `open` calls), not proved. Phase 2 uses no patch;
>   this rests on `scripts/check-original-linkage.sh` (the committed translation, generated from
>   the patched copy, equals block for block the translation of unmodified `7caec76` for the
>   Phase 2 targets): passes locally, CI pending (S22).
> - **Translation patch 03** (R09–R15): +6/−2 lines on the patch-01 copy (`let ttl = options.ttl;`
>   in `seal_at`, an explicit `match` in place of `.map_err(RequestStateError::Deserialization)`
>   in `open_json_with`), reviewed and signed off 2026-11-24; same computation, covered by the
>   existing tests and the boundary tests of the test-only patch 02, not proved.
> - **Translation patch 04** (K05–K07, K13–K16 of `skill.rs`): a private module `prim` of twelve
>   one-line wrappers, each the original expression (SHA-256, the `str` pattern APIs,
>   percent-encoding, NFKC), and hunks H1–H9 that call them or use loops without early return,
>   keeping the computed values; reviewed in 3 rounds and signed off 2026-11-25; not proved
>   equivalent to the unpatched code. It adds one behavioural difference that the statements take
>   as a premise (NFKC fits, above). K01–K04, K08–K12 and K17–K20 do not depend on it (linkage
>   `ORIGINAL`, checked by `scripts/check-original-linkage.sh` locally, CI pending).
> - **Translation patch 05** (N03–N07, N09–N11 of `metadata_resolver.rs`): a private opaque module
>   `prim` and the opaque newtype `Lookup`; the pure parts of `with_lookup`, `with_proxy_hosts` and
>   `resolve` split into helpers (`with_base_url`, `proxy_host`, `allowed_addresses`), which are
>   what is verified; the async shells are not. Not proved equivalent to the unpatched code
>   (differential tests). N01 and N08 do not depend on it (linkage `ORIGINAL`).
> - **Translation patch 06** (A04–A10 of `auth.rs`): a private opaque module `prim` (string helpers,
>   `str::trim`, the issuer-URL rewrite, the four tracing events with their original target) and
>   rewrites that keep the computed values. `AuthError` cannot be translated (a `Box<dyn Error>`
>   field), so the targets of A08/A09 are `check_*` helpers returning a private `IssuerError` with
>   the same three variants and payloads, and that of A10 a `check_*` helper taking the base URL;
>   the one-line `validate_*` wrappers (the map to `AuthError`, the `&self` reads) are unverified
>   glue. The tracing events' callsite metadata (module path, line) differs. Not proved equivalent
>   to the unpatched code: backed by the patch-02 boundary tests (decision AD5) and the review
>   differentials. Every A04–A10 target is `patch-06` (none `ORIGINAL`).
> - **Translation patch 07** (G01–G04 of `transport/common/mcp_headers.rs`): a private opaque
>   module `prim` (string helpers, the `format!` of the Base64 sentinel, `BASE64_STANDARD`
>   encode/decode, each the original expression) and rewrites that keep the computed values; the
>   quote check of `is_tchar` is written `c == char::from(b'\'')` because Aeneas prints `'\''`
>   as invalid Lean. Not proved equivalent to the unpatched code: backed by the patch-02 boundary
>   tests (decision GD3). Every G target is `patch-07`.
> - **Translation patch 08** (the elicitation schema builders X01–X75 of
>   `model/elicitation_schema.rs`; no statement yet): a private opaque module `prim` (the `format!`
>   of the titles-mismatch message, the map's sorted key list), `.to_owned()` error literals,
>   `iter().all` rewrites of two loops with an early return, and a translated helper for the enum
>   titles; it keeps every returned value.
>   Backed by the patch-02 boundary tests (decision XD8). X29, X32, X33, X35–X38, X40, X74, X75 are
>   `patch-08`, the other 65 targets `ORIGINAL`.
> - **The models in [`formal/trusted/`](../trusted/)** of the external functions (standard library,
>   `core::net`, integer parsing, HMAC-SHA256, Base64url, standard padded Base64 (an alphabet
>   renaming of the Base64url model, patch 07), `zeroize`, the `mcp_headers.rs` `prim` wrappers, and
>   for `skill.rs` the `prim` wrappers, `HashSet` and `serde_json::Map`, the latter as the
>   `BTreeMap` it is; for `elicitation_schema.rs` the `prim` wrappers, `BTreeMap` with an
>   `Ord`-driven `insert`, the byte order of `String` and a total `<str as Debug>::fmt`; the float
>   types `F64`, `F32` as opaque carriers that no statement inspects): definitions, structures and
>   26 `opaque` constants (patch 04 adds SHA-256,
>   NFKC and the Unicode General_Category, whose laws enter statements only as premises; patches 05
>   and 06 the abstract `url::Url` and its accessors, the DNS lookup, the proxy settings and the
>   issuer-URL rewrite; list in [`../README.md`](../README.md), "Trusted base"), no trusted axiom
>   (`axioms.lock` is empty). They do not appear in `#print axioms`; their fidelity rests on review
>   and their cited sources. Stated exceptions (`formal/trusted/Rmcp/FunsExternal.lean`, module
>   docstring, "Memory" and "Size convention"): the models make no claim about inputs of `2^61`
>   bytes or more, which cannot exist on `x86_64` (address space at most `2^57` bytes); in
>   particular HMAC's bit-length counter overflow (a message of at least `2^61 − 64` bytes or a key
>   of at least `2^61` bytes, equally impossible) and a `Vec` above `isize::MAX` bytes are not
>   modelled; allocation failure is not modelled. For such inputs a statement may promise a result
>   where Rust panics. The models also state representation choices that change no result of the
>   targets (`Arc` equality checks pointer equality first; `Ipv6Addr` as eight segments;
>   `MaybeUninit` partial initialisation; non-UTF-8 `Str` bytes; `HashMap::get` assumes `Hash`/`Eq`
>   agree; the clock is opaque): complete list in [`../README.md`](../README.md), "Stated exceptions
>   of the external models".
> - **The clock** (human decisions 2026-11-24, extended 2026-11-25; [`../README.md`](../README.md),
>   "Trusted base"): the clock is one opaque reading `ExtModel.nowMs`, which makes `open`,
>   `open_with`, `open_json`, `open_json_with`, `seal` and `seal_with` pure in the model. Only
>   their spec theorems (R07–R10, R13, R14), restatements and the corollaries of R08, R09 and R10
>   may name these functions and `ExtModel.nowMs`, and only with the postconditions
>   `resultBytes result = openAt … nowMs` (`open*`), the `openAt … nowMs` error unchanged or else
>   the `from_slice` outcome mapped `Err` → `Deserialization` (`open_json*`), and
>   `sealAt … nowMs = some (utf8 result)` (`seal*`; `sealAt` is the model of `seal_at`); no
>   statement constrains the value of the reading or relates two readings (R10a and R10b use
>   explicit times). The model of
>   `now_ms` always returns, while Rust's `Utc::now` panics for a clock before 1970 or outside
>   chrono's range (exception (K)).
> - **No native-code assumption** since the Aeneas upgrade of 2026-11-24:
>   [`formal/trusted/native-axioms.lock`](../trusted/native-axioms.lock) is empty, because the
>   `toStr` of `nightly-2026.11.24-fb44cb4` checks the length of a string literal in the kernel.
>   Until then 35 were locked: the side conditions of the Aeneas `toStr` of string literals,
>   decided by compiled code (5 for Phase 1, one of which R07, R08 and the R08 corollary also
>   reached; 30 for the method names and `"http"`/`"https"` of T05–T08 and C05).
> - **The translation pin** [`formal/trusted/translation-pins.txt`](../trusted/translation-pins.txt)
>   (S21): the sha256 of the generated `Funs.lean` and the one line where `lean-guard.sh sources`
>   excuses a metaprogramming word (the T06 literal `"initialize"`); a trusted file.
> - **The statements themselves** (this directory, `../proofs/Proofs/Internal/`) and the
>   definitions they use (`Defs/`, `../proofs/Proofs/Defs/`). `Specs` imports `Proofs`, so a
>   reviewer also checks `proofs/` for instances or notation that change a statement's meaning.
>
> Details: [`../README.md`](../README.md), "Trusted base".

## Not covered

- The callers of the verified functions: the service loop, the client handshake, the SSE stream
  wrapper `bounded_sse_stream`, `AsyncRwTransport` and `JsonRpcMessageCodec`,
  `origin_is_allowed`, `is_allowed_metadata_url`, `AddressClass::of`,
  `MetadataAddressResolver::is_allowed`.
- URL and HTTP parsing (`Origin` and `Host` headers, `url::Url`), `async` code, DNS resolution.
- 2 of the 17 public functions of `request_state.rs` (status in
  [`../README.md`](../README.md), "Results"):
  `seal_json`, `seal_json_with` (R16–R17, excluded, blocked upstream: Aeneas does not support the
  mutually recursive `serde_core::ser` traits; once that is fixed they would additionally need the
  variant-constructor workaround of patch 03 hunk 2, since
  `.map_err(RequestStateError::Serialization)` hits "Arrow types are not supported yet" at
  `request_state.rs` 133:4-133:46 / 461:4-468:5 of the patched copy).
- Statements relating two clock readings (for example `seal` then `open` at a later time: R10b
  and the model round trip state it at explicit times only). The codec-state premises (F) and
  `CodecValid` are derived for the codecs the verified constructors build (R04–R06, R15, and
  R11/R12 preserve them), but stay premises of the internal statements.
- Cryptographic security (HMAC unforgeability), constant-time behaviour, the correctness of the
  `hmac`, `sha2`, `base64` and `zeroize` crates; negative round trips (a tampered token is
  rejected).
- For `skill.rs`: the serialisation impls (`Serialize`/`Deserialize`, `JsonSchema`), the
  `Display`/`Error` impls of its error types, and the correctness of the `sha2`,
  `unicode-normalization`, `unicode-general-category` and `percent-encoding` crates (SHA-256, NFKC
  and General_Category are opaque; no statement assumes collision freedom); the "not covered"
  cases of the skills table (caller side effects, SHA-256 at `2^61` bytes, the `HashSet` random
  source, the `serde_json` feature `preserve_order`).
- Allocation failure, and inputs covered by the stated exceptions above (for those a statement
  may promise a result where Rust panics).
- The full MCP protocol: the method lists are core protocol only (extensions are out of scope),
  and the other functions of the touched files, including those measured and not taken (plan
  Section 16.5).

**Bugs found** (recorded in [`../README.md`, "Bugs found"](../README.md#bugs-found);
the statements describe the code as it is):

- **H7:** `is_standard_method` / `is_standard_notification` (`async_rw.rs`) miss six core MCP
  names (`tasks/get`, `tasks/result`, `tasks/cancel`, `tasks/list`,
  `notifications/tasks/status`, `notifications/elicitation/complete`): when such a line fails
  to deserialize but parses as JSON with a string `method`, it is dropped instead of reported:
  always for the two notifications, and for the four `tasks/*` requests when the line has no
  `id`.
- **H8:** `is_disallowed_metadata_ipv4` (`auth.rs`) does not block the reserved range
  `240.0.0.0/4` (except `255.255.255.255`), so such an address passes the metadata-URL SSRF
  check and the resolved-address filter.
