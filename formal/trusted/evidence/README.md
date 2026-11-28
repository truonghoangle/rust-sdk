# Evidence for the external models (plan steps S08–S09, S26–S27) and the Phase 2 test map (S34)

`formal/trusted/Rmcp/TypesExternal.lean` and `FunsExternal.lean` model every external of the
translation, i.e. every type and function that Charon did not translate: those of other crates
and of the standard library, and the opaque `rmcp` items (the four `prim` functions and
`RequestStateCodec::now_ms`); 41 externals, inventory in the S04a evidence (git history at 223ff12). Since
S08–S09 **they declare no axiom**: each type is a `structure`, each function a definition with
the generated name and signature, keeping the template's `@[rust_type]` or `@[rust_fun]`
attribute where it has one (the five opaque `rmcp` functions have none). What the models
cannot compute is an `opaque` constant, which adds no axiom (`#print axioms` does not list it):

| Opaque constant | Stands for | Why it is not computed |
|---|---|---|
| `ExtModel.hmacSha256 : List U8 → List U8 → Array U8 32` | HMAC-SHA256 (RFC 2104, FIPS 180-4) | correctness of the `hmac`/`sha2` crates is out of scope (plan Section 4) |
| `ExtModel.sipHash13 : U64 → U64 → List U8 → U64` | SipHash-1-3 of `DefaultHasher` | no statement depends on hash values (`HashMap::get` is modelled without hashing) |
| `ExtModel.nowMs : I64` | the clock reading of `now_ms` | not a function of anything the model has |
| `ExtModel.SerdeJsonErrorImpl : Type` | the boxed content of `serde_json::Error` | never inspected. Until translation patch 03 an `opaque` type, never created; since then (reviewed and signed off by the spec owner 2026-11-24) a `def` over the opaque carrier `ExtModel.SerdeJsonErrorImplCarrier` (below), known to be inhabited, which may occur only inside the opaque outcome `ExtModel.serdeJsonFromSlice` |
| `ExtModel.SerdeJsonValue : Type` | `serde_json::Value` (Phase 2, S26/S27) | the translated code only moves values of this type |
| `ExtModel.randomState : RandomState` (translation patch 03, signed off 2026-11-24) | the keys `HashMap::new` stores (`RandomState::new`) | random per thread and incremented per map in Rust; no model hashes for a lookup |
| `ExtModel.serdeJsonFromSlice` (translation patch 03, signed off 2026-11-24) | the outcome of `serde_json::from_slice::<T>` | depends on the caller's `Deserialize` impl and the `serde_json` parser, not translated |
| `ExtModel.SerdeJsonErrorImplCarrier : NonemptyType` (translation patch 03, signed off 2026-11-24) | the carrier of `ExtModel.SerdeJsonErrorImpl` | not inspected; nonempty so that `serdeJsonFromSlice` can return `Err` |

This follows the human decision of 2026-11-23 to convert every placeholder axiom into a
definition (plan Section 4). Because there is no axiom, the consistency models of the earlier
design (`formal/proofs/Proofs/Consistency/`) are unnecessary: a definition cannot prove `False`, and
`trusted/axioms.lock` stays empty. The Base64 laws that the plan expected as axioms are theorems
(`formal/proofs/Proofs/External/Base64.lean`). What remains to be trusted about each model is
that it describes the Rust function; the source each one encodes is cited below (and in its
docstring), and the Rust tests that exercise it are listed. The tests catch a mismatched model;
they are not a proof. All tests named in the Phase 1 sections are in the crate's own test modules
and run with
`cargo test -p rmcp --no-default-features --features request-state --lib model::request_state`
(the Phase 2 map below records its own commands).

Source paths: `rust-src` is
`library/` of the pinned toolchain `nightly-2026-09-17` (since the Aeneas upgrade of 2026-11-24;
the runs recorded below used `nightly-2026-06-01`); crate paths are in
`~/.cargo/registry/src/index.crates.io-*/`, at the versions pinned by
`scripts/aeneas-translate.sh` (`hmac 0.13.0`, `sha2 0.11.2`, `base64 0.23.1`, `digest 0.11.3`,
`zeroize 1.9.2`, `chrono 0.4.45`, `serde_json 1.0.154`; plan Section 4), and std's
`hashbrown 0.17.1` per the toolchain's `library/Cargo.lock`. Test files: `wire` = `crates/rmcp/src/model/
request_state_wire.rs`, `codec` = `crates/rmcp/src/model/request_state.rs`, both in the patched
copy (patch 01 on origin/main 7caec76, `formal/trusted/patches/01-request-state-wire.patch`, D2
fallback 2026-11-23): `request_state_wire.rs` and every test named here that the patch adds exist
only there, so run the command above in `.llbc/work/crates/rmcp` after
`scripts/apply-patches.sh` (as `patched-tests.yml` does).

## HMAC (`prim::hmac_sha256`, `prim::hmac_sha256_verify`)

- **Model.** `hmac_sha256 k m = ok (hmacSha256 k m)`; `hmac_sha256_verify k m t = ok (t =
  hmacSha256 k m)` as byte lists.
- **Source.** `Hmac::<Sha256>::new_from_slice` returns `Ok` for every key length
  (`hmac-0.13.0/src/block_api.rs` lines 53–69, key reduced by `get_der_key`), so the `expect`
  never panics. `Mac::verify_slice` (`digest-0.11.3/src/mac.rs` lines 139–146) returns `Err`
  when `tag.len() != 32` and otherwise compares in constant time (timing not modelled).
- **Tests.** `wire::rfc4231_hmac_sha256_vectors` (RFC 4231 cases 1–7 through both functions,
  flipped tag rejected, case 5's truncated tag rejected by `verify`);
  `wire::hmac_sha256_verify_rejects_wrong_length_tags` (empty, 31-byte and 33-byte tags
  rejected; empty key accepted); `wire::transcripts_match_incremental_hmac`;
  `codec::rs1_known_answer_is_unchanged`, `codec::rs2_known_answer_matches_wire_specification`;
  `wire::s16_prim_rfc4231_verify_accepts_only_the_exact_tag` (S16: for RFC 4231 cases 1–4, 6,
  7 only the exact tag is accepted; prefixes, an extension, flipped bytes and the other
  cases' tags are rejected).
- **Stated exception (not modelled).** SHA-256 finalisation computes the bit length as a `u64`
  (`sha2-0.11.2/src/block_api.rs` line 66), which overflows (a panic under `overflow-checks`)
  when the hashed input reaches `2^61` bytes: for a message of at least `2^61 − 64` bytes (inner
  hash of the 64-byte key block and the message) and for a key of at least `2^61` bytes
  (`get_der_key`, `hmac-0.13.0/src/utils.rs` lines 9–32, hashes a key longer than 64 bytes).
  Both lie outside the size convention of `FunsExternal.lean` (no claim about inputs of at least
  `2^61` bytes; unreachable on `x86_64`, whose address space is at most `2^57` bytes).
- **Not established.** That `hmacSha256` is HMAC-SHA256; cryptographic security; constant time.

## Base64url without padding (`prim::b64_encode_into`, `prim::b64_decode`)

- **Model.** Concrete encoder `ExtModel.b64` and strict decoder `ExtModel.b64Decode` over
  `List U8`. `b64_encode_into x out` appends the symbols of `b64 x` to `out` (subject to the
  `String` limit below); `b64_decode x = ok (b64Decode x)`.
- **Source.** `URL_SAFE_NO_PAD = GeneralPurpose::new(&alphabet::URL_SAFE, NO_PAD)`
  (`base64-0.23.1/src/engine/general_purpose/mod.rs` line 472); `URL_SAFE` alphabet
  `A–Z a–z 0–9 - _` (`src/alphabet.rs` lines 259–262); `NO_PAD` = no padding on encode and
  `DecodePaddingMode::RequireNone` (lines 499–501); `decode_allow_trailing_bits = false` by
  default (line 341). Decoding: `decode_helper` and `complete_quads_len`
  (`src/engine/general_purpose/decode.rs`; `=` is not in the decode table, so it is
  `InvalidByte` in a non-final quad) and `decode_suffix`
  (`src/engine/general_purpose/decode_suffix.rs`: padding rejected under `RequireNone`, one
  leftover symbol is `InvalidLength`, set trailing bits are `InvalidLastSymbol`).
  Encoding: `Engine::encode_string` (`src/engine/mod.rs` lines 188–201) through
  `ChunkedEncoder` (`src/chunked_encoder.rs`, 768-byte chunks, `push_str` of ASCII).
- **Proved** (`formal/proofs/Proofs/External/Base64.lean`): `b64Decode (b64 x) = some x`;
  `b64Decode s = some y ↔ b64 y = s` (so padding, foreign bytes, length `≡ 1 (mod 4)` and
  non-canonical trailing bits are rejected); every output byte is in the URL-safe alphabet (in
  particular never `.`); `(b64 x).length = (4n + 2) / 3`, `≤ Defs.Wire.b64Len n`, with equality
  when `3 ∣ n`; the RFC 4648 Section 10 vectors and every case of the Rust tests below, by
  `decide` (kernel evaluation, no `native_decide`).
- **Tests.** `wire::rfc4648_base64url_vectors`, `wire::base64url_alphabet_and_append`,
  `wire::base64url_decode_is_strict`, `wire::base64url_roundtrip` (all 256 prefixes of
  `0..=255`, alphabet and round trip), `wire::b64_len_matches_encoder_output_length`;
  `codec::non_base64_sections_are_invalid_encoding`,
  `codec::parser_rejects_invalid_tokens_and_unavailable_keys`; added by S16 (their cases are
  not, in general, proved by `decide` above): `wire::s16_prim_rfc4648_sec10_padded_forms_rejected`,
  `wire::s16_prim_rfc4648_standard_alphabet_rejected`,
  `wire::s16_prim_rfc4648_noncanonical_trailing_bits_rejected`.
- **Not established.** That the crate has no bug outside the tested inputs (the model is the
  RFC 4648 definition; the tests compare the crate with it on the vectors).

## Differential check (Base64url and UTF-8)

(The subdirectory `differential/metadata-resolver/` is a different check, Rust against Rust:
translation patch 05 against the original code; see "Address-policy externals".)
`differential/` compares the Lean models with the Rust crates line by line, outside any build or
CI job: `Diff.lean.in` (run with `lake env lean --run`; the extension keeps it out of the
`formal/` source checks, since it needs a root-level `main`) prints the results of
`b64_encode_into`, `b64_decode`, `String::from_utf8` (with `as_bytes`) and `as_bytes` of Lean
strings; `rdiff/` (`base64 = "=0.23.1"`, std) prints the same for `URL_SAFE_NO_PAD.encode_string`
(into an empty and a non-empty `String`), `URL_SAFE_NO_PAD.decode`, `String::from_utf8` and
`String::as_bytes`; `gen.py` writes the inputs with seed `random.Random(20261123)` (random byte
strings, mutated encodings with padding, foreign bytes, wrong lengths and non-canonical trailing
symbols, random and adversarial UTF-8 including overlong forms, surrogates, code points above
`U+10FFFF` and truncations) and, for the long inputs added in fix round 3, a second stream
`random.Random(20261124)`: encodings of byte strings around the 768-byte chunk of
`ChunkedEncoder` and its double (lengths 760–776 and 1530–1544), of 2300–2309 and 2990–3010
bytes (several chunks), and around the 24-byte (32-symbol) steps of the encoder's fast loop
(`24k − 1`, `24k`, `24k + 1` for `k` = 1..11), each with random, all-`0xff` and all-zero
content; and decoder inputs of up to 400 symbols (encodings of 1–300 bytes, past the decoder's
32-symbol unrolled steps), valid, with padding, an extra or a missing symbol, a changed last
symbol (trailing bits), and a foreign byte replacing or inserted at a position among the last 40
symbols. `run.sh` adds exhaustive ranges (every byte string of length ≤ 3 encoded; every byte
string of length ≤ 2 and every 3-byte string with a lead byte ≥ `0x80` through `from_utf8`). It
copies `rdiff/` into the scratch directory and builds it there with `cargo build --locked` from
the committed `rdiff/Cargo.lock` (`base64 0.23.1`, crates.io checksum), so it writes nothing in
the source tree, and records the `cargo`, `rustc` and `python3` versions in
`<scratch>/toolchain.txt`. The script is archived in git history at 9047c72; to re-run it,
restore it and then, from the repository root, after `cd formal && lake build RmcpExternal`:

```
git checkout 9047c72 -- formal/trusted/evidence/differential
formal/trusted/evidence/differential/run.sh formal <new scratch directory>
```

Result (2026-11-23, S08/S09 fix round 3, models of this change; `cargo 1.92.0`, `rustc 1.92.0`,
`Python 3.11.8`, Lean `v4.31.0`): 25,682,976 comparisons, 0 mismatches (`enc_prefix` 10,576;
`dec` 261,694; `utf8` 93,286; `cps` 20,011; `enc_exh` 16,843,009; `utf8_exh` 8,454,400); about
2 minutes. Like the tests, it catches a mismatched model on the inputs it tries; it is not a
proof.

What the check executes: `lake env lean --run` runs the models as compiled code, not their
kernel definitions. For the UTF-8 models this matters: `String.fromUTF8?` (through
`String.validateUTF8`, `@[extern "lean_string_validate_utf8"]`), `String.toByteArray`
(`@[extern "lean_string_to_utf8"]`) and `String.utf8ByteSize` are executed by the C
implementations of the Lean runtime, so the UTF-8 comparisons test that runtime code against
Rust, and say something about the Lean definitions the proofs use only through Lean's own
trust that its runtime implements them. The kernel-level facts are the theorems of
`formal/proofs/Proofs/External/String.lean` (for example `strOfBytes?_eq_some_iff`). The Base64
models use no `extern` string function; they run as code compiled from their list definitions,
with `Nat` and bit-vector arithmetic through the runtime's own implementations, so they too are
tested as compiled code (their laws are the theorems of `Proofs/External/Base64.lean`).

## Standard library

Line numbers in this table and the Phase 2 table below are those cited when the models were
written (`rust-src` of `nightly-2026-06-01`); the current citations, re-checked against
`nightly-2026-09-17` in the Aeneas upgrade of 2026-11-24 (lead decision N9), are those in the
docstrings of `formal/trusted/Rmcp/FunsExternal.lean`, which are authoritative. Rows marked
"moved" are no longer project models: since that upgrade the Aeneas library defines them (lead
decision N8; the upgrade review found the semantics identical); the row is kept as history.

| External | Model | Source (`rust-src`) | Tests |
|---|---|---|---|
| `Borrow::borrow` (blanket) — **moved to the Aeneas library** (N8) | identity | `core/src/borrow.rs` 214–216 | through `HashMap::get` below |
| `Option::ok_or` — **moved to the Aeneas library** (N8) | `Some v ↦ Ok v`, `None ↦ Err e` | `core/src/option.rs` 1334–1339 | `codec::non_base64_sections_are_invalid_encoding` |
| `Option` `Default` | `None` | `core/src/option.rs` 2313–2315 | (non-target) |
| `Result::is_err` | `true` iff `Err` | `core/src/result.rs` 646–648 | `codec::maximum_length_kid_roundtrips_and_oversized_wire_kid_is_rejected` |
| `Result::map_err` — **moved to the Aeneas library** (N8) | `Err e ↦ Err (op e)` via `FnOnce` | `core/src/result.rs` 962–970 | `codec::parser_rejects_invalid_tokens_and_unavailable_keys` (non-UTF-8 kid) |
| `&[T]` `Default` | empty slice | `core/src/slice/mod.rs` 5637–5639 | (non-target) |
| `str::len` | byte count (any `Str`) | `core/src/str/mod.rs` 153–155 | `wire::check_kid_len_counts_utf8_bytes`, `codec::constructor_invariants_are_enforced` |
| `str::as_bytes` | same bytes (any `Str`) | `core/src/str/mod.rs` 498–501 | every `codec` open test |
| `String::with_capacity` | `""`; panic if `> isize::MAX` | `alloc/src/string.rs` 493–495; `alloc/src/raw_vec/mod.rs` 446–482 (`try_allocate_in`), 896–902 (`layout_array`) | `codec::rs1_known_answer_is_unchanged`, `codec::rs2_known_answer_matches_wire_specification` |
| `String::push_str` | append; `fail undef` on non-UTF-8 `Str`; panic beyond `isize::MAX` | `alloc/src/string.rs` 1110–1112; `raw_vec/mod.rs` 502–533 | same |
| `String::push` | append char; panic beyond `isize::MAX` | `alloc/src/string.rs` 1425–1435 | same |
| `String::as_bytes` | UTF-8 bytes; `fail` above `Usize.max` (no Rust `String`) | `alloc/src/string.rs` 1454–1456 | `codec::rs2_roundtrips_with_associated_data_and_ttl` |
| `String::from_utf8` | `Ok s` iff bytes are `utf8 s`, else `Err {bytes}` | `alloc/src/string.rs` 569–574 | `codec::parser_rejects_invalid_tokens_and_unavailable_keys` (kid `[0xff]` ↦ `InvalidKeyId`) |
| `String` `PartialEq::eq`, `Eq::assert_fields_are_eq`, `Clone` | equality; `()`; identity | `alloc/src/string.rs` 350, 2364–2366 | through `HashMap::get` |
| `String` `Hash::hash` | write bytes, then `0xff` | `alloc/src/string.rs` 2740–2742; `core/src/hash/mod.rs` 550–553, 862–866; for `DefaultHasher`: `std/src/hash/random.rs` 135–137 → `core/src/hash/sip.rs` 237–239 → override 303–308 (`write(bytes); write_u8(0xFF)`), `write_u8` not overridden (note at 248) so default `write(&[i])` (`core/src/hash/mod.rs` 362–364) | (unused by the `get` model) |
| `Vec::is_empty` — **moved to the Aeneas library** (N8) | `len == 0` | `alloc/src/vec/mod.rs` 3085–3087 | `codec::pinned_tokens_and_open_results_are_unchanged` (case `rs1 ring no fallbacks: UnknownKeyId`) |
| `RandomState` (type, `Clone`, `build_hasher`) | `{k0, k1}`; identity; keys + empty stream | `std/src/hash/random.rs` 34–38, 83–85 | — |
| `DefaultHasher` (type, `write`, `finish`) | keys + written bytes; append; `sipHash13` | `std/src/hash/random.rs` 94, 125–142 | — |
| `HashMap` (type), `HashMap::get` | association list; first entry with an equal key | `std/src/collections/hash/map.rs` 246–251, 1035–1041; hashbrown 0.17.1 `src/map.rs` (`get`, `Equivalent`) | `codec::rotation_keeps_previous_rs2_key_verifiable` (found and `UnknownKeyId`), `codec::multiple_legacy_fallbacks_are_supported`, `codec::kid_is_authenticated_even_when_ids_share_key_bytes` |
| `HashMap` `Clone` | clone builder, allocator, entries | `map.rs` 1438–1440; hashbrown `impl Clone for HashMap` | (non-target) |
| `Duration`, `FromUtf8Error`, `serde_json::Error` (types) | fields `{secs, nanos}`; `{bytes}` (the `error: Utf8Error` field is not modelled); `{err}` with opaque content | `core/src/time.rs` 81–84; `alloc/src/string.rs` 391–394; `serde_json-1.0.154/src/error.rs` 17–22 | — |

`String` conventions (in `FunsExternal.lean`'s module docstring): out-of-memory is not
modelled (plan Section 4, unlimited memory); growth beyond `isize::MAX` bytes is the
deterministic "capacity overflow" panic and is `fail panic`; a panic that depends on the
capacity history (amortized doubling past `isize::MAX` while the length still fits) is not
modelled. Hence `ok` from a `String` model means "returns, or aborts or panics for memory
reasons": out of memory, or `RawVec::grow_amortized` requesting
`max(2·cap, len + additional)` above `isize::MAX` when the capacity is already above
`isize::MAX / 2`. A Lean `String`, like a Rust `String`, is always valid UTF-8 (`String.isValidUTF8`),
and `ExtModel.strOfBytes?` accepts exactly the encodings of Unicode scalar values (Lean
`String.fromUTF8?`), the set Rust's `core::str::from_utf8` accepts.

`HashMap::get` without hashing: hashbrown's `get` returns `None` on an empty table and otherwise
probes the entries whose hash matches `hash(k)`, comparing with `k == key.borrow()`. For a
`Hash`/`Eq` pair that agree (required by the `HashMap` documentation) the probe finds the entry
with an equal key, whatever the hash values; for `String`, equality is byte equality and `Hash`
writes the bytes. The model is faithful for `Hash`/`Eq` instances that agree and do not fail;
only `K = Q = String` occurs. It returns the first entry with an equal key, which is the Rust
result when keys are pairwise distinct; that invariant is not in the type (a generic `clone`
could not preserve it). Distinctness (`Nodup` of the keys) is needed only to identify *which*
value is returned: `find` returns `some` exactly when an equal key exists, with or without
duplicates. Statements at S12 should therefore assume `Nodup` only where they name the value,
not where they only need "found" or "not found": `Proofs.External.HashMap.find?_key_isSome_iff`
(found exactly when `k` is a key) and `find?_key_of_not_mem` have no `Nodup` premise;
`find?_key_of_mem` uses it to name the value.

## `zeroize`

| External | Model | Source (`zeroize-1.9.2/src/lib.rs`) |
|---|---|---|
| `Zeroizing<Z>` (type) | `{inner : Z}` | 582–584 (`repr(transparent)` tuple struct) |
| `Zeroizing::new` | wrap | 599–601 |
| `Zeroizing` `Clone` | wrap a clone | 606–608 |
| `Zeroizing` `Deref` | the inner value | 634–636 |
| `Zeroize` for `Z: DefaultIsZeroes` | `Z::default()` | 282–284 (`volatile_write(self, Z::default())`) |
| `Zeroize` for `Vec<Z>` | zeroize each element, result empty | 505–516 (spare capacity, `iter_mut().zeroize()`, `clear()`) |

Tests: every keyring test of `codec` goes through `Zeroizing::deref` (`two_key_ring`,
`rotation_keeps_previous_rs2_key_verifiable`, ...). **Not established:** zeroisation on drop
(the `Drop` impl has no counterpart in a value model; plan Section 4) and the volatile writes.

## Clock (`RequestStateCodec::now_ms`)

- **Model.** `ok nowMs`, an opaque constant (`chrono::Utc::now().timestamp_millis()`,
  `codec` lines 729–731; lines 733–735 since translation patch 03).
- **Environmental assumption (stated exception, not modelled).** `Utc::now` panics if the
  system clock is before 1970 or outside chrono's range (`chrono-0.4.45/src/offset/utc.rs`
  lines 96–98: `expect("system time before Unix epoch")`, `DateTime::from_timestamp(..)
  .unwrap()`); the model assumes the clock is in range.
- **Limitation.** One constant cannot express that two readings differ, and it makes every
  function that reads the clock pure. The callers of `now_ms` are `open` and `open_with`, which
  are translated (`formal/translation/Rmcp/Funs.lean`, `open_with` and `open`) but are not
  targets, and `seal_with`, which was excluded from the translation (Charon `exclude`, B13) until
  translation patch 03 (2026-11-24, signed off) and is now translated, with `seal` calling it;
  `open_json`/`open_json_with` (translated since patch 03) read it through `open_with`. (Since
  2026-11-24/25 `open`, `open_with` (R07, R08) and `seal`, `seal_with`, `open_json`,
  `open_json_with` (R09, R10, R13, R14) are specification targets under the review rule below.)
- **Review rule.** No spec statement mentions the functions
  `rmcp.model.request_state.RequestStateCodec.now_ms`, `…RequestStateCodec.open`,
  `…RequestStateCodec.open_with`, `…RequestStateCodec.open_json`,
  `…RequestStateCodec.open_json_with`, `…RequestStateCodec.seal` or
  `…RequestStateCodec.seal_with` (a variable named `now_ms`, such as the time parameter of E01
  `open_authenticated_body`, is not covered); statements about
  opening use `open_at`, and about sealing `seal_at` (or its `Defs` model `sealAt`), with an
  explicit `now` (also in `STATUS.md` at 9047c72). Exceptions (human decisions 2026-11-24,
  extended by the spec owner 2026-11-25), as worded in `formal/README.md`, "Trusted base": the
  spec theorems of the public `open`, `open_with`, `open_json`, `open_json_with`, `seal` and
  `seal_with`, their restatements and the corollaries `open_with_spec_of_length_le`,
  `seal_with_spec_of_length_le` and `seal_spec_of_length_le`, with the postconditions
  `resultBytes result = openAt … ExtModel.nowMs.val` (`open`/`open_with`); the error of
  `openAt … ExtModel.nowMs.val` unchanged, otherwise the `ExtModel.serdeJsonFromSlice` outcome
  for the opened payload with `Err` mapped to `Deserialization` (`open_json`/`open_json_with`);
  and `sealAt … ExtModel.nowMs.val = some (ExtModel.utf8 result)` (`seal`/`seal_with`; `sealAt`
  is the `Defs.CodecState` model of the private `seal_at`, human decision 2026-11-25, replacing
  the earlier wording "the result of the translated `seal_at` at `ExtModel.nowMs`"); their
  docstrings state the one-reading caveat and the inherited exceptions. Besides these, only the
  model's own spec theorem `model.request_state.RequestStateCodec.now_ms_spec` (postcondition
  `result = ExtModel.nowMs`; human decision 2026-11-25) names `now_ms` and `ExtModel.nowMs`; no
  other statement names `ExtModel.nowMs`, and no statement relates two readings. The internal statements of `seal_at`
  (R10a) and of its round trip with `open_at` (R10b) use explicit times.
- **Tests.** `codec::within_ttl_opens`, `codec::past_ttl_is_expired` (through `open`).

## Phase 2 externals (plan steps S26–S27)

The Phase 2 translation (plan step S21) added 26 external functions and 6 external types,
first as `opaque` placeholders that asserted nothing. S26/S27 (stage 1) replaced each by the
model below (plan Section 18); all are definitions, `structure`s or inductive types, and the only
new `opaque` constant is the carrier `ExtModel.SerdeJsonValue`. Sources are `rust-src` of the
pinned toolchain `nightly-2026-09-17` (read in
`~/.rustup/toolchains/nightly-2026-09-17-aarch64-apple-darwin/lib/rustlib/src/rust/library/`;
until the Aeneas upgrade of 2026-11-24, `nightly-2026-06-01`). The line numbers in the table
below are those of `nightly-2026-06-01`, except the `RangeInclusive::contains` row; the current
citations are in the docstrings of `formal/trusted/Rmcp/FunsExternal.lean` (see the note above
the Standard library table).
The model laws (plan Section 18, "Evidence" column): 43 statements, signed off by the spec owner on
2026-11-23, proved (`formal/proofs/Proofs/External/{String,Option,Std,IntParse,Net}.lean`) and
restated in `formal/specs/Specs/External.lean` (Phase 2 part; since 2026-11-24 in
`formal/proofs/Proofs/Internal/External.lean`). **The differential programs of plan
Section 18 were not built: stage 3 was dropped by human decision on 2026-11-23.** The
reproducible evidence for these models is the cited `core`/`alloc` source and (after stage 6)
the proved laws. The spot checks below are unrecorded scratch runs, with no committed harness or
command; they are not reproducible evidence. Phase 2 adds no Rust test to the SDK source (human
decision H3, plan Section 19; the test-only patch 02 adds `#[cfg(test)]` tests to the patched
copy only, S34); the existing upstream tests per target are mapped in "Phase 2
boundary cases: upstream-test map (S34)" below.

New trusted helper definitions (namespace `ExtModel`, in `formal/trusted/Rmcp/`, part of the
trust base like the models that use them): `IntErrorKind` (the six variants of
`core::num::IntErrorKind`), `decDigit?` (value of an ASCII decimal digit), `i64DigitLoop` (the
digit loop of `from_ascii_radix`, radix 10), `i64FromAscii` (sign handling and the loop),
`sliceEq` and `sliceEqSameLength` (element-wise slice equality through `PartialEq`), `beNat`
(big-endian value of a digit list in a base), `ipv4Nats` and `ipv6Nats` (the octets or segments
of an address as natural numbers). The opaque carrier `SerdeJsonValue` is listed above.

### Strings and `Arc`

| External | Model | Source (`rust-src`) |
|---|---|---|
| `str` `PartialEq::eq` | byte-list equality (any `Str`) | `core/src/str/traits.rs` 29–31; `core/src/slice/cmp.rs` 14–29 |
| `String` `Deref<str>` | the UTF-8 bytes (the model of `String::as_bytes`) | `alloc/src/string.rs` 2835–2837 |
| `Arc<T>` (type) | `{data : T}` (reference counts, pointer and allocator not modelled) | `alloc/src/sync.rs` 269–276, `ArcInner` 388–397 |
| `Arc` `Deref` | projection `data` | `alloc/src/sync.rs` 2443–2445 |
| `Arc` `PartialEq::eq` | `data == data` through `T`'s instance | `alloc/src/sync.rs` 3580–3582, 3529–3533 |

- **Stated exception.** For `T: Eq`, Rust's `Arc` equality is `ptr::eq(..) || **self ==
  **other` (`sync.rs` 3548–3552). The model has no pointers and always compares the values; the
  two agree whenever `T`'s equality is reflexive and does not fail; `Eq` asks for reflexivity
  (`core/src/cmp.rs` 280–289; `MarkerEq`, `alloc/src/rc.rs` 2615–2617); `str`, the only
  instance, has both.
- **Planned evidence.** Laws in `Proofs/External/String.lean` (stage 2); the Phase 1 string tests
  above (`String` models) cover `as_bytes`, which `Deref<str>` reuses.

### `Option`, `Result`, slices, ranges, `MaybeUninit`

| External | Model | Source (`rust-src`) |
|---|---|---|
| `Option::or_else` | `Some x ↦ Some x`, `None ↦ f()` via `FnOnce` | `core/src/option.rs` 1644–1655 |
| `Option` `PartialEq::eq` | case split, `Some l, Some r ↦ l == r` | `core/src/option.rs` 2440–2449 |
| `Result::ok` | `Ok x ↦ Some x`, `Err _ ↦ None` | `core/src/result.rs` 708–717 |
| `slice::first` | head or `None` | `core/src/slice/mod.rs` 155–157 |
| `slice::strip_suffix` | `as_slice`, `split_at(len − n)`, `tail == suffix` | `core/src/slice/mod.rs` 2719–2733 |
| `[T] == [U; N]` | `false` unless length `N`, else element-wise `ne` loop | `core/src/array/equality.rs` 48–53, 10–12, 143–145; `core/src/slice/mod.rs` 851–861 (`as_array`); `core/src/slice/cmp.rs` 125–140 |
| `SlicePattern::as_slice` for `[T; N]` | the same elements as a slice | `core/src/slice/mod.rs` 5678–5680 |
| `RangeInclusive::contains` | `start <= item`, then `item <= end` (`item < start` if exhausted, i.e. empty; changed in the Aeneas upgrade, human decision 2026-11-24; one fresh review of model and laws: model exact, one blocking finding (a dropped restatement) fixed; laws re-signed 2026-11-24; up to `nightly-2026-06-01`: `item < end`), short-circuit | `core/src/ops/range.rs` 539–545, 886–900, 1142–1157 (`nightly-2026-09-17`) |
| `MaybeUninit<T>` (type) | `uninit` or `value v` (the two union fields) | `core/src/mem/maybe_uninit.rs` 355–358 |

- **Stated exceptions.** The `BytewiseEq` specializations of slice and array equality
  (`slice/cmp.rs` 146–160, `array/equality.rs` 152–158) compare bytes instead of calling `ne`;
  for the types they apply to (`u8`, `u16` here) `ne` is the negation of byte equality and does
  not fail, so the result is the same. `MaybeUninit` is mentioned by no generated definition (it
  occurs in the LLBC, in the signature of `Box::new_uninit`); a partly initialised value is not
  modelled.
- **Spot check (2026-11-23; an unrecorded scratch run with no committed harness or command,
  not reproducible evidence; Lean `#eval` against `rustc +nightly-2026-06-01`, identical
  results):** `strip_suffix(&[13u8])` of `[1, 2, 13]`, `[1, 2]` and `[]`; `[u8] ==
  [u8; 2]` with equal and unequal lengths; `(64..=127).contains` at `127` (fresh, and exhausted
  by iteration in Rust / `exhausted = true` in Lean) and at `63`. **Run on `nightly-2026-06-01`
  only** (the toolchain before the Aeneas upgrade of 2026-11-24). Its exhausted case does not
  separate the old model (`item < end`) from the new one (`item < start`), and on
  `nightly-2026-09-17` iterating `64u8..=127` to the end leaves `128..=127` with
  `exhausted = false` (`core/src/iter/range.rs` about lines 1538–1546), so that Rust state is no
  longer an exhausted range.
- **Vectors separating the old and new `RangeInclusive::contains` model (2026-11-24, verified on
  `rustc +nightly-2026-09-17` by the reviewer of the changed model; Rust state as printed by
  `{:?}`, model `contains core.cmp.PartialOrdU8 …` on `⟨start, end, exhausted⟩`):**
  - `250u8..=255` iterated to the end → state `0..=255 (exhausted)`; `.contains(&3)` = `false`;
    model `⟨0, 255, true⟩` at `3` → `ok false` (the old model, `item < end`, gave `true`).
  - `(64u8..=127).nth(250)` → state `59..=127 (exhausted)`; `.contains(&100)` = `false`; model
    `⟨59, 127, true⟩` at `100` → `ok false` (the old model gave `true`).
- **Planned evidence.** Laws in `Proofs/External/Option.lean` (`Option`, `Result`) and
  `Proofs/External/Std.lean` (slices, ranges), stage 2.

### Integer parsing (`str::parse`, `i64::from_str`, `ParseIntError`)

- **Model.** `str::parse` calls the `FromStr` instance (`core/src/str/mod.rs` 2765–2767).
  `i64::from_str(src) = from_str_radix(src, 10)` (`core/src/num/mod.rs` 1626–1628) `=
  from_ascii_radix(src.as_bytes(), 10)` (1677–1679), transcribed as `ExtModel.i64FromAscii`
  and `ExtModel.i64DigitLoop` (lines 1756–1844): `""` is `Empty`; a lone `+` or `-` is
  `InvalidDigit`; one leading `+`/`-` sets the sign; each further byte must be `0`–`9`
  (`char::to_digit(10)`, `core/src/char/methods.rs` 402–424), else `InvalidDigit`; a value
  leaving `[-2^63, 2^63)` is `PosOverflow` (positive) or `NegOverflow` (negative), the first
  error from the left winning and a bad digit before an overflow at the same position (checked
  loop, 1815–1841; the unchecked loop for at most 15 digits, 1791–1814, cannot overflow).
  `ParseIntError` is `{kind}` (`core/src/num/error.rs` 74–76) and `IntErrorKind` has its six
  variants (93–129). Never panics (radix 10 passes the radix check).
- **Spot check (2026-11-23; an unrecorded scratch run with no committed harness or command,
  not reproducible evidence; the Lean models evaluated with `#eval` and the same inputs run
  through `str::parse::<i64>` compiled by `rustc +nightly-2026-06-01`; identical results):**
  `""` Empty; `"+"`, `"-"`, `"+-1"`, `"--1"`, `" 1"`, `"1 "`, `"٣"` InvalidDigit; `"007"` 7;
  `"-0"` 0; `i64::MAX`, `i64::MIN` accepted; one past each PosOverflow/NegOverflow;
  `"99999999999999999999a"` PosOverflow; `"1a99999999999999999999"` and
  `"922337203685477580a"` InvalidDigit. Two independent reviewers (S26/S27 review round 1) also
  ran scratch comparisons against `rustc +nightly-2026-06-01` with 0 mismatches over 200,026
  inputs, equally unrecorded.
- **Not built (stage 3 dropped, 2026-11-23).** Planned was a differential
  test against `i64::from_str` over a corpus (signs, empty, `+`/`-` alone, leading zeros, both
  bounds and one past each, non-ASCII digits, whitespace) plus 10^6 random strings over
  `[+\-0-9a ]`. The law `model = Defs.parseI64` (`Proofs/External/IntParse.lean`) was deferred
  until after plan step S24, which defines `Defs.parseI64`; it is now proved as
  `I64.Insts.CoreStrTraitsFromStrParseIntError.from_str_eq_parseI64` (signed off at S24, proved
  at incorporation, 2026-11-24).

### IP addresses (`Ipv4Addr`, `Ipv6Addr`)

| External | Model | Source (`core/src/net/ip_addr.rs`) |
|---|---|---|
| `Ipv4Addr` (type) | `{addrOctets : Array U8 4}` | 74–76 (`octets: [u8; 4]`) |
| `Ipv6Addr` (type) | `{addrSegments : Array U16 8}` (stated change of representation) | 168–170 (`octets: [u8; 16]`); `segments` 1495–1510 |
| `Ipv4Addr::octets` | the octets | 668–670 |
| `Ipv4Addr::is_unspecified` | big-endian value `= 0` | 728–730 |
| `Ipv4Addr::is_loopback` | `octets[0] == 127` | 750–752 |
| `Ipv4Addr::is_private` | `[10, ..]`, `[172, 16..=31, ..]`, `[192, 168, ..]` | 781–788 |
| `Ipv4Addr::is_link_local` | `[169, 254, ..]` | 809–811 |
| `Ipv4Addr::is_multicast` | `224 <= octets[0] <= 239` | 1010–1012 |
| `Ipv4Addr::is_broadcast` | big-endian value `= 0xffffffff` | 1032–1034, `BROADCAST` 652 |
| `From<u32> for Ipv4Addr` | big-endian bytes (`from_bits`, `to_be_bytes`) | 1288–1290, 608–610 |
| `Ipv6Addr::segments` | the segments | 1495–1510 |
| `Ipv6Addr::is_unspecified` | value `= 0` (`::`) | 1558–1560, `UNSPECIFIED` 1479 |
| `Ipv6Addr::is_loopback` | value `= 1` (`::1`) | 1582–1584, `LOCALHOST` 1462 |
| `Ipv6Addr::is_multicast` | `segments[0] & 0xff00 == 0xff00` | 1942–1944 |

- **Stated deviation.** Rust stores an `Ipv6Addr` as 16 octets; the model stores the 8 segments
  `segments()` computes from them (a bijection), as plan Section 18 specifies. The translated
  code reads an address only through the four `Ipv6Addr` functions above, so no result depends
  on the representation. The field names `addrOctets`/`addrSegments` avoid the generated names
  of the methods `octets`/`segments`.
- **Spot check (2026-11-23; an unrecorded scratch run with no committed harness or command,
  not reproducible evidence; Lean `#eval` against the same calls compiled by
  `rustc +nightly-2026-06-01`, identical results):** `From<u32>` of `0x7f000001` gives
  `[127, 0, 0, 1]`; the six IPv4 predicates on `127.0.0.1`, `0.0.0.0`, `255.255.255.255`,
  `10.0.0.1`, `172.16.0.1`, `172.32.0.1`, `192.168.1.1`, `169.254.1.1`, `224.0.0.1`,
  `239.0.0.0`, `240.0.0.0`; the three IPv6 predicates on `::1`, `::`, `ff02::1`, `feff::`,
  `::1:0`. Two independent reviewers (S26/S27 review round 1) also ran scratch comparisons
  against `rustc +nightly-2026-06-01` with 0 mismatches (IPv4: 100,586 addresses; IPv6: 100,011
  addresses), equally unrecorded.
- **Not built (stage 3 dropped, 2026-11-23).** Planned was: IPv4 exhaustive
  over all 2^32 addresses for every predicate, `octets` and `from`; IPv6 every listed prefix
  boundary plus 10^6 random addresses; a Cargo program on the pinned nightly and a compiled Lean
  executable in a separate Lake project, comparing per-function digests (plan Section 18, with
  its fallback to an exhaustive Lean proof if the runtime exceeds a few hours).

### Opaque value (`serde_json::Value`)

- **Model.** `def serde_json.value.Value := ExtModel.SerdeJsonValue`, an `opaque` type
  (`serde_json-1.0.154/src/value/mod.rs` 116–176, `pub enum Value`). The targets only move values
  (`ErrorData.data : Option Value`); no model creates, inspects or compares one. No evidence is
  needed beyond that observation (plan Section 18).

## Public `request_state.rs` API externals (translation patch 03, R09–R15)

**Reviewed in two rounds and signed off by the spec owner 2026-11-24** (human decisions:
targets R09–R15, variant A). Translation patch 03 and the removal of eight Charon `exclude` entries make `seal`,
`seal_with` (through the private `seal_at`), `with_rs1_signing`, `with_rs1_fallback`,
`open_json`, `open_json_with` and `new_with_keyring` translate; the externals they newly reach are
modelled below (14 functions, 2 types, 3 `opaque` constants, no axiom). Toolchain: Aeneas
`nightly-2026.11.24-fb44cb4`, `rust-src` of `nightly-2026-09-17`, hashbrown 0.17.1 (the
toolchain's `library/Cargo.lock`), `serde_json 1.0.154` and `serde_core 1.0.229` (both in
`PINNED_DEPS`). The docstrings in `formal/trusted/Rmcp/{Funs,Types}External.lean` are
authoritative. Test names are relative to `model::request_state::tests::` and run with
`cargo test -p rmcp --no-default-features --features request-state --lib model::request_state`
on the patched copy (`byte_identity::*` come from patch 01).

**Opaque constants** (no axiom):
- `ExtModel.randomState : RandomState`: the keys `HashMap::new` stores (`RandomState::new`,
  `std/src/hash/random.rs` 55–76: random per thread, incremented per map). Review rule: no
  statement about its value or about the `hash_builder` of a map built by `HashMap::new`, and no
  statement states or relies on the equality (or inequality) of two maps, or of two codecs
  containing them, built by distinct `HashMap::new` calls: their keys differ on the same thread
  and are independent random keys otherwise (`std/src/hash/random.rs` 71–75).
- `ExtModel.serdeJsonFromSlice {T} : Deserialize T → List U8 → core.result.Result T
  serde_json::Error`: the outcome of `serde_json::from_slice::<T>`; depends on the caller's
  `Deserialize` impl and the `serde_json` parser, not translated (human decision 2026-11-24:
  `from_slice` is `ok` of this outcome). Review rule: a statement may only say that the result of
  `open_json`/`open_json_with` is this outcome for the opened payload, mapped as the Rust code
  maps it; no statement relates two calls of `open_json`/`open_json_with` (or of `from_slice`).
- `ExtModel.SerdeJsonErrorImplCarrier : NonemptyType`: replaces `opaque ExtModel.SerdeJsonErrorImpl
  : Type`, which is now `def … := Carrier.type`, with `Nonempty` instances for it and for
  `serde_json::Error`, so that `serdeJsonFromSlice` can return `Err` (human decision 2026-11-24).

**Types**

| External | Model | Source | Tests |
|---|---|---|---|
| `OccupiedEntry` | `{key, value}` of the slot | `std/src/collections/hash/map.rs` 1977–1984; hashbrown `src/rustc_entry.rs` (`RustcOccupiedEntry {elem, table}`) | `key_rotation::constructor_invariants_are_enforced` (duplicate kid) |
| `VacantEntry` | `{key, inserted : Option V}` (hash and table not stored; the map is rebuilt by the backward function of `entry`) | `map.rs` 1999–2006; hashbrown `src/rustc_entry.rs` (`RustcVacantEntry {hash, key, table}`) | every `new_with_keyring` test below |

**Functions**

| External | Model | Source (`rust-src` nightly-2026-09-17 unless stated) | Tests |
|---|---|---|---|
| `Duration::as_millis` | `secs*1000 + nanos/1_000_000` as `u128` (exact, no overflow) | `core/src/time.rs` 601–604, constants 28, 30 | `key_rotation::rs1_known_answer_is_unchanged`, `key_rotation::rs2_known_answer_matches_wire_specification` (90 s TTL, byte-exact), `ttl::within_ttl_opens`, `ttl::past_ttl_is_expired`, `ttl::ttl_and_associated_data_combine`, `key_rotation::rs2_roundtrips_with_associated_data_and_ttl`, `byte_identity::pinned_tokens_and_open_results_are_unchanged` (TTL tokens of `pinned_cases`); since 2026-11-25 (patch 02, `public_api_boundaries::*`): `seal_at_sub_millisecond_ttl_adds_no_millisecond` (`nanos/1_000_000` truncation below 1 ms), `seal_at_truncates_ttl_to_whole_milliseconds` (`secs*1000 + nanos/1_000_000`), `seal_at_clamps_ttl_milliseconds_to_i64_max` (`Duration::MAX` and exactly `2^64` ms: the `u128` value is not truncated to 64 bits) |
| `str::to_owned` | same bytes as `String`; `fail undef` on non-UTF-8 `Str` | `alloc/src/str.rs` 252–255 | `key_rotation::rolling_migration_is_bidirectionally_compatible`, `key_rotation::multiple_legacy_fallbacks_are_supported` |
| `HashMap::contains_key` | `find` (as for `get`) is `some`; no hashing | `map.rs` 1268–1274; hashbrown `src/map.rs` 1382–1392, `src/lib.rs` 151–159 (`Equivalent`) | `key_rotation::constructor_invariants_are_enforced` (unknown kid in `with_rs1_*`, absent active kid), `key_rotation::rolling_migration_is_bidirectionally_compatible` (known kid in `with_rs1_*`, followed by the `any → false` path only; the `any → true` path after `contains_key` is covered as stated in the `slice::Iter::any` row); since 2026-11-25 (patch 02, `public_api_boundaries::*`): `rs1_builders_report_exact_messages` (unknown kids `"c"`, `""`, `"A"` in both builders: `contains_key` is byte equality, case-sensitive), `new_with_keyring_reports_exact_messages` and `new_with_keyring_checks_faults_in_source_order` (active kid absent), `rs1_builders_keep_fallbacks_unique_and_ordered` (known kids) |
| `HashMap::is_empty` | `entries = []` | `map.rs` 745–747; hashbrown `src/map.rs` 824–826 | `key_rotation::constructor_invariants_are_enforced` (empty keyring) |
| `HashMap::new` (K, V, `RandomState`, `Global`) | empty, `hash_builder := randomState`; OS-RNG panic not modelled | `map.rs` 269–271, 1488–1497; `std/src/hash/random.rs` 55–76; `std/src/sys/random/linux.rs` 166–172 | every `new_with_keyring` test |
| `HashMap::entry` (helper `ExtModel.HashMap.lookupEntry`) | first entry with `stored.eq(key)` → `Occupied {key, value}`, backward = same map; else `Vacant {key, none}`, backward adds `(key, v)` iff `inserted = some v`; `reserve(1)` not modelled | `map.rs` 1012–1014; hashbrown `src/rustc_entry.rs` 35–54 | `key_rotation::constructor_invariants_are_enforced` (duplicate kid → `InvalidKeyring`), `byte_identity::run3_token_matrix_is_unchanged` and `byte_identity::pinned_tokens_and_open_results_are_unchanged` (keyring codecs of `codecs`), `key_rotation::rotation_keeps_previous_rs2_key_verifiable` |
| `VacantEntry::insert` | returns `value`; backward records the final value as `inserted` | `map.rs` 2975–2977; hashbrown `src/rustc_entry.rs` 574–579 | as for `entry` |
| `Hash for str` | write bytes, then `0xff` | `core/src/hash/mod.rs` 865–867 (`write_str`); default `write_str` and the `DefaultHasher` path as for `String` `Hash` | — (instance only required by `contains_key` with `Q = str`; no model hashes) |
| `Borrow<str> for String` | `String` deref (same bytes) | `alloc/src/str.rs` 233–235 | through `contains_key` in `with_rs1_*` |
| `String == str` (`PartialEq<str> for String`) | byte equality of `utf8 self` and `other` | `alloc/src/string.rs` 2740–2742, `impl_eq! { String, str }` 2763 | `key_rotation::multiple_legacy_fallbacks_are_supported`, `key_rotation::rolling_migration_is_bidirectionally_compatible` (the `any → false` path: a new kid is appended); since 2026-11-25 the `any → true` branch (de-duplication when the kid is already in `rs1_fallbacks`; `request_state.rs` lines 404–406 and 436–438 of the repository source, 394–396 and 426–428 of the patched copy: `if !rs1_fallbacks.iter().any(…) { rs1_fallbacks.push(…) }`) is pinned by patch 02's `public_api_boundaries::rs1_builders_keep_fallbacks_unique_and_ordered` (repeated `with_rs1_fallback("b")`, `with_rs1_signing("a")` twice, then `with_rs1_fallback("a")`: the list stays `["b", "a"]`), and the `false` path with order by `rs1_fallbacks_append_in_call_order_and_signing_registers_its_id`; before, only by reading the source and a scratch test |
| `slice::Iter::any` (helper `ExtModel.sliceIterAny`) | call the `FnMut` on `slice[i..]` in order, stop at the first `true`, advance `i` by the consumed count | `core/src/slice/iter/macros.rs` 321–332, instantiated by `iterator!` in `core/src/slice/iter.rs` 140–148 | as for `String == str`, and `with_rs1_signing` in `key_rotation::rolling_migration_is_bidirectionally_compatible` (`any → false` only); since 2026-11-25 the `any → true` branch (de-duplication) is pinned by patch 02's `public_api_boundaries::rs1_builders_keep_fallbacks_unique_and_ordered` (both builders, a kid already in the list; stop at the first `true`), and the in-order `false` path by `rs1_fallbacks_append_in_call_order_and_signing_registers_its_id`; before, only by reading the source and a scratch test |
| `Iterator::any` (default) | `next`/closure loop through `Aeneas.Std.loop`; stated exception: an overridden `try_fold` | `core/src/iter/traits/iterator.rs` 2897–2910 | — (declared by the template, called by no generated definition) |
| `serde_json::from_slice` | `ok (serdeJsonFromSlice inst v)`; stated exceptions: a panicking or non-terminating caller `Deserialize` impl, and a non-deterministic or side-effecting one (global or thread-local state, RNG) | `serde_json-1.0.154/src/de.rs` 2667–2672 | `seal_open_roundtrips_json` (Ok), `key_rotation::serde_is_reached_only_after_integrity_verification` (invalid JSON → `Deserialization`; tampered → integrity error before serde) |
| `Error::source` (default) | `ok none` | `core/src/error.rs` 111–113 | — (declared by the template because the `serde_core` error traits have `Error` as supertrait; not called) |

Changed docstrings (facts only): `core.time.Duration` is now read by `seal_at` through
`as_millis`; `std.collections.hash.map.HashMap` lists the called functions and notes that
`new_with_keyring` builds a map; `model.request_state.RequestStateCodec.now_ms` is called by
`seal_with` (hence `seal`) since patch 03 (Source lines 733:4–735:5) and carries the extended
clock rule.

## Phase 2 boundary cases: upstream-test map (S34)

Plan step S34 (plan Sections 21 and 22; human decision H3): for each boundary case of plan
Section 22, the existing upstream Rust tests that exercise it on the target function, either
**direct** (the test calls the target) or **via caller** (the test calls a named caller whose
observed result is determined by the target's result on that input). The Lean proofs cover
every input; these tests are evidence that the translated configuration behaves as the
statements say on the boundary cases, not a proof. Phase 2 adds no Rust test to the SDK source
(H3), and the differential programs were dropped (plan Section 18, amendment). The cases that no
upstream test covered (**uncovered** upstream, 96) or covered only in part (**partial**, 8) are
covered by the test-only patch 02 (`formal/trusted/patches/02-phase2-tests.patch`, human
decision 2026-11-24, H3 follow-up; paragraph "Patch 02" below): the Status column names its test
(`s34_…`, a direct call of the target). **Partial**: only some targets of the row, or some of
the inputs, are exercised by upstream tests. **Equivalent input**: the test uses an input of the
same shape as the listed literal (named).

Paths are relative to `crates/rmcp/`; the number in parentheses is the line of the test function
in the repository's files (upstream `7caec76`; in the patched copy, `model.rs` lines after 19 are
2 higher). Lean regression checks (`decide`, kernel-checked when the module builds):
`Net` = `formal/proofs/Proofs/Defs/Net.lean` lines 221–330 (since 2026-11-26; before the additive change below, 190–299); `Sse` =
`formal/proofs/Proofs/Defs/Sse.lean` lines 272–416; `Methods` =
`formal/proofs/Proofs/Defs/Methods.lean` lines 194–262 (list contents only). No `Defs` regression
check evaluates M01–M14, T04 or T07/T08; `Defs.parseI64` (`formal/specs/Defs/IntParse.lean`
lines 80–89) names the M06 strings in its docstring only. The theorems are in
`formal/proofs/Proofs/Model/` and `formal/proofs/Proofs/Transport/`.

**Runs (2026-11-24).** Toolchain `nightly-2026-06-01` (`rustc 1.98.0-nightly (14210df0e
2026-05-31)`, `cargo 1.98.0-nightly (fbb61be30 2026-05-26)`), the pinned nightly of
`patched-tests.yml`; host `aarch64-apple-darwin` (CI: `x86_64-unknown-linux-gnu`). Run in a
scratch copy of `.llbc/work/` (patch 01 applied; its `Cargo.lock` as checked by
`scripts/aeneas-translate.sh --check-deps`), with a separate target directory and the default
`CARGO_HOME` (CI uses an isolated one). `F` is the translated feature list
`request-state,server,client,client-side-sse,transport-streamable-http-server,`
`transport-streamable-http-client,auth`; every command also passes `--locked
--no-default-features --config profile.dev.overflow-checks=true --config
profile.dev.debug-assertions=true`, as `patched-tests.yml` does.

| Command (in `crates/rmcp`) | Exit | Result |
|---|---|---|
| `cargo test --features "$F,macros" --lib` (the `patched-tests.yml` command) | 0 | 801 passed, 0 failed |
| `cargo test --features "$F,macros" --test test_completion --test test_sampling --test test_task --test test_client_initialization --test test_client_lifecycle_modes --test test_async_rw_max_line_length` | 0 | 12, 36, 8, 4, 16, 7 passed (in that order), 0 failed |
| `cargo test --features "$F,macros,transport-streamable-http-client-reqwest" --test test_custom_headers` | 0 | 39 passed, 0 failed |
| `cargo test --features "$F,macros,transport-streamable-http-client-reqwest" --lib clear_stream_response_pending` | 0 | 2 passed, 868 filtered out |

`patched-tests.yml` runs only the first command: the integration tests (`tests/*.rs`) are not
part of the CI evidence job. Tests marked † need `transport-streamable-http-client-reqwest`,
which is outside the translated configuration: all of `tests/test_custom_headers.rs`
(`required-features` in `Cargo.toml`) and the two `clear_stream_response_pending` tests
(`#[cfg(feature = ...)]`). The target functions themselves carry no `cfg` on that feature.

**Patch 02 (S34, 2026-11-24).** Test-only: it adds 34 `#[test]` functions named
`s34_<id>_<case>`, all inside `#[cfg(test)]` modules (at the end of the existing test modules of
`model.rs`, `model/task.rs`, `async_rw.rs`, `auth.rs` and `client_side_sse.rs`, and a new
`#[cfg(test)] mod phase2_boundary_tests` at the end of `tower.rs`); no non-test line, dependency
or `Cargo.toml` changes. Each test cites its plan Section 22 row and the theorem it mirrors; its
expected values are taken from the signed-off statements and their `Defs` (`Defs.parseI64`,
`Defs.Tower.defaultPort`, the `Defs.Methods` lists, the `Defs.Sse` model and checks, the
`Defs.Net` definitions and checks), not from running the code. The tests call the targets
directly, so they also check the limiter state after a call (T01–T03), which no caller exposes,
and need no feature outside the translated configuration plus `macros`. A test of a feature-gated
item carries the item's `cfg`: `s34_m06_numeric_string_value_boundary_strings` has
`#[cfg(any(feature = "client", feature = "server"))]` and the four `s34_m07_*` tests
`#[cfg(feature = "client")]`, as `numeric_string_value` and `matches_response_id` (`model.rs`
lines 321 and 329 at `7caec76`); the other tests call ungated items or sit in modules gated
already (`transport` and its `async_rw`, `auth`, `client_side_sse`, `tower` modules), so the
crate's tests also compile with `request-state` alone (the Phase 1 evidence command, which the
first version of the patch broke). The limiter tests build every start state field by field
(`s34_limiter`), never through `SseEventSizeLimiter::new`, which no signed-off statement
covers. `scripts/apply-patches.sh` applies it after patch 01 to the copy in `.llbc/work/` only
(file-name order, `patch -p1 -F 0`), so `patched-tests.yml` runs these tests; the SDK sources
stay byte-identical to upstream. Every hunk is at the end of its file, so no translated item
moves. As a test-only patch it is a process exception to CONTRIBUTING.md "Translation patches" (plan
Section 21, H3), to be recorded in `STATUS.md` at 9047c72, "Documents". No expected value
disagreed with the code.

Runs of patch 02 (2026-11-24; same toolchain and host as above; scratch directories, a separate
target directory; `F` as above):

| Command | Exit | Result |
|---|---|---|
| `RMCP_LLBC_DIR=<scratch>/llbcA scripts/apply-patches.sh` (fresh directory) | 0 | applied `01-request-state-wire.patch`, then `02-phase2-tests.patch` (`patch -F 0`; applied again by hand: no fuzz or offset message) |
| `RMCP_LLBC_DIR=<scratch>/llbcA scripts/aeneas-translate.sh --check-deps` | 0 | dependency checks passed; checked `Cargo.lock` |
| in `<scratch>/llbcA/work/crates/rmcp`, with `CARGO_HOME=<scratch>/llbcA/cargo-home` (isolated, as in CI): `cargo test --locked --no-default-features --features "$F,macros" --lib --config profile.dev.overflow-checks=true --config profile.dev.debug-assertions=true` (the `patched-tests.yml` command) | 0 | 835 passed, 0 failed (the 801 above plus the 34 `s34_*`) |
| same directory and flags, `--features request-state` (the Phase 1 evidence configuration) | 0 | 303 passed, 0 failed (10 `s34_*`: M01–M05, M08, M09–M12; M06/M07 and the transport tests are compiled out) |
| same directory and flags, `--features request-state,server,macros` (M06 compiled, M07 not; `request-state,server` without `macros` fails to compile upstream tests in `tool_traits.rs`, independent of patch 02) | 0 | 399 passed, 0 failed (17 `s34_*`, incl. `s34_m06_numeric_string_value_boundary_strings`, no `s34_m07_*`) |
| `rustfmt --check` (`nightly-2026-06-01`, the repository's `rustfmt.toml`) on the six patched files | 0 | no difference |
| mutation: `64..=127` → `64..=126` in `is_disallowed_metadata_ipv4` (scratch copy, then restored), the `patched-tests.yml` command filtered to `s34_` | 101, then 0 | `s34_a02_range_boundaries` fails (`100.127.255.255 must be blocked`), 33 passed; after restoring, 34 passed |
| `DYLD_FALLBACK_LIBRARY_PATH=/usr/lib RMCP_LLBC_DIR=<scratch>/llbcB RMCP_TRANSLATION_DEST=<scratch>/trans scripts/aeneas-translate.sh`, then `diff -r <scratch>/trans formal/translation` | 0, 0 | the translation with both patches is byte-identical to `formal/translation/` (`Funs.lean`, `Types.lean`, the two `External` templates, `translation.json`); `Funs.lean` matches its pin |
| `DYLD_FALLBACK_LIBRARY_PATH=/usr/lib scripts/check-original-linkage.sh <scratch>/link` | 0 | 41, 27, 30, 9 blocks identical |

**Patch 02 extension (2026-11-25): boundary tests of the public `request_state.rs` API R09–R12,
R15.** Human decision 2026-11-25 in the R09–R15 spec cycle (findings sR2-a-2, sR2-b-4, sR3-a-3),
signed off by the spec owner 2026-11-25 with the R09–R15 statements. 12 tests in a new
`mod public_api_boundaries` inside `model::request_state::tests` (gated as the existing tests);
patch 02 now adds 46 tests (34 `s34_*` + 12). Expected values come from the upstream source at
`7caec76` (before patch 03), not from the Lean model (patch header). Each `seal_at` test checks the
token's 8-byte expiry decoded independently of the codec, and opens the token at the expiry
(`Ok`) and one millisecond later (`Expired`, when representable) with the private `open_at`.

| Test (`public_api_boundaries::`) | What it pins | Statement |
|---|---|---|
| `seal_at_sub_millisecond_ttl_adds_no_millisecond` | TTLs of 999 999 ns, 1 ns and 0 add nothing (single key and keyring) | R10a (`sealExpiry`, `durationMillis`) |
| `seal_at_truncates_ttl_to_whole_milliseconds` | 1.5 ms → +1, 1 999 999 ns → +1, 2 s + 999 999 ns → +2000 | R10a |
| `seal_at_clamps_ttl_milliseconds_to_i64_max` | `Duration::MAX`, `i64::MAX + 1` ms, exactly `i64::MAX` ms, exactly `2^64` ms (not truncated to 0) are clamped to `i64::MAX` ms; with `now = i64::MIN`, `Duration::MAX` gives `-1` | R10a |
| `seal_at_rs1_ring_opens_until_expiry` | a keyring sealing `rs1` after `with_rs1_signing` (the `h_rs1` path): `rs1.` token, opens until its expiry, also for a negative clock | R10a, R10b |
| `seal_at_saturates_expiry_at_i64_max` | `now + ttl` saturates at `i64::MAX` (`Duration::MAX`, `now` near `i64::MAX`, zero TTL at `i64::MAX`) | R10a |
| `seal_at_with_negative_now_stores_negative_expiry` | negative and `i64::MIN` clocks store negative expiries (a zero TTL stores `now`) | R10a |
| `seal_at_expiry_landing_on_zero_never_expires` | an expiry of exactly 0 (`now = -1000`, TTL 1 s) never expires (opens at `i64::MIN` … `i64::MAX`) and equals the token sealed without a TTL | R10a, R10b (`Expired` with expiry 0) |
| `new_with_keyring_reports_exact_messages` | exact `InvalidKeyring` texts (empty keyring, duplicate id incl. `Display`, active id absent, empty id, id over 255 UTF-8 bytes counted in bytes: 256 two-byte bytes rejected, 255 accepted) and `KeyTooShort { minimum: 32, actual }` for 31 and 0 bytes | R15 (`KeyringFailure.Describes`, message texts) |
| `new_with_keyring_checks_faults_in_source_order` | per entry: id before key length before duplicate; the first faulty entry stops the loop; after the loop: emptiness, then the active id's validity, then its presence | R15 (`keyringScan`, `keyringCheck`) |
| `rs1_builders_report_exact_messages` | the four texts of `with_rs1_signing`/`with_rs1_fallback` on a single-key codec and for unknown ids `"c"`, `""`, `"A"` | R11, R12 |
| `rs1_fallbacks_append_in_call_order_and_signing_registers_its_id` | fallbacks appended in call order; `with_rs1_signing` sets `Rs1 { key_id }` and registers its id (through the `Debug` output) | R11, R12 |
| `rs1_builders_keep_fallbacks_unique_and_ordered` | no duplicate added by either builder (`any → true` branch), order kept, the last `with_rs1_signing` wins | R11, R12 |

`open_json`/`open_json_with` (R13, R14) get no new test (the existing `seal_open_roundtrips_json`
and `serde_is_reached_only_after_integrity_verification` cover both outcomes). Models newly
backed by these tests: `Duration::as_millis`, `HashMap::contains_key`, `String == str` and
`slice::Iter::any` (rows above), and the error paths of `HashMap::entry`/`is_empty`.

Runs (2026-11-25; reported by the test writer and the lead, same toolchain and command as above;
not re-run for this record):

| Command | Result |
|---|---|
| the `patched-tests.yml` command on the copy with patches 01, 02, 03 | 847 passed, 0 failed (835 + 12) |
| the same on the copy with patches 01, 02 (no patch 03; patch 03 is behaviour-preserving and changes only the bodies of `seal_at` and `open_json_with`) | 847 passed, 0 failed |
| re-translation with patches 01–03, `diff -r` against `formal/translation/` | byte-identical |
| test review (one `mcp-review` agent): 28 seeded mutants of the pinned code | 25 caught; the 3 survivors (findings t02-a-1 … a-3) killed by 2 added tests and the `2^64` ms case of the fix round |

### M01–M05 (`JsonRpcMessage::into_*`, `model.rs` 819–849)

The five functions have no caller in the crate, so only direct calls count.

| Case | Upstream test(s) | How | Status |
|---|---|---|---|
| `Request` | `src/model.rs` `tests::test_initial_request_response_serde` (5803); `tests/test_client_initialization.rs` `test_client_init_handles_jsonrpc_error` (118) | M01 direct: `Some (request, Number 1)` (5803); `Some` on the received `initialize` request (118). M02–M05 on a `Request` (`None`): no upstream test | partial upstream (M01 pass); M01–M05 patch 02 `s34_m01_m05_request`: pass |
| `Response` | `tests::test_initial_request_response_serde` (5803) | M02 direct: `Some (result, Number 1)`. M01, M03–M05 on a `Response`: no upstream test | partial upstream (M02 pass); M01–M05 patch 02 `s34_m01_m05_response`: pass |
| `Notification` | none | — | patch 02 `s34_m01_m05_notification`: pass |
| `Error`, `id = Some` | none | the client matches `Error` itself (`service/client.rs` 207–220), not through M04/M05 | patch 02 `s34_m01_m05_error_with_id`: pass |
| `Error`, `id = None` | none | `tests/test_client_lifecycle_modes.rs` `auto_startup_falls_back_for_absent_error_id` (633) sends one, but no target is called on it | patch 02 `s34_m01_m05_error_without_id`: pass |

### M06/M07 (`NumberOrString::numeric_string_value`, `matches_response_id`, `model.rs` 322–338)

Callers: M07 in `expect_response` (`service/client.rs` 183–220; a mismatch fails `serve` with
`ConflictInitResponseId`); M06 in M07, in `remove_pending_request` (`service.rs` 485–494) and in
`clear_stream_response_pending` (`streamable_http_client.rs` 827–837). The first request id of a
fresh client is `Number 0` (`AtomicU32Provider`, `service.rs` 497–507).

| Case | Upstream test(s) | How | Status |
|---|---|---|---|
| M06 `"0"` | `tests/test_client_initialization.rs` `client_initialization_accepts_stringified_numeric_response_id` (27); `tests/test_client_lifecycle_modes.rs` `discover_startup_accepts_stringified_numeric_response_id` (25) | via caller M07 → `expect_response`: `Number 0` matches `String "0"` only if M06 gives `some 0` | pass |
| M06 `"+0"`, `"-0"`, `"007"`, `""`, `"+"`, `"-"`, `" 1"`, `"1 "`, `"9223372036854775807"`, `"9223372036854775808"`, `"-9223372036854775808"`, `"-9223372036854775809"`, `"١"` (13 cases) | none | patch 02 calls M06 directly on all 14 strings (with `"0"`) and on a number | patch 02 `s34_m06_numeric_string_value_boundary_strings`: pass (13) |
| M07 `Number 1` vs `String "1"` | the two tests above | via caller `expect_response`, equivalent input `Number 0` vs `String "0"` (`true`); patch 02 `s34_m07_number_matches_numeric_string` calls M07 on the literal input | pass |
| M07 `String "1"` vs `Number 1` | none | client request ids are numbers; no upstream test sends a string request id and a numeric response | patch 02 `s34_m07_string_does_not_match_number`: pass |
| M07 equal strings | none | — | patch 02 `s34_m07_equal_strings_match`: pass |
| M07 unequal strings | none | patch 02 also `String "1"` vs `String "01"` (`false`) | patch 02 `s34_m07_unequal_strings_do_not_match`: pass |

Not in the Section 22 list, also exercised: M06 `"1"` → `some 1` via `remove_pending_request`
(`tests/test_client_initialization.rs` `client_correlates_stringified_numeric_response_id`
(68)) and via `clear_stream_response_pending` († `src/transport/streamable_http_client.rs`
`tests::clear_stream_response_pending_accepts_stringified_numeric_id` (2834),
`tests::clear_stream_response_pending_prefers_exact_string_id` (2853)); M07 unequal numbers
`Number 0` vs `Number 999` → `false` (`tests/test_client_lifecycle_modes.rs`
`auto_startup_surfaces_uncorrelated_error_id` (592)).

### M08 (`TaskStatus::is_terminal`, `model/task.rs` 38)

| Case | Upstream test(s) | How | Status |
|---|---|---|---|
| `Working` | `src/task_manager.rs` `tests::cancel_is_cooperative_and_lets_the_operation_clean_up` (672) | direct: `!is_terminal()` right after `cancel_task` (line 691); the task is still `Working` (single-threaded test runtime, no pending input) | pass |
| `InputRequired` | none | `tests::cancel_wakes_parked_input_requests` (715) reaches `InputRequired` but compares the status, not `is_terminal`; patch 02 checks all five statuses | patch 02 `s34_m08_is_terminal_each_status`: pass |
| `Completed` | `tests::cancel_is_cooperative_and_lets_the_operation_clean_up` (672); `tests/test_task.rs` `task_lifecycle_create_poll_complete` (128) | direct: the poll loop stops at `is_terminal()` and the status is `Completed` | pass |
| `Failed` | `tests::post_cancel_unrelated_error_settles_as_failed` (634) | direct, as above, status `Failed` | pass |
| `Cancelled` | `tests::cancel_settles_to_cancelled_when_operation_honors_it` (606); `tests/test_task.rs` `task_cancel_acknowledged` (184) | direct, as above, status `Cancelled` | pass |

### M09–M12 (`SamplingContent::{into_vec, is_empty, len, first}`, `model.rs` 2926–2963)

| Case | Upstream test(s) | How | Status |
|---|---|---|---|
| `Single` | `tests/test_sampling.rs` `test_backward_compat_sampling_message_with_image` (518), `test_content_to_sampling_content_conversion` (571), `test_sampling_message_with_tool_use` (408), `test_backward_compat_sampling_message_deserialization` (500) | M11 direct: `len() = 1` (518, 571); M12 direct: `first()` is the item (408, 500, 571). M09 and M10 are called by no upstream test | partial upstream (M11, M12 pass); M09–M12 patch 02 `s34_m09_m12_single`: pass |
| `Multiple []` | none | — | patch 02 `s34_m09_m12_multiple_empty`: pass |
| `Multiple [x]` | none | — | patch 02 `s34_m09_m12_multiple_one`: pass |
| `Multiple [x, y]` | none | `test_validate_rejects_mixed_content_with_tool_result` (639) builds one but reaches only `iter` (not a target) | patch 02 `s34_m09_m12_multiple_two`: pass |

### M13/M14 (`Reference::{as_prompt_name, as_resource_uri}`, `model.rs` 3741–3755)

| Case | Upstream test(s) | How | Status |
|---|---|---|---|
| `Prompt` | `tests/test_completion.rs` `test_reference_convenience_methods` (126) | direct: M13 `Some "test_prompt"`, M14 `None` | pass |
| `Resource` | same test | direct: M14 `Some "file://path/to/resource"`, M13 `None` | pass |

### T01/T02 (`SseEventSizeLimiter::{check_limit, finish_line}`, `client_side_sse.rs` 75–96)

All tests below are in `src/transport/common/client_side_sse.rs` `tests` and reach the targets via
caller: `bounded_sse_stream` (144) → `BoundedSseByteStream::poll_next` (115–141), which calls
`observe` once per chunk and turns its `Err` into `EventTooLarge` and its `Ok` into the
unchanged chunk; `observe` calls `finish_line` at a line end and `check_limit` after every other
byte. The test sees only the result, not the limiter's state.

| Case | Upstream test(s) | How | Status |
|---|---|---|---|
| sum exactly at `max` | `bounded_sse_stream_passes_event_at_exact_limit` (630); `bounded_sse_stream_discards_completed_comment_lines_from_limit` (673) | via caller: `finish_line` reaches `retained = 9 = max` (630); `check_limit` at `0 + 6 = 6 = max` (673); both `Ok` | pass |
| one above `max` | `bounded_sse_stream_rejects_unterminated_event_over_limit` (597); `bounded_sse_stream_counts_multiline_data_join_newlines` (693); `bounded_sse_stream_comments_do_not_reset_accumulated_data` (683) | via caller: `check_limit` `Err` at `17 > 16`, `10 + 9 > 18`, `8 + 7 > 14`. All three fail in `check_limit` after an ordinary byte; no test makes `finish_line` itself fail | pass |
| saturating past `max` | none | needs sizes near `usize::MAX`; patch 02 builds limiter states directly: T01 and T02 at and past `usize::MAX`, the state after `finish_line`, T03 on a line of `usize::MAX` bytes | patch 02 `s34_t01_t02_saturating_past_max`: pass; `Sse`: `satAdd usizeMax64 usizeMax64 1`, `withinLimit` at the cap, all histories with cap 2 |
| empty line | `bounded_sse_stream_resets_limit_after_event_terminator` (613); `skipped_events_do_not_grow_the_stack` (763) | via caller: the second event passes only because the empty line reset `retained` (613); 50,000 events under a 1024-byte limit (763) | pass |
| comment line | `bounded_sse_stream_discards_completed_comment_lines_from_limit` (673); `bounded_sse_stream_comments_do_not_reset_accumulated_data` (683) | via caller: comment lines add nothing (else `7 > 6`, 673) and keep `retained` (683) | pass |
| non-comment line | `bounded_sse_stream_counts_multiline_data_join_newlines` (693); `bounded_sse_stream_passes_event_at_exact_limit` (630) | via caller: `line_size + 1` is added (the error at 693 needs the joining newline) | pass |

### T03/C01/C02 (`SseEventSizeLimiter::observe`, `client_side_sse.rs` 48–73)

Via caller as for T01/T02; the inputs of these eight tests are also replayed in Lean (`Sse`,
lines 299–323).

| Case | Upstream test(s) | How | Status |
|---|---|---|---|
| LF | every test of T01/T02 | via caller | pass |
| CR (a CR not followed by LF) | none | every CR in the upstream tests is followed by LF; patch 02 checks verdict and state on the three `Sse` inputs | patch 02 `s34_t03_cr_line_ends`: pass; `Sse`: `"ab\r"`, `"ab\r\r"`, `"a\rb\n"` |
| CRLF | `bounded_sse_stream_resets_limit_after_event_terminator` (613) | via caller: `"\r\n"` inside the second chunk | pass |
| CRLF split across chunks (C01) | `bounded_sse_stream_handles_crlf_split_across_chunks` (658); `bounded_sse_stream_resets_limit_after_event_terminator` (613) | via caller, result only: both inputs give `Ok` whether or not the split LF counts as a second line end; the state that distinguishes them is pinned by `Sse` (`observeChunks (init 64) ["data: hello\r", "\n"]`), checked directly by patch 02 (the same state as for the unsplit chunk) | pass (result only); state: patch 02 `s34_c01_crlf_split_across_chunks_state`: pass |
| comment that resets nothing | `bounded_sse_stream_comments_do_not_reset_accumulated_data` (683) | via caller | pass |
| blank line resetting | `bounded_sse_stream_resets_limit_after_event_terminator` (613); `skipped_events_do_not_grow_the_stack` (763) | via caller | pass |
| event exactly at the limit | `bounded_sse_stream_passes_event_at_exact_limit` (630) | via caller | pass |
| oversize split across many chunks (C01) | `bounded_sse_stream_rejects_oversize_split_across_many_chunks` (640); `bounded_sse_stream_rejects_unterminated_event_over_limit` (597) | via caller: 20 chunks `"data: x"` under 32; 2 chunks under 16 | pass |
| empty chunk | none | no upstream test yields an empty `Bytes`; patch 02 calls `observe` on an empty chunk from four states, one of them over the bound | patch 02 `s34_t03_empty_chunk`: pass; `Sse`: `observe usizeMax64 st [] = ⟨true, st⟩` |
| error at a CR byte (state afterwards) | none | no test fails at a CR; after an `Err`, `poll_next` ends the stream, so the state is not observable through the caller; patch 02 checks it directly, and that an error stops the fold (`Sse`: `(init 1) "ab\n\n"`) | patch 02 `s34_t03_error_at_cr_state`: pass; `Sse`: `observe usizeMax64 (init 2) (bytesOf "ab\r")` |

C02 (the bound is kept) is a statement about the state and is not observable through the caller;
patch 02 checks concrete states after `Ok` calls (all within the bound) but has no test of C02
as such.

### T04 (`async_rw::without_carriage_return`, `async_rw.rs` 385)

Callers: `JsonRpcMessageCodec::decode` (560) and `decode_eof` (596), `AsyncRwTransport::receive`
(302).

| Case | Upstream test(s) | How | Status |
|---|---|---|---|
| empty | none | `receive` skips an empty line after T04 (305–308), but no test sends one; `test_decode`'s trailing empty line is never decoded (the test reads 10 items) | patch 02 `s34_t04_without_carriage_return`: pass |
| `"\r"` | none | — | patch 02 `s34_t04_without_carriage_return`: pass |
| `"a\r"` | none | no upstream test input contains a CR | patch 02 `s34_t04_without_carriage_return`: pass |
| `"a\r\r"` | none | — | patch 02 `s34_t04_without_carriage_return`: pass |
| `"a"` (no CR) | `src/transport/async_rw.rs` `test::test_decode` (641), `test::receive_ignores_parse_error` (836); `tests/test_async_rw_max_line_length.rs` `message_within_the_limit_is_delivered` (99) | via caller: the line reaches the JSON parser unchanged; dropping its last byte would make it unparsable; patch 02 `s34_t04_without_carriage_return` also calls T04 on `"a"` | pass |

### T05/T06/C05 (`is_standard_notification`, `is_standard_method`, `async_rw.rs` 396–433)

Tests in `src/transport/async_rw.rs` `test`. Caller: `should_ignore_notification` (437–457).

| Case | Upstream test(s) | How | Status |
|---|---|---|---|
| every listed name | `test_standard_notification_check` (717); `test_2026_07_28_standard_method_check` (744); `test_current_standard_notification_is_not_ignored` (755) | T05 direct on all 10 notification names (`true`); T06 direct on 3 of the 18 request names (`elicitation/create`, `server/discover`, `subscriptions/listen`); T06 (C05) via caller on 1 of the 10 notification names (`notifications/subscriptions/acknowledged`: `should_ignore_notification` returns `false` only if T06 is `true`). T06 on the other 15 request and 9 notification names: no upstream test. Patch 02: T05, T06 and C05 on all 22 + 12 core names of `Defs.Methods` (`false` for the six of `codeOmits`; 18 + 10 accepted) | partial upstream; patch 02 `s34_t05_t06_every_listed_name`: pass |
| prefix of a name | none | — | patch 02 `s34_t05_t06_prefix_and_suffix`: pass |
| suffix of a name | none | — | patch 02 `s34_t05_t06_prefix_and_suffix`: pass |
| case variant | none | — | patch 02 `s34_t05_t06_case_variant`: pass |
| `notifications/unknown` | `test_standard_notification_check` (717) | T05 direct, equivalent inputs `notifications/stderr`, `notifications/custom`, `notifications/debug` (`false`); T06 on an unknown notification is not determined: `test_unknown_notification_is_ignored` (766) returns `true` whatever T06 gives | partial upstream (T05 pass); T05 and T06 patch 02 `s34_t05_t06_notifications_unknown`: pass |
| empty | none | — | patch 02 `s34_t05_t06_empty`: pass |

`Methods` pins the list contents (and that the code lists are the core union minus `codeOmits`);
it does not evaluate T05/T06 on any input.

### T07/T08 (`tower::{default_port, AllowedPort::matches}`, `tower.rs` 1146–1171)

All tests are † in `tests/test_custom_headers.rs` `origin_validation` and reach the targets via
caller: `StreamableHttpService::handle` → `validate_dns_rebinding_headers` (1340) →
`validate_origin_header` (1357) → `origin_is_allowed` (1210), which calls T08 when scheme and
host are equal; the test sees `200` or `403`. `parse_origin_value` (1127) lowercases the scheme
before T07/T08.

| Case | Upstream test(s) | How | Status |
|---|---|---|---|
| `"http"` | `explicit_http_default_port_allows_port_less_origin` (1325) | via caller: `Exact 80`, port `None`: allowed only if T07 `"http"` = `some 80` | pass † |
| `"https"` | `explicit_https_default_port_allows_port_less_origin` (1316) | via caller: `Exact 443`, port `None`: needs `some 443` | pass † |
| `"HTTP"` | none | unreachable through the callers (lowercased) | patch 02 `s34_t07_default_port_schemes`: pass |
| `"ftp"` | none | no upstream test uses a scheme other than `http`/`https` | patch 02 `s34_t07_default_port_schemes`: pass |
| `Any` | `wildcard_port_allows_non_default_origin_port` (1370); `wildcard_port_allows_port_less_origin` (1379) | via caller: `true` with port `Some 8443` and `None` | pass † |
| `Unspecified` | `omitted_configured_port_allows_any_origin_port` (1361) | via caller: `true` with port `Some 8443` | pass † |
| `Exact 443` with `None` and `https` | `explicit_https_default_port_allows_port_less_origin` (1316) | via caller: `true` | pass † |
| `Exact 80` with `Some 8080` | `explicit_default_port_forbids_non_default_origin_port` (1343) | via caller, equivalent input `Exact 443` with `Some 8443` and `https` (`false`: an explicit port ignores the scheme default) | pass † |

Patch 02 also calls T07/T08 directly in the translated configuration (no †): `"http"` and
`"https"` (`s34_t07_default_port_schemes`), `Any` and `Unspecified` on every scheme and port tried
(`s34_t08_any_and_unspecified_match_everything`), `Exact 443` with `None` and `https`
(`s34_t08_exact_443_none_https`), and the literal `Exact 80` with `Some 8080`
(`s34_t08_exact_80_some_8080`); all pass.

Also exercised: `Exact 8443` with `None` → `false` (1352); `Exact 443` with `Some 443` → `true`
(1334); `Exact 8080` with `Some 8080` → `true` (`allowlisted_origin_is_allowed`, 1194).

### A01 (`AuthorizationManager::embedded_ipv4`, `auth.rs` 1359)

Tests: `src/transport/auth/metadata_resolver.rs` `tests::classifies_addresses` (294), via caller
`AddressClass::of` (`metadata_resolver.rs` 42–75): an IPv6 address is replaced by A01's IPv4
address when there is one; a class other than `Public` on the IPv6 path needs `::1`, `fc00::/7`
or a blocked prefix, so the class determines A01 where noted.

| Case | Upstream test(s) | How | Status |
|---|---|---|---|
| `::ffff:a.b.c.d` | `classifies_addresses` (294); `src/transport/auth.rs` `tests::metadata_url_checks_bracketed_ipv6_literals` (6817) | via caller: `::ffff:127.0.0.1` → `Loopback`, `::ffff:169.254.169.254` → `Blocked` (each needs `some`); 6817 through `is_allowed_metadata_url` → A03 → A01 | pass |
| `64:ff9b::a.b.c.d` | `classifies_addresses` (294) | via caller: `64:ff9b::a9fe:a9fe` → `Blocked`, `64:ff9b::a00:9` → `Private` (need `some`); `64:ff9b::5db8:d822` → `Public` | pass |
| `::a.b.c.d` | `classifies_addresses` (294) | via caller: `::169.254.169.254` → `Blocked` (needs `some`) | pass |
| `::` | none | — | patch 02 `s34_a01_embedded_ipv4`: pass; `Net`: `embeddedIpv4 (ipv6 [0, …, 0]) = none` |
| `::1` | `classifies_addresses` (294) | via caller: `::1` → `Loopback`; `some 0.0.0.1` would give `Blocked` | pass |
| `2002:abcd:ef01::` | `classifies_addresses` (294) | via caller, equivalent inputs: `2002:7f00:1::` → `Loopback` (needs `some 127.0.0.1` from segments `b`, `c`), `2002:a9fe:a9fe::` → `Blocked` | pass |
| `64:ff9b:1::1` (not embedded) | none | `64:ff9b:1::a9fe:a9fe` → `Blocked` (294) holds whether A01 gives `none` or `some 169.254.169.254`, so it does not determine A01 | patch 02 `s34_a01_embedded_ipv4`: pass; `Net`: `embeddedIpv4 (ipv6 [0x64, 0xff9b, 1, 0, 0, 0, 0, 1]) = none` |

Patch 02 `s34_a01_embedded_ipv4` calls A01 directly on 15 addresses of `Net`'s A01 checks (the
seven cases above, `::2`, the IPv4-translated `::ffff:0:a00:1`, a Teredo address, and the five
addresses next to the four embedding prefixes); all pass.

### A02 (`AuthorizationManager::is_disallowed_metadata_ipv4`, `auth.rs` 1343)

Section 22 asks for the first and last address of each range and the addresses just outside it
(19 inside, 18 outside, as enumerated by `Net`'s two A02 lists), plus a public address: 38 cases.
Via caller `AddressClass::of` (`Public` iff A02 is `false`) and `is_allowed_metadata_url`.
Tested addresses, all in `classifies_addresses` (294), `ip_literal_urls_follow_the_policy` (377)
and `src/transport/auth.rs` `tests::metadata_url_allows_private_literals_only_when_opted_in`
(6840): `0.0.0.0`, `93.184.216.34`, and the interior addresses `10.0.0.9`, `10.0.0.1`,
`127.0.0.1`, `127.0.0.2`, `192.168.1.1`, `100.64.0.1`, `169.254.169.254`.

| Case | Upstream test(s) | How | Status |
|---|---|---|---|
| `0.0.0.0` (first of `0/8`, and the single address `0.0.0.0`) | `classifies_addresses` (294) | via caller: `Blocked` | pass |
| a public address | `classifies_addresses` (294) | via caller: `93.184.216.34` → `Public` | pass |
| `10/8`: `10.0.0.0`, `10.255.255.255`; outside `9.255.255.255`, `11.0.0.0` | none (interior `10.0.0.1`, `10.0.0.9` only) | — | patch 02 `s34_a02_range_boundaries`: pass (4) |
| `172.16/12`: `172.16.0.0`, `172.31.255.255`; `172.15.255.255`, `172.32.0.0` | none (no address in the range) | — | patch 02 `s34_a02_range_boundaries`: pass (4) |
| `192.168/16`: `192.168.0.0`, `192.168.255.255`; `192.167.255.255`, `192.169.0.0` | none (interior `192.168.1.1`) | — | patch 02 `s34_a02_range_boundaries`: pass (4) |
| `127/8`: `127.0.0.0`, `127.255.255.255`; `126.255.255.255`, `128.0.0.0` | none (interior `127.0.0.1`, `127.0.0.2`) | — | patch 02 `s34_a02_range_boundaries`: pass (4) |
| `169.254/16`: `169.254.0.0`, `169.254.255.255`; `169.253.255.255`, `169.255.0.0` | none (interior `169.254.169.254`) | — | patch 02 `s34_a02_range_boundaries`: pass (4) |
| `255.255.255.255`; outside `255.255.255.254` | none | — | patch 02 `s34_a02_range_boundaries`: pass (2) |
| `224/4`: `224.0.0.0`, `239.255.255.255`; `223.255.255.255`, `240.0.0.0` | none | — | patch 02 `s34_a02_range_boundaries`: pass (4) |
| `0/8`: last `0.255.255.255`; outside `1.0.0.0` | none | — | patch 02 `s34_a02_range_boundaries`: pass (2) |
| `100.64/10`: `100.64.0.0`, `100.127.255.255`; `100.63.255.255`, `100.128.0.0` | none (interior `100.64.0.1`) | — | patch 02 `s34_a02_range_boundaries`: pass (4) |
| `198.18/15`: `198.18.0.0`, `198.19.255.255`; `198.17.255.255`, `198.20.0.0` | none | — | patch 02 `s34_a02_range_boundaries`: pass (4) |

Every A02 case uncovered upstream is evaluated by `Net` (A02 lists, lines 253–266) and, with the
same two lists (19 inside; 18 outside plus the public `8.8.8.8`), by patch 02
`s34_a02_range_boundaries` (direct; `240.0.0.0` is not blocked: the bug recorded under H8).

### A03/C04 (`AuthorizationManager::is_disallowed_metadata_ipv6`, `auth.rs` 1370)

Callers: `is_allowed_metadata_url` (`auth.rs` 1412) through `is_disallowed_metadata_host`, and
`AddressClass::of` on its IPv6 path, which it takes only when A01 gives `none`: for an address
that embeds IPv4, `AddressClass::of` calls A01 and A02 directly and never A03. The prefix
boundaries are the 12 inside and 10 outside addresses of `Net`'s two A03 lists (lines 274–297):
22 cases, plus 4 embedded forms and a public address: 27 cases.

| Case | Upstream test(s) | How | Status |
|---|---|---|---|
| `::1` | `classifies_addresses` (294); `tests::metadata_url_checks_bracketed_ipv6_literals` (6817) | via caller: `Loopback`; `[::1]` rejected for a public base | pass |
| `::` | none | — | patch 02 `s34_a03_prefix_boundaries`: pass |
| `ff00::/8`: `ff00::`, `ffff:…:ffff`; outside `feff:ffff:…:ffff` | none (no multicast IPv6 in any test) | — | patch 02 `s34_a03_prefix_boundaries`: pass (3) |
| `fe80::/10`: `fe80::`, `febf:ffff:…:ffff`; outside `fe7f:ffff:…:ffff`, `fec0::` | none (interior `fe80::1`, 294, 6817) | — | patch 02 `s34_a03_prefix_boundaries`: pass (4) |
| `fc00::/7`: `fc00::`, `fdff:ffff:…:ffff`; outside `fbff:ffff:…:ffff`, `fe00::` | none (interior `fd00::1`, 294) | — | patch 02 `s34_a03_prefix_boundaries`: pass (4) |
| `2001::/32`: `2001::`, `2001:0:ffff:…:ffff`; outside `2000:ffff:…:ffff`, `2001:1::` | none (interior `2001:0:4136:e378::1`, 294) | — | patch 02 `s34_a03_prefix_boundaries`: pass (4) |
| `64:ff9b:1::/48`: `64:ff9b:1::`, `64:ff9b:1:ffff:ffff:ffff:808:808`; outside `64:ff9b::1:0:0`, `64:ff9b:2::`, `64:ff9b:0:ffff:ffff:ffff:ffff:ffff` | none (interior `64:ff9b:1::a9fe:a9fe`, 294) | — | patch 02 `s34_a03_prefix_boundaries`: pass (5) |
| embedded blocked IPv4, IPv4-mapped | `tests::metadata_url_checks_bracketed_ipv6_literals` (6817) | via caller `is_allowed_metadata_url`: `[::ffff:127.0.0.1]` rejected only if A03 is `true` (C04: equals A02 of `127.0.0.1`) | pass |
| embedded blocked IPv4, NAT64 | `classifies_addresses` (294) | `64:ff9b::a9fe:a9fe` → `Blocked` exercises A01 and A02 (the right-hand side of C04), not A03 | partial upstream; A03 and C04 patch 02 `s34_a03_c04_embedded_forms`: pass |
| embedded blocked IPv4, IPv4-compatible | `classifies_addresses` (294) | `::169.254.169.254`, as above | partial upstream; A03 and C04 patch 02 `s34_a03_c04_embedded_forms`: pass |
| embedded blocked IPv4, 6to4 | `classifies_addresses` (294) | `2002:a9fe:a9fe::`, as above | partial upstream; A03 and C04 patch 02 `s34_a03_c04_embedded_forms`: pass |
| a public IPv6 address | `classifies_addresses` (294) | via caller: `2606:4700::1111` → `Public` (A01 `none`, A03 `false`) | pass |

Every A03/C04 case uncovered upstream is evaluated by `Net` (A03/C04 lists, lines 274–309).

**`Defs/Net.lean` additive change (2026-11-26, accepted by the human A01–A03 spec owner).**
`formal/proofs/Proofs/Defs/Net.lean` gained `public import Rmcp.Types` and a section "Decidable
equality of addresses" (`DecidableEq` instances for `core.net.ip_addr.Ipv4Addr` and `Ipv6Addr`,
decided on the octet and segment lists, and `deriving instance DecidableEq` for
`rmcp.core.net.ip_addr.IpAddr`), moved there in the `metadata_resolver.rs` spec round 2 so that
every statement comparing IP addresses shares one equality. No A01–A03 definition, check or
statement changed; the regression checks only moved (31 lines; citations above updated). The
A01–A03 `#print axioms` lists (`propext`, `Classical.choice`, `Quot.sound`) are unchanged: `lake
build --wfail` passes with the `#guard_msgs` axiom checks, and `scripts/lean-guard.sh axioms`
passes (2026-11-26).
Patch 02 calls A03 directly on the 12 inside and 11 outside addresses of `Net`'s boundary lists
(`s34_a03_prefix_boundaries`, with the public `2606:4700::1111`) and on 8 blocked and 4 public
embedded forms (`s34_a03_c04_embedded_forms`: `Net`'s two embedded-form lists plus
169.254.169.254 in the NAT64, IPv4-compatible and 6to4 forms of the partial rows), where it also
checks C04 (A03 equals A02 of A01's address) on all 12.

### Summary

141 cases. Upstream tests: 6 pass directly, 31 pass via a caller (3 of them with an equivalent
input: M07 `Number 0`/`String "0"`, T08 `Exact 443`/`Some 8443`, A01 `2002:7f00:1::`), 8
partial, 96 uncovered. Patch 02 (34 tests, direct calls) covers the 96 uncovered cases and the
missing parts of the 8 partial ones (M01–M05 3 + 2 partial, M06/M07 16, M08 1, M09–M12 3 + 1
partial, T01/T02 1, T03/C01/C02 3, T04 4, T05/T06/C05 4 + 2 partial, T07/T08 2, A01 2, A02 36,
A03/C04 21 + 3 partial), so no Section 22 case is left uncovered. No test failed and no expected
value (taken from the statements and `Defs`) disagreed with the code. Before patch 02, the
uncovered cases with no Lean regression check either (only the theorems) were those of M01–M05,
M06/M07, M08 (`InputRequired`), M09–M12, T04, T05/T06/C05 and T07/T08; the uncovered T01–T03,
A01, A02 and A03 cases are also evaluated by `Sse` or `Net`. The tests marked † still need
`transport-streamable-http-client-reqwest`; patch 02 covers the T07/T08 cases directly without it.

## Spec statements and proofs

Phase 1: the facts later proofs needed (72 statements, success and failure cases) are proved in
`formal/proofs/Proofs/External/` (`Base64.lean`, `String.lean`, `Prim.lean`, `Std.lean`);
`formal/specs/Specs/External.lean` restates them as theorems `Theorems.External.*` and checks
their axioms with `#print axioms` (each at most `propext`, `Classical.choice`, `Quot.sound`).
The statements entered git already incorporated, in commit `af41799` (`git show
af41799:formal/specs/Specs/External.lean`); they are now restated in
`formal/proofs/Proofs/Internal/External.lean`.

Phase 2: 43 statements, drafted by an AI agent (Claude Code `mcp-spec`, `claude-opus-5-5`), reviewed
(round 1: two agents, no blocking finding), signed off by the spec owner on 2026-11-23, proved by
separate `mcp-lean` agents and restated in the project file (now
`formal/proofs/Proofs/Internal/External.lean`). Each law depends on at most `propext`,
`Classical.choice` and `Quot.sound`.

## Skills externals (translation patch 04, targets K01–K20)

Translation patch 04 (`formal/trusted/patches/04-skill-public.patch`; human decisions
2026-11-25) lets the twenty public functions of `crates/rmcp/src/model/skill.rs` translate. It
adds the private module `skill::prim` (twelve one-line wrappers, opaque in the translation)
and makes the remaining code call only the standard-library and crate functions below. Every
model is a definition or a `structure` in `formal/trusted/Rmcp/{Types,Funs}External.lean`
(section "Public `skill.rs` API"), with its source cited in its docstring; `axioms.lock` stays
empty. Three values are `opaque` constants, which add no axiom; their laws are not stated and
are taken as hypotheses by the statements that need them (human decision 2026-11-25):

| Opaque constant | Stands for | Why it is not computed |
|---|---|---|
| `ExtModel.sha256 : List U8 → Array U8 32` | SHA-256 (FIPS 180-4) of `sha2 0.11.2` | correctness of the `sha2` crate is out of scope (plan Section 4), as for `hmacSha256` |
| `ExtModel.nfkc : List Char → List Char` | NFKC of `unicode-normalization 0.1.26` | the normalization tables are not modelled |
| `ExtModel.generalCategory : Char → GeneralCategory` | the General_Category tables of `unicode-general-category 1.1.0` | the tables are not modelled |

Every other model is exact, computable and structurally recursive, so it can be evaluated:
`formal/proofs/Proofs/External/Skill.lean` checks the percent decoder, `u8::from_str_radix`,
the `/` and `%` splitting, the last-segment index, the control percent-encoding and the char
boundary test on small inputs by kernel evaluation (`decide`/`rfl`). Each external has a proved
spec theorem `<generated name>_spec` there (no `sorry`; each depends on at most `propext`,
`Classical.choice`, `Quot.sound`).

New trusted helper definitions (namespace `ExtModel`): `usize`, `collectVec` (a `Vec` or the
deterministic capacity-overflow panic), `stringsOfBytes`, `splitBytes`, `lastSegmentStart`,
`digitValue?`, `hexDigitValue?`, `u8DigitLoop`, `u8FromAscii`, `isControlOrNonAscii`,
`upperHexDigit`, `percentEncodeByte`, `percentEncodeControls`, `percentDecodeFrom`,
`percentDecode`, `asciiUppercase`, `sliceIterAll`, `listContainsEq` (membership in the element
list of the `HashSet` model), `bytesLt` (Rust's `Ord` of byte slices, hence of `String`s),
`mapInsert` (`BTreeMap::insert` into the entries sorted by key), `isCharBoundary`, and the length
lemmas `length_take_le_max`, `length_drop_le_max`.

`serde_json::Map` is modelled exactly as the `BTreeMap` it is in this configuration
(`Cargo.lock`: `serde_json 1.0.154` depends on `itoa`, `memchr`, `serde`, `serde_core`, `zmij`
only, so the `preserve_order` feature and `indexmap` are off; lead decision 2026-11-25): its
entries are listed ascending by key in Rust's `String` order (`bytesLt` on the UTF-8 bytes), and
`insert` replaces the value of an existing key in place or inserts the new key at its sorted
position, so each Rust map has exactly one model value. Sources (pinned versions):
`serde_json-1.0.154/src/map.rs` lines 28–29 and 38–39 (`#[cfg(not(feature = "preserve_order"))]
type MapImpl<K, V> = BTreeMap<K, V>;`), 137–139 (`Map::insert` is `self.map.insert(k, v)`) and
329–333 (`Map::keys` is `self.map.keys()`); the standard library of `nightly-2026-09-17`,
`alloc/src/collections/btree/map.rs` line 2691 (`BTreeMap::iter`: "Gets an iterator over the
entries of the map, sorted by key"; `keys` at line 2767 iterates the same order),
`alloc/src/string.rs` lines 350–355 (`#[derive(PartialEq, PartialOrd, Eq, Ord)] pub struct String
{ vec: Vec<u8> }`, so `String` compares its bytes), `core/src/str/traits.rs` lines 18–23 (`impl
Ord for str`: `self.as_bytes().cmp(other.as_bytes())`) and `core/src/slice/cmp.rs` lines 35–40
(`Ord for [T]` compares lexicographically). Rust vector (2026-11-25, a scratch crate outside the
repository, `serde_json = "=1.0.154"` resolved to 1.0.154 from crates.io without
`preserve_order`, `CARGO_TARGET_DIR=<scratch>/target cargo run -q`, cargo 1.92.0): inserting
`"a"`, `"B"`, `"é"`, `"z"` into `serde_json::Map::new()`, in that order and in the reverse order
`"z"`, `"é"`, `"B"`, `"a"`, gives `keys()` = `["B", "a", "z", "é"]` both times, bytes `[42]`,
`[61]`, `[7a]`, `[c3, a9]`, ascending byte-lexicographically (an uppercase letter before a
lowercase one, a non-ASCII char after ASCII), the order of `bytesLt` (evaluated in
`Proofs.External.Skill`: `"B" < "a"`, `"z" < "é"`). `Proofs.External.Skill` proves that the
model keeps the entries sorted (`sortedByKey_mapInsert`) and returns the old value
(`mapInsert_fst_of_sortedByKey`), and evaluates three insertions. `HashSet` stays an element
list whose order carries no meaning (Rust's `HashSet` order is unspecified); review rule: no
statement may depend on that order.

`<ParseIntError as Debug>::fmt` is a total, not exact, model (lead decision 2026-11-25): it
returns `Ok(())` and leaves the formatter unchanged, because `core::fmt::Formatter` is opaque in
the Aeneas library (the written text has no representation) and the only caller is the
`expect` of `push_normalized_part`, whose panic path two checked hexadecimal digits never take.
It is a stated exception of the trusted base.

**Patch-induced premises for K13 and K16** (translation patch 04; the patch header lists
both). Each is a premise a statement may need although the original function would not, and the
statement's docstring says so.

1. NFKC length (hunks H2 and H4; K13). The patched copy
collects each NFKC form into a `Vec<char>` (`prim::nfkc`, modelled with `ExtModel.collectVec 4`),
where the original streams it (`Iterator::eq`, `enumerate`). It therefore adds a
"capacity overflow" panic when a form would exceed `isize::MAX` bytes, which the original never
allocates; NFKC expands a char to at most 18 chars (UAX #15, U+FDFA of 3 UTF-8 bytes), so the
panic needs a name or decoded segment of more than of the order of `isize::MAX / 24` bytes and is
unreachable in practice. A statement of K13 (`Skill::validate`) may take, as an explicit
premise for the strings `t` passed to `prim::nfkc`, the bound `4 * (ExtModel.nfkc t.toList).length
≤ maxStringBytes` of `nfkc_spec` (or a premise about that `t` that implies it); the original
function would not need it, and the statement's docstring says so (review rule of the `nfkc`
constant, `formal/README.md`, "Trusted base").

2. Split vector length (the `prim` wrappers `split_slash` and `split_percent`, hunks H5 and H6;
K13 through `manifest_resource_key` and `normalize_percent_encoding`, K16 through
`normalize_percent_encoding`). The patched copy collects the parts of `s.split(c)` into a
`Vec<String>` (24 bytes per element on the translated 64-bit target; modelled with
`ExtModel.collectVec 24`), where the original iterates the split lazily: H6's `for part in
escaped.split('%')` allocates nothing, and H5 collects only the resolved segments, into a
`Vec<&str>` of 16 bytes per element. The patched copy therefore panics with "capacity overflow"
when 24 times the number of parts exceeds `isize::MAX`, where the original does not, and
`split_slash_spec`/`split_percent_spec` take the premise `hlen : 24 * (splitBytes sep
s.val).length ≤ maxStringBytes` (`sep` = `/` or `%`); statements of K13 and K16 will need it for
the strings they split. It is unreachable on the translated target `x86_64-unknown-linux-gnu`:
`isize::MAX` is 2^63 − 1, a virtual address has at most 57 bits (5-level paging; 48 with
4-level), so every `&str` has fewer than 2^57 bytes and at most 2^57 parts (one more than its
separator bytes), and 24 · 2^57 = 3 · 2^60 < 2^63 − 1. (`maxStringBytes` is `isize::MAX` of the
Lean platform, so the premise is stated, not derived.) Running out of memory while copying the
parts aborts the process in both versions and is not modelled.

Tests (all in `crates/rmcp/src/model/skill.rs`, `mod tests`, unchanged by patch 04; they pass on
the patched copy, 847 library tests in the translated feature configuration plus `macros`,
`cargo test --locked -p rmcp --no-default-features --features
request-state,server,client,client-side-sse,transport-streamable-http-server,transport-streamable-http-client,auth,macros
--lib` in `.llbc/work/` after `scripts/apply-patches.sh`, 2026-11-25):

| Models | Exercised by |
|---|---|
| `prim::sha256`, array `IntoIter` (`into_iter`, `next`), `char::from(u8)` | `sha256_digest::matches_the_digest_in_the_spec_example`, `skill_resource_verify::*` |
| `prim::{find_query_or_fragment, strip_suffix, last_slash_segment}`, `str::is_empty`, `bool::then_some`, `Option` `?` (`branch`, `from_residual`) | `skill_name_from_uri::*` (4 tests), `skill_validate::*` |
| `prim::strip_prefix`, `str::bytes`, `Bytes::all` | `is_sha256_digest::*` (4 tests), `rejects_resources_with_a_different_root` |
| `prim::{split_slash, join_slash}`, `Vec::pop`, `str::split_at`, `String::as_str` | `manifest_paths_must_resolve_to_files_within_the_skill_directory`, `skill_validate::rejects_two_spellings_of_the_same_manifest_file` |
| `prim::{percent_encode_controls, split_once_percent, split_percent}`, `str::split_at_checked`, `u8::{is_ascii_hexdigit, is_ascii_alphanumeric, from_str_radix}`, `str::to_ascii_uppercase`, `Cow::{deref, into_owned}` | `validate_skills::rejects_equivalent_percent_encodings_of_a_skill_uri`, `validate_skills::compatibility_equivalent_names_can_identify_distinct_resources`, `skill_validate::rejects_two_spellings_of_the_same_manifest_file` |
| `prim::{percent_decode_utf8, nfkc}` | `skill_validate::{accepts_a_percent_encoded_unicode_name, compares_unicode_names_in_normalized_form, rejects_invalid_encoded_name_matches, rejects_a_name_that_differs_from_the_uri}` |
| `get_general_category`, `char` equality | `skill_validate::enforces_the_agent_skills_name_rules` |
| `HashSet::{with_capacity, insert}` | `skill_validate::rejects_a_duplicate_file`, `validate_skills::rejects_the_same_skill_listed_twice` |
| `Option::as_deref` | `resource_is_directory::*` (2 tests) |
| `serde_json::Map::new` | every test that builds a `SkillFrontmatter` |

Not exercised by a library test: `serde_json::Map::insert` (`SkillFrontmatter::with_field`),
`<ParseIntError as Debug>::fmt` (total model; reached only on the `expect` panic path, which two
hexadecimal digits never take) and the default `Iterator::all` (declared by the template, called
by no generated definition).

**Linkage of the skills targets** (plan Section 19, amendment 2026-11-25). For the linkage run,
`scripts/check-original-linkage.sh` drops from the copy's Charon settings the seven skills start
points whose targets need patch 04 (`rmcp::model::skill::_::from_bytes`, `…::_::verify`,
`…::sha256_digest`, `…::_::validate`, `…::skill_name_from_uri`, `…::is_sha256_digest`,
`…::validate_skills`: K05–K07, K13–K16) and the opaque entry `rmcp::model::skill::prim`, which
exists only in the patched copy; in that run (`RMCP_TARGET_SET=phase2`)
`scripts/aeneas-translate.sh` checks only the ORIGINAL targets and fails if any of the ten
`PATCH04_TARGETS` (the seven targets and the private helpers `is_valid_skill_name`,
`manifest_resource_key`, `normalize_percent_encoding` of K13) has a definition in the unpatched
`Funs.lean` (then the patch-04 list and the call graph disagree, and an ORIGINAL claim would skip
checking that block). Runs (2026-11-25, Aeneas `nightly-2026.11.24-fb44cb4`, Charon `0.1.324`,
Rust `nightly-2026-09-17`), in a scratch clone of the repository at `b363a8a` with the working
tree of this change committed on top (scratch commit `b3e26c4ac350b509cef91370a4df01f58ff142a0`;
`.aeneas` symlinked, the git-ignored `formal/translation/Rmcp/*_Template.lean` copied; the later
edits of this round touch no file the check reads), each into a fresh scratch directory outside
the repository:

- `scripts/check-original-linkage.sh <scratch>/run1` on `b3e26c4`: **exit 0**. Source is upstream
  `7caec76` (src tree `4efe696…` and both digests); 33 Phase 2 `start_from` entries, `exclude`
  `['serde']`, 33 opaque entries; 29 `_` globs match their expected items; all 38 ORIGINAL targets
  defined, no `sorry`; blocks identical up to `Source:`: `Funs.lean` 60/60, `Types.lean` 40/40,
  `FunsExternal_Template.lean` 34/34, `TypesExternal_Template.lean` 10/10.
- Negative test, scratch commit `a847d99786afda9aab93bcca66cf4c8ac0fa5415` (on `b3e26c4`, only
  `model.skill.Skill.name`, the ORIGINAL target K12, added to `PATCH04_TARGETS` in
  `scripts/aeneas-translate.sh`), `scripts/check-original-linkage.sh <scratch>/run2`: **exit 1**
  with `[aeneas-translate] error: patch-04 target model.skill.Skill.name is translated from the
  unmodified source; update PATCH04_TARGETS and check-original-linkage.sh` and `[linkage] error:
  translation of the unmodified source failed`.

### NFKC expansion bound (premise `hexp` of `Defs.Skill.NfkcFits.of_utf8ByteSize_le`, K13/K16; restated in `formal/proofs/Proofs/Internal/Model/Skill.lean`)

The bridge lemma takes the law `∀ cs, (ExtModel.nfkc cs).length ≤ 18 * cs.length` as an explicit
premise (implication-form law, STATUS "Trusted base" rule U3). It is not a Unicode stability
guarantee, so it was checked on the pinned crate `unicode-normalization 0.1.26` (Unicode 18.0.0),
2026-11-25 (lead decision: universal form kept): over every Unicode scalar value the largest
per-character NFKC and NFKD lengths are both 18 (at U+FDFA), and over 2,000,000 random strings drawn
from 14,670 characters that decompose, compose or combine (Hangul included) there were 0 violations
of `nfkc ≤ nfkd = sum of per-character nfkd ≤ 18·len`. Command: `cargo run --release --offline`
(scratch crate, `unicode-normalization = "=0.1.26"`, exit 0). Program:

```rust
use unicode_normalization::UnicodeNormalization;
fn main() {
    // exhaustive: largest per-character NFKC / NFKD length over all scalar values
    let (mut mk, mut md, mut at) = (0usize, 0usize, 0u32);
    for c in (0u32..=0x10FFFF).filter_map(char::from_u32) {
        let s = c.to_string(); let k = s.nfkc().count(); let d = s.nfkd().count();
        if k > mk { mk = k; at = c as u32; } if d > md { md = d; }
    }
    println!("max per-char nfkc {} nfkd {} at U+{:04X}", mk, md, at);
    // per-string: nfkc count <= nfkd count = sum of per-char nfkd counts
    let mut x: u64 = 0x9E3779B97F4A7C15;
    let mut worst = 0f64; let mut viol = 0u64;
    let pool: Vec<char> = (0u32..=0x10FFFF).filter_map(char::from_u32)
        .filter(|c| { let s=c.to_string(); s.nfkd().count()>1 || s.nfkc().count()!=1 || unicode_normalization::char::canonical_combining_class(*c)!=0 || (0x1100..0x11FF).contains(&(*c as u32)) || (0xAC00..0xD7A4).contains(&(*c as u32)) }).collect();
    println!("pool {}", pool.len());
    for _ in 0..2_000_000u64 {
        x ^= x << 13; x ^= x >> 7; x ^= x << 17;
        let len = 1 + (x % 12) as usize;
        let mut s = String::new();
        for i in 0..len { let y = x.rotate_left(5*i as u32 + 1).wrapping_mul(0x2545F4914F6CDD1D); s.push(pool[(y as usize) % pool.len()]); }
        let n = s.chars().count(); let k = s.nfkc().count(); let d = s.nfkd().count();
        let per: usize = s.chars().map(|c| c.to_string().nfkd().count()).sum();
        if k > 18*n || k > d || d != per { viol += 1; }
        let r = k as f64 / n as f64; if r > worst { worst = r; }
    }
    println!("violations {} worst ratio {}", viol, worst);
}
```
Output: `max per-char nfkc 18 nfkd 18 at U+FDFA`, `pool 14670`, `violations 0 worst ratio 18` (lead re-run 2026-11-25).

## Address-policy externals (translation patch 05, targets N01, N03–N11)

Translation patch 05 (`formal/trusted/patches/05-metadata-resolver.patch`; human decisions
2026-11-25) lets the pure functions of `crates/rmcp/src/transport/auth/metadata_resolver.rs`
translate (N02 `SystemResolver::resolve` is not a target; the async shells of `resolve` and
`with_lookup` stay unverified glue). It adds the module `metadata_resolver::prim` (five
functions, opaque in the translation) and the newtype `Lookup` (opaque), and makes the remaining
code call only the standard-library and `url` functions below. Every model is a definition or a
`structure` in `formal/trusted/Rmcp/{Types,Funs}External.lean` (section "`metadata_resolver.rs`
address policy"), with its source cited in its docstring; `axioms.lock` stays empty. Since
patch 05 only the type `url::Url` of the `url` crate is opaque in the Charon settings (was the
whole crate), so `url::host::Host` and `url::parser::ParseError` are translated from the source
of the pinned `url 2.5.9` (`Rmcp.Types`). Seven new `opaque` constants, which add no axiom;
their laws are not stated and are taken as hypotheses by the statements that need them (human
decision 2026-11-25):

| Opaque constant | Stands for | Why it is not computed |
|---|---|---|
| `ExtModel.UrlCarrier : Type` (carrier of `url.Url`) | a parsed `url::Url` (`url-2.5.9/src/lib.rs` lines 226–249) | the URL parser is not modelled (human decision 2026-11-25) |
| `ExtModel.urlParse : List U8 → Result Url ParseError` | `Url::parse` (lines 340–342) | as above |
| `ExtModel.urlHost : Url → Option (Host Str)` | `Url::host` (lines 1200–1207) | `Url` is abstract |
| `ExtModel.urlHostStr : Url → Option Str` | `Url::host_str` (lines 1161–1167) | `Url` is abstract; its agreement with `urlHost` is not stated |
| `ExtModel.LookupCarrier : NonemptyType` (carrier of `Lookup`) | the newtype `Lookup(Arc<dyn Resolve>)` of hunk H1 | trait objects are not translated (Aeneas: "Dynamic trait types are not supported yet") |
| `ExtModel.systemLookup : Lookup` (noncomputable) | `Lookup(Arc::new(SystemResolver))` (`prim::system_lookup`) | `Lookup` is abstract; only the untranslated async `resolve` calls it |
| `ExtModel.proxyEnvValues : Vec String` | the proxy environment variables that are set (`prim::proxy_env_values`) | an environment reading; one constant, under the clock rule (below) |

**Opaque-constant rule for the environment** (human decision 2026-11-25: the rule of
`ExtModel.nowMs` extended to the environment). `proxyEnvValues` is one constant, so a model of
`MetadataAddressResolver::new` (N03), the only caller of `prim::proxy_env_values`, is pure,
whereas in Rust two calls may read different environments. Review rule (also at
`ExtModel.proxyEnvValues` and in `formal/README.md` and `formal/README.md`, "Trusted base"):
no statement has a premise or conclusion about the value of `proxyEnvValues` or relates two
readings; a statement may name `proxyEnvValues`, `…prim.proxy_env_values` or
`…MetadataAddressResolver.new` only to say that `new` passes the values read to
`with_proxy_hosts` (so that it holds for every environment), besides the model's own spec
`prim.proxy_env_values_spec` (`result = proxyEnvValues`). Human decision 2026-11-26: a statement
may also state a fact about `MetadataAddressResolver::new` that does not depend on the proxy
environment, such as that the fields of the result not set from the proxy values (`base_ip`,
`base_classes`, `lookup`) equal those of `with_base_url u` with the lookup
`ExtModel.systemLookup`, proved from the body for every value of `proxyEnvValues`; nothing is
assumed about `proxyEnvValues` itself beyond its own spec.
Human decision 2026-11-26 (spec round 1, finding P1; an extension of this rule): for `new u = ok r`,
and with no premise on the value of `ExtModel.proxyEnvValues`, a statement may also conclude (1)
that `r.unfiltered_hosts` (as bytes) equals `ExtModel.proxyEnvValues.val.filterMap (fun p =>
Defs.MetadataResolver.proxyHost (Defs.utf8Bytes p))` (`Defs.MetadataResolver.proxyHost` is defined in `formal/proofs/Proofs/Defs/MetadataResolver.lean`), naming `proxyEnvValues` only as the values `new` reads and passes to
`with_proxy_hosts`; (2) the invariant that every unfiltered host of `new`'s result is a normalized
host; (3) production security theorems about resolvers built by `new` (e.g. a filtered host's
returned addresses are Public for a non-localhost domain base). Still no premise on, and no other
statement about, the value of `proxyEnvValues`.
Human decision 2026-11-26 (spec round 3, R1): for `new u = ok r`, statements of the form `host ∈
r.unfiltered_hosts ↔ Defs.utf8Bytes host ∈ ExtModel.proxyEnvValues.val.filterMap
(Defs.MetadataResolver.proxyHost ∘ Defs.utf8Bytes)` and premises `host ∉ r.unfiltered_hosts` in
production theorems count as restatements of items (1) and (3).
Human decision 2026-11-26 (spec sign-off, T1): premises of the form `Defs.utf8Bytes host ∈
ExtModel.proxyEnvValues.val.filterMap (Defs.MetadataResolver.proxyHost ∘ Defs.utf8Bytes)` (the host
is a configured proxy host; used by
`MetadataAddressResolver.allowed_addresses_eq_ok_some_of_new_eq_ok_of_mem_proxyHosts`) also count as
restatements of P1.
The reading itself does not panic:
`std::env::var` returns `Err` for an unset or non-Unicode variable (`std/src/env.rs` lines
228–236) and the six names of `PROXY_ENV_VARS` are fixed, non-empty and contain no `=` or NUL.

Exact models (computable, so they can be evaluated; examples in
`formal/proofs/Proofs/External/MetadataResolver.lean`), with their Rust source (`nightly-2026-09-17`
`rust-src` unless stated):

| Model | Source |
|---|---|
| `prim::trim_end_dots`: drop the trailing bytes 46 (`ExtModel.dropTrailingDots`) | `core/src/str/mod.rs` lines 2643–2654 (`trim_end_matches`), `core/src/str/pattern.rs` lines 330–338 (`next_reject_back` of the `CharSearcher`); `'.'` is the single UTF-8 byte 46 |
| `prim::ends_with`: byte suffix (`<:+`) | `core/src/str/mod.rs` lines 1445–1450, `core/src/str/pattern.rs` lines 1030–1035 (`haystack.as_bytes().ends_with(self.as_bytes())`) |
| `prim::contains`: byte infix (`<:+:`), `true` for `""` | `core/src/str/mod.rs` lines 1382–1384, `core/src/str/pattern.rs` lines 987–1015 (`is_contained_in` for `&str`) |
| `<IpAddr as PartialEq>::eq`: same variant, equal octets / segments | `core/src/net/ip_addr.rs` lines 29–37 (derived), 71–76 and 165–170 (derived on the octets) |
| `IpAddr::V4` as a function, and its `FnOnce::call_once` | `core/src/net/ip_addr.rs` line 33; the compiler's `FnOnce` impl of a function item |
| `SocketAddr::ip` | `core/src/net/socket_addr.rs` lines 193–198, 394–396, 492–494 |
| `Option::map_or` | `core/src/option.rs` lines 1224–1233 |
| `str::to_ascii_lowercase` (`ExtModel.asciiLowercase`) | `alloc/src/str.rs` lines 889–894, `alloc/src/slice.rs` lines 678–680, `core/src/num/mod.rs` lines 710–713 and 584 |
| `<String as PartialEq<&str>>::eq`: byte equality | `alloc/src/string.rs` lines 2740–2742 (`impl_eq! { String, &str }`, line 2764) |
| `<Arc<[T]> as From<Vec<T>>>::from` | `alloc/src/sync.rs` lines 4212–4226, 2467–2476, 416–426 |
| structures `SocketAddrV4 { addrIp, addrPort }`, `SocketAddrV6 { addrIp, addrPort, addrFlowinfo, addrScopeId }` | `core/src/net/socket_addr.rs` lines 79–84 and 145–152 |

The `FnOnce::call_once` model has the type of its use in `Rmcp.Funs`
(`(Ipv4Addr → Result IpAddr) → Ipv4Addr → Result IpAddr`); the Aeneas template prints the
first parameter without parentheses (`Ipv4Addr → Result IpAddr → Ipv4Addr → Result IpAddr`),
which does not build (measured 2026-11-25: "Type mismatch" at the instance in `Funs.lean`). New
trusted helpers (namespace `ExtModel`): `dropTrailingDots` with the length lemma
`length_dropTrailingDots_le_max`, and `asciiLowercase`. Each external has a proved spec
theorem `<generated name>_spec` in `Proofs.External.MetadataResolver` (no `sorry`; each depends
on at most `propext`, `Classical.choice`, `Quot.sound`), plus `call_once_ip_addr_v4_spec` and
`map_or_ip_addr_v4_spec` for the one instance of the translation,
`to_ascii_lowercase_spec_of_eq_utf8` for every Rust `&str`, `to_ascii_lowercase_spec_of_isUtf8`
for the same under the premise `ExtModel.IsUtf8` (below), and `to_ascii_lowercase_eq_fail` for
the model's other branch (bytes whose lowercase mapping is not UTF-8); `call_once_spec` is the
equation `call_once f a = f a`, so it covers the failure of `f` too. `isUtf8_dropTrailingDots` and
`isUtf8_map_asciiLowercase` prove that `dropTrailingDots` and the lowercase mapping keep the
UTF-8 premise.

**UTF-8 premise** (review rule, translation patch 05, human decisions 2026-11-25/2026-11-26: rule
(ii) 2026-11-26, nested `&str` 2026-11-26; the same statement is in the docstring of
`ExtModel.IsUtf8`, in `formal/README.md` and in `formal/README.md`, "Trusted base").
`Url::host` returns a `Host<&str>` and `Url::host_str` an `Option<&str>`, and every Rust `&str` is
valid UTF-8, but the Aeneas `Str` is not constrained: a statement may assume that a `Str` is valid
UTF-8 (the Rust `&str` invariant) (i) only as the premise `ExtModel.IsUtf8 s.val`
(`ExtModel.IsUtf8 l := ∃ t : String, l = ExtModel.utf8 t`, a definition in
`formal/trusted/Rmcp/FunsExternal.lean`; no axiom or model asserts it), and (ii) only for (a) a
`&str` argument of the function the statement is about, or a `&str` carried by an argument (such
as the domain `d` of the argument `host : Host<&str>` of
`AuthorizationManager::is_loopback_metadata_host`, `host = url.host.Host.Domain d`), and (b) the
hosts that the opaque `url` functions return: `ExtModel.IsUtf8 d.val` for
`ExtModel.urlHost u = some (url.host.Host.Domain d)` and `ExtModel.IsUtf8 h.val` for
`ExtModel.urlHostStr u = some h`. That a `Str` computed from such values is UTF-8 is proved, not
assumed (`isUtf8_dropTrailingDots`, `isUtf8_map_asciiLowercase` in
`Proofs.External.MetadataResolver`; `to_ascii_lowercase_spec_of_isUtf8` takes the premise).
Approved exception (spec owner, 2026-11-27): G04 `decode_header_value` assumes the conditional form
`Defs.McpHeaders.sentinelInner? value.val = none → ExtModel.IsUtf8 value.val`, weaker than the plain
premise and shown exact by `Theorems.mcp_headers.decode_header_value_fail_undef`.

**Differential tests of patch 05.** `formal/trusted/evidence/differential/metadata-resolver/` (git history at 9047c72)
(`README.md` there; `run.sh <scratch>` applies the patches with `scripts/apply-patches.sh` into
the scratch directory, appends the original code of `7caec76` as a module `old` and the
reviewers' seven tests, and runs them): the patched `normalize_host`, `is_loopback_metadata_host`
and `prim` string wrappers on 1,953 hosts; the resolver state after `with_lookup`,
`with_proxy_hosts`, `allowing_private_addresses`, `allows_url`, and `resolve` on 327,504 cases
(48 base URLs, 463 proxy lists, 212 lookup answers including an empty answer for an unfiltered
host, which both give as `Ok([])`, and a lookup error, which both propagate); `new` and
`prim::proxy_env_values` with a non-Unicode variable (dropped by both); and the four tests of
reviewer a (18 hosts, 29 proxies, 18 base URLs, every subset of 13 addresses for 4 base URLs,
private addresses allowed or not, unfiltered and filtered host). Result (re-run 2026-11-25): 7
passed, 0 differences. Round-3 fixes (2026-11-26): `run.sh` checks `old_body.rs` and
`old_wrappers.rs` against `7caec76` (failing on drift) and refuses, before creating anything, a
scratch directory inside the repository, a symlink, `/`, `$HOME` or an ancestor of either, and an
existing non-empty directory; `diff_new_reads_env` sets the proxy variables only in a child
process (setting them in the test process made two upstream `metadata_resolver` tests fail when
run alongside, because `reqwest` clients read them). Re-run: 7 passed (1 ignored, the child
helper); `run.sh --full`, the whole patched library suite and the differential modules in one
process: 854 passed, 0 failed.

Tests (all in `crates/rmcp/src/transport/auth/metadata_resolver.rs`, `mod tests`, unchanged by
patch 05; they pass on the patched copy, 847 library tests in the translated feature
configuration plus `macros`, `cargo test --locked -p rmcp --lib --features
request-state,server,client,client-side-sse,transport-streamable-http-server,transport-streamable-http-client,auth,macros`
in a copy of `.llbc/work/` after `scripts/apply-patches.sh`, 2026-11-25; all 16
`metadata_resolver` tests pass):

| Models | Exercised by |
|---|---|
| `IpAddr::V4` / `call_once`, `Option::map_or` (`AddressClass::of` on IPv4-mapped addresses) | `classifies_addresses` |
| `Url::parse`, `Url::host`, `prim::trim_end_dots`, `str::to_ascii_lowercase`, `String == &str`, `prim::ends_with` (`with_base_url`, `literal_ip`, `is_loopback_metadata_host`) | `loopback_resource_allows_loopback_but_not_private`, `loopback_resource_reaches_loopback_authorization_server_by_hostname`, `ip_literal_urls_follow_the_policy` |
| `<IpAddr as PartialEq>::eq` (through `Option` equality in `allows_url`) | `ip_literal_urls_follow_the_policy`, `public_resource_cannot_post_to_internal_ip_literal`, `public_resource_cannot_be_redirected_to_internal_ip_literal` |
| `Arc<[T]>::from(Vec)` (`with_base_url`, `with_proxy_hosts`, `allowing_private_addresses`) | every test that builds a resolver (all but `classifies_addresses`); `allowing_private_addresses_keeps_the_rest_of_the_policy` |
| `prim::contains`, `Url::host_str` (`proxy_host`, with and without a scheme) | `proxy_hosts_are_not_filtered`, `public_resource_cannot_reach_internal_service_by_{literal_address,hostname}` |
| `SocketAddr::ip` (`allowed_addresses`) | `public_resource_rejects_hosts_resolving_to_internal_addresses`, `mixed_answers_keep_only_allowed_addresses`, `every_resolution_is_filtered`, `base_host_*` (2 tests), `private_resource_allows_private_but_not_link_local_or_loopback` |

Not exercised by a `metadata_resolver` test: `prim::system_lookup` and `prim::proxy_env_values`
(N03 `new`), which the tests replace by `with_lookup` and `with_proxy_hosts`; they run in the 24
library-test calls of `AuthorizationManager::new`/`new_allowing_private_addresses`
(`crates/rmcp/src/transport/auth.rs`), whose results do not depend on the environment read.
`url::Url::parse`, `host` and `host_str` are opaque, so no test checks a model value; the tests
above exercise the Rust functions on the paths the targets take.

**Linkage of the address-policy targets** (plan Section 19). N01 `AddressClass::of` and N08
`MetadataAddressResolver::is_allowed` are ORIGINAL; the others and the helpers `with_base_url`,
`allowed_addresses`, `proxy_host`, `is_loopback_metadata_host` are `PATCH05_TARGETS`. For the
linkage run `scripts/check-original-linkage.sh` drops the nine patch-05 start points and the
opaque entries `…::metadata_resolver::Lookup` and `…::metadata_resolver::prim` from the copy's
Charon settings. Runs (2026-11-25, Aeneas `nightly-2026.11.24-fb44cb4`, Charon `0.1.324`, Rust
`nightly-2026-09-17`), in a scratch clone of the repository at `8b21c5e` with the working tree
of this change and the regenerated translation committed on top (scratch commit
`6f63761c96c78e717eff1482665f45e1efb688aa`; the scratch commit also bumps the `PINNED_DEPS` entry
`sha2 0.11.1` to `0.11.2`, because `sha2 0.11.2` was published on 2026-11-25 and a fresh
resolution picks it; `sha2` is opaque, so no generated file depends on it; evidence for the
bump in "`sha2 0.11.2`" below):

- `scripts/check-original-linkage.sh <scratch>/scr` on `6f63761`: **exit 0**. Source is upstream
  `7caec76`; 35 Phase 2 `start_from` entries, `exclude` `['serde']`, 33 opaque entries; 31 `_`
  globs match their expected items; all 40 ORIGINAL targets defined, no `sorry`; blocks identical
  up to `Source:`: `Funs.lean` 65/65, `Types.lean` 42/42, `FunsExternal_Template.lean` 37/37,
  `TypesExternal_Template.lean` 10/10.
- Run with the final text scan (2026-11-26, same toolchain): a scratch clone of `8b21c5e` with
  the working tree committed on top (scratch commit `64cb2fc`), then scratch commit `005e743` on
  it with the text scan's final form and `linkage-scan/` (step 5 was added later, on `2172dd3`,
  `960d6ce`, `c400112` and `5bb9384`, below). The External templates are git-ignored (untracked), so a clone has none
  until it is translated: first `scripts/aeneas-translate.sh` on `64cb2fc`: **exit 0**, `git
  status` clean apart from the `.aeneas` symlink (the committed translation reproduces); then
  `scripts/check-original-linkage.sh <scratch>/r5link2` on `005e743`: **exit 0**. Source is
  upstream `7caec76` (src tree `4efe696a…`, digests pinned), working tree clean; 35 Phase 2
  `start_from` entries, `exclude` `['serde']`, 33 opaque entries, `hide_marker_traits = true`;
  137 translated items, 35 patterns, 31 `_` globs match their expected items, all 40 ORIGINAL
  targets defined, no `sorry`; blocks identical up to `Source:`: `Funs.lean` 65/65, `Types.lean`
  42/42, `FunsExternal_Template.lean` 37/37, `TypesExternal_Template.lean` 10/10; "OK: the
  Phase 2 translation does not depend on any translation patch" (nothing refused as "cannot be
  scanned"). This run predates step 5 (below).
- Elaborated comparison, step 5 of `scripts/check-original-linkage.sh`, which decides `ORIGINAL`
  since 2026-11-26 (plan Section 19, amendment 2026-11-26 "elaborated comparison"; human
  decisions 2026-11-26 after the round-5 review a5: "compare elaborated Lean" and "refuse
  committed-only instances"). The unmodified-source translation (env0) and the committed one
  (env1) are built as Lean environments the same way (`scripts/linkage/make_env.py`, reusing
  `formal/.lake/packages` through Lake's `packagesDir`), each with its own generated External
  templates as externals (`scripts/linkage/repair_template.py` repairs the one known template
  printing bug, a fn item as `FnOnce` printed `A → R → A → R`, with the same rewrite on both
  sides; it keeps distinct types distinct, a wrong rewrite stops the build, and it reports
  "template repair: N of M candidate(s) rewritten"; `make_env.py` fails unless
  `formal/.lake/packages` has `Aeneas.olean` and `Mathlib.olean` built, so Lake never builds
  inside the repository). `scripts/linkage/Dump.lean` and `compare_env.py` require every
  non-auxiliary constant of `Rmcp.Types`/`Rmcp.Funs` of env0 in env1 with the same module, kind,
  universe parameters, canonical type and canonical body (binder names, hygiene and metadata
  dropped; auxiliary `_proof_N`/`_sizeOf_N`, matchers `match_N` and theorems replaced by their
  content, a theorem by its statement), every external of env0 with the same universe parameters
  and type in env1, and (extended after the round-6 review a6) what `Rmcp.Types`/`Rmcp.Funs`
  export besides constants to differ only as new declarations make it differ: instance entries
  (name, priority, scoped/global, class, head of the first argument) of env0 unchanged, a new
  entry only if default priority, global, in `Rmcp.Types`, and class `SizeOf` named
  `<T>._sizeOf_inst` or class `Aeneas.Std.Discriminant` named `instDiscriminant…`, with T a
  committed-only inductive; reducibility entries of env0's non-auxiliary constants unchanged, new
  ones only for new constants of the same module; the module-entry count of every persistent
  environment extension unchanged except the extensions measured on the real translations to
  grow with new declarations (`GROW_OK` in `compare_env.py`: compiler data, declaration ranges,
  docstrings, namespaces, structure/projection/recursor data, simp/grind/inline/implemented_by/
  elab_as_elim sets, Aeneas trait/loop tables, and instance and reducibility, whose content is
  checked), per module since round 7 (e.g. the instance extension only in `Rmcp.Types`);
  notation, macros, syntax, `export`, unification hints and unknown extensions may not grow; a
  dump with no export section is refused; and (round 7) every constant that only env1's translation modules declare, auxiliary ones included, must be under `rmcp.` (after Lean's private prefix `_private.Rmcp.{Types,Funs}.0.`) or be a generated root `instDiscriminant…` instance that passed the instance rule. Step 5 first runs `scripts/lean-guard.sh sources` and stops if it fails: it runs Lean on committed code, so its result means something only for code that cannot act at build time; the CI stale-translation check (the committed translation is exactly Aeneas output) is its other gate. Committed-only code of any form changes an
  unmodified block only by changing what it elaborates to, and importing code only through what
  the modules export or the names they add, so the type-directed forms (`linkage-scan/limits/l1`,
  `l2`) and the a5, a6 and a7 forms are covered here. Stated limits: (1) the hand-written `formal/trusted/Rmcp/*.lean`
  (the trusted base): both environments use the templates, because the trusted models use
  `Type` where the templates use `Type _`; (2) entries of the growing extensions that committed
  code attaches to existing constants (`attribute [simp]`, `[inline]`, `[implemented_by]`,
  `[elab_as_elim]` …), which change proof automation, compilation or elaboration hints, not what
  any constant is. Lean itself refuses a global reducibility change of a constant from another
  module (so that case was dropped). Limit (2) is narrowed in practice by `scripts/lean-guard.sh sources`: `implemented_by` is a banned word in every Lean file; `simp`, `inline`, `grind` and `elab_as_elim` are in `ATTR_ALLOWED` and remain within the limit. It also covers the reducibility hints of auxiliary constants, which step 5 ignores (the kernel ignores reducibility). Round-5 findings: a5-1 (code
  after a head line: indented or same-line `def`, `local notation`, `open`), a5-2 (`_root_`
  names, instances with unread names), a5-3 (instance resolution) covered by step 5, committed-only
  instances refused; a5-4 (`s! "…"` with a space) fixed in the pre-check; a5-5 (expected outcome
  per text case of `linkage-scan/run.sh`) deferred; a5-6 (records overclaim and one list incomplete: the records said the text scan reads "exactly one declaration whose head it reads" and refuses "a declaration other than an instance whose name is not read", which the code did not deliver, see a5-1 and a5-2; and formal/README.md and STATUS.md listed the header commands without `noncomputable section` and `public import`, which the code and the plan accept and the real `Funs.lean` uses) fixed in the records: the claims are now those of a pre-check, step 5 decides, and the lists are complete. Round-6 findings (review a6, one reviewer, 2026-11-26), fixed by
  the lead under the same human decisions: a6-1 (blocking: the generated-instance allowlist
  matched names only; a hand-written instance named `EvilP._sizeOf_inst` or
  `instDiscriminantEvil` passed steps 4 and 5 end to end) fixed by the per-entry instance check;
  a6-2 (blocking: scoped instances, `attribute [instance]` on imported constants, priority
  changes, `macro_rules` and other exported non-constant state invisible to step 5) fixed by the
  export comparison; a6-3 (`repair_template.py` rationale) corrected and its message counts
  rewrites; a6-4 (Lake could build inside the repository) fixed by the fail-fast check of
  `make_env.py`; a6-5 (`linkage-elab/run.sh` outcomes) classified by kind, `differs`,
  `instance`, `exports`, `reducibility` joined by `+`, `END` anchor added; a6-6 (the restored
  package cache, shared key with `lean-build.yml`, is code the job runs; both environments use
  it, so it cannot create a difference, but a poisoned cache could make the comparison
  meaningless) stated as a residual risk in `aeneas-translation.yml`, with the cache-free `check`
  job of `lean-build.yml` as the clean build. Round-7 findings (review a7, one reviewer, 2026-11-26; human decision 2026-11-26: "enforce in script, then sign off (no further review round)"), fixed by the lead: a7-1 (judgment, blocking: step 5 runs Lean on committed code, so code acting at build time, an `initialize` forging the dump or a `run_cmd` spoofing an instance entry, could beat it; such code was already stopped by `scripts/lean-guard.sh sources` and the CI stale-translation check, but this was not stated) fixed: step 5 first runs `scripts/lean-guard.sh sources` and stops if it fails, and its comment names the two gates it relies on, lean-guard sources (`initialize`, `run_cmd`, `#eval`, `IO`, `macro_rules` and `implemented_by` banned, attributes outside `ATTR_ALLOWED` refused in generated modules beyond the pinned lines) and the CI stale-translation check (the committed translation is exactly Aeneas output); the reviewer's build-time attacks x1 (`initialize`) and x3 (`run_cmd`) are refused by that gate and are not suite cases, because `linkage-elab/run.sh` bypasses lean-guard; a7-2 (a committed-only constant outside `rmcp.`, such as `_root_.Theorems.…`, could capture names in downstream specs) fixed: the dump also lists auxiliary constants, and every constant that only env1's translation modules declare, auxiliary ones included, must be under `rmcp.` (after Lean's private prefix `_private.Rmcp.{Types,Funs}.0.`) or be a generated root `instDiscriminant…` instance that passed the instance rule; a7-3 (`GROW_OK` was one list for both modules) fixed: it is per module, the growth measured for `Rmcp.Types` and for `Rmcp.Funs` (e.g. the instance extension may grow only in `Rmcp.Types`); a7-4 (the script header did not match the step-5 comment) aligned; a7-5 (`linkage-elab/run.sh` classified by loose patterns) fixed: exact `compare_env.py` message prefixes; a7-6 (`make_env.py` checks only that the oleans exist, not that they are current) recorded as a note, not changed; a7-7 (efficiency, about 20 s; the canonical form printed as trees, fine today) recorded. Negative controls:
  `formal/trusted/evidence/linkage-elab/` (git history at 9047c72; 20 cases: e1–e6, e8, e9, a6-x1, a6-x2, a6-x2b,
  a6-x2c, a6-x3, a6-x4, a6-x5, a6-x7, a7-x4-root-name-capture and a7-root-theorem attacks
  refused, e0 and e7 controls pass; table in its README). Runs (2026-11-26, same toolchain): scratch commit `2172dd3`, exit 0, text comparison
  65/65, 42/42, 37/37, 10/10, elaborated 520 constants and 41 externals identical, 40 generated
  instances of committed-only types. Run before round 6: a scratch clone of `8b21c5e` with the working
  tree (scratch commits `64cb2fc`, `005e743`, `2172dd3`, then `960d6ce` with the final
  `scripts/check-original-linkage.sh`, `scripts/linkage/*`, `linkage-elab/` and the CI
  workflow; `formal/.lake` of the clone linked to the repository's built packages, git-ignored):
  `scripts/check-original-linkage.sh <scratch>/r7link` on `960d6ce`: **exit 0**, source upstream
  `7caec76` (src tree `4efe696a…`, digests pinned), working tree clean; text comparison OK
  (`Funs.lean` 65/65, `Types.lean` 42/42, `FunsExternal_Template.lean` 37/37,
  `TypesExternal_Template.lean` 10/10); elaborated: 520 constants and 41 externals of the
  unmodified-source translation compared with the committed translation, all identical; 40
  generated instances of committed-only types; "OK: the Phase 2 translation does not depend on
  any translation patch". Then `linkage-elab/run.sh <scratch>/r7link <scratch>/elab3`: 8 cases,
  8 as expected (e0 pass, e1–e3 differs, e4 differs+instance, e5 instance, e6 differs, e7 pass).
  Run after round 6: scratch commit `c400112` on `960d6ce` with the round-6 fixes:
  `scripts/check-original-linkage.sh` **exit 0**; text comparison OK (65/65, 42/42, 37/37,
  10/10); template repair 1 of 1 candidate rewritten on each side; elaborated: 520 constants and
  41 externals compared, identical; 40 generated instances; "OK: the Phase 2 translation does not
  depend on any translation patch". `linkage-elab/run.sh` against it: 18 cases, all as expected;
  `linkage-scan/run.sh`: 57 cases rejected.
  **Final run** after round 7: scratch commit `5bb9384` on `c400112` with the round-7 fixes:
  `scripts/check-original-linkage.sh` **exit 0** (`scripts/lean-guard.sh sources` passed inside
  it); text comparison OK (65/65, 42/42, 37/37, 10/10); elaborated: 520 constants and 41
  externals identical; 40 generated instances; "OK: the Phase 2 translation does not depend on
  any translation patch". `linkage-elab/run.sh` against it: 20 cases, all as expected;
  `linkage-scan/run.sh`: 57 cases rejected.
- Text pre-check, step 4 (the shadow scan; plan Section 19, amendment 2026-11-25, patch 05; human decisions 2026-11-25, and
  2026-11-26 twice: "fix + one extra review round" after reviews a3-1 and b3-1, "fail closed +
  one fresh reviewer" after reviews a4-1, b4-1 and b4-2; since 2026-11-26 a fail-closed
  pre-check, not the guarantee). The comparison also fails if an
  identifier of an unpatched block could resolve, from the block's namespaces or the root, to a
  name of `EXTRA`: the names declared only in the committed (patched) translation, and for a
  committed-only structure, inductive or class `T` the generated `T.mk`, `T.mk.injEq`,
  `T.mk.inj`, `T.rec`, `T.recOn`, `T.casesOn`, `T.noConfusion`, `T.noConfusionType`, `T.below`,
  `T.brecOn`, `T.ctorIdx`, `T.toCtorIdx`, and per member line the projection `T.f` or the
  constructor `T.C` with `T.C.injEq`/`T.C.inj`. The scan reads the layout Aeneas emits (line by line; it does not read code after a head line, so these are the rules of a pre-check, reviews a5-1, a5-2, a5-6; step 5 decides) and, on
  both sides, stops with "cannot be scanned" (exit 1) on: a block that is neither a header block
  (every code line, comments and docstrings blanked, exactly one header command: `module`,
  `import M`, `public import M`, `@[expose] public section`, `open` of plain names without
  `in`, `renaming` or `hiding`, `set_option o v`, `namespace N`, `end [N]`, `section`,
  `noncomputable section`) nor exactly one declaration whose head it reads, preceded only by
  docstrings or comments (attributes; only the modifiers `noncomputable`, `private`, `partial`,
  `unsafe`; the keyword; the full name, `«…»` segments with spaces included, possibly on the next
  line), so also on two declarations in a block, on `protected`, `scoped`, `nonrec`, `public`,
  `irreducible_def`, `notation`, …, and on a command before a head or after a comment on its
  line (`/-- … -/ def …`, `open X in def …`, `open a.b.c` above `def …`); a committed header
  block that is not a header block of the matching unmodified-source file (`open a.b.c`); a non-instance
  declaration whose name it does not read; a `def`/`theorem`/`abbrev`/`opaque`/`impl_def`
  containing `where` or `let rec` (auxiliary declarations); a structure, class or inductive whose
  head contains `extends` or whose head `where` does not end a line, or whose member line is
  not `  f g : T` or `  C ::`
  (structure, class) or `| C : T` or `| C` (inductive; deeper lines continue a member), so on
  one-line forms and fields with binders; an interpolated string (a `!` directly before a
  string, `s!"…"`, `m!"…"`); a non-ASCII letter or digit Lean does not read as an identifier
  character. One lexer pass drops string literals (also raw `r#"…"#`), char literals, `--` and
  nested `/- … -/` comments; identifiers follow Lean's `isIdFirst`/`isIdRest`/`isLetterLike`/
  `isSubScriptAlnum` (Greek except `λ`, `Π`, `Σ`, Coptic, polytonic Greek, the Letterlike Symbols
  block, mathematical alphanumerics; subscripts after the first character; `«…»` segments) and
  are compared without guillemets. Exempt from the lookup check: the block's own declared name,
  the binding occurrences of the declaration's signature parameters, and an identifier whose
  first segment is such a parameter after its binder group has closed (binder groups at bracket
  depth 0 before the type colon, only when a depth-0 `:=` follows; not in earlier binders, its
  own type or its default value). Identifiers bound by `fun`, `let`, `match` or patterns are
  checked like free ones. Not read by the pre-check, and covered by step 5: names resolved
  through the type of a term (generalized field notation `t.a`, `(e).a`, `e |>.a`, the
  leading-dot `.a`), generated names beyond those listed (e.g. anonymous instance names), the a5
  forms. Negative controls (git history at 9047c72): `formal/trusted/evidence/linkage-scan/`
  (`run.sh <scratch-dir>`; 57 synthetic cases that must be rejected, as shadowing or as "cannot
  be scanned", and `limits/l1`, `limits/l2`, not read by the pre-check and covered by step 5,
  reported as accepted without affecting the exit status). Reviews a2-1 and b2-1 (2026-11-25) found 8 false negatives of a
  first version (cases a1, b1–b7, b7b; b0 a control); reviews a3-1 and b3-1 (2026-11-26) 10 of
  the second (cases c1–c10); reviews a4-1, b4-1 and b4-2 (2026-11-26) 26 of the third (cases
  a4-d1–a4-d4, a4-d6–a4-d8, a4-e1–a4-e9, a4-e16, a4-e17, b4-d01, b4-d02, b4-d04–b4-d07, b4-d17,
  b4-d21; table in the linkage-scan README); the records fix of round 4 (2026-11-26) found 9
  more in the fourth, fail-closed version (header-like blocks with code, committed-only `open`
  blocks, a command above a head, `extends`; cases r4-p1–r4-p5, r4-p11–r4-p13, r4-p21, r4-p31,
  with r4-p4 and r4-p22, already rejected, as regression controls), fixed by lead decision under
  the human decision "fail closed". The committed translation was affected by none of them. Run
  2026-11-26 (final scan): 57/57 rejected (29 as shadowing, 28 as "cannot be scanned"), l1 and
  l2 accepted, exit 0; the parameter exemption is still needed (the parameters
  of `is_allowed` are `base_classes` and `class`; `base_classes` would otherwise match the
  committed-only projection `MetadataAddressResolver.base_classes`).
- Negative test, scratch commit `3d75574a70447240533be13ef30fbf03455b0e12` (on `6f63761`, only
  `transport.auth.metadata_resolver.AddressClass.of`, the ORIGINAL target N01, added to
  `PATCH05_TARGETS`): **exit 1** with `[aeneas-translate] error: patch-04/05 target
  transport.auth.metadata_resolver.AddressClass.of is translated from the unmodified source;
  update PATCH04_TARGETS/PATCH05_TARGETS and check-original-linkage.sh` and `[linkage] error:
  translation of the unmodified source failed`.

**`sha2 0.11.2`** (`PINNED_DEPS` bump from `0.11.1`, 2026-11-25). Source comparison of the two
crates as published on crates.io (`diff -r` of `sha2-0.11.1` and `sha2-0.11.2` in the cargo
registry): `src/block_api.rs`, which holds the bit-length computation the HMAC exception cites
(line 66, `let bit_len = 8 * (buffer.get_pos() as u64 + bs * self.block_len);`), is
byte-identical. The other changes, per the 0.11.2 changelog, are backend selection and
refactoring: the `cfg` precedence of `sha2_backend` over `sha2_256_backend`/`sha2_512_backend`
(`src/sha256.rs`, `src/sha512.rs`; `src/lib.rs` fixes the SHA-512 `riscv-zknh` selection), refactored `soft` and `riscv_zknh` backends, a
faster SHA-512 `x86-avx2` backend, the round constants documented and renamed in
`src/consts.rs` (values unchanged; e.g. `K32` to `SHA256_RK`) and their uses in the `aarch64`, `loongarch64`, `wasm32` and `x86` backends, and
the manifest, README and changelog. Tests with `sha2 0.11.2` resolved (`cargo tree --prefix
depth` of `rmcp` in the translated configuration: `1sha2 v0.11.2`; `sha2 0.10.9` only through
`oauth2`), `cargo test -p rmcp --lib` with the features of the translated configuration plus
`macros` on the patched copy (patches 01–05), 2026-11-25: 847 passed, 0 failed, among them the
six HMAC-SHA256 tests `model::request_state_wire::tests::{rfc4231_hmac_sha256_vectors,
hmac_sha256_verify_rejects_wrong_length_tags, transcripts_match_incremental_hmac,
s16_prim_rfc4231_verify_accepts_only_the_exact_tag}` and
`model::request_state::tests::key_rotation::{rs1_known_answer_is_unchanged,
rs2_known_answer_matches_wire_specification}` (RFC 4231 cases 1–7 and the codec known answers)
and the five SHA-256 tests `model::skill::tests::sha256_digest::matches_the_digest_in_the_spec_example`
and `model::skill::tests::skill_resource_verify::*` (4).

## Auth metadata externals (translation patch 06, targets A04–A10)

Translation patch 06 (`formal/trusted/patches/06-auth-metadata.patch`; human decisions
2026-11-26 and 2026-11-27, AD1–AD8) lets the OAuth metadata URL and issuer checks of
`crates/rmcp/src/transport/auth.rs` translate: A04 `is_http_url`, A05
`is_disallowed_metadata_host`, A06 `is_allowed_metadata_url`, A07
`resolve_resource_metadata_url`, and A08–A10 through the patch-06 helpers
`check_authorization_response_issuer`, `check_authorization_metadata_issuer` and
`check_resource_metadata_resource` (the `validate_*` wrappers, which map the mirror enum
`IssuerError` to `AuthError` or read a field of the opaque `AuthorizationManager`, stay
unverified glue, AD1). It adds the module `auth::prim` (ten functions, opaque in the translation)
and makes the remaining code call only the standard-library and `url` functions below. Every
model is a definition in `formal/trusted/Rmcp/FunsExternal.lean` (section "`auth.rs` OAuth
metadata URL and issuer checks"), with its source cited in its docstring; `TypesExternal.lean`
is unchanged; `axioms.lock` stays empty. Seven new `opaque` constants (human decision AD4), which
add no axiom; their laws are not stated and are taken as hypotheses by the statements that need
them (as for patch 05):

| Opaque constant | Stands for | Why it is not computed |
|---|---|---|
| `ExtModel.urlScheme : Url → Str` | `Url::scheme` (`url-2.5.9/src/lib.rs` lines 902–904) | `url.Url` is abstract |
| `ExtModel.urlPath : Url → Str` | `Url::path` (lines 1390–1397) | as above |
| `ExtModel.urlFragment : Url → Option Str` | `Url::fragment` (lines 1544–1549) | as above |
| `ExtModel.urlPort : Url → Option U16` | the field `port`, `Url::port` (lines 1268–1270) | as above |
| `ExtModel.urlSerialization : Url → String` | the field `serialization` (line 237) | as above; its relation to the other components is not stated |
| `ExtModel.urlJoin : Url → List U8 → Result Url ParseError` | `Url::join` (lines 470–472) | the URL parser is not modelled (as `urlParse`) |
| `ExtModel.issuerUrl : Url → List U8 → String` | `auth::prim::issuer_url` (clone, `set_query(None)`, `set_fragment(None)`, `set_path`, `to_string`) | the `url` setters are not modelled |

Exact models (computable, so they can be evaluated; examples in
`formal/proofs/Proofs/External/Auth.lean`), with their Rust source (`nightly-2026-09-17` `rust-src` unless stated):

| Model | Source |
|---|---|
| `Url::port_or_known_default`: `urlPort`, else `ExtModel.defaultPort (urlScheme)` (`http`/`ws` 80, `https`/`wss` 443, `ftp` 21, else `None`) | `url-2.5.9/src/lib.rs` lines 1300–1302, `src/parser.rs` lines 185–192 |
| `<Url as PartialEq>::eq`: equality of `urlSerialization` | `url-2.5.9/src/lib.rs` lines 2830–2836 |
| `<Url as Clone>::clone`: the same value | `url-2.5.9/src/lib.rs` line 226 (`#[derive(Clone)]`) |
| `Url::scheme`, `path`, `fragment`, `join`: `ok` of the opaque value | `url-2.5.9/src/lib.rs` as in the table above |
| `Option::zip` | `core/src/option.rs` lines 1983–1992 |
| `str::eq_ignore_ascii_case`: equal bytes after `ExtModel.asciiLowercase` | `core/src/str/mod.rs` lines 2859–2861; `core/src/slice/ascii.rs` lines 66–87 (length test, then the path chosen by the `cfg` of lines 71–74), both paths: the chunked `eq_ignore_ascii_case_chunks::<16>`, lines 125–171, taken for at least 16 bytes on `x86_64` with `sse2` (the translated target) and `aarch64` with `neon`, and the simple loop `eq_ignore_ascii_case_simple`, lines 92–109, otherwise; `core/src/num/mod.rs` lines 737–739. The model covers both: each compares every index of the equal-length slices with `u8::eq_ignore_ascii_case` (the chunked path all full chunks, lines 145–152, then the last 16 bytes, lines 162–168) and returns `true` exactly when all pairs match |
| `prim::trim`: `ExtModel.trimWhitespace` (strip the UTF-8 encodings `ExtModel.whitespaceUtf8` of the 25 `White_Space` code points `ExtModel.whitespaceCodePoints` from both ends) | `core/src/str/mod.rs` lines 2186–2188 and 2377–2394, `core/src/str/pattern.rs` lines 265–273, 330–338, 684–721, 775–808, 902–933, 943–948, `core/src/char/methods.rs` lines 1088–1094, `core/src/unicode/unicode_data.rs` lines 148 and 906–929 |
| `prim::starts_with`: byte prefix (`<+:`) | `core/src/str/mod.rs` lines 1420–1422, `core/src/str/pattern.rs` lines 983–985 |
| `prim::strip_suffix`: byte suffix, then `take` | `core/src/str/mod.rs` lines 2486–2491, `core/src/str/pattern.rs` lines 1030–1050 |
| `prim::strip_dir_prefix`: byte prefix `prefix ++ "/"`, then `drop` | `format!` of `prefix` and `/`; `core/src/str/mod.rs` lines 2458–2460 with the pattern `&String`, whose `Pattern` impl, `alloc/src/string.rs` lines 2691–2711, forwards to the `&str` pattern (`strip_prefix_of`, lines 2709–2711); `core/src/str/pattern.rs` lines 1019–1026 and 983–985 |
| `prim::trim_start_slashes`: `dropWhile` of the byte 47 | `core/src/str/mod.rs` lines 2424–2431, `core/src/str/pattern.rs` lines 265–273 and 401–477; `'/'` is the single UTF-8 byte 47 |
| `prim::issuer_url`: `ok` of the opaque `issuerUrl` | `crates/rmcp/src/transport/auth.rs` lines 4567–4577 of the patched copy |
| `prim::debug_empty_resource_metadata`, `debug_unparsable_resource_metadata`, `warn_downgraded_resource_metadata`, `warn_disallowed_resource_metadata`: `ok ()` | `crates/rmcp/src/transport/auth.rs` lines 4579–4602 of the patched copy (`debug!`/`warn!` with `target: "rmcp::transport::auth"`, AD2) |

New trusted helpers (namespace `ExtModel`): `defaultPort`, `whitespaceCodePoints`,
`whitespaceUtf8`, `matchedPrefixLength`, `dropEncodedPrefixes`, `trimWhitespace`, with the
length lemmas `length_dropEncodedPrefixes_le`, `length_trimWhitespace_le`,
`length_trimWhitespace_le_max` and `length_dropWhile_le_max`. Stated exceptions (also in the
docstrings): the four logging functions do not model their side effect (a `tracing` event, which
changes no value of the translated code; a subscriber that panics or blocks is not modelled);
`Url::join` is assumed to return and not to panic (as `Url::parse`): its parser stores every
offset with `to_u32(..)?` (`url-2.5.9/src/parser.rs` lines 1752–1758), so an offset beyond
`u32::MAX` gives `Err(Overflow)`, and the assumption covers its internal panic sites
(`unwrap` at lines 554, 905, 941, 1053, 1405, `assert!` at 1465, 1485, `panic!` at 1525,
`debug_assert!`s at 404, 445, 509, 710, 754, 1620, 1626), with one stated exception (human
decision AD8, 2026-11-27): the `debug_assert!` at `src/parser.rs` line 1304
(`self.serialization.as_bytes()[segment_start - 1] == b'/'`, double-dot arm of `parse_path`),
active in the translated configuration, fails for a `file:` base whose last path segment is a
normalized Windows drive letter (`pop_path`, lines 1403–1415, does not pop it) joined with a
leading `..` or `%2e%2e` (or other percent-encoded double-dot) segment, so `Url::join` panics
where the model returns `ok`. Reproduced 2026-11-27 (scratch program, url 2.5.9, kept outside the
repository): `Url::parse("file://h/x/C:").unwrap().join("..")` and `.join("%2e%2e")` panic at
`parser.rs:1304:21` in a debug build and return `Ok(file://h/x/C:)` in a release build; a
reviewer's fuzzing found 595 such panics, all with a `file:` base, all at line 1304, none for
another scheme. A07 statements assume that the base URL's scheme is `http` or `https` (AD8).
`prim::issuer_url` returns `ok` also where Rust panics, for a discovery URL with neither query
nor fragment whose serialization is longer than `u32::MAX` bytes (stated exception, human
decision AD7; A09 statements take a premise bounding the URL). The setters
store lengths with `to_u32(self.serialization.len()).unwrap()` (`url-2.5.9/src/lib.rs` lines
1589, 1610, 1768, 1804). With `None`, `set_query` and `set_fragment` only truncate (1646 and 1589
are on the `Some` branches; 1610 converts a length cut at the old query or fragment start, a
`u32`); `set_path` converts at 1768 the length `L` without query and fragment and at 1804 the
length with the new path, which is shorter than the old one in every branch (the new path is
`""` or `/` and a substring of the old path without the 33- or 40-byte well-known segment; the
path parser writes serialized bytes back unchanged, only removes dot segments, and adds at most
two bytes), so 1804 never panics after 1768 passed. 1768 panics exactly when `L > u32::MAX`,
possible only without query and fragment, because `Url::parse` and `Url::join` check only the
start offsets of the components, not the total length. The `debug_assert!`s of the setters
(lines 1584, 1600, 1641: `#` and `?` at the stored starts) and the `assert!` of line 1609 hold
for every `Url` the parser and the setters build; `restore_after_path`'s `adjust` is not called.
The AD8 panic is not known to be reachable through the path parser that `set_path` runs: the new
path is `/` followed by a substring of a serialized path, and a scratch fuzz run (2026-11-27, url
2.5.9 debug build) of the `issuer_url` setter sequence on `file:` URLs built from drive letters
and dot segments, about 2.9 million paths, found no panic.
`prim::trim` is defined on every `Str` and equals Rust's char-level trim on valid
UTF-8 (every Rust `&str`): at a char boundary the bytes begin with the encoding of a char exactly
when that char is there (UTF-8 is prefix-free), and they end with it exactly when it is the last
char (an encoding is a lead byte followed by continuation bytes). Each external has a proved spec
theorem `<generated name>_spec` in `Proofs.External.Auth` (no `sorry`; the axiom audit accepts
the build with 0 trusted axioms), plus `whitespaceUtf8_eq` (the byte strings of
`whitespaceUtf8` are `utf8` of the one-char strings of `whitespaceCodePoints`, by kernel
evaluation) and `decide` examples of `trimWhitespace` and `defaultPort`. The root
`formal/proofs/Proofs.lean` needs `public import Proofs.External.Auth`.

**White_Space table check** (2026-11-26, scratch program compiled with the pinned
`rustc 1.100.0-nightly (923c95cdf 2026-09-16)`, kept outside the repository): the set of all
`char`s `c` (U+0000–U+10FFFF) with `c.is_whitespace()` equals the 25 code points of
`ExtModel.whitespaceCodePoints`, in order; `char::encode_utf8` of each gives exactly the bytes of
`ExtModel.whitespaceUtf8`; and `str::trim` of `"{l}{r}a\u{200b}b{r}{l}"` is `"a\u{200b}b"` for
all 625 pairs `l`, `r` of these chars (U+200B, not `White_Space`, kept).

Tests (all in `crates/rmcp/src/transport/auth.rs`, `mod tests`, unchanged by patch 06; the
`d5_*` tests are the boundary tests that `02-phase2-tests.patch` adds for these targets, AD5;
they pass on the patched copy: `cargo test --locked -p rmcp --lib --features
request-state,server,client,client-side-sse,transport-streamable-http-server,transport-streamable-http-client,auth,macros`
in a copy of `.llbc/work/` after `scripts/apply-patches.sh` with patches 01–06, 2026-11-27, repository toolchain 1.96: 860
passed, 0 failed, including the thirteen AD5 tests; the same 860 pass on the patch-01..05 copy and
on the upstream copy with patches 01 and 02 only):

| Models | Exercised by |
|---|---|
| `Url::scheme`, `Url::host_str` (A04 `is_http_url`) | `rejects_non_http_resource_metadata_parameter` (`file:`), `parses_resource_metadata_parameter` |
| `Option::zip`, `str::eq_ignore_ascii_case`, `Url::port_or_known_default` (`is_same_origin`, A07) | `parses_resource_metadata_parameter`, `parses_cross_origin_resource_metadata_parameter`, `parses_loopback_resource_metadata_parameter_for_loopback_resource` (explicit ports 9000 and 8080), `discovery_get_follows_same_origin_redirects` |
| `prim::trim`, `Url::parse`, `Url::join` (A07) | `parses_relative_resource_metadata_parameter`, `keeps_same_origin_resource_metadata_parameter_for_private_resource` (relative values joined to the base) |
| `prim::warn_downgraded_resource_metadata` (A07) | `rejects_http_resource_metadata_parameter_for_https_resource`, `resource_metadata_parameter_rejects_https_downgrade` (5 cases) |
| `prim::warn_disallowed_resource_metadata`; A05/A06 hosts, `metadata_resolver::prim::{ends_with, trim_end_dots}` | `rejects_disallowed_host_resource_metadata_parameter` (4 cases, among them `localhost`), `cross_origin_private_resource_metadata_parameter_follows_policy`, `metadata_url_checks_bracketed_ipv6_literals`, `metadata_url_allows_private_literals_only_when_opted_in`, `metadata_url_allows_http_authorization_server_for_https_resource` |
| A08: `IssuerError` and its mapping, `str::to_owned` | `validate_authorization_response_issuer_accepts_valid_cases`, `validate_authorization_response_issuer_rejects_invalid_cases`, `invalid_issuer_does_not_consume_authorization_state` |
| A09: `prim::strip_dir_prefix`, `prim::strip_suffix`, `prim::trim_start_slashes`, `prim::issuer_url`, `trim_root_slash`/`is_root_url` | `authorization_metadata_accepts_oidc_path_inserted_issuer`, `authorization_metadata_accepts_oidc_path_appended_issuer`, `authorization_metadata_rejects_mismatched_issuer`, `authorization_metadata_allows_missing_issuer_when_configured`, `authorization_metadata_rejects_missing_issuer_by_default`, `authorization_metadata_allows_only_root_trailing_slash_equivalence`, `protected_resource_metadata_preserves_non_root_issuer_trailing_slash`, `protected_resource_metadata_supports_authorization_server_path_insertion` |
| A10: `Url::fragment`, `<Url as PartialEq>::eq`, `<Url as Clone>::clone`, `prim::starts_with`, `metadata_resolver::prim::ends_with` | `protected_resource_discovery_rejects_{mismatched_resource, missing_resource, resource_that_is_not_a_url, resource_with_fragment}`, `resource_identifier_matching_allows_matching_host_or_parent_path` |

Boundary tests of patch 02 (AD5; a mutation of the code, such as a renamed host or an
ASCII-only trim, makes them fail): `d5_a05_metadata_host_names` (the cloud-metadata host names
and the `.localhost` suffix of hunks H1/H2), `d5_a07_resolve_trim_empty_unparsable`
(`prim::trim` on a value with surrounding whitespace, also checked above against `str::trim`;
`prim::debug_empty_resource_metadata` and `prim::debug_unparsable_resource_metadata`),
`d5_a07_same_origin` (hosts that differ only in ASCII case, and the port cases of
`is_same_origin`), `d5_a09_issuer_root_slash` (`trim_root_slash`, `is_root_url`),
`d5_a08_response_issuer_paths` and `d5_a09_metadata_issuer_paths` (every `IssuerError` and
`AuthError` path of A08 and A09, including the OIDC path-appended form),
`d5_a09_expected_issuer_forms` (every discovery-URL form of
`expected_issuer_for_authorization_metadata_url`, including repeated leading slashes for
`prim::trim_start_slashes`), `d5_a06_private_ip_targets` (private and loopback IPv4/IPv6 literals
through H4, with and without `allow_private`), `d5_a10_resource_identifier_port` (the port
clause of `is_resource_identifier_valid`, and the exact `ResourceMismatch` payload),
`d5_a06_non_http_target` (an `ftp:` target is refused by A06 with and without `allow_private`,
and an absolute `ftp:` parameter makes A07 return `None`: the `is_http_url` check of the
target), `d5_a06_loopback_base_target` (with a loopback base, a cloud-metadata IP literal or
host name is still refused, while a loopback target is allowed: the order of the metadata-host
check and the loopback exemption), `d5_a07_resolve_parse_before_join` (the parameter
`https:public.example/x`, which `Url::parse` accepts as an absolute URL and `Url::join` would
resolve against the base, gives `https://public.example/x`: H5 tries `Url::parse` first and
joins only on its error) and `d5_a10_resource_identifier_scheme` (an `http:` resource for an
`https:` base with the same host, port and path is refused: the scheme clause of
`is_resource_identifier_valid`). Reviewers' mutation runs (2026-11-27; one run of 60 mutants of
the patch-06 targets plus earlier, smaller runs): after the AD5 extensions every non-equivalent
mutant tried is killed. The surviving mutants are equivalent: m01 (`host_str().is_some()` in
A04: every `http(s)` URL has a host), m18 (`is_http_url` in A07's same-origin branch: equivalent
under the AD8 premise that the base is `http` or `https`), m20 (the downgrade check written
`== "http"`: the same return value; it differs only in which `tracing` event is emitted, a
stated exception), m39 (`set_path("/")` for an empty issuer path: for special schemes the path
is never empty), m40 (`|| path == oidc_prefix`), m51 and m60 (equality fast paths), and the
unreachable `None` arm of H4. The opaque values are not
checked by any test (they are not computed); the tests exercise the Rust functions on the paths
the targets take.

**Clippy.** The property checked is that patch 06 adds no warning. `cargo clippy -p rmcp --lib
--no-default-features --features
request-state,server,client,client-side-sse,transport-streamable-http-server,transport-streamable-http-client,auth`
(the translated feature configuration), with and without `macros`, on the patch-01..05 copy and
on the patch-01..06 copy (2026-11-26, with the AD5 tests in patch 02): the same set of warnings
on both copies (same lint, file and message; only line numbers in `auth.rs` move), none of them
`clippy::nonminimal_bool` (AD3) or `clippy::enum_variant_names` (AD6: `IssuerError`'s variants
copy the names of the `AuthError` variants exactly, so all begin with `Authorization`; without
the allow clippy reports "all variants have the same prefix"). The totals depend on the
toolchain, not on `macros`: 10 with the repository toolchain 1.96 (clippy 0.1.96; nine dead-code
warnings and the patch-05 `redundant_closure`), 29 with the pinned `nightly-2026-09-17` (the
same ten plus 18 `clippy::result_large_err` and one `clippy::question_mark` on the
`else { return None; }` chain of `expected_issuer_for_authorization_metadata_url`, which H7
keeps), each on both copies, with and without `macros`.

**Linkage of the auth metadata targets** (plan Section 19). A04–A10 and their helpers are
`PATCH06_TARGETS` (linkage `patch-06`, AD1; A04 and `is_same_origin` translate unmodified, but
A04's Lean does not build without hunk H3 and `is_same_origin` is reached only from A07). For the
linkage run `scripts/check-original-linkage.sh` drops the seven patch-06 start points and the
opaque entry `rmcp::transport::auth::prim` from the copy's Charon settings. Runs (2026-11-26,
Aeneas `nightly-2026.11.24-fb44cb4`, Charon `0.1.324`, Rust `nightly-2026-09-17`), in a scratch
clone of the repository at `94a3c1b` with this change and the lead-owned Charon settings,
script and pin changes committed on top (scratch commit
`70d7787619defc3e0e88886b277db0b1720f00b7`, without this evidence section): `scripts/apply-patches.sh`
exit 0; `scripts/aeneas-translate.sh` exit 0 (all 100 targets defined, no `sorry`, `Funs.lean`
matches its pin, re-translation byte-identical to the committed output); `lake build --wfail Defs
Proofs Specs Rmcp RmcpExternal` exit 0; `scripts/lean-guard.sh` `build-log`, `sources` and
`axioms` exit 0 (0 trusted axioms, 0 native-code axioms); `scripts/check-original-linkage.sh`
exit 0 (65/42/37/10 blocks identical; 520 constants and 41 externals elaborated identically).

## Header-value externals (translation patch 07, targets G01–G04)

Translation patch 07 (`formal/trusted/patches/07-mcp-headers.patch`; human decisions GD1 and GD2,
2026-11-27) lets the SEP-2243 header-value encoding of
`crates/rmcp/src/transport/common/mcp_headers.rs` translate: G01 `requires_base64`, G02
`is_tchar`, G03 `encode_header_value` and G04 `decode_header_value` (linkage `patch-07` for all
four). It adds the private module `mcp_headers::prim` (eight functions, opaque in the translation,
each the original expression) and makes the remaining code call only the standard-library
functions below. Every model is a definition in `formal/trusted/Rmcp/FunsExternal.lean` (section
"`mcp_headers.rs` header-value encoding"), with its source cited in its docstring;
`TypesExternal.lean` is unchanged; there is no new `opaque` constant, and `axioms.lock` stays
empty. Stated exceptions: none.

Exact models, with their Rust source (`nightly-2026-09-17` `rust-src` unless stated; `Source:`
lines of the `prim` functions refer to the patch-01..07 copy):

| Model | Source |
|---|---|
| `prim::has_control_or_non_ascii` (`mcp_headers.rs` lines 415–419): some byte below `0x20` or above `0x7E` (`ExtModel.isControlOrNonAsciiByte`), on every `Str` (GD2) | `value.chars().any(\|c\| (c as u32) < 0x20 \|\| (c as u32) > 0x7E)`: `core/src/str/mod.rs` lines 1079–1081, `core/src/str/iter.rs` lines 35–43, `core/src/iter/traits/iterator.rs` lines 2897–2910 |
| `prim::starts_with`, `prim::ends_with` (lines 421–427): byte prefix (`<+:`), byte suffix (`<:+`) | `core/src/str/mod.rs` lines 1420–1422 and 1445–1450, `core/src/str/pattern.rs` lines 983–985 and 1030–1035 |
| `prim::strip_prefix`, `prim::strip_suffix` (lines 429–435): byte prefix then `drop`, byte suffix then `take` | `core/src/str/mod.rs` lines 2458–2460 and 2486–2491, `core/src/str/pattern.rs` lines 1019–1026 and 1030–1050 |
| `prim::wrap_sentinel` (lines 437–439): `"=?base64?" ++ t ++ "?="` for the string `t` of the argument, `ExtModel.growString`; `fail undef` off UTF-8 | `format!`, `alloc/src/macros.rs` lines 113–119, `alloc/src/fmt.rs` lines 651–662; the constants, `crates/rmcp/src/transport/common/http_header.rs` lines 13–14 |
| `prim::base64_encode` (lines 441–443): `ExtModel.b64StdPad` of the bytes, one ASCII `Char` per byte, `ExtModel.growString` | `base64-0.23.1`: `src/prelude.rs` line 19, `src/engine/general_purpose/mod.rs` lines 337–343, 436, 487, `src/engine/mod.rs` lines 148–164, `src/encode.rs` lines 101–146, `src/alphabet.rs` lines 251–262 |
| `prim::base64_decode` (lines 445–447): `fail panic` if the buffer estimate `ExtModel.b64StdDecodedLenEstimate` exceeds `isize::MAX` (GD2), otherwise `ExtModel.b64StdPadDecode` of the bytes | `base64-0.23.1`: `src/engine/mod.rs` lines 277–301, `src/engine/general_purpose/decode.rs` lines 15–21, 37–90, 184–217, `src/engine/general_purpose/decode_suffix.rs` lines 13–170, `src/engine/general_purpose/mod.rs` lines 341–342 |
| `char::is_ascii_alphanumeric`: code point in 48–57, 65–90 or 97–122 | `core/src/char/methods.rs` lines 2184–2186 |
| `<[T]>::last`: `getLast?` | `core/src/slice/mod.rs` lines 283–285 |
| `Option<&T>::copied`: the identity (a shared borrow is its value in the translation) | `core/src/option.rs` lines 2135–2145 |

New trusted helpers (namespace `ExtModel`): `isControlOrNonAsciiByte`, `urlToStd`, `stdToUrl`,
`b64StdPad`, `padBody`, `b64StdPadDecode`, `b64StdDecodedLenEstimate`, with the length lemmas
`length_padBody_le` and `b64StdPadDecode_length_le`. Padded standard Base64 renames the alphabet of
the reviewed Base64url models `ExtModel.b64` and `ExtModel.b64Decode`, which are unchanged (GD2):
`STANDARD` and `URL_SAFE` share the 62 symbols of the values 0–61 and differ only in 62
(`+`/`-`) and 63 (`/`/`_`), and the engine code is the same for both. Each external has a proved
spec theorem `<generated name>_spec` in `Proofs.External.Base64Std` (no `sorry`; the
models that can fail also have `_fail` theorems, and `wrap_sentinel_not_utf8` gives the
`fail undef` of `prim::wrap_sentinel` off UTF-8), and the module proves the laws: the round trip
`b64StdPadDecode_b64StdPad` (`b64StdPadDecode (b64StdPad x) = some x`), canonicity
`b64StdPadDecode_eq_some_iff` (the decoder accepts exactly the outputs of `b64StdPad`),
`visible_of_mem_b64StdPad` (every encoded byte is in `0x21`–`0x7E`), `length_b64StdPad`
(`4 ⌈n / 3⌉` bytes, Rust's `encoded_len(n, true)`), and the byte-vs-char lemma
`any_isControlOrNonAsciiByte_utf8`: on the UTF-8 bytes of a string the byte model equals the
char-level test of Rust (GD2), so `has_control_or_non_ascii_spec_utf8` states the Rust behaviour
for every `&str`. The root `formal/proofs/Proofs.lean` needs
`public import Proofs.External.Base64Std`.

**Base64 differential check** (2026-11-27, scratch program with `base64 = "=0.23.1"`, compiled
with the repository toolchain 1.96, kept outside the repository): `BASE64_STANDARD` gives exactly
the values of the `decide` vectors of `Proofs.External.Base64Std` (`""`, `Zg==`, `Zm8=`,
`Zm9vYmFy`, `+/8=` from `[251, 255]`; `decode` of `""` is `Ok([])`, of `+/8=` is `[251, 255]`,
and `Zg`, `Zg=`, `Z===`, `-_8=`, `Zh==`, `Zg==Zg==`, `====` are errors). Canonicity on the Rust
side: for every input of length at most 7 over the bytes `AQgw+/-_=!` (11,111,111 inputs, 1,465
accepted) and of length at most 8 over `Ag/=-!` (2,015,539 inputs, 8,611 accepted), whenever
`decode(s)` is `Ok(y)`, `encode(y)` is `s`; and for 64 inputs of lengths 0–63, `encode` has
`(n + 2) / 3 * 4` bytes, all in `0x21`–`0x7E`, and `decode` returns the input. This is the Rust
side of `b64StdPadDecode_eq_some_iff` and `b64StdPadDecode_b64StdPad`.

**Differential checks by the reviewers** (2026-11-27; a reviewer record: the reviewers' programs
are not in the repository, and these figures were not re-run by the author of this record).
Review round 1 of the translation stage: 586,638 outputs of the translated Lean functions
G01–G04 and of the models above were byte-identical to those of `base64` 0.23.1 and of the Rust
functions on the same inputs; and on 51,580 strings the Rust side satisfies
`decode_header_value(&encode_header_value(v)) == Some(v)`, `HeaderValue::from_str` accepts every
encoding, and no encoding starts or ends with SP or HTAB or has a byte outside `0x20`–`0x7E`.
Review round 3, with fresh seeds 4242027 and 777001: 169,802 and 1,118,076 output lines of the
translated Lean functions were byte-identical to those of the upstream Rust functions with
`base64 = "=0.23.1"`; and the patched Rust functions (patches 01–07) against the upstream ones:
1,188,404 comparisons, 0 differences.

Blob ids of `crates/rmcp/src/transport/common/mcp_headers.rs` (`git hash-object`, abbreviated):
upstream `9882884`; after patches 01–06 `4ee60aa` (patch 02 appends the five GD3 tests; patches
01 and 03–06 do not touch the file); after patches 01–07 `a8f6185` (the `index` line of patch
07).

Tests (all in `crates/rmcp/src/transport/common/mcp_headers.rs`, `mod tests`: the upstream tests
and the five GD3 tests `g07_*` that patch 02 appends; patch 07 changes no test). They pass on
both patched copies. Recorded run (2026-11-27, repository toolchain 1.96): a copy of `.llbc/work/`
after `scripts/apply-patches.sh`; the script deletes `Cargo.lock` in the copy, so the workspace
`Cargo.lock` is copied into it (or `cargo generate-lockfile` is run there) before `cargo test
--locked -p rmcp --lib --no-default-features --features
request-state,server,client,client-side-sse,transport-streamable-http-server,transport-streamable-http-client,auth,macros`:
865 passed, 0 failed with patches 01–07, and 865 passed, 0 failed with patches 01–06 (both
copies carry patch 02 and so the GD3 tests); among them the 64 tests of `mcp_headers`, 5 of them
GD3 tests. The integration test `rejects_decoded_base64_param_mismatch_with_32020` named in the
table (`crates/rmcp/tests/`) is not part of these `--lib` runs.

| Models (and target paths) | Exercised by |
|---|---|
| G01: `<[T]>::first`, `<[T]>::last`, `Option<&u8>::copied` (leading/trailing space or tab) | `encode_header_value::wraps_leading_whitespace`, `wraps_trailing_whitespace`; `decode_header_value::round_trips_with_encode` (`" padded "`); `g07_requires_base64_boundaries` (`""`, `" "`, `"\t"`, `"a b"`, `"a\tb"`); `g07_round_trip_and_header_safe` (`" a"`, `"a "`, `"\t"`) |
| G01: `prim::has_control_or_non_ascii` | `encode_header_value::wraps_non_ascii` (`café`), `wraps_control_characters` (`\n`), `wraps_crlf_injection_attempt` (`\r\n`); `passes_plain_ascii_through`, `passes_internal_spaces_through` (false on printable ASCII); `g07_requires_base64_boundaries` (U+001F, DEL, U+0080, `é` true; `~` false) |
| G01: `prim::starts_with`, `prim::ends_with` | `encode_header_value::wraps_sentinel_collision`; the passing cases above (false); `g07_requires_base64_boundaries` (sentinel exactly, with a payload, overlapping `=?base64?=`; prefix or suffix alone, prefix not at the start, suffix not at the end) |
| G02: `char::is_ascii_alphanumeric`, `char::from(u8)` and the `==` chain | `validate_param_header_annotations::accepts_primitive_types` (`Region`, `Count`, `Flag`), `rejects_non_token_header_name` (`bad:name`); all fifteen punctuation tchars (`-` among them) are pinned by `g07_is_tchar_boundaries` (each punctuation tchar, the alphanumeric bounds, the delimiters and other non-tchars, the count 77 over ASCII); `g07_mutation_vectors` (the count 77 over all chars `U+0000`–`U+10FFFF`) |
| G03: `prim::base64_encode`, `prim::wrap_sentinel`, `str::to_owned` | every `encode_header_value::*` test (`assert_wrapped` checks the prefix; the passing cases compare the value) and `decode_header_value::round_trips_with_encode` (six values, three of them wrapped: `café`, `" padded "`, `"line1\nline2"`; all six decoded back); `g07_round_trip_and_header_safe` (thirteen values, round trip and header safety); `g07_mutation_vectors` (the standard alphabet in encoding: `é?` gives `=?base64?w6k/?=`, `é>` gives `=?base64?w6k+?=`, `\t~~` gives `=?base64?CX5+?=`) |
| G04: `prim::strip_prefix`, `prim::strip_suffix`, `prim::base64_decode`, `String::from_utf8`, `?` | `decode_header_value::round_trips_with_encode`, `decode_header_value::rejects_invalid_base64` (`!!!not-base64!!!` inside the sentinel gives `None`); the `validate_request_headers` tests (`accepts_matching_method_and_name`, `rejects_name_mismatch`, `accepts_matching_param`, `rejects_param_mismatch`, `accepts_matching_nested_param`) decode plain values (no sentinel); the integration test `rejects_decoded_base64_param_mismatch_with_32020` (`crates/rmcp/tests/test_streamable_http_standard_headers.rs`, sentinel `=?base64?ZXUtY2VudHJhbDE=?=`); `g07_decode_header_value_boundaries` (inner `None` arm, non-UTF-8, invalid and non-canonical Base64, untrimmed white space); `g07_round_trip_and_header_safe`; `g07_mutation_vectors` (standard alphabet `Pz8/`, `fn5+` decoded, URL-safe `Pz8_`, `fn5-` give `None`; suffix stripped at the end only, prefix stripped once; trailing NUL of `AA==` kept) |

Paths that no upstream test reaches, and the GD3 test of patch 02 that pins each (expected values
computed from the upstream source, not from the Lean model):

- G01 on the empty string (`false` before any byte is read): `g07_requires_base64_boundaries`
  (`""` is `false`); `g07_round_trip_and_header_safe` (`""` encodes to itself and decodes back).
- G01 on U+001F (the bound of the control test): `g07_requires_base64_boundaries` (`"\u{1f}"`
  and `"a\u{1f}b"` are `true`; also DEL, U+0080 and `é` `true`, `~` (0x7E) `false`).
- G01 sentinel placement: `g07_requires_base64_boundaries` (`=?base64??=`, `=?base64?abc?=` and
  the overlapping `=?base64?=` are `true`; `=?base64?abc`, `=?base64?`, `abc?=`,
  `x=?base64?abc?=`, `=?base64?=x` and `=?base64?a?=b` are `false`: the prefix must start and
  the suffix must end the value).
- G02 for the fifteen punctuation chars (`!#$%&'*+-.^_\`|~`), in particular the quote of
  the GD1 workaround `char::from(b'\'')`: `g07_is_tchar_boundaries` (each of the fifteen
  punctuation tchars, the quote again on its own, the alphanumeric bounds, the delimiters
  `"(),/:;<=>?@[\]{}`, space, tab, NUL, DEL, `é`, U+FF07, and exactly 77 tchars among the 128
  ASCII chars).
- G04 for a value with the prefix but without the suffix (the inner `None` arm of hunk M4):
  `g07_decode_header_value_boundaries` (`=?base64?abc`, `=?base64?`, `=?base64?=` and
  `=?base64?/w==` are returned unchanged, as are values without the prefix: `us-west1`, `""`,
  `abc?=`, ` =?base64?YQ==?=`).
- G04 for a sentinel whose Base64 decodes to bytes that are not UTF-8 (`String::from_utf8`
  error): `g07_decode_header_value_boundaries` (`/w==` = `FF`, `wyg=` = `C3 28` give `None`).
- G04 for invalid or non-canonical Base64: `g07_decode_header_value_boundaries` (`!!!!`, `abc`,
  `YQ=`, `YQ===`, `YQ`, and the non-zero trailing bits `YR==`, `YWJ=` give `None`; the empty
  payload gives `Some("")`, `YQ==` gives `Some("a")`).
- G04 with white space around the payload (not trimmed before decoding):
  `g07_decode_header_value_boundaries` (`=?base64? YQ==?=`, `=?base64?YQ== ?=` give `None`).
- G01 sentinel placement, further look-alikes: `g07_mutation_vectors` (`=?base64?a=`, `=?x?=`,
  `=?base64x?=` are `false`: the suffix is `?=`, not `=`, and the prefix is exactly `=?base64?`).
- G03 and G04 with the two symbols of the standard alphabet that differ from Base64url (`+`,
  `/`): `g07_mutation_vectors` (`é?` encodes to `=?base64?w6k/?=`, `é>` to `=?base64?w6k+?=`,
  `\t~~` to `=?base64?CX5+?=`; `=?base64?Pz8/?=` decodes to `???`, `=?base64?fn5+?=` to `~~~`;
  the URL-safe `=?base64?Pz8_?=` and `=?base64?fn5-?=` give `None`).
- G04 suffix stripped at the end only, prefix stripped once: `g07_mutation_vectors`
  (`=?base64?YQ==?=x` and `=?base64?YQ==?= ` are returned unchanged; `=?base64?YQ==?=?=` and
  `=?base64?=?base64?YQ==?=` give `None`).
- G04 with a trailing NUL byte in the decoded bytes: `g07_mutation_vectors` (`=?base64?AA==?=`
  gives `Some("\0")`).
- G02 over all chars: `g07_mutation_vectors` (exactly 77 of the chars `U+0000`–`U+10FFFF` are
  tchars, so no non-ASCII char is one).
- G03 with G04, round trip and header safety: `g07_round_trip_and_header_safe` (for `""`, `" a"`,
  `"a "`, `"\t"`, `"\r\n"`, `"x\ny"`, `"é"`, four sentinel look-alikes, `"a'b"` and a 1200-byte
  ASCII string: decoding the encoding gives the value back, the encoding has only bytes
  `0x20`–`0x7E`, neither starts nor ends with SP or HTAB, is accepted by
  `http::HeaderValue::from_str`, and differs from the value exactly when `requires_base64`
  holds).

Mutation check (the record of the header of `formal/trusted/patches/02-phase2-tests.patch`;
re-run on 2026-11-27 after the last cases were added, scratch copy with patches 01–07, the same
`cargo test` command filtered to `transport::common::mcp_headers`, 64 tests; each mutant alone;
the failing tests are listed exactly). Kills of patch 07's rewrites: dropping the
`c == char::from(b'\'')` disjunct of `is_tchar` fails `g07_is_tchar_boundaries` and
`g07_mutation_vectors`; changing the inner `None` arm of `decode_header_value` to `None` fails
`g07_decode_header_value_boundaries`, `g07_round_trip_and_header_safe` and
`g07_mutation_vectors` (no upstream test); replacing `prim::strip_suffix` or `prim::strip_prefix`
by `Some(s)` fails those three g07 tests and the upstream `round_trips_with_encode`; `> 0x7F` for
`> 0x7E` in `prim::has_control_or_non_ascii` fails `g07_requires_base64_boundaries` alone; `||`
for `&&` in the sentinel test of `requires_base64` fails `g07_requires_base64_boundaries` and
`g07_mutation_vectors`. Three mutants of the `prim` bodies that a review mutation run found
surviving every `mcp_headers` test are killed by cases added on 2026-11-27 (each fails exactly
one test): `< 0x1F` for `< 0x20` in `prim::has_control_or_non_ascii` and `s.contains(suffix)`
for `s.ends_with(suffix)` in `prim::ends_with` fail `g07_requires_base64_boundaries` (on
`"\u{1f}"` and `"=?base64?=x"`); `BASE64_STANDARD.decode(value.trim())` in
`prim::base64_decode` fails `g07_decode_header_value_boundaries` (on `"=?base64? YQ==?="`). Five
further mutants that a second review mutation run found surviving are killed by
`g07_mutation_vectors` (each fails it alone): `URL_SAFE` imported as `BASE64_STANDARD` in `prim`
(encode and decode; on `é?`), `prim::strip_suffix` as `s.rfind(suffix).map(|i| &s[..i])` or as
`s.find(suffix).map(|i| &s[..i])` (both on `"=?base64?YQ==?=x"`), `ends_with(value, "=")` for the
suffix in `requires_base64` (on `"=?base64?a="`) and `prim::base64_decode` dropping trailing NUL
bytes (on `AA==`). Seven further mutants are killed by the cases of the further round (each
fails `g07_mutation_vectors` alone): in `prim::has_control_or_non_ascii`, `c as u8` for
`c as u32` in the `> 0x7E` test or in both (truncating cast; on `Ł`; changing only the `< 0x20` cast is
equivalent), the `> 0x7E` test limited to the BMP
(`&& (c as u32) <= 0xFFFF`; on U+1F600), `.chars().take(256).any(..)` (on the 257-char value)
and NUL allowed (`(1..0x20)` for `< 0x20`; on `"\0"`); `prim::starts_with` and
`prim::strip_prefix` comparing the prefix ASCII-case-insensitively (on `=?BASE64?x?=` and
`=?BASE64?YQ==?=`); `prim::base64_decode` removing CR and LF before decoding (on
`=?base64?YQ\n==?=`). Ten mutants survive every test and are equivalent: in
`prim::has_control_or_non_ascii`, `c.is_control() || !c.is_ascii()` and
`c.is_ascii_control() || !c.is_ascii()` (the same set: below `0x20`, `0x7F`, above `0x7F`);
`trim_start` before `starts_with` or `trim_end` before `ends_with` in `prim` (`requires_base64`
has returned `true` before on any value whose first or last char is white space: space and tab
are checked, every other white space char is a control or non-ASCII char); dropping the tab
from the first-byte test, from the last-byte test, or from both, in `requires_base64` (a tab is
below `0x20`, so `prim::has_control_or_non_ascii` returns `true` on any value holding one);
dropping the `is_empty` early return of `requires_base64` (the empty value has no first or last
byte, no char, and does not start with the prefix: `false` either way); stripping the suffix
before the prefix in `decode_header_value` (both orders succeed exactly when the value is the
9-byte prefix, then any text, then the 2-byte suffix, the two not overlapping, and give the same
inner part; otherwise both return the value unchanged); and `value.trim().to_owned()` in the
else branch of `encode_header_value` (reached only when `requires_base64` is false, so the value
has no leading or trailing space or tab and no control or non-ASCII char, and `trim`, which
removes Unicode White_Space chars, removes nothing).

**Clippy.** The property checked is that patch 07 adds no warning. `cargo clippy --locked -p rmcp
--lib --no-default-features --features
request-state,server,client,client-side-sse,transport-streamable-http-server,transport-streamable-http-client,auth`
(the translated feature configuration), with and without `macros`, on the patch-01..06 copy and
on the patch-01..07 copy (2026-11-27): the same set of warnings on both copies (same lint, file
and message), none of them in `mcp_headers.rs`. The totals depend on the toolchain, not on
`macros`: 10 with the repository toolchain 1.96 (clippy 0.1.96: nine dead-code warnings and the
patch-05 `redundant_closure`), 29 with the pinned `nightly-2026-09-17` (the same ten plus 18
`clippy::result_large_err` and the patch-06 `clippy::question_mark`), each on both copies, with
and without `macros` (as for patch 06).

**Linkage of the header-value targets** (plan Section 19). G01–G04 are `PATCH07_TARGETS`
(linkage `patch-07`, GD1). For the linkage run `scripts/check-original-linkage.sh` drops the four
patch-07 start points and the opaque entry `rmcp::transport::common::mcp_headers::prim` from the
copy's Charon settings. Runs (2026-11-27, Aeneas `nightly-2026.11.24-fb44cb4`, Charon `0.1.324`,
Rust `nightly-2026-09-17`), in a scratch clone of the repository at `42b7ab9` with this change, the
lead-owned Charon settings, script and pin changes and the root import committed on top
(scratch commit `851c38aea391a15f3332aebaf7ab121f31b9494e`, without this run record):
`scripts/apply-patches.sh` exit 0 (patches 01–07 apply with `-F 0`); `scripts/aeneas-translate.sh`
exit 0 (all 104 targets defined, no `sorry`, `Funs.lean` matches its new pin, re-translation
byte-identical to the committed output); `lake build --wfail Defs Proofs Specs Rmcp RmcpExternal`
exit 0; `scripts/lean-guard.sh` `sources`, `build-log` and `axioms` exit 0 (0 trusted axioms, 0
native-code axioms); `scripts/check-original-linkage.sh` exit 0 (65/42/37/10 blocks identical;
520 constants and 41 externals elaborated identically, as before patch 07).

## Elicitation schema externals (translation patch 08, targets X01–X75)

Translation patch 08 (`formal/trusted/patches/08-elicitation-schema.patch`; human decision XD1,
2026-11-28) lets the elicitation schema builders of `crates/rmcp/src/model/elicitation_schema.rs`
translate. 65 of the 75 targets translate from the unmodified source (linkage `ORIGINAL`,
certified by `scripts/check-original-linkage.sh` with the XD2 extension below); ten need the
patch (linkage `patch-08`): X29 `enum_titles`, X32/X35 `with_default`, X33/X38 `build`, X36
`min_items`, X37 `max_items`, X40 `ElicitationSchema::new`, X74 `ElicitationSchemaBuilder::build`
and X75 `build_unchecked` (in no hunk, but it calls X74). The patch adds the private module
`elicitation_schema::prim` (two functions, opaque in the translation, each the original
expression) and the private translated helper `const_titles`, and makes the remaining code call
only the standard-library functions below. Every model is a definition in
`formal/trusted/Rmcp/FunsExternal.lean` (section "Elicitation schema builders"), with its source
cited in its docstring; `TypesExternal.lean` adds the structure `BTreeMap` and the root types
`F64`, `F32` (human decision XD3, below). No new axiom; `axioms.lock` stays empty. New `opaque`
constants: `ExtModel.F64Carrier : NonemptyType` and `ExtModel.F32Carrier : NonemptyType` (XD3;
non-empty since review finding TR6, as `ExtModel.LookupCarrier`, with the instances
`instNonemptyF64` and `instNonemptyF32`), none for the functions.

Models, with their Rust source (`nightly-2026-09-17` `rust-src`; `Source:` lines of the `prim`
functions refer to the patch-01..08 copy):

| Model | Source |
|---|---|
| type `BTreeMap<K, V, A>`: the entries in iteration order, ascending by `K`'s `Ord`, keys pairwise distinct (as `serde_json::Map`); node structure and allocator not modelled | `alloc/src/collections/btree/map.rs` lines 189–203 |
| `BTreeMap::default`: no entries | `alloc/src/collections/btree/map.rs` lines 2606–2611 (`BTreeMap::new`) |
| `BTreeMap::insert`: `ExtModel.btreeInsert`, a walk over the sorted entries comparing `k.cmp(key)` (`Greater` go on, `Equal` replace the value and keep the stored key, return the old value, `Less` insert before, end: append); failures of `cmp` propagate | `alloc/src/collections/btree/map.rs` lines 1047–1058 (`entry`, `Occupied`/`Vacant`), `alloc/src/collections/btree/search.rs` lines 225–242 (`find_key_index`: `key.cmp(k)`) |
| `<String as Ord>::cmp`: `ExtModel.bytesCmp` of the UTF-8 bytes (built on the reviewed `ExtModel.bytesLt`) | `alloc/src/string.rs` line 350 (`#[derive(Ord)]` on `String { vec: Vec<u8> }`), `core/src/slice/cmp.rs` (`Ord for [u8]`) |
| `<String as PartialOrd>::partial_cmp`: `some` of the `Ord` result | `alloc/src/string.rs` line 350 (`#[derive(PartialOrd)]`); `PartialOrd for [u8]` is `Some(Ord::cmp)` |
| `Vec::default`: the empty vector | `alloc/src/vec/mod.rs` lines 4417–4419 |
| `<str as Debug>::fmt`: `Ok(())`, formatter unchanged (total, not exact; stated exception, as `<ParseIntError as Debug>::fmt`) | `core/src/fmt/mod.rs` lines 2916 ff.; `core::fmt::Formatter` is opaque in the Aeneas library |
| `<slice::Iter<'_, T> as Iterator>::all`: `ExtModel.sliceIterAll` (the reviewed model of `<Bytes as Iterator>::all`), on the remaining elements | `core/src/slice/iter/macros.rs` lines 304–313, instantiated by `iterator!` in `core/src/slice/iter.rs` lines 140–148 |
| `prim::titles_mismatch_message` (lines 1814–1819): the literal text with both counts in decimal (`toString` of the `Nat` values) | `format!`, `alloc/src/macros.rs` lines 113–119, `alloc/src/fmt.rs` lines 651–662; `Display for usize`, `core/src/fmt/num.rs` |
| `prim::sorted_keys` (lines 1821–1825): `ExtModel.collectVec 24` of the keys of the entries, in order | `BTreeMap::keys` and `Keys` (`alloc/src/collections/btree/map.rs` lines 2767–2769 and 2005–2050, `TrustedLen` at 2050), `Cloned` (`core/src/iter/adapters/cloned.rs` line 138), `Vec::from_iter` of a `TrustedLen` iterator (exact capacity; `24 * len > isize::MAX` is the capacity-overflow panic) |

Stated exceptions (listed in `formal/README.md`, "Stated exceptions of the external
models"): `BTreeMap::insert` assumes the entries are sorted with distinct keys and that `Ord::cmp`
is a total, consistent, non-failing order (true of `Ord for String`, the only instance used;
`Proofs.External.ElicitationSchema` proves that every map built from `BTreeMap::default` by
`BTreeMap::insert` with it stays sorted); the B-tree compares `k` with fewer keys, which gives the
same result under these assumptions. `<str as Debug>::fmt` is total, not exact: its only caller is
the `expect` of X75, whose `Err` path is `fail panic` whatever the formatter holds, so the panic
message is not modelled. Allocation failure is not modelled (module convention). Two
consequences of patch 08 that the models make visible or hide (review findings TR2, TR3):
`prim::sorted_keys` runs before the validation of X74 (hunk E7), so the translated X74 returns its
validation `Err` only when `24 * properties.entries.length ≤ isize::MAX` (else the
`ExtModel.collectVec` capacity panic); a spec of that `Err` path states this premise (unreachable
for a map that exists). `const_titles` (hunk E8) builds the `one_of`/`any_of` vectors by `push`,
so their capacity differs from upstream's exact `TrustedLen` collect (for one titled value: 4
patched, 1 upstream); the elements and their order are the same, the capacity is visible only
through `Vec::capacity` and memory use, and is not modelled (a Lean `Vec` is its elements).

New trusted helpers (namespace `ExtModel`): `btreeInsert` and `bytesCmp`. Laws and specs, proved
in `formal/proofs/Proofs/External/ElicitationSchema.lean` (no `sorry`; the root
`formal/proofs/Proofs.lean` imports it): `bytesCmp_eq_lt_iff`, `bytesCmp_eq_eq_iff`,
`bytesCmp_eq_gt_iff`, `Ordering.swap_bytesCmp` (a total order agreeing with `bytesLt` and
equality), `bytesCmp_utf8_eq_eq_iff`; `btreeInsert_stringOrd_eq_ok`: with the generated `Ord`
instance of `String`, `btreeInsert` is the reviewed `serde_json::Map` insertion
`ExtModel.mapInsert`, so `sortedByKey_mapInsert` and `mapInsert_fst_of_sortedByKey`
(`Proofs.External.Skill`) give the sorted invariant and the returned old value; a `_spec`
theorem for each of the nine models (`BTreeMap.insert_string_spec` for `String` keys), and
`prim.sorted_keys_eq_fail`.

**`F64` and `F32` (human decision XD3).** The pinned Aeneas library defines no type for `f32` and
`f64`, but Aeneas prints them as `F32` and `F64`: the committed `Rmcp.Types` already had
`model.annotated.Annotations.priority : Option F32`, and patch 08's targets bring
`model.elicitation_schema.NumberSchema` with `minimum`, `maximum`, `default : Option F64`. With
Lean's default `autoImplicit`, an undefined `F32` in a structure field is bound as an implicit
argument of the field: the committed `Annotations.priority` elaborated to `{F32 : Type} → Option
F32` (only `none` inhabits it) and lifted `Annotations` to `Type 1` (measured on a minimal file with
the pinned Lean, 2026-11-28). XD3 declares the root types `F64 := ExtModel.F64Carrier.type` and `F32
:= ExtModel.F32Carrier.type` in `TypesExternal.lean` over two `opaque` carriers of type
`NonemptyType` (no axiom; with the instances `Nonempty F64` and `Nonempty F32` from the carriers'
property, as for `Lookup`; review finding TR6) and turns `autoImplicit` off for the library `Rmcp`
(`formal/lakefile.toml`; `scripts/lean_guard.py` allows exactly this extra option for `Rmcp` and,
since XD9, `RmcpExternal`), so any undefined name in the translation is now a build error. Decision
XD9 (2026-11-28) sets the same option for `RmcpExternal`, so an undefined name in a trusted model is
a build error too. So that this does not depend on Aeneas never emitting the option (review finding
TR7), `scripts/lean-guard.sh sources` also refuses the option names `autoImplicit` and
`relaxedAutoImplicit` anywhere in `formal/translation/` (any value, the `… in` form, `«…»` quoting,
templates included), `set_option` of either with a value other than `false` in the hand-written
files (five proof files set it to `false`; `Defs`, `Proofs` and `Specs` otherwise keep Lean's
default, so this rule only refuses writing `true` explicitly), and a comment between `set_option`
and its value in any file.

Guard rules for `set_option` (review findings TR11, TR12; `scripts/lean_guard.py`, `RULE_LINTER`,
`RULE_AUTOIMPLICIT_ON`, `RULE_SETOPT_COMMENT`). What Lean v4.36.0 (the pinned toolchain) accepts,
tried on scratch files with `lean` 2026-11-28: the option name may follow `set_option` without
whitespace when quoted (`set_option«autoImplicit» true in` takes effect) and the value may follow a
closing `»` directly (`set_option«autoImplicit»false`); each name component may be quoted
(`«linter».unusedVariables`, `linter.«unusedVariables»`, `«linter».«unusedVariables»` switch the
linter off; `«linter.unusedVariables»` is an unknown option); a comment may stand between the name
and the value (`set_option linter.unusedVariables /- c -/ false in` switches the linter off,
`set_option autoImplicit /- c -/ true in` switches it on); the value is the token `true` or `false`
(`«false»` and `true.x` are syntax errors, `"true"` and `0` type errors for a `Bool` option);
`«auto»Implicit` and `_root_.autoImplicit` are not the option. The rules: in hand-written files,
`set_option` with a name whose first component is `linter` or `«linter»` (later components plain or
quoted) and the value `false` is refused (the one `dupNamespace` line of `FunsExternal.lean`
excepted); `set_option autoImplicit`/`relaxedAutoImplicit` (plain or `«…»`-quoted, with or without
whitespace after `set_option`) is refused unless the next token after whitespace (line breaks
included) is `false`; in every file, a comment (`--`, `/-`) between `set_option` and its value,
before or after the option name, is refused. Before this round, `set_option«autoImplicit» true`,
`set_option «linter».unusedVariables false` and a comment between the name and the value passed, and
`set_option «relaxedAutoImplicit» false` was wrongly refused. The elicitation stage added 34
`lean_guard.py selftest` cases (13 before, 47 now; 5 of them for the generated-code rule) (47
sources cases and 12 leanOptions cases in all, all passing on 2026-11-28). Control: the same
selftest with the round-2 patterns of the three rules swapped back in fails exactly ten of the new
cases (the comment between name and value in a generated and in a hand-written file, the linter
options with a quoted first component or all components quoted, the two comment-before-`false`
linter cases, `set_option«autoImplicit» true`, `set_option«relaxedAutoImplicit» true in`, and the
two quoted-name-with-`false` cases refused).

Justification: no translated target
and no external model creates, reads or compares a float; the targets only move the `Option`
fields of `NumberSchema` and `Annotations` values they are given (the `f64` builders of
`NumberSchema` are not targets), so an abstract carrier is exact for them. No statement may
inspect a value of these types (none can: no operation on them is declared). Checked (scratch
`#check`, 2026-11-28): `model.annotated.Annotations.mk : Option (Vec model.Role) → Option F32 →
Option String → model.annotated.Annotations`, `NumberSchema.mk : … → Option F64 → Option F64 →
Option F64 → NumberSchema`, `Annotations`, `NumberSchema`, `PrimitiveSchemaDefinition` and
`ElicitationSchema` in `Type`, `F64`/`F32` the root definitions; `lake build --wfail Defs Proofs
Specs Rmcp RmcpExternal` passes with nothing else changed (no existing proof mentions
`Annotations`). The upstream defect is recorded in
`formal/trusted/issues/aeneas-elicitation-schema.md` (draft issue, not filed).

Blob ids of `crates/rmcp/src/model/elicitation_schema.rs` (`git hash-object`, abbreviated):
upstream `929b446`; after patches 01–07 `ca78a8d` (patch 02 appends the seven XD tests; no
other patch touches the file); after patches 01–08 `3c55487` (the `index` line of patch 08).

Tests. The upstream tests of `elicitation_schema.rs` (`mod tests`) and
`crates/rmcp/tests/test_elicitation.rs`, and seven XD tests `x08_*` that patch 02 appends at the
end of `mod tests` (human decision XD1; expected values computed from the upstream source, not
from the Lean model): `x08_enum_titles_count_mismatch_message`,
`x08_titled_options_pair_titles_with_values_in_order`, `x08_multi_select_default_membership`,
`x08_property_order_is_the_byte_order_of_the_names`,
`x08_build_required_names_must_be_property_names`, `x08_build_unchecked_panics_with_the_error`,
`x08_build_unchecked_returns_the_built_schema`. Recorded run (2026-11-28, repository toolchain
1.96, the workspace `Cargo.lock` copied into each copy): `cargo test --locked -p rmcp --lib
--no-default-features --features
request-state,server,client,client-side-sse,transport-streamable-http-server,transport-streamable-http-client,auth,macros`:
872 passed, 0 failed with patches 01–07 and 872 passed, 0 failed with patches 01–08 (865 before
plus the seven XD tests); `cargo test --locked -p rmcp --test test_elicitation --features
elicitation,client,server`: 56 passed, 0 failed on both copies.

| Models (and target paths) | Exercised by |
|---|---|
| `BTreeMap::default`, `Vec::default` (the derived `Default` of `ElicitationSchemaBuilder`, X45/X46) | every builder test: `test_elicitation_schema_builder_simple`, `test_elicitation_schema_builder_complex`, `test_elicitation_schema_serialization`; `test_elicitation.rs` `test_build_validation_required_field_not_in_properties`, `test_build_validation_required_field_exists`; `x08_property_order_is_the_byte_order_of_the_names` (empty builder: no properties, `required` `None`) |
| `BTreeMap::insert`, `<String as Ord>::cmp` (X47–X70) | the builder tests above (two and four properties); `x08_property_order_is_the_byte_order_of_the_names` (seven names inserted out of order, among them `""`, `"B"`, `"a"`, `"aa"`, `"~"`, `"é"`: the map iterates them in byte order; inserting `"a"` again replaces its value and keeps one entry) |
| `<String as PartialOrd>::partial_cmp` | not called by a target: it is the `partialOrdInst` field of the generated `Ord for String` instance; consistent with `cmp` (derived) |
| `<slice::Iter as Iterator>::all` (X35 `with_default`, X74 `build`) | `test_enum_schema_invalid_multi_default`, `test_enum_schema_multi_select_with_default`, `test_enum_schema_multi_select_empty_default_means_no_default`; `test_elicitation.rs` `test_build_validation_required_field_not_in_properties`, `test_build_validation_required_field_exists`; `x08_multi_select_default_membership` (empty, reordered, repeated defaults accepted; a non-member first, last, differing in case or by a space rejected; membership checked before `max_items`); `x08_build_required_names_must_be_property_names` (no, reordered, repeated required names accepted; a missing name first or last, `"A"`, `""` rejected) |
| `<str as Debug>::fmt` (X75 through `Result::expect`) | `test_elicitation.rs` `test_build_unchecked_panics_on_invalid`; `x08_build_unchecked_panics_with_the_error` (the exact panic message, the error `Debug`-quoted: not modelled); `x08_build_unchecked_returns_the_built_schema` |
| `prim::titles_mismatch_message` (X29) | `x08_enum_titles_count_mismatch_message` (2 vs 1, 0 vs 3, multi-select 2 vs 0, 1000 vs 10; equal counts accepted); no upstream test |
| `prim::sorted_keys` (X40, X74) | `test_elicitation_schema_with_schema_setter_serializes_dialect` (`ElicitationSchema::new` of the empty map); `x08_property_order_is_the_byte_order_of_the_names` (`property_order` of `build` and of `ElicitationSchema::new` is the byte order of the names; empty map and empty builder give `Some([])`); no upstream test checks the `property_order` of `build` |
| `const_titles` (translated, X33/X38) | `test_enum_schema_titled_single_select_serialization`, `test_enum_schema_titled_multi_select_serialization`, `test_enum_schema_titled_with_default`; `x08_titled_options_pair_titles_with_values_in_order` (three, one and zero pairs, single and multi select) |

Mutation check (2026-11-28, scratch copy with patches 01–08, `cargo test` as above filtered to
`elicitation_schema`, 40 tests; each mutant alone; failing tests listed exactly): swapping the
two counts in `prim::titles_mismatch_message` fails `x08_enum_titles_count_mismatch_message`
alone; `any` for `all` in X35 fails `test_enum_schema_invalid_multi_default`,
`test_enum_schema_multi_select_empty_default_means_no_default` and
`x08_multi_select_default_membership`; `|_| true` for `names.contains` in X74 fails
`x08_build_required_names_must_be_property_names` and `x08_build_unchecked_panics_with_the_error`;
`any` for `all` in X74 fails `x08_build_required_names_must_be_property_names` alone; reversed
values in `const_titles` fails `test_enum_schema_titled_multi_select_serialization`,
`test_enum_schema_titled_single_select_serialization`, `test_enum_schema_titled_with_default` and
`x08_titled_options_pair_titles_with_values_in_order`; `prim::sorted_keys` reversed, and
`property_order` of X40 dropped for fewer than two keys, each fail
`x08_property_order_is_the_byte_order_of_the_names` alone (no upstream test). Equivalent, survive:
dropping `!self.required.is_empty() &&` in X74 (`all` of the empty list is true), and `None =>
continue` for `None => break` in `const_titles` (the values are exhausted; every later `next` is
`None`).

**Clippy.** `cargo clippy --locked -p rmcp --lib --no-default-features --features
request-state,server,client,client-side-sse,transport-streamable-http-server,transport-streamable-http-client,auth`,
with and without `macros`, on the patch-01..07 and patch-01..08 copies (2026-11-28, repository
toolchain 1.96): the same 10 warnings on all four runs (same lint, file and message), none in
`elicitation_schema.rs`; with `--tests` and `macros`, no warning in `elicitation_schema.rs` (the XD
tests included).

**Linkage of the elicitation targets** (plan Section 19; human decision XD2). The eight patch-08
start points (the `Type::method` patterns `EnumSchemaBuilder::{enum_titles, with_default, build,
min_items, max_items}`, `ElicitationSchema::new`, `ElicitationSchemaBuilder::{build,
build_unchecked}`) and the opaque entry `rmcp::model::elicitation_schema::prim` are dropped from
the copy's Charon settings; the other 65 targets stay start points and are translated from the
unmodified source. XD2 extends the check in two ways. (a) In the name-shadowing pre-check, a
one-segment identifier directly before a `:=` of a declaration's body is no lookup when it is a
binder or a field name: after `let`, `let mut`, `have` or `(`, or a structure-instance field
(innermost bracket `{`, no `:` before it in that brace, after `{`, `,`, `with` or first on its
line); without it the field `min_items := none` of X34 `single_select` read as the committed-only
X36 `min_items`. (b) A std trait-instance block (`@[reducible, rust_trait_impl …]`, `Source:
'/rustc/…'`) of the unmodified source may differ from the committed one by fields only the
committed block sets (Aeneas emits a field only for a method the translated code reaches; the
others are the Aeneas structure's defaults), `def` becoming `impl_def` only when such a field
refers to the instance itself; and a token `P.m` that could read as field access on a
committed-only std trait instance `P` whose field is `m := P.m` names the same function either
way. Step 5 then requires the elaborated values of those instances to be the same structure
constructor with the same binders, levels and parameters, differing exactly at those fields
(`scripts/linkage/Dump.lean` dumps the constructor arguments, `compare_env.py` compares them);
every other constant must still elaborate identically. Without (b), X47–X70 failed: patch 08's
code reaches `Eq::assert_fields_are_eq` and `Ord::min` of `String`, and the `Clone` instance of
`String`. Run (2026-11-28, scratch clone with this change and the lead-owned changes committed):
`scripts/check-original-linkage.sh` exit 0 (Funs.lean 140 blocks: 138 identical, 2 std trait
instances equal up to committed-only fields, `CoreCmpEq` (`assert_fields_are_eq`) and
`CoreCmpOrd` (`min`, `impl_def`); Types.lean 72, the templates 45 and 11, identical; 926
constants and 50 externals elaborated, 2 std trait instances equal up to committed-only fields).
Negative controls (2026-11-28): end to end, a scratch clone whose committed `CoreCmpOrd` has
`cmp := …CoreCmpPartialOrdString.partial_cmp` fails the check (exit 1, `DIFFERS in committed
Funs.lean: alloc.string.String.Insts.CoreCmpOrd`); on the extracted text step, each fails with the
expected message: a committed-only `…EnumSchemaBuilderMultiSelect.none` (a value position), a
changed field value of X34, `let y : min_items := 0` (a type before `:=`), a `:` inside the
brace, a changed shared field of `CoreCmpOrd`, a field only the unmodified `CoreCmpEq` sets,
`impl_def` without a self-referring field, a changed instance type, and a committed-only `Clone`
instance whose `clone` field names another function; the unedited translations pass. On the
step-5 dumps of the run, `compare_env.py` fails without the instance list, when the shared field
`cmp` of `CoreCmpOrd` differs, when the listed field is wrong (`max`) and when the list names no
constant, and passes when only the listed field differs.

Committed-only instance fields (review finding TR4, 2026-11-28). Rule (b) assumed that a field only
the committed block sets either equals what the unmodified side gets (the Aeneas structure's
default, which Lean fills in) or is read by nothing the unmodified side runs. Step 5 now checks it
(`scripts/linkage/Widen.lean`, decided in `compare_env.py`): for each listed field, either the
kernel finds the committed value definitionally equal to the env0 value (transported exactly as a
JSON expression tree, closed, all constants present, reaching no listed instance) in env2, the
committed translation built with the hand-written `formal/trusted/Rmcp/*External.lean` (as `lake
build Rmcp RmcpExternal` builds it; env1's templates leave `String.Insts.CoreCmpEq.assert_fields_are_eq`
an axiom), or no definition reachable from env0's four modules and none reachable from the
hand-written external models projects the field (projection function, `Expr.proj` at its index,
or an eliminator of the structure such as `casesOn`, `noConfusion` or a `match`; the structure's
own generated declarations are not counted; theorems are not followed); otherwise the check
fails. Run (scratch clone, 2026-11-28): both fields are definitionally equal,
`CoreCmpEq.assert_fields_are_eq` (`Aeneas.Std.core.cmp.Eq`, index 1; committed: the external
`ok ()`, unmodified: the default `fun _ => ok ()`) and `CoreCmpOrd.min` (`core.cmp.Ord`, index 4;
committed `Ord.min.trait_default CoreCmpOrd`, unmodified `Ord.min_body (PartialOrd.lt
CoreCmpPartialOrdString)`), and neither is projected by any reachable definition of env0 or of
the external models. Stated limit (script header): code outside both environments (formal/specs,
formal/proofs, downstream users) is not inspected; it sees the committed values.

Executable controls (reviews TR4, TR10): `python3 -I scripts/linkage/controls.py <linkage-dir>
<controls-dir>` after a passing run, exit 0 iff every case has its expected outcome; 34 of 34 on
2026-11-28. Group A runs the text step (the step-4 Python extracted from the script) on edited
copies of both translations: the unedited translations, a value shadowed, a changed field value,
a `let` type, a brace with a colon, the instance cases above, and for the binder rule (TR10) a
`let mut` binder and a `have` binder (pass), a `have` type and a `have` value (fail), a named
argument `(min_items := none)` and one inside a structure-instance brace (pass), a named-argument
value `(x := min_items)`, an application `(f min_items := none)` and a dotted name in binder
position (fail). Group B runs `compare_env.py` on the run's dumps and `Widen.lean` results: the
cases above, and for TR4: results missing or incomplete, field index differing (fail), not
definitionally equal and projected by nothing (pass), not definitionally equal and projected in
env0 or only by an external model (fail), definitionally equal though projected (pass). Group C
builds a synthetic translation with `make_env.py` (env0, env1 with templates, env2 with a
hand-written model) and runs `Dump.lean`, `Widen.lean` and `compare_env.py` end to end: a field
`ok (x + 0)` against the default `ok x` (definitionally equal, accepted), `ok (x + 1)` projected by
nothing (accepted), projected by an env0 definition, by an env0 `match` (`uses5.match_1`) or only
by the hand-written model (each refused); with only the first two committed the check passes.

Translation runs (2026-11-28, Aeneas `nightly-2026.11.24-fb44cb4`, Charon `0.1.324`, Rust
`nightly-2026-09-17`, scratch clone of the repository at `1de63fd` with this change and the
lead-owned changes): `scripts/apply-patches.sh` exit 0 (patches 01–08 apply with `-F 0`);
`scripts/aeneas-translate.sh` exit 0 twice (all 179 targets defined, no `sorry`; the 73
`Type::method` start points each name exactly one local function, `EnumSchemaBuilder::with_default`
and `EnumSchemaBuilder::build` exactly their `SingleSelect` and `MultiSelect` methods, review
finding TR9; `Funs.lean` sha256
`eef79934a10cb94ba4c4d2ce2a5ca98ede7211b8da67a311c593d233137c3900` matching its new pin; the
second run byte-identical, the generated files unchanged by the XD tests of patch 02); every
target X01–X75 has a `def` with a body in `Funs.lean`. Controls of the `Type::method` count (TR9; the step-5b
Python of the script extracted and run on edited copies of the committed `translation.json`,
2026-11-28): unedited, pass; the `MultiSelect` `with_default` removed, a third instantiation
`EnumSchemaBuilder<Other>::build` added, a second `StringSchema<u8>::email` added, and
`StringSchema::email` made non-local, each fail with the pattern named; a closure below
`StringSchema::email` added, pass (a method's own items are not counted). Count of the `Type::method` patterns (review finding TR16): the step-5b check
now derives them from `start_from` itself (no `_` element; the element before the last starts with
an upper-case ASCII letter, a Rust type), requires that each reaches its methods only through the
type of an inherent impl (one that also matches an item by its own path is an error, no longer
skipped), that no other pattern does so, and that their number equals the derived one: 73 of 73 in
the full translation, 65 of 65 in the phase2 set of `scripts/check-original-linkage.sh` (logged by
both runs). Controls (the step-5b Python extracted and run on edited copies of the committed
`translation.json`, beside the round-2 version, 2026-11-28): unedited, and with the eight patch-08
patterns removed from `start_from` (65 of 65), pass; a function named exactly
`…::StringSchema::email`, one below that path, and a non-local item of that name each fail with
"also matches a translated item by its own path" and "72 … expected 73" (the round-2 check passed
all three, counting 72); a pattern `rmcp::model::lowmod::lowty::f` reaching a method through a
lower-case type fails (round 2: pass); a `Type::method` pattern matching nothing fails (as before).
