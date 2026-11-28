/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
module
public import Aeneas
public import Rmcp.Types

/-!
External functions of the `rmcp` translation (`Rmcp.Funs` imports this module).

Started at plan step S04a from the template that Aeneas generated
(`formal/translation/Rmcp/FunsExternal_Template.lean`) for the translation of commit
`f8fb6a7` with the Charon settings of S04a part 2 (derived `Debug` impls excluded), Aeneas
`nightly-2026.08.20-5d08da4`. Since the D2 fallback (2026-11-23) the translated source is the
patched copy (patch 01 on origin/main 7caec76), which gives the same translation; the `Source:`
line numbers below refer to it. Plan steps S08 (HMAC and Base64 `prim` functions) and S09
(standard library, `HashMap`, clock) replaced every placeholder of the template by a
definition with the generated name and signature, keeping the template's `@[rust_fun]` attribute
where it has one (the external functions of other crates; the five opaque `rmcp` functions, the
four `prim` functions and `RequestStateCodec::now_ms`, have none in the template). **This module
declares no axiom.** The two things the models cannot compute are `opaque` constants, which
add no axiom: the HMAC-SHA256 reference function `ExtModel.hmacSha256` and the clock reading
`ExtModel.nowMs` (and, for the unused hasher, `ExtModel.sipHash13`). The 26 external functions
that the Phase 2 translation (plan step S21) added were temporary `opaque` placeholders; plan
steps S26/S27 replaced them by definitions (sections "Phase 2", plan Section 18): string and
`Arc` equality and deref; `Option::or_else`, `Option` equality, `Result::ok`, `slice::first`,
`slice::strip_suffix`, slice-array equality, `SlicePattern::as_slice` of arrays and
`RangeInclusive::contains`, each the `core` body transcribed; `str::parse` and
`i64::from_str` (Rust's radix-10 grammar and error kinds); and the `Ipv4Addr`/`Ipv6Addr`
functions transcribed from `core/src/net/ip_addr.rs`. None of them needs an `opaque` constant.
Translation patch 03 (human decisions 2026-11-24, targets R09–R15) added the models of the last
section, for `seal`/`seal_with`, `with_rs1_signing`/`with_rs1_fallback`, `open_json`/
`open_json_with` and `new_with_keyring`, with two more `opaque` constants (no axiom):
`ExtModel.randomState` (the hash keys of a new map) and `ExtModel.serdeJsonFromSlice` (the
outcome of a caller's `Deserialize` impl).
Translation patch 04 (human decisions 2026-11-25, targets K01–K20 of `skill.rs`) added the models
of the section "Public `skill.rs` API": the twelve `skill::prim` wrappers and 28 functions of
`core`, `alloc`, `std`, `serde_json` and `unicode-general-category`, with three more `opaque`
constants (no axiom): `ExtModel.sha256`, `ExtModel.nfkc` and `ExtModel.generalCategory`.
Translation patch 05 (human decisions 2026-11-25, targets N01, N03–N11 of `metadata_resolver.rs`)
added the models of the section "`metadata_resolver.rs` address policy": the five
`metadata_resolver::prim` functions, three functions of `url` and eight of `core` and `alloc`,
with five more `opaque` constants (no axiom): `ExtModel.urlParse`, `ExtModel.urlHost`,
`ExtModel.urlHostStr`, `ExtModel.systemLookup` and `ExtModel.proxyEnvValues` (an environment
reading, under the review rule of `ExtModel.nowMs`).
Translation patch 06 (human decisions 2026-11-26 and 2026-11-27, AD1–AD8, targets A04–A10 of
`auth.rs`) added the models of the section "`auth.rs` OAuth metadata URL and issuer checks": the ten `auth::prim`
functions, seven functions of `url::Url` and two of `core`, with seven more `opaque` constants (no
axiom): `ExtModel.urlScheme`, `ExtModel.urlPath`, `ExtModel.urlFragment`, `ExtModel.urlPort`,
`ExtModel.urlSerialization`, `ExtModel.urlJoin` and `ExtModel.issuerUrl`.
Translation patch 07 (human decisions GD1 and GD2, 2026-11-27, targets G01–G04 of
`mcp_headers.rs`) added the models of the section "`mcp_headers.rs` header-value encoding": the
eight `mcp_headers::prim` functions (padded standard Base64 by renaming the alphabet of the
Base64url models, which are unchanged) and three functions of `core`, with no `opaque` constant
and no axiom.
Translation patch 08 (human decision XD1, 2026-11-28, targets X01–X75 of
`elicitation_schema.rs`) added the models of the section "Elicitation schema builders": the two
`elicitation_schema::prim` functions and seven functions of `core` and `alloc`, with no `opaque`
constant and no axiom.
The conventions below apply to all models.

Ordering note (S21): the generated external `core.result.Result.ok` shadows Aeneas' `ok` for
every declaration after it in the namespace `core.result.Result` (and for proofs that open it), so
such code must write `Aeneas.Std.Result.ok`; the models above it (`is_err`, `map_err`) are
unaffected.

Each definition returns `ok` exactly where the Rust function returns and `fail` where it
panics, with the exceptions stated in its docstring. Two conventions apply throughout:

* **Memory.** Allocation failure (out of memory) is not modelled (plan Section 4: unlimited
  memory is not established). A `String` that would grow beyond `isize::MAX` bytes is a
  deterministic Rust panic ("capacity overflow": `RawVec::grow_amortized`, lines 516–547 of
  `alloc/src/raw_vec/mod.rs`, through `finish_grow`, lines 557–580, and
  `RawVec::try_allocate_in`, lines 458–496, compute the layout with `layout_array`, lines
  929–935, which returns `CapacityOverflow` for a layout larger than `isize::MAX`; `handle_error`,
  lines 920–925, turns it into the panic) and is modelled as `fail panic`
  (`ExtModel.growString`). A panic that depends on the capacity history (amortized doubling
  past `isize::MAX` while the length still fits) is not modelled, so `ok` from a `String`
  model means "returns, or aborts or panics for memory reasons".
* **`Str`.** The Aeneas `Str` is `Slice U8` and admits byte sequences that are not UTF-8,
  while a Rust `&str` is always UTF-8. Functions that only read the bytes (`str::len`,
  `str::as_bytes`, `str` equality, `i64::from_str`) are modelled on all of `Str`;
  `String::push_str`, which builds a `String` from the bytes, returns `fail undef` outside the
  Rust domain (a non-UTF-8 `&str` is undefined behaviour in Rust).
* **Size convention.** A `Slice` or `String` of the model may be up to `Usize.max` bytes long,
  more than any machine can hold. The models make no claim about inputs of at least `2^61`
  bytes (2 EiB): such an input cannot exist in a running process on the translated target
  `x86_64-unknown-linux-gnu`, whose virtual address space is at most `2^57` bytes (5-level
  paging), and plan Section 4 does not model memory limits. The only behaviour this convention
  hides is the SHA-256 length overflow of the HMAC functions (section HMAC).

Source paths: `/rustc/library/…` is the `rust-src` of the pinned toolchain `nightly-2026-09-17`
(Aeneas upgrade, 2026-11-24: every cited `rust-src` range was compared with `nightly-2026-06-01`
and renumbered. Behaviour is unchanged except for `core.ops.range.RangeInclusive.contains`
(`RangeBounds::end_bound` of an exhausted `RangeInclusive` is now `Excluded(start)`; changed in
the Aeneas upgrade, human decision 2026-11-24; model reviewed 2026-11-24, re-signed 2026-11-24). Textual changes without a
change of behaviour: `RawVec::finish_grow` uses `map_err` instead of a `match`,
`SlicePartialEq::equal_same_length` a `for` instead of a `while` loop, `i64::from_ascii_radix`
is now `from_ascii_bytes_radix_impl` (same body, renamed panic helper), and comments);
`/cargo/registry/…` is the crate at the version in the path. `scripts/aeneas-translate.sh`
pins every crate cited here (`PINNED_DEPS`): `hmac 0.13.0`, `sha2 0.11.2`, `base64 0.23.1`,
`digest 0.11.3`, `zeroize 1.9.2`, `chrono 0.4.45`, `serde_json 1.0.154` (plan Section 4) and, since
translation patch 04, `percent-encoding 2.3.2`, `unicode-normalization 0.1.26` and
`unicode-general-category 1.1.0`, and since translation patch 05 `url 2.5.9`. The
Rust tests that check the models are listed in `formal/trusted/evidence/README.md`.
-/
@[expose] public section
open Aeneas Aeneas.Std Result ControlFlow Error
open rmcp

/-! ## Model functions

Pure functions used by the definitions below. They are root-level names in the namespace
`ExtModel` (never `rmcp`, see `formal/README.md`, "Trusted base"). -/

namespace ExtModel

/-- The byte with value `n % 256`. -/
def byte (n : Nat) : Std.U8 := ⟨BitVec.ofNat _ n⟩

/-- The UTF-8 bytes of a Lean `String` (its `toByteArray`, as `U8` values; the same conversion
as the Aeneas `toStr` for literals). A Lean `String` is always valid UTF-8, as is a Rust
`String`. -/
def utf8 (s : String) : List Std.U8 := s.toByteArray.toList.map (fun x => byte x.toNat)

/-- **UTF-8 premise** (the Rust `&str` invariant as a proposition): the bytes `l` are the UTF-8
encoding of a string. Every Rust `&str` is valid UTF-8; an Aeneas `Str` need not be (the `Str`
convention above). Review rule (translation patch 05, human decisions 2026-11-25/2026-11-26:
rule (ii) 2026-11-26, nested `&str` 2026-11-26; the same statement is in `formal/README.md`,
`formal/README.md` and `formal/trusted/evidence/README.md`): a statement may assume that a
`Str` is valid UTF-8 (i) only as the premise `IsUtf8 s.val`, and (ii) only for (a) a `&str`
argument of the function the statement is about, or a `&str` carried by an argument (such as the
domain `d` of the argument `host : Host<&str>` of `AuthorizationManager::is_loopback_metadata_host`,
`host = url.host.Host.Domain d`), and (b) the hosts that the opaque `url` functions return:
`IsUtf8 d.val` for `urlHost u = some (url.host.Host.Domain d)` and `IsUtf8 h.val` for
`urlHostStr u = some h`. That a `Str` computed from such values is UTF-8 is proved, not assumed
(`isUtf8_dropTrailingDots`, `isUtf8_map_asciiLowercase` in `Proofs.External.MetadataResolver`).
No axiom or model asserts it. Approved exception (spec owner, 2026-11-27): G04
`decode_header_value` assumes the conditional form `Defs.McpHeaders.sentinelInner? value.val =
none → IsUtf8 value.val`, weaker than `IsUtf8 value.val` and shown exact by
`Theorems.mcp_headers.decode_header_value_fail_undef` (both in the `Proofs` library). -/
def IsUtf8 (l : List Std.U8) : Prop := ∃ t : String, l = utf8 t

/-- The `String` whose UTF-8 encoding is `l`, or `none` if `l` is not valid UTF-8 (Lean's
`String.fromUTF8?`, which accepts exactly the encodings of lists of Unicode scalar values: no
surrogates, no overlong forms, nothing above `U+10FFFF`; the same set as Rust's
`core::str::from_utf8`, `core/src/str/validations.rs`, `run_utf8_validation`). -/
def strOfBytes? (l : List Std.U8) : Option String :=
  String.fromUTF8? ⟨(l.map (fun b => b.val.toUInt8)).toArray⟩

/-- The largest byte length of a Rust `String`: `isize::MAX` (`alloc/src/raw_vec/mod.rs`,
`layout_array` fails above it). -/
def maxStringBytes : Nat := Isize.max.toNat

/-- `ok r` if `r` fits in a Rust `String`, otherwise the "capacity overflow" panic of the
reservation that would create it. -/
def growString (r : String) : Result String :=
  if r.utf8ByteSize ≤ maxStringBytes then ok r else fail panic

/-! ### HMAC-SHA256 -/

/-- **HMAC-SHA256 reference function** (opaque): `hmacSha256 key msg` is the 32-byte
HMAC-SHA256 tag of `msg` under `key` (RFC 2104 with SHA-256, FIPS 180-4), for a key of any
length. Opaque because its value is not modelled (plan Section 4; the correctness of the
`hmac`/`sha2` crates is not established). The value given here only shows that the type is
inhabited; an `opaque` constant does not unfold to it. -/
opaque hmacSha256 : List Std.U8 → List Std.U8 → Std.Array Std.U8 32#usize :=
  fun _ _ => Std.Array.from (List.replicate 32 (byte 0)) (by simp)

/-! ### Base64url without padding -/

/-- The symbol of the URL-safe alphabet for the 6-bit value `n` (RFC 4648 Section 5, Table 2:
`A`–`Z` = 0–25, `a`–`z` = 26–51, `0`–`9` = 52–61, `-` = 62, `_` = 63; `base64-0.23.1`
`src/alphabet.rs` lines 259–262, `URL_SAFE`). Values above 63 do not occur. -/
def b64Sym (n : Nat) : Std.U8 :=
  if n < 26 then byte (65 + n)
  else if n < 52 then byte (97 + (n - 26))
  else if n < 62 then byte (48 + (n - 52))
  else if n = 62 then byte 45
  else byte 95

/-- The 6-bit value of a symbol of the URL-safe alphabet, `none` for every other byte
(including the padding byte `=` and the standard-alphabet symbols `+` and `/`). -/
def b64Val (c : Std.U8) : Option Nat :=
  if 65 ≤ c.val ∧ c.val ≤ 90 then some (c.val - 65)
  else if 97 ≤ c.val ∧ c.val ≤ 122 then some (c.val - 71)
  else if 48 ≤ c.val ∧ c.val ≤ 57 then some (c.val + 4)
  else if c.val = 45 then some 62
  else if c.val = 95 then some 63
  else none

/-- **Base64url encoding without padding** (RFC 4648 Section 5; Section 3.2 without the `=`
padding): every 3 bytes give 4 symbols, a final 1 or 2 bytes give 2 or 3 symbols whose unused
low bits are zero. This is the output of `base64-0.23.1` `URL_SAFE_NO_PAD`
(`src/engine/general_purpose/mod.rs` line 472: alphabet `URL_SAFE`, config `NO_PAD` =
`encode_padding = false`, lines 499–501), produced by `Engine::encode_string`
(`src/engine/mod.rs` lines 188–201) through `ChunkedEncoder` (`src/chunked_encoder.rs`), which
encodes 768-byte chunks (a multiple of 3, so the chunking does not change the output). -/
def b64 : List Std.U8 → List Std.U8
  | a :: b :: c :: rest =>
    b64Sym (a.val / 4) :: b64Sym (a.val % 4 * 16 + b.val / 16) ::
      b64Sym (b.val % 16 * 4 + c.val / 64) :: b64Sym (c.val % 64) :: b64 rest
  | [a, b] => [b64Sym (a.val / 4), b64Sym (a.val % 4 * 16 + b.val / 16), b64Sym (b.val % 16 * 4)]
  | [a] => [b64Sym (a.val / 4), b64Sym (a.val % 4 * 16)]
  | [] => []

/-- **Strict Base64url decoding without padding**, as `base64-0.23.1` `URL_SAFE_NO_PAD`
decodes (`Engine::decode`, `src/engine/mod.rs` lines 277–301; `decode_helper`,
`src/engine/general_purpose/decode.rs`; `decode_suffix`,
`src/engine/general_purpose/decode_suffix.rs`), with the error collapsed to `none`:

* every byte must be a symbol of the URL-safe alphabet; `=` is rejected in any position
  (config `NO_PAD` has `DecodePaddingMode::RequireNone`, `mod.rs` line 501: padding in the
  final quad is `InvalidPadding` or `InvalidByte`, in an earlier quad `InvalidByte`);
* a length `≡ 1 (mod 4)` is rejected (`InvalidLength`);
* a final group of 2 or 3 symbols must have zero unused low bits (the config default
  `decode_allow_trailing_bits = false`, `mod.rs` line 341; `InvalidLastSymbol` otherwise);
* otherwise the result is the standard decoding (4 symbols give 3 bytes, a final 2 or 3 give
  1 or 2). -/
def b64Decode : List Std.U8 → Option (List Std.U8)
  | [] => some []
  | c0 :: c1 :: c2 :: c3 :: rest => do
    let v0 ← b64Val c0
    let v1 ← b64Val c1
    let v2 ← b64Val c2
    let v3 ← b64Val c3
    let tail ← b64Decode rest
    some (byte (v0 * 4 + v1 / 16) :: byte (v1 % 16 * 16 + v2 / 4) :: byte (v2 % 4 * 64 + v3) ::
      tail)
  | [c0, c1, c2] => do
    let v0 ← b64Val c0
    let v1 ← b64Val c1
    let v2 ← b64Val c2
    if v2 % 4 = 0 then some [byte (v0 * 4 + v1 / 16), byte (v1 % 16 * 16 + v2 / 4)] else none
  | [c0, c1] => do
    let v0 ← b64Val c0
    let v1 ← b64Val c1
    if v1 % 16 = 0 then some [byte (v0 * 4 + v1 / 16)] else none
  | [_] => none

/-- Decoding never produces more bytes than it reads (so the result fits in a `Vec`). -/
theorem b64Decode_length_le :
    ∀ (s l : List Std.U8), b64Decode s = some l → l.length ≤ s.length
  | [], l, h => by simp [b64Decode] at h; simp [← h]
  | _ :: _ :: _ :: _ :: rest, l, h => by
    simp only [b64Decode, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨_, _, _, _, _, _, _, _, tail, ht, hl⟩ := h
    have := b64Decode_length_le rest tail ht
    simp at hl; subst hl; simp; omega
  | [_, _, _], l, h => by
    simp only [b64Decode, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨_, _, _, _, _, _, hl⟩ := h
    split at hl <;> simp at hl; subst hl; simp
  | [_, _], l, h => by
    simp only [b64Decode, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨_, _, _, _, hl⟩ := h
    split at hl <;> simp at hl; subst hl; simp
  | [_], l, h => by simp [b64Decode] at h

/-! ### Hasher and clock -/

/-- **SipHash-1-3 reference function** (opaque): `sipHash13 k0 k1 msg` is the value of
`finish` of a `SipHasher13` with keys `k0`, `k1` after writing the byte stream `msg`
(`core/src/hash/sip.rs`). Opaque because no statement depends on hash values: the
`HashMap::get` model does not hash (see `std.collections.hash.map.HashMap.get`). -/
opaque sipHash13 : Std.U64 → Std.U64 → List Std.U8 → Std.U64

/-- **Clock reading** (opaque): the value of `chrono::Utc::now().timestamp_millis()` that
`RequestStateCodec::now_ms` returns. A single constant cannot model that two readings differ,
and it makes every function that reads the clock (`now_ms`, `open`, `open_with` and, since
translation patch 03, `open_json`, `open_json_with`, `seal`, `seal_with`) pure. Review rule: no
spec statement mentions the functions `rmcp.model.request_state.RequestStateCodec.now_ms`,
`…RequestStateCodec.open`, `…RequestStateCodec.open_with`, `…RequestStateCodec.open_json`,
`…RequestStateCodec.open_json_with`, `…RequestStateCodec.seal` or
`…RequestStateCodec.seal_with` (a variable named `now_ms`, such as the time parameter of E01
`open_authenticated_body`, is not covered; `formal/README.md`, "Trusted base"). Exceptions
(human decisions 2026-11-24, extended 2026-11-25; `formal/README.md`, "Trusted base"): only the
spec theorems of `open`, `open_with`, `open_json`, `open_json_with`, `seal` and `seal_with`,
their `Theorems.*` restatements and the corollaries `open_with_spec_of_length_le`,
`seal_with_spec_of_length_le` and `seal_spec_of_length_le` (and their restatements) may name
these functions and `nowMs`, and only with these postconditions: `open`/`open_with`,
`resultBytes result = openAt … nowMs.val`; `open_json`/`open_json_with`, the error of
`openAt … nowMs.val` unchanged, otherwise the `serdeJsonFromSlice` outcome for the opened
payload with `Err` mapped to `Deserialization`; `seal`/`seal_with`,
`sealAt … nowMs.val = some (utf8 result)`, with `sealAt` the `Defs.CodecState` model of the
private `seal_at` (human decision 2026-11-25; it replaces the earlier wording "the result of the
translated `seal_at` at `nowMs`"). Their docstrings state the one-reading caveat and the
inherited exceptions. Besides these, only the model's own spec theorem
`model.request_state.RequestStateCodec.now_ms_spec` (postcondition `result = nowMs`; human
decision 2026-11-25) names `now_ms` and `nowMs`. No other statement names `nowMs`, and no
statement has a premise or conclusion about its value or relates two clock readings; the
internal statements of `seal_at` (R10a) and of its round trip with `open_at` (R10b) use explicit
times. -/
opaque nowMs : Std.I64

end ExtModel

/-! ## HMAC -/

/-- [rmcp::model::request_state_wire::prim::hmac_sha256]:
    Source: 'crates/rmcp/src/model/request_state_wire.rs', lines 253:4-258:5
    Visibility: public

**Model:** `ok (hmacSha256 key msg)`. Succeeds: `Hmac::<Sha256>::new_from_slice`
returns `Ok` for every key length (`hmac-0.13.0/src/block_api.rs` lines 53–69: the key is
hashed or padded to the block size by `get_der_key`, `src/utils.rs` lines 9–32, no error path),
so the `expect` never panics; `update` and `finalize` do not fail within the size convention of
this module (module docstring).
Exception (not modelled): SHA-256 finalisation computes the length of the hashed input in bits
as a `u64` (`sha2-0.11.2/src/block_api.rs` line 66, `8 * (buffer.get_pos() as u64 + bs *
self.block_len)`), which overflows, and panics under `overflow-checks`, when the hashed input
reaches `2^61` bytes. This happens for a **message** of at least `2^61 − 64` bytes (the inner
hash covers the 64-byte key block and the message) and for a **key** of at least `2^61` bytes
(`get_der_key` hashes a key longer than the 64-byte block with `D::digest`). The model does not
represent that panic: both inputs lie outside the size convention (at least `2^61` bytes, more
than the at most `2^57`-byte address space of `x86_64`), like out of memory, which plan
Section 4 does not model. -/
def model.request_state_wire.prim.hmac_sha256 (key : Slice Std.U8) (msg : Slice Std.U8) :
    Result (Std.Array Std.U8 32#usize) :=
  ok (ExtModel.hmacSha256 key.val msg.val)

/-- [rmcp::model::request_state_wire::prim::hmac_sha256_verify]:
    Source: 'crates/rmcp/src/model/request_state_wire.rs', lines 261:4-266:5
    Visibility: public

**Model:** `ok (tag = hmacSha256 key msg)`, compared as byte lists, so a tag of any length
other than 32 is rejected. `Mac::verify_slice` (`digest-0.11.3/src/mac.rs` lines 139–146)
returns `Err` if `tag.len() != OutputSize` (32 for SHA-256) and otherwise compares the computed
tag with `tag` (constant-time `ct_eq`; timing is not modelled); `is_ok()` turns that into the
`bool`. Key setup always succeeds, as for `hmac_sha256`, with the same unmodelled
key- and message-length exception (a key of at least `2^61` bytes or a message of at least
`2^61 − 64` bytes, outside the size convention). -/
def model.request_state_wire.prim.hmac_sha256_verify (key : Slice Std.U8) (msg : Slice Std.U8)
    (tag : Slice Std.U8) : Result Bool :=
  ok (decide (tag.val = (ExtModel.hmacSha256 key.val msg.val).val))

/-! ## Base64 -/

/-- [rmcp::model::request_state_wire::prim::b64_encode_into]:
    Source: 'crates/rmcp/src/model/request_state_wire.rs', lines 269:4-271:5
    Visibility: public

**Model:** appends the symbols `b64 input` (ASCII, one `Char` per byte) to `out`.
`URL_SAFE_NO_PAD.encode_string` (`base64-0.23.1/src/engine/mod.rs` lines 188–201) pushes the
encoded chunks with `String::push_str` (`src/chunked_encoder.rs`, `StringSink`); the
`str::from_utf8(..).unwrap()` there cannot fail on ASCII. The result is subject to the
`String` length limit (`ExtModel.growString`). -/
def model.request_state_wire.prim.b64_encode_into (input : Slice Std.U8) (out : String) :
    Result String :=
  ExtModel.growString
    (out ++ String.ofList ((ExtModel.b64 input.val).map (fun b => Char.ofNat b.val)))

/-- [rmcp::model::request_state_wire::prim::b64_decode]:
    Source: 'crates/rmcp/src/model/request_state_wire.rs', lines 274:4-276:5
    Visibility: public

**Model:** `ok (b64Decode input)`, the decoded bytes as a `Vec` (`URL_SAFE_NO_PAD.decode(input)
.ok()`; `Engine::decode` allocates a buffer of the conservative estimate and never reaches its
`unreachable!`). -/
def model.request_state_wire.prim.b64_decode (input : Slice Std.U8) :
    Result (Option (alloc.vec.Vec Std.U8)) :=
  match h : ExtModel.b64Decode input.val with
  | none => ok none
  | some l => ok (some (alloc.vec.Vec.from l ((ExtModel.b64Decode_length_le _ _ h).trans input.property)))

/-! ## Standard library -/

/-- [core::option::{impl core::default::Default for core::option::Option<T>}::default]:
    Source: '/rustc/library/core/src/option.rs', lines 2314:4-2314:29
    Name pattern: [core::option::{core::default::Default<core::option::Option<@T>>}::default]
    Visibility: public

**Model:** `None` (lines 2314–2316). -/
@[rust_fun
  "core::option::{core::default::Default<core::option::Option<@T>>}::default"]
def core.option.Option.Insts.CoreDefaultDefault.default (T : Type) : Result (Option T) :=
  ok none

/-- [core::result::{core::result::Result<T, E>}::is_err]:
    Source: '/rustc/library/core/src/result.rs', lines 647:4-647:38
    Name pattern: [core::result::{core::result::Result<@T, @E>}::is_err]
    Visibility: public

**Model:** `true` exactly for `Err` (`!self.is_ok()`, lines 647–649). -/
@[rust_fun "core::result::{core::result::Result<@T, @E>}::is_err"]
def core.result.Result.is_err {T : Type} {E : Type} (self : core.result.Result T E) :
    Result Bool :=
  match self with
  | core.result.Result.Ok _ => ok false
  | core.result.Result.Err _ => ok true

/-- [core::slice::{impl core::default::Default for &'_0 [T]}::default]:
    Source: '/rustc/library/core/src/slice/mod.rs', lines 5655:4-5655:24
    Name pattern: [core::slice::{core::default::Default<&'0 [@T]>}::default]
    Visibility: public

**Model:** the empty slice (`&[]`, lines 5655–5657). -/
@[rust_fun "core::slice::{core::default::Default<&'0 [@T]>}::default"]
def Shared0Slice.Insts.CoreDefaultDefault.default (T : Type) : Result (Slice T) :=
  ok (Slice.new T)

/-- [core::str::{str}::len]:
    Source: '/rustc/library/core/src/str/mod.rs', lines 155:4-155:36
    Name pattern: [core::str::{str}::len]
    Visibility: public

**Model:** the number of bytes (`self.as_bytes().len()`, lines 155–157), for every `Str`. -/
@[rust_fun "core::str::{str}::len"]
def core.str.Str.len (self : Str) : Result Std.Usize :=
  ok (Slice.len (self : Slice Std.U8))

/-- [core::str::{str}::as_bytes]:
    Source: '/rustc/library/core/src/str/mod.rs', lines 514:4-514:41
    Name pattern: [core::str::{str}::as_bytes]
    Visibility: public

**Model:** the same bytes (a `transmute` of `&str` to `&[u8]`, lines 514–517), for every
`Str`. -/
@[rust_fun "core::str::{str}::as_bytes"]
def core.str.Str.as_bytes (self : Str) : Result (Slice Std.U8) :=
  ok self

/-- The value of the first entry of `entries` whose key, borrowed as `Q`, is equal to `k`
(`k == key.borrow()`, through the `Borrow` and `Eq` instances; their failures propagate). -/
def ExtModel.HashMap.find {K V Q : Type} (coreborrowBorrowInst : core.borrow.Borrow K Q)
    (corecmpEqInst : core.cmp.Eq Q) (k : Q) : List (K × V) → Result (Option V)
  | [] => ok none
  | (key, v) :: rest => do
    let kb ← coreborrowBorrowInst.borrow key
    let b ← corecmpEqInst.partialEqInst.eq k kb
    if b then ok (some v) else ExtModel.HashMap.find coreborrowBorrowInst corecmpEqInst k rest

/-- [std::collections::hash::map::{std::collections::hash::map::HashMap<K, V, S, A>}::get]:
    Source: '/rustc/library/std/src/collections/hash/map.rs', lines 1034:4-1037:21
    Name pattern: [std::collections::hash::map::{std::collections::hash::map::HashMap<@K, @V, @S, @A>}::get]
    Visibility: public

**Model:** lookup by key equality: the value of the first entry whose key `key` satisfies
`k == key.borrow()` (`ExtModel.HashMap.find`). The Rust function is `self.base.get(k)`
(lines 1034–1040), i.e. hashbrown 0.17.1 `HashMap::get` (`src/map.rs`): `None` on an empty
table, otherwise it hashes `k` with `make_hash` and returns the entry for which
`Equivalent::equivalent` (`k == key.borrow()`) holds among the entries with a matching hash.

Why hashing is not modelled: for a `Hash`/`Eq` pair that agree (`a == b → hash a = hash b`,
required by the `HashMap` documentation, lines 37–47, and for the borrowed form `Q`, lines
1018–1020), the probe finds the entry with an
equal key whatever the hash values are, and a map has at most one such entry. For the only
instance in the translation, `K = Q = String`, equality is byte equality and `Hash` writes the
bytes, so they agree; hashing a `String` never panics, and `String` equality does not fail.
The model is therefore faithful for `Hash`/`Eq` instances that agree and do not fail; only
`K = Q = String` occurs. Pairwise distinct keys are needed only to identify *which* value is
returned: `find` returns `some` exactly when an entry with an equal key exists, with or
without duplicates (see `std.collections.hash.map.HashMap`). -/
@[rust_fun
  "std::collections::hash::map::{std::collections::hash::map::HashMap<@K, @V, @S, @A>}::get"]
def std.collections.hash.map.HashMap.get
    {K : Type} {V : Type} {S : Type} {A : Type} {Q : Type} {Clause2_Hasher : Type}
    (_corecmpEqInst : core.cmp.Eq K) (_corehashHashInst : core.hash.Hash K)
    (_corehashBuildHasherInst : core.hash.BuildHasher S Clause2_Hasher)
    (coreborrowBorrowInst : core.borrow.Borrow K Q) (_corehashHashInst1 : core.hash.Hash Q)
    (corecmpEqInst1 : core.cmp.Eq Q)
    (self : std.collections.hash.map.HashMap K V S A) (k : Q) : Result (Option V) :=
  ExtModel.HashMap.find coreborrowBorrowInst corecmpEqInst1 k self.entries

/-- [std::collections::hash::map::{impl core::clone::Clone for std::collections::hash::map::HashMap<K, V, S, A>}::clone]:
    Source: '/rustc/library/std/src/collections/hash/map.rs', lines 1437:4-1437:27
    Name pattern: [std::collections::hash::map::{core::clone::Clone<std::collections::hash::map::HashMap<@K, @V, @S, @A>>}::clone]
    Visibility: public

**Model:** clones the hash builder, the allocator and every key and value
(`Self { base: self.base.clone() }`, lines 1437–1439; hashbrown 0.17.1 `src/map.rs`
`impl Clone for HashMap`: `hash_builder.clone()`, `table.clone()`). -/
@[rust_fun
  "std::collections::hash::map::{core::clone::Clone<std::collections::hash::map::HashMap<@K, @V, @S, @A>>}::clone"]
def std.collections.hash.map.HashMap.Insts.CoreCloneClone.clone
    {K : Type} {V : Type} {S : Type} {A : Type} (corecloneCloneInst : core.clone.Clone K)
    (corecloneCloneInst1 : core.clone.Clone V) (corecloneCloneInst2 : core.clone.Clone S)
    (corecloneCloneInst3 : core.clone.Clone A)
    (self : std.collections.hash.map.HashMap K V S A) :
    Result (std.collections.hash.map.HashMap K V S A) := do
  let hash_builder ← corecloneCloneInst2.clone self.hash_builder
  let alloc ← corecloneCloneInst3.clone self.alloc
  let entries ← self.entries.mapM (fun (e : K × V) => do
    let k ← corecloneCloneInst.clone e.1
    let v ← corecloneCloneInst1.clone e.2
    ok (k, v))
  ok { hash_builder, alloc, entries }

/-- [std::hash::random::{impl core::clone::Clone for std::hash::random::RandomState}::clone]:
    Source: '/rustc/library/std/src/hash/random.rs', lines 34:9-34:14
    Name pattern: [std::hash::random::{core::clone::Clone<std::hash::random::RandomState>}::clone]
    Visibility: public

**Model:** the same value (derived `Clone` of two `u64` fields). -/
@[rust_fun
  "std::hash::random::{core::clone::Clone<std::hash::random::RandomState>}::clone"]
def std.hash.random.RandomState.Insts.CoreCloneClone.clone
    (self : std.hash.random.RandomState) : Result std.hash.random.RandomState :=
  ok self

/-- [std::hash::random::{impl core::hash::Hasher for std::hash::random::DefaultHasher}::finish]:
    Source: '/rustc/library/std/src/hash/random.rs', lines 140:4-140:27
    Name pattern: [std::hash::random::{core::hash::Hasher<std::hash::random::DefaultHasher>}::finish]
    Visibility: public

**Model:** `ok (sipHash13 k0 k1 written)` (`self.0.finish()`, lines 140–142; SipHash-1-3 of
the keys and the byte stream). -/
@[rust_fun
  "std::hash::random::{core::hash::Hasher<std::hash::random::DefaultHasher>}::finish"]
def std.hash.random.DefaultHasher.Insts.CoreHashHasher.finish
    (self : std.hash.random.DefaultHasher) : Result Std.U64 :=
  ok (ExtModel.sipHash13 self.k0 self.k1 self.written)

/-- [std::hash::random::{impl core::hash::Hasher for std::hash::random::DefaultHasher}::write]:
    Source: '/rustc/library/std/src/hash/random.rs', lines 130:4-130:35
    Name pattern: [std::hash::random::{core::hash::Hasher<std::hash::random::DefaultHasher>}::write]
    Visibility: public

**Model:** appends `msg` to the byte stream (`self.0.write(msg)`, lines 130–132). -/
@[rust_fun
  "std::hash::random::{core::hash::Hasher<std::hash::random::DefaultHasher>}::write"]
def std.hash.random.DefaultHasher.Insts.CoreHashHasher.write
    (self : std.hash.random.DefaultHasher) (msg : Slice Std.U8) :
    Result std.hash.random.DefaultHasher :=
  ok { self with written := self.written ++ msg.val }

/-- [std::hash::random::{impl core::hash::BuildHasher<std::hash::random::DefaultHasher> for std::hash::random::RandomState}::build_hasher]:
    Source: '/rustc/library/std/src/hash/random.rs', lines 83:4-83:43
    Name pattern: [std::hash::random::{core::hash::BuildHasher<std::hash::random::RandomState, std::hash::random::DefaultHasher>}::build_hasher]
    Visibility: public

**Model:** a hasher with the map's keys and an empty byte stream
(`DefaultHasher(SipHasher13::new_with_keys(self.k0, self.k1))`, lines 83–85). -/
@[rust_fun
  "std::hash::random::{core::hash::BuildHasher<std::hash::random::RandomState, std::hash::random::DefaultHasher>}::build_hasher"]
def std.hash.random.RandomState.Insts.CoreHashBuildHasherDefaultHasher.build_hasher
    (self : std.hash.random.RandomState) : Result std.hash.random.DefaultHasher :=
  ok { k0 := self.k0, k1 := self.k1, written := [] }

/-- [alloc::string::{impl core::cmp::PartialEq<alloc::string::String> for alloc::string::String}::eq]:
    Source: '/rustc/library/alloc/src/string.rs', lines 350:9-350:18
    Name pattern: [alloc::string::{core::cmp::PartialEq<alloc::string::String, alloc::string::String>}::eq]
    Visibility: public

**Model:** equality (derived `PartialEq` of `String { vec: Vec<u8> }`, line 350: byte
equality, which is equality of the strings). -/
@[rust_fun
  "alloc::string::{core::cmp::PartialEq<alloc::string::String, alloc::string::String>}::eq"]
def alloc.string.String.Insts.CoreCmpPartialEqString.eq (self : String) (other : String) :
    Result Bool :=
  ok (decide (self = other))

/-- [alloc::string::{impl core::cmp::Eq for alloc::string::String}::assert_fields_are_eq]:
    Source: '/rustc/library/alloc/src/string.rs', lines 350:32-350:34
    Name pattern: [alloc::string::{core::cmp::Eq<alloc::string::String>}::assert_fields_are_eq]
    Visibility: public

**Model:** `ok ()` (a derived marker method with an empty body). -/
@[rust_fun
  "alloc::string::{core::cmp::Eq<alloc::string::String>}::assert_fields_are_eq"]
def alloc.string.String.Insts.CoreCmpEq.assert_fields_are_eq (_self : String) : Result Unit :=
  ok ()

/-- [alloc::string::{alloc::string::String}::with_capacity]:
    Source: '/rustc/library/alloc/src/string.rs', lines 493:4-493:51
    Name pattern: [alloc::string::{alloc::string::String}::with_capacity]
    Visibility: public

**Model:** the empty string; `fail panic` if `capacity > isize::MAX`
(`String { vec: Vec::with_capacity(capacity) }`, lines 493–495; `RawVec::try_allocate_in`
rejects the layout and `handle_error` panics with "capacity overflow"). Capacity is not part of
the value model. -/
@[rust_fun "alloc::string::{alloc::string::String}::with_capacity"]
def alloc.string.String.with_capacity (capacity : Std.Usize) : Result String :=
  if capacity.val ≤ ExtModel.maxStringBytes then ok "" else fail panic

/-- [alloc::string::{alloc::string::String}::from_utf8]:
    Source: '/rustc/library/alloc/src/string.rs', lines 569:4-569:67
    Name pattern: [alloc::string::{alloc::string::String}::from_utf8]
    Visibility: public

**Model:** `Ok s` if the bytes are the UTF-8 encoding of a string `s`, otherwise
`Err { bytes := vec }` (lines 569–574: `str::from_utf8(&vec)` decides; see
`ExtModel.strOfBytes?`). -/
@[rust_fun "alloc::string::{alloc::string::String}::from_utf8"]
def alloc.string.String.from_utf8 (vec : alloc.vec.Vec Std.U8) :
    Result (core.result.Result String alloc.string.FromUtf8Error) :=
  match ExtModel.strOfBytes? vec.val with
  | some s => ok (core.result.Result.Ok s)
  | none => ok (core.result.Result.Err { bytes := vec })

/-- [alloc::string::{alloc::string::String}::push_str]:
    Source: '/rustc/library/alloc/src/string.rs', lines 1122:4-1122:44
    Name pattern: [alloc::string::{alloc::string::String}::push_str]
    Visibility: public

**Model:** appends the string whose UTF-8 bytes are `string`
(`self.vec.extend_from_slice(string.as_bytes())`, lines 1122–1124), subject to the `String`
length limit (`ExtModel.growString`). `fail undef` if `string` is not UTF-8, which no Rust
`&str` is. -/
@[rust_fun "alloc::string::{alloc::string::String}::push_str"]
def alloc.string.String.push_str (self : String) (string : Str) : Result String :=
  match ExtModel.strOfBytes? string.val with
  | some t => ExtModel.growString (self ++ t)
  | none => fail undef

/-- [alloc::string::{alloc::string::String}::push]:
    Source: '/rustc/library/alloc/src/string.rs', lines 1451:4-1451:36
    Name pattern: [alloc::string::{alloc::string::String}::push]
    Visibility: public

**Model:** appends the character (its UTF-8 encoding, lines 1451–1461), subject to the
`String` length limit (`ExtModel.growString`). A Lean `Char` is a Unicode scalar value, as a
Rust `char` is. -/
@[rust_fun "alloc::string::{alloc::string::String}::push"]
def alloc.string.String.push (self : String) (ch : Char) : Result String :=
  ExtModel.growString (self.push ch)

/-- [alloc::string::{alloc::string::String}::as_bytes]:
    Source: '/rustc/library/alloc/src/string.rs', lines 1480:4-1480:41
    Name pattern: [alloc::string::{alloc::string::String}::as_bytes]
    Visibility: public

**Model:** the UTF-8 bytes (`self.vec.as_slice()`, lines 1480–1482). A Rust `String` has at
most `isize::MAX` bytes, so the bytes always fit in a slice; a Lean `String` longer than
`Usize.max` bytes, which no Rust `String` is, gives `fail maximumSizeExceeded`. -/
@[rust_fun "alloc::string::{alloc::string::String}::as_bytes"]
def alloc.string.String.as_bytes (self : String) : Result (Slice Std.U8) :=
  if h : (ExtModel.utf8 self).length ≤ Usize.max then ok (Std.Slice.from (ExtModel.utf8 self) h)
  else fail maximumSizeExceeded

/-- [alloc::string::{impl core::clone::Clone for alloc::string::String}::clone]:
    Source: '/rustc/library/alloc/src/string.rs', lines 2425:4-2425:27
    Name pattern: [alloc::string::{core::clone::Clone<alloc::string::String>}::clone]
    Visibility: public

**Model:** the same string (`String { vec: self.vec.clone() }`, lines 2425–2427). -/
@[rust_fun "alloc::string::{core::clone::Clone<alloc::string::String>}::clone"]
def alloc.string.String.Insts.CoreCloneClone.clone (self : String) : Result String :=
  ok self

/-- [alloc::string::{impl core::hash::Hash for alloc::string::String}::hash]:
    Source: '/rustc/library/alloc/src/string.rs', lines 2801:4-2801:51
    Name pattern: [alloc::string::{core::hash::Hash<alloc::string::String>}::hash]
    Visibility: public

**Model:** writes the UTF-8 bytes, then the byte `0xff`, through the hasher instance
(`(**self).hash(hasher)`, lines 2801–2803; `impl Hash for str` calls `state.write_str(self)`,
`core/src/hash/mod.rs` lines 863–867, whose default is `self.write(s.as_bytes());
self.write_u8(0xff)`, lines 550–553). For `DefaultHasher` the same bytes are written:
`DefaultHasher::write_str` forwards to `SipHasher13::write_str` (`std/src/hash/random.rs`
lines 135–137, `core/src/hash/sip.rs` lines 237–239), which reaches the override
of `Hasher<S>::write_str`, `core/src/hash/sip.rs` lines 303–308: `self.write(s.as_bytes());
self.write_u8(0xFF)`; `write_u8` is not overridden there (the note at line 248), so it is the
default `self.write(&[i])` (`core/src/hash/mod.rs` lines 362–364). The `Hasher` instance of
the Aeneas library has only `write` and `finish`, so `write_u8(0xff)` is the `write` of the
one-byte slice. -/
@[rust_fun "alloc::string::{core::hash::Hash<alloc::string::String>}::hash"]
def alloc.string.String.Insts.CoreHashHash.hash {H : Type}
    (corehashHasherInst : core.hash.Hasher H) (self : String) (state : H) : Result H := do
  let bytes ← alloc.string.String.as_bytes self
  let state ← corehashHasherInst.write state bytes
  corehashHasherInst.write state (Std.Slice.from [ExtModel.byte 255] (by scalar_tac))

set_option linter.dupNamespace false in
/-- [zeroize::{impl zeroize::Zeroize for Z}::zeroize]:
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/zeroize-1.9.2/src/lib.rs', lines 282:4-282:25
    Name pattern: [zeroize::{zeroize::Zeroize<@Z>}::zeroize]
    Visibility: public

**Model:** `Z::default()` (`volatile_write(self, Z::default())`, lines 282–284; the volatile
write is not modelled, only its value). -/
@[rust_fun "zeroize::{zeroize::Zeroize<@Z>}::zeroize"]
def zeroize.Zeroize.Blanket.zeroize {Z : Type}
    (DefaultIsZeroesInst : zeroize.DefaultIsZeroes Z) (_self : Z) : Result Z :=
  DefaultIsZeroesInst.coredefaultDefaultInst.default

/-- [zeroize::{impl zeroize::Zeroize for alloc::vec::Vec<Z>}::zeroize]:
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/zeroize-1.9.2/src/lib.rs', lines 505:4-505:25
    Name pattern: [zeroize::{zeroize::Zeroize<alloc::vec::Vec<@Z>>}::zeroize]
    Visibility: public

**Model:** zeroizes every element through the element instance (failures propagate) and then
clears the vector, so the result is empty (lines 505–516: spare capacity, which the value
model does not have, then `iter_mut().zeroize()`, then `clear()`). -/
@[rust_fun "zeroize::{zeroize::Zeroize<alloc::vec::Vec<@Z>>}::zeroize"]
def alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize {Z : Type} (ZeroizeInst : zeroize.Zeroize Z)
    (self : alloc.vec.Vec Z) : Result (alloc.vec.Vec Z) := do
  let _ ← self.val.mapM ZeroizeInst.zeroize
  ok (alloc.vec.Vec.new Z)

/-- [zeroize::{zeroize::Zeroizing<Z>}::new]:
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/zeroize-1.9.2/src/lib.rs', lines 599:4-599:32
    Name pattern: [zeroize::{zeroize::Zeroizing<@Z>}::new]
    Visibility: public

**Model:** wraps the value (`Self(value)`, lines 599–601). -/
@[rust_fun "zeroize::{zeroize::Zeroizing<@Z>}::new"]
def zeroize.Zeroizing.new {Z : Type} (_ZeroizeInst : zeroize.Zeroize Z) (value : Z) :
    Result (zeroize.Zeroizing Z) :=
  ok { inner := value }

/-- [zeroize::{impl core::clone::Clone for zeroize::Zeroizing<Z>}::clone]:
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/zeroize-1.9.2/src/lib.rs', lines 606:4-606:27
    Name pattern: [zeroize::{core::clone::Clone<zeroize::Zeroizing<@Z>>}::clone]
    Visibility: public

**Model:** wraps a clone of the value (`Self(self.0.clone())`, lines 606–608). -/
@[rust_fun "zeroize::{core::clone::Clone<zeroize::Zeroizing<@Z>>}::clone"]
def zeroize.Zeroizing.Insts.CoreCloneClone.clone {Z : Type} (_ZeroizeInst : zeroize.Zeroize Z)
    (corecloneCloneInst : core.clone.Clone Z) (self : zeroize.Zeroizing Z) :
    Result (zeroize.Zeroizing Z) := do
  let v ← corecloneCloneInst.clone self.inner
  ok { inner := v }

/-- [zeroize::{impl core::ops::deref::Deref<Z> for zeroize::Zeroizing<Z>}::deref]:
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/zeroize-1.9.2/src/lib.rs', lines 634:4-634:25
    Name pattern: [zeroize::{core::ops::deref::Deref<zeroize::Zeroizing<@Z>, @Z>}::deref]
    Visibility: public

**Model:** the wrapped value (`&self.0`, lines 634–636). -/
@[rust_fun
  "zeroize::{core::ops::deref::Deref<zeroize::Zeroizing<@Z>, @Z>}::deref"]
def zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref {Z : Type}
    (_ZeroizeInst : zeroize.Zeroize Z) (self : zeroize.Zeroizing Z) : Result Z :=
  ok self.inner

/-! ## Clock -/

/-- [rmcp::model::request_state::{rmcp::model::request_state::RequestStateCodec}::now_ms]:
    Source: 'crates/rmcp/src/model/request_state.rs', lines 733:4-735:5

**Model:** `ok nowMs`, an opaque value (`chrono::Utc::now().timestamp_millis()`).
Environmental assumption (stated exception, not modelled): `Utc::now` panics if the system
clock is before 1970 or outside chrono's range (`chrono-0.4.45/src/offset/utc.rs` lines 96–98:
`duration_since(UNIX_EPOCH).expect("system time before Unix epoch")` and
`DateTime::from_timestamp(..).unwrap()`); the model assumes a clock within that range. Called
by the translated wrappers `open` and `open_with` (hence, since translation patch 03,
`open_json` and `open_json_with`) and, since translation patch 03, `seal_with` (hence `seal`).
Because `nowMs` is one constant, those wrappers are pure in the model; no spec statement may
mention the functions `rmcp.model.request_state.RequestStateCodec.now_ms`,
`…RequestStateCodec.open`, `…RequestStateCodec.open_with`, `…RequestStateCodec.open_json`,
`…RequestStateCodec.open_json_with`, `…RequestStateCodec.seal` or
`…RequestStateCodec.seal_with` (a variable named `now_ms`, such as the time parameter of E01
`open_authenticated_body`, is not covered), except as stated at `ExtModel.nowMs` (the spec
theorems of `open`/`open_with`, `open_json`/`open_json_with` and `seal`/`seal_with`, their
restatements and the listed `_of_length_le` corollaries; human decisions 2026-11-24, extended
2026-11-25), and the model's own spec theorem `now_ms_spec` (`result = nowMs`; human decision
2026-11-25). -/
def model.request_state.RequestStateCodec.now_ms : Result Std.I64 :=
  ok ExtModel.nowMs

/-! ## Phase 2: strings and `Arc`

Plan steps S26/S27 replaced the 26 placeholders of plan step S21 by the models of this and the
following sections (plan Section 18). -/

/-- [core::str::traits::{impl core::cmp::PartialEq<str> for str}::eq]:
    Source: '/rustc/library/core/src/str/traits.rs', lines 29:4-29:37
    Name pattern: [core::str::traits::{core::cmp::PartialEq<str, str>}::eq]
    Visibility: public

**Model:** byte-list equality (`self.as_bytes() == other.as_bytes()`, lines 29–31; slice
equality of `u8`: equal lengths and equal bytes, `core/src/slice/cmp.rs` lines 14–29), for every
`Str`. -/
@[rust_fun "core::str::traits::{core::cmp::PartialEq<str, str>}::eq"]
def Str.Insts.CoreCmpPartialEqStr.eq (self : Str) (other : Str) : Result Bool :=
  ok (decide (self.val = other.val))

/-- [alloc::string::{impl core::ops::deref::Deref<str> for alloc::string::String}::deref]:
    Source: '/rustc/library/alloc/src/string.rs', lines 2896:4-2896:27
    Name pattern: [alloc::string::{core::ops::deref::Deref<alloc::string::String, str>}::deref]
    Visibility: public

**Model:** the UTF-8 bytes of the string, the identity on bytes (`self.as_str()`, lines
2835–2837; `String::as_str` is `str::from_utf8_unchecked(self.vec.as_slice())`), defined as the
model of `String::as_bytes`, which returns the same bytes: `fail maximumSizeExceeded` only for a
Lean `String` longer than `Usize.max` bytes, which no Rust `String` is. -/
@[rust_fun
  "alloc::string::{core::ops::deref::Deref<alloc::string::String, str>}::deref"]
def alloc.string.String.Insts.CoreOpsDerefDerefStr.deref (self : String) : Result Str :=
  alloc.string.String.as_bytes self

/-- [alloc::sync::{impl core::ops::deref::Deref<T> for alloc::sync::Arc<T>}::deref]:
    Source: '/rustc/library/alloc/src/sync.rs', lines 2570:4-2570:25
    Name pattern: [alloc::sync::{core::ops::deref::Deref<alloc::sync::Arc<@T>, @T>}::deref]
    Visibility: public

**Model:** the shared value, a projection (`&self.inner().data`, lines 2570–2572). The
allocator parameter `A` is not used. -/
@[rust_fun
  "alloc::sync::{core::ops::deref::Deref<alloc::sync::Arc<@T>, @T>}::deref"]
def alloc.sync.Arc.Insts.CoreOpsDerefDeref.deref {T : Type} (_A : Type)
    (self : alloc.sync.Arc T) : Result T :=
  ok self.data

/-- [alloc::sync::{impl core::cmp::PartialEq<alloc::sync::Arc<T>> for alloc::sync::Arc<T>}::eq]:
    Source: '/rustc/library/alloc/src/sync.rs', lines 3745:4-3745:43
    Name pattern: [alloc::sync::{core::cmp::PartialEq<alloc::sync::Arc<@T>, alloc::sync::Arc<@T>>}::eq]
    Visibility: public

**Model:** value equality, through the instance of `T` (its failure propagates): `**self ==
**other`, the generic `ArcEqIdent::eq` (lines 3745–3747, 3694–3698).
Stated exception: for `T: Eq` Rust specializes to `ptr::eq(self, other) || **self == **other`
(lines 3713–3717). The model has no pointers, so it always compares the values. The two agree
whenever the equality of `T` is reflexive and does not fail; `Eq` asks for reflexivity
(`core/src/cmp.rs` lines 295–304; `MarkerEq`, `alloc/src/rc.rs` lines 2727–2729), not for the
absence of failure. The only instance in the translation, `T = str`, is byte equality, which has
both. -/
@[rust_fun
  "alloc::sync::{core::cmp::PartialEq<alloc::sync::Arc<@T>, alloc::sync::Arc<@T>>}::eq"]
def alloc.sync.Arc.Insts.CoreCmpPartialEqArc.eq {T : Type} (_A : Type)
    (corecmpPartialEqInst : core.cmp.PartialEq T T) (self : alloc.sync.Arc T)
    (other : alloc.sync.Arc T) : Result Bool :=
  corecmpPartialEqInst.eq self.data other.data

/-! ## Phase 2: `Option`, `Result`, slices and ranges -/

/-- [core::option::{core::option::Option<T>}::or_else]:
    Source: '/rustc/library/core/src/option.rs', lines 1645:4-1650:28
    Name pattern: [core::option::{core::option::Option<@T>}::or_else]
    Visibility: public

**Model:** `Some x ↦ Some x`; `None ↦ f()`, calling the closure through its `FnOnce`
instance, whose failure propagates (lines 1645–1656). -/
@[rust_fun "core::option::{core::option::Option<@T>}::or_else"]
def core.option.Option.or_else {T : Type} {F : Type}
    (opsfunctionFnOnceFTupleOptionInst : core.ops.function.FnOnce F Unit (Option T))
    (self : Option T) (f : F) : Result (Option T) :=
  match self with
  | some x => ok (some x)
  | none => opsfunctionFnOnceFTupleOptionInst.call_once f ()

/-- [core::option::{impl core::cmp::PartialEq<core::option::Option<T>> for core::option::Option<T>}::eq]:
    Source: '/rustc/library/core/src/option.rs', lines 2441:4-2441:38
    Name pattern: [core::option::{core::cmp::PartialEq<core::option::Option<@T>, core::option::Option<@T>>}::eq]
    Visibility: public

**Model:** `(Some l, Some r) ↦ l == r` through the instance of `T` (its failure propagates);
`(None, None) ↦ true`; otherwise `false` (lines 2441–2450). -/
@[rust_fun
  "core::option::{core::cmp::PartialEq<core::option::Option<@T>, core::option::Option<@T>>}::eq"]
def core.option.Option.Insts.CoreCmpPartialEqOption.eq {T : Type}
    (cmpPartialEqInst : core.cmp.PartialEq T T) (self : Option T) (other : Option T) :
    Result Bool :=
  match self, other with
  | some l, some r => cmpPartialEqInst.eq l r
  | some _, none => ok false
  | none, some _ => ok false
  | none, none => ok true

/-- [core::result::{core::result::Result<T, E>}::ok]:
    Source: '/rustc/library/core/src/result.rs', lines 709:4-712:28
    Name pattern: [core::result::{core::result::Result<@T, @E>}::ok]
    Visibility: public

**Model:** `Ok x ↦ Some x`, `Err _ ↦ None` (lines 709–718). Inside its own namespace `ok`
names this definition, hence `Aeneas.Std.Result.ok` (module docstring, ordering note). -/
@[rust_fun "core::result::{core::result::Result<@T, @E>}::ok"]
def core.result.Result.ok {T : Type} {E : Type} (self : core.result.Result T E) :
    Result (Option T) :=
  match self with
  | core.result.Result.Ok x => Aeneas.Std.Result.ok (some x)
  | core.result.Result.Err _ => Aeneas.Std.Result.ok none

/-- [core::slice::{[T]}::first]:
    Source: '/rustc/library/core/src/slice/mod.rs', lines 157:4-157:43
    Name pattern: [core::slice::{[@T]}::first]
    Visibility: public

**Model:** the first element, `None` for the empty slice
(`if let [first, ..] = self { Some(first) } else { None }`, lines 157–159). -/
@[rust_fun "core::slice::{[@T]}::first"]
def core.slice.Slice.first {T : Type} (self : Slice T) : Result (Option T) :=
  match self.val with
  | first :: _ => ok (some first)
  | [] => ok none

/-- Slice equality for slices of equal length (`SlicePartialEq::equal_same_length`,
`core/src/slice/cmp.rs` lines 125–137): compares the elements left to right with `ne` of the
instance (`*lhs.add(idx) != *rhs.add(idx)`) and returns `false` at the first pair for which `ne`
holds, `true` at the end; a failure of `ne` propagates. Rust specializes the loop to a byte
comparison for `BytewiseEq` types (lines 143–157; such as `u8`, `u16`), whose `ne` is the
negation of byte equality and does not fail, so the result is the same. On lists of different
lengths it compares the common prefix; the callers below check the lengths first. -/
def ExtModel.sliceEqSameLength {T U : Type} (inst : core.cmp.PartialEq T U) :
    List T → List U → Result Bool
  | a :: l, b :: r => do
    let d ← inst.ne a b
    if d then ok false else ExtModel.sliceEqSameLength inst l r
  | _, _ => ok true

/-- Slice equality `[T] == [U]` (`impl PartialEq<[U]> for [T]`, `core/src/slice/cmp.rs` lines
14–29): `false` if the lengths differ, otherwise `ExtModel.sliceEqSameLength`. -/
def ExtModel.sliceEq {T U : Type} (inst : core.cmp.PartialEq T U) (l : List T) (r : List U) :
    Result Bool :=
  if l.length = r.length then ExtModel.sliceEqSameLength inst l r else ok false

/-- [core::slice::{[T]}::strip_suffix]:
    Source: '/rustc/library/core/src/slice/mod.rs', lines 2731:4-2733:21
    Name pattern: [core::slice::{[@T]}::strip_suffix]
    Visibility: public

**Model:** the Rust body transcribed (lines 2731–2745): take the suffix as a slice through the
`SlicePattern` instance; if `n = suffix.len() ≤ len = self.len()`, split `self` at `len - n`
(`core.slice.Slice.split_at` of the Aeneas library) and return `Some head` if the tail equals
the suffix (`ExtModel.sliceEq`, i.e. `tail == suffix`); otherwise `None`. Failures of
`as_slice` and of the element equality propagate; the subtraction and the split do not fail
since `n ≤ len`. -/
@[rust_fun "core::slice::{[@T]}::strip_suffix"]
def core.slice.Slice.strip_suffix {T : Type} {P : Type}
    (SlicePatternInst : core.slice.SlicePattern P T) (cmpPartialEqInst : core.cmp.PartialEq T T)
    (self : Slice T) (suffix : P) : Result (Option (Slice T)) := do
  let suffix ← SlicePatternInst.as_slice suffix
  let len := Slice.len self
  let n := Slice.len suffix
  if n ≤ len then
    let mid ← len - n
    let (head, tail) ← core.slice.Slice.split_at self mid
    let b ← ExtModel.sliceEq cmpPartialEqInst tail.val suffix.val
    if b then ok (some head) else ok none
  else ok none

/-- [core::array::equality::{impl core::cmp::PartialEq<[U; N]> for [T]}::eq]:
    Source: '/rustc/library/core/src/array/equality.rs', lines 48:4-48:40
    Name pattern: [core::array::equality::{core::cmp::PartialEq<[@T], [@U; @N]>}::eq]
    Visibility: public

**Model:** `false` unless the slice has length `N` (`self.as_array::<N>()` is `None`,
`core/src/slice/mod.rs` lines 855–865); otherwise array equality `[T; N] == [U; N]`
(lines 48–53, then lines 10–12 and `SpecArrayEq::spec_eq`, lines 143–145: `a[..] == b[..]`),
which is slice equality of two slices of length `N` (`ExtModel.sliceEqSameLength`). The
`BytewiseEq` specialization of `spec_eq` (lines 152–158) gives the same result, as for slices
(see `ExtModel.sliceEqSameLength`). -/
@[rust_fun "core::array::equality::{core::cmp::PartialEq<[@T], [@U; @N]>}::eq"]
def Slice.Insts.CoreCmpPartialEqArray.eq {T : Type} {U : Type} {N : Std.Usize}
    (cmpPartialEqInst : core.cmp.PartialEq T U) (self : Slice T) (other : Array U N) :
    Result Bool :=
  if self.val.length = N.val then ExtModel.sliceEqSameLength cmpPartialEqInst self.val other.val
  else ok false

/-- [core::slice::{impl core::slice::SlicePattern<T> for [T; N]}::as_slice]:
    Source: '/rustc/library/core/src/slice/mod.rs', lines 5696:4-5696:39
    Name pattern: [core::slice::{core::slice::SlicePattern<[@T; @N], @T>}::as_slice]
    Visibility: public

**Model:** the same elements as a slice (`self`, an unsizing coercion, lines 5696–5698;
`Array.to_slice` of the Aeneas library). -/
@[rust_fun "core::slice::{core::slice::SlicePattern<[@T; @N], @T>}::as_slice"]
def Array.Insts.CoreSliceSlicePattern.as_slice {T : Type} {N : Std.Usize} (self : Array T N) :
    Result (Slice T) :=
  ok (Aeneas.Std.Array.to_slice self)

/-- [core::ops::range::{core::ops::range::RangeInclusive<Idx>}::contains]:
    Source: '/rustc/library/core/src/ops/range.rs', lines 539:4-542:44
    Name pattern: [core::ops::range::{core::ops::range::RangeInclusive<@Idx>}::contains]
    Visibility: public

**Model:** `start <= item && item <= end`, or `start <= item && item < start` when the range is
exhausted, with `&&` short-circuiting and failures of the comparisons propagating. `contains`
calls `RangeBounds::contains` (lines 539–545), which is `(match start_bound { Included(s) => s
<= item, .. }) && (match end_bound { Included(e) => item <= e, Excluded(e) => item < e, .. })`
(lines 886–900); for `RangeInclusive` the start bound is `Included(start)` and the end bound is
`Excluded(start)` if `exhausted` ("bounds which are always empty: Included(start)..Excluded(start)"),
else `Included(end)` (lines 1142–1157). `start <= item` is `le` of the instance
`Idx: PartialOrd<U>`; `item <= end` and `item < start` are `le` and `lt` of `U: PartialOrd<Idx>`;
the instance `Idx: PartialOrd<Idx>` is not called. For an exhausted range the result is `false`
whenever the two instances are consistent (`start <= item` and `item < start` cannot both hold),
but the model still calls `lt`, as Rust does, so its failure propagates. Changed in the Aeneas
upgrade (human decision 2026-11-24; model reviewed 2026-11-24, re-signed 2026-11-24): up to `nightly-2026-06-01` the end
bound of an exhausted range was `Excluded(end)`. -/
@[rust_fun
  "core::ops::range::{core::ops::range::RangeInclusive<@Idx>}::contains"]
def core.ops.range.RangeInclusive.contains {Idx : Type} {U : Type}
    (_cmpPartialOrdInst : core.cmp.PartialOrd Idx Idx)
    (cmpPartialOrdInst1 : core.cmp.PartialOrd Idx U)
    (cmpPartialOrdInst2 : core.cmp.PartialOrd U Idx)
    (self : core.ops.range.RangeInclusive Idx) (item : U) : Result Bool := do
  let lower ← cmpPartialOrdInst1.le self.start item
  if lower then
    if self.exhausted then cmpPartialOrdInst2.lt item self.start
    else cmpPartialOrdInst2.le item self.«end»
  else ok false

/-! ## Phase 2: integer parsing -/

/-- The value of an ASCII decimal digit, `none` for every other byte: `(*c as char)
.to_digit(10)` (`core/src/char/methods.rs` lines 409–431, `to_digit`: `'0'`–`'9'` only for
radix 10; a byte cast to `char` is `U+0000`–`U+00FF`, so no other byte is a digit). -/
def ExtModel.decDigit? (c : Std.U8) : Option Nat :=
  if 48 ≤ c.val ∧ c.val ≤ 57 then some (c.val - 48) else none

/-- The digit loop of `i64::from_ascii_bytes_radix_impl` for radix 10 (`core/src/num/mod.rs` lines
1810–1862): from the accumulated value `acc`, read the digits left to right; a byte that is not
a digit is `InvalidDigit`; otherwise the next value is `acc * 10 + d` (positive) or
`acc * 10 - d` (negative), and a value outside `[-2^63, 2^63)` is `PosOverflow` (positive) or
`NegOverflow` (negative). This is the checked loop of the source (lines 1834–1860): at each
digit the digit is checked before the overflow of `checked_mul`, then `checked_add` or
`checked_sub` is checked, and for an accumulated value of the right sign the next value is out
of range exactly when the multiplication or the addition overflows. For at most 15 digits Rust
runs an unchecked loop instead (lines 1810–1833; `can_not_overflow`, lines 1575–1577:
`digits.len() <= 2 * 8 - 1`), whose values lie in range, so the checks above never fire there
either. -/
def ExtModel.i64DigitLoop (positive : Bool) (acc : Int) :
    List Std.U8 → Except ExtModel.IntErrorKind Int
  | [] => .ok acc
  | c :: rest =>
    match ExtModel.decDigit? c with
    | none => .error .InvalidDigit
    | some d =>
      let next : Int := if positive then acc * 10 + d else acc * 10 - d
      if -2 ^ 63 ≤ next ∧ next < 2 ^ 63 then ExtModel.i64DigitLoop positive next rest
      else .error (if positive then .PosOverflow else .NegOverflow)

/-- `i64::from_ascii_bytes_radix_impl(src, 10)` (`core/src/num/mod.rs` lines 1775–1863), as an integer or
an error kind: empty input is `Empty`; a single `+` or `-` is `InvalidDigit`; a leading `+` or
`-` is removed and sets the sign (the type is signed); then `ExtModel.i64DigitLoop` from `0`. -/
def ExtModel.i64FromAscii (src : List Std.U8) : Except ExtModel.IntErrorKind Int :=
  match src with
  | [] => .error .Empty
  | [c] =>
    if c.val = 43 ∨ c.val = 45 then .error .InvalidDigit
    else ExtModel.i64DigitLoop true 0 [c]
  | c :: rest =>
    if c.val = 43 then ExtModel.i64DigitLoop true 0 rest
    else if c.val = 45 then ExtModel.i64DigitLoop false 0 rest
    else ExtModel.i64DigitLoop true 0 (c :: rest)

/-- [core::num::{impl core::str::traits::FromStr<core::num::error::ParseIntError> for i64}::from_str]:
    Source: '/rustc/library/core/src/num/mod.rs', lines 1632:12-1632:68
    Name pattern: [core::num::{core::str::traits::FromStr<i64, core::num::error::ParseIntError>}::from_str]
    Visibility: public

**Model:** `Ok v` where `ExtModel.i64FromAscii` gives the integer `v`, `Err { kind }` where it
gives the error kind. Rust: `from_str(src) = i64::from_str_radix(src, 10)` (lines 1632–1634),
which is `i64::from_ascii_bytes_radix_impl(src.as_bytes(), 10)` (lines 1683–1685); radix 10 passes the
radix check, so this never panics. Grammar: an optional single `+` or `-`, then at least one
ASCII digit and nothing else; leading zeros are allowed; whitespace, `_` and non-ASCII digits
are `InvalidDigit`; error kinds as reported by Rust (`Empty`, `InvalidDigit`, `PosOverflow`,
`NegOverflow`; the first error met from the left wins, a non-digit before an overflow at the
same position). The model reads only the bytes, as Rust does, so it is defined on every `Str`.
The integer `v` lies in `[-2^63, 2^63)` (checked by the loop), so it is the value of the
`I64` built from it. -/
@[rust_fun
  "core::num::{core::str::traits::FromStr<i64, core::num::error::ParseIntError>}::from_str"]
def I64.Insts.CoreStrTraitsFromStrParseIntError.from_str (src : Str) :
    Result (core.result.Result Std.I64 core.num.error.ParseIntError) :=
  match ExtModel.i64FromAscii src.val with
  | .ok v => ok (core.result.Result.Ok ⟨BitVec.ofInt 64 v⟩)
  | .error kind => ok (core.result.Result.Err { kind })

/-- [core::str::{str}::parse]:
    Source: '/rustc/library/core/src/str/mod.rs', lines 2781:4-2781:56
    Name pattern: [core::str::{str}::parse]
    Visibility: public

**Model:** dispatches to the `FromStr` instance (`FromStr::from_str(self)`, lines 2781–2783);
its failure propagates. -/
@[rust_fun "core::str::{str}::parse"]
def core.str.Str.parse {F : Type} {Clause0_Err : Type}
    (traitsFromStrInst : core.str.traits.FromStr F Clause0_Err) (self : Str) :
    Result (core.result.Result F Clause0_Err) :=
  traitsFromStrInst.from_str self

/-! ## Phase 2: IP addresses

Transcribed from `library/core/src/net/ip_addr.rs` of the pinned toolchain. An `Ipv4Addr` is
its four octets and an `Ipv6Addr` its eight segments (`Rmcp.TypesExternal`); every function
below is total and never panics, like its Rust source. -/

/-- The number whose big-endian digits in base `b` are `l` (most significant first):
`u32::from_be_bytes` for four octets with `b = 256`, and `u128::from_be_bytes` of the sixteen
octets of an IPv6 address for its eight segments with `b = 65536`. -/
def ExtModel.beNat (b : Nat) (l : List Nat) : Nat :=
  l.foldl (fun acc d => acc * b + d) 0

/-- The octets of an IPv4 address as natural numbers, most significant first. -/
def ExtModel.ipv4Nats (a : core.net.ip_addr.Ipv4Addr) : List Nat :=
  a.addrOctets.val.map (fun o => o.val)

/-- The segments of an IPv6 address as natural numbers, most significant first. -/
def ExtModel.ipv6Nats (a : core.net.ip_addr.Ipv6Addr) : List Nat :=
  a.addrSegments.val.map (fun s => s.val)

/-- [core::net::ip_addr::{core::net::ip_addr::Ipv4Addr}::octets]:
    Source: '/rustc/library/core/src/net/ip_addr.rs', lines 697:4-697:41
    Name pattern: [core::net::ip_addr::{core::net::ip_addr::Ipv4Addr}::octets]
    Visibility: public

**Model:** the four octets (`self.octets`, lines 697–699). -/
@[rust_fun "core::net::ip_addr::{core::net::ip_addr::Ipv4Addr}::octets"]
def core.net.ip_addr.Ipv4Addr.octets (self : core.net.ip_addr.Ipv4Addr) :
    Result (Array Std.U8 4#usize) :=
  ok self.addrOctets

/-- [core::net::ip_addr::{core::net::ip_addr::Ipv4Addr}::is_unspecified]:
    Source: '/rustc/library/core/src/net/ip_addr.rs', lines 757:4-757:46
    Name pattern: [core::net::ip_addr::{core::net::ip_addr::Ipv4Addr}::is_unspecified]
    Visibility: public

**Model:** `u32::from_be_bytes(self.octets) == 0` (lines 757–759), i.e. `0.0.0.0`. -/
@[rust_fun
  "core::net::ip_addr::{core::net::ip_addr::Ipv4Addr}::is_unspecified"]
def core.net.ip_addr.Ipv4Addr.is_unspecified (self : core.net.ip_addr.Ipv4Addr) :
    Result Bool :=
  ok (decide (ExtModel.beNat 256 (ExtModel.ipv4Nats self) = 0))

/-- [core::net::ip_addr::{core::net::ip_addr::Ipv4Addr}::is_loopback]:
    Source: '/rustc/library/core/src/net/ip_addr.rs', lines 779:4-779:43
    Name pattern: [core::net::ip_addr::{core::net::ip_addr::Ipv4Addr}::is_loopback]
    Visibility: public

**Model:** `self.octets()[0] == 127` (lines 779–781), i.e. `127.0.0.0/8`. The index is in
bounds (four octets); the default of `getD` is never used. -/
@[rust_fun "core::net::ip_addr::{core::net::ip_addr::Ipv4Addr}::is_loopback"]
def core.net.ip_addr.Ipv4Addr.is_loopback (self : core.net.ip_addr.Ipv4Addr) : Result Bool :=
  ok (decide ((ExtModel.ipv4Nats self).getD 0 0 = 127))

/-- [core::net::ip_addr::{core::net::ip_addr::Ipv4Addr}::is_private]:
    Source: '/rustc/library/core/src/net/ip_addr.rs', lines 810:4-810:42
    Name pattern: [core::net::ip_addr::{core::net::ip_addr::Ipv4Addr}::is_private]
    Visibility: public

**Model:** the match of lines 810–817: `[10, ..]`, `[172, b, ..]` with `16 ≤ b ≤ 31`, and
`[192, 168, ..]` are private (`10.0.0.0/8`, `172.16.0.0/12`, `192.168.0.0/16`); everything else
is not. -/
@[rust_fun "core::net::ip_addr::{core::net::ip_addr::Ipv4Addr}::is_private"]
def core.net.ip_addr.Ipv4Addr.is_private (self : core.net.ip_addr.Ipv4Addr) : Result Bool :=
  match ExtModel.ipv4Nats self with
  | 10 :: _ => ok true
  | 172 :: b :: _ => ok (decide (b ≥ 16 ∧ b ≤ 31))
  | 192 :: 168 :: _ => ok true
  | _ => ok false

/-- [core::net::ip_addr::{core::net::ip_addr::Ipv4Addr}::is_link_local]:
    Source: '/rustc/library/core/src/net/ip_addr.rs', lines 838:4-838:45
    Name pattern: [core::net::ip_addr::{core::net::ip_addr::Ipv4Addr}::is_link_local]
    Visibility: public

**Model:** `matches!(self.octets(), [169, 254, ..])` (lines 838–840), i.e. `169.254.0.0/16`. -/
@[rust_fun "core::net::ip_addr::{core::net::ip_addr::Ipv4Addr}::is_link_local"]
def core.net.ip_addr.Ipv4Addr.is_link_local (self : core.net.ip_addr.Ipv4Addr) :
    Result Bool :=
  match ExtModel.ipv4Nats self with
  | 169 :: 254 :: _ => ok true
  | _ => ok false

/-- [core::net::ip_addr::{core::net::ip_addr::Ipv4Addr}::is_multicast]:
    Source: '/rustc/library/core/src/net/ip_addr.rs', lines 1039:4-1039:44
    Name pattern: [core::net::ip_addr::{core::net::ip_addr::Ipv4Addr}::is_multicast]
    Visibility: public

**Model:** `self.octets()[0] >= 224 && self.octets()[0] <= 239` (lines 1039–1041), i.e.
`224.0.0.0/4`. The default of `getD` is never used (four octets). -/
@[rust_fun "core::net::ip_addr::{core::net::ip_addr::Ipv4Addr}::is_multicast"]
def core.net.ip_addr.Ipv4Addr.is_multicast (self : core.net.ip_addr.Ipv4Addr) :
    Result Bool :=
  ok (decide ((ExtModel.ipv4Nats self).getD 0 0 ≥ 224 ∧
    (ExtModel.ipv4Nats self).getD 0 0 ≤ 239))

/-- [core::net::ip_addr::{core::net::ip_addr::Ipv4Addr}::is_broadcast]:
    Source: '/rustc/library/core/src/net/ip_addr.rs', lines 1061:4-1061:44
    Name pattern: [core::net::ip_addr::{core::net::ip_addr::Ipv4Addr}::is_broadcast]
    Visibility: public

**Model:** `u32::from_be_bytes(self.octets()) == u32::from_be_bytes(Self::BROADCAST.octets())`
(lines 1061–1063), with `BROADCAST = 255.255.255.255` (line 681). -/
@[rust_fun "core::net::ip_addr::{core::net::ip_addr::Ipv4Addr}::is_broadcast"]
def core.net.ip_addr.Ipv4Addr.is_broadcast (self : core.net.ip_addr.Ipv4Addr) :
    Result Bool :=
  ok (decide (ExtModel.beNat 256 (ExtModel.ipv4Nats self) =
    ExtModel.beNat 256 [255, 255, 255, 255]))

/-- [core::net::ip_addr::{impl core::convert::From<u32> for core::net::ip_addr::Ipv4Addr}::from]:
    Source: '/rustc/library/core/src/net/ip_addr.rs', lines 1318:4-1318:32
    Name pattern: [core::net::ip_addr::{core::convert::From<core::net::ip_addr::Ipv4Addr, u32>}::from]
    Visibility: public

**Model:** the big-endian bytes of `ip` as octets: `Ipv4Addr::from_bits(ip)` (lines 1318–1320),
which is `Ipv4Addr { octets: bits.to_be_bytes() }` (lines 637–639), so the first octet is
`ip / 2^24` and the last `ip mod 256` (`ExtModel.byte` takes the value modulo 256). -/
@[rust_fun
  "core::net::ip_addr::{core::convert::From<core::net::ip_addr::Ipv4Addr, u32>}::from"]
def core.net.ip_addr.Ipv4Addr.Insts.CoreConvertFromU32.from (ip : Std.U32) :
    Result core.net.ip_addr.Ipv4Addr :=
  ok { addrOctets := Std.Array.from [ExtModel.byte (ip.val / 2 ^ 24), ExtModel.byte (ip.val / 2 ^ 16),
                   ExtModel.byte (ip.val / 2 ^ 8), ExtModel.byte ip.val] (by simp) }

/-- [core::net::ip_addr::{core::net::ip_addr::Ipv6Addr}::segments]:
    Source: '/rustc/library/core/src/net/ip_addr.rs', lines 1525:4-1525:44
    Name pattern: [core::net::ip_addr::{core::net::ip_addr::Ipv6Addr}::segments]
    Visibility: public

**Model:** the eight segments, which the model stores (lines 1525–1540 compute them from the
sixteen octets as big-endian `u16` values; see `core.net.ip_addr.Ipv6Addr`). -/
@[rust_fun "core::net::ip_addr::{core::net::ip_addr::Ipv6Addr}::segments"]
def core.net.ip_addr.Ipv6Addr.segments (self : core.net.ip_addr.Ipv6Addr) :
    Result (Array Std.U16 8#usize) :=
  ok self.addrSegments

/-- [core::net::ip_addr::{core::net::ip_addr::Ipv6Addr}::is_unspecified]:
    Source: '/rustc/library/core/src/net/ip_addr.rs', lines 1588:4-1588:46
    Name pattern: [core::net::ip_addr::{core::net::ip_addr::Ipv6Addr}::is_unspecified]
    Visibility: public

**Model:** `u128::from_be_bytes(self.octets()) == u128::from_be_bytes(Ipv6Addr::UNSPECIFIED
.octets())` (lines 1588–1590), with `UNSPECIFIED = ::` (line 1509), i.e. all segments zero. The
`u128` of the octets is `ExtModel.beNat 65536` of the segments. -/
@[rust_fun
  "core::net::ip_addr::{core::net::ip_addr::Ipv6Addr}::is_unspecified"]
def core.net.ip_addr.Ipv6Addr.is_unspecified (self : core.net.ip_addr.Ipv6Addr) :
    Result Bool :=
  ok (decide (ExtModel.beNat 65536 (ExtModel.ipv6Nats self) =
    ExtModel.beNat 65536 [0, 0, 0, 0, 0, 0, 0, 0]))

/-- [core::net::ip_addr::{core::net::ip_addr::Ipv6Addr}::is_loopback]:
    Source: '/rustc/library/core/src/net/ip_addr.rs', lines 1612:4-1612:43
    Name pattern: [core::net::ip_addr::{core::net::ip_addr::Ipv6Addr}::is_loopback]
    Visibility: public

**Model:** `u128::from_be_bytes(self.octets()) == u128::from_be_bytes(Ipv6Addr::LOCALHOST
.octets())` (lines 1612–1614), with `LOCALHOST = ::1` (line 1492). -/
@[rust_fun "core::net::ip_addr::{core::net::ip_addr::Ipv6Addr}::is_loopback"]
def core.net.ip_addr.Ipv6Addr.is_loopback (self : core.net.ip_addr.Ipv6Addr) : Result Bool :=
  ok (decide (ExtModel.beNat 65536 (ExtModel.ipv6Nats self) =
    ExtModel.beNat 65536 [0, 0, 0, 0, 0, 0, 0, 1]))

/-- [core::net::ip_addr::{core::net::ip_addr::Ipv6Addr}::is_multicast]:
    Source: '/rustc/library/core/src/net/ip_addr.rs', lines 1972:4-1972:44
    Name pattern: [core::net::ip_addr::{core::net::ip_addr::Ipv6Addr}::is_multicast]
    Visibility: public

**Model:** `(self.segments()[0] & 0xff00) == 0xff00` (lines 1972–1974), i.e. `ff00::/8`. The
default of `getD` is never used (eight segments). -/
@[rust_fun "core::net::ip_addr::{core::net::ip_addr::Ipv6Addr}::is_multicast"]
def core.net.ip_addr.Ipv6Addr.is_multicast (self : core.net.ip_addr.Ipv6Addr) :
    Result Bool :=
  ok (decide ((self.addrSegments.val.getD 0 0#u16 &&& 0xff00#u16) = 0xff00#u16))

/-! ## Public `request_state.rs` API (R09–R15)

External functions reached by the public functions `seal`, `seal_with` (through the private
`seal_at`), `with_rs1_signing`, `with_rs1_fallback`, `open_json`, `open_json_with` and
`new_with_keyring` once their `exclude` entries are removed (translation patch 03). Every model
is a definition; the two values a model cannot compute are the `opaque` constants
`ExtModel.randomState` (the hash keys of a new map) and `ExtModel.serdeJsonFromSlice` (the
outcome of a user `Deserialize` impl), which add no axiom. -/

/-- [core::time::{core::time::Duration}::as_millis]:
    Source: '/rustc/library/core/src/time.rs', lines 601:4-601:41
    Name pattern: [core::time::{core::time::Duration}::as_millis]
    Visibility: public

**Model:** `secs * 1000 + nanos / 1_000_000` as a `u128` (`self.secs as u128 * MILLIS_PER_SEC
as u128 + (self.nanos.as_inner() / NANOS_PER_MILLI) as u128`, lines 601–604, with
`NANOS_PER_MILLI = 1_000_000` and `MILLIS_PER_SEC = 1_000`, lines 28 and 30). Exact: the value
is below `2^64 * 1000 + 1000 < 2^128`, so the `u128` arithmetic neither overflows nor panics and
`BitVec.ofNat 128` does not wrap. -/
@[rust_fun "core::time::{core::time::Duration}::as_millis"]
def core.time.Duration.as_millis (self : core.time.Duration) : Result Std.U128 :=
  ok ⟨BitVec.ofNat 128 (self.secs.val * 1000 + self.nanos.val / 1000000)⟩

/-- [alloc::str::{impl alloc::borrow::ToOwned<alloc::string::String> for str}::to_owned]:
    Source: '/rustc/library/alloc/src/str.rs', lines 252:4-252:32
    Name pattern: [alloc::str::{alloc::borrow::ToOwned<str, alloc::string::String>}::to_owned]
    Visibility: public

**Model:** the `String` with the same UTF-8 bytes
(`String::from_utf8_unchecked(self.as_bytes().to_owned())`, lines 252–255). `fail undef` if
the bytes are not UTF-8, which no Rust `&str` is (the `Str` convention above, as for
`String::push_str`). A Rust `&str` has at most `isize::MAX` bytes, so the copy never hits the
capacity-overflow panic (memory convention above). -/
@[rust_fun "alloc::str::{alloc::borrow::ToOwned<str, alloc::string::String>}::to_owned"]
def Str.Insts.AllocBorrowToOwnedString.to_owned (self : Str) : Result String :=
  match ExtModel.strOfBytes? self.val with
  | some s => ok s
  | none => fail undef

/-- [std::collections::hash::map::{std::collections::hash::map::HashMap<K, V, S, A>}::contains_key]:
    Source: '/rustc/library/std/src/collections/hash/map.rs', lines 1268:4-1271:21
    Name pattern: [std::collections::hash::map::{std::collections::hash::map::HashMap<@K, @V, @S, @A>}::contains_key]
    Visibility: public

**Model:** `true` exactly when some entry's key `key` satisfies `k == key.borrow()`, i.e. when
`ExtModel.HashMap.find` (the lookup of the `get` model) returns `some`. The Rust function is
`self.base.contains_key(k)` (lines 1268–1274), i.e. hashbrown 0.17.1 `HashMap::contains_key`
(`src/map.rs` lines 1382–1392): `false` on an empty table, otherwise
`self.table.get(hash, equivalent_key(k)).is_some()`, the same hash and `Equivalent` probe as
`get`. Hashing is not modelled, for the reason given at `std.collections.hash.map.HashMap.get`:
faithful for `Hash`/`Eq` instances that agree and do not fail. The instances in the translation
are `K = String` with `Q = str` (`with_rs1_signing`, `with_rs1_fallback`) and with `Q = String`
(`new_with_keyring`); `String` and `str` equality are byte equality, `Hash for String` hashes the
bytes as `Hash for str` does (`(**self).hash(hasher)`), and `Borrow<str> for String` returns the
same bytes, so they agree, and none fails. Unlike `get`, the result does not depend on which of
several equal keys is found, so it is exact also for a map with duplicate keys. -/
@[rust_fun
  "std::collections::hash::map::{std::collections::hash::map::HashMap<@K, @V, @S, @A>}::contains_key"]
def std.collections.hash.map.HashMap.contains_key
    {K : Type} {V : Type} {S : Type} {A : Type} {Q : Type} {Clause2_Hasher : Type}
    (_corecmpEqInst : core.cmp.Eq K) (_corehashHashInst : core.hash.Hash K)
    (_corehashBuildHasherInst : core.hash.BuildHasher S Clause2_Hasher)
    (coreborrowBorrowInst : core.borrow.Borrow K Q) (_corehashHashInst1 : core.hash.Hash Q)
    (corecmpEqInst1 : core.cmp.Eq Q)
    (self : std.collections.hash.map.HashMap K V S A) (k : Q) : Result Bool := do
  let r ← ExtModel.HashMap.find coreborrowBorrowInst corecmpEqInst1 k self.entries
  ok r.isSome

/-- [std::collections::hash::map::{std::collections::hash::map::HashMap<K, V, S, A>}::is_empty]:
    Source: '/rustc/library/std/src/collections/hash/map.rs', lines 745:4-745:34
    Name pattern: [std::collections::hash::map::{std::collections::hash::map::HashMap<@K, @V, @S, @A>}::is_empty]
    Visibility: public

**Model:** `true` exactly when the map has no entry (`self.base.is_empty()`, lines 745–747;
hashbrown 0.17.1 `self.len() == 0`, `src/map.rs` lines 824–826). Exact also for an entry list
with duplicate keys (emptiness does not depend on duplicates). -/
@[rust_fun
  "std::collections::hash::map::{std::collections::hash::map::HashMap<@K, @V, @S, @A>}::is_empty"]
def std.collections.hash.map.HashMap.is_empty {K : Type} {V : Type} {S : Type} {A : Type}
    (self : std.collections.hash.map.HashMap K V S A) : Result Bool :=
  ok self.entries.isEmpty

/-- **Hash keys of a new map** (opaque): the `RandomState` that `HashMap::new` stores. Rust
takes it from a per-thread pair of random keys, read once from the operating system, whose
first key is incremented on every `RandomState::new` (`std/src/hash/random.rs` lines 55–76), so
two maps built on the same thread get different keys (maps on different threads get independent
random keys). One constant cannot model that, and nothing in the value model
depends on the keys (no model hashes for a lookup; `std.collections.hash.map.HashMap.get`).
Review rule: no statement has a premise or conclusion about the value of `randomState` or about
the `hash_builder` of a map built by `HashMap::new`; and no statement states or relies on the
equality (or inequality) of two maps, or of two codecs containing them, built by distinct
`HashMap::new` calls (for example two results of `new_with_keyring`): in the model they share
`randomState`, in Rust their `RandomState` keys differ on the same thread and are independent random keys
otherwise (`std/src/hash/random.rs` lines 71–75).
The `hash_builder` is unobservable through the modelled API. -/
opaque ExtModel.randomState : std.hash.random.RandomState :=
  { k0 := 0#u64, k1 := 0#u64 }

/-- [std::collections::hash::map::{std::collections::hash::map::HashMap<K, V, std::hash::random::RandomState, alloc::alloc::Global>}::new]:
    Source: '/rustc/library/std/src/collections/hash/map.rs', lines 269:4-269:46
    Name pattern: [std::collections::hash::map::{std::collections::hash::map::HashMap<@K, @V, std::hash::random::RandomState, alloc::alloc::Global>}::new]
    Visibility: public

**Model:** the empty map with hash builder `ExtModel.randomState` and the `Global` allocator
(`Default::default()`, lines 269–271, i.e. `HashMap::with_hasher(RandomState::new())`, lines
1488–1497; `RandomState::new`, `std/src/hash/random.rs` lines 55–76). Stated exception: the
keys of the `RandomState` are random in Rust and an unknown constant here (see
`ExtModel.randomState`). Not modelled: `hashmap_random_keys` panics if the operating system's
random source fails (`std/src/sys/random/linux.rs` lines 166–172, `getrandom`), an
environmental assumption like the clock's. -/
@[rust_fun
  "std::collections::hash::map::{std::collections::hash::map::HashMap<@K, @V, std::hash::random::RandomState, alloc::alloc::Global>}::new"]
def std.collections.hash.map.HashMapKVRandomStateGlobal.new (K : Type) (V : Type) :
    Result (std.collections.hash.map.HashMap K V std.hash.random.RandomState
      alloc.alloc.Global) :=
  ok { hash_builder := ExtModel.randomState, alloc := alloc.alloc.Global.mk, entries := [] }

/-- The first entry of `entries` whose key is equal to `key` as `rustc_entry` compares
(`stored.eq(&key)` through the `Eq` instance of `K`; its failures propagate). -/
def ExtModel.HashMap.lookupEntry {K V : Type} (corecmpEqInst : core.cmp.Eq K) (key : K) :
    List (K × V) → Result (Option (K × V))
  | [] => ok none
  | (k, v) :: rest => do
    let b ← corecmpEqInst.partialEqInst.eq k key
    if b then ok (some (k, v)) else ExtModel.HashMap.lookupEntry corecmpEqInst key rest

/-- [std::collections::hash::map::{std::collections::hash::map::HashMap<K, V, S, A>}::entry]:
    Source: '/rustc/library/std/src/collections/hash/map.rs', lines 1012:4-1012:57
    Name pattern: [std::collections::hash::map::{std::collections::hash::map::HashMap<@K, @V, @S, @A>}::entry]
    Visibility: public

**Model:** if an entry with a key equal to `key` exists (`ExtModel.HashMap.lookupEntry`), an
`Occupied` entry with that slot's key and value, and a backward function that returns the map
unchanged; otherwise a `Vacant` entry for `key` with nothing inserted, and a backward function
that adds `(key, v)` to the map if the final entry holds an inserted value `v`, and otherwise
returns the map unchanged. The Rust function is `map_entry(self.base.rustc_entry(key))` (lines
1012–1014), i.e. hashbrown 0.17.1 `rustc_entry` (`src/rustc_entry.rs` lines 35–54): it hashes
`key`, probes for a slot whose key satisfies `q.0.eq(&key)`, and returns `Occupied` (the passed
`key` is dropped) or, after `self.reserve(1)`, `Vacant` with the hash and the key. Hashing is
not modelled, for the reason given at `std.collections.hash.map.HashMap.get` (faithful for
`Hash`/`Eq` instances that agree and do not fail; the only instance is `K = String`). The
backward function of an `Occupied` entry ignores the final entry: no translated function and no
model changes an occupied entry. Not modelled: the allocation of `reserve(1)` (memory
convention above; its capacity-overflow panic needs more than `isize::MAX` bytes of
entries). -/
@[rust_fun
  "std::collections::hash::map::{std::collections::hash::map::HashMap<@K, @V, @S, @A>}::entry"]
def std.collections.hash.map.HashMap.entry
    {K : Type} {V : Type} {S : Type} {A : Type} {Clause2_Hasher : Type}
    (corecmpEqInst : core.cmp.Eq K) (_corehashHashInst : core.hash.Hash K)
    (_corehashBuildHasherInst : core.hash.BuildHasher S Clause2_Hasher)
    (self : std.collections.hash.map.HashMap K V S A) (key : K) :
    Result ((std.collections.hash.map.Entry K V A) ×
      (std.collections.hash.map.Entry K V A → std.collections.hash.map.HashMap K V S A)) := do
  let found ← ExtModel.HashMap.lookupEntry corecmpEqInst key self.entries
  match found with
  | some (k, v) =>
    ok (std.collections.hash.map.Entry.Occupied { key := k, value := v }, fun _ => self)
  | none =>
    ok (std.collections.hash.map.Entry.Vacant { key := key, inserted := none },
      fun e => match e with
        | std.collections.hash.map.Entry.Vacant { key := k, inserted := some v } =>
          { self with entries := self.entries ++ [(k, v)] }
        | _ => self)

/-- [std::collections::hash::map::{std::collections::hash::map::VacantEntry<'a, K, V, A>}::insert]:
    Source: '/rustc/library/std/src/collections/hash/map.rs', lines 2975:4-2975:46
    Name pattern: [std::collections::hash::map::{std::collections::hash::map::VacantEntry<'a, @K, @V, @A>}::insert]
    Visibility: public

**Model:** returns `value` (the new slot, as the `&'a mut V` that Rust returns), with a
backward function that records the final value `v` of that reference as the entry's inserted
value. The Rust function is `self.base.insert(value)` (lines 2975–2977), i.e. hashbrown 0.17.1
`RustcVacantEntry::insert` (`src/rustc_entry.rs` lines 574–579): `insert_no_grow` of
`(self.key, value)` at the hash, into capacity that `rustc_entry` reserved, then a reference to
the value; it does not fail. The map is updated by the backward function of
`std.collections.hash.map.HashMap.entry`. -/
@[rust_fun
  "std::collections::hash::map::{std::collections::hash::map::VacantEntry<'a, @K, @V, @A>}::insert"]
def std.collections.hash.map.VacantEntry.insert {K : Type} {V : Type} {A : Type}
    (self : std.collections.hash.map.VacantEntry K V A) (value : V) :
    Result (V × (V → std.collections.hash.map.VacantEntry K V A)) :=
  ok (value, fun v => { self with inserted := some v })

/-- **Outcome of `serde_json::from_slice`** (opaque): `serdeJsonFromSlice inst v` is what
`serde_json::from_slice::<T>(v)` returns for the `Deserialize` instance `inst` of `T`: `Ok` of
the value it builds or `Err` of a `serde_json` error. Opaque because it depends on the
`Deserialize` impl of the caller's type `T` (arbitrary code, derived or hand-written) and on the
whole `serde_json` parser, neither of which is translated (plan Section 4: the crate's
correctness is out of scope). A statement can only say that the result of `open_json_with` is
this outcome, for the opened payload, mapped as the Rust code maps it. The model is a function
of `inst` and the bytes, so it assumes a deterministic `Deserialize` impl without side effects;
stated exception: an impl that is non-deterministic or has side effects (global or thread-local
state, a random number generator). Review rule (as for two clock readings): no statement relates
two calls of `open_json`/`open_json_with` (or of `serde_json::from_slice`), for example by
equating their results. -/
noncomputable opaque ExtModel.serdeJsonFromSlice {T : Type} (inst : serde_core.de.Deserialize T)
    (v : List Std.U8) : core.result.Result T serde_json.error.Error :=
  core.result.Result.Err (Classical.choice inferInstance)

/-- [serde_json::de::from_slice]:
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/serde_json-1.0.154/src/de.rs', lines 2667:0-2669:27
    Name pattern: [serde_json::de::from_slice]
    Visibility: public

**Model:** `ok (serdeJsonFromSlice inst v)`, an opaque outcome (`from_trait(read::SliceRead::new
(v))`, lines 2667–2672: `T::deserialize` on a slice deserializer, then `Deserializer::end`,
which rejects trailing non-whitespace). Stated exceptions: the model claims that the call
returns; a `Deserialize` impl of the caller's type that panics, aborts or does not terminate is
not modelled (derived impls and `serde_json`'s own code return an `Err` instead of panicking;
its recursion limit of 128 nested levels turns deep input into `Err`, `de.rs`
`check_recursion!`); nor is one that is non-deterministic or has side effects (global or
thread-local state, a random number generator), since the model returns the same outcome for
the same instance and bytes. Review rule (as for two clock readings): no statement relates two
calls of `from_slice` (or of `open_json`/`open_json_with`). -/
@[rust_fun "serde_json::de::from_slice"]
noncomputable def serde_json.de.from_slice {T : Type} (serde_coredeDeserializeInst : serde_core.de.Deserialize T)
    (v : Slice Std.U8) : Result (core.result.Result T serde_json.error.Error) :=
  ok (ExtModel.serdeJsonFromSlice serde_coredeDeserializeInst v.val)

/-- [core::error::Error::source]:
    Source: '/rustc/library/core/src/error.rs', lines 111:4-111:54
    Name pattern: [core::error::Error::source]
    Visibility: public

**Model:** `None`, the body of the default method (lines 111–113). Declared by the Aeneas
template because the `serde_core` error traits (opaque crate) have `core::error::Error` as a
supertrait; no generated definition calls it. -/
@[rust_fun "core::error::Error::source"]
def core.error.Error.source.default {Self : Type} (_ErrorInst : core.error.Error Self)
    (_self : Self) : Result (Option (Dyn (fun _dyn => core.error.Error _dyn))) :=
  ok none

/-- [core::hash::impls::{impl core::hash::Hash for str}::hash]:
    Source: '/rustc/library/core/src/hash/mod.rs', lines 865:8-865:48
    Name pattern: [core::hash::impls::{core::hash::Hash<str>}::hash]
    Visibility: public

**Model:** writes the bytes, then the byte `0xff`, through the hasher instance
(`state.write_str(self)`, lines 865–867; the default `Hasher::write_str` is `self.write(s.as_bytes());
self.write_u8(0xff)`, and `DefaultHasher` writes the same bytes, as stated at
`alloc.string.String.Insts.CoreHashHash.hash`, which is the same function on the `String`'s
bytes). Defined for every `Str`. No model hashes for a lookup; the instance is required by the
signatures of `HashMap::contains_key` with `Q = str`. -/
@[rust_fun "core::hash::impls::{core::hash::Hash<str>}::hash"]
def Str.Insts.CoreHashHash.hash {H : Type} (HasherInst : core.hash.Hasher H) (self : Str)
    (state : H) : Result H := do
  let state ← HasherInst.write state self
  HasherInst.write state (Std.Slice.from [ExtModel.byte 255] (by scalar_tac))

/-- [alloc::str::{impl core::borrow::Borrow<str> for alloc::string::String}::borrow]:
    Source: '/rustc/library/alloc/src/str.rs', lines 233:4-233:28
    Name pattern: [alloc::str::{core::borrow::Borrow<alloc::string::String, str>}::borrow]
    Visibility: public

**Model:** the UTF-8 bytes of the string (`&self[..]`, lines 233–235: the full-range index of
`String`, which is `self.as_str()`), defined as the model of `String`'s `Deref<str>`, which
returns the same bytes: `fail maximumSizeExceeded` only for a Lean `String` longer than
`Usize.max` bytes, which no Rust `String` is. -/
@[rust_fun "alloc::str::{core::borrow::Borrow<alloc::string::String, str>}::borrow"]
def alloc.string.String.Insts.CoreBorrowBorrowStr.borrow (self : String) : Result Str :=
  alloc.string.String.Insts.CoreOpsDerefDerefStr.deref self

/-- [alloc::string::{impl core::cmp::PartialEq<str> for alloc::string::String}::eq]:
    Source: '/rustc/library/alloc/src/string.rs', lines 2740:12-2740:46
    Name pattern: [alloc::string::{core::cmp::PartialEq<alloc::string::String, str>}::eq]
    Visibility: public

**Model:** byte equality of the string's UTF-8 bytes and `other`
(`PartialEq::eq(&self[..], &other[..])`, lines 2740–2742, generated by `impl_eq! { String,
str }`, line 2763: `str` equality of the two byte sequences), for every `Str`. -/
@[rust_fun "alloc::string::{core::cmp::PartialEq<alloc::string::String, str>}::eq"]
def alloc.string.String.Insts.CoreCmpPartialEqStr.eq (self : String) (other : Str) :
    Result Bool :=
  ok (decide (ExtModel.utf8 self = other.val))

/-- The model of `slice::Iter::any`: given the list of remaining elements, call the closure on each in
order and stop at the first `true`. Returns the result and the number of elements consumed. -/
def ExtModel.sliceIterAny {T F : Type} (inst : core.ops.function.FnMut F T Bool) :
    List T → F → Result (Bool × Nat)
  | [], _ => ok (false, 0)
  | x :: rest, f => do
    let (b, f) ← inst.call_mut f x
    if b then ok (true, 1)
    else do
      let (r, n) ← ExtModel.sliceIterAny inst rest f
      ok (r, n + 1)

/-- [core::slice::iter::{impl core::iter::traits::iterator::Iterator<&'a T> for core::slice::iter::Iter<'a, T>}::any]:
    Source: '/rustc/library/core/src/slice/iter/macros.rs', lines 321:12-324:45
    Name pattern: [core::slice::iter::{core::iter::traits::iterator::Iterator<core::slice::iter::Iter<'a, @T>, &'a @T>}::any]
    Visibility: public

**Model:** calls the closure (through its `FnMut` instance, whose failures propagate) on the
remaining elements in order, stops at the first `true`, and returns whether one was found and
the iterator advanced past every element it consumed. The Rust function is the slice override
of `Iterator::any` (lines 321–332, instantiated for `Iter` by `iterator!`,
`core/src/slice/iter.rs` lines 140–148): `while let Some(x) = self.next() { if f(x) { return
true; } } false`. The remaining elements of the Aeneas `Iter` are `slice[i..]`
(`Aeneas.Std.core.slice.iter.IteratorSliceIter.next`). -/
@[rust_fun
  "core::slice::iter::{core::iter::traits::iterator::Iterator<core::slice::iter::Iter<'a, @T>, &'a @T>}::any"]
def core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.any {T : Type} {F : Type}
    (opsfunctionFnMutFTupleSharedATBoolInst : core.ops.function.FnMut F T Bool)
    (self : core.slice.iter.Iter T) (f : F) : Result (Bool × (core.slice.iter.Iter T)) := do
  let (b, n) ← ExtModel.sliceIterAny opsfunctionFnMutFTupleSharedATBoolInst
    (self.slice.val.drop self.i) f
  ok (b, { self with i := self.i + n })

/-- [core::iter::traits::iterator::Iterator::any]:
    Source: '/rustc/library/core/src/iter/traits/iterator.rs', lines 2897:4-2900:37
    Name pattern: [core::iter::traits::iterator::Iterator::any]
    Visibility: public

**Model:** calls `next` and the closure alternately until the closure returns `true` (result
`true`) or `next` returns `None` (result `false`), through the `loop` combinator of the Aeneas
library, which is `div` if this never happens. The Rust default method is
`self.try_fold((), check(f)) == ControlFlow::Break(())` (lines 2897–2910), and the default
`try_fold` is that `next` loop. Stated exception: an iterator that overrides `try_fold` is
modelled by the loop. Declared by the Aeneas template; no generated definition calls it (the
translated code calls the slice override above). -/
@[rust_fun "core::iter::traits::iterator::Iterator::any"]
def core.iter.traits.iterator.Iterator.any.default {Self : Type} {F : Type} {Clause0_Item : Type}
    (IteratorInst : core.iter.traits.iterator.Iterator Self Clause0_Item)
    (opsfunctionFnMutFTupleClause0_ItemBoolInst :
      core.ops.function.FnMut F Clause0_Item Bool)
    (self : Self) (f : F) : Result (Bool × Self) :=
  loop (fun (st : Self × F) => do
      let (o, it) ← IteratorInst.next st.1
      match o with
      | none => ok (ControlFlow.done (false, it))
      | some x => do
        let (b, f) ← opsfunctionFnMutFTupleClause0_ItemBoolInst.call_mut st.2 x
        if b then ok (ControlFlow.done (true, it)) else ok (ControlFlow.cont (it, f)))
    (self, f)

/-! ## Public `skill.rs` API (K01–K20, translation patch 04)

External functions reached by the twenty public functions of `crates/rmcp/src/model/skill.rs`
(human decisions 2026-11-25). Translation patch 04 adds the private module `skill::prim`, whose
twelve one-line wrappers (`Source:` lines refer to the patched copy, patch 04 on top of patches
01–03) are opaque in the translation and modelled here, and makes the remaining code use only
standard-library functions whose models follow. Every model is a definition; the three values a
model cannot compute are the `opaque` constants `ExtModel.sha256` (SHA-256, FIPS 180-4),
`ExtModel.nfkc` (Unicode normalization form NFKC) and `ExtModel.generalCategory` (the Unicode
General_Category property), which add no axiom. Their laws are not stated here: a statement that
needs one takes it as a hypothesis (human decision 2026-11-25). Every other model is exact and
computable by structural recursion, so it can be evaluated on small inputs (examples in
`Proofs.External.Skill`).

Crates cited (pinned in `scripts/aeneas-translate.sh`, `PINNED_DEPS`): `sha2 0.11.2`,
`percent-encoding 2.3.2`, `unicode-normalization 0.1.26`, `unicode-general-category 1.1.0`,
`serde_json 1.0.154`; std's `hashbrown 0.17.1` as for `HashMap`. -/

namespace ExtModel

/-- **SHA-256 reference function** (opaque): `sha256 msg` is the 32-byte SHA-256 digest of
`msg` (FIPS 180-4). Opaque because its value is not modelled (plan Section 4; the correctness of
the `sha2` crate is not established), as for `ExtModel.hmacSha256`. The value given here only
shows that the type is inhabited; an `opaque` constant does not unfold to it. Compiled
evaluation (the compiled code of any definition that reaches it, run by Lean's evaluation
command or an executable) returns this placeholder, 32 zero bytes, not the SHA-256 digest, so
evaluating anything that reaches `sha256`, or comparing it differentially with Rust, is
meaningless (lead decision 2026-11-25: no compiled replacement is attached). -/
opaque sha256 : List Std.U8 → Std.Array Std.U8 32#usize :=
  fun _ => Std.Array.from (List.replicate 32 (byte 0)) (by simp)

/-- **NFKC normalization** (opaque): `nfkc cs` is the Unicode Normalization Form KC (UAX #15:
compatibility decomposition, canonical ordering, canonical composition) of the character
sequence `cs`, as `unicode-normalization 0.1.26` computes it with its Unicode tables
(`src/lib.rs`, `UnicodeNormalization::nfkc`; `src/recompose.rs`, `src/decompose.rs`). Opaque
because the normalization tables are not modelled. The value given here only shows that the
type is inhabited; an `opaque` constant does not unfold to it. Compiled evaluation (the compiled
code of any definition that reaches it, run by Lean's evaluation command or an executable)
returns this placeholder, the identity, not the NFKC form, so evaluating anything that reaches
`nfkc`, or comparing it differentially with Rust, is meaningless (lead decision 2026-11-25: no
compiled replacement is attached). -/
opaque nfkc : List Char → List Char :=
  fun cs => cs

/-- **General category** (opaque): `generalCategory c` is the Unicode General_Category of `c`
as the tables of `unicode-general-category 1.1.0` give it (`src/category.rs` lines 15–23:
`PrivateUse` above `LAST_CODEPOINT`, otherwise a two-level table lookup generated by the crate's
build script). Opaque because the tables are not modelled. The value given here only shows that
the type is inhabited; an `opaque` constant does not unfold to it. Compiled evaluation (the
compiled code of any definition that reaches it, run by Lean's evaluation command or an
executable) returns this placeholder, `Unassigned` for every character, not the Unicode
category, so evaluating anything that reaches `generalCategory`, or comparing it
differentially with Rust, is meaningless (lead decision 2026-11-25: no compiled replacement is
attached). -/
opaque generalCategory : Char → unicode_general_category.tables.GeneralCategory :=
  fun _ => unicode_general_category.tables.GeneralCategory.Unassigned

/-- A prefix of a slice's elements fits in a slice. -/
theorem length_take_le_max {α : Type} (s : Slice α) (n : Nat) :
    (s.val.take n).length ≤ Usize.max := by
  have := s.property
  rw [List.length_take]
  omega

/-- A suffix of a slice's elements fits in a slice. -/
theorem length_drop_le_max {α : Type} (s : Slice α) (n : Nat) :
    (s.val.drop n).length ≤ Usize.max := by
  have := s.property
  rw [List.length_drop]
  omega

/-- The `usize` with value `n % 2^64` (on the 64-bit target; exact for `n ≤ Usize.max`). -/
def usize (n : Nat) : Std.Usize := ⟨BitVec.ofNat _ n⟩

/-- A `Vec` of the elements `l`, or the "capacity overflow" panic when `l.length` elements of
`elemSize` bytes exceed `isize::MAX` bytes (`alloc/src/raw_vec/mod.rs` lines 929–935,
`layout_array`, through `handle_error`, lines 920–925). Collecting into a `Vec` grows its
buffer, so this is the deterministic panic of the final size; a panic caused by the capacity
history is not modelled (memory convention, module docstring). The condition `l.length ≤
Usize.max` follows from the first one for `elemSize ≥ 1` and is stated for the `Vec`
constructor. -/
def collectVec {α : Type} (elemSize : Nat) (l : List α) : Result (alloc.vec.Vec α) :=
  if h : elemSize * l.length ≤ maxStringBytes ∧ l.length ≤ Usize.max then
    ok (alloc.vec.Vec.from l h.2)
  else fail panic

/-- The `String`s with the UTF-8 encodings `parts`, in order; `fail undef` if one of them is
not UTF-8 (the `str::to_owned` model, `Str.Insts.AllocBorrowToOwnedString.to_owned`). -/
def stringsOfBytes : List (List Std.U8) → Result (List String)
  | [] => ok []
  | p :: ps =>
    match strOfBytes? p with
    | some s => do
      let rest ← stringsOfBytes ps
      ok (s :: rest)
    | none => fail undef

/-- The parts of `l` between the occurrences of the byte `sep`, in order: `str::split` with a
one-byte ASCII pattern (`core/src/str/iter.rs`, `Split`; `CharSearcher` matches the UTF-8
encoding of the char, which for an ASCII char is the byte). Always at least one part; `k`
occurrences give `k + 1` parts, empty parts included. -/
def splitBytes (sep : Std.U8) : List Std.U8 → List (List Std.U8)
  | [] => [[]]
  | b :: rest =>
    if b = sep then [] :: splitBytes sep rest
    else
      match splitBytes sep rest with
      | p :: ps => (b :: p) :: ps
      | [] => [[b]]

/-- The index just after the last occurrence of the byte `sep` in `l`, `0` if there is none:
the start of the part that `str::rsplit(sep).next()` yields. -/
def lastSegmentStart (sep : Std.U8) (l : List Std.U8) : Nat :=
  match l.reverse.findIdx? (fun b => decide (b = sep)) with
  | none => 0
  | some j => l.length - j

/-- The value of a byte as a digit in base `radix` (`2 ≤ radix ≤ 36`), `none` if it is not one:
`(c as char).to_digit(radix)` (`core/src/char/methods.rs` lines 409–431) for a byte `c`. The
decimal digits `'0'`–`'9'` have their value; for `radix > 10` the ASCII letters of either case
have the values 10–35 (`'A'`/`'a'` = 10); a value at or above `radix` is `none`, and so is
every other byte. (Rust computes the letter value with a wrapping subtraction and the mask
`!0x20`; the result is below 36 exactly for the ASCII letters.) -/
def digitValue? (radix : Nat) (c : Std.U8) : Option Nat :=
  if 48 ≤ c.val ∧ c.val ≤ 57 then
    if c.val - 48 < radix then some (c.val - 48) else none
  else if 10 < radix ∧ 65 ≤ c.val ∧ c.val ≤ 90 then
    if c.val - 55 < radix then some (c.val - 55) else none
  else if 10 < radix ∧ 97 ≤ c.val ∧ c.val ≤ 122 then
    if c.val - 87 < radix then some (c.val - 87) else none
  else none

/-- The digit loop of `u8::from_ascii_bytes_radix_impl` (`core/src/num/mod.rs` lines
1811–1857): from the accumulated value `acc`, read the digits left to right; a byte that is not
a digit is `InvalidDigit`; otherwise the next value is `acc * radix + d`, and a value above 255
is `PosOverflow`. This is the checked loop (lines 1834–1853): `checked_mul` is computed, then the
digit is checked, then the overflow of the multiplication and of `checked_add` is reported, both
as `PosOverflow` (for `acc ≤ 255` one of them overflows exactly when `acc * radix + d > 255`).
For `radix ≤ 16` and at most two digits Rust runs an unchecked loop instead (lines 1811–1825;
`can_not_overflow`, lines 1575–1577), whose values stay below `radix^2 ≤ 256`, so the overflow
check never fires there. -/
def u8DigitLoop (radix : Nat) (acc : Nat) : List Std.U8 → Except ExtModel.IntErrorKind Nat
  | [] => .ok acc
  | c :: rest =>
    match digitValue? radix c with
    | none => .error .InvalidDigit
    | some d =>
      if acc * radix + d ≤ 255 then u8DigitLoop radix (acc * radix + d) rest
      else .error .PosOverflow

/-- `u8::from_ascii_bytes_radix_impl(src, radix)` for `2 ≤ radix ≤ 36` (`core/src/num/mod.rs`
lines 1775–1863), as a number or an error kind: empty input is `Empty`; a single `+` or `-` is
`InvalidDigit`; a leading `+` is removed (`u8` is unsigned, so a leading `-` stays and is an
`InvalidDigit` of the loop); then `ExtModel.u8DigitLoop` from `0`. -/
def u8FromAscii (radix : Nat) (src : List Std.U8) : Except ExtModel.IntErrorKind Nat :=
  match src with
  | [] => .error .Empty
  | [c] =>
    if c.val = 43 ∨ c.val = 45 then .error .InvalidDigit
    else u8DigitLoop radix 0 [c]
  | c :: rest =>
    if c.val = 43 then u8DigitLoop radix 0 rest
    else u8DigitLoop radix 0 (c :: rest)

/-- `true` for the bytes that `percent_encoding::CONTROLS` percent-encodes in
`utf8_percent_encode`: every non-ASCII byte and the controls `0x00`–`0x1F` and `0x7F`
(`should_percent_encode`, `percent-encoding-2.3.2/src/ascii_set.rs` lines 52–54: `!byte.is_ascii()
|| self.contains(byte)`; `CONTROLS`, lines 103–114). -/
def isControlOrNonAscii (b : Std.U8) : Bool :=
  decide (128 ≤ b.val ∨ b.val < 32 ∨ b.val = 127)

/-- The uppercase hexadecimal digit of `n < 16` (`0`–`9`, `A`–`F`), as in the table of
`percent_encode_byte` (`percent-encoding-2.3.2/src/lib.rs` lines 73–100). -/
def upperHexDigit (n : Nat) : Std.U8 :=
  if n < 10 then byte (48 + n) else byte (55 + n)

/-- `%XX` with the two uppercase hexadecimal digits of the byte (`percent_encode_byte`,
`percent-encoding-2.3.2/src/lib.rs` lines 73–100). -/
def percentEncodeByte (b : Std.U8) : List Std.U8 :=
  [byte 37, upperHexDigit (b.val / 16), upperHexDigit (b.val % 16)]

/-- The bytes of `utf8_percent_encode(input, CONTROLS)`, the concatenation of the chunks its
iterator yields (`percent-encoding-2.3.2/src/lib.rs` lines 147–176): every byte for which
`isControlOrNonAscii` holds becomes `%XX`, every other byte is kept. -/
def percentEncodeControls : List Std.U8 → List Std.U8
  | [] => []
  | b :: rest =>
    if isControlOrNonAscii b then percentEncodeByte b ++ percentEncodeControls rest
    else b :: percentEncodeControls rest

/-- The value of a hexadecimal digit of either case (`char::from(b).to_digit(16)`), `none` for
every other byte. -/
def hexDigitValue? (b : Std.U8) : Option Nat := digitValue? 16 b

/-- The percent-decoding of `l` after the bytes already read, `state`: `none` if no `%` is
pending, `some none` after a `%`, `some (some h)` after a `%` and a hexadecimal digit `h`. A
pending `%` and digit are decoded with the next byte if that is a hexadecimal digit too;
otherwise they are kept as they are and the next byte is read again with no `%` pending. This
is `PercentDecode::next` (`percent-encoding-2.3.2/src/lib.rs` lines 252–277) written one byte
at a time: `after_percent_sign` looks at the two bytes after a `%` and consumes them only if
both are hexadecimal digits, otherwise the `%` is yielded and the following bytes are read
normally. -/
def percentDecodeFrom : Option (Option Std.U8) → List Std.U8 → List Std.U8
  | none, [] => []
  | some none, [] => [byte 37]
  | some (some h), [] => [byte 37, h]
  | none, c :: rest =>
    if c.val = 37 then percentDecodeFrom (some none) rest
    else c :: percentDecodeFrom none rest
  | some none, c :: rest =>
    match hexDigitValue? c with
    | some _ => percentDecodeFrom (some (some c)) rest
    | none =>
      if c.val = 37 then byte 37 :: percentDecodeFrom (some none) rest
      else byte 37 :: c :: percentDecodeFrom none rest
  | some (some h), c :: rest =>
    match hexDigitValue? h, hexDigitValue? c with
    | some a, some b => byte (16 * a + b) :: percentDecodeFrom none rest
    | _, _ =>
      if c.val = 37 then byte 37 :: h :: percentDecodeFrom (some none) rest
      else byte 37 :: h :: c :: percentDecodeFrom none rest

/-- The bytes of `percent_decode(input)` (`percent-encoding-2.3.2/src/lib.rs` lines 252–277):
`%` followed by two hexadecimal digits (either case) becomes the byte they denote; every other
byte, including a `%` not followed by two hexadecimal digits, is kept
(`ExtModel.percentDecodeFrom` with no `%` pending). -/
def percentDecode (l : List Std.U8) : List Std.U8 := percentDecodeFrom none l

/-- The byte with ASCII lowercase letters mapped to uppercase (`u8::to_ascii_uppercase`,
`core/src/num/mod.rs`: `*self & !(self.is_ascii_lowercase() as u8 * 0x20)`), other bytes
unchanged. -/
def asciiUppercase (b : Std.U8) : Std.U8 :=
  if 97 ≤ b.val ∧ b.val ≤ 122 then byte (b.val - 32) else b

/-- The model of `Iterator::all` on a list of remaining elements: call the closure on each in
order and stop at the first `false`. Returns the result and the number of elements consumed
(as `ExtModel.sliceIterAny` for `any`). -/
def sliceIterAll {T F : Type} (inst : core.ops.function.FnMut F T Bool) :
    List T → F → Result (Bool × Nat)
  | [], _ => ok (true, 0)
  | x :: rest, f => do
    let (b, f) ← inst.call_mut f x
    if b then do
      let (r, n) ← sliceIterAll inst rest f
      ok (r, n + 1)
    else ok (false, 1)

/-- Whether `value` is equal to some element of the list, compared as hashbrown's
`HashMap::insert` compares (`value == element` through the `Eq` instance of `T`, which
`equivalent_key` calls; its failures propagate). Used for the element list of the `HashSet`
model. -/
def listContainsEq {T : Type} (corecmpEqInst : core.cmp.Eq T) (value : T) :
    List T → Result Bool
  | [] => ok false
  | x :: rest => do
    let b ← corecmpEqInst.partialEqInst.eq value x
    if b then ok true else listContainsEq corecmpEqInst value rest

/-- `true` if the bytes `a` are less than the bytes `b` in Rust's order of byte slices
(`Ord for [u8]`, `core/src/slice/cmp.rs`: lexicographic, compared byte by byte as unsigned
numbers, a proper prefix before the longer slice). Rust's `Ord for str` and `Ord for String`
compare the UTF-8 bytes this way (`core/src/str/traits.rs`:
`self.as_bytes().cmp(other.as_bytes())`; `String` derives `Ord` from its `Vec<u8>`). -/
def bytesLt : List Std.U8 → List Std.U8 → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | a :: xs, b :: ys =>
    if a.val < b.val then true else if a.val = b.val then bytesLt xs ys else false

/-- `BTreeMap::insert` on the entries of a map with `String` keys, kept sorted by key in Rust's
`String` order (`ExtModel.bytesLt` on the UTF-8 bytes) with pairwise distinct keys: walking the
entries in order, at the first entry whose key is not less than `k`, replace its value by `v` and
return the old value if its key is `k` (the stored key is kept, as Rust's "the key is not
updated"; equal `String`s are identical), otherwise insert `(k, v)` before it and return `none`;
after the last entry, append `(k, v)` and return `none`. On sorted entries this is the `BTreeMap`
result; every list built from `[]` by `mapInsert` is sorted (`Proofs.External.Skill`). -/
def mapInsert {V : Type} (k : String) (v : V) :
    List (String × V) → Option V × List (String × V)
  | [] => (none, [(k, v)])
  | (k', v') :: rest =>
    if k' = k then (some v', (k', v) :: rest)
    else if bytesLt (utf8 k) (utf8 k') then (none, (k, v) :: (k', v') :: rest)
    else
      let r := mapInsert k v rest
      (r.1, (k', v') :: r.2)

end ExtModel

/-- [rmcp::model::skill::prim::sha256]:
    Source: 'crates/rmcp/src/model/skill.rs', lines 588:4-590:5
    Visibility: public

**Model:** `ok (sha256 bytes)`, an opaque value (`Sha256::digest(bytes).into()`:
`sha2-0.11.2`, `Digest::digest`, `digest-0.11.3/src/digest.rs`; the `Array<u8, U32>` converts to
`[u8; 32]`). Never panics within the size convention (module docstring): SHA-256 finalisation
overflows its `u64` bit length, and panics under `overflow-checks`, only for an input of at
least `2^61` bytes (`sha2-0.11.2/src/block_api.rs` line 66), as stated for `hmac_sha256`. -/
def model.skill.prim.sha256 (bytes : Slice Std.U8) : Result (Std.Array Std.U8 32#usize) :=
  ok (ExtModel.sha256 bytes.val)

/-- [rmcp::model::skill::prim::find_query_or_fragment]:
    Source: 'crates/rmcp/src/model/skill.rs', lines 592:4-594:5
    Visibility: public

**Model:** the index of the first byte `?` (63) or `#` (35), `None` if there is none
(`s.find(['?', '#'])`: `str::find` with a `[char; 2]` pattern returns the byte index of the first
char in the set, `core/src/str/mod.rs`, `find`, and `core/src/str/pattern.rs`,
`MultiCharEqSearcher`;
in UTF-8 the bytes 63 and 35 occur only as these chars). Defined on every `Str`. -/
def model.skill.prim.find_query_or_fragment (s : Str) : Result (Option Std.Usize) :=
  ok ((s.val.findIdx? (fun b => decide (b.val = 63 ∨ b.val = 35))).map ExtModel.usize)

/-- [rmcp::model::skill::prim::strip_suffix]:
    Source: 'crates/rmcp/src/model/skill.rs', lines 596:4-598:5
    Visibility: public

**Model:** `Some` of all but the last `suffix.len()` bytes if `s` ends with the bytes of
`suffix`, otherwise `None` (`s.strip_suffix(suffix)` with a `&str` pattern:
`core/src/str/pattern.rs`, `impl Pattern for &str`, `strip_suffix_of`: `is_suffix_of`, i.e.
`haystack.as_bytes().ends_with(self.as_bytes())`, then `haystack[..len - self.len()]`). The test
`s.drop (len - n) = suffix` holds exactly when `suffix` is a suffix of `s` (for `n > len` it would
say `s = suffix`, which has the wrong length). Defined on every `Str`. -/
def model.skill.prim.strip_suffix (s : Str) (suffix : Str) : Result (Option Str) :=
  if s.val.drop (s.val.length - suffix.val.length) = suffix.val then
    ok (some (Slice.from (s.val.take (s.val.length - suffix.val.length))
      (ExtModel.length_take_le_max s _)))
  else ok none

/-- [rmcp::model::skill::prim::strip_prefix]:
    Source: 'crates/rmcp/src/model/skill.rs', lines 600:4-602:5
    Visibility: public

**Model:** `Some` of the bytes after the first `prefix.len()` if `s` starts with the bytes of
`prefix`, otherwise `None` (`s.strip_prefix(prefix)` with a `&str` pattern:
`core/src/str/pattern.rs`, `impl Pattern for &str`, `strip_prefix_of`: `is_prefix_of`, i.e.
`haystack.as_bytes().starts_with(self.as_bytes())`, then `haystack[self.len()..]`). Defined on
every `Str`. -/
def model.skill.prim.strip_prefix (s : Str) («prefix» : Str) : Result (Option Str) :=
  if s.val.take «prefix».val.length = «prefix».val then
    ok (some (Slice.from (s.val.drop «prefix».val.length)
      (ExtModel.length_drop_le_max s _)))
  else ok none

/-- [rmcp::model::skill::prim::last_slash_segment]:
    Source: 'crates/rmcp/src/model/skill.rs', lines 604:4-606:5
    Visibility: public

**Model:** the bytes after the last `/` (47), all of `s` if there is none
(`s.rsplit('/').next().unwrap_or(s)`: `rsplit` always yields at least one item, the last part of
the split, `core/src/str/iter.rs`, `RSplit`; the `unwrap_or` is never taken). Defined on every
`Str`. -/
def model.skill.prim.last_slash_segment (s : Str) : Result Str :=
  ok (Slice.from (s.val.drop (ExtModel.lastSegmentStart (ExtModel.byte 47) s.val))
    (ExtModel.length_drop_le_max s _))

/-- [rmcp::model::skill::prim::split_slash]:
    Source: 'crates/rmcp/src/model/skill.rs', lines 608:4-610:5
    Visibility: public

**Model:** the parts of `s` between the `/` bytes (`ExtModel.splitBytes`), each as a `String`,
collected into a `Vec` (`s.split('/').map(str::to_owned).collect()`). `fail undef` if a part is
not UTF-8, which no part of a Rust `&str` split at an ASCII byte is (the `Str` convention,
module docstring); `fail panic` if the `Vec` of 24-byte `String`s would exceed `isize::MAX`
bytes (`ExtModel.collectVec`). The panic is patch-induced (the original call sites stream the
split or collect 16-byte `&str`s; patch 04 header, patch-induced premise 2) and unreachable on
the translated x86_64 target, where a `&str` has fewer than 2^57 bytes. -/
def model.skill.prim.split_slash (s : Str) : Result (alloc.vec.Vec String) := do
  let parts ← ExtModel.stringsOfBytes (ExtModel.splitBytes (ExtModel.byte 47) s.val)
  ExtModel.collectVec 24 parts

/-- [rmcp::model::skill::prim::join_slash]:
    Source: 'crates/rmcp/src/model/skill.rs', lines 612:4-614:5
    Visibility: public

**Model:** the segments joined with `/` (`segments.join("/")`: `alloc/src/str.rs`,
`join_generic_copy`, which reserves the exact total length and copies the separator between
consecutive segments; `""` for no segment), subject to the `String` length limit
(`ExtModel.growString`: the total length is computed with `checked_add` and the reservation
panics above `isize::MAX` bytes). -/
def model.skill.prim.join_slash (segments : alloc.vec.Vec String) : Result String :=
  ExtModel.growString (String.intercalate "/" segments.val)

/-- [rmcp::model::skill::prim::split_once_percent]:
    Source: 'crates/rmcp/src/model/skill.rs', lines 616:4-618:5
    Visibility: public

**Model:** `Some` of the bytes before and after the first `%` (37), `None` if there is none
(`s.split_once('%')`: `core/src/str/mod.rs`, `split_once`, finds the first match and returns
`(&self[..start], &self[end..])`). Defined on every `Str`. -/
def model.skill.prim.split_once_percent (s : Str) : Result (Option (Str × Str)) :=
  match s.val.findIdx? (fun b => decide (b.val = 37)) with
  | none => ok none
  | some i =>
    ok (some (Slice.from (s.val.take i) (ExtModel.length_take_le_max s _),
      Slice.from (s.val.drop (i + 1)) (ExtModel.length_drop_le_max s _)))

/-- [rmcp::model::skill::prim::split_percent]:
    Source: 'crates/rmcp/src/model/skill.rs', lines 620:4-622:5
    Visibility: public

**Model:** as `split_slash`, at the `%` bytes (37) (`s.split('%').map(str::to_owned).collect()`),
with the same `fail undef` and `fail panic` cases (the panic patch-induced and unreachable, as
for `split_slash`). -/
def model.skill.prim.split_percent (s : Str) : Result (alloc.vec.Vec String) := do
  let parts ← ExtModel.stringsOfBytes (ExtModel.splitBytes (ExtModel.byte 37) s.val)
  ExtModel.collectVec 24 parts

/-- [rmcp::model::skill::prim::percent_encode_controls]:
    Source: 'crates/rmcp/src/model/skill.rs', lines 624:4-626:5
    Visibility: public

**Model:** `Cow::Borrowed(s)` if no byte needs encoding (in particular for the empty string);
`Cow::Borrowed` of `%XX` if `s` is a single byte that needs encoding; otherwise `Cow::Owned` of the
`String` of `ExtModel.percentEncodeControls`, which is ASCII. This is
`utf8_percent_encode(value, CONTROLS).into()` (`percent-encoding-2.3.2/src/lib.rs` lines
136–138 and 194–209): the conversion takes the first two chunks of the iterator (lines
147–176: a chunk is either `%XX` for one byte that needs encoding or a maximal run of bytes that
do not) and returns `Borrowed("")` for none, `Borrowed(first)` for exactly one, and otherwise
the owned concatenation of all chunks. There is at most one chunk exactly when no byte needs
encoding (one run, or none for the empty input) or the input is one byte that needs encoding; a
byte that needs encoding next to any other byte gives two chunks. The owned string is subject to
the `String` length limit (`ExtModel.growString`). Defined on every `Str`. -/
def model.skill.prim.percent_encode_controls (value : Str) :
    Result (alloc.borrow.Cow Str String) :=
  if value.val.all (fun b => !ExtModel.isControlOrNonAscii b) then
    ok (alloc.borrow.Cow.Borrowed value)
  else
    match value.val with
    | [b] =>
      ok (alloc.borrow.Cow.Borrowed (Slice.from (ExtModel.percentEncodeByte b) (by
        simp only [ExtModel.percentEncodeByte, List.length_cons, List.length_nil]
        scalar_tac)))
    | _ => do
      let s ← ExtModel.growString (String.ofList ((ExtModel.percentEncodeControls value.val).map
        (fun b => Char.ofNat b.val)))
      ok (alloc.borrow.Cow.Owned s)

/-- [rmcp::model::skill::prim::percent_decode_utf8]:
    Source: 'crates/rmcp/src/model/skill.rs', lines 628:4-633:5
    Visibility: public

**Model:** `Some s` if the percent-decoded bytes (`ExtModel.percentDecode`) are the UTF-8
encoding of `s`, otherwise `None` (`percent_decode_str(s).decode_utf8().ok().map(Cow::into_owned)`:
`percent-encoding-2.3.2/src/lib.rs` lines 217–219 and 312–323; `decode_utf8` checks the decoded
bytes with `str::from_utf8` or `String::from_utf8`, whichever the `Cow` holds, and both decide
UTF-8 validity, see `ExtModel.strOfBytes?`). The decoded bytes are at most as many as the input
bytes, so no capacity panic is possible. Defined on every `Str`. -/
def model.skill.prim.percent_decode_utf8 (s : Str) : Result (Option String) :=
  ok (ExtModel.strOfBytes? (ExtModel.percentDecode s.val))

/-- [rmcp::model::skill::prim::nfkc]:
    Source: 'crates/rmcp/src/model/skill.rs', lines 635:4-637:5
    Visibility: public

**Model:** the characters `nfkc cs` of the NFKC form of the characters `cs` of `s`, an opaque
value, collected into a `Vec` (`s.nfkc().collect()`: `unicode-normalization-0.1.26`,
`UnicodeNormalization for str`, `src/lib.rs`, an iterator over the `chars()` of `s`).
`fail undef` if `s` is not UTF-8, which no Rust `&str` is (the `Str` convention); `fail panic` if
the `Vec` of 4-byte `char`s would exceed `isize::MAX` bytes (`ExtModel.collectVec`). -/
def model.skill.prim.nfkc (s : Str) : Result (alloc.vec.Vec Char) :=
  match ExtModel.strOfBytes? s.val with
  | some str => ExtModel.collectVec 4 (ExtModel.nfkc str.toList)
  | none => fail undef

/-- [unicode_general_category::category::get_general_category]:
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/unicode-general-category-1.1.0/src/category.rs', lines 15:0-15:57
    Name pattern: [unicode_general_category::category::get_general_category]
    Visibility: public

**Model:** `ok (generalCategory c)`, an opaque value (lines 15–23: a table lookup that never
panics, the indices being bounded by the generated tables). -/
@[rust_fun "unicode_general_category::category::get_general_category"]
def unicode_general_category.category.get_general_category (c : Char) :
    Result unicode_general_category.tables.GeneralCategory :=
  ok (ExtModel.generalCategory c)

/-- [core::array::iter::{impl core::iter::traits::collect::IntoIterator<T, core::array::iter::IntoIter<T, N>> for [T; N]}::into_iter]:
    Source: '/rustc/library/core/src/array/iter.rs', lines 59:4-59:40
    Name pattern: [core::array::iter::{core::iter::traits::collect::IntoIterator<[@T; @N], @T, core::array::iter::IntoIter<@T, @N>>}::into_iter]
    Visibility: public

**Model:** the iterator over the whole array, `alive = 0..N` (lines 59–78:
`InnerSized::new_unchecked(IndexRange::zero_to(N), data)` on the array reinterpreted as
`[MaybeUninit<T>; N]`). -/
@[rust_fun
  "core::array::iter::{core::iter::traits::collect::IntoIterator<[@T; @N], @T, core::array::iter::IntoIter<@T, @N>>}::into_iter"]
def Array.Insts.CoreIterTraitsCollectIntoIteratorTIntoIter.into_iter {T : Type} {N : Std.Usize}
    (self : Array T N) : Result (core.array.iter.IntoIter T N) :=
  ok { data := self, aliveStart := 0, aliveEnd := N.val, aliveStart_le := Nat.zero_le _,
       aliveEnd_le := Nat.le_refl _ }

/-- [core::array::iter::{impl core::iter::traits::iterator::Iterator<T> for core::array::iter::IntoIter<T, N>}::next]:
    Source: '/rustc/library/core/src/array/iter.rs', lines 245:4-245:44
    Name pattern: [core::array::iter::{core::iter::traits::iterator::Iterator<core::array::iter::IntoIter<@T, @N>, @T>}::next]
    Visibility: public

**Model:** if the alive range is not empty, the element at its start, and the iterator with the
start moved one on; otherwise `None` and the iterator unchanged (lines 245–247,
`self.unsize_mut().next()`; `PolymorphicIter::next`, `array/iter/iter_inner.rs` lines 206–222:
`self.alive.next().map(|idx| data[idx].assume_init_read())`; `IndexRange::next`,
`core/src/ops/index_range.rs` lines 130–137). The index is in bounds by the invariants of the
model type. -/
@[rust_fun
  "core::array::iter::{core::iter::traits::iterator::Iterator<core::array::iter::IntoIter<@T, @N>, @T>}::next"]
def core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator.next {T : Type} {N : Std.Usize}
    (self : core.array.iter.IntoIter T N) :
    Result (Option T × core.array.iter.IntoIter T N) :=
  if h : self.aliveStart < self.aliveEnd then
    ok (some (self.data.val[self.aliveStart]'(by
          have h1 := self.data.property
          have h2 := self.aliveEnd_le
          omega)),
      { self with aliveStart := self.aliveStart + 1, aliveStart_le := h })
  else ok (none, self)

/-- [core::bool::{bool}::then_some]:
    Source: '/rustc/library/core/src/bool.rs', lines 36:4-36:72
    Name pattern: [core::bool::{bool}::then_some]
    Visibility: public

**Model:** `Some t` if `self`, otherwise `None` (lines 36–38). -/
@[rust_fun "core::bool::{bool}::then_some"]
def core.bool.Bool.then_some {T : Type} (self : Bool) (t : T) : Result (Option T) :=
  if self then ok (some t) else ok none

/-- [core::char::convert::{impl core::convert::From<u8> for char}::from]:
    Source: '/rustc/library/core/src/char/convert.rs', lines 229:4-229:26
    Name pattern: [core::char::convert::{core::convert::From<char, u8>}::from]
    Visibility: public

**Model:** the character with the byte's value as code point, `U+0000`–`U+00FF` (`i as char`,
lines 229–231; every such value is a Unicode scalar value). -/
@[rust_fun "core::char::convert::{core::convert::From<char, u8>}::from"]
def Char.Insts.CoreConvertFromU8.from (i : Std.U8) : Result Char :=
  ok (Char.ofNat i.val)

/-- [core::cmp::impls::{impl core::cmp::PartialEq<char> for char}::eq]:
    Source: '/rustc/library/core/src/cmp.rs', lines 2185:16-2185:50
    Name pattern: [core::cmp::impls::{core::cmp::PartialEq<char, char>}::eq]
    Visibility: public

**Model:** equality of the characters (`*self == *other`, line 2185, for the primitive `char`:
equality of the code points). -/
@[rust_fun "core::cmp::impls::{core::cmp::PartialEq<char, char>}::eq"]
def Char.Insts.CoreCmpPartialEqChar.eq (self : Char) (other : Char) : Result Bool :=
  ok (decide (self = other))

/-- [core::iter::traits::iterator::Iterator::all]:
    Source: '/rustc/library/core/src/iter/traits/iterator.rs', lines 2840:4-2843:64
    Name pattern: [core::iter::traits::iterator::Iterator::all]
    Visibility: public

**Model:** calls `next` and the closure alternately until the closure returns `false` (result
`false`) or `next` returns `None` (result `true`), through the `loop` combinator of the Aeneas
library, which is `div` if this never happens. The Rust default method is
`self.try_fold((), check(f)) == ControlFlow::Continue(())` (lines 2840–2855), and the default
`try_fold` is that `next` loop. Stated exception: an iterator that overrides `try_fold` is
modelled by the loop. Declared by the Aeneas template; no generated definition calls it (the
translated code calls the `Bytes` override below). -/
@[rust_fun "core::iter::traits::iterator::Iterator::all"]
def core.iter.traits.iterator.Iterator.all.default {Self : Type} {F : Type} {Clause0_Item : Type}
    (IteratorInst : core.iter.traits.iterator.Iterator Self Clause0_Item)
    (opsfunctionFnMutFTupleClause0_ItemBoolInst :
      core.ops.function.FnMut F Clause0_Item Bool)
    (self : Self) (f : F) : Result (Bool × Self) :=
  loop (fun (st : Self × F) => do
      let (o, it) ← IteratorInst.next st.1
      match o with
      | none => ok (ControlFlow.done (true, it))
      | some x => do
        let (b, f) ← opsfunctionFnMutFTupleClause0_ItemBoolInst.call_mut st.2 x
        if b then ok (ControlFlow.cont (it, f)) else ok (ControlFlow.done (false, it)))
    (self, f)

/-- [core::num::error::{impl core::fmt::Debug for core::num::error::ParseIntError}::fmt]:
    Source: '/rustc/library/core/src/num/error.rs', lines 67:9-67:14
    Name pattern: [core::num::error::{core::fmt::Debug<core::num::error::ParseIntError>}::fmt]
    Visibility: public

**Model (total, lead decision 2026-11-25; a stated exception of the trusted base):** `Ok(())`
and the formatter unchanged; the text
written (the derived `Debug` output `ParseIntError { kind: .. }`, line 67) is not modelled, as
for the `Debug` models of the Aeneas library (`core.fmt.DebugBool.fmt`). It is reached only
through `Result::expect` in `push_normalized_part`, whose `Err` path is `fail panic` whatever the
formatter holds (`core.result.Result.expect` of the Aeneas library), and that path is never taken
(`from_str_radix` is called on two hexadecimal digits, checked before the call). An exact model
is not possible: `core::fmt::Formatter` is opaque in the Aeneas library, so the written text has
no representation. -/
@[rust_fun
  "core::num::error::{core::fmt::Debug<core::num::error::ParseIntError>}::fmt"]
def core.num.error.ParseIntError.Insts.CoreFmtDebug.fmt (_self : core.num.error.ParseIntError)
    (f : core.fmt.Formatter) :
    Result ((core.result.Result Unit core.fmt.Error) × core.fmt.Formatter) :=
  ok (core.result.Result.Ok (), f)

/-- [core::num::{u8}::is_ascii_alphanumeric]:
    Source: '/rustc/library/core/src/num/mod.rs', lines 930:4-930:53
    Name pattern: [core::num::{u8}::is_ascii_alphanumeric]
    Visibility: public

**Model:** `true` exactly for `0`–`9`, `A`–`Z` and `a`–`z` (lines 930–932). -/
@[rust_fun "core::num::{u8}::is_ascii_alphanumeric"]
def core.num.U8.is_ascii_alphanumeric (self : Std.U8) : Result Bool :=
  ok (decide ((48 ≤ self.val ∧ self.val ≤ 57) ∨ (65 ≤ self.val ∧ self.val ≤ 90) ∨
    (97 ≤ self.val ∧ self.val ≤ 122)))

/-- [core::num::{u8}::is_ascii_hexdigit]:
    Source: '/rustc/library/core/src/num/mod.rs', lines 1032:4-1032:49
    Name pattern: [core::num::{u8}::is_ascii_hexdigit]
    Visibility: public

**Model:** `true` exactly for `0`–`9`, `A`–`F` and `a`–`f` (lines 1032–1034). -/
@[rust_fun "core::num::{u8}::is_ascii_hexdigit"]
def core.num.U8.is_ascii_hexdigit (self : Std.U8) : Result Bool :=
  ok (decide ((48 ≤ self.val ∧ self.val ≤ 57) ∨ (65 ≤ self.val ∧ self.val ≤ 70) ∨
    (97 ≤ self.val ∧ self.val ≤ 102)))

/-- [core::num::{u8}::from_str_radix]:
    Source: '/rustc/library/core/src/num/mod.rs', lines 1683:12-1683:96
    Name pattern: [core::num::{u8}::from_str_radix]
    Visibility: public

**Model:** `fail panic` if `radix` is not in `2..=36` (`from_ascii_bytes_radix_panic`, lines
1779–1781, before any other check); otherwise `Ok v` where `ExtModel.u8FromAscii` gives the
number `v` and `Err { kind }` where it gives the error kind. Rust: `from_str_radix(src, radix) =
u8::from_ascii_bytes_radix_impl(src.as_bytes(), radix)` (lines 1683–1685). Grammar: an optional
single `+`, then at least one digit of the radix and nothing else (no `-`: the type is unsigned);
error kinds `Empty`, `InvalidDigit`, `PosOverflow` (the first met from the left; a non-digit
before an overflow at the same position). The model reads only the bytes, as Rust does, so it is
defined on every `Str`. The number `v` is at most 255 (checked by the loop), so it is the value
of the `U8` built from it. -/
@[rust_fun "core::num::{u8}::from_str_radix"]
def core.num.U8.from_str_radix (src : Str) (radix : Std.U32) :
    Result (core.result.Result Std.U8 core.num.error.ParseIntError) :=
  if radix.val < 2 ∨ 36 < radix.val then fail panic
  else
    match ExtModel.u8FromAscii radix.val src.val with
    | .ok v => ok (core.result.Result.Ok (ExtModel.byte v))
    | .error kind => ok (core.result.Result.Err { kind })

/-- [core::option::{core::option::Option<T>}::as_deref]:
    Source: '/rustc/library/core/src/option.rs', lines 1388:4-1390:25
    Name pattern: [core::option::{core::option::Option<@T>}::as_deref]
    Visibility: public

**Model:** `Some t ↦ Some (t.deref())` through the `Deref` instance (its failure propagates),
`None ↦ None` (`self.as_ref().map(Deref::deref)`, lines 1388–1393). -/
@[rust_fun "core::option::{core::option::Option<@T>}::as_deref"]
def core.option.Option.as_deref {T : Type} {Clause0_Target : Type}
    (opsderefDerefInst : core.ops.deref.Deref T Clause0_Target) (self : Option T) :
    Result (Option Clause0_Target) :=
  match self with
  | some t => do
    let x ← opsderefDerefInst.deref t
    ok (some x)
  | none => ok none

/-- [core::option::{impl core::ops::try_trait::Try for core::option::Option<T>}::branch]:
    Source: '/rustc/library/core/src/option.rs', lines 2875:4-2875:64
    Name pattern: [core::option::{core::ops::try_trait::Try<core::option::Option<@T>>}::branch]
    Visibility: public

**Model:** `Some v ↦ Continue v`, `None ↦ Break None` (lines 2875–2880; the `?` operator). -/
@[rust_fun
  "core::option::{core::ops::try_trait::Try<core::option::Option<@T>>}::branch"]
def core.option.Option.Insts.CoreOpsTry_traitTry.branch {T : Type} (self : Option T) :
    Result (core.ops.control_flow.ControlFlow (Option Never) T) :=
  match self with
  | some v => ok (core.ops.control_flow.ControlFlow.Continue v)
  | none => ok (core.ops.control_flow.ControlFlow.Break none)

/-- [core::option::{impl core::ops::try_trait::FromResidual<core::option::Option<!>> for core::option::Option<T>}::from_residual]:
    Source: '/rustc/library/core/src/option.rs', lines 2889:4-2889:49
    Name pattern: [core::option::{core::ops::try_trait::FromResidual<core::option::Option<@T>, core::option::Option<!>>}::from_residual]
    Visibility: public

**Model:** `None ↦ None` (lines 2889–2893; `Option<!>` has no other value, `Never` being
empty). -/
@[rust_fun
  "core::option::{core::ops::try_trait::FromResidual<core::option::Option<@T>, core::option::Option<!>>}::from_residual"]
def core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionNever.from_residual (T : Type)
    (residual : Option Never) : Result (Option T) :=
  match residual with
  | none => ok none
  | some n => nomatch n

/-- [core::str::iter::{impl core::iter::traits::iterator::Iterator<u8> for core::str::iter::Bytes<'_0>}::all]:
    Source: '/rustc/library/core/src/str/iter.rs', lines 316:4-318:37
    Name pattern: [core::str::iter::{core::iter::traits::iterator::Iterator<core::str::iter::Bytes<'0>, u8>}::all]
    Visibility: public

**Model:** calls the closure (through its `FnMut` instance, whose failures propagate) on the
remaining bytes in order, stops at the first `false`, and returns whether none was found and
the iterator advanced past every byte it consumed (`ExtModel.sliceIterAll`). The Rust function
is `self.0.all(f)` (lines 316–321) on `Copied<slice::Iter<u8>>`, the default `Iterator::all`
(`try_fold` of `Copied` forwards to the slice iterator's `try_fold` with the copied items), which
consumes the items up to and including the first one for which the closure returns `false`. -/
@[rust_fun
  "core::str::iter::{core::iter::traits::iterator::Iterator<core::str::iter::Bytes<'0>, u8>}::all"]
def core.str.iter.Bytes.Insts.CoreIterTraitsIteratorIteratorU8.all {F : Type}
    (opsfunctionFnMutFTupleU8BoolInst : core.ops.function.FnMut F Std.U8 Bool)
    (self : core.str.iter.Bytes) (f : F) : Result (Bool × core.str.iter.Bytes) := do
  let (b, n) ← ExtModel.sliceIterAll opsfunctionFnMutFTupleU8BoolInst
    (self.inner.slice.val.drop self.inner.i) f
  ok (b, { inner := { self.inner with i := self.inner.i + n } })

/-- [core::str::{str}::is_empty]:
    Source: '/rustc/library/core/src/str/mod.rs', lines 175:4-175:40
    Name pattern: [core::str::{str}::is_empty]
    Visibility: public

**Model:** `true` exactly for no bytes (`self.len() == 0`, lines 175–177), for every `Str`. -/
@[rust_fun "core::str::{str}::is_empty"]
def core.str.Str.is_empty (self : Str) : Result Bool :=
  ok self.val.isEmpty

/-- Whether byte index `i` is a char boundary of the bytes `l` (`str::is_char_boundary`,
`core/src/str/mod.rs` lines 375–398): `0` always; at or beyond the end exactly the length; inside,
when the byte at `i` is not a UTF-8 continuation byte (`(b as i8) >= -0x40`, i.e. `b < 128` or
`b ≥ 192`, `core/src/num/mod.rs` lines 1229–1232). -/
def ExtModel.isCharBoundary (l : List Std.U8) (i : Nat) : Bool :=
  if i = 0 then true
  else if l.length ≤ i then decide (i = l.length)
  else decide ((l.getD i (ExtModel.byte 0)).val < 128 ∨ 192 ≤ (l.getD i (ExtModel.byte 0)).val)

/-- [core::str::{str}::split_at_checked]:
    Source: '/rustc/library/core/src/str/mod.rs', lines 941:4-941:76
    Name pattern: [core::str::{str}::split_at_checked]
    Visibility: public

**Model:** `Some` of the bytes before and from `mid` if `mid` is a char boundary
(`ExtModel.isCharBoundary`), otherwise `None` (lines 941–949). Defined on every `Str`. -/
@[rust_fun "core::str::{str}::split_at_checked"]
def core.str.Str.split_at_checked (self : Str) (mid : Std.Usize) : Result (Option (Str × Str)) :=
  if ExtModel.isCharBoundary self.val mid.val then
    ok (some (Slice.from (self.val.take mid.val) (ExtModel.length_take_le_max self _),
      Slice.from (self.val.drop mid.val) (ExtModel.length_drop_le_max self _)))
  else ok none

/-- [core::str::{str}::split_at]:
    Source: '/rustc/library/core/src/str/mod.rs', lines 860:4-860:60
    Name pattern: [core::str::{str}::split_at]
    Visibility: public

**Model:** the bytes before and from `mid` if `mid` is a char boundary, otherwise `fail panic`
(lines 860–865: `split_at_checked`, and `slice_error_fail` panics on `None`). Defined on every
`Str`. -/
@[rust_fun "core::str::{str}::split_at"]
def core.str.Str.split_at (self : Str) (mid : Std.Usize) : Result (Str × Str) :=
  if ExtModel.isCharBoundary self.val mid.val then
    ok (Slice.from (self.val.take mid.val) (ExtModel.length_take_le_max self _),
      Slice.from (self.val.drop mid.val) (ExtModel.length_drop_le_max self _))
  else fail panic

/-- [core::str::{str}::bytes]:
    Source: '/rustc/library/core/src/str/mod.rs', lines 1159:4-1159:36
    Name pattern: [core::str::{str}::bytes]
    Visibility: public

**Model:** the byte iterator at the first byte (`Bytes(self.as_bytes().iter().copied())`, lines
1159–1161; `slice::iter` of the Aeneas library starts at index 0). -/
@[rust_fun "core::str::{str}::bytes"]
def core.str.Str.bytes (self : Str) : Result core.str.iter.Bytes :=
  ok { inner := { slice := self, i := 0 } }

/-- [std::collections::hash::set::{std::collections::hash::set::HashSet<T, std::hash::random::RandomState, alloc::alloc::Global>}::with_capacity]:
    Source: '/rustc/library/std/src/collections/hash/set.rs', lines 169:4-169:68
    Name pattern: [std::collections::hash::set::{std::collections::hash::set::HashSet<@T, std::hash::random::RandomState, alloc::alloc::Global>}::with_capacity]
    Visibility: public

**Model:** the empty set with hash builder `ExtModel.randomState` and the `Global` allocator
(`HashSet::with_capacity_and_hasher(capacity, Default::default())`, lines 169–171; hashbrown
0.17.1 `HashSet::with_capacity_and_hasher`, `src/set.rs` lines 502–506). Capacity is not part of
the value model. Stated exceptions, as for `HashMap::new`: the `RandomState` keys are random in
Rust and an unknown constant here (`ExtModel.randomState`), and the panic of the operating
system's random source is not modelled. The review rule of `ExtModel.randomState` applies to
the `hash_builder` of a set built here and to the equality of two such sets. Not modelled
either: hashbrown's "Hash table capacity overflow" panic, which needs `capacity * 8 / 7` to
overflow `usize` or a table of more than `isize::MAX` bytes. It depends on `size_of::<T>()`,
which the model does not have (a merged type), and it cannot occur in the translation within
the size convention (module docstring): `capacity` is the length of a slice of `SkillResource`
or `Skill` values (each at least 24 bytes) held in an address space of at most `2^57` bytes, so
`capacity < 2^53`, and the table of `String`s then has at most `2^54` buckets of 25 bytes (the
element and one control byte), far below `isize::MAX`. Allocation
failure is not modelled (memory convention). -/
@[rust_fun
  "std::collections::hash::set::{std::collections::hash::set::HashSet<@T, std::hash::random::RandomState, alloc::alloc::Global>}::with_capacity"]
def std.collections.hash.set.HashSetTRandomStateGlobal.with_capacity (T : Type)
    (_capacity : Std.Usize) :
    Result (std.collections.hash.set.HashSet T std.hash.random.RandomState alloc.alloc.Global) :=
  ok { hash_builder := ExtModel.randomState, alloc := alloc.alloc.Global.mk, elements := [] }

/-- [std::collections::hash::set::{std::collections::hash::set::HashSet<T, S, A>}::insert]:
    Source: '/rustc/library/std/src/collections/hash/set.rs', lines 1034:4-1034:46
    Name pattern: [std::collections::hash::set::{std::collections::hash::set::HashSet<@T, @S, @A>}::insert]
    Visibility: public

**Model:** if an element equal to `value` is present (`ExtModel.listContainsEq`), `false`
and the set unchanged; otherwise `true` and the set with `value` added. The Rust function is
`self.base.insert(value)` (lines 1034–1036), i.e. hashbrown 0.17.1 `HashSet::insert`
(`src/set.rs` lines 1074–1076: `self.map.insert(value, ()).is_none()`), and `HashMap::insert`
(`src/map.rs` lines 1806–1823) replaces the unit value of an equal key, keeping the stored key,
or inserts the new one. Hashing is not modelled, for the reason given at
`std.collections.hash.map.HashMap.get` (faithful for `Hash`/`Eq` instances that agree and do not
fail; the only instance in the translation is `T = String`). Not modelled: the growth of the
table (memory convention). -/
@[rust_fun
  "std::collections::hash::set::{std::collections::hash::set::HashSet<@T, @S, @A>}::insert"]
def std.collections.hash.set.HashSet.insert {T : Type} {S : Type} {A : Type}
    {Clause2_Hasher : Type} (corecmpEqInst : core.cmp.Eq T)
    (_corehashHashInst : core.hash.Hash T)
    (_corehashBuildHasherInst : core.hash.BuildHasher S Clause2_Hasher)
    (self : std.collections.hash.set.HashSet T S A) (value : T) :
    Result (Bool × (std.collections.hash.set.HashSet T S A)) := do
  let found ← ExtModel.listContainsEq corecmpEqInst value self.elements
  if found then ok (false, self)
  else ok (true, { self with elements := self.elements ++ [value] })

/-- [alloc::borrow::{alloc::borrow::Cow<'_0, B, Clause0_Owned>}::into_owned]:
    Source: '/rustc/library/alloc/src/borrow.rs', lines 331:4-331:52
    Name pattern: [alloc::borrow::{alloc::borrow::Cow<'0, @B, @Clause0_Owned>}::into_owned]
    Visibility: public

**Model:** `Borrowed b ↦ b.to_owned()` through the `ToOwned` instance (its failure propagates),
`Owned o ↦ o` (lines 331–336). -/
@[rust_fun
  "alloc::borrow::{alloc::borrow::Cow<'0, @B, @Clause0_Owned>}::into_owned"]
def alloc.borrow.Cow.into_owned {B : Type} {Clause0_Owned : Type}
    (ToOwnedInst : alloc.borrow.ToOwned B Clause0_Owned)
    (self : alloc.borrow.Cow B Clause0_Owned) : Result Clause0_Owned :=
  match self with
  | alloc.borrow.Cow.Borrowed b => ToOwnedInst.to_owned b
  | alloc.borrow.Cow.Owned o => ok o

/-- [alloc::borrow::{impl core::ops::deref::Deref<B> for alloc::borrow::Cow<'_0, B, Clause0_Owned>}::deref]:
    Source: '/rustc/library/alloc/src/borrow.rs', lines 349:4-349:25
    Name pattern: [alloc::borrow::{core::ops::deref::Deref<alloc::borrow::Cow<'0, @B, @Clause0_Owned>, @B>}::deref]
    Visibility: public

**Model:** `Borrowed b ↦ b`, `Owned o ↦ o.borrow()` through the `Borrow` instance of the
`ToOwned` instance (its failure propagates) (lines 349–354). -/
@[rust_fun
  "alloc::borrow::{core::ops::deref::Deref<alloc::borrow::Cow<'0, @B, @Clause0_Owned>, @B>}::deref"]
def alloc.borrow.Cow.Insts.CoreOpsDerefDeref.deref {B : Type} {Clause0_Owned : Type}
    (ToOwnedInst : alloc.borrow.ToOwned B Clause0_Owned)
    (self : alloc.borrow.Cow B Clause0_Owned) : Result B :=
  match self with
  | alloc.borrow.Cow.Borrowed b => ok b
  | alloc.borrow.Cow.Owned o => ToOwnedInst.coreborrowBorrowInst.borrow o

/-- [alloc::str::{str}::to_ascii_uppercase]:
    Source: '/rustc/library/alloc/src/str.rs', lines 856:4-856:46
    Name pattern: [alloc::str::{str}::to_ascii_uppercase]
    Visibility: public

**Model:** the `String` of the bytes with `a`–`z` mapped to `A`–`Z` (`ExtModel.asciiUppercase`;
lines 856–861: `self.as_bytes().to_ascii_uppercase()`, then `String::from_utf8_unchecked`).
`fail undef` if the bytes are not UTF-8, which no Rust `&str` is (the `Str` convention; the
mapping keeps UTF-8 validity in both directions). The copy has the length of an existing slice,
so it never hits the capacity-overflow panic. -/
@[rust_fun "alloc::str::{str}::to_ascii_uppercase"]
def alloc.str.Str.to_ascii_uppercase (self : Str) : Result String :=
  match ExtModel.strOfBytes? (self.val.map ExtModel.asciiUppercase) with
  | some s => ok s
  | none => fail undef

/-- [alloc::string::{alloc::string::String}::as_str]:
    Source: '/rustc/library/alloc/src/string.rs', lines 1073:4-1073:38
    Name pattern: [alloc::string::{alloc::string::String}::as_str]
    Visibility: public

**Model:** the UTF-8 bytes of the string (`str::from_utf8_unchecked(self.vec.as_slice())`, lines
1073–1077), defined as the model of `String::as_bytes`, which returns the same bytes:
`fail maximumSizeExceeded` only for a Lean `String` longer than `Usize.max` bytes, which no Rust
`String` is. -/
@[rust_fun "alloc::string::{alloc::string::String}::as_str"]
def alloc.string.String.as_str (self : String) : Result Str :=
  alloc.string.String.as_bytes self

/-- [alloc::vec::{alloc::vec::Vec<T>}::pop]:
    Source: '/rustc/library/alloc/src/vec/mod.rs', lines 2901:4-2901:38
    Name pattern: [alloc::vec::{alloc::vec::Vec<@T>}::pop]
    Visibility: public

**Model:** `None` and the vector unchanged if it is empty; otherwise its last element and the
vector without it (lines 2901–2913). The allocator parameter `A` is not used. -/
@[rust_fun "alloc::vec::{alloc::vec::Vec<@T>}::pop"]
def alloc.vec.Vec.pop {T : Type} (_A : Type) (self : alloc.vec.Vec T) :
    Result ((Option T) × (alloc.vec.Vec T)) :=
  if h : self.val = [] then ok (none, self)
  else
    ok (some (self.val.getLast h), alloc.vec.Vec.from self.val.dropLast (by
      have := alloc.vec.Vec.property self
      rw [List.length_dropLast]
      omega))

/-- [serde_json::map::{serde_json::map::Map<alloc::string::String, serde_json::value::Value>}::new]:
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/serde_json-1.0.154/src/map.rs', lines 51:4-51:24
    Name pattern: [serde_json::map::{serde_json::map::Map<alloc::string::String, serde_json::value::Value>}::new]
    Visibility: public

**Model:** the empty map (`Map { map: MapImpl::default() }`, lines 51–55: an empty
`BTreeMap`, which does not allocate). -/
@[rust_fun
  "serde_json::map::{serde_json::map::Map<alloc::string::String, serde_json::value::Value>}::new"]
def serde_json.map.MapStringValue.new :
    Result (serde_json.map.Map String serde_json.value.Value) :=
  ok { entries := [] }

/-- [serde_json::map::{serde_json::map::Map<alloc::string::String, serde_json::value::Value>}::insert]:
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/serde_json-1.0.154/src/map.rs', lines 137:4-137:66
    Name pattern: [serde_json::map::{serde_json::map::Map<alloc::string::String, serde_json::value::Value>}::insert]
    Visibility: public

**Model:** the `BTreeMap` insertion into the entries sorted by key (`ExtModel.mapInsert`): if
an entry has key `k`, its value is replaced by `v` in place and the old value returned;
otherwise `(k, v)` is inserted at its position in the key order and `None` returned
(`self.map.insert(k, v)`, lines 137–139, `BTreeMap::insert`, `alloc/src/collections/btree/map.rs`:
"If the map did have this key present, the value is updated, and the old value is returned. The
key is not updated"). Keys are compared as Rust compares `String`s (`Ord for String`, the
lexicographic order of the UTF-8 bytes, `ExtModel.bytesLt`, whose equality is equality of the
strings). Not modelled: the node structure of the B-tree and allocation failure. -/
@[rust_fun
  "serde_json::map::{serde_json::map::Map<alloc::string::String, serde_json::value::Value>}::insert"]
def serde_json.map.MapStringValue.insert
    (self : serde_json.map.Map String serde_json.value.Value) (k : String)
    (v : serde_json.value.Value) :
    Result ((Option serde_json.value.Value) ×
      (serde_json.map.Map String serde_json.value.Value)) :=
  let r := ExtModel.mapInsert k v self.entries
  ok (r.1, { entries := r.2 })

/-! ## `metadata_resolver.rs` address policy (N01, N03–N11, translation patch 05)

External functions reached by the targets N01 and N03–N11 of
`crates/rmcp/src/transport/auth/metadata_resolver.rs` and the helpers of translation patch 05
(human decisions 2026-11-25). Translation patch 05 adds the module `metadata_resolver::prim`,
whose five functions (`Source:` lines refer to the patched copy, patch 05 on top of patches
01–04) are opaque in the translation and modelled here, and makes the remaining code use only
standard-library functions and three functions of `url 2.5.9`, whose models follow. Every model
is a definition. The values a model cannot compute are the `opaque` constants
`ExtModel.urlParse`, `ExtModel.urlHost` and `ExtModel.urlHostStr` (the URL parser, of the
abstract type `url.Url`), `ExtModel.systemLookup` (the operating-system resolver, of the
abstract type `Lookup`) and `ExtModel.proxyEnvValues` (the proxy environment variables, an
opaque constant under the review rule of `ExtModel.nowMs`), which add no axiom. No law is stated
here: a statement that needs one, such as the agreement of `Url::host` and `Url::host_str`,
takes it as a hypothesis (human decision 2026-11-25). Every other model is exact and computable,
so it can be evaluated on small inputs (examples in `Proofs.External.MetadataResolver`).

Crates cited (pinned in `scripts/aeneas-translate.sh`, `PINNED_DEPS`): `url 2.5.9`. -/

namespace ExtModel

/-- **URL parsing** (opaque): `urlParse input` is the value of `url::Url::parse` on the string
with the UTF-8 bytes `input` (`url-2.5.9/src/lib.rs` lines 340–342: `Url::options().parse(input)`,
the WHATWG URL parser of `src/parser.rs`, with IDNA processing of domains by `idna`). Opaque
because the parser is not modelled (human decision 2026-11-25). The value given here only shows
that the type is inhabited; an `opaque` constant does not unfold to it. Compiled evaluation (the
compiled code of any definition that reaches it, run by Lean's evaluation command or an
executable) returns this placeholder, `Err(EmptyHost)` for every input, so evaluating anything
that reaches `urlParse`, or comparing it differentially with Rust, is meaningless (as for
`ExtModel.sha256`; no compiled replacement is attached). -/
opaque urlParse : List Std.U8 → core.result.Result url.Url url.parser.ParseError :=
  fun _ => core.result.Result.Err url.parser.ParseError.EmptyHost

/-- **Host of a URL** (opaque): `urlHost u` is the value of `url::Url::host` on `u`
(`url-2.5.9/src/lib.rs` lines 1200–1207: `None` for `HostInternal::None`, otherwise the domain
as the slice `host_start..host_end` of the serialization, or the parsed IPv4 or IPv6 address).
Opaque because `url.Url` is abstract. Placeholder for compiled evaluation: `None` (see
`urlParse`). Review rule (UTF-8 premise (ii)(b), translation patch 05; the full rule at
`ExtModel.IsUtf8`): a statement may assume, as a
premise, `ExtModel.IsUtf8 d.val` for the domain `d` of `urlHost u = some (url.host.Host.Domain d)`
(the Rust `&str` invariant: `Url::host` returns a `Host<&str>`); no axiom states it, and a
statement that needs it names this premise in this form. -/
opaque urlHost : url.Url → Option (url.host.Host Str) :=
  fun _ => none

/-- **Host string of a URL** (opaque): `urlHostStr u` is the value of `url::Url::host_str` on `u`
(`url-2.5.9/src/lib.rs` lines 1161–1167: the slice `host_start..host_end` of the serialization if
the URL has a host, otherwise `None`; an IPv6 host keeps its brackets). Opaque because `url.Url`
is abstract; its relation to `urlHost` is not stated (a statement that needs it takes it as a
hypothesis). Placeholder for compiled evaluation: `None` (see `urlParse`). Review rule (UTF-8
premise (ii)(b), as at `urlHost`): a statement may assume, as a premise, `ExtModel.IsUtf8 h.val` for
`urlHostStr u = some h` (`Url::host_str` returns an `Option<&str>`); no axiom states it. -/
opaque urlHostStr : url.Url → Option Str :=
  fun _ => none

/-- **The operating-system resolver** (opaque): the value `Lookup(Arc::new(SystemResolver))`
that `metadata_resolver::prim::system_lookup` returns (`SystemResolver` resolves a name with
`tokio::task::spawn_blocking(move || (host.as_str(), 0).to_socket_addrs())`, the blocking
`std::net::ToSocketAddrs` lookup on a blocking thread; `metadata_resolver.rs` lines 78–89 at
upstream `7caec76`). Opaque because `Lookup` is abstract (`Rmcp.TypesExternal`): the
translated code only stores it; the async `resolve` that calls it is not translated. Unlike
`nowMs` this is one fixed value in Rust as well (a unit struct behind a new `Arc`; the pointer
identity of the `Arc` is not modelled, as for `alloc.sync.Arc`), so no review rule applies.
Noncomputable: `Lookup` is only known to be nonempty, so there is no placeholder to compile. -/
noncomputable opaque systemLookup : transport.auth.metadata_resolver.Lookup

/-- **Proxy environment reading** (opaque): the value of
`metadata_resolver::prim::proxy_env_values`, the values of the proxy environment variables
`HTTP_PROXY`, `http_proxy`, `HTTPS_PROXY`, `https_proxy`, `ALL_PROXY`, `all_proxy` that are set
and Unicode, in this order (`PROXY_ENV_VARS.iter().filter_map(|var| std::env::var(var).ok())`,
collected). A single constant cannot model that two readings differ (the environment can change
between them), and it makes `MetadataAddressResolver::new` (N03), the only function that calls
`proxy_env_values`, pure. Review rule (human decision 2026-11-25: the rule of `nowMs` extended to
the environment; `formal/README.md`, "Trusted base"): no statement has a premise or conclusion
about the value of `proxyEnvValues` or relates two readings; a statement may name
`proxyEnvValues`, `…prim.proxy_env_values` or `…MetadataAddressResolver.new` only to say that
`new` passes the values read to `with_proxy_hosts`, so that it holds for every value of the
environment, besides the model's own spec theorem `prim.proxy_env_values_spec`
(`result = proxyEnvValues`; human decision 2026-11-25). Human decision 2026-11-26: a statement
may also state a fact about `MetadataAddressResolver::new` that does not depend on the proxy
environment, such as that the fields of the result not set from the proxy values (`base_ip`,
`base_classes`, `lookup`) equal those of `with_base_url u` with the lookup `systemLookup`, proved
from the body for every value of `proxyEnvValues`; nothing is assumed about `proxyEnvValues`
itself beyond its own spec.
Human decision 2026-11-26 (spec round 1, finding P1; an extension of this rule): for `new u = ok r`,
and with no premise on the value of `ExtModel.proxyEnvValues`, a statement may also conclude (1)
that `r.unfiltered_hosts` (as bytes) equals `ExtModel.proxyEnvValues.val.filterMap (fun p =>
Defs.MetadataResolver.proxyHost (Defs.utf8Bytes p))` (`Defs.MetadataResolver.proxyHost` is defined
in `formal/proofs/Proofs/Defs/MetadataResolver.lean`), naming `proxyEnvValues` only as the values
`new` reads and passes to `with_proxy_hosts`; (2) the invariant that every unfiltered host of
`new`'s result is a normalized host; (3) production security theorems about resolvers built by `new`
(e.g. a filtered host's returned addresses are Public for a non-localhost domain base). Still no
premise on, and no other statement about, the value of `proxyEnvValues`.
Human decision 2026-11-26 (spec round 3, R1): for `new u = ok r`, statements of the form `host ∈
r.unfiltered_hosts ↔ Defs.utf8Bytes host ∈ ExtModel.proxyEnvValues.val.filterMap
(Defs.MetadataResolver.proxyHost ∘ Defs.utf8Bytes)` and premises `host ∉ r.unfiltered_hosts` in
production theorems count as restatements of items (1) and (3).
Human decision 2026-11-26 (spec sign-off, T1): premises of the form `Defs.utf8Bytes host ∈
ExtModel.proxyEnvValues.val.filterMap (Defs.MetadataResolver.proxyHost ∘ Defs.utf8Bytes)` (the host
is a configured proxy host; used by
`MetadataAddressResolver.allowed_addresses_eq_ok_some_of_new_eq_ok_of_mem_proxyHosts`) also count as
restatements of P1.
The value given here (no variable set) only shows that the type is
inhabited; an
`opaque` constant does not unfold to it, and compiled evaluation returns it, not the
environment. -/
opaque proxyEnvValues : alloc.vec.Vec String :=
  alloc.vec.Vec.new String

/-- The bytes of `l` without its trailing `.` bytes (46): `str::trim_end_matches('.')` on the
bytes (`'.'` is ASCII, and in UTF-8 the byte 46 occurs only as `'.'`). -/
def dropTrailingDots (l : List Std.U8) : List Std.U8 :=
  (l.reverse.dropWhile (fun b => decide (b.val = 46))).reverse

/-- A slice without its trailing dots fits in a slice. -/
theorem length_dropTrailingDots_le_max (s : Slice Std.U8) :
    (dropTrailingDots s.val).length ≤ Usize.max := by
  have hs := s.property
  have hd := (List.dropWhile_sublist (l := s.val.reverse) (fun b => decide (b.val = 46))).length_le
  rw [dropTrailingDots, List.length_reverse]
  rw [List.length_reverse] at hd
  omega

/-- `u8::to_ascii_lowercase`: `A`–`Z` (65–90) to `a`–`z`, every other byte unchanged
(`core/src/num/mod.rs` lines 710–713, `u8::to_ascii_lowercase`: `*self | (self.is_ascii_uppercase()
as u8 * ASCII_CASE_MASK)`, with `ASCII_CASE_MASK = 0b0010_0000`, line 584; for `A`–`Z` bit 5 is
clear, so the `|` adds 32). -/
def asciiLowercase (b : Std.U8) : Std.U8 :=
  if 65 ≤ b.val ∧ b.val ≤ 90 then byte (b.val + 32) else b

end ExtModel

/-- [core::net::ip_addr::{impl core::cmp::PartialEq<core::net::ip_addr::IpAddr> for core::net::ip_addr::IpAddr}::eq]:
    Source: '/rustc/library/core/src/net/ip_addr.rs', lines 29:26-29:35
    Name pattern: [core::net::ip_addr::{core::cmp::PartialEq<core::net::ip_addr::IpAddr, core::net::ip_addr::IpAddr>}::eq]
    Visibility: public

**Model:** the derived equality of `enum IpAddr { V4(Ipv4Addr), V6(Ipv6Addr) }` (`ip_addr.rs`
lines 29–37: `#[derive(PartialEq)]`): equal variants with equal addresses. `Ipv4Addr` equality is
the derived equality of its octets (lines 71–76), `Ipv6Addr` equality that of its sixteen
octets (lines 165–170), which holds exactly when the eight segments of the model are equal (the
segments are a bijective image of the octets, `Rmcp.TypesExternal`). -/
@[rust_fun
  "core::net::ip_addr::{core::cmp::PartialEq<core::net::ip_addr::IpAddr, core::net::ip_addr::IpAddr>}::eq"]
def core.net.ip_addr.IpAddr.Insts.CoreCmpPartialEqIpAddr.eq (self : core.net.ip_addr.IpAddr)
    (other : core.net.ip_addr.IpAddr) : Result Bool :=
  match self, other with
  | core.net.ip_addr.IpAddr.V4 a, core.net.ip_addr.IpAddr.V4 b =>
    ok (decide (a.addrOctets.val = b.addrOctets.val))
  | core.net.ip_addr.IpAddr.V6 a, core.net.ip_addr.IpAddr.V6 b =>
    ok (decide (a.addrSegments.val = b.addrSegments.val))
  | core.net.ip_addr.IpAddr.V4 _, core.net.ip_addr.IpAddr.V6 _ => ok false
  | core.net.ip_addr.IpAddr.V6 _, core.net.ip_addr.IpAddr.V4 _ => ok false

/-- [core::net::ip_addr::IpAddr::V4]:
    Source: '/rustc/library/core/src/net/ip_addr.rs', lines 33:4-33:6
    Name pattern: [core::net::ip_addr::IpAddr::V4]

**Model:** the variant constructor `IpAddr::V4` used as a function (line 33), which builds the
value and never fails. -/
@[rust_fun "core::net::ip_addr::IpAddr::V4"]
def core.net.ip_addr.IpAddr.V4.constructor (a : core.net.ip_addr.Ipv4Addr) :
    Result core.net.ip_addr.IpAddr :=
  ok (core.net.ip_addr.IpAddr.V4 a)

/-- [core::net::ip_addr::IpAddr::{impl core::ops::function::FnOnce<(core::net::ip_addr::Ipv4Addr,), core::net::ip_addr::IpAddr> for core::net::ip_addr::IpAddr::V4}::call_once]:
    Source: '/rustc/library/core/src/net/ip_addr.rs', lines 33:4-33:6
    Name pattern: [core::net::ip_addr::IpAddr::{core::ops::function::FnOnce<@, (core::net::ip_addr::Ipv4Addr), core::net::ip_addr::IpAddr>}::call_once]

**Model:** calls the function item on the argument (the compiler-provided `FnOnce` impl of a
function item; here the item is the constructor `IpAddr::V4`, passed by `Option::map_or` in
`AddressClass::of`). Signature: the template that Aeneas generates prints the first parameter
without parentheses, `Ipv4Addr → Result IpAddr → Ipv4Addr → Result IpAddr`, which does not
match the use in `Rmcp.Funs` (`FnOnce (Ipv4Addr → Result IpAddr) Ipv4Addr IpAddr`, whose
`call_once` takes the function first); the definition has the type of that use. -/
@[rust_fun
  "core::net::ip_addr::IpAddr::{core::ops::function::FnOnce<@, (core::net::ip_addr::Ipv4Addr), core::net::ip_addr::IpAddr>}::call_once"]
def P.Insts.CoreOpsFunctionFnOnceTupleIpv4AddrIpAddr.call_once
    (f : core.net.ip_addr.Ipv4Addr → Result core.net.ip_addr.IpAddr)
    (a : core.net.ip_addr.Ipv4Addr) : Result core.net.ip_addr.IpAddr :=
  f a

/-- [core::net::socket_addr::{core::net::socket_addr::SocketAddr}::ip]:
    Source: '/rustc/library/core/src/net/socket_addr.rs', lines 193:4-193:36
    Name pattern: [core::net::socket_addr::{core::net::socket_addr::SocketAddr}::ip]
    Visibility: public

**Model:** the IP address of either variant (lines 193–198: `SocketAddr::V4(ref a) =>
IpAddr::V4(*a.ip())`, `SocketAddr::V6(ref a) => IpAddr::V6(*a.ip())`; `ip()` returns the field
`ip`, lines 394–396 and 492–494). -/
@[rust_fun "core::net::socket_addr::{core::net::socket_addr::SocketAddr}::ip"]
def core.net.socket_addr.SocketAddr.ip (self : core.net.socket_addr.SocketAddr) :
    Result core.net.ip_addr.IpAddr :=
  match self with
  | core.net.socket_addr.SocketAddr.V4 a => ok (core.net.ip_addr.IpAddr.V4 a.addrIp)
  | core.net.socket_addr.SocketAddr.V6 a => ok (core.net.ip_addr.IpAddr.V6 a.addrIp)

/-- [core::option::{core::option::Option<T>}::map_or]:
    Source: '/rustc/library/core/src/option.rs', lines 1224:4-1227:28
    Name pattern: [core::option::{core::option::Option<@T>}::map_or]
    Visibility: public

**Model:** `Some(t) ↦ f(t)` through the `FnOnce` instance (its failure propagates), `None ↦
default` (lines 1224–1233). -/
@[rust_fun "core::option::{core::option::Option<@T>}::map_or"]
def core.option.Option.map_or {T : Type} {U : Type} {F : Type}
    (opsfunctionFnOnceFTupleTUInst : core.ops.function.FnOnce F T U) (self : Option T)
    (default : U) (f : F) : Result U :=
  match self with
  | some t => opsfunctionFnOnceFTupleTUInst.call_once f t
  | none => ok default

/-- [alloc::str::{str}::to_ascii_lowercase]:
    Source: '/rustc/library/alloc/src/str.rs', lines 889:4-889:46
    Name pattern: [alloc::str::{str}::to_ascii_lowercase]
    Visibility: public

**Model:** the `String` of the bytes with `A`–`Z` mapped to `a`–`z` (`ExtModel.asciiLowercase`;
lines 889–894: `self.as_bytes().to_ascii_lowercase()`, `alloc/src/slice.rs` lines 678–680, then
`String::from_utf8_unchecked`). `fail undef` if the bytes are not UTF-8, which no Rust `&str` is
(the `Str` convention; the mapping keeps UTF-8 validity in both directions). The copy has the
length of an existing slice, so it never hits the capacity-overflow panic (as
`to_ascii_uppercase`). -/
@[rust_fun "alloc::str::{str}::to_ascii_lowercase"]
def alloc.str.Str.to_ascii_lowercase (self : Str) : Result String :=
  match ExtModel.strOfBytes? (self.val.map ExtModel.asciiLowercase) with
  | some s => ok s
  | none => fail undef

/-- [alloc::string::{impl core::cmp::PartialEq<&'_0 str> for alloc::string::String}::eq]:
    Source: '/rustc/library/alloc/src/string.rs', lines 2740:12-2740:46 (expanded at lines
    2764:0-2764:25)
    Name pattern: [alloc::string::{core::cmp::PartialEq<alloc::string::String, &'0 str>}::eq]
    Visibility: public

**Model:** byte equality of the string's UTF-8 bytes and `other`
(`PartialEq::eq(&self[..], &other[..])`, lines 2740–2742, generated by `impl_eq! { String, &str
}`, line 2764: `str` equality of the two byte sequences), for every `Str`; as the model of
`String == str` (`alloc.string.String.Insts.CoreCmpPartialEqStr.eq`). -/
@[rust_fun
  "alloc::string::{core::cmp::PartialEq<alloc::string::String, &'0 str>}::eq"]
def alloc.string.String.Insts.CoreCmpPartialEqShared0Str.eq (self : String) (other : Str) :
    Result Bool :=
  ok (decide (ExtModel.utf8 self = other.val))

/-- [alloc::sync::{impl core::convert::From<alloc::vec::Vec<T>> for alloc::sync::Arc<[T]>}::from]:
    Source: '/rustc/library/alloc/src/sync.rs', lines 4212:4-4212:40
    Name pattern: [alloc::sync::{core::convert::From<alloc::sync::Arc<[@T]>, alloc::vec::Vec<@T>>}::from]
    Visibility: public

**Model:** an `Arc` holding the vector's elements as a slice (lines 4212–4226: allocate an
`ArcInner<[T]>` for `len` elements, move the elements, free the vector's buffer). The allocator
instance is not used (only `Global` occurs). Never panics within the size convention (module
docstring): `Layout::array::<T>(len)` (line 2471) succeeds for the length of an existing `Vec`,
and adding the two reference counts to the layout (`arcinner_layout_for_value_layout`, lines
416–426, "capacity overflow") overflows only for a buffer within 16 bytes of `isize::MAX`, which
is at least `2^61` bytes. Allocation failure is not modelled (memory convention). -/
@[rust_fun
  "alloc::sync::{core::convert::From<alloc::sync::Arc<[@T]>, alloc::vec::Vec<@T>>}::from"]
def alloc.sync.ArcSlice.Insts.CoreConvertFromVec.from {T : Type} {A : Type}
    (_coreallocAllocatorCloneInst : core.alloc.AllocatorClone A) (v : alloc.vec.Vec T) :
    Result (alloc.sync.Arc (Slice T)) :=
  ok { data := alloc.vec.Vec.deref v }

/-- [url::{url::Url}::parse]:
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/url-2.5.9/src/lib.rs', lines 340:4-340:64
    Name pattern: [url::{url::Url}::parse]
    Visibility: public

**Model:** `ok (urlParse input)`, an opaque value (`Self::options().parse(input)`, lines
340–342; human decision 2026-11-25: `url::Url` is opaque and the parser is not modelled, no
axiom). Stated assumption (part of the trusted base, not established): `Url::parse` returns
(`Ok` or `Err`) and does not panic; the crate documents no panic. -/
@[rust_fun "url::{url::Url}::parse"]
def url.Url.parse (input : Str) :
    Result (core.result.Result url.Url url.parser.ParseError) :=
  ok (ExtModel.urlParse input.val)

/-- [url::{url::Url}::host_str]:
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/url-2.5.9/src/lib.rs', lines 1161:4-1161:42

**Model:** `ok (urlHostStr self)`, an opaque value (lines 1161–1167: a slice of the
serialization or `None`; the slice is in bounds for every `Url` the parser builds, so the
function does not panic). -/
@[rust_fun "url::{url::Url}::host_str"]
def url.Url.host_str (self : url.Url) : Result (Option Str) :=
  ok (ExtModel.urlHostStr self)

/-- [url::{url::Url}::host]:
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/url-2.5.9/src/lib.rs', lines 1200:4-1200:44

**Model:** `ok (urlHost self)`, an opaque value (lines 1200–1207: `None`, the domain slice of the
serialization, or the parsed IPv4 or IPv6 address; no panic, as for `host_str`). -/
@[rust_fun "url::{url::Url}::host"]
def url.Url.host (self : url.Url) : Result (Option (url.host.Host Str)) :=
  ok (ExtModel.urlHost self)

/-- [rmcp::transport::auth::metadata_resolver::prim::proxy_env_values]:
    Source: 'crates/rmcp/src/transport/auth/metadata_resolver.rs', lines 280:4-285:5

**Model:** `ok proxyEnvValues`, an opaque constant (`PROXY_ENV_VARS.iter().filter_map(|var|
std::env::var(var).ok()).collect()`: `std::env::var` returns `Err` for an unset or non-Unicode
variable and does not panic for these six fixed names, `std/src/env.rs` lines 228–236; collecting
at most six `String`s cannot overflow). Review rule at `ExtModel.proxyEnvValues` (human decisions
2026-11-25 and 2026-11-26: facts about `MetadataAddressResolver::new` that do not depend on the
proxy environment may be stated, proved from its body; 2026-11-26, spec round 1, finding P1: also
`new`'s unfiltered hosts as `filterMap` of `proxyHost` over the values read, their
normalization, and security theorems about resolvers built by `new`, with no premise on the
value of `proxyEnvValues`). -/
def transport.auth.metadata_resolver.prim.proxy_env_values : Result (alloc.vec.Vec String) :=
  ok ExtModel.proxyEnvValues

/-- [rmcp::transport::auth::metadata_resolver::prim::system_lookup]:
    Source: 'crates/rmcp/src/transport/auth/metadata_resolver.rs', lines 275:4-277:5

**Model:** `ok systemLookup`, an opaque value (`super::Lookup(std::sync::Arc::new(
super::SystemResolver))`; allocation failure is not modelled). -/
noncomputable def transport.auth.metadata_resolver.prim.system_lookup :
    Result transport.auth.metadata_resolver.Lookup :=
  ok ExtModel.systemLookup

/-- [rmcp::transport::auth::metadata_resolver::prim::contains]:
    Source: 'crates/rmcp/src/transport/auth/metadata_resolver.rs', lines 270:4-272:5

**Model:** whether the bytes of `pat` occur contiguously in the bytes of `s` (`s.contains(pat)`
with a `&str` pattern: `core/src/str/mod.rs` lines 1382–1384, `pat.is_contained_in(self)`, and
`core/src/str/pattern.rs` lines 987–1015, `impl Pattern for &str`: `true` for an empty pattern,
otherwise a byte search, `memchr`, `simd_contains` or `StrSearcher`, or byte equality if the
pattern is not shorter than the haystack). Defined on every `Str`. -/
def transport.auth.metadata_resolver.prim.contains (s : Str) (pat : Str) : Result Bool :=
  ok (decide (pat.val <:+: s.val))

/-- [rmcp::transport::auth::metadata_resolver::prim::trim_end_dots]:
    Source: 'crates/rmcp/src/transport/auth/metadata_resolver.rs', lines 262:4-264:5

**Model:** the bytes of `s` without its trailing `.` bytes (`ExtModel.dropTrailingDots`;
`s.trim_end_matches('.')`: `core/src/str/mod.rs` lines 2643–2654, the prefix up to the end of
the last char that the `CharSearcher` for `'.'` rejects from the back, `core/src/str/pattern.rs`
lines 330–338; `'.'` is the single byte 46, which in UTF-8 occurs only as that char). Defined on
every `Str`. -/
def transport.auth.metadata_resolver.prim.trim_end_dots (s : Str) : Result Str :=
  ok (Slice.from (ExtModel.dropTrailingDots s.val) (ExtModel.length_dropTrailingDots_le_max s))

/-- [rmcp::transport::auth::metadata_resolver::prim::ends_with]:
    Source: 'crates/rmcp/src/transport/auth/metadata_resolver.rs', lines 266:4-268:5

**Model:** whether the bytes of `suffix` are a suffix of the bytes of `s` (`s.ends_with(suffix)`
with a `&str` pattern: `core/src/str/mod.rs` lines 1445–1450, `pat.is_suffix_of(self)`, and
`core/src/str/pattern.rs` lines 1030–1035: `haystack.as_bytes().ends_with(self.as_bytes())`).
Defined on every `Str`. -/
def transport.auth.metadata_resolver.prim.ends_with (s : Str) (suffix : Str) : Result Bool :=
  ok (decide (suffix.val <:+ s.val))

/-! ## `auth.rs` OAuth metadata URL and issuer checks (A04–A10, translation patch 06)

External functions reached by the targets A04 `is_http_url`, A05 `is_disallowed_metadata_host`,
A06 `is_allowed_metadata_url`, A07 `resolve_resource_metadata_url`, A08
`check_authorization_response_issuer`, A09 `check_authorization_metadata_issuer` and A10
`check_resource_metadata_resource` of `crates/rmcp/src/transport/auth.rs` and their helpers
(human decisions 2026-11-26 and 2026-11-27, AD1–AD8). Translation patch 06 adds the private
module `auth::prim`, whose ten functions (`Source:` lines refer to the patched copy, patch 06 on top of patches
01–05) are opaque in the translation and modelled here: five `str` wrappers, the `url` rewriting
of an issuer and four `tracing` events. The remaining code calls `Option::zip`,
`str::eq_ignore_ascii_case` and seven functions of the opaque type `url::Url` of `url 2.5.9`.
Human decision AD4 (2026-11-26) fixes which values are opaque: the URL components
`ExtModel.urlScheme`, `ExtModel.urlPath`, `ExtModel.urlFragment`, `ExtModel.urlPort` and
`ExtModel.urlSerialization`, the URL resolution `ExtModel.urlJoin` and the rewritten issuer
`ExtModel.issuerUrl`; they add no axiom. Every other model is an exact definition:
`Url::port_or_known_default` over `urlPort` and `urlScheme` with the default-port table of the
`url` crate (`ExtModel.defaultPort`), `Url` equality over `urlSerialization`, `Url::clone` the
identity, `prim::trim` over the Unicode `White_Space` code points (`ExtModel.trimWhitespace`), and
the other `str` wrappers on the bytes. No law relating the opaque values (for example that
`urlScheme` and `urlSerialization` agree, or that `urlPort` is never the default port of the
scheme) is stated; a statement that needs one takes it as a hypothesis (as for patch 05, human
decision 2026-11-25).
Stated exceptions (the same three in the header of patch 06, the section docstring of
FunsExternal.lean and the module docstring of Proofs.External.Auth): (1) AD7: the `issuer_url`
setters can panic for a discovery URL longer than `u32::MAX` bytes; the model returns `ok`. (2) AD8:
the `debug_assert!` of `Url::join` (url-2.5.9 `src/parser.rs` line 1304) can panic for a `file:`
base whose last path segment is a normalized Windows drive letter; the model returns `ok`. (3)
The `tracing` side effect of the four log functions is not modelled; they return `()`. Details in the
docstrings of `transport.auth.prim.issuer_url` and `url.Url.join`, and in `formal/README.md`,
"Stated exceptions of the external models".

Crates cited (pinned in `scripts/aeneas-translate.sh`, `PINNED_DEPS`): `url 2.5.9`. -/

namespace ExtModel

/-- **Scheme of a URL** (opaque, human decision AD4 2026-11-26): `urlScheme u` is the value of
`url::Url::scheme` on `u` (`url-2.5.9/src/lib.rs` lines 902–904: `self.slice(..self.scheme_end)`,
the serialization before the first `:`, lowercase ASCII for every URL the parser builds). Opaque
because `url.Url` is abstract. Placeholder for compiled evaluation: the empty string (see
`urlParse`). -/
opaque urlScheme : url.Url → Str :=
  fun _ => Slice.new Std.U8

/-- **Path of a URL** (opaque, human decision AD4 2026-11-26): `urlPath u` is the value of
`url::Url::path` on `u` (`url-2.5.9/src/lib.rs` lines 1390–1397: the serialization from
`path_start` up to the query or fragment, or to the end). Opaque because `url.Url` is abstract.
Placeholder for compiled evaluation: the empty string (see `urlParse`). -/
opaque urlPath : url.Url → Str :=
  fun _ => Slice.new Std.U8

/-- **Fragment of a URL** (opaque, human decision AD4 2026-11-26): `urlFragment u` is the value of
`url::Url::fragment` on `u` (`url-2.5.9/src/lib.rs` lines 1544–1549: `None` without a fragment,
otherwise the serialization after the `#`; the `debug_assert!` of line 1546 holds for every URL
the parser builds). Opaque because `url.Url` is abstract. Placeholder for compiled evaluation:
`None` (see `urlParse`). -/
opaque urlFragment : url.Url → Option Str :=
  fun _ => none

/-- **Explicit port of a URL** (opaque, human decision AD4 2026-11-26): `urlPort u` is the field
`port` of `u`, the value of `url::Url::port` (`url-2.5.9/src/lib.rs` lines 1268–1270:
`self.port`; the field, line 245, is `None` when the URL has no port or the port is the default
port of a special scheme, which the parser drops). Opaque because `url.Url` is abstract.
Placeholder for compiled evaluation: `None` (see `urlParse`). -/
opaque urlPort : url.Url → Option Std.U16 :=
  fun _ => none

/-- **Serialization of a URL** (opaque, human decision AD4 2026-11-26): `urlSerialization u` is
the field `serialization : String` of `u` (`url-2.5.9/src/lib.rs` line 237), which `Url::as_str`
(lines 652–654) and `Display` (lines 2794–2799) return and on which `PartialEq` compares (lines
2830–2836). Opaque because `url.Url` is abstract; its relation to `urlScheme`, `urlPath`,
`urlFragment`, `urlPort`, `urlHost` and `urlHostStr` (all slices or parts of it) is not stated.
Placeholder for compiled evaluation: the empty string (see `urlParse`). -/
opaque urlSerialization : url.Url → String :=
  fun _ => ""

/-- **URL resolution** (opaque, human decision AD4 2026-11-26): `urlJoin base input` is the value
of `url::Url::join` on the base URL `base` and the string with the UTF-8 bytes `input`
(`url-2.5.9/src/lib.rs` lines 470–472: `Self::options().base_url(Some(self)).parse(input)`, the
WHATWG parser of `src/parser.rs` relative to `base`). Opaque because the parser is not modelled
(as `urlParse`). Placeholder for compiled evaluation: `Err(EmptyHost)` for every input (see
`urlParse`). -/
opaque urlJoin : url.Url → List Std.U8 → core.result.Result url.Url url.parser.ParseError :=
  fun _ _ => core.result.Result.Err url.parser.ParseError.EmptyHost

/-- **Issuer of a discovery URL** (opaque, human decision AD4 2026-11-26): `issuerUrl u path` is
the value of `auth::prim::issuer_url` on the URL `u` and the string with the UTF-8 bytes `path`
(`crates/rmcp/src/transport/auth.rs` lines 4567–4577 of the patched copy: a clone of `u` with
`set_query(None)`, `set_fragment(None)` and `set_path("")` if `path` is empty, otherwise
`set_path(&format!("/{path}"))`, then `to_string()`, the new serialization; `url-2.5.9/src/lib.rs`
`set_query`, `set_fragment`, `set_path`, which re-serialize through the parser). Opaque because
the `url` setters are not modelled. Placeholder for compiled evaluation: the empty string (see
`urlParse`). -/
opaque issuerUrl : url.Url → List Std.U8 → String :=
  fun _ _ => ""

/-- The default port of a URL scheme known to the `url` crate, `None` for any other scheme
(`url-2.5.9/src/parser.rs` lines 185–192, `default_port`: `"http" | "ws" => Some(80)`,
`"https" | "wss" => Some(443)`, `"ftp" => Some(21)`, `_ => None`; a `match` on `&str` compares
the bytes). -/
def defaultPort (scheme : List Std.U8) : Option Std.U16 :=
  if scheme = utf8 "http" ∨ scheme = utf8 "ws" then some 80#u16
  else if scheme = utf8 "https" ∨ scheme = utf8 "wss" then some 443#u16
  else if scheme = utf8 "ftp" then some 21#u16
  else none

/-- The Unicode code points with the property `White_Space` (Unicode 17.0.0, the version of the
pinned `core`, `core/src/unicode/unicode_data.rs` line 148), the chars for which
`char::is_whitespace` is `true` (`core/src/char/methods.rs` lines 1088–1094: `' '` and
`'\x09'..='\x0d'`, `false` for the rest of `'\0'..='\u{84}'`, otherwise
`unicode::White_Space(c)`, which is `core/src/unicode/unicode_data.rs` lines 906–929: the bits of
`WHITESPACE_MAP` give U+0085 and U+00A0 in page 0 and U+2000–U+200A, U+2028, U+2029, U+202F,
U+205F in page 0x20, plus U+1680 and U+3000): U+0009–U+000D, U+0020, U+0085, U+00A0, U+1680,
U+2000–U+200A, U+2028, U+2029, U+202F, U+205F, U+3000 (25 code points). -/
def whitespaceCodePoints : List Nat :=
  [0x09, 0x0A, 0x0B, 0x0C, 0x0D, 0x20, 0x85, 0xA0, 0x1680, 0x2000, 0x2001, 0x2002, 0x2003, 0x2004,
    0x2005, 0x2006, 0x2007, 0x2008, 0x2009, 0x200A, 0x2028, 0x2029, 0x202F, 0x205F, 0x3000]

/-- The UTF-8 encodings of `whitespaceCodePoints`, in the same order (one byte below U+0080, two
bytes `0xC2 x` below U+0800, three bytes `0xE1`/`0xE2`/`0xE3 x y` for the rest;
`Proofs.External.Auth.whitespaceUtf8_eq` proves that each is `utf8` of the one-char string). -/
def whitespaceUtf8 : List (List Std.U8) :=
  [[0x09#u8], [0x0A#u8], [0x0B#u8], [0x0C#u8], [0x0D#u8], [0x20#u8],
    [0xC2#u8, 0x85#u8], [0xC2#u8, 0xA0#u8], [0xE1#u8, 0x9A#u8, 0x80#u8],
    [0xE2#u8, 0x80#u8, 0x80#u8], [0xE2#u8, 0x80#u8, 0x81#u8], [0xE2#u8, 0x80#u8, 0x82#u8],
    [0xE2#u8, 0x80#u8, 0x83#u8], [0xE2#u8, 0x80#u8, 0x84#u8], [0xE2#u8, 0x80#u8, 0x85#u8],
    [0xE2#u8, 0x80#u8, 0x86#u8], [0xE2#u8, 0x80#u8, 0x87#u8], [0xE2#u8, 0x80#u8, 0x88#u8],
    [0xE2#u8, 0x80#u8, 0x89#u8], [0xE2#u8, 0x80#u8, 0x8A#u8], [0xE2#u8, 0x80#u8, 0xA8#u8],
    [0xE2#u8, 0x80#u8, 0xA9#u8], [0xE2#u8, 0x80#u8, 0xAF#u8], [0xE2#u8, 0x81#u8, 0x9F#u8],
    [0xE3#u8, 0x80#u8, 0x80#u8]]

/-- The length of the first of the byte strings `encs` that is a prefix of `l`, `0` if none
is. -/
def matchedPrefixLength (encs : List (List Std.U8)) (l : List Std.U8) : Nat :=
  match encs.find? (fun w => w.isPrefixOf l) with
  | some w => w.length
  | none => 0

/-- `l` without the longest run of leading byte strings of `encs` (taken greedily, the first
match of `encs` each time), with at most `n` steps. Each step drops at least one byte or stops,
so `n = l.length` steps remove the whole run. -/
def dropEncodedPrefixes (encs : List (List Std.U8)) : Nat → List Std.U8 → List Std.U8
  | 0, l => l
  | n + 1, l =>
    match matchedPrefixLength encs l with
    | 0 => l
    | k + 1 => dropEncodedPrefixes encs n (l.drop (k + 1))

/-- `str::trim` on the bytes `l`: `l` without its leading and its trailing UTF-8-encoded
`White_Space` chars (`whitespaceUtf8`). The leading run is dropped from the front, then the
trailing run of the rest from the back (the reversed encodings matched against the reversed
bytes). On a valid UTF-8 `l` (every Rust `&str`) this is exactly the char-level trim: at a char
boundary the bytes of `l` begin with the encoding of a char `c` exactly when the char there is
`c` (UTF-8 is prefix-free), and they end with it exactly when the last char is `c` (the encoding
begins with a lead byte and continues with continuation bytes only). -/
def trimWhitespace (l : List Std.U8) : List Std.U8 :=
  let front := dropEncodedPrefixes whitespaceUtf8 l.length l
  (dropEncodedPrefixes (whitespaceUtf8.map List.reverse) front.length front.reverse).reverse

/-- `dropEncodedPrefixes` returns a list no longer than its input. -/
theorem length_dropEncodedPrefixes_le (encs : List (List Std.U8)) :
    ∀ (n : Nat) (l : List Std.U8), (dropEncodedPrefixes encs n l).length ≤ l.length
  | 0, l => le_refl _
  | n + 1, l => by
    unfold dropEncodedPrefixes
    split
    · exact le_refl _
    · exact le_trans (length_dropEncodedPrefixes_le encs n _) (by rw [List.length_drop]; omega)

/-- `trimWhitespace` returns a list no longer than its input. -/
theorem length_trimWhitespace_le (l : List Std.U8) : (trimWhitespace l).length ≤ l.length := by
  unfold trimWhitespace
  simp only [List.length_reverse]
  refine le_trans (length_dropEncodedPrefixes_le _ _ _) ?_
  rw [List.length_reverse]
  exact length_dropEncodedPrefixes_le _ _ _

/-- A trimmed slice fits in a slice. -/
theorem length_trimWhitespace_le_max (s : Slice Std.U8) :
    (trimWhitespace s.val).length ≤ Usize.max :=
  le_trans (length_trimWhitespace_le s.val) s.property

/-- A slice without its leading `/` bytes fits in a slice. -/
theorem length_dropWhile_le_max (s : Slice Std.U8) (p : Std.U8 → Bool) :
    (s.val.dropWhile p).length ≤ Usize.max :=
  le_trans (List.dropWhile_sublist p).length_le s.property

end ExtModel

/-- [core::option::{core::option::Option<T>}::zip]:
    Source: '/rustc/library/core/src/option.rs', lines 1983:4-1986:28
    Name pattern: [core::option::{core::option::Option<@T>}::zip]
    Visibility: public

**Model:** `Some((a, b))` if both are `Some`, otherwise `None` (lines 1983–1992:
`match (self, other) { (Some(a), Some(b)) => Some((a, b)), _ => None }`). -/
@[rust_fun "core::option::{core::option::Option<@T>}::zip"]
def core.option.Option.zip {T : Type} {U : Type} (self : Option T) (other : Option U) :
    Result (Option (T × U)) :=
  match self, other with
  | some a, some b => ok (some (a, b))
  | _, _ => ok none

/-- [core::str::{str}::eq_ignore_ascii_case]:
    Source: '/rustc/library/core/src/str/mod.rs', lines 2859:4-2859:65
    Name pattern: [core::str::{str}::eq_ignore_ascii_case]
    Visibility: public

**Model:** whether the bytes are equal after mapping `A`–`Z` to `a`–`z`
(`ExtModel.asciiLowercase`; lines 2859–2861:
`self.as_bytes().eq_ignore_ascii_case(other.as_bytes())`, `core/src/slice/ascii.rs` lines
66–87: `false` for different lengths; otherwise, on `x86_64` with `sse2` and on `aarch64` with
`neon` (the `cfg` of lines 71–74; the translated target `x86_64-unknown-linux-gnu` has `sse2`
in its baseline, and an `aarch64` test host has `neon`) and for at least 16 bytes, the chunked
path `eq_ignore_ascii_case_chunks::<16>`, lines 125–171, and in every other case the simple loop
`eq_ignore_ascii_case_simple`, lines 92–109; both compare pairs with `u8::eq_ignore_ascii_case`, `core/src/num/mod.rs` lines 737–739:
`self.to_ascii_lowercase() == other.to_ascii_lowercase()`). The model covers both paths: the
simple loop returns `true` exactly when every pair of bytes at the same index is equal after
lowercasing; the chunked path compares every full 16-byte chunk pairwise (lines 145–152) and
then, if bytes remain, the last 16 bytes of both slices (lines 162–168: `last_chunk::<16>` is
`Some`, both lengths being at least 16, the same condition as its `debug_assert!` at line 158),
so it too compares every index of the equal-length slices (some twice) with the same per-byte
test and returns `true` exactly when all of them are equal. Equal mapped lists have equal
lengths, so the length test is part of the list equality. Defined on every `Str`. -/
@[rust_fun "core::str::{str}::eq_ignore_ascii_case"]
def core.str.Str.eq_ignore_ascii_case (self : Str) (other : Str) : Result Bool :=
  ok (decide (self.val.map ExtModel.asciiLowercase = other.val.map ExtModel.asciiLowercase))

/-- [url::{impl core::clone::Clone for url::Url}::clone]:
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/url-2.5.9/src/lib.rs', lines 226:9-226:14
    Name pattern: [url::{core::clone::Clone<url::Url>}::clone]
    Visibility: public

**Model:** `ok self` (line 226: `#[derive(Clone)]` on `struct Url`, lines 227–249: clones the
`serialization` string and copies the other fields, so the clone equals the original in every
component; `url.Url` is abstract, so the model value is the same value). Allocation failure is
not modelled (memory convention). -/
@[rust_fun "url::{core::clone::Clone<url::Url>}::clone"]
def url.Url.Insts.CoreCloneClone.clone (self : url.Url) : Result url.Url :=
  ok self

/-- [url::{url::Url}::join]:
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/url-2.5.9/src/lib.rs', lines 470:4-470:70
    Name pattern: [url::{url::Url}::join]
    Visibility: public

**Model:** `ok (urlJoin self input.val)`, an opaque value (lines 470–472; human decision AD4
2026-11-26). Stated assumption (part of the trusted base, not established; as for `Url::parse`):
`Url::join` returns (`Ok` or `Err`) and does not panic. What the source shows: the parser
converts every offset it stores with `to_u32(..)?` (`src/parser.rs` lines 1752–1758, used at
lines 427, 476, 522, 837, 844, 885, 896, 909, 926, 942, 1515, 1528 and 1630), so a component
that starts beyond `u32::MAX` bytes gives `Err(ParseError::Overflow)`, not a panic (the total
length is not checked: the last component may end beyond `u32::MAX`). Its explicit panic sites
in `src/parser.rs` are internal invariants that the assumption covers: `unwrap` at lines 554,
905, 941, 1053 and 1405, `assert!` at lines 1465 and 1485, `panic!` at line 1525, and the
`debug_assert!`s at lines 404, 445, 509, 710, 754, 1620 and 1626, active in the translated
configuration; slicing and indexing, and the callees in `src/host.rs` and the `idna` crate, are
covered by the same general assumption.

**Stated exception (human decision AD8, 2026-11-27):** the `debug_assert!` at `src/parser.rs`
line 1304 (`self.serialization.as_bytes()[segment_start - 1] == b'/'`, in the double-dot arm of
`parse_path`), active in the translated configuration, is not an invariant: for a `file:` base
whose last path segment is a normalized Windows drive letter (`pop_path`, lines 1403–1415, does
not pop it), joined with an input whose first segment is `..` or a percent-encoded form of it
(`%2e%2e`, `.%2e`, ...), `Url::join` can panic there; for example
`Url::parse("file://h/x/C:").unwrap().join("..")` and `.join("%2e%2e")` panic (reproduced
2026-11-27 with url 2.5.9 in a debug build; a release build, without debug assertions, returns
`Ok(file://h/x/C:)`). The condition is a superset description, not an exact one: for example
`Url::parse("file:///C:").unwrap().join("..")` does not panic (it returns `Ok(file:///C:/)`). A reviewer's fuzzing found 595 such panics, all with a `file:` base, all at
line 1304, none for another scheme. Rust panics and the model returns `ok`; statements about A07
assume that the base URL's scheme is `http` or `https` (AD8). -/
@[rust_fun "url::{url::Url}::join"]
def url.Url.join (self : url.Url) (input : Str) :
    Result (core.result.Result url.Url url.parser.ParseError) :=
  ok (ExtModel.urlJoin self input.val)

/-- [url::{url::Url}::scheme]:
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/url-2.5.9/src/lib.rs', lines 902:4-902:32
    Name pattern: [url::{url::Url}::scheme]
    Visibility: public

**Model:** `ok (urlScheme self)`, an opaque value (lines 902–904: a slice of the serialization,
in bounds for every `Url` the parser builds, so the function does not panic). -/
@[rust_fun "url::{url::Url}::scheme"]
def url.Url.scheme (self : url.Url) : Result Str :=
  ok (ExtModel.urlScheme self)

/-- [url::{url::Url}::port_or_known_default]:
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/url-2.5.9/src/lib.rs', lines 1300:4-1300:54
    Name pattern: [url::{url::Url}::port_or_known_default]
    Visibility: public

**Model:** the explicit port `urlPort self` if there is one, otherwise the default port of the
scheme `urlScheme self` (`ExtModel.defaultPort`) (lines 1300–1302:
`self.port.or_else(|| parser::default_port(self.scheme()))`; `parser::default_port`,
`src/parser.rs` lines 185–192). Exact over the opaque values `urlPort` and `urlScheme` (human
decision AD4 2026-11-26); never panics. -/
@[rust_fun "url::{url::Url}::port_or_known_default"]
def url.Url.port_or_known_default (self : url.Url) : Result (Option Std.U16) :=
  match ExtModel.urlPort self with
  | some p => ok (some p)
  | none => ok (ExtModel.defaultPort (ExtModel.urlScheme self).val)

/-- [url::{url::Url}::path]:
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/url-2.5.9/src/lib.rs', lines 1390:4-1390:30
    Name pattern: [url::{url::Url}::path]
    Visibility: public

**Model:** `ok (urlPath self)`, an opaque value (lines 1390–1397: a slice of the serialization,
in bounds for every `Url` the parser builds, so the function does not panic). -/
@[rust_fun "url::{url::Url}::path"]
def url.Url.path (self : url.Url) : Result Str :=
  ok (ExtModel.urlPath self)

/-- [url::{url::Url}::fragment]:
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/url-2.5.9/src/lib.rs', lines 1544:4-1544:42
    Name pattern: [url::{url::Url}::fragment]
    Visibility: public

**Model:** `ok (urlFragment self)`, an opaque value (lines 1544–1549: `None` or the slice of the
serialization after `#`; the `debug_assert!` at line 1546, active in the translated
configuration, holds for every `Url` the parser builds, so the function does not panic). -/
@[rust_fun "url::{url::Url}::fragment"]
def url.Url.fragment (self : url.Url) : Result (Option Str) :=
  ok (ExtModel.urlFragment self)

/-- [url::{impl core::cmp::PartialEq<url::Url> for url::Url}::eq]:
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/url-2.5.9/src/lib.rs', lines 2833:4-2833:38
    Name pattern: [url::{core::cmp::PartialEq<url::Url, url::Url>}::eq]
    Visibility: public

**Model:** equality of the serializations `urlSerialization` (lines 2830–2836: "URLs compare like
their serialization", `self.serialization == other.serialization`, `String` equality, i.e. equality
of the bytes). Exact over the opaque value `urlSerialization` (human decision AD4 2026-11-26). -/
@[rust_fun "url::{core::cmp::PartialEq<url::Url, url::Url>}::eq"]
def url.Url.Insts.CoreCmpPartialEqUrl.eq (self : url.Url) (other : url.Url) : Result Bool :=
  ok (decide (ExtModel.urlSerialization self = ExtModel.urlSerialization other))

/-- [rmcp::transport::auth::prim::trim]:
    Source: 'crates/rmcp/src/transport/auth.rs', lines 4545:4-4547:5

**Model:** the bytes of `s` without leading and trailing `White_Space` chars
(`ExtModel.trimWhitespace`; `s.trim()`: `core/src/str/mod.rs` lines 2186–2188,
`self.trim_matches(char::is_whitespace)`, lines 2377–2394: the slice from the start of the first
char the searcher rejects (`next_reject`, `core/src/str/pattern.rs` lines 265–273) to the end of
the last one (`next_reject_back`, lines 330–338), empty if every char matches; the searcher of a
`char` predicate, lines 902–933 and 943–948, forwards (`searcher_methods!`, lines 775–808) to
`MultiCharEqSearcher`, lines 684–721, which decodes the chars; `char::is_whitespace`,
`core/src/char/methods.rs` lines 1088–1094, and the code points at
`ExtModel.whitespaceCodePoints`). Defined on every `Str`; it equals the char-level trim on valid
UTF-8 (every Rust `&str`; see `ExtModel.trimWhitespace`). -/
def transport.auth.prim.trim (s : Str) : Result Str :=
  ok (Slice.from (ExtModel.trimWhitespace s.val) (ExtModel.length_trimWhitespace_le_max s))

/-- [rmcp::transport::auth::prim::starts_with]:
    Source: 'crates/rmcp/src/transport/auth.rs', lines 4549:4-4551:5

**Model:** whether the bytes of `pre` are a prefix of the bytes of `s` (`s.starts_with(prefix)`
with a `&str` pattern: `core/src/str/mod.rs` lines 1420–1422, `pat.is_prefix_of(self)`, and
`core/src/str/pattern.rs` lines 983–985: `haystack.as_bytes().starts_with(self.as_bytes())`).
Defined on every `Str`. -/
def transport.auth.prim.starts_with (s : Str) (pre : Str) : Result Bool :=
  ok (decide (pre.val <+: s.val))

/-- [rmcp::transport::auth::prim::strip_suffix]:
    Source: 'crates/rmcp/src/transport/auth.rs', lines 4553:4-4555:5

**Model:** `Some` of all but the last `suffix.len()` bytes if the bytes of `suffix` are a suffix
of the bytes of `s`, otherwise `None` (`s.strip_suffix(suffix)` with a `&str` pattern:
`core/src/str/mod.rs` lines 2486–2491, `suffix.strip_suffix_of(self)`, and
`core/src/str/pattern.rs` lines 1030–1050: `is_suffix_of`, i.e.
`haystack.as_bytes().ends_with(self.as_bytes())`, then `haystack[..haystack.len() - self.len()]`).
Defined on every `Str`. -/
def transport.auth.prim.strip_suffix (s : Str) (suffix : Str) : Result (Option Str) :=
  if suffix.val <:+ s.val then
    ok (some (Slice.from (s.val.take (s.val.length - suffix.val.length))
      (ExtModel.length_take_le_max s _)))
  else ok none

/-- [rmcp::transport::auth::prim::strip_dir_prefix]:
    Source: 'crates/rmcp/src/transport/auth.rs', lines 4558:4-4560:5

**Model:** `Some` of the bytes after the first `pre.len() + 1` if `s` starts with the bytes of
`pre` followed by `/` (47), otherwise `None` (`path.strip_prefix(&format!("{prefix}/"))`:
`format!` builds the `String` of the bytes of `prefix` and `/` (`str`'s `Display` writes the
bytes); `strip_prefix` with the pattern `&String`, `core/src/str/mod.rs` lines 2458–2460,
`prefix.strip_prefix_of(self)`, which the `Pattern` impl for `&String`,
`alloc/src/string.rs` lines 2691–2711, forwards to the `&str` pattern (`self[..]`, lines
2709–2711), `core/src/str/pattern.rs` lines 1019–1026 and 983–985: `is_prefix_of`, i.e.
`haystack.as_bytes().starts_with(self.as_bytes())`, then `haystack[self.len()..]`).
The `String` of `pre.len() + 1` bytes exceeds `isize::MAX` only for a prefix of `isize::MAX`
bytes, outside the size convention (module docstring). Defined on every `Str`. -/
def transport.auth.prim.strip_dir_prefix (path : Str) (pre : Str) : Result (Option Str) :=
  if pre.val ++ [47#u8] <+: path.val then
    ok (some (Slice.from (path.val.drop (pre.val.length + 1))
      (ExtModel.length_drop_le_max path _)))
  else ok none

/-- [rmcp::transport::auth::prim::trim_start_slashes]:
    Source: 'crates/rmcp/src/transport/auth.rs', lines 4562:4-4564:5

**Model:** the bytes of `s` without its leading `/` bytes (47) (`s.trim_start_matches('/')`:
`core/src/str/mod.rs` lines 2424–2431, the suffix from the start of the first char that the
`CharSearcher` for `'/'` rejects, `core/src/str/pattern.rs` lines 265–273 and 401–477, the whole
`s` consumed if there is none; `'/'` is the single byte 47, which in UTF-8 occurs only as that
char). Defined on every `Str`. -/
def transport.auth.prim.trim_start_slashes (s : Str) : Result Str :=
  ok (Slice.from (s.val.dropWhile (fun b => decide (b.val = 47)))
    (ExtModel.length_dropWhile_le_max s _))

/-- [rmcp::transport::auth::prim::issuer_url]:
    Source: 'crates/rmcp/src/transport/auth.rs', lines 4567:4-4577:5

**Model:** `ok (issuerUrl discovery_url issuer_path.val)`, an opaque value (human decision AD4
2026-11-26; the body at `ExtModel.issuerUrl`).

Panics (`url-2.5.9/src/lib.rs`). The setters store lengths with
`to_u32(self.serialization.len()).unwrap()` (`to_u32`, `src/parser.rs` lines 1752–1758), which
panics above `u32::MAX` bytes. With `None`, `set_query` (lines 1636–1666) and `set_fragment`
(lines 1581–1596) only truncate: their unwraps at lines 1646 and 1589 are on the `Some`
branches, and the one at line 1610 (`restore_already_parsed_fragment`, lines 1607–1614, which
puts back the fragment `set_query` took off) converts the length truncated at the old query or
fragment start, a `u32`. `set_path` (lines 1766–1789) converts at line 1768 the length `L` of
the URL without query and fragment, and `restore_after_path` (lines 1803–1816) at line 1804 the
length with the new path. Line 1804 cannot panic when line 1768 did not: in each branch of
`expected_issuer_for_authorization_metadata_url` the new path is `""` or `/` followed by a
substring of the old path `discovery_url.path()` that lacks the well-known segment
(`/.well-known/oauth-authorization-server/`, 40 bytes, or `/.well-known/openid-configuration`,
33 bytes, with or without the `/` after it); the setter's parser writes the bytes of a serialized
path back unchanged (they are already percent-encoded, and `%` is not encoded again), only
removes dot segments, and adds at most two bytes (`%2F` for the leading `/` of an opaque path,
line 1775, or the `/` of an empty special path), so the new length is below `L`. Line 1768
panics exactly when `L > u32::MAX`. With a query or a fragment, `L` is at most its start offset,
a `u32`. Without them, `L` is the whole length (minus the trailing spaces of an opaque path,
lines 386–410, which a URL parsed without query and fragment does not have), and `Url::parse`
and `Url::join` accept such URLs longer than `u32::MAX` bytes, since they check only the start
offsets of the components (see `url.Url.join`). For such a discovery URL `issuer_url` panics at
line 1768.

**Stated exception (human decision AD7):** for a discovery URL with neither query nor fragment
whose serialization is longer than `u32::MAX` bytes (4 GiB, inside the size convention), Rust
panics and the model returns `ok`; a statement that A09 does not fail holds in Rust only for
discovery URLs of at most `u32::MAX` bytes or with a query or fragment, and A09 statements take a
premise bounding the URL (AD7). The other panic sites cannot fire: the
`debug_assert!`s at lines 1584, 1600 and 1641 (active in the translated configuration;
`byte_at`, lines 2770–2772, reads `#` at the stored fragment start and `?` at the stored query
start) and the `assert!` at line 1609 (`take_fragment`, lines 1598–1605, has just cleared the
fragment start) hold for every `Url` the parser and the setters build; the `adjust` closure of
`restore_after_path` is not called (query and fragment starts are both `None` by then); the
path parser that `set_path` runs is covered by the stated assumption of `url.Url.join` (its AD8
exception at `src/parser.rs` line 1304 is not known to be reachable here: the new path is `/`
followed by a substring of a serialized path; a scratch fuzz run on 2026-11-27, url 2.5.9 debug
build, of this setter sequence on `file:` URLs built from drive letters and dot segments, about
2.9 million paths, found no panic).
`to_string` writes the serialization (`Display`, lines 2794–2799). Allocation failure is not
modelled (memory convention). -/
def transport.auth.prim.issuer_url (discovery_url : url.Url) (issuer_path : Str) :
    Result String :=
  ok (ExtModel.issuerUrl discovery_url issuer_path.val)

/-- [rmcp::transport::auth::prim::debug_empty_resource_metadata]:
    Source: 'crates/rmcp/src/transport/auth.rs', lines 4579:4-4581:5

**Model:** `ok ()`. Stated exception: the side effect, a `tracing` event at level `DEBUG` with
target `rmcp::transport::auth` (`debug!(target: …, …)`; it reaches the subscriber only if the
level and target are enabled), is not modelled; the function returns `()` and the event does not
change any value of the translated code. A subscriber that panics or blocks is not modelled. -/
def transport.auth.prim.debug_empty_resource_metadata : Result Unit :=
  ok ()

/-- [rmcp::transport::auth::prim::debug_unparsable_resource_metadata]:
    Source: 'crates/rmcp/src/transport/auth.rs', lines 4583:4-4588:5

**Model:** `ok ()`. Stated exception: the side effect, a `tracing` event at level `DEBUG` with
target `rmcp::transport::auth` whose message formats `value` and `error` (`ParseError`'s
`Display`), is not modelled, as at `debug_empty_resource_metadata`. -/
def transport.auth.prim.debug_unparsable_resource_metadata (_value : Str)
    (_error : url.parser.ParseError) : Result Unit :=
  ok ()

/-- [rmcp::transport::auth::prim::warn_downgraded_resource_metadata]:
    Source: 'crates/rmcp/src/transport/auth.rs', lines 4590:4-4595:5

**Model:** `ok ()`. Stated exception: the side effect, a `tracing` event at level `WARN` with
target `rmcp::transport::auth` whose message formats both URLs (`Url`'s `Display`, the
serialization), is not modelled, as at `debug_empty_resource_metadata`. -/
def transport.auth.prim.warn_downgraded_resource_metadata (_url : url.Url) (_base_url : url.Url) :
    Result Unit :=
  ok ()

/-- [rmcp::transport::auth::prim::warn_disallowed_resource_metadata]:
    Source: 'crates/rmcp/src/transport/auth.rs', lines 4597:4-4602:5

**Model:** `ok ()`. Stated exception: the side effect, a `tracing` event at level `WARN` with
target `rmcp::transport::auth` whose message formats both URLs, is not modelled, as at
`debug_empty_resource_metadata`. -/
def transport.auth.prim.warn_disallowed_resource_metadata (_url : url.Url) (_base_url : url.Url) :
    Result Unit :=
  ok ()

/-! ## `mcp_headers.rs` header-value encoding (G01–G04, translation patch 07)

External functions reached by the targets G01 `requires_base64`, G02 `is_tchar`, G03
`encode_header_value` and G04 `decode_header_value` of
`crates/rmcp/src/transport/common/mcp_headers.rs` (SEP-2243 header values; human decisions GD1
and GD2, 2026-11-27). Translation patch 07 adds the private module `mcp_headers::prim`, whose
eight functions (`Source:` lines refer to the patched copy, patch 07 on top of patches 01–06) are
opaque in the translation and modelled here, each the original expression: the control/non-ASCII
test, four `str` pattern wrappers, the `format!` of the sentinel and the `base64` engine
`BASE64_STANDARD` (encode and decode). The remaining code calls `char::is_ascii_alphanumeric`,
`<[u8]>::last` and `Option<&u8>::copied` (models below), and functions modelled in earlier
sections (`str::is_empty`, `str::as_bytes`, `<[T]>::first`, `char::from(u8)`, `str::to_owned`,
`String::deref`, `String::from_utf8`, `Option`'s `?`).
Every model is an exact definition; there is no new `opaque` constant and no axiom (GD2).
Standard padded Base64 is modelled by renaming the alphabet of the reviewed URL-safe models
`ExtModel.b64` and `ExtModel.b64Decode` (which are unchanged): `ExtModel.b64StdPad` and
`ExtModel.b64StdPadDecode`; their laws (round trip, the decoder accepts exactly the padded
encodings, every encoded byte is visible ASCII) are theorems in `Proofs.External.Base64Std`.
The control/non-ASCII test is modelled on the bytes of every `Str`
(`ExtModel.isControlOrNonAsciiByte`); on valid UTF-8 (every Rust `&str`) it equals Rust's
char-level test (theorem `Proofs.External.Base64Std.any_isControlOrNonAsciiByte_utf8`).
Stated exceptions: none (beyond the conventions above: memory, `Str`, size).

Crates cited (pinned in `scripts/aeneas-translate.sh`, `PINNED_DEPS`): `base64 0.23.1`. -/

namespace ExtModel

/-- A byte below `0x20` or above `0x7E`: on the bytes of a `&str`, the test of
`mcp_headers::prim::has_control_or_non_ascii`. A char `c` with `(c as u32) < 0x20` is the one byte
`c as u8 < 0x20`; a char with `(c as u32) > 0x7E` is either `U+007F` (the byte `0x7F`) or a
non-ASCII char, all of whose UTF-8 bytes are at least `0x80`; and every byte of valid UTF-8 below
`0x20` or above `0x7E` belongs to such a char. -/
def isControlOrNonAsciiByte (b : Std.U8) : Bool := decide (b.val < 0x20 ∨ 0x7E < b.val)

/-- The standard-alphabet symbol for a URL-safe symbol: `-` (45) ↦ `+` (43), `_` (95) ↦ `/`
(47), every other byte unchanged (`base64-0.23.1` `src/alphabet.rs` lines 251–262: `STANDARD`
and `URL_SAFE` list the same 62 symbols for the values 0–61 and differ only in the symbols for 62
and 63). -/
def urlToStd (c : Std.U8) : Std.U8 :=
  if c.val = 45 then byte 43 else if c.val = 95 then byte 47 else c

/-- The inverse renaming, `+` (43) ↦ `-` (45), `/` (47) ↦ `_` (95), every other byte unchanged. -/
def stdToUrl (c : Std.U8) : Std.U8 :=
  if c.val = 43 then byte 45 else if c.val = 47 then byte 95 else c

/-- **Padded standard Base64** (RFC 4648 Section 4): the output of `base64-0.23.1`
`BASE64_STANDARD.encode` (`src/prelude.rs` line 19: `BASE64_STANDARD` is
`general_purpose::STANDARD`; `src/engine/general_purpose/mod.rs` line 436:
`STANDARD = GeneralPurpose::new(&alphabet::STANDARD, PAD)`; line 487 and lines 337–343:
`PAD = GeneralPurposeConfig::new()`, `encode_padding = true`). `Engine::encode`
(`src/engine/mod.rs` lines 148–164) writes the unpadded symbols with `encode_with_padding`
(`src/encode.rs`) and then `=` (61) up to a multiple of 4 (`add_padding`, `src/encode.rs` lines
136–146: `(4 - unpadded_len % 4) % 4` bytes). The unpadded symbols are those of the reviewed
URL-safe model `b64` (the same engine code with the alphabet `URL_SAFE`, `NO_PAD`), renamed to
the standard alphabet by `urlToStd`. -/
def b64StdPad (x : List Std.U8) : List Std.U8 :=
  (b64 x).map urlToStd ++ List.replicate ((4 - (b64 x).length % 4) % 4) (byte 61)

/-- The symbols before the padding: `s` without a final `==`, or else without a final `=`, or
else `s`. -/
def padBody (s : List Std.U8) : List Std.U8 :=
  if s.drop (s.length - 2) = [byte 61, byte 61] then s.take (s.length - 2)
  else if s.drop (s.length - 1) = [byte 61] then s.take (s.length - 1) else s

/-- **Strict padded standard Base64 decoding**, as `base64-0.23.1` `BASE64_STANDARD.decode`
(`Engine::decode`, `src/engine/mod.rs` lines 277–301; `decode_helper` and `complete_quads_len`,
`src/engine/general_purpose/decode.rs` lines 37–90 and 184–217; `decode_suffix`,
`src/engine/general_purpose/decode_suffix.rs` lines 13–170), with the error collapsed to `none`
(`.ok()`). `PAD` has `decode_padding_mode = RequireCanonical` and
`decode_allow_trailing_bits = false` (`src/engine/general_purpose/mod.rs` lines 341–342). The
decoder decodes every quad but the last as four symbols (`=` there is `InvalidByte`), and the
last 1–4 bytes in `decode_suffix`: `=` at index 0 or 1 of that group is `InvalidByte` (line 50),
a symbol after `=` is `InvalidByte` (line 73), fewer than 2 symbols is `InvalidLength` (line 97),
`(padding + symbols) % 4 ≠ 0` is `InvalidPadding` (`RequireCanonical`, line 105), and non-zero
unused low bits of the last symbol are `InvalidLastSymbol` (line 141). So the input must have a
length divisible by 4, end in no padding, `=` or `==` after at least two symbols of the last
quad, and otherwise contain only symbols of the standard alphabet with zero trailing bits. The
model: length divisible by 4; drop the padding (`padBody`); reject the URL-safe symbols `-` and
`_` (which `stdToUrl` would otherwise accept); rename to the URL-safe alphabet and decode with the
reviewed strict model `b64Decode` (which rejects any remaining `=`, any other foreign byte, a body
length `≡ 1 (mod 4)` and non-zero trailing bits). The theorem
`Proofs.External.Base64Std.b64StdPadDecode_eq_some_iff` shows that it accepts exactly the outputs
of `b64StdPad`. -/
def b64StdPadDecode (s : List Std.U8) : Option (List Std.U8) :=
  if s.length % 4 ≠ 0 then none
  else if (padBody s).any (fun c => c.val = 45 || c.val = 95) then none
  else b64Decode ((padBody s).map stdToUrl)

/-- `padBody` only removes bytes. -/
theorem length_padBody_le (s : List Std.U8) : (padBody s).length ≤ s.length := by
  unfold padBody; split_ifs <;> simp

/-- Decoding never produces more bytes than it reads (so the result fits in a `Vec`). -/
theorem b64StdPadDecode_length_le (s l : List Std.U8) (h : b64StdPadDecode s = some l) :
    l.length ≤ s.length := by
  unfold b64StdPadDecode at h
  split_ifs at h
  have := b64Decode_length_le _ _ h
  simp only [List.length_map] at this
  exact this.trans (length_padBody_le s)

/-- The buffer that `BASE64_STANDARD.decode` allocates for an input of `n` bytes: the
conservative estimate `(n / 4 + (n % 4 > 0)) * 3` (`GeneralPurposeEstimate::new`,
`base64-0.23.1/src/engine/general_purpose/decode.rs` lines 15–21). -/
def b64StdDecodedLenEstimate (n : Nat) : Nat := (n / 4 + (if n % 4 > 0 then 1 else 0)) * 3

end ExtModel

/-- [core::char::methods::{char}::is_ascii_alphanumeric]:
    Source: '/rustc/library/core/src/char/methods.rs', lines 2184:4-2184:53
    Name pattern: [core::char::methods::{char}::is_ascii_alphanumeric]
    Visibility: public

**Model:** whether the code point is in `'0'..='9'` (48–57), `'A'..='Z'` (65–90) or
`'a'..='z'` (97–122) (`matches!(*self, '0'..='9') | matches!(*self, 'A'..='Z') |
matches!(*self, 'a'..='z')`, lines 2184–2186). -/
@[rust_fun "core::char::methods::{char}::is_ascii_alphanumeric"]
def core.char.methods.Char.is_ascii_alphanumeric (self : Char) : Result Bool :=
  ok (decide ((48 ≤ self.toNat ∧ self.toNat ≤ 57) ∨ (65 ≤ self.toNat ∧ self.toNat ≤ 90) ∨
    (97 ≤ self.toNat ∧ self.toNat ≤ 122)))

/-- [core::slice::{[T]}::last]:
    Source: '/rustc/library/core/src/slice/mod.rs', lines 283:4-283:42
    Name pattern: [core::slice::{[@T]}::last]
    Visibility: public

**Model:** the last element, `None` for the empty slice
(`if let [.., last] = self { Some(last) } else { None }`, lines 283–285). -/
@[rust_fun "core::slice::{[@T]}::last"]
def core.slice.Slice.last {T : Type} (self : Slice T) : Result (Option T) :=
  ok self.val.getLast?

/-- [core::option::{core::option::Option<&'_0 T>}::copied]:
    Source: '/rustc/library/core/src/option.rs', lines 2135:4-2137:16
    Name pattern: [core::option::{core::option::Option<&'0 @T>}::copied]
    Visibility: public

**Model:** the same option (`match self { Some(&v) => Some(v), None => None }`, lines
2135–2145). A shared borrow `&T` is its value in the translation, so `Option<&T>` and
`Option<T>` are both `Option T` here; the model is the identity on it. Its Lean type thus merges
`Option<&T>` and `Option<T>`; the `formal/CONTRIBUTING.md` rule "No models on merged types"
targets models whose value depends on which Rust type is meant (such as `size_of`), and `copied`
is the identity on the value, so the merge is harmless (lead decision, review round 1). -/
@[rust_fun "core::option::{core::option::Option<&'0 @T>}::copied"]
def core.option.OptionShared0T.copied {T : Type} (_markerCopyInst : core.marker.Copy T)
    (self : Option T) : Result (Option T) :=
  ok self

/-- [rmcp::transport::common::mcp_headers::prim::has_control_or_non_ascii]:
    Source: 'crates/rmcp/src/transport/common/mcp_headers.rs', lines 415:4-419:5

**Model:** whether some byte of `value` is below `0x20` or above `0x7E`
(`ExtModel.isControlOrNonAsciiByte`). Rust: `value.chars().any(|c| (c as u32) < 0x20 ||
(c as u32) > 0x7E)` (`str::chars`, `core/src/str/mod.rs` lines 1079–1081; `Chars::next`,
`core/src/str/iter.rs` lines 35–43, decodes one UTF-8 char; `Iterator::any`,
`core/src/iter/traits/iterator.rs` lines 2897–2910, stops at the first `true`; `c as u32` is the
code point). Defined on every `Str` (GD2); on valid UTF-8 (every Rust `&str`) it equals the
char-level test (`Proofs.External.Base64Std.any_isControlOrNonAsciiByte_utf8`). -/
def transport.common.mcp_headers.prim.has_control_or_non_ascii (value : Str) : Result Bool :=
  ok (value.val.any ExtModel.isControlOrNonAsciiByte)

/-- [rmcp::transport::common::mcp_headers::prim::starts_with]:
    Source: 'crates/rmcp/src/transport/common/mcp_headers.rs', lines 421:4-423:5

**Model:** whether the bytes of `pre` are a prefix of the bytes of `s` (`s.starts_with(prefix)`
with a `&str` pattern: `core/src/str/mod.rs` lines 1420–1422, `pat.is_prefix_of(self)`, and
`core/src/str/pattern.rs` lines 983–985: `haystack.as_bytes().starts_with(self.as_bytes())`).
Defined on every `Str`. -/
def transport.common.mcp_headers.prim.starts_with (s : Str) (pre : Str) : Result Bool :=
  ok (decide (pre.val <+: s.val))

/-- [rmcp::transport::common::mcp_headers::prim::ends_with]:
    Source: 'crates/rmcp/src/transport/common/mcp_headers.rs', lines 425:4-427:5

**Model:** whether the bytes of `suffix` are a suffix of the bytes of `s` (`s.ends_with(suffix)`
with a `&str` pattern: `core/src/str/mod.rs` lines 1445–1450, `pat.is_suffix_of(self)`, and
`core/src/str/pattern.rs` lines 1030–1035: `haystack.as_bytes().ends_with(self.as_bytes())`).
Defined on every `Str`. -/
def transport.common.mcp_headers.prim.ends_with (s : Str) (suffix : Str) : Result Bool :=
  ok (decide (suffix.val <:+ s.val))

/-- [rmcp::transport::common::mcp_headers::prim::strip_prefix]:
    Source: 'crates/rmcp/src/transport/common/mcp_headers.rs', lines 429:4-431:5

**Model:** `Some` of the bytes after `prefix` if the bytes of `prefix` are a prefix of the bytes
of `s`, otherwise `None` (`s.strip_prefix(prefix)` with a `&str` pattern: `core/src/str/mod.rs`
lines 2458–2460, `prefix.strip_prefix_of(self)`, and `core/src/str/pattern.rs` lines 1019–1026:
`is_prefix_of`, then `haystack[self.len()..]`). Defined on every `Str`. -/
def transport.common.mcp_headers.prim.strip_prefix (s : Str) (pre : Str) : Result (Option Str) :=
  if pre.val <+: s.val then
    ok (some (Slice.from (s.val.drop pre.val.length) (ExtModel.length_drop_le_max s _)))
  else ok none

/-- [rmcp::transport::common::mcp_headers::prim::strip_suffix]:
    Source: 'crates/rmcp/src/transport/common/mcp_headers.rs', lines 433:4-435:5

**Model:** `Some` of all but the last `suffix.len()` bytes if the bytes of `suffix` are a suffix
of the bytes of `s`, otherwise `None` (`s.strip_suffix(suffix)` with a `&str` pattern:
`core/src/str/mod.rs` lines 2486–2491, `suffix.strip_suffix_of(self)`, and
`core/src/str/pattern.rs` lines 1030–1050: `is_suffix_of`, then
`haystack[..haystack.len() - self.len()]`). Defined on every `Str`. -/
def transport.common.mcp_headers.prim.strip_suffix (s : Str) (suffix : Str) :
    Result (Option Str) :=
  if suffix.val <:+ s.val then
    ok (some (Slice.from (s.val.take (s.val.length - suffix.val.length))
      (ExtModel.length_take_le_max s _)))
  else ok none

/-- [rmcp::transport::common::mcp_headers::prim::wrap_sentinel]:
    Source: 'crates/rmcp/src/transport/common/mcp_headers.rs', lines 437:4-439:5

**Model:** the string `"=?base64?" ++ t ++ "?="` for the string `t` with the bytes of `encoded`
(`format!("{BASE64_HEADER_PREFIX}{encoded}{BASE64_HEADER_SUFFIX}")`; the constants are
`"=?base64?"` and `"?="`, `crates/rmcp/src/transport/common/http_header.rs` lines 13–14;
`format!`, `alloc/src/macros.rs` lines 113–119, is `alloc::fmt::format`, `alloc/src/fmt.rs`
lines 651–662, which writes the three `&str` pieces in order into a new `String` with
`write_str`, i.e. `push_str`). Subject to the `String` length limit (`ExtModel.growString`).
`fail undef` if `encoded` is not UTF-8, which no Rust `&str` is (convention `Str` above). -/
def transport.common.mcp_headers.prim.wrap_sentinel (encoded : Str) : Result String :=
  match ExtModel.strOfBytes? encoded.val with
  | some t => ExtModel.growString ("=?base64?" ++ t ++ "?=")
  | none => fail undef

/-- [rmcp::transport::common::mcp_headers::prim::base64_encode]:
    Source: 'crates/rmcp/src/transport/common/mcp_headers.rs', lines 441:4-443:5

**Model:** the padded standard Base64 symbols `ExtModel.b64StdPad` of the bytes of `value`
(ASCII, one `Char` per byte), as `BASE64_STANDARD.encode(value)` (`Engine::encode`,
`base64-0.23.1/src/engine/mod.rs` lines 148–164: a buffer of `encoded_len(len, true)` bytes,
`src/encode.rs` lines 101–129, filled by `encode_with_padding`, then
`String::from_utf8(buf).expect(..)`, which cannot fail on ASCII). `fail panic` if the result is
longer than `isize::MAX` bytes (`ExtModel.growString`): Rust then panics, either in the
`expect` of `encoded_len` (which is `None` only beyond `usize::MAX`) or in `vec![0; encoded_size]`
("capacity overflow", convention Memory above). Defined on every `Str` (it reads only the
bytes). -/
def transport.common.mcp_headers.prim.base64_encode (value : Str) : Result String :=
  ExtModel.growString
    (String.ofList ((ExtModel.b64StdPad value.val).map (fun b => Char.ofNat b.val)))

/-- [rmcp::transport::common::mcp_headers::prim::base64_decode]:
    Source: 'crates/rmcp/src/transport/common/mcp_headers.rs', lines 445:4-447:5

**Model:** `ExtModel.b64StdPadDecode` of the bytes of `value`, as
`BASE64_STANDARD.decode(value).ok()` (`Engine::decode`, `base64-0.23.1/src/engine/mod.rs` lines
277–301; the `unreachable!` on `OutputSliceTooSmall` cannot be reached, the buffer being the
conservative estimate). `fail panic` if that buffer, `ExtModel.b64StdDecodedLenEstimate` bytes
(`vec![0; estimate.decoded_len_estimate()]`, line 283, allocated before any byte is read), is
longer than `isize::MAX` bytes ("capacity overflow", convention Memory above): human decision
GD2 keeps this guard. Defined on every `Str` (it reads only the bytes). -/
def transport.common.mcp_headers.prim.base64_decode (value : Str) :
    Result (Option (alloc.vec.Vec Std.U8)) :=
  if ExtModel.maxStringBytes < ExtModel.b64StdDecodedLenEstimate value.val.length then fail panic
  else
    match h : ExtModel.b64StdPadDecode value.val with
    | none => ok none
    | some l => ok (some (alloc.vec.Vec.from l
        ((ExtModel.b64StdPadDecode_length_le _ _ h).trans value.property)))

/-! ## Elicitation schema builders (X01–X75, translation patch 08)

External functions reached by the targets X01–X75 of `crates/rmcp/src/model/elicitation_schema.rs`
(human decision XD1, 2026-11-28): the two `elicitation_schema::prim` wrappers of translation
patch 08 (opaque in the translation) and seven functions of `core` and `alloc` (`BTreeMap`'s
`default` and `insert`, `Ord`/`PartialOrd` of `String`, `Vec`'s `default`, `Debug for str`,
`slice::Iter::all`). No `opaque` constant, no axiom. Stated exceptions: `BTreeMap::insert`
assumes sorted entries with distinct keys and a total, consistent, non-failing `Ord` (true of
`Ord for String`, the only instance used); `<str as Debug>::fmt` is total, not exact. Laws and
spec theorems: `Proofs.External.ElicitationSchema`. -/

namespace ExtModel

/-- `BTreeMap::insert` on the entries of a map kept ascending by key: walking the entries in
order, compare `k` with each key through the `Ord` instance (`k.cmp(key)`, the orientation of
`find_key_index`, `alloc/src/collections/btree/search.rs` lines 225–242; failures propagate):
`Greater` continues, `Equal` replaces the value in place and returns the old one (the stored key
is kept: "the key is not updated"), `Less` inserts `(k, v)` before the entry and returns `none`;
after the last entry, append `(k, v)` and return `none`. On sorted entries and for a lawful `Ord`
this is the `BTreeMap` result; the B-tree compares `k` with fewer keys (one path through the
nodes), which gives the same result when `cmp` is a total order and does not fail. -/
def btreeInsert {K V : Type _} (ord : core.cmp.Ord K) (k : K) (v : V) :
    List (K × V) → Result (Option V × List (K × V))
  | [] => ok (none, [(k, v)])
  | (k', v') :: rest => do
    let c ← ord.cmp k k'
    match c with
    | .lt => ok (none, (k, v) :: (k', v') :: rest)
    | .eq => ok (some v', (k', v) :: rest)
    | .gt => do
      let (o, r) ← btreeInsert ord k v rest
      ok (o, (k', v') :: r)

/-- Rust's `Ord` of byte sequences (`Ord for [u8]`: lexicographic on unsigned bytes, a proper
prefix first), through `ExtModel.bytesLt`. -/
def bytesCmp (a b : List Std.U8) : Ordering :=
  if bytesLt a b then .lt else if a = b then .eq else .gt

end ExtModel

/-- [alloc::collections::btree::map::{impl core::default::Default for alloc::collections::btree::map::BTreeMap<K, V, alloc::alloc::Global>}::default]:
    Source: '/rustc/library/alloc/src/collections/btree/map.rs', lines 2608:4-2608:34
    Name pattern: [alloc::collections::btree::map::{core::default::Default<alloc::collections::btree::map::BTreeMap<@K, @V, alloc::alloc::Global>>}::default]
    Visibility: public

**Model:** the empty map (`BTreeMap::new()`, lines 2608–2610: no root, length 0, no
allocation). -/
@[rust_fun
  "alloc::collections::btree::map::{core::default::Default<alloc::collections::btree::map::BTreeMap<@K, @V, alloc::alloc::Global>>}::default"]
def alloc.collections.btree.map.BTreeMapKVGlobal.Insts.CoreDefaultDefault.default
    (K : Type _) (V : Type _) :
    Result (alloc.collections.btree.map.BTreeMap K V alloc.alloc.Global) :=
  ok { entries := [] }

/-- [alloc::collections::btree::map::{alloc::collections::btree::map::BTreeMap<K, V, A>}::insert]:
    Source: '/rustc/library/alloc/src/collections/btree/map.rs', lines 1047:4-1049:15
    Name pattern: [alloc::collections::btree::map::{alloc::collections::btree::map::BTreeMap<@K, @V, @A>}::insert]
    Visibility: public

**Model:** `ExtModel.btreeInsert` with the map's `Ord` instance (lines 1047–1058: `entry(key)`,
then `Occupied` replaces the value and returns the old one, `Vacant` inserts and returns
`None`). Stated exceptions: the entries are assumed sorted with distinct keys (every map built by
these models from `default` is, for a lawful `Ord`), and `Ord::cmp` is assumed total,
consistent and non-failing (true of `Ord for String`, the only instance used); the allocator
clone instance and allocation failure are not modelled. -/
@[rust_fun
  "alloc::collections::btree::map::{alloc::collections::btree::map::BTreeMap<@K, @V, @A>}::insert"]
def alloc.collections.btree.map.BTreeMap.insert {K : Type _} {V : Type _} {A : Type _}
    (_coreallocAllocatorCloneInst : core.alloc.AllocatorClone A)
    (corecmpOrdInst : core.cmp.Ord K) (self : alloc.collections.btree.map.BTreeMap K V A)
    (k : K) (v : V) :
    Result ((Option V) × (alloc.collections.btree.map.BTreeMap K V A)) := do
  let (o, entries) ← ExtModel.btreeInsert corecmpOrdInst k v self.entries
  ok (o, { entries })

/-- [alloc::string::{impl core::cmp::Ord for alloc::string::String}::cmp]:
    Source: '/rustc/library/alloc/src/string.rs', lines 350:36-350:39
    Name pattern: [alloc::string::{core::cmp::Ord<alloc::string::String>}::cmp]
    Visibility: public

**Model:** the order of the UTF-8 bytes (`ExtModel.bytesCmp`): `#[derive(Ord)]` on
`String { vec: Vec<u8> }` (line 350) compares the byte vectors lexicographically. Never fails. -/
@[rust_fun "alloc::string::{core::cmp::Ord<alloc::string::String>}::cmp"]
def alloc.string.String.Insts.CoreCmpOrd.cmp (self : String) (other : String) :
    Result Ordering :=
  ok (ExtModel.bytesCmp (ExtModel.utf8 self) (ExtModel.utf8 other))

/-- [alloc::string::{impl core::cmp::PartialOrd<alloc::string::String> for alloc::string::String}::partial_cmp]:
    Source: '/rustc/library/alloc/src/string.rs', lines 350:20-350:30
    Name pattern: [alloc::string::{core::cmp::PartialOrd<alloc::string::String, alloc::string::String>}::partial_cmp]
    Visibility: public

**Model:** `Some` of the `Ord` result: `#[derive(PartialOrd)]` (line 350) compares the `Vec<u8>`
fields, and `PartialOrd for [u8]` is `Some(Ord::cmp)` (`u8` is totally ordered). -/
@[rust_fun
  "alloc::string::{core::cmp::PartialOrd<alloc::string::String, alloc::string::String>}::partial_cmp"]
def alloc.string.String.Insts.CoreCmpPartialOrdString.partial_cmp (self : String)
    (other : String) : Result (Option Ordering) :=
  ok (some (ExtModel.bytesCmp (ExtModel.utf8 self) (ExtModel.utf8 other)))

/-- [alloc::vec::{impl core::default::Default for alloc::vec::Vec<T>}::default]:
    Source: '/rustc/library/alloc/src/vec/mod.rs', lines 4417:4-4417:26
    Name pattern: [alloc::vec::{core::default::Default<alloc::vec::Vec<@T>>}::default]
    Visibility: public

**Model:** the empty vector (`Vec::new()`, lines 4417–4419; no allocation). -/
@[rust_fun "alloc::vec::{core::default::Default<alloc::vec::Vec<@T>>}::default"]
def alloc.vec.Vec.Insts.CoreDefaultDefault.default (T : Type _) : Result (alloc.vec.Vec T) :=
  ok (alloc.vec.Vec.new T)

/-- [core::fmt::{impl core::fmt::Debug for str}::fmt]:
    Source: '/rustc/library/core/src/fmt/mod.rs', lines 2917:4-2917:50
    Name pattern: [core::fmt::{core::fmt::Debug<str>}::fmt]
    Visibility: public

**Model (total, not exact; a stated exception, as `ParseIntError`'s `Debug`):** `Ok(())` and the
formatter unchanged; the quoted, escaped text written (lines 2917 ff.) is not modelled.
`core::fmt::Formatter` is opaque in the Aeneas library, so no exact model exists. It is reached
only through `Result::expect` in `ElicitationSchemaBuilder::build_unchecked` (X75), whose `Err`
path is `fail panic` whatever the formatter holds (`core.result.Result.expect` of the Aeneas
library): the panic message is not modelled. -/
@[rust_fun "core::fmt::{core::fmt::Debug<str>}::fmt"]
def Str.Insts.CoreFmtDebug.fmt (_self : Str) (f : core.fmt.Formatter) :
    Result ((core.result.Result Unit core.fmt.Error) × core.fmt.Formatter) :=
  ok (core.result.Result.Ok (), f)

/-- [core::slice::iter::{impl core::iter::traits::iterator::Iterator<&'a T> for core::slice::iter::Iter<'a, T>}::all]:
    Source: '/rustc/library/core/src/slice/iter/macros.rs', lines 304:12-307:45
    Name pattern: [core::slice::iter::{core::iter::traits::iterator::Iterator<core::slice::iter::Iter<'a, @T>, &'a @T>}::all]
    Visibility: public

**Model:** calls the closure (through its `FnMut` instance, whose failures propagate) on the
remaining elements in order, stops at the first `false`, and returns whether none was found and
the iterator advanced past every element it consumed (`ExtModel.sliceIterAll`). The Rust
function is the slice override of `Iterator::all` (lines 304–313, instantiated for `Iter` by
`iterator!`, `core/src/slice/iter.rs` lines 140–148): `while let Some(x) = self.next() { if
!f(x) { return false; } } true`. As the `any` model above. -/
@[rust_fun
  "core::slice::iter::{core::iter::traits::iterator::Iterator<core::slice::iter::Iter<'a, @T>, &'a @T>}::all"]
def core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.all {T : Type} {F : Type}
    (opsfunctionFnMutFTupleSharedATBoolInst : core.ops.function.FnMut F T Bool)
    (self : core.slice.iter.Iter T) (f : F) : Result (Bool × (core.slice.iter.Iter T)) := do
  let (b, n) ← ExtModel.sliceIterAll opsfunctionFnMutFTupleSharedATBoolInst
    (self.slice.val.drop self.i) f
  ok (b, { self with i := self.i + n })

/-- [rmcp::model::elicitation_schema::prim::titles_mismatch_message]:
    Source: 'crates/rmcp/src/model/elicitation_schema.rs', lines 1814:4-1819:5

**Model:** the `format!` of the original `EnumSchemaBuilder::enum_titles`: the literal text with
`expected` and `got` in decimal (`Display for usize`: the digits, no sign, no padding), which is
Lean's `toString` of a `Nat`. The result is shorter than 200 bytes, so no capacity panic. -/
def model.elicitation_schema.prim.titles_mismatch_message (expected : Std.Usize)
    (got : Std.Usize) : Result String :=
  ok ("Provided number of titles do not match number of values: expected " ++
    toString expected.val ++ ", but got " ++ toString got.val)

/-- [rmcp::model::elicitation_schema::prim::sorted_keys]:
    Source: 'crates/rmcp/src/model/elicitation_schema.rs', lines 1821:4-1825:5

**Model:** the keys of the entries, in the map's (ascending) order, collected into a `Vec`
(`properties.keys().cloned().collect()`: `Keys` iterates in key order, `Cloned` clones each
`String`, same bytes, and `Vec::from_iter` of this `TrustedLen` iterator reserves the exact
length: `Keys` is `TrustedLen`, `alloc/src/collections/btree/map.rs` line 2050, and so is
`Cloned` of it, `core/src/iter/adapters/cloned.rs` line 138); `fail panic` when `24 * len` bytes
exceed `isize::MAX` (`ExtModel.collectVec 24`; unreachable for a map that exists). Patch 08 (E7)
calls this before the validation of X74 `ElicitationSchemaBuilder::build`, so the translated X74
returns its validation `Err` only when `24 * properties.entries.length ≤ isize::MAX`
(`ExtModel.maxStringBytes`); a spec of that `Err` path states this premise. -/
def model.elicitation_schema.prim.sorted_keys
    (properties : alloc.collections.btree.map.BTreeMap String
      model.elicitation_schema.PrimitiveSchemaDefinition alloc.alloc.Global) :
    Result (alloc.vec.Vec String) :=
  ExtModel.collectVec 24 (properties.entries.map Prod.fst)
