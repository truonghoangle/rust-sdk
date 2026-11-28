/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
module
public import Aeneas

/-!
External types of the `rmcp` translation (`Rmcp.Types` imports this module).

Started at plan step S04a from the template that Aeneas generated
(`formal/translation/Rmcp/TypesExternal_Template.lean`) for the translation of commit
`f8fb6a7` with the Charon settings of S04a part 2 (derived `Debug` impls excluded), Aeneas
`nightly-2026.08.20-5d08da4`. Since the D2 fallback (2026-11-23) the translated source is the
patched copy (patch 01 on origin/main 7caec76), which gives the same translation; the `Source:`
line numbers below refer to it. Plan steps S08–S09 replaced every placeholder of that (Phase 1)
template: each type is now a `structure` that models the fields of the Rust type; the one field
that no translated code and no model looks inside (`serde_json`'s boxed `ErrorImpl`) has an
abstract type (since translation patch 03 over the `opaque` carrier
`ExtModel.SerdeJsonErrorImplCarrier : NonemptyType`, so that the opaque outcome of
`serde_json::from_slice` can contain an error). Translation patch 03 also added the entry types
`OccupiedEntry` and `VacantEntry` of `HashMap::entry` (last section). The six external types that the Phase 2 translation (plan step S21) added were
temporary placeholders over `opaque` carrier types; plan steps S26/S27 replaced them (last
section, plan Section 18): `MaybeUninit` is an inductive type of its two union fields,
`Ipv4Addr` a structure of its four octets, `Ipv6Addr` a structure of its eight segments (a
stated change of representation), `ParseIntError` a structure of its error kind, and `Arc` a
structure holding its value; `serde_json::Value`, whose values the translated code only moves,
is a definition over the `opaque` carrier `ExtModel.SerdeJsonValue`. Translation patch 04
(targets K01–K20 of `skill.rs`) added four structures: `array::IntoIter`,
`str::Bytes`, `HashSet` and `serde_json::Map`. Translation patch 05 (targets N01, N03–N11 of
`metadata_resolver.rs`) added two structures, `SocketAddrV4` and `SocketAddrV6`, and two
abstract types over `opaque` carriers, `url::Url` (`ExtModel.UrlCarrier`) and the `rmcp`
newtype `Lookup` (`ExtModel.LookupCarrier`). Translation patch 08 (targets X01–X75 of
`elicitation_schema.rs`, human decision XD1) added the structure `BTreeMap` (its entries in key
order), and human decision XD3 the root types `F64` and `F32`, abstract over the `opaque`
carriers `ExtModel.F64Carrier` and `ExtModel.F32Carrier` (last sections). This module declares
no axiom.

The `@[rust_type]` names and the source lines in the docstrings are those Aeneas generated.
Source paths: `/rustc/library/…` is the `rust-src` of the pinned toolchain `nightly-2026-09-17`
(Aeneas upgrade, 2026-11-24: every cited `rust-src` range was compared with `nightly-2026-06-01`
and renumbered; no change of behaviour, only comments of `ArcInner` and the renaming of
`i64::from_ascii_radix` to `from_ascii_bytes_radix_impl`);
`/cargo/registry/…` is the crate at the version in the path. The justification of each model is
also recorded in `formal/trusted/evidence/README.md`.
-/
@[expose] public section
open Aeneas Aeneas.Std Result ControlFlow Error

/-- [core::time::Duration]
    Source: '/rustc/library/core/src/time.rs', lines 81:0-81:19

**Model: the two fields of the Rust struct** `pub struct Duration { secs: u64, nanos:
Nanoseconds }` (`time.rs` lines 81–84), with its documented invariant `nanos < 10^9` ("Always
0 <= nanos < NANOS_PER_SEC"; `Nanoseconds` is a `u32` restricted to that range). Used by
`SealOptions::ttl : Option<Duration>`; since translation patch 03 the private `seal_at` reads one
through the model of `Duration::as_millis` (`Rmcp.FunsExternal`), the only external model that
reads its fields. -/
@[rust_type "core::time::Duration"]
structure core.time.Duration : Type where
  /-- Whole seconds. -/
  secs : Std.U64
  /-- Sub-second nanoseconds. -/
  nanos : Std.U32
  /-- `nanos < NANOS_PER_SEC`. -/
  nanos_lt : nanos.val < 1000000000

/-- [std::collections::hash::map::HashMap]
    Source: '/rustc/library/std/src/collections/hash/map.rs', lines 245:0-250:1

**Model: association list.** `entries` lists the key-value pairs of the map; `hash_builder`
is the `S` value the Rust map stores and `alloc` the allocator of its table (std wraps
`hashbrown::HashMap { hash_builder: S, table: RawTable<(K, V), A> }`, hashbrown 0.17.1 as
pinned by the toolchain's `library/Cargo.lock`, `src/map.rs`). The order of `entries` carries
no meaning: the translated code only calls `get`, `clone`, `contains_key`, `is_empty`, `entry`
(with `VacantEntry::insert`) and `HashMap::new`, none of which reveals the table order.

The Rust invariant "no two keys are equal" is not part of the type: a generic `clone` could not
preserve a proof of it (`K::clone` is an arbitrary function). Since translation patch 03 one
translated function builds a map, `new_with_keyring` (through `HashMap::new`, `entry` and
`VacantEntry::insert`, whose models add an entry only for a key that no entry has). A statement
that needs the invariant takes it as a hypothesis (the codec-state invariant, plan Section 4) or
proves it for the maps that `new_with_keyring` builds.
`std.collections.hash.map.HashMap.get` returns the value of the first entry whose key equals
the query, which is the Rust result whenever the keys are pairwise distinct. -/
@[rust_type "std::collections::hash::map::HashMap"]
structure std.collections.hash.map.HashMap (K : Type) (V : Type) (S : Type) (A : Type) :
    Type where
  /-- The `BuildHasher` value of the map (`hash_builder` in hashbrown). -/
  hash_builder : S
  /-- The allocator of the table. -/
  alloc : A
  /-- The key-value pairs. -/
  entries : List (K × V)

/-- [std::hash::random::RandomState]
    Source: '/rustc/library/std/src/hash/random.rs', lines 35:0-35:22

**Model: the two fields of the Rust struct** `pub struct RandomState { k0: u64, k1: u64 }`
(`random.rs` lines 35–38), the SipHash keys. -/
@[rust_type "std::hash::random::RandomState"]
structure std.hash.random.RandomState : Type where
  /-- First SipHash key. -/
  k0 : Std.U64
  /-- Second SipHash key. -/
  k1 : Std.U64

/-- [std::hash::random::DefaultHasher]
    Source: '/rustc/library/std/src/hash/random.rs', lines 94:0-94:24

**Model: the keys and the bytes written so far.** The Rust value is
`DefaultHasher(SipHasher13)` (`random.rs` line 94). `SipHasher13` treats successive `write`
calls as one byte stream, and `finish` depends only on the keys and that stream
(`core/src/hash/sip.rs`, `impl Hasher for Hasher<S>`). The state is therefore modelled as the
keys and the concatenation of the written bytes; `finish` applies the opaque function
`ExtModel.sipHash13` (`Rmcp.FunsExternal`). -/
@[rust_type "std::hash::random::DefaultHasher"]
structure std.hash.random.DefaultHasher : Type where
  /-- First SipHash key. -/
  k0 : Std.U64
  /-- Second SipHash key. -/
  k1 : Std.U64
  /-- All bytes written so far, in order. -/
  written : List Std.U8

/-- [alloc::string::FromUtf8Error]
    Source: '/rustc/library/alloc/src/string.rs', lines 391:0-391:24

**Model: the `bytes` field.** The Rust struct is `FromUtf8Error { bytes: Vec<u8>, error:
Utf8Error }` (`string.rs` lines 391–394). The `error` field (the position of the first invalid
sequence) is not modelled: no translated code reads it (its only use, in `open_rs2_at`, maps
the error to `RequestStateError::InvalidKeyId` without inspecting it). -/
@[rust_type "alloc::string::FromUtf8Error"]
structure alloc.string.FromUtf8Error : Type where
  /-- The bytes that `String::from_utf8` rejected. -/
  bytes : alloc.vec.Vec Std.U8

/-- The carrier of `ExtModel.SerdeJsonErrorImpl`: an opaque type together with the fact that it
has an element (`NonemptyType`; a Rust `ErrorImpl` exists). Opaque, adds no axiom. -/
opaque ExtModel.SerdeJsonErrorImplCarrier : NonemptyType

/-- The content of a `serde_json` error (`serde_json-1.0.154/src/error.rs`, `struct ErrorImpl`
behind the `Box`). **Abstract**: no translated function and no external model inspects one;
only the opaque outcome `ExtModel.serdeJsonFromSlice` of the `serde_json::from_slice` model
(`Rmcp.FunsExternal`) may contain one, which is why the type is known to be nonempty. -/
def ExtModel.SerdeJsonErrorImpl : Type := ExtModel.SerdeJsonErrorImplCarrier.type

/-- A `serde_json` error content exists (the carrier's property). -/
instance ExtModel.SerdeJsonErrorImpl.nonempty : Nonempty ExtModel.SerdeJsonErrorImpl :=
  ExtModel.SerdeJsonErrorImplCarrier.property

/-- [serde_json::error::Error]
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/serde_json-1.0.154/src/error.rs', lines 17:0-17:16

**Model: the one field of the Rust struct** `pub struct Error { err: Box<ErrorImpl> }`
(`error.rs` lines 17–22), with the boxed content opaque (`ExtModel.SerdeJsonErrorImpl`). It
occurs only as the payload of `RequestStateError::{Serialization, Deserialization}`. -/
@[rust_type "serde_json::error::Error"]
structure serde_json.error.Error : Type where
  /-- The boxed error content. -/
  err : ExtModel.SerdeJsonErrorImpl

/-- A `serde_json` error exists (from `ExtModel.SerdeJsonErrorImpl.nonempty`). -/
instance serde_json.error.Error.nonempty : Nonempty serde_json.error.Error :=
  let ⟨e⟩ := ExtModel.SerdeJsonErrorImpl.nonempty; ⟨{ err := e }⟩

/-- [zeroize::Zeroizing]
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/zeroize-1.9.2/src/lib.rs', lines 584:0-584:41

**Model: a wrapper around the value.** The Rust type is the `repr(transparent)` tuple struct
`pub struct Zeroizing<Z: Zeroize + ?Sized>(Z)` (`lib.rs` lines 582–584). Its `Drop` impl,
which zeroizes the value when it goes out of scope, has no counterpart in the value model
(plan Section 4: zeroisation on drop is not established). -/
@[rust_type "zeroize::Zeroizing"]
structure zeroize.Zeroizing (Z : Type) : Type where
  /-- The wrapped value (the tuple field `.0`). -/
  inner : Z

/-! ## Types of the Phase 2 translation (plan steps S21, S26/S27)

The six external types that the Phase 2 translation (plan step S21) uses. Plan steps S26/S27
replaced the S21 placeholders by the models below (plan Section 18). Five are exact models of
the Rust type; `serde_json::Value` is an abstract type over an `opaque` carrier, because the
translated code only moves its values. -/

/-- [core::mem::maybe_uninit::MaybeUninit]
    Source: '/rustc/library/core/src/mem/maybe_uninit.rs', lines 355:0-355:24

**Model: the two fields of the Rust union** `pub union MaybeUninit<T> { uninit: (), value:
ManuallyDrop<T> }` (`maybe_uninit.rs` lines 355–358), as a choice between "no value" and an
initialised value. Why the type is here: it occurs only in the LLBC, in the signature of
`alloc::boxed::Box::new_uninit`, which Charon extracted as a dependency; Aeneas therefore
declares it in the template, but no generated Lean definition and no model mentions it.
Not modelled: a partly initialised value (the union's bytes may be partly written), which no
translated code observes. -/
@[rust_type "core::mem::maybe_uninit::MaybeUninit"]
inductive core.mem.maybe_uninit.MaybeUninit (T : Type) : Type where
  /-- No value has been written (the field `uninit`). -/
  | uninit : core.mem.maybe_uninit.MaybeUninit T
  /-- An initialised value (the field `value`; `ManuallyDrop<T>` is a transparent wrapper). -/
  | value (v : T) : core.mem.maybe_uninit.MaybeUninit T

/-- [core::net::ip_addr::Ipv4Addr]
    Source: '/rustc/library/core/src/net/ip_addr.rs', lines 74:0-74:19

**Model: the one field of the Rust struct** `pub struct Ipv4Addr { octets: [u8; 4] }`
(`ip_addr.rs` lines 74–76), the four octets in network order (the first octet is the leftmost
in dotted notation). The field is named `addrOctets` because the generated name of the method
`Ipv4Addr::octets` is `core.net.ip_addr.Ipv4Addr.octets`, which a field `octets` would
take. -/
@[rust_type "core::net::ip_addr::Ipv4Addr"]
structure core.net.ip_addr.Ipv4Addr : Type where
  /-- The four octets, most significant first. -/
  addrOctets : Std.Array Std.U8 4#usize

/-- [core::net::ip_addr::Ipv6Addr]
    Source: '/rustc/library/core/src/net/ip_addr.rs', lines 168:0-168:19

**Model: the eight 16-bit segments.** The Rust struct is `pub struct Ipv6Addr { octets: [u8;
16] }` (`ip_addr.rs` lines 168–170). Stated deviation of representation (plan Section 18): the
model stores the segments that `Ipv6Addr::segments` computes from the octets (lines 1525–1540:
segment `i` is the big-endian `u16` of octets `2i` and `2i + 1`). That map is a bijection
between `[u8; 16]` and `[u16; 8]`, and the translated code reads an address only through
`segments`, `is_loopback`, `is_unspecified` and `is_multicast`, whose models
(`Rmcp.FunsExternal`) are stated on the segments, so no result of a translated function
depends on the choice. The field is named `addrSegments` because a field `segments` would take
the generated name of the method `Ipv6Addr::segments`. -/
@[rust_type "core::net::ip_addr::Ipv6Addr"]
structure core.net.ip_addr.Ipv6Addr : Type where
  /-- The eight segments, most significant first. -/
  addrSegments : Std.Array Std.U16 8#usize

/-- The kinds of integer parsing error: Rust's `pub enum IntErrorKind` (`core/src/num/error.rs`
lines 88–124, `#[non_exhaustive]`), all six variants in source order. `i64::from_str` produces
only `Empty`, `InvalidDigit`, `PosOverflow` and `NegOverflow` (`core/src/num/mod.rs`, lines
1775–1863, `from_ascii_bytes_radix_impl`). A helper type of the model of `ParseIntError`: Aeneas did not need the Rust type, so
it has no generated name. -/
inductive ExtModel.IntErrorKind : Type where
  /-- The input is empty. -/
  | Empty
  /-- A byte that is not a decimal digit, or a sign alone or not in first position. -/
  | InvalidDigit
  /-- The value is above the maximum of the target type. -/
  | PosOverflow
  /-- The value is below the minimum of the target type. -/
  | NegOverflow
  /-- The value is zero, for a nonzero target type. -/
  | Zero
  /-- The value is not a power of two (conversion to an alignment). -/
  | NotAPowerOfTwo

/-- [core::num::error::ParseIntError]
    Source: '/rustc/library/core/src/num/error.rs', lines 69:0-69:24

**Model: the one field of the Rust struct** `pub struct ParseIntError { pub(super) kind:
IntErrorKind }` (`error.rs` lines 69–71), with `IntErrorKind` as `ExtModel.IntErrorKind`. -/
@[rust_type "core::num::error::ParseIntError"]
structure core.num.error.ParseIntError : Type where
  /-- The kind of the error (`ParseIntError::kind`, lines 131–133). -/
  kind : ExtModel.IntErrorKind

/-- [alloc::sync::Arc]
    Source: '/rustc/library/alloc/src/sync.rs', lines 274:0-277:1

**Model: a structure holding the shared value.** The Rust struct (`sync.rs` lines 274–281)
holds a pointer to an `ArcInner<T> { strong, weak, data: T }` (lines 400–413) and the
allocator. The value model keeps `data` only: the reference counts, the pointer identity and the
allocator (only `Global`, a unit struct, occurs) are not modelled. The translated code never
mutates the shared value, so sharing is not observable in it. One stated consequence, in the
model of `PartialEq` (`Rmcp.FunsExternal`): the pointer-equality shortcut of Rust's `Arc`
equality for `T: Eq` is not represented. -/
@[rust_type "alloc::sync::Arc"]
structure alloc.sync.Arc (T : Type) : Type where
  /-- The shared value (the field `data` of `ArcInner`). -/
  data : T

/-- The carrier of `serde_json.value.Value`: a JSON value (`serde_json-1.0.154/src/value/mod.rs`,
`pub enum Value`, lines 116–176). **Opaque**: no translated function and no external model
creates, inspects or compares one; the targets only move values of this type (the field `data :
Option Value` of `ErrorData`). -/
opaque ExtModel.SerdeJsonValue : Type

/-- [serde_json::value::Value]
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/serde_json-1.0.154/src/value/mod.rs', lines 116:0-116:14

**Model: an abstract type** (plan Section 18, "Opaque values"), the `opaque` carrier
`ExtModel.SerdeJsonValue`. Faithful for the translated code, which only moves values of this
type; a statement can say that a value is passed through unchanged and nothing more. The
`@[rust_type]` attribute needs a definition, not an `opaque` constant (Aeneas
`Aeneas/Extract/Extract.lean`, `processType`), hence the `def` over the carrier. -/
@[rust_type "serde_json::value::Value"]
def serde_json.value.Value : Type := ExtModel.SerdeJsonValue

/-! ## Types of the public `request_state.rs` API (R15 `new_with_keyring`)

The two entry types that `HashMap::entry` returns in `new_with_keyring`. Their only purpose in
the value model is to carry, through the backward functions that Aeneas generates for the
`&mut` borrow of the map, what the translated code does with the entry; the map itself is
rebuilt by the backward function of the model of `HashMap::entry` (`Rmcp.FunsExternal`). -/

/-- [std::collections::hash::map::OccupiedEntry]
    Source: '/rustc/library/std/src/collections/hash/map.rs', lines 1977:0-1982:1

**Model: the key and value of the occupied slot.** The Rust struct is `OccupiedEntry { base:
RustcOccupiedEntry<'a, K, V, A> }` (`map.rs` lines 1977–1984), i.e. hashbrown 0.17.1
`RustcOccupiedEntry { elem: Bucket<(K, V)>, table: &'a mut RawTable<(K, V), A> }`
(`src/rustc_entry.rs`): a pointer to the slot and the borrowed table. The model keeps the
slot's contents only. No translated function and no external model reads or changes an
occupied entry (`new_with_keyring` only matches `Entry::Occupied(_)`). -/
@[rust_type "std::collections::hash::map::OccupiedEntry" (mutRegions := #[0])]
structure std.collections.hash.map.OccupiedEntry (K : Type) (V : Type) (A : Type) : Type where
  /-- The key stored in the slot. -/
  key : K
  /-- The value stored in the slot. -/
  value : V

/-- [std::collections::hash::map::VacantEntry]
    Source: '/rustc/library/std/src/collections/hash/map.rs', lines 1999:0-2004:1

**Model: the key, and the value inserted through the entry.** The Rust struct is `VacantEntry {
base: RustcVacantEntry<'a, K, V, A> }` (`map.rs` lines 1999–2006), i.e. hashbrown 0.17.1
`RustcVacantEntry { hash: u64, key: K, table: &'a mut RawTable<(K, V), A> }`
(`src/rustc_entry.rs`). The hash and the borrowed table are not stored: the model of
`HashMap::entry` rebuilds the map from the original map and the final value of this entry.
`inserted` is `none` for the entry that `HashMap::entry` returns and `some v` after
`VacantEntry::insert` (in the backward function of the returned `&mut V`, `v` being the final
value of that reference); dropping a vacant entry without inserting leaves the map unchanged,
as in Rust (`rustc_entry` only reserves capacity, which the value model does not have). -/
@[rust_type "std::collections::hash::map::VacantEntry" (mutRegions := #[0])]
structure std.collections.hash.map.VacantEntry (K : Type) (V : Type) (A : Type) : Type where
  /-- The key the entry was created for (`RustcVacantEntry::key`). -/
  key : K
  /-- The value written into the new slot, if any. -/
  inserted : Option V

/-! ## Types of the public `skill.rs` API (K01–K20, translation patch 04)

The four external types that the skills targets reach (human decisions 2026-11-25). Each is a
structure of the fields of the Rust type, with the collapses stated in its docstring; none is
abstract. -/

/-- [core::array::iter::IntoIter]
    Source: '/rustc/library/core/src/array/iter.rs', lines 20:0-20:38

**Model: the array and the alive range.** The Rust struct is `IntoIter<T, N> { inner:
ManuallyDrop<InnerSized<T, N>> }` (`array/iter.rs` lines 20–22), i.e.
`PolymorphicIter<[MaybeUninit<T>; N]> { alive: IndexRange, data }`
(`array/iter/iter_inner.rs` lines 35–59) with the invariants `alive.start <= alive.end <= N`;
the elements `data[alive]` are initialised, the others have been moved out. The model keeps the
whole array (`MaybeUninit` and `ManuallyDrop` are transparent wrappers; the moved-out elements
are never read again, `alive` excludes them) and the two bounds of `alive` with both invariants.
Dropping the iterator (which drops `data[alive]`) has no counterpart in the value model. -/
@[rust_type "core::array::iter::IntoIter"]
structure core.array.iter.IntoIter (T : Type) (N : Std.Usize) : Type where
  /-- The array iterated over (`data`). -/
  data : Std.Array T N
  /-- `alive.start`: the index of the next element to yield. -/
  aliveStart : Nat
  /-- `alive.end`: one past the index of the last element not yet yielded. -/
  aliveEnd : Nat
  /-- `alive.start <= alive.end` (an invariant of `IndexRange`). -/
  aliveStart_le : aliveStart ≤ aliveEnd
  /-- `alive.end <= N`. -/
  aliveEnd_le : aliveEnd ≤ N.val

/-- [core::str::iter::Bytes]
    Source: '/rustc/library/core/src/str/iter.rs', lines 284:0-284:20

**Model: the byte-slice iterator inside.** The Rust struct is the tuple struct `pub struct
Bytes<'a>(pub(super) Copied<slice::Iter<'a, u8>>)` (`str/iter.rs` line 284), created by
`str::bytes` as `Bytes(self.as_bytes().iter().copied())` (`str/mod.rs` lines 1159–1161).
`Copied` is a transparent adapter (it holds the inner iterator only and copies each item), so
the model keeps the inner `slice::Iter<u8>` as the Aeneas library models it (the slice and the
index of the next element, `Aeneas/Std/SliceIter.lean`). -/
@[rust_type "core::str::iter::Bytes"]
structure core.str.iter.Bytes : Type where
  /-- The inner slice iterator (the field `.0` without the `Copied` wrapper). -/
  inner : core.slice.iter.Iter Std.U8

/-- [std::collections::hash::set::HashSet]
    Source: '/rustc/library/std/src/collections/hash/set.rs', lines 126:0-130:1

**Model: element list.** `elements` lists the elements of the set; `hash_builder` is the `S`
value and `alloc` the allocator. The Rust set is `HashSet { base: hashbrown::HashSet<T, S, A> }`
(lines 126–130), i.e. hashbrown 0.17.1 `HashSet { map: HashMap<T, (), S, A> }` (`src/set.rs`):
the model is the `HashMap` model (`std.collections.hash.map.HashMap`) with unit values left out.
The order of `elements` carries no meaning: the iteration order of a Rust `HashSet` is
unspecified (it depends on the random `RandomState` keys), and the translated code only calls
`HashSet::with_capacity` and `HashSet::insert`, whose result does not reveal the table order.
Review rule (lead decision 2026-11-25): no statement may depend on the order of `elements`;
statements about a set speak only of membership (`x ∈ s.elements`), of the `bool` that `insert`
returns, and of quantities that do not depend on the order (such as the length). The Rust
invariant "no two elements are equal" is not part of the type (as for `HashMap`);
`HashSet::insert` adds an element only if no equal element is present, so every set built from
`with_capacity` by `insert` satisfies it. -/
@[rust_type "std::collections::hash::set::HashSet"]
structure std.collections.hash.set.HashSet (T : Type) (S : Type) (A : Type) : Type where
  /-- The `BuildHasher` value of the set (`hash_builder` in hashbrown). -/
  hash_builder : S
  /-- The allocator of the table. -/
  alloc : A
  /-- The elements (listed in insertion order in the model; the order carries no meaning). -/
  elements : List T

/-- [serde_json::map::Map]
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/serde_json-1.0.154/src/map.rs', lines 34:0-34:20

**Model: the entries of the `BTreeMap` in key order.** The Rust struct is `pub struct Map<K, V>
{ map: MapImpl<K, V> }` (`map.rs` lines 34–36) with `MapImpl = BTreeMap<K, V>` (line 39; the
`preserve_order` feature, which would select `IndexMap`, is not enabled in the translated
configuration: `serde_json` 1.0.154 resolves without `indexmap`). `entries` lists the key-value
pairs in the order in which the `BTreeMap` iterates them, ascending by key in Rust's `String`
order (the byte order of the UTF-8 encodings, `ExtModel.bytesLt`), with pairwise distinct keys,
so that each Rust map has exactly one model value (lead decision 2026-11-25). The node structure
of the B-tree is not modelled. The invariant is not part of the type (as for `HashMap`): the
models of `Map::new` (`[]`) and `Map::insert` (`ExtModel.mapInsert`, insertion at the sorted
position) keep it, so every map built by them satisfies it (proved in
`Proofs.External.Skill`). -/
@[rust_type "serde_json::map::Map"]
structure serde_json.map.Map (K : Type) (V : Type) : Type where
  /-- The key-value pairs, ascending by key. -/
  entries : List (K × V)

/-! ## Types of the `metadata_resolver.rs` address policy (N01, N03–N11, translation patch 05)

The external types that the address-policy targets reach (human decisions 2026-11-25). The two
socket-address types are structures of the fields of the Rust types; `url::Url` and the
`rmcp` newtype `Lookup` (created by translation patch 05, opaque in the Charon settings) are
abstract types over `opaque` carriers, which add no axiom. The enums `url::host::Host` and
`url::parser::ParseError` are translated from the source of `url 2.5.9` (`Rmcp.Types`). -/

/-- [core::net::socket_addr::SocketAddrV4]
    Source: '/rustc/library/core/src/net/socket_addr.rs', lines 81:0-81:23

**Model: the two fields of the Rust struct** `pub struct SocketAddrV4 { ip: Ipv4Addr, port: u16
}` (`socket_addr.rs` lines 79–84). The fields are named `addrIp` and `addrPort` because the
generated names of the methods `SocketAddrV4::ip` and `SocketAddrV4::port` would be
`core.net.socket_addr.SocketAddrV4.ip` and `….port` (as for `Ipv4Addr.addrOctets`). -/
@[rust_type "core::net::socket_addr::SocketAddrV4"]
structure core.net.socket_addr.SocketAddrV4 : Type where
  /-- The IPv4 address (`ip`). -/
  addrIp : core.net.ip_addr.Ipv4Addr
  /-- The port (`port`). -/
  addrPort : Std.U16

/-- [core::net::socket_addr::SocketAddrV6]
    Source: '/rustc/library/core/src/net/socket_addr.rs', lines 147:0-147:23

**Model: the four fields of the Rust struct** `pub struct SocketAddrV6 { ip: Ipv6Addr, port:
u16, flowinfo: u32, scope_id: u32 }` (`socket_addr.rs` lines 145–152), named with the prefix
`addr` as for `SocketAddrV4`. -/
@[rust_type "core::net::socket_addr::SocketAddrV6"]
structure core.net.socket_addr.SocketAddrV6 : Type where
  /-- The IPv6 address (`ip`). -/
  addrIp : core.net.ip_addr.Ipv6Addr
  /-- The port (`port`). -/
  addrPort : Std.U16
  /-- The flow label (`flowinfo`). -/
  addrFlowinfo : Std.U32
  /-- The scope identifier (`scope_id`). -/
  addrScopeId : Std.U32

/-- The carrier of `url.Url`: a parsed URL (`url-2.5.9/src/lib.rs`, `pub struct Url`, lines
226–249: the serialization and the offsets and kinds of its components). **Opaque** (human
decision 2026-11-25): the URL parser is not modelled; the translated code reads a `Url` only
through `Url::host` and `Url::host_str`, whose models (`Rmcp.FunsExternal`) are opaque functions
of it. -/
opaque ExtModel.UrlCarrier : Type

/-- [url::Url]
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/url-2.5.9/src/lib.rs', lines 227:0-227:14

**Model: an abstract type** (plan Section 18, "Opaque values"), the `opaque` carrier
`ExtModel.UrlCarrier`. Since translation patch 05 only this type of the `url` crate is opaque in
the Charon settings (`"url::Url"` instead of `"url"`), so that `url::host::Host` and
`url::parser::ParseError` are translated. A statement can relate the results of `Url::parse`,
`Url::host` and `Url::host_str` only through hypotheses about the opaque functions
`ExtModel.urlParse`, `ExtModel.urlHost` and `ExtModel.urlHostStr` (human decision 2026-11-25:
laws as premises of the specs that need them). The `@[rust_type]` attribute needs a definition,
not an `opaque` constant, hence the `def` over the carrier. -/
@[rust_type "url::Url"]
def url.Url : Type := ExtModel.UrlCarrier

/-- The carrier of `transport.auth.metadata_resolver.Lookup`: an opaque type together with the
fact that it has an element (`NonemptyType`; `prim::system_lookup` returns one). Opaque, adds no
axiom. -/
opaque ExtModel.LookupCarrier : NonemptyType

/-- [rmcp::transport::auth::metadata_resolver::Lookup]
    Source: 'crates/rmcp/src/transport/auth/metadata_resolver.rs', lines 102:0-102:32

**Model: an abstract type.** The Rust type is the newtype `struct Lookup(Arc<dyn Resolve>)` that
translation patch 05 adds (hunk H1; Aeneas cannot translate the trait object `dyn Resolve`), the
DNS resolver that `MetadataAddressResolver` filters; it is opaque in the Charon settings. The
translated targets only store and move a `Lookup` (the field `lookup` of
`MetadataAddressResolver`); it is called only by the async `resolve`, which is not translated
(unverified glue). Nonempty because `prim::system_lookup` returns one
(`ExtModel.systemLookup`, `Rmcp.FunsExternal`). -/
def transport.auth.metadata_resolver.Lookup : Type := ExtModel.LookupCarrier.type

/-- A `Lookup` exists (the carrier's property). -/
instance transport.auth.metadata_resolver.instNonemptyLookup :
    Nonempty transport.auth.metadata_resolver.Lookup :=
  ExtModel.LookupCarrier.property

/-! ## Types of the elicitation schema builders (X01–X75, translation patch 08) -/

/-- [alloc::collections::btree::map::BTreeMap]
    Source: '/rustc/library/alloc/src/collections/btree/map.rs', lines 189:0-193:1
    Name pattern: [alloc::collections::btree::map::BTreeMap]
    Visibility: public

**Model: the entries of the map in key order** (as `serde_json.map.Map`, whose Rust type is a
`BTreeMap<String, Value>`). The Rust struct holds the root node, the length and the allocator
(lines 189–203). `entries` lists the key-value pairs in the order in which the `BTreeMap`
iterates them, ascending by the `Ord` instance of `K` with which the map is used (for `String`
keys, the byte order of the UTF-8 encodings, `ExtModel.bytesCmp`), with pairwise distinct keys,
so that each Rust map has exactly one model value (human decision XD1, 2026-11-28). The node
structure and the allocator `A` (always `Global` in the translation) are not modelled. The
invariant is not part of the type (as for `serde_json.map.Map`): the models of
`BTreeMap::default` (`[]`) and `BTreeMap::insert` (`ExtModel.btreeInsert`, insertion at the
sorted position) keep it for a lawful `Ord` (proved for `String` keys in
`Proofs.External.ElicitationSchema`). -/
@[rust_type "alloc::collections::btree::map::BTreeMap"]
structure alloc.collections.btree.map.BTreeMap (K : Type) (V : Type) (A : Type) : Type where
  /-- The key-value pairs, ascending by key. -/
  entries : List (K × V)

/-! ## Floating-point types (human decision XD3, 2026-11-28)

The pinned Aeneas library defines no type for Rust's `f32` and `f64`, yet Aeneas prints them as
`F32` and `F64` in the generated `Rmcp.Types` (the field `priority : Option F32` of
`model.annotated.Annotations`, and `minimum`, `maximum`, `default : Option F64` of
`model.elicitation_schema.NumberSchema`). They are declared here, at the root (where the
generated code, inside `namespace rmcp`, finds them), as abstract types over `opaque` carriers,
which add no axiom. No translated target and no external model creates, reads or compares a
float: the targets X01–X75 only move the `Option` fields of `NumberSchema` and `Annotations`
values they receive (the `f64` builders of `NumberSchema` are not targets). No statement may
inspect a value of these types (there is nothing to inspect: no operation is declared). The
library `Rmcp` is built with `autoImplicit = false` (`formal/lakefile.toml`), so a type name
missing in the translation is an error and not an automatically bound variable, as these two
were before. -/

/-- The carrier of `F64`: a Rust `f64` (IEEE 754 binary64), an opaque type together with the fact
that it has an element (`NonemptyType`, as `ExtModel.LookupCarrier`; every IEEE 754 format has
values). **Opaque**: never created, read or compared by the translated code or a model. Adds no
axiom. -/
opaque ExtModel.F64Carrier : NonemptyType

/-- Rust's `f64`, which the pinned Aeneas prints as `F64` without defining it (human decision
XD3). **Model: an abstract type** over the `opaque` carrier `ExtModel.F64Carrier`; the
translated targets only move values of it (the `Option F64` fields of `NumberSchema`). -/
def F64 : Type := ExtModel.F64Carrier.type

/-- An `F64` exists (the carrier's property). -/
instance instNonemptyF64 : Nonempty F64 :=
  ExtModel.F64Carrier.property

/-- The carrier of `F32`: a Rust `f32` (IEEE 754 binary32), an opaque type together with the fact
that it has an element (`NonemptyType`, as `ExtModel.LookupCarrier`; every IEEE 754 format has
values). **Opaque**: never created, read or compared by the translated code or a model. Adds no
axiom. -/
opaque ExtModel.F32Carrier : NonemptyType

/-- Rust's `f32`, which the pinned Aeneas prints as `F32` without defining it (human decision
XD3). **Model: an abstract type** over the `opaque` carrier `ExtModel.F32Carrier`; the
translated code only moves values of it (the field `priority : Option F32` of
`model.annotated.Annotations`). -/
def F32 : Type := ExtModel.F32Carrier.type

/-- An `F32` exists (the carrier's property). -/
instance instNonemptyF32 : Nonempty F32 :=
  ExtModel.F32Carrier.property
