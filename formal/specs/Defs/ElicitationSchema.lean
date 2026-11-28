/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
module
public import Aeneas
public import Rmcp.Types
public import Rmcp.FunsExternal
public import Defs.Bytes

@[expose] public section

/-!
# Definitions for the `elicitation_schema.rs` statements (X01–X75)

Signed off by the spec owner (Hoang Le Truong) on 2026-11-28 (decision XS6) together with the
statements; drafted by AI (Claude Code, `claude-opus-5-5`) for the specification stage of the
elicitation schema builders, revised in round 1b (decisions XS1–XS4), round 1 fixes (SR1–SR5,
XS5) and round 2 fixes (SR9–SR14).

The vocabulary of the statements X01–X75 about the builders of
`crates/rmcp/src/model/elicitation_schema.rs` (restated in
`formal/specs/Specs/Model/ElicitationSchema.lean` and, for the intermediate functions and the
model laws, `formal/proofs/Proofs/Internal/Model/ElicitationSchema.lean`):
the default values the constructors start from, the error messages, the titled options built from
titles and values, the first failing check of the validating setters of a multi-select enum
builder, the lookups, key list, sortedness and size premise of a property map, and the
consistency predicates of enum builders, enum schemas and elicitation schemas.

**Strings.** A Rust `&'static str` error message is a Lean `String` compared through its UTF-8
bytes (`Defs.utf8Bytes`, the `val` of a `Str`); a Rust `String` error is a Lean `String`
(the translation's `String`).

**Maps.** A Rust `BTreeMap<String, PrimitiveSchemaDefinition>` is its list of entries in the
order of iteration (`trusted/Rmcp/TypesExternal.lean`, `BTreeMap`): in Rust ascending by key with
distinct keys (`KeysSorted`), an invariant the Lean type does not carry. The statements therefore
take `KeysSorted` only where a conclusion needs it, and then in implication form
(`KeysSorted old → KeysSorted new`).

**Floats.** `NumberSchema` (fields of type `F64`, decision XD3) appears only inside
`PrimitiveSchemaDefinition` values that are stored and returned unchanged; no definition here
inspects, compares or constructs an `F64` (the float rule of `formal/README.md`).

**Evaluation.** The data-valued definitions are computable; the `Prop`-valued ones (`KeysSorted`,
`PropertiesFit`, `PropertyInserted`, `RequiredPropertiesExist`, `ValidEnumSchemaBuilder`,
`ValidMultiSelectBuilder`, `ConsistentItems`, `ConsistentEnumSchema`,
`ConsistentElicitationSchema`) are properties.

**Internal-only definitions.** The error message of the intermediate X74
`ElicitationSchemaBuilder::build`, `requiredNotInPropertiesMsg`, is used only by internal
statements and lives in `formal/proofs/Proofs/Defs/ElicitationSchema.lean` (module
`Proofs.Defs.ElicitationSchema`, same namespace; decision XS3).

**Line citations.** "upstream" is `crates/rmcp/src/model/elicitation_schema.rs` at origin/main
`7caec76` (the working tree, unmodified, blob `929b446`); "patched" is the copy with translation
patches 01–08 applied, from which the translation is made (its line numbers are those of the
`Source:` lines of `Rmcp/Funs.lean`). They first differ at line 885 (patch 08 hunk E1).
-/

namespace Defs.ElicitationSchema

open Aeneas.Std
open Defs (utf8Bytes)
open rmcp.model.elicitation_schema (StringSchema IntegerSchema BooleanSchema ConstTitle EnumSchema
  SingleSelectEnumSchema MultiSelectEnumSchema EnumSchemaBuilder MultiSelect
  PrimitiveSchemaDefinition ElicitationSchema ElicitationSchemaBuilder)

/-! ## Default values -/

/-- The string schema with no constraint: `type: "string"` and every optional field `None`
(`impl Default for StringSchema`, upstream and patched lines 126–138). -/
def defaultStringSchema : StringSchema :=
  { type_ := (), title := none, description := none, min_length := none, max_length := none,
    format := none, default := none }

/-- The integer schema with no constraint: `type: "integer"` and every optional field `None`
(`impl Default for IntegerSchema`, upstream and patched lines 389–400). -/
def defaultIntegerSchema : IntegerSchema :=
  { type_ := (), title := none, description := none, minimum := none, maximum := none,
    default := none }

/-- The boolean schema with no constraint: `type: "boolean"`, no title, description or default
(`impl Default for BooleanSchema`, upstream and patched lines 484–493). -/
def defaultBooleanSchema : BooleanSchema :=
  { type_ := (), title := none, description := none, default := none }

/-- The single-select enum builder for `values` and nothing else set: untitled, no title,
description, titles, item bounds or default (`EnumSchemaBuilder::<SingleSelect>::new`, upstream
lines 899–904, patched 898–903, with `impl Default for EnumSchemaBuilder<SingleSelect>`,
upstream and patched lines 844–858). -/
def newEnumSchemaBuilder {T : Type} (values : alloc.vec.Vec String) : EnumSchemaBuilder T :=
  { enum_values := values, titled := false, title := none, description := none,
    enum_titles := alloc.vec.Vec.new String, min_items := none, max_items := none,
    default := alloc.vec.Vec.new String, select_type := () }

/-- The empty elicitation schema builder: no property, no required name, no title or description
(`#[derive(Default)]` on `ElicitationSchemaBuilder`, upstream line 1398, patched 1388; the
`Default` of `BTreeMap`, `Vec` and `Option`). -/
def emptyElicitationSchemaBuilder : ElicitationSchemaBuilder :=
  { properties := { entries := [] }, required := alloc.vec.Vec.new String, title := none,
    description := none }

/-! ## Error messages -/

/-- The error of `StringSchema::with_length` for `min > max` (upstream and patched line 193; also
the message of the `assert!` of `StringSchema::length`, line 202). -/
def minLengthGtMaxLengthMsg : String := "min_length must be <= max_length"

/-- The error of `IntegerSchema::with_range` for `min > max` (upstream and patched line 411; also
the message of the `assert!` of `IntegerSchema::range`, line 420). -/
def minimumGtMaximumMsg : String := "minimum must be <= maximum"

/-- The error of `EnumSchemaBuilder::enum_titles` when the numbers of titles and values differ:
the text of the `format!` with `expected` (the number of values) and `got` (the number of titles)
in decimal (upstream lines 885–889; patched line 885, `prim::titles_mismatch_message`, patched
lines 1814–1819; `Display for usize` writes the decimal digits, no sign or padding). -/
def titlesMismatchMsg (expected got : Nat) : String :=
  "Provided number of titles do not match number of values: expected " ++ Nat.repr expected ++
    ", but got " ++ Nat.repr got

/-- The error of `EnumSchemaBuilder::<SingleSelect>::with_default` for a value that is not an
enum value (upstream line 932, patched line 931). -/
def defaultNotInValuesMsg : String := "Provided default value is not in enum values"

/-- The error of `EnumSchemaBuilder::<MultiSelect>::with_default` when a default value is not an
enum value (upstream line 1002, patched line 998). -/
def defaultsNotInValuesMsg : String := "One of the provided default values is not in enum values"

/-- The error of `EnumSchemaBuilder::<MultiSelect>::{with_default, min_items}` when a non-empty
default has fewer values than the minimum (upstream lines 1011 and 1042; patched lines 1006 and
1037). -/
def defaultsBelowMinItemsMsg : String :=
  "Number of provided default values is less than min_items"

/-- The error of `EnumSchemaBuilder::<MultiSelect>::{with_default, max_items}` when a non-empty
default has more values than the maximum (upstream lines 1016–1018 and 1064; patched lines
1011–1013 and 1059). -/
def defaultsAboveMaxItemsMsg : String :=
  "Number of provided default values is greater than max_items"

/-- The error of `EnumSchemaBuilder::<MultiSelect>::min_items` for a minimum above the maximum
already set (upstream line 1038, patched line 1033). -/
def minItemsGtMaxItemsMsg : String := "Provided value is greater than max_items"

/-- The error of `EnumSchemaBuilder::<MultiSelect>::max_items` for a maximum below the minimum
already set (upstream line 1061, patched line 1056). -/
def maxItemsLtMinItemsMsg : String := "Provided value is less than min_items"

/-! ## Enum builders -/

/-- **The titled options** of a titled enum schema: the `i`-th title paired with the `i`-th value,
as many as the shorter list (`titles.into_iter().zip(values).map(|(title, const_)| ConstTitle {
const_, title }).collect()`, upstream lines 955–960 and 1098–1103; patched `const_titles`, lines
1795–1805, which stops at the end of either list). -/
def constTitles (titles values : List String) : List ConstTitle :=
  List.zipWith (fun title const_ => { const_, title }) titles values

/-- **The first failing check of `EnumSchemaBuilder::<MultiSelect>::with_default b ds`**, in the
Rust order (upstream lines 1000–1020; patched lines 994–1015), `none` if every check passes:
1. a value of `ds` is not an enum value of `b`: `defaultsNotInValuesMsg`;
2. an empty `ds` passes the remaining checks ("no default");
3. a minimum is set and `ds` has fewer values: `defaultsBelowMinItemsMsg`;
4. a maximum is set and `ds` has more values: `defaultsAboveMaxItemsMsg`.

Duplicate values in `ds` are not checked (H22). -/
def multiSelectDefaultError? {T : Type} (b : EnumSchemaBuilder T) (ds : List String) :
    Option String :=
  if !ds.all (fun d => decide (d ∈ b.enum_values.val)) then some defaultsNotInValuesMsg
  else if ds = [] then none
  else if b.min_items.any (fun lo => decide (ds.length < lo.val)) then
    some defaultsBelowMinItemsMsg
  else if b.max_items.any (fun hi => decide (hi.val < ds.length)) then
    some defaultsAboveMaxItemsMsg
  else none

/-- **The first failing check of `EnumSchemaBuilder::<MultiSelect>::min_items b value`**, in the
Rust order (upstream lines 1035–1043; patched lines 1030–1038), `none` if both pass:
1. a maximum is set and `value` exceeds it: `minItemsGtMaxItemsMsg`;
2. the default is non-empty and has fewer than `value` values: `defaultsBelowMinItemsMsg`.

The number of enum values is not checked (H22). -/
def minItemsError? {T : Type} (b : EnumSchemaBuilder T) (value : U64) : Option String :=
  if b.max_items.any (fun hi => decide (hi.val < value.val)) then some minItemsGtMaxItemsMsg
  else if b.default.val ≠ [] ∧ b.default.length < value.val then some defaultsBelowMinItemsMsg
  else none

/-- **The first failing check of `EnumSchemaBuilder::<MultiSelect>::max_items b value`**, in the
Rust order (upstream lines 1058–1065; patched lines 1053–1060), `none` if both pass:
1. a minimum is set and `value` is below it: `maxItemsLtMinItemsMsg`;
2. the default is non-empty and has more than `value` values: `defaultsAboveMaxItemsMsg`. -/
def maxItemsError? {T : Type} (b : EnumSchemaBuilder T) (value : U64) : Option String :=
  if b.min_items.any (fun lo => decide (value.val < lo.val)) then some maxItemsLtMinItemsMsg
  else if b.default.val ≠ [] ∧ value.val < b.default.length then some defaultsAboveMaxItemsMsg
  else none

/-- **The enum builder invariant** kept by every enum builder method (both select types):
1. a titled builder has as many titles as values (`enum_titles` checks it, upstream lines
   884–890; `new` and `untitled` make the builder untitled, upstream lines 849, 878);
2. every default value is an enum value (`with_default` checks it, upstream lines 931, 1000–1004).

The builder's fields are private (upstream lines 823–841), so every builder a caller holds was
made by its constructors (`EnumSchemaBuilder::<SingleSelect>::new`, `EnumSchema::builder` and
the public `impl Default for EnumSchemaBuilder<SingleSelect>`, upstream lines 844–858: untitled,
no values, no default; internal statement `EnumSchemaBuilderSingleSelect.default_valid`) and its
methods, which establish and keep the invariant. -/
def ValidEnumSchemaBuilder {T : Type} (b : EnumSchemaBuilder T) : Prop :=
  (b.titled = true → b.enum_titles.length = b.enum_values.length) ∧
    ∀ d ∈ b.default.val, d ∈ b.enum_values.val

/-- **The multi-select builder invariant**: `ValidEnumSchemaBuilder`, and
3. if both item bounds are set, the minimum is at most the maximum (`min_items` and `max_items`
   check it against each other, upstream lines 1035–1039 and 1058–1062);
4. a non-empty default respects the bounds set (`with_default`, `min_items` and `max_items` check
   it, upstream lines 1007–1020, 1041, 1063).

The number of enum values bounds neither the minimum nor the default (H22). -/
def ValidMultiSelectBuilder {T : Type} (b : EnumSchemaBuilder T) : Prop :=
  ValidEnumSchemaBuilder b ∧
    (∀ lo hi, b.min_items = some lo → b.max_items = some hi → lo.val ≤ hi.val) ∧
    (b.default.val ≠ [] →
      (∀ lo, b.min_items = some lo → lo.val ≤ b.default.length) ∧
        ∀ hi, b.max_items = some hi → b.default.length ≤ hi.val)

/-- **The item constraints of a multi-select schema are consistent**: the minimum is at most the
maximum when both are set, and a default is non-empty, made of the given values, and within the
bounds. Duplicate defaults and a minimum above the number of values are allowed (H22). -/
def ConsistentItems (minItems maxItems : Option U64) (default : Option (alloc.vec.Vec String))
    (values : List String) : Prop :=
  (∀ lo hi, minItems = some lo → maxItems = some hi → lo.val ≤ hi.val) ∧
    ∀ ds, default = some ds →
      ds.val ≠ [] ∧ (∀ d ∈ ds.val, d ∈ values) ∧
        (∀ lo, minItems = some lo → lo.val ≤ ds.length) ∧
        ∀ hi, maxItems = some hi → ds.length ≤ hi.val

/-- **A consistent enum schema**: its default (if any) is among its values (the `const_` of the
titled options), and a multi-select schema's item constraints are consistent
(`ConsistentItems`). The builders never produce a `Legacy` schema; for one, the default is among
`enum_`. -/
def ConsistentEnumSchema : EnumSchema → Prop
  | .Single (.Untitled u) => ∀ d, u.default = some d → d ∈ u.enum_.val
  | .Single (.Titled t) => ∀ d, t.default = some d → d ∈ t.one_of.val.map (·.const_)
  | .Multi (.Untitled u) => ConsistentItems u.min_items u.max_items u.default u.items.enum_.val
  | .Multi (.Titled t) =>
    ConsistentItems t.min_items t.max_items t.default (t.items.any_of.val.map (·.const_))
  | .Legacy l => ∀ d, l.default = some d → d ∈ l.enum_.val

/-! ## Property maps -/

/-- The property names of a map, in the order of its entries (in Rust: ascending, the order of
`keys()`). -/
def propertyNames {V A : Type} (m : alloc.collections.btree.map.BTreeMap String V A) :
    List String :=
  m.entries.map Prod.fst

/-- The definition of property `k` in a map: the value of the first entry with key `k`, `none` if
there is none (`BTreeMap::get`). -/
def propertyLookup {V A : Type} (m : alloc.collections.btree.map.BTreeMap String V A)
    (k : String) : Option V :=
  (m.entries.find? fun e => e.1 == k).map Prod.snd

/-- **The map invariant**: the entries are strictly ascending by key in Rust's `String` order
(the lexicographic order of the UTF-8 bytes, `Ord for String`), so the keys are pairwise
distinct. The model of `BTreeMap` (`trusted/Rmcp/TypesExternal.lean`) represents each Rust map
by its entries in this order; the type does not carry the invariant (`formal/README.md`, "Stated
exceptions": `BTreeMap::insert`). -/
def KeysSorted {V A : Type} (m : alloc.collections.btree.map.BTreeMap String V A) : Prop :=
  m.entries.Pairwise fun a b => utf8Bytes a.1 < utf8Bytes b.1

/-- **The key list of a map fits in a `Vec<String>`**: `24 * n ≤ isize::MAX` for `n` entries
(a `String` is 24 bytes on the translated target). It is the exact condition under which the
model of `prim::sorted_keys` (`properties.keys().cloned().collect()`, patched lines 1821–1825;
`ExtModel.collectVec 24`) does not panic. Every Rust map meets it: its keys are `String`s that
already exist in memory. -/
def PropertiesFit {V A : Type} (m : alloc.collections.btree.map.BTreeMap String V A) : Prop :=
  24 * m.entries.length ≤ ExtModel.maxStringBytes

/-- **`new` is `old` with property `k` set to `v`** (`BTreeMap::insert(k, v)`, the old value
dropped): the lookup of `k` gives `v`, every other lookup is unchanged, and the result is sorted
if `old` is. For sorted maps the lookups determine the entries. -/
def PropertyInserted (old : alloc.collections.btree.map.BTreeMap String PrimitiveSchemaDefinition
      alloc.alloc.Global) (k : String) (v : PrimitiveSchemaDefinition)
    (new : alloc.collections.btree.map.BTreeMap String PrimitiveSchemaDefinition
      alloc.alloc.Global) : Prop :=
  (∀ k', propertyLookup new k' = if k' = k then some v else propertyLookup old k') ∧
    (KeysSorted old → KeysSorted new)

/-! ## Elicitation schemas -/

/-- **Every required name of a builder is a property** (the check of
`ElicitationSchemaBuilder::build`, upstream lines 1766–1772; patched lines 1756–1765, against
the key list). Duplicate required names are allowed (H20). **Not an invariant** of
`ElicitationSchemaBuilder`: its fields are `pub` (upstream lines 1400–1405) and `mark_required`
(upstream lines 1740–1743) appends any name (H20), so it is a premise of the statements that need
it (`build_unchecked` panics without it). It is checked only when `build` runs (upstream lines
1766–1772): a name marked required before its property is added breaks it only until a
property of that name is added. The empty builder meets it and the property helpers
keep it (they insert each property they require). -/
def RequiredPropertiesExist (b : ElicitationSchemaBuilder) : Prop :=
  ∀ r ∈ b.required.val, r ∈ propertyNames b.properties

/-- **A consistent elicitation schema**: a list of required names, if present, is non-empty and
names only properties, and the property order is present and lists the property names in the
map's order. Duplicate required names are allowed (H20); an empty property map is allowed (H19).
-/
def ConsistentElicitationSchema (s : ElicitationSchema) : Prop :=
  (∀ rs, s.required = some rs → rs.val ≠ [] ∧ ∀ r ∈ rs.val, r ∈ propertyNames s.properties) ∧
    s.property_order.map (·.val) = some (propertyNames s.properties)

end Defs.ElicitationSchema
