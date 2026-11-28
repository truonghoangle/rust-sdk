/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
module
public import Defs
public import Proofs.Defs.ElicitationSchema
public import Proofs.Model.ElicitationSchema.Primitive
public import Proofs.Model.ElicitationSchema.Enum
public import Proofs.Model.ElicitationSchema.Schema

@[expose] public section

/-!
# Internal spec file for `elicitation_schema.rs` (intermediate functions, model laws)

The public API of `elicitation_schema.rs` that `formal/specs/` states is its **top-level** public
functions only: those that no other verified function calls
(`formal/specs/Specs/Model/ElicitationSchema.lean`). This file holds the rest of the verified
`elicitation_schema.rs` statements, which the top-level statements are built on:

* the **intermediate public functions**, `pub` in upstream rmcp but called by a top-level one
  (table below), with their failing cases and the corollaries of X47 and X48;
* the statement of `impl Default for EnumSchemaBuilder<SingleSelect>` (public, not a target,
  called by X30);
* the **compositions** that involve an intermediate function;
* the **model laws** (statements about the definitions of `Defs.ElicitationSchema` only, with no
  Rust call): two that justify the premise (Q) (`PropertyInserted.forall_mem_propertyNames_append`,
  `requiredPropertiesExist_emptyElicitationSchemaBuilder`) and one about the map invariant of (S)
  (`keysSorted_emptyElicitationSchemaBuilder_properties`: the empty builder's map is sorted).

| ID | Function | Class | Called by | File |
|---|---|---|---|---|
| X01 | `StringSchema::new` | intermediate | X49, X50, X55, X56, X59, X60 | Internal |
| X02 | `StringSchema::email` | intermediate | X57, X58 | Internal |
| X14 | `IntegerSchema::new` | intermediate | X51, X52, X61–X64 | Internal |
| X16 | `IntegerSchema::range` | intermediate | X61, X62 | Internal |
| X22 | `BooleanSchema::new` | intermediate | X53, X54, X65–X68 | Internal |
| X25 | `BooleanSchema::with_default` | intermediate | X66 | Internal |
| X30 | `EnumSchemaBuilder<SingleSelect>::new` | intermediate | X39 | Internal |
| X46 | `ElicitationSchemaBuilder::new` | intermediate | X45 | Internal |
| — | `impl Default for EnumSchemaBuilder<SingleSelect>` (not a target) | intermediate | X30 | Internal |
| X47 | `ElicitationSchemaBuilder::property` | intermediate | X56, X58, X60, X62, X64, X66, X68, X70 | Internal |
| X48 | `ElicitationSchemaBuilder::required_property` | intermediate | X55, X57, X59, X61, X63, X65, X67, X69 | Internal |
| X74 | `ElicitationSchemaBuilder::build` | intermediate | X75 | Internal |

So 11 intermediate targets (X01, X02, X14, X16, X22, X25, X30, X46, X47, X48, X74) and 23
statements here. The statements, their text, IDs, proofs and sign-off (spec owner, 2026-11-28,
decision XS6) are those of the signed-off file; only their place differs. The premise keys
(caller code, (R), (L), (B), (V), (Q), (S)) and the keys of the exceptions not covered ((I), (A),
(M), (C), (D), (F)) are those defined in `formal/specs/Specs/Model/ElicitationSchema.lean`,
"Premises" and "Not covered"; the bugs H19, H20, H22, H23 (confirmed, decision XS7), the
recorded behaviour H21 (decision XS7), the translated configuration, line citations and linkage
are as stated there.

One row per theorem below; the theorem is `Theorems.elicitation_schema.<Theorem>`. In the ID
column, `Xnn fail` is the failing-case companion of `Xnn`, `Xnn cor.` a corollary, `Xnn comp.` a
composition about one call of `Xnn`, `Xmm+Xnn` a composition of two calls, and `model` a model
law.

| ID | Function | Theorem | Guarantee | Premises (caller must ensure) | Not covered (Rust may panic or behave otherwise; the model does not) |
|---|---|---|---|---|---|
| X01 | `StringSchema::new` | `StringSchema.new` | `defaultStringSchema` | none | none |
| X02 | `StringSchema::email` | `StringSchema.email` | the default string schema with format `Email` | none | none |
| X14 | `IntegerSchema::new` | `IntegerSchema.new` | `defaultIntegerSchema` | none | none |
| X16 | `IntegerSchema::range` | `IntegerSchema.range` | both bounds set | (B) | none |
| X16 fail | `IntegerSchema::range` | `IntegerSchema.range_fail` | panics (`assert!`) | `min > max` | none |
| X22 | `BooleanSchema::new` | `BooleanSchema.new` | `defaultBooleanSchema` | none | none |
| X25 | `BooleanSchema::with_default` | `BooleanSchema.with_default` | default set, other fields unchanged | none | none |
| X30 | `EnumSchemaBuilder<SingleSelect>::new` | `EnumSchemaBuilderSingleSelect.new` | `newEnumSchemaBuilder values` | none | none |
| X46 | `ElicitationSchemaBuilder::new` | `ElicitationSchemaBuilder.new` | `emptyElicitationSchemaBuilder` | none | none |
| X47 | `ElicitationSchemaBuilder::property` | `ElicitationSchemaBuilder.property` | property `name.into()` set to `schema` (`PropertyInserted`), other fields unchanged | caller code | (I), (M), (A) |
| X47 cor. | same | `ElicitationSchemaBuilder.property_entries_eq_mapInsert` | the entries are `ExtModel.mapInsert n schema self.properties.entries` | caller code | (I), (M), (A) |
| X48 | `ElicitationSchemaBuilder::required_property` | `ElicitationSchemaBuilder.required_property` | `name.into()` appended to the required list (H20) and set to `schema` | caller code, (R) | (I), (M), (A) |
| X48 cor. | same | `ElicitationSchemaBuilder.required_property_entries_eq_mapInsert` | the entries are `ExtModel.mapInsert n schema self.properties.entries` | caller code, (R) | (I), (M), (A) |
| X48 fail | same | `ElicitationSchemaBuilder.required_property_fail` | fails in the model (`Vec::push`; no Rust `Vec` is that long) | caller code; required list of `Usize.max` names | none |
| X74 | `ElicitationSchemaBuilder::build` | `ElicitationSchemaBuilder.build` | `Ok` iff `RequiredPropertiesExist` (H19, H20), with the builder's fields and property order; else `Err` with its message | (L) | (A) |
| X74 fail | same | `ElicitationSchemaBuilder.build_fail` | panics in the model (`prim::sorted_keys`; no Rust map is that large) | `¬ PropertiesFit self.properties` | none |
| X30 comp. | `EnumSchemaBuilder<SingleSelect>::new` | `EnumSchemaBuilderSingleSelect.new_valid` | the builder meets `ValidEnumSchemaBuilder` | none | none |
| — | `impl Default for EnumSchemaBuilder<SingleSelect>` | `EnumSchemaBuilderSingleSelect.default_valid` | `newEnumSchemaBuilder` of the empty vector, meeting `ValidEnumSchemaBuilder` | none | none |
| X74 comp. | `ElicitationSchemaBuilder::build` | `ElicitationSchemaBuilder.build_consistent` | every `Ok` schema is `ConsistentElicitationSchema` (H19, H20) | (L) | (A) |
| X46+X74 | `new`, then `build` | `ElicitationSchemaBuilder.build_new` | `Ok`, no property and no required list (H19) | none | none |
| model | — | `PropertyInserted.forall_mem_propertyNames_append` | after inserting `n`, a required list of properties with `n` appended is still one | none | none |
| model | — | `requiredPropertiesExist_emptyElicitationSchemaBuilder` | the empty builder meets (Q) | none | none |
| model | — | `keysSorted_emptyElicitationSchemaBuilder_properties` | the map of the empty builder is sorted | none | none |

Each statement is restated as a theorem `Theorems.elicitation_schema.<name>`, proved by its spec
theorem in `Proofs/Model/ElicitationSchema/{Primitive,Enum,Schema}.lean` (the model laws keep
their names, `Defs.ElicitationSchema.<name>` in `Proofs/Model/ElicitationSchema/Schema.lean`,
under `Theorems.elicitation_schema.<name>`), and followed by the assumptions its proof depends on,
checked by `#print axioms` under `#guard_msgs`.
-/

open Aeneas Aeneas.Std Result
open Defs (utf8Bytes)
open Defs.ElicitationSchema
open rmcp.model.elicitation_schema (StringSchema StringFormat IntegerSchema BooleanSchema
  ConstTitle EnumSchema EnumSchemaBuilder SingleSelect MultiSelect PrimitiveSchemaDefinition
  ElicitationSchema ElicitationSchemaBuilder)

/-! ## Intermediate public functions (X01, X02, X14, X16, X22, X25, X30, X46–X48, X74) -/

/-- X01 `StringSchema::new` (intermediate → Internal): the default string schema
(`Self::default()`, upstream and patched lines 142–144; `Default`, lines 126–138). No premise. -/
theorem Theorems.elicitation_schema.StringSchema.new :
    rmcp.model.elicitation_schema.StringSchema.new ⦃ (result : StringSchema) =>
      result = defaultStringSchema ⦄ :=
  rmcp.model.elicitation_schema.StringSchema.new_spec

/--
info: 'Theorems.elicitation_schema.StringSchema.new' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.elicitation_schema.StringSchema.new

/-- X02 `StringSchema::email` (intermediate → Internal): the default string schema with format
`Email` (upstream and patched lines 147–152). No premise. -/
theorem Theorems.elicitation_schema.StringSchema.email :
    rmcp.model.elicitation_schema.StringSchema.email ⦃ (result : StringSchema) =>
      result = { defaultStringSchema with format := some .Email } ⦄ :=
  rmcp.model.elicitation_schema.StringSchema.email_spec

/--
info: 'Theorems.elicitation_schema.StringSchema.email' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.elicitation_schema.StringSchema.email

/-- X14 `IntegerSchema::new` (intermediate → Internal): the default integer schema
(`Self::default()`, upstream and patched lines 404–406; `Default`, lines 389–400). No premise. -/
theorem Theorems.elicitation_schema.IntegerSchema.new :
    rmcp.model.elicitation_schema.IntegerSchema.new ⦃ (result : IntegerSchema) =>
      result = defaultIntegerSchema ⦄ :=
  rmcp.model.elicitation_schema.IntegerSchema.new_spec

/--
info: 'Theorems.elicitation_schema.IntegerSchema.new' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.elicitation_schema.IntegerSchema.new

/-- X16 `IntegerSchema::range` (intermediate → Internal): for `min ≤ max`, both bounds set
(upstream and patched lines 419–424).

Premise: (B). The case `min > max` is `IntegerSchema.range_fail`. -/
theorem Theorems.elicitation_schema.IntegerSchema.range (self : IntegerSchema) (min max : I64)
    (h_le : min.val ≤ max.val) :
    rmcp.model.elicitation_schema.IntegerSchema.range self min max ⦃ (result : IntegerSchema) =>
      result = { self with minimum := some min, maximum := some max } ⦄ :=
  rmcp.model.elicitation_schema.IntegerSchema.range_spec self min max h_le

/--
info: 'Theorems.elicitation_schema.IntegerSchema.range' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.elicitation_schema.IntegerSchema.range

/-- X16, failing case (intermediate → Internal): for `min > max` the `assert!` panics (upstream
line 420). -/
theorem Theorems.elicitation_schema.IntegerSchema.range_fail (self : IntegerSchema)
    (min max : I64) (h_gt : max.val < min.val) :
    rmcp.model.elicitation_schema.IntegerSchema.range self min max = fail .assertionFailure :=
  rmcp.model.elicitation_schema.IntegerSchema.range_fail self min max h_gt

/--
info: 'Theorems.elicitation_schema.IntegerSchema.range_fail' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.elicitation_schema.IntegerSchema.range_fail

/-- X22 `BooleanSchema::new` (intermediate → Internal): the default boolean schema
(`Self::default()`, upstream and patched lines 497–499; `Default`, lines 484–493). No premise. -/
theorem Theorems.elicitation_schema.BooleanSchema.new :
    rmcp.model.elicitation_schema.BooleanSchema.new ⦃ (result : BooleanSchema) =>
      result = defaultBooleanSchema ⦄ :=
  rmcp.model.elicitation_schema.BooleanSchema.new_spec

/--
info: 'Theorems.elicitation_schema.BooleanSchema.new' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.elicitation_schema.BooleanSchema.new

/-- X25 `BooleanSchema::with_default` (intermediate → Internal): sets the default, other fields
unchanged (upstream and patched lines 514–517). No premise. -/
theorem Theorems.elicitation_schema.BooleanSchema.with_default (self : BooleanSchema)
    (default : Bool) :
    rmcp.model.elicitation_schema.BooleanSchema.with_default self default ⦃
      (result : BooleanSchema) =>
      result = { self with default := some default } ⦄ :=
  rmcp.model.elicitation_schema.BooleanSchema.with_default_spec self default

/--
info: 'Theorems.elicitation_schema.BooleanSchema.with_default' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.elicitation_schema.BooleanSchema.with_default

/-- X30 `EnumSchemaBuilder::<SingleSelect>::new` (intermediate → Internal): the builder for
`values` with nothing else set (upstream lines 899–904, patched 898–903; `Default`, lines
844–858). No premise. -/
theorem Theorems.elicitation_schema.EnumSchemaBuilderSingleSelect.new
    (values : alloc.vec.Vec String) :
    rmcp.model.elicitation_schema.EnumSchemaBuilderSingleSelect.new values ⦃
      (result : EnumSchemaBuilder SingleSelect) =>
      result = newEnumSchemaBuilder values ⦄ :=
  rmcp.model.elicitation_schema.EnumSchemaBuilderSingleSelect.new_spec values

/--
info: 'Theorems.elicitation_schema.EnumSchemaBuilderSingleSelect.new' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.elicitation_schema.EnumSchemaBuilderSingleSelect.new

/-- X46 `ElicitationSchemaBuilder::new` (intermediate → Internal): the empty builder
(`Self::default()`, upstream lines 1409–1411, patched 1399–1401; the derived `Default`, upstream
line 1398). No premise. -/
theorem Theorems.elicitation_schema.ElicitationSchemaBuilder.new :
    rmcp.model.elicitation_schema.ElicitationSchemaBuilder.new ⦃
      (result : ElicitationSchemaBuilder) =>
      result = emptyElicitationSchemaBuilder ⦄ :=
  rmcp.model.elicitation_schema.ElicitationSchemaBuilder.new_spec

/--
info: 'Theorems.elicitation_schema.ElicitationSchemaBuilder.new' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.elicitation_schema.ElicitationSchemaBuilder.new

/-- X47 `ElicitationSchemaBuilder::property` (intermediate → Internal): property
`n = name.into()` set to `schema` (an earlier definition of `n` replaced), the required list,
title and description unchanged (`self.properties.insert(name.into(), schema)`, upstream lines
1414–1417, patched 1404–1407).

Premise: caller code. Not covered: (I), (M), (A). -/
theorem Theorems.elicitation_schema.ElicitationSchemaBuilder.property {NameLike : Type}
    (nameInto : core.convert.Into NameLike String) (self : ElicitationSchemaBuilder)
    («name» : NameLike) (schema : PrimitiveSchemaDefinition) (n : String)
    (h_name_into : nameInto.into «name» = ok n) :
    rmcp.model.elicitation_schema.ElicitationSchemaBuilder.property nameInto self «name» schema ⦃
      (result : ElicitationSchemaBuilder) =>
      result.required = self.required ∧ result.title = self.title ∧
        result.description = self.description ∧
        PropertyInserted self.properties n schema result.properties ⦄ :=
  rmcp.model.elicitation_schema.ElicitationSchemaBuilder.property_spec nameInto self «name» schema n
    h_name_into

/--
info: 'Theorems.elicitation_schema.ElicitationSchemaBuilder.property' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.elicitation_schema.ElicitationSchemaBuilder.property

/-- X47, corollary (intermediate → Internal; decision XS1): the entries of the property map are
`ExtModel.mapInsert n schema self.properties.entries`, the trusted model of `BTreeMap::insert`
with `String` keys (`btreeInsert_stringOrd_eq_ok`), for any entry list. `ExtModel.mapInsert n v`
walks the entries while their key differs from `n` and is not greater than it (in the byte order
of `KeysSorted`); at the entry where it stops it replaces the value if that key is `n`, and
otherwise inserts `(n, v)` before that entry (at the end if it reaches the end). On a sorted list
this is the `BTreeMap` insertion. The other fields are as in X47.

Premise: caller code. Not covered: (I), (M), (A). -/
theorem Theorems.elicitation_schema.ElicitationSchemaBuilder.property_entries_eq_mapInsert
    {NameLike : Type} (nameInto : core.convert.Into NameLike String)
    (self : ElicitationSchemaBuilder) («name» : NameLike) (schema : PrimitiveSchemaDefinition)
    (n : String) (h_name_into : nameInto.into «name» = ok n) :
    rmcp.model.elicitation_schema.ElicitationSchemaBuilder.property nameInto self «name» schema ⦃
      (result : ElicitationSchemaBuilder) =>
      result.required = self.required ∧ result.title = self.title ∧
        result.description = self.description ∧
        result.properties.entries = (ExtModel.mapInsert n schema self.properties.entries).2 ⦄ :=
  rmcp.model.elicitation_schema.ElicitationSchemaBuilder.property_entries_eq_mapInsert nameInto self
    «name» schema n h_name_into

/--
info: 'Theorems.elicitation_schema.ElicitationSchemaBuilder.property_entries_eq_mapInsert' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.elicitation_schema.ElicitationSchemaBuilder.property_entries_eq_mapInsert

/-- X48 `ElicitationSchemaBuilder::required_property` (intermediate → Internal): `n =
name.into()` appended to the required list and property `n` set to `schema`, title and
description unchanged (upstream lines 1420–1429, patched 1410–1419). **H20**: `n` is appended
even if it is already required.

Premises: caller code, (R). Not covered: (I), (M), (A). The case
`self.required.val.length = Usize.max` is `ElicitationSchemaBuilder.required_property_fail`. -/
theorem Theorems.elicitation_schema.ElicitationSchemaBuilder.required_property {NameLike : Type}
    (nameInto : core.convert.Into NameLike String) (self : ElicitationSchemaBuilder)
    («name» : NameLike) (schema : PrimitiveSchemaDefinition) (n : String)
    (h_name_into : nameInto.into «name» = ok n)
    (h_required_len : self.required.val.length < Usize.max) :
    rmcp.model.elicitation_schema.ElicitationSchemaBuilder.required_property nameInto self
      «name» schema ⦃ (result : ElicitationSchemaBuilder) =>
      result.required.val = self.required.val ++ [n] ∧ result.title = self.title ∧
        result.description = self.description ∧
        PropertyInserted self.properties n schema result.properties ⦄ :=
  rmcp.model.elicitation_schema.ElicitationSchemaBuilder.required_property_spec nameInto self «name»
    schema n h_name_into h_required_len

/--
info: 'Theorems.elicitation_schema.ElicitationSchemaBuilder.required_property' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.elicitation_schema.ElicitationSchemaBuilder.required_property

/-- X48, corollary (intermediate → Internal; decision XS1): the entries of the property map are
`ExtModel.mapInsert n schema self.properties.entries` (as X47's corollary), for any entry list;
the other fields are as in X48. **H20**.

Premises: caller code, (R). Not covered: (I), (M), (A). -/
theorem Theorems.elicitation_schema.ElicitationSchemaBuilder.required_property_entries_eq_mapInsert
    {NameLike : Type} (nameInto : core.convert.Into NameLike String)
    (self : ElicitationSchemaBuilder) («name» : NameLike) (schema : PrimitiveSchemaDefinition)
    (n : String) (h_name_into : nameInto.into «name» = ok n)
    (h_required_len : self.required.val.length < Usize.max) :
    rmcp.model.elicitation_schema.ElicitationSchemaBuilder.required_property nameInto self
      «name» schema ⦃ (result : ElicitationSchemaBuilder) =>
      result.required.val = self.required.val ++ [n] ∧ result.title = self.title ∧
        result.description = self.description ∧
        result.properties.entries = (ExtModel.mapInsert n schema self.properties.entries).2 ⦄ :=
  rmcp.model.elicitation_schema.ElicitationSchemaBuilder.required_property_entries_eq_mapInsert
    nameInto self «name» schema n h_name_into h_required_len

/--
info: 'Theorems.elicitation_schema.ElicitationSchemaBuilder.required_property_entries_eq_mapInsert' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.elicitation_schema.ElicitationSchemaBuilder.required_property_entries_eq_mapInsert

/-- X48, failing case (intermediate → Internal): a required list of `Usize.max` names makes the
Aeneas model of `Vec::push` fail (no Rust `Vec<String>` is that long; Rust panics earlier, (A)).

Premise: caller code. -/
theorem Theorems.elicitation_schema.ElicitationSchemaBuilder.required_property_fail
    {NameLike : Type} (nameInto : core.convert.Into NameLike String)
    (self : ElicitationSchemaBuilder) («name» : NameLike) (schema : PrimitiveSchemaDefinition)
    (n : String) (h_name_into : nameInto.into «name» = ok n)
    (h_full : self.required.val.length = Usize.max) :
    rmcp.model.elicitation_schema.ElicitationSchemaBuilder.required_property nameInto self
      «name» schema = fail .maximumSizeExceeded :=
  rmcp.model.elicitation_schema.ElicitationSchemaBuilder.required_property_fail nameInto self «name»
    schema n h_name_into h_full

/--
info: 'Theorems.elicitation_schema.ElicitationSchemaBuilder.required_property_fail' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.elicitation_schema.ElicitationSchemaBuilder.required_property_fail

/-- X74 `ElicitationSchemaBuilder::build` (intermediate → Internal; linkage patch-08, hunk E7):
`Ok` exactly when every required name is a property (`RequiredPropertiesExist`), with the
builder's properties, title and description, no dialect, the property order the property names in
the map's order, and the required list (`None` if it is empty); otherwise `Err("Required field does
not exist in properties")` (upstream lines 1764–1788; patched lines 1754–1781, the key list from
`prim::sorted_keys` computed first, patched lines 1821–1825). **H19**: a builder with no property
(and no required name) gives `Ok`, although the documentation (upstream line 1763) lists an empty
schema as an error. **H20**: duplicate required names are kept.

Premise: (L); on the `Err` path it is patch-induced (patch 08 hunk E7 computes the key list
before the check; patch-08 header, and `formal/README.md`, "Stated exceptions of the external
models", `elicitation_schema::prim::sorted_keys`). Not covered: (A). The case
`¬ PropertiesFit self.properties` is `ElicitationSchemaBuilder.build_fail`. -/
theorem Theorems.elicitation_schema.ElicitationSchemaBuilder.build
    (self : ElicitationSchemaBuilder) (h_fit : PropertiesFit self.properties) :
    rmcp.model.elicitation_schema.ElicitationSchemaBuilder.build self ⦃
      (result : core.result.Result ElicitationSchema Str) =>
      match result with
      | .Ok s =>
        RequiredPropertiesExist self ∧ s.schema = none ∧ s.title = self.title ∧
          s.properties = self.properties ∧
          s.property_order.map (·.val) = some (propertyNames self.properties) ∧
          s.required = (if self.required.val = [] then none else some self.required) ∧
          s.description = self.description
      | .Err e => ¬ RequiredPropertiesExist self ∧ e.val = utf8Bytes requiredNotInPropertiesMsg ⦄ :=
  rmcp.model.elicitation_schema.ElicitationSchemaBuilder.build_spec self h_fit

/--
info: 'Theorems.elicitation_schema.ElicitationSchemaBuilder.build' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.elicitation_schema.ElicitationSchemaBuilder.build

/-- X74, failing case (intermediate → Internal): when the key list would exceed `isize::MAX`
bytes, the model of `prim::sorted_keys` panics before any check (no Rust map is that large). -/
theorem Theorems.elicitation_schema.ElicitationSchemaBuilder.build_fail
    (self : ElicitationSchemaBuilder) (h_big : ¬ PropertiesFit self.properties) :
    rmcp.model.elicitation_schema.ElicitationSchemaBuilder.build self = fail .panic :=
  rmcp.model.elicitation_schema.ElicitationSchemaBuilder.build_fail self h_big

/--
info: 'Theorems.elicitation_schema.ElicitationSchemaBuilder.build_fail' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.elicitation_schema.ElicitationSchemaBuilder.build_fail

/-! ## Compositions; `impl Default for EnumSchemaBuilder<SingleSelect>` -/

/-- Composition X30 (intermediate → Internal): the builder of `EnumSchemaBuilder::new` meets the
enum builder invariant. No premise. -/
theorem Theorems.elicitation_schema.EnumSchemaBuilderSingleSelect.new_valid
    (values : alloc.vec.Vec String) :
    rmcp.model.elicitation_schema.EnumSchemaBuilderSingleSelect.new values ⦃
      (result : EnumSchemaBuilder SingleSelect) =>
      ValidEnumSchemaBuilder result ⦄ :=
  rmcp.model.elicitation_schema.EnumSchemaBuilderSingleSelect.new_valid values

/--
info: 'Theorems.elicitation_schema.EnumSchemaBuilderSingleSelect.new_valid' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.elicitation_schema.EnumSchemaBuilderSingleSelect.new_valid

/-- `impl Default for EnumSchemaBuilder<SingleSelect>` (intermediate → Internal; called by X30
`new`): the builder with no values and nothing else set, `newEnumSchemaBuilder` of the empty
vector (upstream and patched lines 844–858; translated as
`EnumSchemaBuilderSingleSelect.Insts.CoreDefaultDefault.default`, patched lines 845–857), which
meets the enum builder invariant (V): it is the third constructor of an enum builder. No premise.
-/
theorem Theorems.elicitation_schema.EnumSchemaBuilderSingleSelect.default_valid :
    rmcp.model.elicitation_schema.EnumSchemaBuilderSingleSelect.Insts.CoreDefaultDefault.default ⦃
      (result : EnumSchemaBuilder SingleSelect) =>
      result = newEnumSchemaBuilder (alloc.vec.Vec.new String) ∧ ValidEnumSchemaBuilder result ⦄ :=
  rmcp.model.elicitation_schema.EnumSchemaBuilderSingleSelect.default_valid

/--
info: 'Theorems.elicitation_schema.EnumSchemaBuilderSingleSelect.default_valid' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.elicitation_schema.EnumSchemaBuilderSingleSelect.default_valid

/-- Composition X74 (intermediate → Internal): every schema `build` accepts is consistent: its
required names (if any) are properties, its property order is the property names (its map is the
builder's, so it is sorted if the builder's is). **H19**, **H20** (empty property map and
duplicate required names are consistent).

Premise: (L). Not covered: (A). -/
theorem Theorems.elicitation_schema.ElicitationSchemaBuilder.build_consistent
    (self : ElicitationSchemaBuilder) (h_fit : PropertiesFit self.properties) :
    rmcp.model.elicitation_schema.ElicitationSchemaBuilder.build self ⦃
      (result : core.result.Result ElicitationSchema Str) =>
      ∀ s, result = .Ok s →
        ConsistentElicitationSchema s ⦄ :=
  rmcp.model.elicitation_schema.ElicitationSchemaBuilder.build_consistent self h_fit

/--
info: 'Theorems.elicitation_schema.ElicitationSchemaBuilder.build_consistent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.elicitation_schema.ElicitationSchemaBuilder.build_consistent

/-- Composition X46+X74 (intermediate → Internal), **H19**: `build` on a new builder returns
`Ok`, a schema with no property and no required list, although the documentation (upstream line
1763) lists "No properties are defined (empty schema)" as an error. No premise. -/
theorem Theorems.elicitation_schema.ElicitationSchemaBuilder.build_new :
    (do
      let b ← rmcp.model.elicitation_schema.ElicitationSchemaBuilder.new
      rmcp.model.elicitation_schema.ElicitationSchemaBuilder.build b) ⦃
      (result : core.result.Result ElicitationSchema Str) =>
      ∃ s, result = .Ok s ∧ s.properties.entries = [] ∧ s.required = none ⦄ :=
  rmcp.model.elicitation_schema.ElicitationSchemaBuilder.build_new

/--
info: 'Theorems.elicitation_schema.ElicitationSchemaBuilder.build_new' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.elicitation_schema.ElicitationSchemaBuilder.build_new

/-! ## Model laws -/

/-- Model law: inserting property `n` keeps every name already present and adds `n`, so a
required list whose names are all properties stays so after appending `n`. This is why X48, X50,
X52, X54, X55, X57, X59, X61, X63, X65, X67, X69 (append `n` and insert it) and X47, X49, X51,
X53, X56, X58, X60, X62, X64, X66, X68, X70 (required list unchanged) keep (Q); X71 appends
without inserting and can break it. No premise. -/
theorem Theorems.elicitation_schema.PropertyInserted.forall_mem_propertyNames_append
    (old new : alloc.collections.btree.map.BTreeMap String PrimitiveSchemaDefinition
      alloc.alloc.Global)
    (n : String) (v : PrimitiveSchemaDefinition) (rs : List String)
    (h_ins : PropertyInserted old n v new) (h_rs : ∀ r ∈ rs, r ∈ propertyNames old) :
    ∀ r ∈ rs ++ [n], r ∈ propertyNames new :=
  Defs.ElicitationSchema.PropertyInserted.forall_mem_propertyNames_append old new n v rs h_ins h_rs

/--
info: 'Theorems.elicitation_schema.PropertyInserted.forall_mem_propertyNames_append' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.elicitation_schema.PropertyInserted.forall_mem_propertyNames_append

/-- Model law: the empty builder (X45, X46) meets `RequiredPropertiesExist` (Q). No premise. -/
theorem Theorems.elicitation_schema.requiredPropertiesExist_emptyElicitationSchemaBuilder :
    RequiredPropertiesExist emptyElicitationSchemaBuilder :=
  Defs.ElicitationSchema.requiredPropertiesExist_emptyElicitationSchemaBuilder

/--
info: 'Theorems.elicitation_schema.requiredPropertiesExist_emptyElicitationSchemaBuilder' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.elicitation_schema.requiredPropertiesExist_emptyElicitationSchemaBuilder

/-- Model law: the map of the empty builder (X45, X46) is sorted. No premise. -/
theorem Theorems.elicitation_schema.keysSorted_emptyElicitationSchemaBuilder_properties :
    KeysSorted emptyElicitationSchemaBuilder.properties :=
  Defs.ElicitationSchema.keysSorted_emptyElicitationSchemaBuilder_properties

/--
info: 'Theorems.elicitation_schema.keysSorted_emptyElicitationSchemaBuilder_properties' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms Theorems.elicitation_schema.keysSorted_emptyElicitationSchemaBuilder_properties
