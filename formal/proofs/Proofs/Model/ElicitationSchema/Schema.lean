/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
module
public import Rmcp.Funs
public import Defs.Bytes
public import Defs.ElicitationSchema
public import Proofs.Defs.ElicitationSchema
public import Proofs.External.ElicitationSchema
public import Proofs.External.String
public import Proofs.External.Std
public import Proofs.External.WP
public import Proofs.Model.ElicitationSchema.Common

@[expose] public section

/-!
# Spec theorems for the elicitation schemas of `elicitation_schema.rs` (X40–X75)

The constructor and setters of `ElicitationSchema` (X40–X45) and the builder
`ElicitationSchemaBuilder` (X46–X75): the property setters insert into the property map through
the model of `BTreeMap::insert` (`Proofs.External.ElicitationSchema.insert_string_eq`, for any
entry list, so the lookups of `PropertyInserted` hold without a sortedness premise), the required
setters append to the required list, and `build` (X74) checks the required names against the key
list of `prim::sorted_keys`. Then the compositions (consistent schemas, H19 for the empty builder)
and the model laws of `Defs.ElicitationSchema` about property insertion and the empty builder.

Source: "crates/rmcp/src/model/elicitation_schema.rs", upstream lines 1269–1797, patched lines
1259–1825 (X40, X74, X75 through translation patch 08, hunks E6, E7; the line of each function
is in its docstring).
-/

open Aeneas Aeneas.Std Result
open Defs (utf8Bytes)
open Defs.ElicitationSchema
open rmcp.model.elicitation_schema (StringSchema StringFormat IntegerSchema BooleanSchema
  ConstTitle EnumSchema EnumSchemaBuilder SingleSelect MultiSelect PrimitiveSchemaDefinition
  ElicitationSchema ElicitationSchemaBuilder)
open Proofs.External.ElicitationSchema Proofs.Model.ElicitationSchema

namespace rmcp.model.elicitation_schema

/-- **Spec theorem for `rmcp::model::elicitation_schema::ElicitationSchema::new`** (X40)

X40 `ElicitationSchema::new` (top-level → Specs; linkage patch-08, hunk E6): the schema with
these properties, the property order their names in the map's order, and no dialect, title,
required list or description (upstream lines 1269–1280; patched lines 1259–1270, the key list
from `prim::sorted_keys`, patched lines 1821–1825).

Premise: (L). Not covered: (A). The case `¬ PropertiesFit properties` is
`ElicitationSchema.new_fail`. -/
@[step]
theorem ElicitationSchema.new_spec
    (properties : alloc.collections.btree.map.BTreeMap String PrimitiveSchemaDefinition
      alloc.alloc.Global)
    (h_fit : PropertiesFit properties) :
    rmcp.model.elicitation_schema.ElicitationSchema.new properties ⦃
      (result : ElicitationSchema) =>
      result.schema = none ∧ result.title = none ∧ result.properties = properties ∧
        result.property_order.map (·.val) = some (propertyNames properties) ∧
        result.required = none ∧ result.description = none ⦄ := by
  obtain ⟨names, hn, hnv⟩ := sorted_keys_eq_ok properties h_fit
  simp only [ElicitationSchema.new, hn, bind_ok]
  exact (WP.spec_ok _).2 ⟨rfl, rfl, rfl, by rw [Option.map_some, hnv], rfl, rfl⟩

/-- **Failing case of `rmcp::model::elicitation_schema::ElicitationSchema::new`** (X40)

X40, failing case (top-level → Specs): when the key list would exceed `isize::MAX` bytes the
model of `prim::sorted_keys` panics (no Rust map is that large). -/
theorem ElicitationSchema.new_fail
    (properties : alloc.collections.btree.map.BTreeMap String PrimitiveSchemaDefinition
      alloc.alloc.Global)
    (h_big : ¬ PropertiesFit properties) :
    rmcp.model.elicitation_schema.ElicitationSchema.new properties = fail .panic := by
  unfold ElicitationSchema.new
  rw [model.elicitation_schema.prim.sorted_keys_eq_fail properties
    (by unfold PropertiesFit at h_big; omega), bind_fail]

/-- **Spec theorem for `rmcp::model::elicitation_schema::ElicitationSchema::with_required`** (X41)

X41 `ElicitationSchema::with_required` (top-level → Specs): sets the required list, other
fields unchanged (upstream lines 1351–1354, patched 1341–1344). Recorded behaviour (not a bug,
decision XS4): the names are not checked against the properties, and an empty list gives
`Some([])`, so the result need not be `ConsistentElicitationSchema`. No premise. -/
@[step]
theorem ElicitationSchema.with_required_spec (self : ElicitationSchema)
    (required : alloc.vec.Vec String) :
    rmcp.model.elicitation_schema.ElicitationSchema.with_required self required ⦃
      (result : ElicitationSchema) =>
      result = { self with required := some required } ⦄ := by
  simp [ElicitationSchema.with_required]

/-- **Spec theorem for `rmcp::model::elicitation_schema::ElicitationSchema::with_title`** (X42)

X42 `ElicitationSchema::with_title` (top-level → Specs): sets the title to
`c = title.into()` (upstream lines 1357–1360, patched 1347–1350).

Premise: caller code. Not covered: (I). -/
@[step]
theorem ElicitationSchema.with_title_spec {TitleLike : Type}
    (titleInto : core.convert.Into TitleLike (rmcp.alloc.borrow.Cow Str String))
    (self : ElicitationSchema) (title : TitleLike) (c : rmcp.alloc.borrow.Cow Str String)
    (h_title_into : titleInto.into title = ok c) :
    rmcp.model.elicitation_schema.ElicitationSchema.with_title titleInto self title ⦃
      (result : ElicitationSchema) =>
      result = { self with title := some c } ⦄ := by
  simp [ElicitationSchema.with_title, h_title_into]

/-- **Spec theorem for
`rmcp::model::elicitation_schema::ElicitationSchema::with_description`** (X43)

X43 `ElicitationSchema::with_description` (top-level → Specs): sets the description to
`c = description.into()` (upstream lines 1363–1366, patched 1353–1356).

Premise: caller code. Not covered: (I). -/
@[step]
theorem ElicitationSchema.with_description_spec {DescriptionLike : Type}
    (descriptionInto : core.convert.Into DescriptionLike (rmcp.alloc.borrow.Cow Str String))
    (self : ElicitationSchema) (description : DescriptionLike)
    (c : rmcp.alloc.borrow.Cow Str String)
    (h_description_into : descriptionInto.into description = ok c) :
    rmcp.model.elicitation_schema.ElicitationSchema.with_description descriptionInto self
      description ⦃ (result : ElicitationSchema) =>
      result = { self with description := some c } ⦄ := by
  simp [ElicitationSchema.with_description, h_description_into]

/-- **Spec theorem for `rmcp::model::elicitation_schema::ElicitationSchema::with_schema`** (X44)

X44 `ElicitationSchema::with_schema` (top-level → Specs): sets the dialect (`$schema`) to
`c = schema.into()` (upstream lines 1369–1372, patched 1359–1362).

Premise: caller code. Not covered: (I). -/
@[step]
theorem ElicitationSchema.with_schema_spec {SchemaLike : Type}
    (schemaInto : core.convert.Into SchemaLike (rmcp.alloc.borrow.Cow Str String))
    (self : ElicitationSchema) (schema : SchemaLike) (c : rmcp.alloc.borrow.Cow Str String)
    (h_schema_into : schemaInto.into schema = ok c) :
    rmcp.model.elicitation_schema.ElicitationSchema.with_schema schemaInto self schema ⦃
      (result : ElicitationSchema) =>
      result = { self with schema := some c } ⦄ := by
  simp [ElicitationSchema.with_schema, h_schema_into]

/-- **Spec theorem for `rmcp::model::elicitation_schema::ElicitationSchema::builder`** (X45)

X45 `ElicitationSchema::builder` (top-level → Specs): the empty builder
(`ElicitationSchemaBuilder::new()`, upstream lines 1375–1377, patched 1365–1367). No premise. -/
@[step]
theorem ElicitationSchema.builder_spec :
    rmcp.model.elicitation_schema.ElicitationSchema.builder ⦃
      (result : ElicitationSchemaBuilder) =>
      result = emptyElicitationSchemaBuilder ⦄ := by
  rw [ElicitationSchema.builder, elicitationSchemaBuilder_new_eq]
  exact (WP.spec_ok _).2 rfl

/-- **Spec theorem for `rmcp::model::elicitation_schema::ElicitationSchemaBuilder::new`** (X46)

X46 `ElicitationSchemaBuilder::new` (intermediate → Internal): the empty builder
(`Self::default()`, upstream lines 1409–1411, patched 1399–1401; the derived `Default`, upstream
line 1398). No premise. -/
@[step]
theorem ElicitationSchemaBuilder.new_spec :
    rmcp.model.elicitation_schema.ElicitationSchemaBuilder.new ⦃
      (result : ElicitationSchemaBuilder) =>
      result = emptyElicitationSchemaBuilder ⦄ := by
  simp [ElicitationSchemaBuilder.new,
    ElicitationSchemaBuilder.Insts.CoreDefaultDefault.default,
    alloc.collections.btree.map.BTreeMapKVGlobal.Insts.CoreDefaultDefault.default,
    alloc.vec.Vec.Insts.CoreDefaultDefault.default,
    core.option.Option.Insts.CoreDefaultDefault.default, emptyElicitationSchemaBuilder]

/-- **Spec theorem for `rmcp::model::elicitation_schema::ElicitationSchemaBuilder::property`** (X47)

X47 `ElicitationSchemaBuilder::property` (intermediate → Internal): property
`n = name.into()` set to `schema` (an earlier definition of `n` replaced), the required list,
title and description unchanged (`self.properties.insert(name.into(), schema)`, upstream lines
1414–1417, patched 1404–1407).

Premise: caller code. Not covered: (I), (M), (A). -/
@[step]
theorem ElicitationSchemaBuilder.property_spec {NameLike : Type}
    (nameInto : core.convert.Into NameLike String) (self : ElicitationSchemaBuilder)
    («name» : NameLike) (schema : PrimitiveSchemaDefinition) (n : String)
    (h_name_into : nameInto.into «name» = ok n) :
    rmcp.model.elicitation_schema.ElicitationSchemaBuilder.property nameInto self «name» schema ⦃
      (result : ElicitationSchemaBuilder) =>
      result.required = self.required ∧ result.title = self.title ∧
        result.description = self.description ∧
        PropertyInserted self.properties n schema result.properties ⦄ := by
  unfold ElicitationSchemaBuilder.property
  rw [h_name_into, bind_ok]
  rw [insert_string_eq, bind_ok]
  exact (WP.spec_ok _).2 ⟨rfl, rfl, rfl, propertyInserted_mapInsert _ _ _⟩

/-- X47, corollary (intermediate → Internal; decision XS1): the entries of the property map are
`ExtModel.mapInsert n schema self.properties.entries`, the trusted model of `BTreeMap::insert`
with `String` keys (`btreeInsert_stringOrd_eq_ok`), for any entry list. `ExtModel.mapInsert n v`
walks the entries while their key differs from `n` and is not greater than it (in the byte order
of `KeysSorted`); at the entry where it stops it replaces the value if that key is `n`, and
otherwise inserts `(n, v)` before that entry (at the end if it reaches the end). On a sorted list
this is the `BTreeMap` insertion. The other fields are as in X47.

Premise: caller code. Not covered: (I), (M), (A). -/
theorem ElicitationSchemaBuilder.property_entries_eq_mapInsert
    {NameLike : Type} (nameInto : core.convert.Into NameLike String)
    (self : ElicitationSchemaBuilder) («name» : NameLike) (schema : PrimitiveSchemaDefinition)
    (n : String) (h_name_into : nameInto.into «name» = ok n) :
    rmcp.model.elicitation_schema.ElicitationSchemaBuilder.property nameInto self «name» schema ⦃
      (result : ElicitationSchemaBuilder) =>
      result.required = self.required ∧ result.title = self.title ∧
        result.description = self.description ∧
        result.properties.entries = (ExtModel.mapInsert n schema self.properties.entries).2 ⦄ := by
  simp only [ElicitationSchemaBuilder.property, h_name_into,
    insert_string_eq, bind_ok]
  exact (WP.spec_ok _).2 ⟨rfl, rfl, rfl, rfl⟩

/-- **Spec theorem for
`rmcp::model::elicitation_schema::ElicitationSchemaBuilder::required_property`** (X48)

X48 `ElicitationSchemaBuilder::required_property` (intermediate → Internal): `n =
name.into()` appended to the required list and property `n` set to `schema`, title and
description unchanged (upstream lines 1420–1429, patched 1410–1419). **H20**: `n` is appended
even if it is already required.

Premises: caller code, (R). Not covered: (I), (M), (A). The case
`self.required.val.length = Usize.max` is `ElicitationSchemaBuilder.required_property_fail`. -/
@[step]
theorem ElicitationSchemaBuilder.required_property_spec {NameLike : Type}
    (nameInto : core.convert.Into NameLike String) (self : ElicitationSchemaBuilder)
    («name» : NameLike) (schema : PrimitiveSchemaDefinition) (n : String)
    (h_name_into : nameInto.into «name» = ok n)
    (h_required_len : self.required.val.length < Usize.max) :
    rmcp.model.elicitation_schema.ElicitationSchemaBuilder.required_property nameInto self
      «name» schema ⦃ (result : ElicitationSchemaBuilder) =>
      result.required.val = self.required.val ++ [n] ∧ result.title = self.title ∧
        result.description = self.description ∧
        PropertyInserted self.properties n schema result.properties ⦄ := by
  simp only [ElicitationSchemaBuilder.required_property,
    h_name_into, alloc.string.String.Insts.CoreCloneClone.clone,
    Proofs.External.WP.push_eq_ok _ _ h_required_len, insert_string_eq, bind_ok]
  exact (WP.spec_ok _).2 ⟨alloc.vec.Vec.from_val .., rfl, rfl, propertyInserted_mapInsert _ _ _⟩

/-- X48, corollary (intermediate → Internal; decision XS1): the entries of the property map are
`ExtModel.mapInsert n schema self.properties.entries` (as X47's corollary), for any entry list;
the other fields are as in X48. **H20**.

Premises: caller code, (R). Not covered: (I), (M), (A). -/
theorem ElicitationSchemaBuilder.required_property_entries_eq_mapInsert
    {NameLike : Type} (nameInto : core.convert.Into NameLike String)
    (self : ElicitationSchemaBuilder) («name» : NameLike) (schema : PrimitiveSchemaDefinition)
    (n : String) (h_name_into : nameInto.into «name» = ok n)
    (h_required_len : self.required.val.length < Usize.max) :
    rmcp.model.elicitation_schema.ElicitationSchemaBuilder.required_property nameInto self
      «name» schema ⦃ (result : ElicitationSchemaBuilder) =>
      result.required.val = self.required.val ++ [n] ∧ result.title = self.title ∧
        result.description = self.description ∧
        result.properties.entries = (ExtModel.mapInsert n schema self.properties.entries).2 ⦄ := by
  simp only [ElicitationSchemaBuilder.required_property,
    h_name_into, alloc.string.String.Insts.CoreCloneClone.clone,
    Proofs.External.WP.push_eq_ok _ _ h_required_len, insert_string_eq, bind_ok]
  exact (WP.spec_ok _).2 ⟨alloc.vec.Vec.from_val .., rfl, rfl, rfl⟩

/-- **Failing case of
`rmcp::model::elicitation_schema::ElicitationSchemaBuilder::required_property`** (X48)

X48, failing case (intermediate → Internal): a required list of `Usize.max` names makes the
Aeneas model of `Vec::push` fail (no Rust `Vec<String>` is that long; Rust panics earlier, (A)).

Premise: caller code. -/
theorem ElicitationSchemaBuilder.required_property_fail
    {NameLike : Type} (nameInto : core.convert.Into NameLike String)
    (self : ElicitationSchemaBuilder) («name» : NameLike) (schema : PrimitiveSchemaDefinition)
    (n : String) (h_name_into : nameInto.into «name» = ok n)
    (h_full : self.required.val.length = Usize.max) :
    rmcp.model.elicitation_schema.ElicitationSchemaBuilder.required_property nameInto self
      «name» schema = fail .maximumSizeExceeded := by
  simp only [ElicitationSchemaBuilder.required_property,
    h_name_into, alloc.string.String.Insts.CoreCloneClone.clone,
    Proofs.External.WP.push_eq_fail self.required n (by omega), bind_ok, bind_fail]

/-- **Spec theorem for
`rmcp::model::elicitation_schema::ElicitationSchemaBuilder::string_property`** (X49)

X49 `ElicitationSchemaBuilder::string_property` (top-level → Specs): property `n =
name.into()` set to `String(s)`, where `s` is the caller's closure applied to the default string
schema; the required list, title and description unchanged (upstream lines 1436–1446, patched
1426–1436). **H23**: documented "(required)", but `n` is not added to the required list.

Premise: caller code. Not covered: (I), (M), (A). -/
@[step]
theorem ElicitationSchemaBuilder.string_property_spec {NameLike F : Type}
    (nameInto : core.convert.Into NameLike String)
    (fOnce : core.ops.function.FnOnce F StringSchema StringSchema)
    (self : ElicitationSchemaBuilder) («name» : NameLike) (f : F) (n : String) (s : StringSchema)
    (h_name_into : nameInto.into «name» = ok n)
    (h_f : fOnce.call_once f defaultStringSchema = ok s) :
    rmcp.model.elicitation_schema.ElicitationSchemaBuilder.string_property nameInto fOnce self
      «name» f ⦃ (result : ElicitationSchemaBuilder) =>
      result.required = self.required ∧ result.title = self.title ∧
        result.description = self.description ∧
        PropertyInserted self.properties n (.String s) result.properties ⦄ := by
  have hd : StringSchema.new = ok defaultStringSchema := rfl
  simp only [ElicitationSchemaBuilder.string_property, h_name_into,
    hd, h_f, insert_string_eq, bind_ok]
  exact (WP.spec_ok _).2 ⟨rfl, rfl, rfl, propertyInserted_mapInsert _ _ _⟩

/-- **Spec theorem for
`rmcp::model::elicitation_schema::ElicitationSchemaBuilder::required_string_property`** (X50)

X50 `ElicitationSchemaBuilder::required_string_property` (top-level → Specs): `n =
name.into()` appended to the required list and property `n` set to `String(s)`, `s` the closure
applied to the default string schema (upstream lines 1449–1461, patched 1439–1451). **H20**.

Premises: caller code, (R). Not covered: (I), (M), (A). -/
@[step]
theorem ElicitationSchemaBuilder.required_string_property_spec
    {NameLike F : Type} (nameInto : core.convert.Into NameLike String)
    (fOnce : core.ops.function.FnOnce F StringSchema StringSchema)
    (self : ElicitationSchemaBuilder) («name» : NameLike) (f : F) (n : String) (s : StringSchema)
    (h_name_into : nameInto.into «name» = ok n)
    (h_f : fOnce.call_once f defaultStringSchema = ok s)
    (h_required_len : self.required.val.length < Usize.max) :
    rmcp.model.elicitation_schema.ElicitationSchemaBuilder.required_string_property nameInto
      fOnce self «name» f ⦃ (result : ElicitationSchemaBuilder) =>
      result.required.val = self.required.val ++ [n] ∧ result.title = self.title ∧
        result.description = self.description ∧
        PropertyInserted self.properties n (.String s) result.properties ⦄ := by
  have hd : StringSchema.new = ok defaultStringSchema := rfl
  simp only [ElicitationSchemaBuilder.required_string_property, h_name_into,
    alloc.string.String.Insts.CoreCloneClone.clone,
    Proofs.External.WP.push_eq_ok _ _ h_required_len, hd, h_f, insert_string_eq, bind_ok]
  exact (WP.spec_ok _).2 ⟨alloc.vec.Vec.from_val .., rfl, rfl, propertyInserted_mapInsert _ _ _⟩

/-- **Spec theorem for
`rmcp::model::elicitation_schema::ElicitationSchemaBuilder::integer_property`** (X51)

X51 `ElicitationSchemaBuilder::integer_property` (top-level → Specs): property `n =
name.into()` set to `Integer(i)`, `i` the closure applied to the default integer schema; the
required list, title and description unchanged (upstream lines 1492–1502, patched 1482–1492).

Premise: caller code. Not covered: (I), (M), (A). -/
@[step]
theorem ElicitationSchemaBuilder.integer_property_spec {NameLike F : Type}
    (nameInto : core.convert.Into NameLike String)
    (fOnce : core.ops.function.FnOnce F IntegerSchema IntegerSchema)
    (self : ElicitationSchemaBuilder) («name» : NameLike) (f : F) (n : String) (i : IntegerSchema)
    (h_name_into : nameInto.into «name» = ok n)
    (h_f : fOnce.call_once f defaultIntegerSchema = ok i) :
    rmcp.model.elicitation_schema.ElicitationSchemaBuilder.integer_property nameInto fOnce self
      «name» f ⦃ (result : ElicitationSchemaBuilder) =>
      result.required = self.required ∧ result.title = self.title ∧
        result.description = self.description ∧
        PropertyInserted self.properties n (.Integer i) result.properties ⦄ := by
  have hd : IntegerSchema.new = ok defaultIntegerSchema := rfl
  simp only [ElicitationSchemaBuilder.integer_property, h_name_into, hd, h_f, insert_string_eq,
    bind_ok]
  exact (WP.spec_ok _).2 ⟨rfl, rfl, rfl, propertyInserted_mapInsert _ _ _⟩

/-- **Spec theorem for
`rmcp::model::elicitation_schema::ElicitationSchemaBuilder::required_integer_property`** (X52)

X52 `ElicitationSchemaBuilder::required_integer_property` (top-level → Specs): `n` appended
to the required list and property `n` set to `Integer(i)`, `i` the closure applied to the
default integer schema (upstream lines 1505–1517, patched 1495–1507). **H20**.

Premises: caller code, (R). Not covered: (I), (M), (A). -/
@[step]
theorem ElicitationSchemaBuilder.required_integer_property_spec
    {NameLike F : Type} (nameInto : core.convert.Into NameLike String)
    (fOnce : core.ops.function.FnOnce F IntegerSchema IntegerSchema)
    (self : ElicitationSchemaBuilder) («name» : NameLike) (f : F) (n : String) (i : IntegerSchema)
    (h_name_into : nameInto.into «name» = ok n)
    (h_f : fOnce.call_once f defaultIntegerSchema = ok i)
    (h_required_len : self.required.val.length < Usize.max) :
    rmcp.model.elicitation_schema.ElicitationSchemaBuilder.required_integer_property nameInto
      fOnce self «name» f ⦃ (result : ElicitationSchemaBuilder) =>
      result.required.val = self.required.val ++ [n] ∧ result.title = self.title ∧
        result.description = self.description ∧
        PropertyInserted self.properties n (.Integer i) result.properties ⦄ := by
  have hd : IntegerSchema.new = ok defaultIntegerSchema := rfl
  simp only [ElicitationSchemaBuilder.required_integer_property, h_name_into,
    alloc.string.String.Insts.CoreCloneClone.clone,
    Proofs.External.WP.push_eq_ok _ _ h_required_len, hd, h_f, insert_string_eq, bind_ok]
  exact (WP.spec_ok _).2 ⟨alloc.vec.Vec.from_val .., rfl, rfl, propertyInserted_mapInsert _ _ _⟩

/-- **Spec theorem for
`rmcp::model::elicitation_schema::ElicitationSchemaBuilder::bool_property`** (X53)

X53 `ElicitationSchemaBuilder::bool_property` (top-level → Specs): property `n =
name.into()` set to `Boolean(b)`, `b` the closure applied to the default boolean schema; the
required list, title and description unchanged (upstream lines 1520–1530, patched 1510–1520).

Premise: caller code. Not covered: (I), (M), (A). -/
@[step]
theorem ElicitationSchemaBuilder.bool_property_spec {NameLike F : Type}
    (nameInto : core.convert.Into NameLike String)
    (fOnce : core.ops.function.FnOnce F BooleanSchema BooleanSchema)
    (self : ElicitationSchemaBuilder) («name» : NameLike) (f : F) (n : String) (b : BooleanSchema)
    (h_name_into : nameInto.into «name» = ok n)
    (h_f : fOnce.call_once f defaultBooleanSchema = ok b) :
    rmcp.model.elicitation_schema.ElicitationSchemaBuilder.bool_property nameInto fOnce self
      «name» f ⦃ (result : ElicitationSchemaBuilder) =>
      result.required = self.required ∧ result.title = self.title ∧
        result.description = self.description ∧
        PropertyInserted self.properties n (.Boolean b) result.properties ⦄ := by
  have hd : BooleanSchema.new = ok defaultBooleanSchema := rfl
  simp only [ElicitationSchemaBuilder.bool_property, h_name_into, hd, h_f, insert_string_eq,
    bind_ok]
  exact (WP.spec_ok _).2 ⟨rfl, rfl, rfl, propertyInserted_mapInsert _ _ _⟩

/-- **Spec theorem for
`rmcp::model::elicitation_schema::ElicitationSchemaBuilder::required_bool_property`** (X54)

X54 `ElicitationSchemaBuilder::required_bool_property` (top-level → Specs): `n` appended to
the required list and property `n` set to `Boolean(b)`, `b` the closure applied to the default
boolean schema (upstream lines 1533–1545, patched 1523–1535). **H20**.

Premises: caller code, (R). Not covered: (I), (M), (A). -/
@[step]
theorem ElicitationSchemaBuilder.required_bool_property_spec
    {NameLike F : Type} (nameInto : core.convert.Into NameLike String)
    (fOnce : core.ops.function.FnOnce F BooleanSchema BooleanSchema)
    (self : ElicitationSchemaBuilder) («name» : NameLike) (f : F) (n : String) (b : BooleanSchema)
    (h_name_into : nameInto.into «name» = ok n)
    (h_f : fOnce.call_once f defaultBooleanSchema = ok b)
    (h_required_len : self.required.val.length < Usize.max) :
    rmcp.model.elicitation_schema.ElicitationSchemaBuilder.required_bool_property nameInto
      fOnce self «name» f ⦃ (result : ElicitationSchemaBuilder) =>
      result.required.val = self.required.val ++ [n] ∧ result.title = self.title ∧
        result.description = self.description ∧
        PropertyInserted self.properties n (.Boolean b) result.properties ⦄ := by
  have hd : BooleanSchema.new = ok defaultBooleanSchema := rfl
  simp only [ElicitationSchemaBuilder.required_bool_property, h_name_into,
    alloc.string.String.Insts.CoreCloneClone.clone,
    Proofs.External.WP.push_eq_ok _ _ h_required_len, hd, h_f, insert_string_eq, bind_ok]
  exact (WP.spec_ok _).2 ⟨alloc.vec.Vec.from_val .., rfl, rfl, propertyInserted_mapInsert _ _ _⟩

/-- **Spec theorem for
`rmcp::model::elicitation_schema::ElicitationSchemaBuilder::required_string`** (X55)

X55 `ElicitationSchemaBuilder::required_string` (top-level → Specs): `n = name.into()`
required, with the default string schema (upstream lines 1552–1554, patched 1542–1544). **H20**.

Premises: caller code, (R). Not covered: (I), (M), (A). -/
@[step]
theorem ElicitationSchemaBuilder.required_string_spec {NameLike : Type}
    (nameInto : core.convert.Into NameLike String) (self : ElicitationSchemaBuilder)
    («name» : NameLike) (n : String) (h_name_into : nameInto.into «name» = ok n)
    (h_required_len : self.required.val.length < Usize.max) :
    rmcp.model.elicitation_schema.ElicitationSchemaBuilder.required_string nameInto self «name» ⦃
      (result : ElicitationSchemaBuilder) =>
      result.required.val = self.required.val ++ [n] ∧ result.title = self.title ∧
        result.description = self.description ∧
        PropertyInserted self.properties n (.String defaultStringSchema) result.properties ⦄ := by
  simp only [ElicitationSchemaBuilder.required_string,
    StringSchema.new,
    StringSchema.Insts.CoreDefaultDefault.default, bind_ok]
  exact ElicitationSchemaBuilder.required_property_spec nameInto self
    «name» _ n h_name_into h_required_len

/-- **Spec theorem for
`rmcp::model::elicitation_schema::ElicitationSchemaBuilder::optional_string`** (X56)

X56 `ElicitationSchemaBuilder::optional_string` (top-level → Specs): property `n =
name.into()` with the default string schema, not required (upstream lines 1557–1559, patched
1547–1549).

Premise: caller code. Not covered: (I), (M), (A). -/
@[step]
theorem ElicitationSchemaBuilder.optional_string_spec {NameLike : Type}
    (nameInto : core.convert.Into NameLike String) (self : ElicitationSchemaBuilder)
    («name» : NameLike) (n : String) (h_name_into : nameInto.into «name» = ok n) :
    rmcp.model.elicitation_schema.ElicitationSchemaBuilder.optional_string nameInto self «name» ⦃
      (result : ElicitationSchemaBuilder) =>
      result.required = self.required ∧ result.title = self.title ∧
        result.description = self.description ∧
        PropertyInserted self.properties n (.String defaultStringSchema) result.properties ⦄ := by
  simp only [ElicitationSchemaBuilder.optional_string,
    StringSchema.new,
    StringSchema.Insts.CoreDefaultDefault.default, bind_ok]
  exact ElicitationSchemaBuilder.property_spec nameInto self
    «name» _ n h_name_into

/-- **Spec theorem for
`rmcp::model::elicitation_schema::ElicitationSchemaBuilder::required_email`** (X57)

X57 `ElicitationSchemaBuilder::required_email` (top-level → Specs): `n = name.into()`
required, a string with format `Email` (upstream lines 1562–1567, patched 1552–1557). **H20**.

Premises: caller code, (R). Not covered: (I), (M), (A). -/
@[step]
theorem ElicitationSchemaBuilder.required_email_spec {NameLike : Type}
    (nameInto : core.convert.Into NameLike String) (self : ElicitationSchemaBuilder)
    («name» : NameLike) (n : String) (h_name_into : nameInto.into «name» = ok n)
    (h_required_len : self.required.val.length < Usize.max) :
    rmcp.model.elicitation_schema.ElicitationSchemaBuilder.required_email nameInto self «name» ⦃
      (result : ElicitationSchemaBuilder) =>
      result.required.val = self.required.val ++ [n] ∧ result.title = self.title ∧
        result.description = self.description ∧
        PropertyInserted self.properties n
          (.String { defaultStringSchema with format := some .Email }) result.properties ⦄ := by
  have hd : StringSchema.email = ok { defaultStringSchema with format := some .Email } := by
    simp [StringSchema.email, StringSchema.Insts.CoreDefaultDefault.default,
      defaultStringSchema]
  simp only [ElicitationSchemaBuilder.required_email, hd, bind_ok]
  exact ElicitationSchemaBuilder.required_property_spec nameInto self
    «name» _ n h_name_into h_required_len

/-- **Spec theorem for
`rmcp::model::elicitation_schema::ElicitationSchemaBuilder::optional_email`** (X58)

X58 `ElicitationSchemaBuilder::optional_email` (top-level → Specs): property `n =
name.into()`, a string with format `Email`, not required (upstream lines 1570–1575, patched
1560–1565).

Premise: caller code. Not covered: (I), (M), (A). -/
@[step]
theorem ElicitationSchemaBuilder.optional_email_spec {NameLike : Type}
    (nameInto : core.convert.Into NameLike String) (self : ElicitationSchemaBuilder)
    («name» : NameLike) (n : String) (h_name_into : nameInto.into «name» = ok n) :
    rmcp.model.elicitation_schema.ElicitationSchemaBuilder.optional_email nameInto self «name» ⦃
      (result : ElicitationSchemaBuilder) =>
      result.required = self.required ∧ result.title = self.title ∧
        result.description = self.description ∧
        PropertyInserted self.properties n
          (.String { defaultStringSchema with format := some .Email }) result.properties ⦄ := by
  have hd : StringSchema.email = ok { defaultStringSchema with format := some .Email } := by
    simp [StringSchema.email, StringSchema.Insts.CoreDefaultDefault.default,
      defaultStringSchema]
  simp only [ElicitationSchemaBuilder.optional_email, hd, bind_ok]
  exact ElicitationSchemaBuilder.property_spec nameInto self
    «name» _ n h_name_into

/-- **Spec theorem for
`rmcp::model::elicitation_schema::ElicitationSchemaBuilder::required_string_with`** (X59)

X59 `ElicitationSchemaBuilder::required_string_with` (top-level → Specs): `n` required, with
`String(s)`, `s` the closure applied to the default string schema (upstream lines 1578–1587,
patched 1568–1577; the closure is called before `name.into()`). **H20**.

Premises: caller code, (R). Not covered: (I), (M), (A). -/
@[step]
theorem ElicitationSchemaBuilder.required_string_with_spec
    {NameLike F : Type} (nameInto : core.convert.Into NameLike String)
    (fOnce : core.ops.function.FnOnce F StringSchema StringSchema)
    (self : ElicitationSchemaBuilder) («name» : NameLike) (f : F) (n : String) (s : StringSchema)
    (h_name_into : nameInto.into «name» = ok n)
    (h_f : fOnce.call_once f defaultStringSchema = ok s)
    (h_required_len : self.required.val.length < Usize.max) :
    rmcp.model.elicitation_schema.ElicitationSchemaBuilder.required_string_with nameInto fOnce
      self «name» f ⦃ (result : ElicitationSchemaBuilder) =>
      result.required.val = self.required.val ++ [n] ∧ result.title = self.title ∧
        result.description = self.description ∧
        PropertyInserted self.properties n (.String s) result.properties ⦄ := by
  have hd : StringSchema.new = ok defaultStringSchema := rfl
  simp only [ElicitationSchemaBuilder.required_string_with, hd, h_f, bind_ok]
  exact ElicitationSchemaBuilder.required_property_spec nameInto self
    «name» _ n h_name_into h_required_len

/-- **Spec theorem for
`rmcp::model::elicitation_schema::ElicitationSchemaBuilder::optional_string_with`** (X60)

X60 `ElicitationSchemaBuilder::optional_string_with` (top-level → Specs): property `n` set to
`String(s)`, not required (upstream lines 1590–1599, patched 1580–1589).

Premise: caller code. Not covered: (I), (M), (A). -/
@[step]
theorem ElicitationSchemaBuilder.optional_string_with_spec
    {NameLike F : Type} (nameInto : core.convert.Into NameLike String)
    (fOnce : core.ops.function.FnOnce F StringSchema StringSchema)
    (self : ElicitationSchemaBuilder) («name» : NameLike) (f : F) (n : String) (s : StringSchema)
    (h_name_into : nameInto.into «name» = ok n)
    (h_f : fOnce.call_once f defaultStringSchema = ok s) :
    rmcp.model.elicitation_schema.ElicitationSchemaBuilder.optional_string_with nameInto fOnce
      self «name» f ⦃ (result : ElicitationSchemaBuilder) =>
      result.required = self.required ∧ result.title = self.title ∧
        result.description = self.description ∧
        PropertyInserted self.properties n (.String s) result.properties ⦄ := by
  have hd : StringSchema.new = ok defaultStringSchema := rfl
  simp only [ElicitationSchemaBuilder.optional_string_with, hd, h_f, bind_ok]
  exact ElicitationSchemaBuilder.property_spec nameInto self
    «name» _ n h_name_into

/-- **Spec theorem for
`rmcp::model::elicitation_schema::ElicitationSchemaBuilder::required_integer`** (X61)

X61 `ElicitationSchemaBuilder::required_integer` (top-level → Specs): for `min ≤ max`, `n`
required, an integer with both bounds (`IntegerSchema::new().range(min, max)`, upstream lines
1646–1651, patched 1636–1641). **H20**.

Premises: caller code, (R), (B). Not covered: (I), (M), (A). The case `min > max` is
`ElicitationSchemaBuilder.required_integer_fail`. -/
@[step]
theorem ElicitationSchemaBuilder.required_integer_spec {NameLike : Type}
    (nameInto : core.convert.Into NameLike String) (self : ElicitationSchemaBuilder)
    («name» : NameLike) (min max : I64) (n : String) (h_name_into : nameInto.into «name» = ok n)
    (h_le : min.val ≤ max.val) (h_required_len : self.required.val.length < Usize.max) :
    rmcp.model.elicitation_schema.ElicitationSchemaBuilder.required_integer nameInto self «name»
      min max ⦃ (result : ElicitationSchemaBuilder) =>
      result.required.val = self.required.val ++ [n] ∧ result.title = self.title ∧
        result.description = self.description ∧
        PropertyInserted self.properties n
          (.Integer { defaultIntegerSchema with minimum := some min, maximum := some max })
          result.properties ⦄ := by
  have hd : IntegerSchema.new = ok defaultIntegerSchema := rfl
  have hr : IntegerSchema.range defaultIntegerSchema min max =
      ok { defaultIntegerSchema with minimum := some min, maximum := some max } := by
    unfold IntegerSchema.range
    have : (min <= max) = true := by scalar_tac
    simp [massert, this]
  simp only [ElicitationSchemaBuilder.required_integer, hd, hr,
    bind_ok]
  exact ElicitationSchemaBuilder.required_property_spec nameInto self
    «name» _ n h_name_into h_required_len

/-- **Failing case of
`rmcp::model::elicitation_schema::ElicitationSchemaBuilder::required_integer`** (X61)

X61, failing case (top-level → Specs): for `min > max` the `assert!` of `range` panics before
the name is converted (upstream line 420). No premise. -/
theorem ElicitationSchemaBuilder.required_integer_fail
    {NameLike : Type} (nameInto : core.convert.Into NameLike String)
    (self : ElicitationSchemaBuilder) («name» : NameLike) (min max : I64)
    (h_gt : max.val < min.val) :
    rmcp.model.elicitation_schema.ElicitationSchemaBuilder.required_integer nameInto self «name»
      min max = fail .assertionFailure := by
  have hd : IntegerSchema.new = ok defaultIntegerSchema := rfl
  have hr : IntegerSchema.range defaultIntegerSchema min max =
      fail .assertionFailure := by
    unfold IntegerSchema.range
    have : (min <= max) = false := by scalar_tac
    simp [massert, this]
  simp only [ElicitationSchemaBuilder.required_integer, hd, hr,
    bind_ok, bind_fail]

/-- **Spec theorem for
`rmcp::model::elicitation_schema::ElicitationSchemaBuilder::optional_integer`** (X62)

X62 `ElicitationSchemaBuilder::optional_integer` (top-level → Specs): for `min ≤ max`,
property `n` an integer with both bounds, not required (upstream lines 1654–1659, patched
1644–1649).

Premises: caller code, (B). Not covered: (I), (M), (A). The case `min > max` is
`ElicitationSchemaBuilder.optional_integer_fail`. -/
@[step]
theorem ElicitationSchemaBuilder.optional_integer_spec {NameLike : Type}
    (nameInto : core.convert.Into NameLike String) (self : ElicitationSchemaBuilder)
    («name» : NameLike) (min max : I64) (n : String) (h_name_into : nameInto.into «name» = ok n)
    (h_le : min.val ≤ max.val) :
    rmcp.model.elicitation_schema.ElicitationSchemaBuilder.optional_integer nameInto self «name»
      min max ⦃ (result : ElicitationSchemaBuilder) =>
      result.required = self.required ∧ result.title = self.title ∧
        result.description = self.description ∧
        PropertyInserted self.properties n
          (.Integer { defaultIntegerSchema with minimum := some min, maximum := some max })
          result.properties ⦄ := by
  have hd : IntegerSchema.new = ok defaultIntegerSchema := rfl
  have hr : IntegerSchema.range defaultIntegerSchema min max =
      ok { defaultIntegerSchema with minimum := some min, maximum := some max } := by
    unfold IntegerSchema.range
    have : (min <= max) = true := by scalar_tac
    simp [massert, this]
  simp only [ElicitationSchemaBuilder.optional_integer, hd, hr, bind_ok]
  exact ElicitationSchemaBuilder.property_spec nameInto self
    «name» _ n h_name_into

/-- **Failing case of
`rmcp::model::elicitation_schema::ElicitationSchemaBuilder::optional_integer`** (X62)

X62, failing case (top-level → Specs): for `min > max` the `assert!` of `range` panics. No
premise. -/
theorem ElicitationSchemaBuilder.optional_integer_fail
    {NameLike : Type} (nameInto : core.convert.Into NameLike String)
    (self : ElicitationSchemaBuilder) («name» : NameLike) (min max : I64)
    (h_gt : max.val < min.val) :
    rmcp.model.elicitation_schema.ElicitationSchemaBuilder.optional_integer nameInto self «name»
      min max = fail .assertionFailure := by
  have hd : IntegerSchema.new = ok defaultIntegerSchema := rfl
  have hr : IntegerSchema.range defaultIntegerSchema min max =
      fail .assertionFailure := by
    unfold IntegerSchema.range
    have : (min <= max) = false := by scalar_tac
    simp [massert, this]
  simp only [ElicitationSchemaBuilder.optional_integer, hd, hr, bind_ok, bind_fail]

/-- **Spec theorem for
`rmcp::model::elicitation_schema::ElicitationSchemaBuilder::required_integer_with`** (X63)

X63 `ElicitationSchemaBuilder::required_integer_with` (top-level → Specs): `n` required, with
`Integer(i)`, `i` the closure applied to the default integer schema (upstream lines 1662–1671,
patched 1652–1661). **H20**; the closure may set `minimum > maximum` (H21).

Premises: caller code, (R). Not covered: (I), (M), (A). -/
@[step]
theorem ElicitationSchemaBuilder.required_integer_with_spec
    {NameLike F : Type} (nameInto : core.convert.Into NameLike String)
    (fOnce : core.ops.function.FnOnce F IntegerSchema IntegerSchema)
    (self : ElicitationSchemaBuilder) («name» : NameLike) (f : F) (n : String) (i : IntegerSchema)
    (h_name_into : nameInto.into «name» = ok n)
    (h_f : fOnce.call_once f defaultIntegerSchema = ok i)
    (h_required_len : self.required.val.length < Usize.max) :
    rmcp.model.elicitation_schema.ElicitationSchemaBuilder.required_integer_with nameInto fOnce
      self «name» f ⦃ (result : ElicitationSchemaBuilder) =>
      result.required.val = self.required.val ++ [n] ∧ result.title = self.title ∧
        result.description = self.description ∧
        PropertyInserted self.properties n (.Integer i) result.properties ⦄ := by
  have hd : IntegerSchema.new = ok defaultIntegerSchema := rfl
  simp only [ElicitationSchemaBuilder.required_integer_with, hd, h_f, bind_ok]
  exact ElicitationSchemaBuilder.required_property_spec nameInto self
    «name» _ n h_name_into h_required_len

/-- **Spec theorem for
`rmcp::model::elicitation_schema::ElicitationSchemaBuilder::optional_integer_with`** (X64)

X64 `ElicitationSchemaBuilder::optional_integer_with` (top-level → Specs): property `n` set to
`Integer(i)`, not required (upstream lines 1674–1683, patched 1664–1673).

Premise: caller code. Not covered: (I), (M), (A). -/
@[step]
theorem ElicitationSchemaBuilder.optional_integer_with_spec
    {NameLike F : Type} (nameInto : core.convert.Into NameLike String)
    (fOnce : core.ops.function.FnOnce F IntegerSchema IntegerSchema)
    (self : ElicitationSchemaBuilder) («name» : NameLike) (f : F) (n : String) (i : IntegerSchema)
    (h_name_into : nameInto.into «name» = ok n)
    (h_f : fOnce.call_once f defaultIntegerSchema = ok i) :
    rmcp.model.elicitation_schema.ElicitationSchemaBuilder.optional_integer_with nameInto fOnce
      self «name» f ⦃ (result : ElicitationSchemaBuilder) =>
      result.required = self.required ∧ result.title = self.title ∧
        result.description = self.description ∧
        PropertyInserted self.properties n (.Integer i) result.properties ⦄ := by
  have hd : IntegerSchema.new = ok defaultIntegerSchema := rfl
  simp only [ElicitationSchemaBuilder.optional_integer_with, hd, h_f, bind_ok]
  exact ElicitationSchemaBuilder.property_spec nameInto self
    «name» _ n h_name_into

/-- **Spec theorem for
`rmcp::model::elicitation_schema::ElicitationSchemaBuilder::required_bool`** (X65)

X65 `ElicitationSchemaBuilder::required_bool` (top-level → Specs): `n` required, with the
default boolean schema (upstream lines 1688–1693, patched 1678–1683). **H20**.

Premises: caller code, (R). Not covered: (I), (M), (A). -/
@[step]
theorem ElicitationSchemaBuilder.required_bool_spec {NameLike : Type}
    (nameInto : core.convert.Into NameLike String) (self : ElicitationSchemaBuilder)
    («name» : NameLike) (n : String) (h_name_into : nameInto.into «name» = ok n)
    (h_required_len : self.required.val.length < Usize.max) :
    rmcp.model.elicitation_schema.ElicitationSchemaBuilder.required_bool nameInto self «name» ⦃
      (result : ElicitationSchemaBuilder) =>
      result.required.val = self.required.val ++ [n] ∧ result.title = self.title ∧
        result.description = self.description ∧
        PropertyInserted self.properties n (.Boolean defaultBooleanSchema) result.properties ⦄ := by
  have hd : BooleanSchema.new = ok defaultBooleanSchema := rfl
  simp only [ElicitationSchemaBuilder.required_bool, hd, bind_ok]
  exact ElicitationSchemaBuilder.required_property_spec nameInto self
    «name» _ n h_name_into h_required_len

/-- **Spec theorem for
`rmcp::model::elicitation_schema::ElicitationSchemaBuilder::optional_bool`** (X66)

X66 `ElicitationSchemaBuilder::optional_bool` (top-level → Specs): property `n` a boolean
with default `default`, not required (upstream lines 1696–1701, patched 1686–1691).

Premise: caller code. Not covered: (I), (M), (A). -/
@[step]
theorem ElicitationSchemaBuilder.optional_bool_spec {NameLike : Type}
    (nameInto : core.convert.Into NameLike String) (self : ElicitationSchemaBuilder)
    («name» : NameLike) (default : Bool) (n : String)
    (h_name_into : nameInto.into «name» = ok n) :
    rmcp.model.elicitation_schema.ElicitationSchemaBuilder.optional_bool nameInto self «name»
      default ⦃ (result : ElicitationSchemaBuilder) =>
      result.required = self.required ∧ result.title = self.title ∧
        result.description = self.description ∧
        PropertyInserted self.properties n
          (.Boolean { defaultBooleanSchema with default := some default }) result.properties ⦄ := by
  have hd : BooleanSchema.new = ok defaultBooleanSchema := rfl
  have hw : BooleanSchema.with_default defaultBooleanSchema default =
      ok { defaultBooleanSchema with default := some default } := rfl
  simp only [ElicitationSchemaBuilder.optional_bool, hd, hw, bind_ok]
  exact ElicitationSchemaBuilder.property_spec nameInto self
    «name» _ n h_name_into

/-- **Spec theorem for
`rmcp::model::elicitation_schema::ElicitationSchemaBuilder::required_bool_with`** (X67)

X67 `ElicitationSchemaBuilder::required_bool_with` (top-level → Specs): `n` required, with
`Boolean(b)`, `b` the closure applied to the default boolean schema (upstream lines 1704–1713,
patched 1694–1703). **H20**.

Premises: caller code, (R). Not covered: (I), (M), (A). -/
@[step]
theorem ElicitationSchemaBuilder.required_bool_with_spec
    {NameLike F : Type} (nameInto : core.convert.Into NameLike String)
    (fOnce : core.ops.function.FnOnce F BooleanSchema BooleanSchema)
    (self : ElicitationSchemaBuilder) («name» : NameLike) (f : F) (n : String) (b : BooleanSchema)
    (h_name_into : nameInto.into «name» = ok n)
    (h_f : fOnce.call_once f defaultBooleanSchema = ok b)
    (h_required_len : self.required.val.length < Usize.max) :
    rmcp.model.elicitation_schema.ElicitationSchemaBuilder.required_bool_with nameInto fOnce
      self «name» f ⦃ (result : ElicitationSchemaBuilder) =>
      result.required.val = self.required.val ++ [n] ∧ result.title = self.title ∧
        result.description = self.description ∧
        PropertyInserted self.properties n (.Boolean b) result.properties ⦄ := by
  have hd : BooleanSchema.new = ok defaultBooleanSchema := rfl
  simp only [ElicitationSchemaBuilder.required_bool_with, hd, h_f, bind_ok]
  exact ElicitationSchemaBuilder.required_property_spec nameInto self
    «name» _ n h_name_into h_required_len

/-- **Spec theorem for
`rmcp::model::elicitation_schema::ElicitationSchemaBuilder::optional_bool_with`** (X68)

X68 `ElicitationSchemaBuilder::optional_bool_with` (top-level → Specs): property `n` set to
`Boolean(b)`, not required (upstream lines 1716–1725, patched 1706–1715).

Premise: caller code. Not covered: (I), (M), (A). -/
@[step]
theorem ElicitationSchemaBuilder.optional_bool_with_spec
    {NameLike F : Type} (nameInto : core.convert.Into NameLike String)
    (fOnce : core.ops.function.FnOnce F BooleanSchema BooleanSchema)
    (self : ElicitationSchemaBuilder) («name» : NameLike) (f : F) (n : String) (b : BooleanSchema)
    (h_name_into : nameInto.into «name» = ok n)
    (h_f : fOnce.call_once f defaultBooleanSchema = ok b) :
    rmcp.model.elicitation_schema.ElicitationSchemaBuilder.optional_bool_with nameInto fOnce
      self «name» f ⦃ (result : ElicitationSchemaBuilder) =>
      result.required = self.required ∧ result.title = self.title ∧
        result.description = self.description ∧
        PropertyInserted self.properties n (.Boolean b) result.properties ⦄ := by
  have hd : BooleanSchema.new = ok defaultBooleanSchema := rfl
  simp only [ElicitationSchemaBuilder.optional_bool_with, hd, h_f, bind_ok]
  exact ElicitationSchemaBuilder.property_spec nameInto self
    «name» _ n h_name_into

/-- **Spec theorem for
`rmcp::model::elicitation_schema::ElicitationSchemaBuilder::required_enum_schema`** (X69)

X69 `ElicitationSchemaBuilder::required_enum_schema` (top-level → Specs): `n` required, with
`Enum(enum_schema)` stored unchanged (upstream lines 1730–1732, patched 1720–1722). **H20**.
Recorded behaviour (not a bug, decision XS4): the enum schema is stored unchecked
(`ConsistentEnumSchema` is not required).

Premises: caller code, (R). Not covered: (I), (M), (A). -/
@[step]
theorem ElicitationSchemaBuilder.required_enum_schema_spec
    {NameLike : Type} (nameInto : core.convert.Into NameLike String)
    (self : ElicitationSchemaBuilder) («name» : NameLike) (enum_schema : EnumSchema) (n : String)
    (h_name_into : nameInto.into «name» = ok n)
    (h_required_len : self.required.val.length < Usize.max) :
    rmcp.model.elicitation_schema.ElicitationSchemaBuilder.required_enum_schema nameInto self
      «name» enum_schema ⦃ (result : ElicitationSchemaBuilder) =>
      result.required.val = self.required.val ++ [n] ∧ result.title = self.title ∧
        result.description = self.description ∧
        PropertyInserted self.properties n (.Enum enum_schema) result.properties ⦄ := by
  simp only [ElicitationSchemaBuilder.required_enum_schema]
  exact ElicitationSchemaBuilder.required_property_spec nameInto self
    «name» _ n h_name_into h_required_len

/-- **Spec theorem for
`rmcp::model::elicitation_schema::ElicitationSchemaBuilder::optional_enum_schema`** (X70)

X70 `ElicitationSchemaBuilder::optional_enum_schema` (top-level → Specs): property `n` set to
`Enum(enum_schema)`, not required (upstream lines 1735–1737, patched 1725–1727). Recorded
behaviour (not a bug, decision XS4): the enum schema is stored unchecked (`ConsistentEnumSchema`
is not required).

Premise: caller code. Not covered: (I), (M), (A). -/
@[step]
theorem ElicitationSchemaBuilder.optional_enum_schema_spec
    {NameLike : Type} (nameInto : core.convert.Into NameLike String)
    (self : ElicitationSchemaBuilder) («name» : NameLike) (enum_schema : EnumSchema) (n : String)
    (h_name_into : nameInto.into «name» = ok n) :
    rmcp.model.elicitation_schema.ElicitationSchemaBuilder.optional_enum_schema nameInto self
      «name» enum_schema ⦃ (result : ElicitationSchemaBuilder) =>
      result.required = self.required ∧ result.title = self.title ∧
        result.description = self.description ∧
        PropertyInserted self.properties n (.Enum enum_schema) result.properties ⦄ := by
  simp only [ElicitationSchemaBuilder.optional_enum_schema]
  exact ElicitationSchemaBuilder.property_spec nameInto self
    «name» _ n h_name_into

/-- **Spec theorem for
`rmcp::model::elicitation_schema::ElicitationSchemaBuilder::mark_required`** (X71)

X71 `ElicitationSchemaBuilder::mark_required` (top-level → Specs): `n = name.into()`
appended to the required list, everything else unchanged (upstream lines 1740–1743, patched
1730–1733). **H20** (decision XS5): `n` need not be a property ("Mark an existing property" is
not checked here) and is appended even if already required. A name that is not a property breaks
(Q) until a property of that name is added (the check is made by `build`, upstream lines
1766–1772); if it is still missing when `build` runs, X74 returns `Err` and X75
`build_unchecked` panics (`build_unchecked_fail`).

Premises: caller code, (R). Not covered: (I), (A). The case `self.required.val.length =
Usize.max` is `ElicitationSchemaBuilder.mark_required_fail`. -/
@[step]
theorem ElicitationSchemaBuilder.mark_required_spec {NameLike : Type}
    (nameInto : core.convert.Into NameLike String) (self : ElicitationSchemaBuilder)
    («name» : NameLike) (n : String) (h_name_into : nameInto.into «name» = ok n)
    (h_required_len : self.required.val.length < Usize.max) :
    rmcp.model.elicitation_schema.ElicitationSchemaBuilder.mark_required nameInto self «name» ⦃
      (result : ElicitationSchemaBuilder) =>
      result.required.val = self.required.val ++ [n] ∧ result.properties = self.properties ∧
        result.title = self.title ∧ result.description = self.description ⦄ := by
  simp [ElicitationSchemaBuilder.mark_required, h_name_into,
    Proofs.External.WP.push_eq_ok _ _ h_required_len]

/-- **Failing case of
`rmcp::model::elicitation_schema::ElicitationSchemaBuilder::mark_required`** (X71)

X71, failing case (top-level → Specs): a required list of `Usize.max` names makes the Aeneas
model of `Vec::push` fail (no Rust `Vec<String>` is that long).

Premise: caller code. -/
theorem ElicitationSchemaBuilder.mark_required_fail
    {NameLike : Type} (nameInto : core.convert.Into NameLike String)
    (self : ElicitationSchemaBuilder) («name» : NameLike) (n : String)
    (h_name_into : nameInto.into «name» = ok n) (h_full : self.required.val.length = Usize.max) :
    rmcp.model.elicitation_schema.ElicitationSchemaBuilder.mark_required nameInto self «name» =
      fail .maximumSizeExceeded := by
  simp [ElicitationSchemaBuilder.mark_required, h_name_into,
    Proofs.External.WP.push_eq_fail self.required n (by omega)]

/-- **Spec theorem for `rmcp::model::elicitation_schema::ElicitationSchemaBuilder::title`** (X72)

X72 `ElicitationSchemaBuilder::title` (top-level → Specs): sets the title to
`c = title.into()` (upstream lines 1746–1749, patched 1736–1739).

Premise: caller code. Not covered: (I). -/
@[step]
theorem ElicitationSchemaBuilder.impl.title_spec {TitleLike : Type}
    (titleInto : core.convert.Into TitleLike (rmcp.alloc.borrow.Cow Str String))
    (self : ElicitationSchemaBuilder) (title : TitleLike) (c : rmcp.alloc.borrow.Cow Str String)
    (h_title_into : titleInto.into title = ok c) :
    rmcp.model.elicitation_schema.ElicitationSchemaBuilder.impl.title titleInto self title ⦃
      (result : ElicitationSchemaBuilder) =>
      result = { self with title := some c } ⦄ := by
  simp [ElicitationSchemaBuilder.impl.title, h_title_into]

/-- **Spec theorem for
`rmcp::model::elicitation_schema::ElicitationSchemaBuilder::description`** (X73)

X73 `ElicitationSchemaBuilder::description` (top-level → Specs): sets the description to
`c = description.into()` (upstream lines 1752–1755, patched 1742–1745).

Premise: caller code. Not covered: (I). -/
@[step]
theorem ElicitationSchemaBuilder.impl.description_spec {DescriptionLike : Type}
    (descriptionInto : core.convert.Into DescriptionLike (rmcp.alloc.borrow.Cow Str String))
    (self : ElicitationSchemaBuilder) (description : DescriptionLike)
    (c : rmcp.alloc.borrow.Cow Str String)
    (h_description_into : descriptionInto.into description = ok c) :
    rmcp.model.elicitation_schema.ElicitationSchemaBuilder.impl.description descriptionInto self
      description ⦃ (result : ElicitationSchemaBuilder) =>
      result = { self with description := some c } ⦄ := by
  simp [ElicitationSchemaBuilder.impl.description, h_description_into]

/-- **Spec theorem for `rmcp::model::elicitation_schema::ElicitationSchemaBuilder::build`** (X74)

X74 `ElicitationSchemaBuilder::build` (intermediate → Internal; linkage patch-08, hunk E7):
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
@[step]
theorem ElicitationSchemaBuilder.build_spec
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
      | .Err e =>
        ¬ RequiredPropertiesExist self ∧ e.val = utf8Bytes requiredNotInPropertiesMsg ⦄ := by
  obtain ⟨names, hn, hnv⟩ := sorted_keys_eq_ok self.properties h_fit
  obtain ⟨it, hall⟩ := build_all_eq self.required names
  unfold ElicitationSchemaBuilder.build
  simp only [hn, bind_ok, alloc.vec.Vec.is_empty, core.slice.Slice.iter]
  by_cases hr : self.required.val = []
  · have hl : self.required.length = 0 := by simp [hr]
    simp only [hl, decide_true, ↓reduceIte]
    refine (WP.spec_ok _).2
      ⟨?_, rfl, rfl, rfl, by rw [Option.map_some, hnv], by rw [ite_eq_left hr], rfl⟩
    intro r h; simp [hr] at h
  · have hl : ¬ self.required.length = 0 := by simpa using hr
    simp only [hl, decide_false, Bool.false_eq_true, ↓reduceIte, hall, bind_ok]
    by_cases hq : ∀ r ∈ self.required.val, r ∈ names.val
    · simp only [decide_eq_true hq]
      exact (WP.spec_ok _).2 ⟨fun r h => hnv ▸ hq r h, rfl, rfl, rfl, by rw [Option.map_some, hnv],
        by rw [ite_eq_right hr], rfl⟩
    · simp only [decide_eq_false hq]
      exact (WP.spec_ok _).2 ⟨fun h => hq (fun r hr' => hnv ▸ h r hr'),
        Proofs.External.Utf8.toStr_val _ _⟩

/-- **Failing case of `rmcp::model::elicitation_schema::ElicitationSchemaBuilder::build`** (X74)

X74, failing case (intermediate → Internal): when the key list would exceed `isize::MAX`
bytes, the model of `prim::sorted_keys` panics before any check (no Rust map is that large). -/
theorem ElicitationSchemaBuilder.build_fail
    (self : ElicitationSchemaBuilder) (h_big : ¬ PropertiesFit self.properties) :
    rmcp.model.elicitation_schema.ElicitationSchemaBuilder.build self = fail .panic := by
  unfold ElicitationSchemaBuilder.build
  rw [model.elicitation_schema.prim.sorted_keys_eq_fail self.properties
    (by unfold PropertiesFit at h_big; omega), bind_fail]

/-- **Spec theorem for
`rmcp::model::elicitation_schema::ElicitationSchemaBuilder::build_unchecked`** (X75)

X75 `ElicitationSchemaBuilder::build_unchecked` (top-level → Specs; linkage patch-08, as it
calls X74): when every required name is a property, the schema of X74 (upstream lines 1795–1797,
patched 1788–1790). **H19**, **H20** as X74. Builders a caller holds can violate (Q) (pub fields,
X71), and then this function panics: see `build_unchecked_fail`.

Premises: (L), (Q). Not covered: (A). The other inputs are
`ElicitationSchemaBuilder.build_unchecked_fail`. -/
@[step]
theorem ElicitationSchemaBuilder.build_unchecked_spec
    (self : ElicitationSchemaBuilder) (h_fit : PropertiesFit self.properties)
    (h_required : RequiredPropertiesExist self) :
    rmcp.model.elicitation_schema.ElicitationSchemaBuilder.build_unchecked self ⦃
      (result : ElicitationSchema) =>
      result.schema = none ∧ result.title = self.title ∧ result.properties = self.properties ∧
        result.property_order.map (·.val) = some (propertyNames self.properties) ∧
        result.required = (if self.required.val = [] then none else some self.required) ∧
        result.description = self.description ⦄ := by
  obtain ⟨r, hr, hp⟩ := Proofs.External.WP.exists_ok_of_spec
    (ElicitationSchemaBuilder.build_spec self h_fit)
  unfold ElicitationSchemaBuilder.build_unchecked
  rw [hr, bind_ok]
  cases r with
  | Ok s => exact (WP.spec_ok _).2 hp.2
  | Err e => exact absurd h_required hp.1

/-- **Failing case of
`rmcp::model::elicitation_schema::ElicitationSchemaBuilder::build_unchecked`** (X75)

X75, failing case (top-level → Specs): `build_unchecked` panics exactly when a required name
is not a property when it runs (`expect`, upstream line 1796; message not modelled, (D)), as
after X71 `mark_required` of a name for which no property was added afterwards (H20), or a direct
write to the `pub` field `required`, or, in the model, when the key list does not fit (L). -/
theorem ElicitationSchemaBuilder.build_unchecked_fail
    (self : ElicitationSchemaBuilder)
    (h_bad : ¬ (PropertiesFit self.properties ∧ RequiredPropertiesExist self)) :
    rmcp.model.elicitation_schema.ElicitationSchemaBuilder.build_unchecked self = fail .panic := by
  unfold ElicitationSchemaBuilder.build_unchecked
  by_cases h_fit : PropertiesFit self.properties
  · have h_req : ¬ RequiredPropertiesExist self := fun h => h_bad ⟨h_fit, h⟩
    obtain ⟨r, hr, hp⟩ := Proofs.External.WP.exists_ok_of_spec
      (ElicitationSchemaBuilder.build_spec self h_fit)
    rw [hr, bind_ok]
    cases r with
    | Ok s => exact absurd hp.1 h_req
    | Err e => rfl
  · rw [ElicitationSchemaBuilder.build_fail self h_fit, bind_fail]

/-- Composition X40 (top-level → Specs): `ElicitationSchema::new` gives a consistent schema (no
required list; the property order is the property names).

Premise: (L). Not covered: (A). -/
theorem ElicitationSchema.new_consistent
    (properties : alloc.collections.btree.map.BTreeMap String PrimitiveSchemaDefinition
      alloc.alloc.Global)
    (h_fit : PropertiesFit properties) :
    rmcp.model.elicitation_schema.ElicitationSchema.new properties ⦃
      (result : ElicitationSchema) =>
      ConsistentElicitationSchema result ⦄ := by
  apply WP.spec_mono (ElicitationSchema.new_spec properties h_fit)
  rintro s ⟨-, -, hprops, horder, hreq, -⟩
  refine ⟨fun rs hrs => ?_, by rw [horder, hprops]⟩
  rw [hreq] at hrs
  cases hrs

/-- Composition X74 (intermediate → Internal): every schema `build` accepts is consistent: its
required names (if any) are properties, its property order is the property names (its map is the
builder's, so it is sorted if the builder's is). **H19**, **H20** (empty property map and
duplicate required names are consistent).

Premise: (L). Not covered: (A). -/
theorem ElicitationSchemaBuilder.build_consistent
    (self : ElicitationSchemaBuilder) (h_fit : PropertiesFit self.properties) :
    rmcp.model.elicitation_schema.ElicitationSchemaBuilder.build self ⦃
      (result : core.result.Result ElicitationSchema Str) =>
      ∀ s, result = .Ok s →
        ConsistentElicitationSchema s ⦄ := by
  apply WP.spec_mono (ElicitationSchemaBuilder.build_spec self h_fit)
  rintro r hp s rfl
  obtain ⟨hq, -, -, hprops, horder, hreq, -⟩ := hp
  refine ⟨fun rs hrs => ?_, by rw [horder, hprops]⟩
  rw [hreq] at hrs
  split at hrs
  · cases hrs
  · cases hrs
    rw [hprops]
    exact ⟨by assumption, hq⟩

/-- Composition X75 (top-level → Specs): the schema `build_unchecked` returns is consistent (its
map is the builder's). **H19**, **H20**.

Premises: (L), (Q). Not covered: (A). -/
theorem ElicitationSchemaBuilder.build_unchecked_consistent
    (self : ElicitationSchemaBuilder) (h_fit : PropertiesFit self.properties)
    (h_required : RequiredPropertiesExist self) :
    rmcp.model.elicitation_schema.ElicitationSchemaBuilder.build_unchecked self ⦃
      (result : ElicitationSchema) =>
      ConsistentElicitationSchema result ⦄ := by
  apply WP.spec_mono
    (ElicitationSchemaBuilder.build_unchecked_spec self h_fit h_required)
  rintro s ⟨-, -, hprops, horder, hreq, -⟩
  refine ⟨fun rs hrs => ?_, by rw [horder, hprops]⟩
  rw [hreq] at hrs
  split at hrs
  · cases hrs
  · cases hrs
    rw [hprops]
    exact ⟨by assumption, h_required⟩

/-- Composition X46+X74 (intermediate → Internal), **H19**: `build` on a new builder returns
`Ok`, a schema with no property and no required list, although the documentation (upstream line
1763) lists "No properties are defined (empty schema)" as an error. No premise. -/
theorem ElicitationSchemaBuilder.build_new :
    (do
      let b ← rmcp.model.elicitation_schema.ElicitationSchemaBuilder.new
      rmcp.model.elicitation_schema.ElicitationSchemaBuilder.build b) ⦃
      (result : core.result.Result ElicitationSchema Str) =>
      ∃ s, result = .Ok s ∧ s.properties.entries = [] ∧ s.required = none ⦄ := by
  have hnew : ElicitationSchemaBuilder.new =
      ok emptyElicitationSchemaBuilder := elicitationSchemaBuilder_new_eq
  have hfit : PropertiesFit emptyElicitationSchemaBuilder.properties := by
    unfold PropertiesFit; simp [emptyElicitationSchemaBuilder]
  rw [hnew, bind_ok]
  apply WP.spec_mono
    (ElicitationSchemaBuilder.build_spec _ hfit)
  intro r hp
  cases r with
  | Ok s =>
    refine ⟨s, rfl, by rw [hp.2.2.2.1]; rfl, ?_⟩
    rw [hp.2.2.2.2.2.1]
    simp [emptyElicitationSchemaBuilder, alloc.vec.Vec.new]
  | Err e =>
    exact absurd (fun r h => by simp [emptyElicitationSchemaBuilder, alloc.vec.Vec.new] at h) hp.1

/-- Composition X45+X75 (top-level → Specs), **H19**: `build_unchecked` on
`ElicitationSchema::builder()` returns (does not panic) a schema with no property and no required
list. No premise. -/
theorem ElicitationSchema.builder_build_unchecked_empty :
    (do
      let b ← rmcp.model.elicitation_schema.ElicitationSchema.builder
      rmcp.model.elicitation_schema.ElicitationSchemaBuilder.build_unchecked b) ⦃
      (result : ElicitationSchema) =>
      result.properties.entries = [] ∧ result.required = none ⦄ := by
  have hnew : ElicitationSchema.builder =
      ok emptyElicitationSchemaBuilder := elicitationSchemaBuilder_new_eq
  have hfit : PropertiesFit emptyElicitationSchemaBuilder.properties := by
    unfold PropertiesFit; simp [emptyElicitationSchemaBuilder]
  have hq : RequiredPropertiesExist emptyElicitationSchemaBuilder := by
    intro r h; simp [emptyElicitationSchemaBuilder, alloc.vec.Vec.new] at h
  rw [hnew, bind_ok]
  apply WP.spec_mono
    (ElicitationSchemaBuilder.build_unchecked_spec _ hfit hq)
  rintro s ⟨-, -, hprops, -, hreq, -⟩
  refine ⟨by rw [hprops]; rfl, ?_⟩
  rw [hreq]
  simp [emptyElicitationSchemaBuilder, alloc.vec.Vec.new]

end rmcp.model.elicitation_schema

namespace Defs.ElicitationSchema

/-- Model law: inserting property `n` keeps every name already present and adds `n`, so a
required list whose names are all properties stays so after appending `n`. This is why X48, X50,
X52, X54, X55, X57, X59, X61, X63, X65, X67, X69 (append `n` and insert it) and X47, X49, X51,
X53, X56, X58, X60, X62, X64, X66, X68, X70 (required list unchanged) keep (Q); X71 appends
without inserting and can break it. No premise. -/
theorem PropertyInserted.forall_mem_propertyNames_append
    (old new : alloc.collections.btree.map.BTreeMap String PrimitiveSchemaDefinition
      alloc.alloc.Global)
    (n : String) (v : PrimitiveSchemaDefinition) (rs : List String)
    (h_ins : PropertyInserted old n v new) (h_rs : ∀ r ∈ rs, r ∈ propertyNames old) :
    ∀ r ∈ rs ++ [n], r ∈ propertyNames new := by
  have key : ∀ k, k ∈ propertyNames new ↔ (propertyLookup new k).isSome := by
    intro k
    simp [propertyNames, propertyLookup, List.find?_isSome]
  have key' : ∀ k, k ∈ propertyNames old ↔ (propertyLookup old k).isSome := by
    intro k
    simp [propertyNames, propertyLookup, List.find?_isSome]
  intro r hr
  rw [key, h_ins.1 r]
  rcases List.mem_append.1 hr with hr | hr
  · split
    · rfl
    · exact (key' r).1 (h_rs r hr)
  · rw [List.mem_singleton] at hr
    simp [hr]

/-- Model law: the empty builder (X45, X46) meets `RequiredPropertiesExist` (Q). No premise. -/
theorem requiredPropertiesExist_emptyElicitationSchemaBuilder :
    RequiredPropertiesExist emptyElicitationSchemaBuilder := by
  intro r hr
  simp [emptyElicitationSchemaBuilder, alloc.vec.Vec.new] at hr

/-- Model law: the map of the empty builder (X45, X46) is sorted. No premise. -/
theorem keysSorted_emptyElicitationSchemaBuilder_properties :
    KeysSorted emptyElicitationSchemaBuilder.properties := List.Pairwise.nil

end Defs.ElicitationSchema
