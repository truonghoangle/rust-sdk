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
# Spec theorems for the primitive schemas of `elicitation_schema.rs` (X01–X25)

The constructors and setters of `StringSchema` (X01–X13), `IntegerSchema` (X14–X21) and
`BooleanSchema` (X22–X25): each returns the default schema or `self` with the fields it sets.
The validating setters `with_length` (X08) and `with_range` (X15) return `Err` with their message
when `min > max`; `length` (X09) and `range` (X16) panic then (`assert!`), with the companions
`StringSchema.length_fail` and `IntegerSchema.range_fail`. All are proved by unfolding.

Source: "crates/rmcp/src/model/elicitation_schema.rs", upstream and patched lines 126–517
(unchanged by translation patch 08; the line of each function is in its docstring).
-/

open Aeneas Aeneas.Std Result
open Defs (utf8Bytes)
open Defs.ElicitationSchema
open rmcp.model.elicitation_schema (StringSchema StringFormat IntegerSchema BooleanSchema
  ConstTitle EnumSchema EnumSchemaBuilder SingleSelect MultiSelect PrimitiveSchemaDefinition
  ElicitationSchema ElicitationSchemaBuilder)
open Proofs.External.ElicitationSchema Proofs.Model.ElicitationSchema

namespace rmcp.model.elicitation_schema

/-- **Spec theorem for `rmcp::model::elicitation_schema::StringSchema::new`** (X01)

X01 `StringSchema::new` (intermediate → Internal): the default string schema
(`Self::default()`, upstream and patched lines 142–144; `Default`, lines 126–138). No premise. -/
@[step]
theorem StringSchema.new_spec :
    rmcp.model.elicitation_schema.StringSchema.new ⦃ (result : StringSchema) =>
      result = defaultStringSchema ⦄ := by
  simp [StringSchema.new,
    StringSchema.Insts.CoreDefaultDefault.default,
    defaultStringSchema]

/-- **Spec theorem for `rmcp::model::elicitation_schema::StringSchema::email`** (X02)

X02 `StringSchema::email` (intermediate → Internal): the default string schema with format
`Email` (upstream and patched lines 147–152). No premise. -/
@[step]
theorem StringSchema.email_spec :
    rmcp.model.elicitation_schema.StringSchema.email ⦃ (result : StringSchema) =>
      result = { defaultStringSchema with format := some .Email } ⦄ := by
  simp [StringSchema.email,
    StringSchema.Insts.CoreDefaultDefault.default,
    defaultStringSchema]

/-- **Spec theorem for `rmcp::model::elicitation_schema::StringSchema::uri`** (X03)

X03 `StringSchema::uri` (top-level → Specs): the default string schema with format `Uri`
(upstream and patched lines 155–160). No premise. -/
@[step]
theorem StringSchema.uri_spec :
    rmcp.model.elicitation_schema.StringSchema.uri ⦃ (result : StringSchema) =>
      result = { defaultStringSchema with format := some .Uri } ⦄ := by
  simp [StringSchema.uri,
    StringSchema.Insts.CoreDefaultDefault.default, defaultStringSchema]

/-- **Spec theorem for `rmcp::model::elicitation_schema::StringSchema::date`** (X04)

X04 `StringSchema::date` (top-level → Specs): the default string schema with format `Date`
(upstream and patched lines 163–168). No premise. -/
@[step]
theorem StringSchema.date_spec :
    rmcp.model.elicitation_schema.StringSchema.date ⦃ (result : StringSchema) =>
      result = { defaultStringSchema with format := some .Date } ⦄ := by
  simp [StringSchema.date,
    StringSchema.Insts.CoreDefaultDefault.default, defaultStringSchema]

/-- **Spec theorem for `rmcp::model::elicitation_schema::StringSchema::date_time`** (X05)

X05 `StringSchema::date_time` (top-level → Specs): the default string schema with format
`DateTime` (upstream and patched lines 171–176). No premise. -/
@[step]
theorem StringSchema.date_time_spec :
    rmcp.model.elicitation_schema.StringSchema.date_time ⦃ (result : StringSchema) =>
      result = { defaultStringSchema with format := some .DateTime } ⦄ := by
  simp [StringSchema.date_time,
    StringSchema.Insts.CoreDefaultDefault.default, defaultStringSchema]

/-- **Spec theorem for `rmcp::model::elicitation_schema::StringSchema::title`** (X06)

X06 `StringSchema::title` (top-level → Specs): sets the title to `c = title.into()`, other
fields unchanged (upstream and patched lines 179–182).

Premise: caller code. Not covered: (I). -/
@[step]
theorem StringSchema.impl.title_spec {TitleLike : Type}
    (titleInto : core.convert.Into TitleLike (rmcp.alloc.borrow.Cow Str String))
    (self : StringSchema) (title : TitleLike) (c : rmcp.alloc.borrow.Cow Str String)
    (h_title_into : titleInto.into title = ok c) :
    rmcp.model.elicitation_schema.StringSchema.impl.title titleInto self title ⦃
      (result : StringSchema) =>
      result = { self with title := some c } ⦄ := by
  simp [StringSchema.impl.title, h_title_into]

/-- **Spec theorem for `rmcp::model::elicitation_schema::StringSchema::description`** (X07)

X07 `StringSchema::description` (top-level → Specs): sets the description to
`c = description.into()`, other fields unchanged (upstream and patched lines 185–188).

Premise: caller code. Not covered: (I). -/
@[step]
theorem StringSchema.impl.description_spec {DescriptionLike : Type}
    (descriptionInto : core.convert.Into DescriptionLike (rmcp.alloc.borrow.Cow Str String))
    (self : StringSchema) (description : DescriptionLike) (c : rmcp.alloc.borrow.Cow Str String)
    (h_description_into : descriptionInto.into description = ok c) :
    rmcp.model.elicitation_schema.StringSchema.impl.description descriptionInto self description ⦃
      (result : StringSchema) =>
      result = { self with description := some c } ⦄ := by
  simp [StringSchema.impl.description, h_description_into]

/-- **Spec theorem for `rmcp::model::elicitation_schema::StringSchema::with_length`** (X08)

X08 `StringSchema::with_length` (top-level → Specs): `Ok` with both length bounds set when
`min ≤ max`; otherwise `Err("min_length must be <= max_length")`, the schema dropped (upstream and
patched lines 191–198). No premise. -/
@[step]
theorem StringSchema.with_length_spec (self : StringSchema)
    (min max : U32) :
    rmcp.model.elicitation_schema.StringSchema.with_length self min max ⦃
      (result : core.result.Result StringSchema Str) =>
      match result with
      | .Ok s =>
        min.val ≤ max.val ∧ s = { self with min_length := some min, max_length := some max }
      | .Err e => max.val < min.val ∧ e.val = utf8Bytes minLengthGtMaxLengthMsg ⦄ := by
  unfold StringSchema.with_length
  split
  · simp only [WP.spec_ok, Proofs.External.Utf8.toStr_val]
    exact ⟨by scalar_tac, rfl⟩
  · simp only [WP.spec_ok, and_true]
    scalar_tac

/-- **Spec theorem for `rmcp::model::elicitation_schema::StringSchema::length`** (X09)

X09 `StringSchema::length` (top-level → Specs): for `min ≤ max`, both length bounds set
(upstream and patched lines 201–206).

Premise: (B). The case `min > max` is `StringSchema.length_fail`. -/
@[step]
theorem StringSchema.length_spec (self : StringSchema) (min max : U32)
    (h_le : min.val ≤ max.val) :
    rmcp.model.elicitation_schema.StringSchema.length self min max ⦃ (result : StringSchema) =>
      result = { self with min_length := some min, max_length := some max } ⦄ := by
  unfold StringSchema.length
  have : (min <= max) = true := by scalar_tac
  simp [massert, this]

/-- **Failing case of `rmcp::model::elicitation_schema::StringSchema::length`** (X09)

X09, failing case (top-level → Specs): for `min > max` the `assert!` panics (upstream line
202; Aeneas `massert`, `fail assertionFailure`). -/
theorem StringSchema.length_fail (self : StringSchema)
    (min max : U32) (h_gt : max.val < min.val) :
    rmcp.model.elicitation_schema.StringSchema.length self min max = fail .assertionFailure := by
  unfold StringSchema.length
  have : (min <= max) = false := by scalar_tac
  simp [massert, this]

/-- **Spec theorem for `rmcp::model::elicitation_schema::StringSchema::min_length`** (X10)

X10 `StringSchema::min_length` (top-level → Specs): sets the minimum length, other fields
unchanged (upstream and patched lines 209–212). **H21**: no check against `max_length` or the
default. No premise. -/
@[step]
theorem StringSchema.impl.min_length_spec (self : StringSchema) (min : U32) :
    rmcp.model.elicitation_schema.StringSchema.impl.min_length self min ⦃
      (result : StringSchema) =>
      result = { self with min_length := some min } ⦄ := by
  simp [StringSchema.impl.min_length]

/-- **Spec theorem for `rmcp::model::elicitation_schema::StringSchema::max_length`** (X11)

X11 `StringSchema::max_length` (top-level → Specs): sets the maximum length, other fields
unchanged (upstream and patched lines 215–218). **H21**: no check against `min_length` or the
default. No premise. -/
@[step]
theorem StringSchema.impl.max_length_spec (self : StringSchema) (max : U32) :
    rmcp.model.elicitation_schema.StringSchema.impl.max_length self max ⦃
      (result : StringSchema) =>
      result = { self with max_length := some max } ⦄ := by
  simp [StringSchema.impl.max_length]

/-- **Spec theorem for `rmcp::model::elicitation_schema::StringSchema::format`** (X12)

X12 `StringSchema::format` (top-level → Specs): sets the format, other fields unchanged
(upstream and patched lines 221–224). No premise. -/
@[step]
theorem StringSchema.impl.format_spec (self : StringSchema)
    (format : StringFormat) :
    rmcp.model.elicitation_schema.StringSchema.impl.format self format ⦃
      (result : StringSchema) =>
      result = { self with format := some format } ⦄ := by
  simp [StringSchema.impl.format]

/-- **Spec theorem for `rmcp::model::elicitation_schema::StringSchema::with_default`** (X13)

X13 `StringSchema::with_default` (top-level → Specs): sets the default to
`d = default.into()`, other fields unchanged (upstream and patched lines 227–230). **H21**: the
default is not checked against the length bounds or the format.

Premise: caller code. Not covered: (I). -/
@[step]
theorem StringSchema.with_default_spec {DefaultLike : Type}
    (defaultInto : core.convert.Into DefaultLike String) (self : StringSchema)
    (default : DefaultLike) (d : String) (h_default_into : defaultInto.into default = ok d) :
    rmcp.model.elicitation_schema.StringSchema.with_default defaultInto self default ⦃
      (result : StringSchema) =>
      result = { self with default := some d } ⦄ := by
  simp [StringSchema.with_default, h_default_into]

/-- **Spec theorem for `rmcp::model::elicitation_schema::IntegerSchema::new`** (X14)

X14 `IntegerSchema::new` (intermediate → Internal): the default integer schema
(`Self::default()`, upstream and patched lines 404–406; `Default`, lines 389–400). No premise. -/
@[step]
theorem IntegerSchema.new_spec :
    rmcp.model.elicitation_schema.IntegerSchema.new ⦃ (result : IntegerSchema) =>
      result = defaultIntegerSchema ⦄ := by
  simp [IntegerSchema.new, IntegerSchema.Insts.CoreDefaultDefault.default,
    defaultIntegerSchema]

/-- **Spec theorem for `rmcp::model::elicitation_schema::IntegerSchema::with_range`** (X15)

X15 `IntegerSchema::with_range` (top-level → Specs): `Ok` with both bounds set when
`min ≤ max`; otherwise `Err("minimum must be <= maximum")` (upstream and patched lines 409–416).
No premise. -/
@[step]
theorem IntegerSchema.with_range_spec (self : IntegerSchema)
    (min max : I64) :
    rmcp.model.elicitation_schema.IntegerSchema.with_range self min max ⦃
      (result : core.result.Result IntegerSchema Str) =>
      match result with
      | .Ok s => min.val ≤ max.val ∧ s = { self with minimum := some min, maximum := some max }
      | .Err e => max.val < min.val ∧ e.val = utf8Bytes minimumGtMaximumMsg ⦄ := by
  unfold IntegerSchema.with_range
  split
  · simp only [WP.spec_ok, Proofs.External.Utf8.toStr_val]
    exact ⟨by scalar_tac, rfl⟩
  · simp only [WP.spec_ok, and_true]
    scalar_tac

/-- **Spec theorem for `rmcp::model::elicitation_schema::IntegerSchema::range`** (X16)

X16 `IntegerSchema::range` (intermediate → Internal): for `min ≤ max`, both bounds set
(upstream and patched lines 419–424).

Premise: (B). The case `min > max` is `IntegerSchema.range_fail`. -/
@[step]
theorem IntegerSchema.range_spec (self : IntegerSchema) (min max : I64)
    (h_le : min.val ≤ max.val) :
    rmcp.model.elicitation_schema.IntegerSchema.range self min max ⦃ (result : IntegerSchema) =>
      result = { self with minimum := some min, maximum := some max } ⦄ := by
  unfold IntegerSchema.range
  have : (min <= max) = true := by scalar_tac
  simp [massert, this]

/-- **Failing case of `rmcp::model::elicitation_schema::IntegerSchema::range`** (X16)

X16, failing case (intermediate → Internal): for `min > max` the `assert!` panics (upstream
line 420). -/
theorem IntegerSchema.range_fail (self : IntegerSchema)
    (min max : I64) (h_gt : max.val < min.val) :
    rmcp.model.elicitation_schema.IntegerSchema.range self min max = fail .assertionFailure := by
  unfold IntegerSchema.range
  have : (min <= max) = false := by scalar_tac
  simp [massert, this]

/-- **Spec theorem for `rmcp::model::elicitation_schema::IntegerSchema::minimum`** (X17)

X17 `IntegerSchema::minimum` (top-level → Specs): sets the minimum, other fields unchanged
(upstream and patched lines 427–430). **H21**: no check against `maximum` or the default.
No premise. -/
@[step]
theorem IntegerSchema.impl.minimum_spec (self : IntegerSchema) (min : I64) :
    rmcp.model.elicitation_schema.IntegerSchema.impl.minimum self min ⦃
      (result : IntegerSchema) =>
      result = { self with minimum := some min } ⦄ := by
  simp [IntegerSchema.impl.minimum]

/-- **Spec theorem for `rmcp::model::elicitation_schema::IntegerSchema::maximum`** (X18)

X18 `IntegerSchema::maximum` (top-level → Specs): sets the maximum, other fields unchanged
(upstream and patched lines 433–436). **H21**: no check against `minimum` or the default.
No premise. -/
@[step]
theorem IntegerSchema.impl.maximum_spec (self : IntegerSchema) (max : I64) :
    rmcp.model.elicitation_schema.IntegerSchema.impl.maximum self max ⦃
      (result : IntegerSchema) =>
      result = { self with maximum := some max } ⦄ := by
  simp [IntegerSchema.impl.maximum]

/-- **Spec theorem for `rmcp::model::elicitation_schema::IntegerSchema::title`** (X19)

X19 `IntegerSchema::title` (top-level → Specs): sets the title to `c = title.into()`
(upstream and patched lines 439–442).

Premise: caller code. Not covered: (I). -/
@[step]
theorem IntegerSchema.impl.title_spec {TitleLike : Type}
    (titleInto : core.convert.Into TitleLike (rmcp.alloc.borrow.Cow Str String))
    (self : IntegerSchema) (title : TitleLike) (c : rmcp.alloc.borrow.Cow Str String)
    (h_title_into : titleInto.into title = ok c) :
    rmcp.model.elicitation_schema.IntegerSchema.impl.title titleInto self title ⦃
      (result : IntegerSchema) =>
      result = { self with title := some c } ⦄ := by
  simp [IntegerSchema.impl.title, h_title_into]

/-- **Spec theorem for `rmcp::model::elicitation_schema::IntegerSchema::description`** (X20)

X20 `IntegerSchema::description` (top-level → Specs): sets the description to
`c = description.into()` (upstream and patched lines 445–448).

Premise: caller code. Not covered: (I). -/
@[step]
theorem IntegerSchema.impl.description_spec {DescriptionLike : Type}
    (descriptionInto : core.convert.Into DescriptionLike (rmcp.alloc.borrow.Cow Str String))
    (self : IntegerSchema) (description : DescriptionLike) (c : rmcp.alloc.borrow.Cow Str String)
    (h_description_into : descriptionInto.into description = ok c) :
    rmcp.model.elicitation_schema.IntegerSchema.impl.description descriptionInto self
      description ⦃ (result : IntegerSchema) =>
      result = { self with description := some c } ⦄ := by
  simp [IntegerSchema.impl.description, h_description_into]

/-- **Spec theorem for `rmcp::model::elicitation_schema::IntegerSchema::with_default`** (X21)

X21 `IntegerSchema::with_default` (top-level → Specs): sets the default, other fields
unchanged (upstream and patched lines 451–454). **H21**: the default is not checked against the
bounds. No premise. -/
@[step]
theorem IntegerSchema.with_default_spec (self : IntegerSchema)
    (default : I64) :
    rmcp.model.elicitation_schema.IntegerSchema.with_default self default ⦃
      (result : IntegerSchema) =>
      result = { self with default := some default } ⦄ := by
  simp [IntegerSchema.with_default]

/-- **Spec theorem for `rmcp::model::elicitation_schema::BooleanSchema::new`** (X22)

X22 `BooleanSchema::new` (intermediate → Internal): the default boolean schema
(`Self::default()`, upstream and patched lines 497–499; `Default`, lines 484–493). No premise. -/
@[step]
theorem BooleanSchema.new_spec :
    rmcp.model.elicitation_schema.BooleanSchema.new ⦃ (result : BooleanSchema) =>
      result = defaultBooleanSchema ⦄ := by
  simp [BooleanSchema.new, BooleanSchema.Insts.CoreDefaultDefault.default,
    defaultBooleanSchema]

/-- **Spec theorem for `rmcp::model::elicitation_schema::BooleanSchema::title`** (X23)

X23 `BooleanSchema::title` (top-level → Specs): sets the title to `c = title.into()`
(upstream and patched lines 502–505).

Premise: caller code. Not covered: (I). -/
@[step]
theorem BooleanSchema.impl.title_spec {TitleLike : Type}
    (titleInto : core.convert.Into TitleLike (rmcp.alloc.borrow.Cow Str String))
    (self : BooleanSchema) (title : TitleLike) (c : rmcp.alloc.borrow.Cow Str String)
    (h_title_into : titleInto.into title = ok c) :
    rmcp.model.elicitation_schema.BooleanSchema.impl.title titleInto self title ⦃
      (result : BooleanSchema) =>
      result = { self with title := some c } ⦄ := by
  simp [BooleanSchema.impl.title, h_title_into]

/-- **Spec theorem for `rmcp::model::elicitation_schema::BooleanSchema::description`** (X24)

X24 `BooleanSchema::description` (top-level → Specs): sets the description to
`c = description.into()` (upstream and patched lines 508–511).

Premise: caller code. Not covered: (I). -/
@[step]
theorem BooleanSchema.impl.description_spec {DescriptionLike : Type}
    (descriptionInto : core.convert.Into DescriptionLike (rmcp.alloc.borrow.Cow Str String))
    (self : BooleanSchema) (description : DescriptionLike) (c : rmcp.alloc.borrow.Cow Str String)
    (h_description_into : descriptionInto.into description = ok c) :
    rmcp.model.elicitation_schema.BooleanSchema.impl.description descriptionInto self
      description ⦃ (result : BooleanSchema) =>
      result = { self with description := some c } ⦄ := by
  simp [BooleanSchema.impl.description, h_description_into]

/-- **Spec theorem for `rmcp::model::elicitation_schema::BooleanSchema::with_default`** (X25)

X25 `BooleanSchema::with_default` (intermediate → Internal): sets the default, other fields
unchanged (upstream and patched lines 514–517). No premise. -/
@[step]
theorem BooleanSchema.with_default_spec (self : BooleanSchema)
    (default : Bool) :
    rmcp.model.elicitation_schema.BooleanSchema.with_default self default ⦃
      (result : BooleanSchema) =>
      result = { self with default := some default } ⦄ := by
  simp [BooleanSchema.with_default]

end rmcp.model.elicitation_schema
