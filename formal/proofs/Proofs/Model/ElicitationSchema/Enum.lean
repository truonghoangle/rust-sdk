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
# Spec theorems for the enum schema builders of `elicitation_schema.rs` (X26–X39)

The setters of `EnumSchemaBuilder<T>` (X26–X29), of `EnumSchemaBuilder<SingleSelect>` (X30–X33)
and `EnumSchemaBuilder<MultiSelect>` (X34–X38), and `EnumSchema::builder` (X39), with the
compositions saying that the constructors (including `impl Default for
EnumSchemaBuilder<SingleSelect>`) establish the builder invariants `ValidEnumSchemaBuilder` and
`ValidMultiSelectBuilder`, that the setters keep them, and that a valid builder builds a
consistent enum schema (`ConsistentEnumSchema`). The titled options of `build` (X33, X38) are
proved through `const_titles` (`Proofs.Model.ElicitationSchema.const_titles_eq`); the checks of
the multi-select setters through `multiSelectDefaultError?`, `minItemsError?` and
`maxItemsError?`.

Source: "crates/rmcp/src/model/elicitation_schema.rs", upstream lines 844–1140, patched lines
844–1130 (X29, X32, X33, X35–X38 through translation patch 08, hunks E1–E5, E8; the line of
each function is in its docstring).
-/

open Aeneas Aeneas.Std Result
open Defs (utf8Bytes)
open Defs.ElicitationSchema
open rmcp.model.elicitation_schema (StringSchema StringFormat IntegerSchema BooleanSchema
  ConstTitle EnumSchema EnumSchemaBuilder SingleSelect MultiSelect PrimitiveSchemaDefinition
  ElicitationSchema ElicitationSchemaBuilder)
open Proofs.External.ElicitationSchema Proofs.Model.ElicitationSchema

namespace rmcp.model.elicitation_schema

/-- **Spec theorem for `rmcp::model::elicitation_schema::EnumSchemaBuilder::title`** (X26)

X26 `EnumSchemaBuilder::title` (top-level → Specs): sets the title to `c = value.into()`,
other fields unchanged (upstream and patched lines 863–866).

Premise: caller code. Not covered: (I). -/
@[step]
theorem EnumSchemaBuilder.impl.title_spec {T ValueLike : Type}
    (valueInto : core.convert.Into ValueLike (rmcp.alloc.borrow.Cow Str String))
    (self : EnumSchemaBuilder T) (value : ValueLike) (c : rmcp.alloc.borrow.Cow Str String)
    (h_value_into : valueInto.into value = ok c) :
    rmcp.model.elicitation_schema.EnumSchemaBuilder.impl.title valueInto self value ⦃
      (result : EnumSchemaBuilder T) =>
      result = { self with title := some c } ⦄ := by
  simp [EnumSchemaBuilder.impl.title, h_value_into]

/-- **Spec theorem for `rmcp::model::elicitation_schema::EnumSchemaBuilder::description`** (X27)

X27 `EnumSchemaBuilder::description` (top-level → Specs): sets the description to
`c = value.into()`, other fields unchanged (upstream and patched lines 869–872).

Premise: caller code. Not covered: (I). -/
@[step]
theorem EnumSchemaBuilder.impl.description_spec {T ValueLike : Type}
    (valueInto : core.convert.Into ValueLike (rmcp.alloc.borrow.Cow Str String))
    (self : EnumSchemaBuilder T) (value : ValueLike) (c : rmcp.alloc.borrow.Cow Str String)
    (h_value_into : valueInto.into value = ok c) :
    rmcp.model.elicitation_schema.EnumSchemaBuilder.impl.description valueInto self value ⦃
      (result : EnumSchemaBuilder T) =>
      result = { self with description := some c } ⦄ := by
  simp [EnumSchemaBuilder.impl.description, h_value_into]

/-- **Spec theorem for `rmcp::model::elicitation_schema::EnumSchemaBuilder::untitled`** (X28)

X28 `EnumSchemaBuilder::untitled` (top-level → Specs): untitled, with no titles, other
fields unchanged (upstream and patched lines 876–880). No premise. -/
@[step]
theorem EnumSchemaBuilder.untitled_spec {T : Type}
    (self : EnumSchemaBuilder T) :
    rmcp.model.elicitation_schema.EnumSchemaBuilder.untitled self ⦃
      (result : EnumSchemaBuilder T) =>
      result = { self with titled := false, enum_titles := alloc.vec.Vec.new String } ⦄ := by
  simp [EnumSchemaBuilder.untitled]

/-- **Spec theorem for `rmcp::model::elicitation_schema::EnumSchemaBuilder::enum_titles`** (X29)

X29 `EnumSchemaBuilder::enum_titles` (top-level → Specs; linkage patch-08, hunk E1): `Ok`,
titled with these titles, when there are as many titles as values; otherwise
`Err` with the message of `titlesMismatchMsg (number of values) (number of titles)` (upstream
lines 883–894; patched lines 883–893, the `format!` in `prim::titles_mismatch_message`, patched
lines 1814–1819). No premise. Not covered: (A). -/
@[step]
theorem EnumSchemaBuilder.impl.enum_titles_spec {T : Type}
    (self : EnumSchemaBuilder T) (titles : alloc.vec.Vec String) :
    rmcp.model.elicitation_schema.EnumSchemaBuilder.impl.enum_titles self titles ⦃
      (result : core.result.Result (EnumSchemaBuilder T) String) =>
      match result with
      | .Ok b =>
        titles.val.length = self.enum_values.val.length ∧
          b = { self with titled := true, enum_titles := titles }
      | .Err e =>
        titles.val.length ≠ self.enum_values.val.length ∧
          e = titlesMismatchMsg self.enum_values.val.length titles.val.length ⦄ := by
  unfold EnumSchemaBuilder.impl.enum_titles
  dsimp only
  split
  · rename_i h
    simp only [model.elicitation_schema.prim.titles_mismatch_message, bind_ok, WP.spec_ok]
    refine ⟨?_, ?_⟩
    · simp only [bne_iff_ne, ne_eq] at h
      intro h'; apply h; scalar_tac
    · simp only [titlesMismatchMsg, alloc.vec.Vec.len]
      rfl
  · rename_i h
    simp only [WP.spec_ok, and_true]
    simp only [bne_iff_ne, ne_eq, Decidable.not_not] at h
    scalar_tac

/-- **Spec theorem for
`rmcp::model::elicitation_schema::EnumSchemaBuilder::<SingleSelect>::new`** (X30)

X30 `EnumSchemaBuilder::<SingleSelect>::new` (intermediate → Internal): the builder for
`values` with nothing else set (upstream lines 899–904, patched 898–903; `Default`, lines
844–858). No premise. -/
@[step]
theorem EnumSchemaBuilderSingleSelect.new_spec
    (values : alloc.vec.Vec String) :
    rmcp.model.elicitation_schema.EnumSchemaBuilderSingleSelect.new values ⦃
      (result : EnumSchemaBuilder SingleSelect) =>
      result = newEnumSchemaBuilder values ⦄ := by
  simp [EnumSchemaBuilderSingleSelect.new,
    EnumSchemaBuilderSingleSelect.Insts.CoreDefaultDefault.default,
    newEnumSchemaBuilder]

/-- **Spec theorem for
`rmcp::model::elicitation_schema::EnumSchemaBuilder::<SingleSelect>::multiselect`** (X31)

X31 `EnumSchemaBuilder::<SingleSelect>::multiselect` (top-level → Specs): the multi-select
builder with the same values, titles, title and description, and no item bounds or default
(upstream lines 911–923, patched 910–922). No premise. -/
@[step]
theorem EnumSchemaBuilderSingleSelect.multiselect_spec
    (self : EnumSchemaBuilder SingleSelect) :
    rmcp.model.elicitation_schema.EnumSchemaBuilderSingleSelect.multiselect self ⦃
      (result : EnumSchemaBuilder MultiSelect) =>
      result =
        { enum_values := self.enum_values, titled := self.titled, title := self.title,
          description := self.description, enum_titles := self.enum_titles, min_items := none,
          max_items := none, default := alloc.vec.Vec.new String, select_type := () } ⦄ := by
  simp [EnumSchemaBuilderSingleSelect.multiselect]

/-- **Spec theorem for
`rmcp::model::elicitation_schema::EnumSchemaBuilder::<SingleSelect>::with_default`** (X32)

X32 `EnumSchemaBuilder::<SingleSelect>::with_default` (top-level → Specs; linkage patch-08,
hunk E2): for `v = default_value.into()`, `Ok` with the default `[v]` when `v` is an enum value;
otherwise `Err("Provided default value is not in enum values")` (upstream lines 926–936; patched
lines 925–935).

Premise: caller code. Not covered: (I), (A). -/
@[step]
theorem EnumSchemaBuilderSingleSelect.with_default_spec
    {DefaultLike : Type} (defaultInto : core.convert.Into DefaultLike String)
    (self : EnumSchemaBuilder SingleSelect) (default_value : DefaultLike) (v : String)
    (h_default_into : defaultInto.into default_value = ok v) :
    rmcp.model.elicitation_schema.EnumSchemaBuilderSingleSelect.with_default defaultInto self
      default_value ⦃ (result : core.result.Result (EnumSchemaBuilder SingleSelect) String) =>
      match result with
      | .Ok b =>
        v ∈ self.enum_values.val ∧ b.default.val = [v] ∧ b = { self with default := b.default }
      | .Err e => v ∉ self.enum_values.val ∧ e = defaultNotInValuesMsg ⦄ := by
  unfold EnumSchemaBuilderSingleSelect.with_default
  simp only [h_default_into, bind_ok, Proofs.Transport.MetadataResolver.contains_string,
    to_owned_toStr, lift]
  by_cases hv : v ∈ (alloc.vec.Vec.deref self.enum_values).val
  · simp only [hv, decide_true, ↓reduceIte]
    refine (WP.spec_ok _).2 ⟨by simpa [alloc.vec.Vec.deref] using hv, ?_, rfl⟩
    rfl
  · simp only [hv, decide_false, Bool.false_eq_true, ↓reduceIte]
    exact (WP.spec_ok _).2 ⟨by simpa [alloc.vec.Vec.deref] using hv, rfl⟩

/-- **Spec theorem for
`rmcp::model::elicitation_schema::EnumSchemaBuilder::<SingleSelect>::build`** (X33)

X33 `EnumSchemaBuilder::<SingleSelect>::build` (top-level → Specs; linkage patch-08, hunk
E8): a single-select enum schema with the builder's title and description and, as default, the
last default value (`self.default.pop()`; at most one in practice). Titled: the options pair the
`i`-th title with the `i`-th value, as many as the shorter list (`constTitles`); untitled: the
values (upstream lines 939–965; patched lines 938–959, the options built by `const_titles`,
patched lines 1795–1805). No premise. Not covered: (A), (C). -/
@[step]
theorem EnumSchemaBuilderSingleSelect.build_spec
    (self : EnumSchemaBuilder SingleSelect) :
    rmcp.model.elicitation_schema.EnumSchemaBuilderSingleSelect.build self ⦃
      (result : EnumSchema) =>
      if self.titled then
        ∃ t, result = .Single (.Titled t) ∧ t.title = self.title ∧
          t.description = self.description ∧
          t.one_of.val = constTitles self.enum_titles.val self.enum_values.val ∧
          t.default = self.default.val.getLast?
      else
        ∃ u, result = .Single (.Untitled u) ∧ u.title = self.title ∧
          u.description = self.description ∧ u.enum_ = self.enum_values ∧
          u.default = self.default.val.getLast? ⦄ := by
  obtain ⟨v, hv, hvv⟩ := const_titles_eq self.enum_titles self.enum_values
  obtain ⟨⟨o, rest⟩, hp, hpo, -⟩ := Proofs.External.WP.exists_ok_of_spec
    (alloc.vec.Vec.pop_spec alloc.alloc.Global self.default)
  unfold EnumSchemaBuilderSingleSelect.build
  cases ht : self.titled
  · simp only [Bool.false_eq_true, ↓reduceIte, hp, bind_ok]
    exact (WP.spec_ok _).2 ⟨_, rfl, rfl, rfl, rfl, hpo⟩
  · simp only [↓reduceIte, hv, hp, bind_ok]
    exact (WP.spec_ok _).2 ⟨_, rfl, rfl, rfl, hvv, hpo⟩

/-- **Spec theorem for
`rmcp::model::elicitation_schema::EnumSchemaBuilder::<MultiSelect>::single_select`** (X34)

X34 `EnumSchemaBuilder::<MultiSelect>::single_select` (top-level → Specs): the single-select
builder with the same values, titles, title and description, and no item bounds or default
(upstream lines 972–984, patched 966–978). No premise. -/
@[step]
theorem EnumSchemaBuilderMultiSelect.single_select_spec
    (self : EnumSchemaBuilder MultiSelect) :
    rmcp.model.elicitation_schema.EnumSchemaBuilderMultiSelect.single_select self ⦃
      (result : EnumSchemaBuilder SingleSelect) =>
      result =
        { enum_values := self.enum_values, titled := self.titled, title := self.title,
          description := self.description, enum_titles := self.enum_titles, min_items := none,
          max_items := none, default := alloc.vec.Vec.new String, select_type := () } ⦄ := by
  simp [EnumSchemaBuilderMultiSelect.single_select]

/-- **Spec theorem for
`rmcp::model::elicitation_schema::EnumSchemaBuilder::<MultiSelect>::with_default`** (X35)

X35 `EnumSchemaBuilder::<MultiSelect>::with_default` (top-level → Specs; linkage patch-08,
hunk E3): `Ok` with the default `default_values` when every check passes; otherwise `Err` with
the message of the first failing check, in the Rust order (`multiSelectDefaultError?`: a value
not an enum value; for a non-empty default, fewer values than `min_items`, more than
`max_items`) (upstream lines 996–1023; patched lines 990–1018). An empty default passes the bound
checks. **H22**: duplicate default values are accepted. No premise. Not covered: (A). -/
@[step]
theorem EnumSchemaBuilderMultiSelect.with_default_spec
    (self : EnumSchemaBuilder MultiSelect) (default_values : alloc.vec.Vec String) :
    rmcp.model.elicitation_schema.EnumSchemaBuilderMultiSelect.with_default self default_values ⦃
      (result : core.result.Result (EnumSchemaBuilder MultiSelect) String) =>
      match result with
      | .Ok b =>
        multiSelectDefaultError? self default_values.val = none ∧
          b = { self with default := default_values }
      | .Err e => multiSelectDefaultError? self default_values.val = some e ⦄ := by
  obtain ⟨it, hall⟩ := withDefault_all_eq default_values self.enum_values
  have hlen : (UScalar.cast .U64 default_values.len).val = default_values.val.length := by
    rw [Proofs.RequestStateWire.val_cast_u64]; rfl
  unfold EnumSchemaBuilderMultiSelect.with_default
  simp only [core.slice.Slice.iter, hall, bind_ok, alloc.vec.Vec.is_empty, to_owned_toStr, lift]
  have hgt : ∀ m : U64, (UScalar.cast .U64 default_values.len > m) ↔
      m.val < default_values.val.length := by
    intro m; rw [gt_iff_lt, UScalar.lt_equiv, hlen]
  have hlt : ∀ m : U64, (UScalar.cast .U64 default_values.len < m) ↔
      default_values.val.length < m.val := by
    intro m; rw [UScalar.lt_equiv, hlen]
  have he : default_values.length = 0 ↔ default_values.val = [] := by simp
  by_cases hin : (default_values.val.all fun d => decide (d ∈ self.enum_values.val)) = true
  · simp only [hin]
    by_cases hemp : default_values.val = []
    · rw [ite_eq_left (by simpa using he.2 hemp)]
      exact (WP.spec_ok _).2 ⟨by simp [multiSelectDefaultError?, hemp], rfl⟩
    · rw [ite_eq_right (by simpa using fun h => hemp (he.1 h))]
      cases hmin : self.min_items with
      | none =>
        cases hmax : self.max_items with
        | none =>
          exact (WP.spec_ok _).2
            ⟨by simp [multiSelectDefaultError?, hin, hemp, hmin, hmax], rfl⟩
        | some hi =>
          dsimp only
          by_cases h1 : hi.val < default_values.val.length
          · rw [ite_eq_left ((hgt hi).2 h1)]
            exact (WP.spec_ok _).2 (by
              simp [multiSelectDefaultError?, defaultsAboveMaxItemsMsg, hin, hemp, hmin, hmax, h1])
          · rw [ite_eq_right (fun h => h1 ((hgt hi).1 h))]
            exact (WP.spec_ok _).2
              ⟨by simp [multiSelectDefaultError?, hin, hemp, hmin, hmax, h1], rfl⟩
      | some lo =>
        dsimp only
        by_cases h0 : default_values.val.length < lo.val
        · rw [ite_eq_left ((hlt lo).2 h0)]
          exact (WP.spec_ok _).2 (by
            simp [multiSelectDefaultError?, defaultsBelowMinItemsMsg, hin, hemp, hmin, h0])
        · rw [ite_eq_right (fun h => h0 ((hlt lo).1 h))]
          cases hmax : self.max_items with
          | none =>
            exact (WP.spec_ok _).2
              ⟨by simp [multiSelectDefaultError?, hin, hemp, hmin, hmax, h0], rfl⟩
          | some hi =>
            dsimp only
            by_cases h1 : hi.val < default_values.val.length
            · rw [ite_eq_left ((hgt hi).2 h1)]
              exact (WP.spec_ok _).2
                (by simp [multiSelectDefaultError?, defaultsAboveMaxItemsMsg, hin, hemp, hmin, hmax,
                  h0, h1])
            · rw [ite_eq_right (fun h => h1 ((hgt hi).1 h))]
              exact (WP.spec_ok _).2
                ⟨by simp [multiSelectDefaultError?, hin, hemp, hmin, hmax, h0, h1],
                  rfl⟩
  · simp only [hin]
    exact (WP.spec_ok _).2 (by simp [multiSelectDefaultError?, hin, defaultsNotInValuesMsg])

/-- **Spec theorem for
`rmcp::model::elicitation_schema::EnumSchemaBuilder::<MultiSelect>::min_items`** (X36)

X36 `EnumSchemaBuilder::<MultiSelect>::min_items` (top-level → Specs; linkage patch-08, hunk
E4): `Ok` with the minimum `value` when both checks pass; otherwise `Err` with the message of the
first failing check (`minItemsError?`: above `max_items`; a non-empty default with fewer values)
(upstream lines 1034–1046; patched lines 1029–1041). **H22**: `value` is not checked against the
number of enum values. No premise. Not covered: (A). -/
@[step]
theorem EnumSchemaBuilderMultiSelect.min_items_spec
    (self : EnumSchemaBuilder MultiSelect) (value : U64) :
    rmcp.model.elicitation_schema.EnumSchemaBuilderMultiSelect.min_items self value ⦃
      (result : core.result.Result (EnumSchemaBuilder MultiSelect) String) =>
      match result with
      | .Ok b => minItemsError? self value = none ∧ b = { self with min_items := some value }
      | .Err e => minItemsError? self value = some e ⦄ := by
  have hlen : (UScalar.cast .U64 self.default.len).val = self.default.val.length := by
    rw [Proofs.RequestStateWire.val_cast_u64]; rfl
  have hlt : (UScalar.cast .U64 self.default.len < value) ↔
      self.default.val.length < value.val := by
    rw [UScalar.lt_equiv, hlen]
  have he : self.default.length = 0 ↔ self.default.val = [] := by simp
  unfold EnumSchemaBuilderMultiSelect.min_items
  simp only [bind_ok, alloc.vec.Vec.is_empty, to_owned_toStr, lift]
  have hrest : ∀ b0 : EnumSchemaBuilder MultiSelect,
      (if decide (self.default.length = 0) = true then
        ok (core.result.Result.Ok b0)
      else if UScalar.cast .U64 self.default.len < value then
        ok (core.result.Result.Err "Number of provided default values is less than min_items")
      else ok (core.result.Result.Ok b0)) ⦃
      (result : core.result.Result (EnumSchemaBuilder MultiSelect) String) =>
      match result with
      | .Ok b => (¬ (self.default.val ≠ [] ∧ self.default.length < value.val)) ∧
          b = b0
      | .Err e => (self.default.val ≠ [] ∧ self.default.length < value.val) ∧
          e = defaultsBelowMinItemsMsg ⦄ := by
    intro b0
    by_cases hemp : self.default.val = []
    · rw [ite_eq_left (by simpa using he.2 hemp)]
      exact (WP.spec_ok _).2 ⟨by simp [hemp], rfl⟩
    · rw [ite_eq_right (by simpa using fun h => hemp (he.1 h))]
      by_cases h0 : self.default.val.length < value.val
      · rw [ite_eq_left (hlt.2 h0)]
        exact (WP.spec_ok _).2 ⟨⟨hemp, h0⟩, rfl⟩
      · rw [ite_eq_right (fun h => h0 (hlt.1 h))]
        exact (WP.spec_ok _).2 ⟨fun h => h0 h.2, rfl⟩
  cases hmax : self.max_items with
  | none =>
    dsimp only
    apply WP.spec_mono (hrest _)
    intro r hr
    cases r with
    | Ok b => exact ⟨by simp [minItemsError?, hmax, hr.1], hr.2⟩
    | Err e => simp [minItemsError?, hmax, hr.1, hr.2]
  | some hi =>
    dsimp only
    by_cases h1 : hi.val < value.val
    · rw [ite_eq_left (by rw [gt_iff_lt, UScalar.lt_equiv]; exact h1)]
      exact (WP.spec_ok _).2 (by simp [minItemsError?, hmax, h1, minItemsGtMaxItemsMsg])
    · rw [ite_eq_right (by rw [gt_iff_lt, UScalar.lt_equiv]; exact h1)]
      apply WP.spec_mono (hrest _)
      intro r hr
      cases r with
      | Ok b => exact ⟨by simp [minItemsError?, hmax, h1, hr.1], hr.2⟩
      | Err e => simp [minItemsError?, hmax, h1, hr.1, hr.2]

/-- **Spec theorem for
`rmcp::model::elicitation_schema::EnumSchemaBuilder::<MultiSelect>::max_items`** (X37)

X37 `EnumSchemaBuilder::<MultiSelect>::max_items` (top-level → Specs; linkage patch-08, hunk
E5): `Ok` with the maximum `value` when both checks pass; otherwise `Err` with the message of the
first failing check (`maxItemsError?`: below `min_items`; a non-empty default with more values)
(upstream lines 1057–1068; patched lines 1052–1063). A maximum above the number of enum values is
not checked. No premise. Not covered: (A). -/
@[step]
theorem EnumSchemaBuilderMultiSelect.max_items_spec
    (self : EnumSchemaBuilder MultiSelect) (value : U64) :
    rmcp.model.elicitation_schema.EnumSchemaBuilderMultiSelect.max_items self value ⦃
      (result : core.result.Result (EnumSchemaBuilder MultiSelect) String) =>
      match result with
      | .Ok b => maxItemsError? self value = none ∧ b = { self with max_items := some value }
      | .Err e => maxItemsError? self value = some e ⦄ := by
  have hlen : (UScalar.cast .U64 self.default.len).val = self.default.val.length := by
    rw [Proofs.RequestStateWire.val_cast_u64]; rfl
  have hgt : (UScalar.cast .U64 self.default.len > value) ↔
      value.val < self.default.val.length := by
    rw [gt_iff_lt, UScalar.lt_equiv, hlen]
  have he : self.default.length = 0 ↔ self.default.val = [] := by simp
  unfold EnumSchemaBuilderMultiSelect.max_items
  simp only [bind_ok, alloc.vec.Vec.is_empty, to_owned_toStr, lift]
  have hrest : ∀ b0 : EnumSchemaBuilder MultiSelect,
      (if decide (self.default.length = 0) = true then
        ok (core.result.Result.Ok b0)
      else if UScalar.cast .U64 self.default.len > value then
        ok (core.result.Result.Err "Number of provided default values is greater than max_items")
      else ok (core.result.Result.Ok b0)) ⦃
      (result : core.result.Result (EnumSchemaBuilder MultiSelect) String) =>
      match result with
      | .Ok b => (¬ (self.default.val ≠ [] ∧ value.val < self.default.length)) ∧
          b = b0
      | .Err e => (self.default.val ≠ [] ∧ value.val < self.default.length) ∧
          e = defaultsAboveMaxItemsMsg ⦄ := by
    intro b0
    by_cases hemp : self.default.val = []
    · rw [ite_eq_left (by simpa using he.2 hemp)]
      exact (WP.spec_ok _).2 ⟨by simp [hemp], rfl⟩
    · rw [ite_eq_right (by simpa using fun h => hemp (he.1 h))]
      by_cases h0 : value.val < self.default.val.length
      · rw [ite_eq_left (hgt.2 h0)]
        exact (WP.spec_ok _).2 ⟨⟨hemp, h0⟩, rfl⟩
      · rw [ite_eq_right (fun h => h0 (hgt.1 h))]
        exact (WP.spec_ok _).2 ⟨fun h => h0 h.2, rfl⟩
  cases hmin : self.min_items with
  | none =>
    dsimp only
    apply WP.spec_mono (hrest _)
    intro r hr
    cases r with
    | Ok b => exact ⟨by simp [maxItemsError?, hmin, hr.1], hr.2⟩
    | Err e => simp [maxItemsError?, hmin, hr.1, hr.2]
  | some lo =>
    dsimp only
    by_cases h1 : value.val < lo.val
    · rw [ite_eq_left (by rw [UScalar.lt_equiv]; exact h1)]
      exact (WP.spec_ok _).2 (by simp [maxItemsError?, hmin, h1, maxItemsLtMinItemsMsg])
    · rw [ite_eq_right (by rw [UScalar.lt_equiv]; exact h1)]
      apply WP.spec_mono (hrest _)
      intro r hr
      cases r with
      | Ok b => exact ⟨by simp [maxItemsError?, hmin, h1, hr.1], hr.2⟩
      | Err e => simp [maxItemsError?, hmin, h1, hr.1, hr.2]

/-- **Spec theorem for
`rmcp::model::elicitation_schema::EnumSchemaBuilder::<MultiSelect>::build`** (X38)

X38 `EnumSchemaBuilder::<MultiSelect>::build` (top-level → Specs; linkage patch-08, hunk
E8): a multi-select enum schema with the builder's title, description and item bounds, and the
default if it is non-empty (`None` for an empty one). Titled: the options `constTitles titles
values`; untitled: the values (upstream lines 1071–1112; patched lines 1066–1102 and
`const_titles`, patched lines 1795–1805). No premise. Not covered: (A), (C). -/
@[step]
theorem EnumSchemaBuilderMultiSelect.build_spec
    (self : EnumSchemaBuilder MultiSelect) :
    rmcp.model.elicitation_schema.EnumSchemaBuilderMultiSelect.build self ⦃
      (result : EnumSchema) =>
      if self.titled then
        ∃ t, result = .Multi (.Titled t) ∧ t.title = self.title ∧
          t.description = self.description ∧ t.min_items = self.min_items ∧
          t.max_items = self.max_items ∧
          t.items.any_of.val = constTitles self.enum_titles.val self.enum_values.val ∧
          t.default = (if self.default.val = [] then none else some self.default)
      else
        ∃ u, result = .Multi (.Untitled u) ∧ u.title = self.title ∧
          u.description = self.description ∧ u.min_items = self.min_items ∧
          u.max_items = self.max_items ∧ u.items.enum_ = self.enum_values ∧
          u.default = (if self.default.val = [] then none else some self.default) ⦄ := by
  obtain ⟨v, hv, hvv⟩ := const_titles_eq self.enum_titles self.enum_values
  unfold EnumSchemaBuilderMultiSelect.build
  have he : (self.default.length = 0) ↔ self.default.val = [] := by simp
  by_cases hd : self.default.val = []
  · have hl : self.default.length = 0 := he.2 hd
    cases ht : self.titled
    · simp only [Bool.false_eq_true, ↓reduceIte, alloc.vec.Vec.is_empty, hl, decide_true,
        bind_ok]
      exact (WP.spec_ok _).2 ⟨_, rfl, rfl, rfl, rfl, rfl, rfl, by rw [ite_eq_left hd]⟩
    · simp only [↓reduceIte, hv, alloc.vec.Vec.is_empty, hl, decide_true, bind_ok]
      exact (WP.spec_ok _).2 ⟨_, rfl, rfl, rfl, rfl, rfl, hvv, by rw [ite_eq_left hd]⟩
  · have hl : ¬ self.default.length = 0 := fun h => hd (he.1 h)
    cases ht : self.titled
    · simp only [Bool.false_eq_true, ↓reduceIte, alloc.vec.Vec.is_empty, hl, decide_false,
        bind_ok]
      exact (WP.spec_ok _).2 ⟨_, rfl, rfl, rfl, rfl, rfl, rfl, by rw [ite_eq_right hd]⟩
    · simp only [↓reduceIte, hv, alloc.vec.Vec.is_empty, hl, decide_false, Bool.false_eq_true,
        bind_ok]
      exact (WP.spec_ok _).2 ⟨_, rfl, rfl, rfl, rfl, rfl, hvv, by rw [ite_eq_right hd]⟩

/-- **Spec theorem for `rmcp::model::elicitation_schema::EnumSchema::builder`** (X39)

X39 `EnumSchema::builder` (top-level → Specs): the single-select builder for `values` with
nothing else set (`EnumSchemaBuilder::new(values)`, upstream lines 1138–1140, patched
1128–1130). No premise. -/
@[step]
theorem EnumSchema.builder_spec (values : alloc.vec.Vec String) :
    rmcp.model.elicitation_schema.EnumSchema.builder values ⦃
      (result : EnumSchemaBuilder SingleSelect) =>
      result = newEnumSchemaBuilder values ⦄ := by
  simp [EnumSchema.builder, EnumSchemaBuilderSingleSelect.new,
    EnumSchemaBuilderSingleSelect.Insts.CoreDefaultDefault.default, newEnumSchemaBuilder]

/-- Composition X39: the builder of `EnumSchema::builder` meets the enum builder invariant (it is
untitled and has no default). No premise. -/
theorem EnumSchema.builder_valid (values : alloc.vec.Vec String) :
    rmcp.model.elicitation_schema.EnumSchema.builder values ⦃
      (result : EnumSchemaBuilder SingleSelect) =>
      ValidEnumSchemaBuilder result ⦄ := by
  simp only [EnumSchema.builder, EnumSchemaBuilderSingleSelect.new,
    EnumSchemaBuilderSingleSelect.Insts.CoreDefaultDefault.default, bind_ok]
  refine (WP.spec_ok _).2 ⟨(fun h => by cases h), fun d hd => ?_⟩
  simp [alloc.vec.Vec.new] at hd

/-- Composition X30 (intermediate → Internal): the builder of `EnumSchemaBuilder::new` meets the
enum builder invariant. No premise. -/
theorem EnumSchemaBuilderSingleSelect.new_valid
    (values : alloc.vec.Vec String) :
    rmcp.model.elicitation_schema.EnumSchemaBuilderSingleSelect.new values ⦃
      (result : EnumSchemaBuilder SingleSelect) =>
      ValidEnumSchemaBuilder result ⦄ := by
  simp only [EnumSchemaBuilderSingleSelect.new,
    EnumSchemaBuilderSingleSelect.Insts.CoreDefaultDefault.default, bind_ok]
  refine (WP.spec_ok _).2 ⟨(fun h => by cases h), fun d hd => ?_⟩
  simp [alloc.vec.Vec.new] at hd

/-- `impl Default for EnumSchemaBuilder<SingleSelect>` (intermediate → Internal; called by X30
`new`): the builder with no values and nothing else set, `newEnumSchemaBuilder` of the empty
vector (upstream and patched lines 844–858; translated as
`EnumSchemaBuilderSingleSelect.Insts.CoreDefaultDefault.default`, patched lines 845–857), which
meets the enum builder invariant (V): it is the third constructor of an enum builder. No premise.
-/
theorem EnumSchemaBuilderSingleSelect.default_valid :
    rmcp.model.elicitation_schema.EnumSchemaBuilderSingleSelect.Insts.CoreDefaultDefault.default ⦃
      (result : EnumSchemaBuilder SingleSelect) =>
      result = newEnumSchemaBuilder (alloc.vec.Vec.new String) ∧
        ValidEnumSchemaBuilder result ⦄ := by
  simp only [EnumSchemaBuilderSingleSelect.Insts.CoreDefaultDefault.default,
    WP.spec_ok]
  refine ⟨rfl, ?_, ?_⟩
  · intro h; cases h
  · intro d hd; simp at hd

/-- Composition X26: `title` keeps both enum builder invariants.

Premise: caller code. Not covered: (I). -/
theorem EnumSchemaBuilder.title_valid {T ValueLike : Type}
    (valueInto : core.convert.Into ValueLike (rmcp.alloc.borrow.Cow Str String))
    (self : EnumSchemaBuilder T) (value : ValueLike) (c : rmcp.alloc.borrow.Cow Str String)
    (h_value_into : valueInto.into value = ok c) :
    rmcp.model.elicitation_schema.EnumSchemaBuilder.impl.title valueInto self value ⦃
      (result : EnumSchemaBuilder T) =>
      (ValidEnumSchemaBuilder self → ValidEnumSchemaBuilder result) ∧
        (ValidMultiSelectBuilder self → ValidMultiSelectBuilder result) ⦄ := by
  simp only [EnumSchemaBuilder.impl.title, h_value_into, bind_ok]
  exact (WP.spec_ok _).2 ⟨fun h => h, fun h => h⟩

/-- Composition X27: `description` keeps both enum builder invariants.

Premise: caller code. Not covered: (I). -/
theorem EnumSchemaBuilder.description_valid {T ValueLike : Type}
    (valueInto : core.convert.Into ValueLike (rmcp.alloc.borrow.Cow Str String))
    (self : EnumSchemaBuilder T) (value : ValueLike) (c : rmcp.alloc.borrow.Cow Str String)
    (h_value_into : valueInto.into value = ok c) :
    rmcp.model.elicitation_schema.EnumSchemaBuilder.impl.description valueInto self value ⦃
      (result : EnumSchemaBuilder T) =>
      (ValidEnumSchemaBuilder self → ValidEnumSchemaBuilder result) ∧
        (ValidMultiSelectBuilder self → ValidMultiSelectBuilder result) ⦄ := by
  simp only [EnumSchemaBuilder.impl.description, h_value_into, bind_ok]
  exact (WP.spec_ok _).2 ⟨fun h => h, fun h => h⟩

/-- Composition X28: `untitled` keeps both enum builder invariants. No premise. -/
theorem EnumSchemaBuilder.untitled_valid {T : Type}
    (self : EnumSchemaBuilder T) :
    rmcp.model.elicitation_schema.EnumSchemaBuilder.untitled self ⦃
      (result : EnumSchemaBuilder T) =>
      (ValidEnumSchemaBuilder self → ValidEnumSchemaBuilder result) ∧
        (ValidMultiSelectBuilder self → ValidMultiSelectBuilder result) ⦄ := by
  unfold EnumSchemaBuilder.untitled
  refine (WP.spec_ok _).2 ⟨fun h => ⟨(fun h' => by cases h'), h.2⟩,
    fun h => ⟨⟨(fun h' => by cases h'), h.1.2⟩, h.2⟩⟩

/-- Composition X29: an accepted `enum_titles` keeps both enum builder invariants (its check makes
the titled builder have as many titles as values). No premise. -/
theorem EnumSchemaBuilder.enum_titles_valid {T : Type}
    (self : EnumSchemaBuilder T) (titles : alloc.vec.Vec String) :
    rmcp.model.elicitation_schema.EnumSchemaBuilder.impl.enum_titles self titles ⦃
      (result : core.result.Result (EnumSchemaBuilder T) String) =>
      ∀ b, result = .Ok b →
        (ValidEnumSchemaBuilder self → ValidEnumSchemaBuilder b) ∧
          (ValidMultiSelectBuilder self → ValidMultiSelectBuilder b) ⦄ := by
  unfold EnumSchemaBuilder.impl.enum_titles
  dsimp only
  split
  · simp only [model.elicitation_schema.prim.titles_mismatch_message, bind_ok]
    exact (WP.spec_ok _).2 (fun b h => by cases h)
  · rename_i h
    simp only [bne_iff_ne, ne_eq, Decidable.not_not] at h
    have hl : titles.length = self.enum_values.length := by
      have := congrArg UScalar.val h; simpa [alloc.vec.Vec.len] using this
    refine (WP.spec_ok _).2 (fun b hb => ?_)
    cases hb
    exact ⟨fun hv => ⟨fun _ => hl, hv.2⟩, fun hv => ⟨⟨fun _ => hl, hv.1.2⟩, hv.2⟩⟩

/-- Composition X31: `multiselect` turns a valid builder into a valid multi-select builder (no
item bounds, no default).

Premise: (V). -/
theorem EnumSchemaBuilderSingleSelect.multiselect_valid
    (self : EnumSchemaBuilder SingleSelect) (h_valid : ValidEnumSchemaBuilder self) :
    rmcp.model.elicitation_schema.EnumSchemaBuilderSingleSelect.multiselect self ⦃
      (result : EnumSchemaBuilder MultiSelect) =>
      ValidMultiSelectBuilder result ⦄ := by
  unfold EnumSchemaBuilderSingleSelect.multiselect
  refine (WP.spec_ok _).2 ⟨⟨h_valid.1, ?_⟩, ?_, ?_⟩
  · intro d hd; simp [alloc.vec.Vec.new] at hd
  · intro lo hi h; cases h
  · intro h; simp [alloc.vec.Vec.new] at h

/-- Composition X32: an accepted single-select default keeps the enum builder invariant.

Premises: caller code, (V). Not covered: (I). -/
theorem EnumSchemaBuilderSingleSelect.with_default_valid
    {DefaultLike : Type} (defaultInto : core.convert.Into DefaultLike String)
    (self : EnumSchemaBuilder SingleSelect) (default_value : DefaultLike) (v : String)
    (h_default_into : defaultInto.into default_value = ok v)
    (h_valid : ValidEnumSchemaBuilder self) :
    rmcp.model.elicitation_schema.EnumSchemaBuilderSingleSelect.with_default defaultInto self
      default_value ⦃ (result : core.result.Result (EnumSchemaBuilder SingleSelect) String) =>
      ∀ b, result = .Ok b → ValidEnumSchemaBuilder b ⦄ := by
  apply WP.spec_mono (EnumSchemaBuilderSingleSelect.with_default_spec
    defaultInto self default_value v h_default_into)
  rintro r hr b rfl
  obtain ⟨hv, hd, hb⟩ := hr
  rw [hb]
  refine ⟨h_valid.1, fun d h => ?_⟩
  simp only at h
  rw [hd, List.mem_singleton] at h
  rw [h]; exact hv

/-- Composition X33: a valid single-select builder builds a consistent enum schema (its default,
if any, is an enum value) and, if titled, the options carry exactly the values and the titles,
in order (titles match values).

Premise: (V). Not covered: (A), (C). -/
theorem EnumSchemaBuilderSingleSelect.build_consistent
    (self : EnumSchemaBuilder SingleSelect) (h_valid : ValidEnumSchemaBuilder self) :
    rmcp.model.elicitation_schema.EnumSchemaBuilderSingleSelect.build self ⦃
      (result : EnumSchema) =>
      ConsistentEnumSchema result ∧
        ∀ t, result = .Single (.Titled t) →
          t.one_of.val.map (·.const_) = self.enum_values.val ∧
            t.one_of.val.map (·.title) = self.enum_titles.val ⦄ := by
  apply WP.spec_mono (EnumSchemaBuilderSingleSelect.build_spec self)
  intro r hr
  have hlast : ∀ d, self.default.val.getLast? = some d → d ∈ self.enum_values.val :=
    fun d hd => h_valid.2 d (List.mem_of_getLast? hd)
  cases ht : self.titled
  · rw [ht] at hr
    obtain ⟨u, rfl, -, -, hu, hd⟩ := hr
    refine ⟨fun d h => ?_, fun t h => by cases h⟩
    rw [hd] at h; rw [hu]; exact hlast d h
  · rw [ht, ite_eq_left rfl] at hr
    obtain ⟨t, rfl, -, -, ho, hd⟩ := hr
    have hlen := h_valid.1 ht
    obtain ⟨h1, h2⟩ := map_const_constTitles _ _ hlen
    refine ⟨fun d h => ?_, fun t' h => ?_⟩
    · rw [hd] at h; rw [ho, h1]; exact hlast d h
    · cases h; rw [ho]; exact ⟨h1, h2⟩

/-- Composition X34: `single_select` turns a builder meeting the enum builder invariant into one
meeting it again (the default is cleared).

Premise: (V). -/
theorem EnumSchemaBuilderMultiSelect.single_select_valid
    (self : EnumSchemaBuilder MultiSelect) (h_valid : ValidEnumSchemaBuilder self) :
    rmcp.model.elicitation_schema.EnumSchemaBuilderMultiSelect.single_select self ⦃
      (result : EnumSchemaBuilder SingleSelect) =>
      ValidEnumSchemaBuilder result ⦄ := by
  unfold EnumSchemaBuilderMultiSelect.single_select
  refine (WP.spec_ok _).2 ⟨h_valid.1, fun d hd => ?_⟩
  simp [alloc.vec.Vec.new] at hd

/-- Composition X35: an accepted multi-select default keeps the multi-select invariant.

Premise: (V). -/
theorem EnumSchemaBuilderMultiSelect.with_default_valid
    (self : EnumSchemaBuilder MultiSelect) (default_values : alloc.vec.Vec String)
    (h_valid : ValidMultiSelectBuilder self) :
    rmcp.model.elicitation_schema.EnumSchemaBuilderMultiSelect.with_default self default_values ⦃
      (result : core.result.Result (EnumSchemaBuilder MultiSelect) String) =>
      ∀ b, result = .Ok b → ValidMultiSelectBuilder b ⦄ := by
  apply WP.spec_mono
    (EnumSchemaBuilderMultiSelect.with_default_spec self default_values)
  rintro r hr b rfl
  obtain ⟨he, rfl⟩ := hr
  obtain ⟨⟨htl, -⟩, hb, -⟩ := h_valid
  obtain ⟨hin, hbd⟩ := (multiSelectDefaultError?_eq_none_iff _ _).1 he
  exact ⟨⟨htl, hin⟩, hb, hbd⟩

/-- Composition X36: an accepted `min_items` keeps the multi-select invariant (minimum at most
the maximum; a non-empty default has at least the minimum).

Premise: (V). -/
theorem EnumSchemaBuilderMultiSelect.min_items_valid
    (self : EnumSchemaBuilder MultiSelect) (value : U64) (h_valid : ValidMultiSelectBuilder self) :
    rmcp.model.elicitation_schema.EnumSchemaBuilderMultiSelect.min_items self value ⦃
      (result : core.result.Result (EnumSchemaBuilder MultiSelect) String) =>
      ∀ b, result = .Ok b → ValidMultiSelectBuilder b ⦄ := by
  apply WP.spec_mono
    (EnumSchemaBuilderMultiSelect.min_items_spec self value)
  rintro r hr b rfl
  obtain ⟨he, rfl⟩ := hr
  obtain ⟨hv, -, hdb⟩ := h_valid
  obtain ⟨h1, h2⟩ := (minItemsError?_eq_none_iff _ _).1 he
  refine ⟨hv, fun lo hi hlo hhi => ?_, fun hne => ⟨fun lo hlo => ?_, (hdb hne).2⟩⟩
  · cases hlo; exact h1 hi hhi
  · cases hlo; exact h2 hne

/-- Composition X37: an accepted `max_items` keeps the multi-select invariant.

Premise: (V). -/
theorem EnumSchemaBuilderMultiSelect.max_items_valid
    (self : EnumSchemaBuilder MultiSelect) (value : U64) (h_valid : ValidMultiSelectBuilder self) :
    rmcp.model.elicitation_schema.EnumSchemaBuilderMultiSelect.max_items self value ⦃
      (result : core.result.Result (EnumSchemaBuilder MultiSelect) String) =>
      ∀ b, result = .Ok b → ValidMultiSelectBuilder b ⦄ := by
  apply WP.spec_mono
    (EnumSchemaBuilderMultiSelect.max_items_spec self value)
  rintro r hr b rfl
  obtain ⟨he, rfl⟩ := hr
  obtain ⟨hv, -, hdb⟩ := h_valid
  obtain ⟨h1, h2⟩ := (maxItemsError?_eq_none_iff _ _).1 he
  refine ⟨hv, fun lo hi hlo hhi => ?_, fun hne => ⟨(hdb hne).1, fun hi hhi => ?_⟩⟩
  · cases hhi; exact h1 lo hlo
  · cases hhi; exact h2 hne

/-- Composition X38: a valid multi-select builder builds a consistent enum schema (minimum at
most maximum, a default that is non-empty, made of enum values and within the bounds) and, if
titled, the options carry exactly the values and the titles, in order. **H22**: neither a minimum
above the number of values nor duplicate defaults are excluded.

Premise: (V). Not covered: (A), (C). -/
theorem EnumSchemaBuilderMultiSelect.build_consistent
    (self : EnumSchemaBuilder MultiSelect) (h_valid : ValidMultiSelectBuilder self) :
    rmcp.model.elicitation_schema.EnumSchemaBuilderMultiSelect.build self ⦃
      (result : EnumSchema) =>
      ConsistentEnumSchema result ∧
        ∀ t, result = .Multi (.Titled t) →
          t.items.any_of.val.map (·.const_) = self.enum_values.val ∧
            t.items.any_of.val.map (·.title) = self.enum_titles.val ⦄ := by
  apply WP.spec_mono (EnumSchemaBuilderMultiSelect.build_spec self)
  intro r hr
  obtain ⟨⟨htl, hdef⟩, hbounds, hdb⟩ := h_valid
  have hitems : ∀ (default : Option (alloc.vec.Vec String)),
      default = (if self.default.val = [] then none else some self.default) →
      ConsistentItems self.min_items self.max_items default self.enum_values.val := by
    intro default hd
    refine ⟨hbounds, fun ds hds => ?_⟩
    rw [hd] at hds
    split at hds
    · cases hds
    · rename_i hne
      cases hds
      exact ⟨hne, hdef, (hdb hne).1, (hdb hne).2⟩
  cases ht : self.titled
  · rw [ht] at hr
    obtain ⟨u, rfl, -, -, hmin, hmax, hu, hd⟩ := hr
    refine ⟨?_, fun t h => by cases h⟩
    show ConsistentItems u.min_items u.max_items u.default u.items.enum_.val
    rw [hmin, hmax, hu]
    exact hitems _ hd
  · rw [ht, ite_eq_left rfl] at hr
    obtain ⟨t, rfl, -, -, hmin, hmax, ho, hd⟩ := hr
    obtain ⟨h1, h2⟩ := map_const_constTitles _ _ (htl ht)
    refine ⟨?_, fun t' h => ?_⟩
    · show ConsistentItems t.min_items t.max_items t.default (t.items.any_of.val.map (·.const_))
      rw [hmin, hmax, ho, h1]
      exact hitems _ hd
    · cases h; rw [ho]; exact ⟨h1, h2⟩

end rmcp.model.elicitation_schema
