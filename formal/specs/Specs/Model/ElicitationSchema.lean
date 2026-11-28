/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
module
public import Defs
public import Rmcp.Funs
import Proofs.Model.ElicitationSchema.Primitive
import Proofs.Model.ElicitationSchema.Enum
import Proofs.Model.ElicitationSchema.Schema

@[expose] public section

/-!
# Public API of `crates/rmcp/src/model/elicitation_schema.rs`: top-level functions

This file states only the **top-level** public functions of `elicitation_schema.rs`: those that no
other verified function calls (human decision 2026-11-28). Of the 75 targets X01–X75, all `pub` in
upstream rmcp, 64 are top-level. The eleven public functions that a top-level one calls are
verified too: X01 `StringSchema::new`, X02 `StringSchema::email`, X14 `IntegerSchema::new`, X16
`IntegerSchema::range`, X22 `BooleanSchema::new`, X25 `BooleanSchema::with_default`, X30
`EnumSchemaBuilder::<SingleSelect>::new`, X46 `ElicitationSchemaBuilder::new`, X47 `property`, X48
`required_property` and X74 `build` (callers in "Scope and placement"). Their statements, the
compositions that involve them, the statement of `impl Default for EnumSchemaBuilder<SingleSelect>`
and the model laws of `Defs.ElicitationSchema` are in
`formal/proofs/Proofs/Internal/Model/ElicitationSchema.lean`. The theorem docstrings below are
unchanged signed-off text; their parentheticals "(top-level → Specs)" record the placement. Where
one names an intermediate function, `build_fail`, `build_consistent`, `build_new`, the corollaries
`property_entries_eq_mapInsert` and `required_property_entries_eq_mapInsert`,
`EnumSchemaBuilderSingleSelect.default_valid` or a model law, that statement is in the internal
file.

One row per theorem below; the theorem is `Theorems.elicitation_schema.<Theorem>`. In the ID
column, `Xnn fail` is the failing-case companion of `Xnn` (the inputs its premises exclude),
`Xnn comp.` a composition about one call of `Xnn` (an invariant it establishes or keeps, or the
consistency of its result), and `Xmm+Xnn` a composition of two calls. The keys of the last two
columns are explained in "Premises" and "Not covered" below; they are local to this file and its
internal companion (other spec files use some of the same letters with other meanings).

| ID | Function | Theorem | Guarantee | Premises (caller must ensure) | Not covered (Rust may panic or behave otherwise; the model does not) |
|---|---|---|---|---|---|
| X03 | `StringSchema::uri` | `StringSchema.uri` | the default string schema with format `Uri` | none | none |
| X04 | `StringSchema::date` | `StringSchema.date` | the default string schema with format `Date` | none | none |
| X05 | `StringSchema::date_time` | `StringSchema.date_time` | the default string schema with format `DateTime` | none | none |
| X06 | `StringSchema::title` | `StringSchema.title` | title set to `title.into()`, other fields unchanged | caller code | (I) |
| X07 | `StringSchema::description` | `StringSchema.description` | description set to `description.into()`, other fields unchanged | caller code | (I) |
| X08 | `StringSchema::with_length` | `StringSchema.with_length` | `Ok` with both length bounds iff `min ≤ max`; else `Err("min_length must be <= max_length")` | none | none |
| X09 | `StringSchema::length` | `StringSchema.length` | both length bounds set | (B) | none |
| X09 fail | `StringSchema::length` | `StringSchema.length_fail` | panics (`assert!`) | `min > max` | none |
| X10 | `StringSchema::min_length` | `StringSchema.min_length` | minimum length set, other fields unchanged (unchecked, H21) | none | none |
| X11 | `StringSchema::max_length` | `StringSchema.max_length` | maximum length set, other fields unchanged (unchecked, H21) | none | none |
| X12 | `StringSchema::format` | `StringSchema.format` | format set, other fields unchanged | none | none |
| X13 | `StringSchema::with_default` | `StringSchema.with_default` | default set to `default.into()`, other fields unchanged (unchecked, H21) | caller code | (I) |
| X15 | `IntegerSchema::with_range` | `IntegerSchema.with_range` | `Ok` with both bounds iff `min ≤ max`; else `Err("minimum must be <= maximum")` | none | none |
| X17 | `IntegerSchema::minimum` | `IntegerSchema.minimum` | minimum set, other fields unchanged (unchecked, H21) | none | none |
| X18 | `IntegerSchema::maximum` | `IntegerSchema.maximum` | maximum set, other fields unchanged (unchecked, H21) | none | none |
| X19 | `IntegerSchema::title` | `IntegerSchema.title` | title set to `title.into()`, other fields unchanged | caller code | (I) |
| X20 | `IntegerSchema::description` | `IntegerSchema.description` | description set to `description.into()`, other fields unchanged | caller code | (I) |
| X21 | `IntegerSchema::with_default` | `IntegerSchema.with_default` | default set, other fields unchanged (unchecked, H21) | none | none |
| X23 | `BooleanSchema::title` | `BooleanSchema.title` | title set to `title.into()`, other fields unchanged | caller code | (I) |
| X24 | `BooleanSchema::description` | `BooleanSchema.description` | description set to `description.into()`, other fields unchanged | caller code | (I) |
| X26 | `EnumSchemaBuilder<T>::title` | `EnumSchemaBuilder.title` | title set to `value.into()`, other fields unchanged | caller code | (I) |
| X27 | `EnumSchemaBuilder<T>::description` | `EnumSchemaBuilder.description` | description set to `value.into()`, other fields unchanged | caller code | (I) |
| X28 | `EnumSchemaBuilder<T>::untitled` | `EnumSchemaBuilder.untitled` | untitled with no titles, other fields unchanged | none | none |
| X29 | `EnumSchemaBuilder<T>::enum_titles` | `EnumSchemaBuilder.enum_titles` | `Ok`, titled with `titles`, iff as many titles as values; else `Err(titlesMismatchMsg …)` | none | (A) |
| X31 | `EnumSchemaBuilder<SingleSelect>::multiselect` | `EnumSchemaBuilderSingleSelect.multiselect` | the multi-select builder with the same values, titles, title, description; no bounds or default | none | none |
| X32 | `EnumSchemaBuilder<SingleSelect>::with_default` | `EnumSchemaBuilderSingleSelect.with_default` | `Ok` with default `[v]` iff `v = default_value.into()` is an enum value; else `Err` with its message | caller code | (I), (A) |
| X33 | `EnumSchemaBuilder<SingleSelect>::build` | `EnumSchemaBuilderSingleSelect.build` | the single-select schema: title, description, last default; titled options `constTitles` or the values | none | (A), (C) |
| X34 | `EnumSchemaBuilder<MultiSelect>::single_select` | `EnumSchemaBuilderMultiSelect.single_select` | the single-select builder with the same values, titles, title, description; no bounds or default | none | none |
| X35 | `EnumSchemaBuilder<MultiSelect>::with_default` | `EnumSchemaBuilderMultiSelect.with_default` | `Ok` with the defaults iff `multiSelectDefaultError?` is `none`; else `Err` with the first failing check (duplicates accepted, H22) | none | (A) |
| X36 | `EnumSchemaBuilder<MultiSelect>::min_items` | `EnumSchemaBuilderMultiSelect.min_items` | `Ok` with the minimum iff `minItemsError?` is `none`; else `Err` with the first failing check (H22) | none | (A) |
| X37 | `EnumSchemaBuilder<MultiSelect>::max_items` | `EnumSchemaBuilderMultiSelect.max_items` | `Ok` with the maximum iff `maxItemsError?` is `none`; else `Err` with the first failing check | none | (A) |
| X38 | `EnumSchemaBuilder<MultiSelect>::build` | `EnumSchemaBuilderMultiSelect.build` | the multi-select schema: title, description, item bounds, non-empty default; titled options `constTitles` or the values | none | (A), (C) |
| X39 | `EnumSchema::builder` | `EnumSchema.builder` | `newEnumSchemaBuilder values` | none | none |
| X40 | `ElicitationSchema::new` | `ElicitationSchema.new` | the schema with these properties, property order their names, nothing else set | (L) | (A) |
| X40 fail | `ElicitationSchema::new` | `ElicitationSchema.new_fail` | panics in the model (`prim::sorted_keys`; no Rust map is that large) | `¬ PropertiesFit properties` | none |
| X41 | `ElicitationSchema::with_required` | `ElicitationSchema.with_required` | required list set (`Some`, even if empty; names unchecked), other fields unchanged | none | none |
| X42 | `ElicitationSchema::with_title` | `ElicitationSchema.with_title` | title set to `title.into()`, other fields unchanged | caller code | (I) |
| X43 | `ElicitationSchema::with_description` | `ElicitationSchema.with_description` | description set to `description.into()`, other fields unchanged | caller code | (I) |
| X44 | `ElicitationSchema::with_schema` | `ElicitationSchema.with_schema` | dialect (`$schema`) set to `schema.into()`, other fields unchanged | caller code | (I) |
| X45 | `ElicitationSchema::builder` | `ElicitationSchema.builder` | `emptyElicitationSchemaBuilder` | none | none |
| X49 | `ElicitationSchemaBuilder::string_property` | `ElicitationSchemaBuilder.string_property` | property `n` set to `String(s)`, `s` the closure on the default; not required (H23) | caller code | (I), (M), (A) |
| X50 | `ElicitationSchemaBuilder::required_string_property` | `ElicitationSchemaBuilder.required_string_property` | `n` appended to the required list (H20), property `n` set to `String(s)` | caller code, (R) | (I), (M), (A) |
| X51 | `ElicitationSchemaBuilder::integer_property` | `ElicitationSchemaBuilder.integer_property` | property `n` set to `Integer(i)`, `i` the closure on the default; not required | caller code | (I), (M), (A) |
| X52 | `ElicitationSchemaBuilder::required_integer_property` | `ElicitationSchemaBuilder.required_integer_property` | `n` appended to the required list (H20), property `n` set to `Integer(i)` | caller code, (R) | (I), (M), (A) |
| X53 | `ElicitationSchemaBuilder::bool_property` | `ElicitationSchemaBuilder.bool_property` | property `n` set to `Boolean(b)`, `b` the closure on the default; not required | caller code | (I), (M), (A) |
| X54 | `ElicitationSchemaBuilder::required_bool_property` | `ElicitationSchemaBuilder.required_bool_property` | `n` appended to the required list (H20), property `n` set to `Boolean(b)` | caller code, (R) | (I), (M), (A) |
| X55 | `ElicitationSchemaBuilder::required_string` | `ElicitationSchemaBuilder.required_string` | `n` required (H20), the default string schema | caller code, (R) | (I), (M), (A) |
| X56 | `ElicitationSchemaBuilder::optional_string` | `ElicitationSchemaBuilder.optional_string` | property `n`, the default string schema, not required | caller code | (I), (M), (A) |
| X57 | `ElicitationSchemaBuilder::required_email` | `ElicitationSchemaBuilder.required_email` | `n` required (H20), a string with format `Email` | caller code, (R) | (I), (M), (A) |
| X58 | `ElicitationSchemaBuilder::optional_email` | `ElicitationSchemaBuilder.optional_email` | property `n`, a string with format `Email`, not required | caller code | (I), (M), (A) |
| X59 | `ElicitationSchemaBuilder::required_string_with` | `ElicitationSchemaBuilder.required_string_with` | `n` required (H20), `String(s)` with `s` the closure on the default | caller code, (R) | (I), (M), (A) |
| X60 | `ElicitationSchemaBuilder::optional_string_with` | `ElicitationSchemaBuilder.optional_string_with` | property `n` set to `String(s)`, not required | caller code | (I), (M), (A) |
| X61 | `ElicitationSchemaBuilder::required_integer` | `ElicitationSchemaBuilder.required_integer` | `n` required (H20), an integer with both bounds | caller code, (R), (B) | (I), (M), (A) |
| X61 fail | same | `ElicitationSchemaBuilder.required_integer_fail` | panics (`assert!` of `range`) | `min > max` | none |
| X62 | `ElicitationSchemaBuilder::optional_integer` | `ElicitationSchemaBuilder.optional_integer` | property `n`, an integer with both bounds, not required | caller code, (B) | (I), (M), (A) |
| X62 fail | same | `ElicitationSchemaBuilder.optional_integer_fail` | panics (`assert!` of `range`) | `min > max` | none |
| X63 | `ElicitationSchemaBuilder::required_integer_with` | `ElicitationSchemaBuilder.required_integer_with` | `n` required (H20), `Integer(i)` with `i` the closure on the default (H21) | caller code, (R) | (I), (M), (A) |
| X64 | `ElicitationSchemaBuilder::optional_integer_with` | `ElicitationSchemaBuilder.optional_integer_with` | property `n` set to `Integer(i)`, not required | caller code | (I), (M), (A) |
| X65 | `ElicitationSchemaBuilder::required_bool` | `ElicitationSchemaBuilder.required_bool` | `n` required (H20), the default boolean schema | caller code, (R) | (I), (M), (A) |
| X66 | `ElicitationSchemaBuilder::optional_bool` | `ElicitationSchemaBuilder.optional_bool` | property `n`, a boolean with default `default`, not required | caller code | (I), (M), (A) |
| X67 | `ElicitationSchemaBuilder::required_bool_with` | `ElicitationSchemaBuilder.required_bool_with` | `n` required (H20), `Boolean(b)` with `b` the closure on the default | caller code, (R) | (I), (M), (A) |
| X68 | `ElicitationSchemaBuilder::optional_bool_with` | `ElicitationSchemaBuilder.optional_bool_with` | property `n` set to `Boolean(b)`, not required | caller code | (I), (M), (A) |
| X69 | `ElicitationSchemaBuilder::required_enum_schema` | `ElicitationSchemaBuilder.required_enum_schema` | `n` required (H20), `Enum(enum_schema)` stored unchecked | caller code, (R) | (I), (M), (A) |
| X70 | `ElicitationSchemaBuilder::optional_enum_schema` | `ElicitationSchemaBuilder.optional_enum_schema` | property `n` set to `Enum(enum_schema)` (unchecked), not required | caller code | (I), (M), (A) |
| X71 | `ElicitationSchemaBuilder::mark_required` | `ElicitationSchemaBuilder.mark_required` | `name.into()` appended to the required list, unchecked (H20), other fields unchanged | caller code, (R) | (I), (A) |
| X71 fail | same | `ElicitationSchemaBuilder.mark_required_fail` | fails in the model (`Vec::push`; no Rust `Vec` is that long) | caller code; required list of `Usize.max` names | none |
| X72 | `ElicitationSchemaBuilder::title` | `ElicitationSchemaBuilder.title` | title set to `title.into()`, other fields unchanged | caller code | (I) |
| X73 | `ElicitationSchemaBuilder::description` | `ElicitationSchemaBuilder.description` | description set to `description.into()`, other fields unchanged | caller code | (I) |
| X75 | `ElicitationSchemaBuilder::build_unchecked` | `ElicitationSchemaBuilder.build_unchecked` | the schema of X74 `build` (H19, H20) | (L), (Q) | (A) |
| X75 fail | same | `ElicitationSchemaBuilder.build_unchecked_fail` | panics exactly when (L) or (Q) fails (message not modelled) | `¬ ((L) ∧ (Q))` | (D) |
| X39 comp. | `EnumSchema::builder` | `EnumSchema.builder_valid` | the builder meets `ValidEnumSchemaBuilder` | none | none |
| X26 comp. | `EnumSchemaBuilder<T>::title` | `EnumSchemaBuilder.title_valid` | keeps both enum builder invariants | caller code | (I) |
| X27 comp. | `EnumSchemaBuilder<T>::description` | `EnumSchemaBuilder.description_valid` | keeps both enum builder invariants | caller code | (I) |
| X28 comp. | `EnumSchemaBuilder<T>::untitled` | `EnumSchemaBuilder.untitled_valid` | keeps both enum builder invariants | none | none |
| X29 comp. | `EnumSchemaBuilder<T>::enum_titles` | `EnumSchemaBuilder.enum_titles_valid` | an `Ok` result keeps both enum builder invariants | none | none |
| X31 comp. | `EnumSchemaBuilder<SingleSelect>::multiselect` | `EnumSchemaBuilderSingleSelect.multiselect_valid` | a valid builder gives a valid multi-select builder | (V) | none |
| X32 comp. | `EnumSchemaBuilder<SingleSelect>::with_default` | `EnumSchemaBuilderSingleSelect.with_default_valid` | an `Ok` result meets `ValidEnumSchemaBuilder` | caller code, (V) | (I) |
| X33 comp. | `EnumSchemaBuilder<SingleSelect>::build` | `EnumSchemaBuilderSingleSelect.build_consistent` | `ConsistentEnumSchema`; titled options carry the values and titles in order | (V) | (A), (C) |
| X34 comp. | `EnumSchemaBuilder<MultiSelect>::single_select` | `EnumSchemaBuilderMultiSelect.single_select_valid` | the result meets `ValidEnumSchemaBuilder` | (V) | none |
| X35 comp. | `EnumSchemaBuilder<MultiSelect>::with_default` | `EnumSchemaBuilderMultiSelect.with_default_valid` | an `Ok` result meets `ValidMultiSelectBuilder` | (V) | none |
| X36 comp. | `EnumSchemaBuilder<MultiSelect>::min_items` | `EnumSchemaBuilderMultiSelect.min_items_valid` | an `Ok` result meets `ValidMultiSelectBuilder` | (V) | none |
| X37 comp. | `EnumSchemaBuilder<MultiSelect>::max_items` | `EnumSchemaBuilderMultiSelect.max_items_valid` | an `Ok` result meets `ValidMultiSelectBuilder` | (V) | none |
| X38 comp. | `EnumSchemaBuilder<MultiSelect>::build` | `EnumSchemaBuilderMultiSelect.build_consistent` | `ConsistentEnumSchema` (H22); titled options carry the values and titles in order | (V) | (A), (C) |
| X40 comp. | `ElicitationSchema::new` | `ElicitationSchema.new_consistent` | `ConsistentElicitationSchema` | (L) | (A) |
| X75 comp. | `ElicitationSchemaBuilder::build_unchecked` | `ElicitationSchemaBuilder.build_unchecked_consistent` | `ConsistentElicitationSchema` (H19, H20) | (L), (Q) | (A) |
| X45+X75 | `ElicitationSchema::builder`, then `build_unchecked` | `ElicitationSchema.builder_build_unchecked_empty` | no panic; no property and no required list (H19) | none | none |

## Scope and placement

A target is **top-level** if no other target calls it, directly or through translated helpers
(computed from the bodies in `Rmcp/Funs.lean`); otherwise **intermediate**. The top-level targets
(the intermediate ones are listed with their callers in the internal file):

| ID | Function | Class | Called by | File |
|---|---|---|---|---|
| X03–X13 | `StringSchema::{uri, date, date_time, title, description, with_length, length, min_length, max_length, format, with_default}` | top-level | — | Specs |
| X15 | `IntegerSchema::with_range` | top-level | — | Specs |
| X17–X21 | `IntegerSchema::{minimum, maximum, title, description, with_default}` | top-level | — | Specs |
| X23, X24 | `BooleanSchema::{title, description}` | top-level | — | Specs |
| X26–X29 | `EnumSchemaBuilder<T>::{title, description, untitled, enum_titles}` | top-level | — | Specs |
| X31–X33 | `EnumSchemaBuilder<SingleSelect>::{multiselect, with_default, build}` | top-level | — | Specs |
| X34–X38 | `EnumSchemaBuilder<MultiSelect>::{single_select, with_default, min_items, max_items, build}` | top-level | — | Specs |
| X39 | `EnumSchema::builder` | top-level | — | Specs |
| X40–X45 | `ElicitationSchema::{new, with_required, with_title, with_description, with_schema, builder}` | top-level | — | Specs |
| X49–X73 | `ElicitationSchemaBuilder::{string_property, …, description}` | top-level | — | Specs |
| X75 | `ElicitationSchemaBuilder::build_unchecked` | top-level | — | Specs |

So 64 top-level targets, stated here with their failing cases (X09, X40, X61, X62, X71, X75) and
the compositions of top-level functions: 86 statements. The other 23 (the 11 intermediate targets
with their failing cases and corollaries, the compositions that involve an intermediate function,
the `Default` impl of `EnumSchemaBuilder<SingleSelect>` and three model laws) are in the internal
file.

## What the statements promise

`f x ⦃ (result : T) => P result ⦄` says that `f x` terminates without panicking in the Lean model
and that `result` satisfies `P` (plan Section 3). For every target the postcondition determines
the result uniquely, except that for a property map that is not sorted (no Rust map) the lookups
of `PropertyInserted` do not fix the order of the entries; for X47 and X48 the corollaries
`property_entries_eq_mapInsert` and `required_property_entries_eq_mapInsert` (decision XS1; in the
internal file) give the exact entry list for any map, through the trusted model
`ExtModel.mapInsert`. `Result`-returning targets (X08, X15, X29, X32, X35–X37, and X74 in the
internal file) cover `Ok` and every `Err` in the Rust order of checks, with the error payload.
Targets that panic (`assert!` in X09, X16, X61, X62; `expect` in X75) and the patch- or
model-induced `collect` panic (X40, X74, X75) have `_fail` companions, so that with the premises
every input is covered. Hypotheses `(h_… : …)` are premises the caller must ensure; nothing is
promised when one fails.

The Rust bugs of decision XD4, confirmed by decision XS7, are stated as the code behaves (the
theorem docstrings, signed-off text, mark them only by number): **H19** `build` is `Ok`
for a schema with no property (X74, X75, `ElicitationSchemaBuilder.build_consistent`,
`ElicitationSchemaBuilder.build_unchecked_consistent`,
`ElicitationSchema.builder_build_unchecked_empty`, `ElicitationSchemaBuilder.build_new`); **H20**
(widened by decision XS5) the required list keeps duplicates, and `mark_required` accepts names
that are not properties, so that, if no property of that name is added before `build`, X74
returns `Err` and X75 panics (X48, X50, X52, X54, X55, X57, X59, X61, X63, X65, X67, X69, X71,
X74, X75, `ElicitationSchemaBuilder.required_property_entries_eq_mapInsert`,
`ElicitationSchemaBuilder.build_unchecked_fail`, `ElicitationSchemaBuilder.build_consistent`,
`ElicitationSchemaBuilder.build_unchecked_consistent`); **H22** a multi-select enum accepts
`min_items` above the number of values and duplicate defaults (X35, X36,
`EnumSchemaBuilderMultiSelect.build_consistent`); **H23** `string_property` does not make the
property required (X49).
Recorded behaviours, not bugs, also stated exactly: **H21** (decision XS7) the single setters
accept inconsistent bounds and defaults (X10, X11, X13, X17, X18, X21, X63); and (decision XS4)
X41 `with_required` does not check the names and keeps an empty list as `Some([])`; X69/X70
store the enum schema unchecked.

Translated functions are written in full (`rmcp.model.elicitation_schema.…`), as a bare name
would resolve to a restated theorem. Rust strings are read as their UTF-8 bytes
(`Defs.utf8Bytes`, the `val` of a `Str`).

## Premises (caller must ensure)

* **caller code** (`h_*_into`, `h_f`): a conversion of the caller (`Into<String>`,
  `Into<Cow<'static, str>>`) or the caller's closure (`FnOnce(XSchema) -> XSchema`, applied to
  the default schema) returns the value the hypothesis names.
* **(R)** `self.required.val.length < Usize.max`: the exact condition under which the Aeneas model
  of `Vec::push` does not fail on the required list. Every Rust `Vec<String>` meets it (at most
  `isize::MAX / 24` elements). Each statement has it only where the target pushes.
* **(L)** `PropertiesFit`: `24 * n ≤ isize::MAX` for `n` properties, the exact condition under
  which the model of `prim::sorted_keys` (`ExtModel.collectVec 24`) does not panic (X40, X74, X75;
  for the `Err` path of X74 it is patch-induced, patch 08 hunk E7 computes the key list first).
  Every Rust map meets it.
* **(B)** `min ≤ max` for the targets with `assert!(min <= max)` (X09, X16, X61, X62); the `_fail`
  companion covers `min > max`.
* **(V)** the enum builder invariants `ValidEnumSchemaBuilder` and `ValidMultiSelectBuilder`, only
  in the enum compositions. They are true invariants: the fields of `EnumSchemaBuilder` are
  private (upstream lines 823–841), so every enum builder a caller holds was made by its three
  constructors (`EnumSchemaBuilder::<SingleSelect>::new`, `EnumSchema::builder`, and the public
  `impl Default for EnumSchemaBuilder<SingleSelect>`, upstream lines 844–858, untitled with no
  values and no default: `EnumSchemaBuilderSingleSelect.default_valid`, in the internal file) and
  its setters, which establish and keep them (the `_valid` compositions).
* **(Q)** `RequiredPropertiesExist self`: every required name is a property. **Not an invariant**:
  an exact caller premise of X75 and its composition (like (B)), whose complement (with (L)) is
  `ElicitationSchemaBuilder.build_unchecked_fail`. The fields of `ElicitationSchemaBuilder` are
  `pub` (upstream lines 1400–1405), so a caller can write `required` directly, and X71
  `mark_required` (upstream lines 1740–1743) appends any name (H20). (Q) is checked only when
  `build` runs (upstream lines 1766–1772, 1796): a name marked required before its property is
  added breaks (Q) only until a property of that name is added, so
  `ElicitationSchema::builder().mark_required("a").optional_string("a").build()` returns `Ok`,
  while `ElicitationSchema::builder().mark_required("x").build_unchecked()` panics. The empty
  builder meets it (X45, X46; model law `requiredPropertiesExist_emptyElicitationSchemaBuilder`,
  in the internal file), and X47–X70 keep it (model law
  `PropertyInserted.forall_mem_propertyNames_append`, in the internal file: they add the property
  they require); X71 and direct writes to the fields can break it.
* **(S)** `KeysSorted` (decision XS1: no sortedness premise, only the weakest form) appears only
  in implication form, inside `PropertyInserted` (`KeysSorted old → KeysSorted new`): no
  statement needs it as a premise, because the lookups, the key list and the membership tests of
  X40, X47–X75 hold for any entry list.

## Not covered (Rust may panic or behave otherwise; the model does not)

* **(I)** caller code: the caller-code premises describe `Into` impls and closures as functions
  of their argument; side effects and global state are not described.
* **(A)** allocation: allocation failure is not modelled in any model (`formal/README.md`,
  "Stated exceptions": "Allocation failure is not modelled"; e.g. `Vec::push`, `vec![…]`,
  `BTreeMap::insert`, `collect`, `str::to_owned`, the `format!` of
  `prim::titles_mismatch_message`), nor the capacity-overflow panic of `Vec::push` above
  `isize::MAX` bytes, which no Rust `Vec<String>` reaches before (R) fails (size convention).
* **(M)** `BTreeMap` model: for an entry list that is not `KeysSorted` (no Rust map) the result is
  the model's linear insertion, not a Rust map (stated exception of `BTreeMap::insert`).
* **(C)** capacity: the `one_of`/`any_of` vectors of X33/X38 may have another capacity than
  upstream (patch 08 hunk E8); capacity is not modelled.
* **(D)** the panic message of X75 (`expect`, `<str as Debug>::fmt` total, not exact).
* **(F)** floats: applies to every statement that moves a property map or a
  `PrimitiveSchemaDefinition` (X40–X75 and their compositions; not repeated in the per-statement
  key lists): a `PrimitiveSchemaDefinition::Number` (fields `F64`) is stored, moved and looked up
  unchanged (equality of a moved value; decision XS2); no statement inspects an `F64` (float
  rule, decision XD3).

## Provenance

*Order.* The statements are in Rust source order (= ID order), each failing case and corollary
after its statement; then the compositions (enum builders, then elicitation schemas).

*Proofs.* Each statement is restated as a theorem `Theorems.elicitation_schema.<Type>.<function>`
(failing cases and compositions keep the descriptive name of their statement), proved by its spec
theorem in `Proofs/Model/ElicitationSchema/{Primitive,Enum,Schema}.lean` (function spec theorems
`rmcp.model.elicitation_schema.<generated name>_spec` and `…_fail`, compositions
`rmcp.model.elicitation_schema.<Theorem>`; with the helpers of `Common` and the external-model
laws of `Proofs.External.ElicitationSchema`), and followed by the assumptions its proof depends
on, checked by `#print axioms` under `#guard_msgs`. The restated text is that of the signed-off
statements.

*Sign-off.* The 109 statements (86 here, 23 in the internal file) and the definitions
`Defs.ElicitationSchema` (both files): signed off by the spec owner (Hoang Le Truong) on
2026-11-28 (decision XS6).

*Linkage.* X29, X32, X33, X35–X38, X40, X74, X75 are `patch-08` (hunks E1–E8 of
`formal/trusted/patches/08-elicitation-schema.patch`); the other 65 are `ORIGINAL`.

*Translated configuration* (the proofs hold only for it): target `x86_64-unknown-linux-gnu`,
`--no-default-features` with the features `request-state`, `server`, `client`, `client-side-sse`,
`transport-streamable-http-server`, `transport-streamable-http-client` and `auth` (plan
Section 15), with `overflow-checks=true` and `debug-assertions=true` (plan Section 1). Aeneas
`nightly-2026.11.24-fb44cb4`. The translation is of upstream origin/main `7caec76` with
translation patches 01–08 applied in order (`scripts/apply-patches.sh`).

*Line citations.* "upstream" is `crates/rmcp/src/model/elicitation_schema.rs` at origin/main
`7caec76` (the working tree, unmodified, blob `929b446`); "patched" is the copy with translation
patches 01–08 applied (`.llbc/work/…`), whose line numbers the `Source:` lines of
`Rmcp/Funs.lean` give. They first differ at line 885 (patch 08 hunk E1).

*Definitions:* `Defs.ElicitationSchema` in `formal/specs/Defs/ElicitationSchema.lean`, except the
internal-only message `requiredNotInPropertiesMsg` (X74), which is in
`formal/proofs/Proofs/Defs/ElicitationSchema.lean` (same namespace; decision XS3).

*Not translated, not specified:* the `NumberSchema` methods and the `number` builder helpers
(floats, decision XD3), `ConstTitle::new`, `LegacyEnumSchema::new`,
`TitledSingleSelectEnumSchema::new`, `UntitledItems::new`, `TitledItems::new`, the
`TitledMultiSelectEnumSchema` methods, `from_json_schema`, `from_type`, the `serde` impls and
the wire conversion `ElicitationSchemaWire`. *Translated, specified only through
`Defs.ElicitationSchema`:* the `Default` impls of `StringSchema`, `IntegerSchema`,
`BooleanSchema` and `ElicitationSchemaBuilder` (`defaultStringSchema`, `defaultIntegerSchema`,
`defaultBooleanSchema`, `emptyElicitationSchemaBuilder`; reached through X01, X14, X22, X46). The
`Default` impl of `EnumSchemaBuilder<SingleSelect>` has its own internal statement,
`EnumSchemaBuilderSingleSelect.default_valid` (result `newEnumSchemaBuilder` of the empty vector).
The patch-only helpers are specified the same way: `const_titles` through `constTitles`, and the
functions of `prim` through their models in `trusted/Rmcp/FunsExternal.lean`.
-/

open Aeneas Aeneas.Std Result
open Defs (utf8Bytes)
open Defs.ElicitationSchema
open rmcp.model.elicitation_schema (StringSchema StringFormat IntegerSchema BooleanSchema
  ConstTitle EnumSchema EnumSchemaBuilder SingleSelect MultiSelect PrimitiveSchemaDefinition
  ElicitationSchema ElicitationSchemaBuilder)

/-! ## X03–X13: `StringSchema` -/

/-- X03 `StringSchema::uri` (top-level → Specs): the default string schema with format `Uri`
(upstream and patched lines 155–160). No premise. -/
theorem Theorems.elicitation_schema.StringSchema.uri :
    rmcp.model.elicitation_schema.StringSchema.uri ⦃ (result : StringSchema) =>
      result = { defaultStringSchema with format := some .Uri } ⦄ :=
  rmcp.model.elicitation_schema.StringSchema.uri_spec

/--
info: 'Theorems.elicitation_schema.StringSchema.uri' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.elicitation_schema.StringSchema.uri

/-- X04 `StringSchema::date` (top-level → Specs): the default string schema with format `Date`
(upstream and patched lines 163–168). No premise. -/
theorem Theorems.elicitation_schema.StringSchema.date :
    rmcp.model.elicitation_schema.StringSchema.date ⦃ (result : StringSchema) =>
      result = { defaultStringSchema with format := some .Date } ⦄ :=
  rmcp.model.elicitation_schema.StringSchema.date_spec

/--
info: 'Theorems.elicitation_schema.StringSchema.date' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.elicitation_schema.StringSchema.date

/-- X05 `StringSchema::date_time` (top-level → Specs): the default string schema with format
`DateTime` (upstream and patched lines 171–176). No premise. -/
theorem Theorems.elicitation_schema.StringSchema.date_time :
    rmcp.model.elicitation_schema.StringSchema.date_time ⦃ (result : StringSchema) =>
      result = { defaultStringSchema with format := some .DateTime } ⦄ :=
  rmcp.model.elicitation_schema.StringSchema.date_time_spec

/--
info: 'Theorems.elicitation_schema.StringSchema.date_time' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.elicitation_schema.StringSchema.date_time

/-- X06 `StringSchema::title` (top-level → Specs): sets the title to `c = title.into()`, other
fields unchanged (upstream and patched lines 179–182).

Premise: caller code. Not covered: (I). -/
theorem Theorems.elicitation_schema.StringSchema.title {TitleLike : Type}
    (titleInto : core.convert.Into TitleLike (rmcp.alloc.borrow.Cow Str String))
    (self : StringSchema) (title : TitleLike) (c : rmcp.alloc.borrow.Cow Str String)
    (h_title_into : titleInto.into title = ok c) :
    rmcp.model.elicitation_schema.StringSchema.impl.title titleInto self title ⦃
      (result : StringSchema) =>
      result = { self with title := some c } ⦄ :=
  rmcp.model.elicitation_schema.StringSchema.impl.title_spec titleInto self title c h_title_into

/--
info: 'Theorems.elicitation_schema.StringSchema.title' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.elicitation_schema.StringSchema.title

/-- X07 `StringSchema::description` (top-level → Specs): sets the description to
`c = description.into()`, other fields unchanged (upstream and patched lines 185–188).

Premise: caller code. Not covered: (I). -/
theorem Theorems.elicitation_schema.StringSchema.description {DescriptionLike : Type}
    (descriptionInto : core.convert.Into DescriptionLike (rmcp.alloc.borrow.Cow Str String))
    (self : StringSchema) (description : DescriptionLike) (c : rmcp.alloc.borrow.Cow Str String)
    (h_description_into : descriptionInto.into description = ok c) :
    rmcp.model.elicitation_schema.StringSchema.impl.description descriptionInto self description ⦃
      (result : StringSchema) =>
      result = { self with description := some c } ⦄ :=
  rmcp.model.elicitation_schema.StringSchema.impl.description_spec descriptionInto self description
    c h_description_into

/--
info: 'Theorems.elicitation_schema.StringSchema.description' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.elicitation_schema.StringSchema.description

/-- X08 `StringSchema::with_length` (top-level → Specs): `Ok` with both length bounds set when
`min ≤ max`; otherwise `Err("min_length must be <= max_length")`, the schema dropped (upstream and
patched lines 191–198). No premise. -/
theorem Theorems.elicitation_schema.StringSchema.with_length (self : StringSchema)
    (min max : U32) :
    rmcp.model.elicitation_schema.StringSchema.with_length self min max ⦃
      (result : core.result.Result StringSchema Str) =>
      match result with
      | .Ok s =>
        min.val ≤ max.val ∧ s = { self with min_length := some min, max_length := some max }
      | .Err e => max.val < min.val ∧ e.val = utf8Bytes minLengthGtMaxLengthMsg ⦄ :=
  rmcp.model.elicitation_schema.StringSchema.with_length_spec self min max

/--
info: 'Theorems.elicitation_schema.StringSchema.with_length' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.elicitation_schema.StringSchema.with_length

/-- X09 `StringSchema::length` (top-level → Specs): for `min ≤ max`, both length bounds set
(upstream and patched lines 201–206).

Premise: (B). The case `min > max` is `StringSchema.length_fail`. -/
theorem Theorems.elicitation_schema.StringSchema.length (self : StringSchema) (min max : U32)
    (h_le : min.val ≤ max.val) :
    rmcp.model.elicitation_schema.StringSchema.length self min max ⦃ (result : StringSchema) =>
      result = { self with min_length := some min, max_length := some max } ⦄ :=
  rmcp.model.elicitation_schema.StringSchema.length_spec self min max h_le

/--
info: 'Theorems.elicitation_schema.StringSchema.length' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.elicitation_schema.StringSchema.length

/-- X09, failing case (top-level → Specs): for `min > max` the `assert!` panics (upstream line
202; Aeneas `massert`, `fail assertionFailure`). -/
theorem Theorems.elicitation_schema.StringSchema.length_fail (self : StringSchema)
    (min max : U32) (h_gt : max.val < min.val) :
    rmcp.model.elicitation_schema.StringSchema.length self min max = fail .assertionFailure :=
  rmcp.model.elicitation_schema.StringSchema.length_fail self min max h_gt

/--
info: 'Theorems.elicitation_schema.StringSchema.length_fail' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.elicitation_schema.StringSchema.length_fail

/-- X10 `StringSchema::min_length` (top-level → Specs): sets the minimum length, other fields
unchanged (upstream and patched lines 209–212). **H21**: no check against `max_length` or the
default. No premise. -/
theorem Theorems.elicitation_schema.StringSchema.min_length (self : StringSchema) (min : U32) :
    rmcp.model.elicitation_schema.StringSchema.impl.min_length self min ⦃
      (result : StringSchema) =>
      result = { self with min_length := some min } ⦄ :=
  rmcp.model.elicitation_schema.StringSchema.impl.min_length_spec self min

/--
info: 'Theorems.elicitation_schema.StringSchema.min_length' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.elicitation_schema.StringSchema.min_length

/-- X11 `StringSchema::max_length` (top-level → Specs): sets the maximum length, other fields
unchanged (upstream and patched lines 215–218). **H21**: no check against `min_length` or the
default. No premise. -/
theorem Theorems.elicitation_schema.StringSchema.max_length (self : StringSchema) (max : U32) :
    rmcp.model.elicitation_schema.StringSchema.impl.max_length self max ⦃
      (result : StringSchema) =>
      result = { self with max_length := some max } ⦄ :=
  rmcp.model.elicitation_schema.StringSchema.impl.max_length_spec self max

/--
info: 'Theorems.elicitation_schema.StringSchema.max_length' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.elicitation_schema.StringSchema.max_length

/-- X12 `StringSchema::format` (top-level → Specs): sets the format, other fields unchanged
(upstream and patched lines 221–224). No premise. -/
theorem Theorems.elicitation_schema.StringSchema.format (self : StringSchema)
    (format : StringFormat) :
    rmcp.model.elicitation_schema.StringSchema.impl.format self format ⦃
      (result : StringSchema) =>
      result = { self with format := some format } ⦄ :=
  rmcp.model.elicitation_schema.StringSchema.impl.format_spec self format

/--
info: 'Theorems.elicitation_schema.StringSchema.format' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.elicitation_schema.StringSchema.format

/-- X13 `StringSchema::with_default` (top-level → Specs): sets the default to
`d = default.into()`, other fields unchanged (upstream and patched lines 227–230). **H21**: the
default is not checked against the length bounds or the format.

Premise: caller code. Not covered: (I). -/
theorem Theorems.elicitation_schema.StringSchema.with_default {DefaultLike : Type}
    (defaultInto : core.convert.Into DefaultLike String) (self : StringSchema)
    (default : DefaultLike) (d : String) (h_default_into : defaultInto.into default = ok d) :
    rmcp.model.elicitation_schema.StringSchema.with_default defaultInto self default ⦃
      (result : StringSchema) =>
      result = { self with default := some d } ⦄ :=
  rmcp.model.elicitation_schema.StringSchema.with_default_spec defaultInto self default d
    h_default_into

/--
info: 'Theorems.elicitation_schema.StringSchema.with_default' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.elicitation_schema.StringSchema.with_default

/-! ## X15, X17–X21: `IntegerSchema` -/

/-- X15 `IntegerSchema::with_range` (top-level → Specs): `Ok` with both bounds set when
`min ≤ max`; otherwise `Err("minimum must be <= maximum")` (upstream and patched lines 409–416).
No premise. -/
theorem Theorems.elicitation_schema.IntegerSchema.with_range (self : IntegerSchema)
    (min max : I64) :
    rmcp.model.elicitation_schema.IntegerSchema.with_range self min max ⦃
      (result : core.result.Result IntegerSchema Str) =>
      match result with
      | .Ok s => min.val ≤ max.val ∧ s = { self with minimum := some min, maximum := some max }
      | .Err e => max.val < min.val ∧ e.val = utf8Bytes minimumGtMaximumMsg ⦄ :=
  rmcp.model.elicitation_schema.IntegerSchema.with_range_spec self min max

/--
info: 'Theorems.elicitation_schema.IntegerSchema.with_range' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.elicitation_schema.IntegerSchema.with_range

/-- X17 `IntegerSchema::minimum` (top-level → Specs): sets the minimum, other fields unchanged
(upstream and patched lines 427–430). **H21**: no check against `maximum` or the default.
No premise. -/
theorem Theorems.elicitation_schema.IntegerSchema.minimum (self : IntegerSchema) (min : I64) :
    rmcp.model.elicitation_schema.IntegerSchema.impl.minimum self min ⦃
      (result : IntegerSchema) =>
      result = { self with minimum := some min } ⦄ :=
  rmcp.model.elicitation_schema.IntegerSchema.impl.minimum_spec self min

/--
info: 'Theorems.elicitation_schema.IntegerSchema.minimum' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.elicitation_schema.IntegerSchema.minimum

/-- X18 `IntegerSchema::maximum` (top-level → Specs): sets the maximum, other fields unchanged
(upstream and patched lines 433–436). **H21**: no check against `minimum` or the default.
No premise. -/
theorem Theorems.elicitation_schema.IntegerSchema.maximum (self : IntegerSchema) (max : I64) :
    rmcp.model.elicitation_schema.IntegerSchema.impl.maximum self max ⦃
      (result : IntegerSchema) =>
      result = { self with maximum := some max } ⦄ :=
  rmcp.model.elicitation_schema.IntegerSchema.impl.maximum_spec self max

/--
info: 'Theorems.elicitation_schema.IntegerSchema.maximum' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.elicitation_schema.IntegerSchema.maximum

/-- X19 `IntegerSchema::title` (top-level → Specs): sets the title to `c = title.into()`
(upstream and patched lines 439–442).

Premise: caller code. Not covered: (I). -/
theorem Theorems.elicitation_schema.IntegerSchema.title {TitleLike : Type}
    (titleInto : core.convert.Into TitleLike (rmcp.alloc.borrow.Cow Str String))
    (self : IntegerSchema) (title : TitleLike) (c : rmcp.alloc.borrow.Cow Str String)
    (h_title_into : titleInto.into title = ok c) :
    rmcp.model.elicitation_schema.IntegerSchema.impl.title titleInto self title ⦃
      (result : IntegerSchema) =>
      result = { self with title := some c } ⦄ :=
  rmcp.model.elicitation_schema.IntegerSchema.impl.title_spec titleInto self title c h_title_into

/--
info: 'Theorems.elicitation_schema.IntegerSchema.title' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.elicitation_schema.IntegerSchema.title

/-- X20 `IntegerSchema::description` (top-level → Specs): sets the description to
`c = description.into()` (upstream and patched lines 445–448).

Premise: caller code. Not covered: (I). -/
theorem Theorems.elicitation_schema.IntegerSchema.description {DescriptionLike : Type}
    (descriptionInto : core.convert.Into DescriptionLike (rmcp.alloc.borrow.Cow Str String))
    (self : IntegerSchema) (description : DescriptionLike) (c : rmcp.alloc.borrow.Cow Str String)
    (h_description_into : descriptionInto.into description = ok c) :
    rmcp.model.elicitation_schema.IntegerSchema.impl.description descriptionInto self
      description ⦃ (result : IntegerSchema) =>
      result = { self with description := some c } ⦄ :=
  rmcp.model.elicitation_schema.IntegerSchema.impl.description_spec descriptionInto self description
    c h_description_into

/--
info: 'Theorems.elicitation_schema.IntegerSchema.description' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.elicitation_schema.IntegerSchema.description

/-- X21 `IntegerSchema::with_default` (top-level → Specs): sets the default, other fields
unchanged (upstream and patched lines 451–454). **H21**: the default is not checked against the
bounds. No premise. -/
theorem Theorems.elicitation_schema.IntegerSchema.with_default (self : IntegerSchema)
    (default : I64) :
    rmcp.model.elicitation_schema.IntegerSchema.with_default self default ⦃
      (result : IntegerSchema) =>
      result = { self with default := some default } ⦄ :=
  rmcp.model.elicitation_schema.IntegerSchema.with_default_spec self default

/--
info: 'Theorems.elicitation_schema.IntegerSchema.with_default' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.elicitation_schema.IntegerSchema.with_default

/-! ## X23, X24: `BooleanSchema` -/

/-- X23 `BooleanSchema::title` (top-level → Specs): sets the title to `c = title.into()`
(upstream and patched lines 502–505).

Premise: caller code. Not covered: (I). -/
theorem Theorems.elicitation_schema.BooleanSchema.title {TitleLike : Type}
    (titleInto : core.convert.Into TitleLike (rmcp.alloc.borrow.Cow Str String))
    (self : BooleanSchema) (title : TitleLike) (c : rmcp.alloc.borrow.Cow Str String)
    (h_title_into : titleInto.into title = ok c) :
    rmcp.model.elicitation_schema.BooleanSchema.impl.title titleInto self title ⦃
      (result : BooleanSchema) =>
      result = { self with title := some c } ⦄ :=
  rmcp.model.elicitation_schema.BooleanSchema.impl.title_spec titleInto self title c h_title_into

/--
info: 'Theorems.elicitation_schema.BooleanSchema.title' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.elicitation_schema.BooleanSchema.title

/-- X24 `BooleanSchema::description` (top-level → Specs): sets the description to
`c = description.into()` (upstream and patched lines 508–511).

Premise: caller code. Not covered: (I). -/
theorem Theorems.elicitation_schema.BooleanSchema.description {DescriptionLike : Type}
    (descriptionInto : core.convert.Into DescriptionLike (rmcp.alloc.borrow.Cow Str String))
    (self : BooleanSchema) (description : DescriptionLike) (c : rmcp.alloc.borrow.Cow Str String)
    (h_description_into : descriptionInto.into description = ok c) :
    rmcp.model.elicitation_schema.BooleanSchema.impl.description descriptionInto self
      description ⦃ (result : BooleanSchema) =>
      result = { self with description := some c } ⦄ :=
  rmcp.model.elicitation_schema.BooleanSchema.impl.description_spec descriptionInto self description
    c h_description_into

/--
info: 'Theorems.elicitation_schema.BooleanSchema.description' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.elicitation_schema.BooleanSchema.description

/-! ## X26–X29: `EnumSchemaBuilder<T>` (both select types) -/

/-- X26 `EnumSchemaBuilder::title` (top-level → Specs): sets the title to `c = value.into()`,
other fields unchanged (upstream and patched lines 863–866).

Premise: caller code. Not covered: (I). -/
theorem Theorems.elicitation_schema.EnumSchemaBuilder.title {T ValueLike : Type}
    (valueInto : core.convert.Into ValueLike (rmcp.alloc.borrow.Cow Str String))
    (self : EnumSchemaBuilder T) (value : ValueLike) (c : rmcp.alloc.borrow.Cow Str String)
    (h_value_into : valueInto.into value = ok c) :
    rmcp.model.elicitation_schema.EnumSchemaBuilder.impl.title valueInto self value ⦃
      (result : EnumSchemaBuilder T) =>
      result = { self with title := some c } ⦄ :=
  rmcp.model.elicitation_schema.EnumSchemaBuilder.impl.title_spec valueInto self value c
    h_value_into

/--
info: 'Theorems.elicitation_schema.EnumSchemaBuilder.title' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.elicitation_schema.EnumSchemaBuilder.title

/-- X27 `EnumSchemaBuilder::description` (top-level → Specs): sets the description to
`c = value.into()`, other fields unchanged (upstream and patched lines 869–872).

Premise: caller code. Not covered: (I). -/
theorem Theorems.elicitation_schema.EnumSchemaBuilder.description {T ValueLike : Type}
    (valueInto : core.convert.Into ValueLike (rmcp.alloc.borrow.Cow Str String))
    (self : EnumSchemaBuilder T) (value : ValueLike) (c : rmcp.alloc.borrow.Cow Str String)
    (h_value_into : valueInto.into value = ok c) :
    rmcp.model.elicitation_schema.EnumSchemaBuilder.impl.description valueInto self value ⦃
      (result : EnumSchemaBuilder T) =>
      result = { self with description := some c } ⦄ :=
  rmcp.model.elicitation_schema.EnumSchemaBuilder.impl.description_spec valueInto self value c
    h_value_into

/--
info: 'Theorems.elicitation_schema.EnumSchemaBuilder.description' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.elicitation_schema.EnumSchemaBuilder.description

/-- X28 `EnumSchemaBuilder::untitled` (top-level → Specs): untitled, with no titles, other
fields unchanged (upstream and patched lines 876–880). No premise. -/
theorem Theorems.elicitation_schema.EnumSchemaBuilder.untitled {T : Type}
    (self : EnumSchemaBuilder T) :
    rmcp.model.elicitation_schema.EnumSchemaBuilder.untitled self ⦃
      (result : EnumSchemaBuilder T) =>
      result = { self with titled := false, enum_titles := alloc.vec.Vec.new String } ⦄ :=
  rmcp.model.elicitation_schema.EnumSchemaBuilder.untitled_spec self

/--
info: 'Theorems.elicitation_schema.EnumSchemaBuilder.untitled' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.elicitation_schema.EnumSchemaBuilder.untitled

/-- X29 `EnumSchemaBuilder::enum_titles` (top-level → Specs; linkage patch-08, hunk E1): `Ok`,
titled with these titles, when there are as many titles as values; otherwise
`Err` with the message of `titlesMismatchMsg (number of values) (number of titles)` (upstream
lines 883–894; patched lines 883–893, the `format!` in `prim::titles_mismatch_message`, patched
lines 1814–1819). No premise. Not covered: (A). -/
theorem Theorems.elicitation_schema.EnumSchemaBuilder.enum_titles {T : Type}
    (self : EnumSchemaBuilder T) (titles : alloc.vec.Vec String) :
    rmcp.model.elicitation_schema.EnumSchemaBuilder.impl.enum_titles self titles ⦃
      (result : core.result.Result (EnumSchemaBuilder T) String) =>
      match result with
      | .Ok b =>
        titles.val.length = self.enum_values.val.length ∧
          b = { self with titled := true, enum_titles := titles }
      | .Err e =>
        titles.val.length ≠ self.enum_values.val.length ∧
          e = titlesMismatchMsg self.enum_values.val.length titles.val.length ⦄ :=
  rmcp.model.elicitation_schema.EnumSchemaBuilder.impl.enum_titles_spec self titles

/--
info: 'Theorems.elicitation_schema.EnumSchemaBuilder.enum_titles' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.elicitation_schema.EnumSchemaBuilder.enum_titles

/-! ## X31–X33: `EnumSchemaBuilder<SingleSelect>` -/

/-- X31 `EnumSchemaBuilder::<SingleSelect>::multiselect` (top-level → Specs): the multi-select
builder with the same values, titles, title and description, and no item bounds or default
(upstream lines 911–923, patched 910–922). No premise. -/
theorem Theorems.elicitation_schema.EnumSchemaBuilderSingleSelect.multiselect
    (self : EnumSchemaBuilder SingleSelect) :
    rmcp.model.elicitation_schema.EnumSchemaBuilderSingleSelect.multiselect self ⦃
      (result : EnumSchemaBuilder MultiSelect) =>
      result =
        { enum_values := self.enum_values, titled := self.titled, title := self.title,
          description := self.description, enum_titles := self.enum_titles, min_items := none,
          max_items := none, default := alloc.vec.Vec.new String, select_type := () } ⦄ :=
  rmcp.model.elicitation_schema.EnumSchemaBuilderSingleSelect.multiselect_spec self

/--
info: 'Theorems.elicitation_schema.EnumSchemaBuilderSingleSelect.multiselect' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.elicitation_schema.EnumSchemaBuilderSingleSelect.multiselect

/-- X32 `EnumSchemaBuilder::<SingleSelect>::with_default` (top-level → Specs; linkage patch-08,
hunk E2): for `v = default_value.into()`, `Ok` with the default `[v]` when `v` is an enum value;
otherwise `Err("Provided default value is not in enum values")` (upstream lines 926–936; patched
lines 925–935).

Premise: caller code. Not covered: (I), (A). -/
theorem Theorems.elicitation_schema.EnumSchemaBuilderSingleSelect.with_default
    {DefaultLike : Type} (defaultInto : core.convert.Into DefaultLike String)
    (self : EnumSchemaBuilder SingleSelect) (default_value : DefaultLike) (v : String)
    (h_default_into : defaultInto.into default_value = ok v) :
    rmcp.model.elicitation_schema.EnumSchemaBuilderSingleSelect.with_default defaultInto self
      default_value ⦃ (result : core.result.Result (EnumSchemaBuilder SingleSelect) String) =>
      match result with
      | .Ok b =>
        v ∈ self.enum_values.val ∧ b.default.val = [v] ∧ b = { self with default := b.default }
      | .Err e => v ∉ self.enum_values.val ∧ e = defaultNotInValuesMsg ⦄ :=
  rmcp.model.elicitation_schema.EnumSchemaBuilderSingleSelect.with_default_spec defaultInto self
    default_value v h_default_into

/--
info: 'Theorems.elicitation_schema.EnumSchemaBuilderSingleSelect.with_default' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.elicitation_schema.EnumSchemaBuilderSingleSelect.with_default

/-- X33 `EnumSchemaBuilder::<SingleSelect>::build` (top-level → Specs; linkage patch-08, hunk
E8): a single-select enum schema with the builder's title and description and, as default, the
last default value (`self.default.pop()`; at most one in practice). Titled: the options pair the
`i`-th title with the `i`-th value, as many as the shorter list (`constTitles`); untitled: the
values (upstream lines 939–965; patched lines 938–959, the options built by `const_titles`,
patched lines 1795–1805). No premise. Not covered: (A), (C). -/
theorem Theorems.elicitation_schema.EnumSchemaBuilderSingleSelect.build
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
          u.default = self.default.val.getLast? ⦄ :=
  rmcp.model.elicitation_schema.EnumSchemaBuilderSingleSelect.build_spec self

/--
info: 'Theorems.elicitation_schema.EnumSchemaBuilderSingleSelect.build' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.elicitation_schema.EnumSchemaBuilderSingleSelect.build

/-! ## X34–X38: `EnumSchemaBuilder<MultiSelect>` -/

/-- X34 `EnumSchemaBuilder::<MultiSelect>::single_select` (top-level → Specs): the single-select
builder with the same values, titles, title and description, and no item bounds or default
(upstream lines 972–984, patched 966–978). No premise. -/
theorem Theorems.elicitation_schema.EnumSchemaBuilderMultiSelect.single_select
    (self : EnumSchemaBuilder MultiSelect) :
    rmcp.model.elicitation_schema.EnumSchemaBuilderMultiSelect.single_select self ⦃
      (result : EnumSchemaBuilder SingleSelect) =>
      result =
        { enum_values := self.enum_values, titled := self.titled, title := self.title,
          description := self.description, enum_titles := self.enum_titles, min_items := none,
          max_items := none, default := alloc.vec.Vec.new String, select_type := () } ⦄ :=
  rmcp.model.elicitation_schema.EnumSchemaBuilderMultiSelect.single_select_spec self

/--
info: 'Theorems.elicitation_schema.EnumSchemaBuilderMultiSelect.single_select' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.elicitation_schema.EnumSchemaBuilderMultiSelect.single_select

/-- X35 `EnumSchemaBuilder::<MultiSelect>::with_default` (top-level → Specs; linkage patch-08,
hunk E3): `Ok` with the default `default_values` when every check passes; otherwise `Err` with
the message of the first failing check, in the Rust order (`multiSelectDefaultError?`: a value
not an enum value; for a non-empty default, fewer values than `min_items`, more than
`max_items`) (upstream lines 996–1023; patched lines 990–1018). An empty default passes the bound
checks. **H22**: duplicate default values are accepted. No premise. Not covered: (A). -/
theorem Theorems.elicitation_schema.EnumSchemaBuilderMultiSelect.with_default
    (self : EnumSchemaBuilder MultiSelect) (default_values : alloc.vec.Vec String) :
    rmcp.model.elicitation_schema.EnumSchemaBuilderMultiSelect.with_default self default_values ⦃
      (result : core.result.Result (EnumSchemaBuilder MultiSelect) String) =>
      match result with
      | .Ok b =>
        multiSelectDefaultError? self default_values.val = none ∧
          b = { self with default := default_values }
      | .Err e => multiSelectDefaultError? self default_values.val = some e ⦄ :=
  rmcp.model.elicitation_schema.EnumSchemaBuilderMultiSelect.with_default_spec self default_values

/--
info: 'Theorems.elicitation_schema.EnumSchemaBuilderMultiSelect.with_default' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.elicitation_schema.EnumSchemaBuilderMultiSelect.with_default

/-- X36 `EnumSchemaBuilder::<MultiSelect>::min_items` (top-level → Specs; linkage patch-08, hunk
E4): `Ok` with the minimum `value` when both checks pass; otherwise `Err` with the message of the
first failing check (`minItemsError?`: above `max_items`; a non-empty default with fewer values)
(upstream lines 1034–1046; patched lines 1029–1041). **H22**: `value` is not checked against the
number of enum values. No premise. Not covered: (A). -/
theorem Theorems.elicitation_schema.EnumSchemaBuilderMultiSelect.min_items
    (self : EnumSchemaBuilder MultiSelect) (value : U64) :
    rmcp.model.elicitation_schema.EnumSchemaBuilderMultiSelect.min_items self value ⦃
      (result : core.result.Result (EnumSchemaBuilder MultiSelect) String) =>
      match result with
      | .Ok b => minItemsError? self value = none ∧ b = { self with min_items := some value }
      | .Err e => minItemsError? self value = some e ⦄ :=
  rmcp.model.elicitation_schema.EnumSchemaBuilderMultiSelect.min_items_spec self value

/--
info: 'Theorems.elicitation_schema.EnumSchemaBuilderMultiSelect.min_items' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.elicitation_schema.EnumSchemaBuilderMultiSelect.min_items

/-- X37 `EnumSchemaBuilder::<MultiSelect>::max_items` (top-level → Specs; linkage patch-08, hunk
E5): `Ok` with the maximum `value` when both checks pass; otherwise `Err` with the message of the
first failing check (`maxItemsError?`: below `min_items`; a non-empty default with more values)
(upstream lines 1057–1068; patched lines 1052–1063). A maximum above the number of enum values is
not checked. No premise. Not covered: (A). -/
theorem Theorems.elicitation_schema.EnumSchemaBuilderMultiSelect.max_items
    (self : EnumSchemaBuilder MultiSelect) (value : U64) :
    rmcp.model.elicitation_schema.EnumSchemaBuilderMultiSelect.max_items self value ⦃
      (result : core.result.Result (EnumSchemaBuilder MultiSelect) String) =>
      match result with
      | .Ok b => maxItemsError? self value = none ∧ b = { self with max_items := some value }
      | .Err e => maxItemsError? self value = some e ⦄ :=
  rmcp.model.elicitation_schema.EnumSchemaBuilderMultiSelect.max_items_spec self value

/--
info: 'Theorems.elicitation_schema.EnumSchemaBuilderMultiSelect.max_items' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.elicitation_schema.EnumSchemaBuilderMultiSelect.max_items

/-- X38 `EnumSchemaBuilder::<MultiSelect>::build` (top-level → Specs; linkage patch-08, hunk
E8): a multi-select enum schema with the builder's title, description and item bounds, and the
default if it is non-empty (`None` for an empty one). Titled: the options `constTitles titles
values`; untitled: the values (upstream lines 1071–1112; patched lines 1066–1102 and
`const_titles`, patched lines 1795–1805). No premise. Not covered: (A), (C). -/
theorem Theorems.elicitation_schema.EnumSchemaBuilderMultiSelect.build
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
          u.default = (if self.default.val = [] then none else some self.default) ⦄ :=
  rmcp.model.elicitation_schema.EnumSchemaBuilderMultiSelect.build_spec self

/--
info: 'Theorems.elicitation_schema.EnumSchemaBuilderMultiSelect.build' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.elicitation_schema.EnumSchemaBuilderMultiSelect.build

/-! ## X39: `EnumSchema::builder` -/

/-- X39 `EnumSchema::builder` (top-level → Specs): the single-select builder for `values` with
nothing else set (`EnumSchemaBuilder::new(values)`, upstream lines 1138–1140, patched
1128–1130). No premise. -/
theorem Theorems.elicitation_schema.EnumSchema.builder (values : alloc.vec.Vec String) :
    rmcp.model.elicitation_schema.EnumSchema.builder values ⦃
      (result : EnumSchemaBuilder SingleSelect) =>
      result = newEnumSchemaBuilder values ⦄ :=
  rmcp.model.elicitation_schema.EnumSchema.builder_spec values

/--
info: 'Theorems.elicitation_schema.EnumSchema.builder' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.elicitation_schema.EnumSchema.builder

/-! ## X40–X45: `ElicitationSchema` -/

/-- X40 `ElicitationSchema::new` (top-level → Specs; linkage patch-08, hunk E6): the schema with
these properties, the property order their names in the map's order, and no dialect, title,
required list or description (upstream lines 1269–1280; patched lines 1259–1270, the key list
from `prim::sorted_keys`, patched lines 1821–1825).

Premise: (L). Not covered: (A). The case `¬ PropertiesFit properties` is
`ElicitationSchema.new_fail`. -/
theorem Theorems.elicitation_schema.ElicitationSchema.new
    (properties : alloc.collections.btree.map.BTreeMap String PrimitiveSchemaDefinition
      alloc.alloc.Global)
    (h_fit : PropertiesFit properties) :
    rmcp.model.elicitation_schema.ElicitationSchema.new properties ⦃
      (result : ElicitationSchema) =>
      result.schema = none ∧ result.title = none ∧ result.properties = properties ∧
        result.property_order.map (·.val) = some (propertyNames properties) ∧
        result.required = none ∧ result.description = none ⦄ :=
  rmcp.model.elicitation_schema.ElicitationSchema.new_spec properties h_fit

/--
info: 'Theorems.elicitation_schema.ElicitationSchema.new' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.elicitation_schema.ElicitationSchema.new

/-- X40, failing case (top-level → Specs): when the key list would exceed `isize::MAX` bytes the
model of `prim::sorted_keys` panics (no Rust map is that large). -/
theorem Theorems.elicitation_schema.ElicitationSchema.new_fail
    (properties : alloc.collections.btree.map.BTreeMap String PrimitiveSchemaDefinition
      alloc.alloc.Global)
    (h_big : ¬ PropertiesFit properties) :
    rmcp.model.elicitation_schema.ElicitationSchema.new properties = fail .panic :=
  rmcp.model.elicitation_schema.ElicitationSchema.new_fail properties h_big

/--
info: 'Theorems.elicitation_schema.ElicitationSchema.new_fail' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.elicitation_schema.ElicitationSchema.new_fail

/-- X41 `ElicitationSchema::with_required` (top-level → Specs): sets the required list, other
fields unchanged (upstream lines 1351–1354, patched 1341–1344). Recorded behaviour (not a bug,
decision XS4): the names are not checked against the properties, and an empty list gives
`Some([])`, so the result need not be `ConsistentElicitationSchema`. No premise. -/
theorem Theorems.elicitation_schema.ElicitationSchema.with_required (self : ElicitationSchema)
    (required : alloc.vec.Vec String) :
    rmcp.model.elicitation_schema.ElicitationSchema.with_required self required ⦃
      (result : ElicitationSchema) =>
      result = { self with required := some required } ⦄ :=
  rmcp.model.elicitation_schema.ElicitationSchema.with_required_spec self required

/--
info: 'Theorems.elicitation_schema.ElicitationSchema.with_required' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.elicitation_schema.ElicitationSchema.with_required

/-- X42 `ElicitationSchema::with_title` (top-level → Specs): sets the title to
`c = title.into()` (upstream lines 1357–1360, patched 1347–1350).

Premise: caller code. Not covered: (I). -/
theorem Theorems.elicitation_schema.ElicitationSchema.with_title {TitleLike : Type}
    (titleInto : core.convert.Into TitleLike (rmcp.alloc.borrow.Cow Str String))
    (self : ElicitationSchema) (title : TitleLike) (c : rmcp.alloc.borrow.Cow Str String)
    (h_title_into : titleInto.into title = ok c) :
    rmcp.model.elicitation_schema.ElicitationSchema.with_title titleInto self title ⦃
      (result : ElicitationSchema) =>
      result = { self with title := some c } ⦄ :=
  rmcp.model.elicitation_schema.ElicitationSchema.with_title_spec titleInto self title c
    h_title_into

/--
info: 'Theorems.elicitation_schema.ElicitationSchema.with_title' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.elicitation_schema.ElicitationSchema.with_title

/-- X43 `ElicitationSchema::with_description` (top-level → Specs): sets the description to
`c = description.into()` (upstream lines 1363–1366, patched 1353–1356).

Premise: caller code. Not covered: (I). -/
theorem Theorems.elicitation_schema.ElicitationSchema.with_description {DescriptionLike : Type}
    (descriptionInto : core.convert.Into DescriptionLike (rmcp.alloc.borrow.Cow Str String))
    (self : ElicitationSchema) (description : DescriptionLike)
    (c : rmcp.alloc.borrow.Cow Str String)
    (h_description_into : descriptionInto.into description = ok c) :
    rmcp.model.elicitation_schema.ElicitationSchema.with_description descriptionInto self
      description ⦃ (result : ElicitationSchema) =>
      result = { self with description := some c } ⦄ :=
  rmcp.model.elicitation_schema.ElicitationSchema.with_description_spec descriptionInto self
    description c h_description_into

/--
info: 'Theorems.elicitation_schema.ElicitationSchema.with_description' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.elicitation_schema.ElicitationSchema.with_description

/-- X44 `ElicitationSchema::with_schema` (top-level → Specs): sets the dialect (`$schema`) to
`c = schema.into()` (upstream lines 1369–1372, patched 1359–1362).

Premise: caller code. Not covered: (I). -/
theorem Theorems.elicitation_schema.ElicitationSchema.with_schema {SchemaLike : Type}
    (schemaInto : core.convert.Into SchemaLike (rmcp.alloc.borrow.Cow Str String))
    (self : ElicitationSchema) (schema : SchemaLike) (c : rmcp.alloc.borrow.Cow Str String)
    (h_schema_into : schemaInto.into schema = ok c) :
    rmcp.model.elicitation_schema.ElicitationSchema.with_schema schemaInto self schema ⦃
      (result : ElicitationSchema) =>
      result = { self with schema := some c } ⦄ :=
  rmcp.model.elicitation_schema.ElicitationSchema.with_schema_spec schemaInto self schema c
    h_schema_into

/--
info: 'Theorems.elicitation_schema.ElicitationSchema.with_schema' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.elicitation_schema.ElicitationSchema.with_schema

/-- X45 `ElicitationSchema::builder` (top-level → Specs): the empty builder
(`ElicitationSchemaBuilder::new()`, upstream lines 1375–1377, patched 1365–1367). No premise. -/
theorem Theorems.elicitation_schema.ElicitationSchema.builder :
    rmcp.model.elicitation_schema.ElicitationSchema.builder ⦃
      (result : ElicitationSchemaBuilder) =>
      result = emptyElicitationSchemaBuilder ⦄ :=
  rmcp.model.elicitation_schema.ElicitationSchema.builder_spec

/--
info: 'Theorems.elicitation_schema.ElicitationSchema.builder' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.elicitation_schema.ElicitationSchema.builder

/-! ## X49–X73, X75: `ElicitationSchemaBuilder` -/

/-- X49 `ElicitationSchemaBuilder::string_property` (top-level → Specs): property `n =
name.into()` set to `String(s)`, where `s` is the caller's closure applied to the default string
schema; the required list, title and description unchanged (upstream lines 1436–1446, patched
1426–1436). **H23**: documented "(required)", but `n` is not added to the required list.

Premise: caller code. Not covered: (I), (M), (A). -/
theorem Theorems.elicitation_schema.ElicitationSchemaBuilder.string_property {NameLike F : Type}
    (nameInto : core.convert.Into NameLike String)
    (fOnce : core.ops.function.FnOnce F StringSchema StringSchema)
    (self : ElicitationSchemaBuilder) («name» : NameLike) (f : F) (n : String) (s : StringSchema)
    (h_name_into : nameInto.into «name» = ok n)
    (h_f : fOnce.call_once f defaultStringSchema = ok s) :
    rmcp.model.elicitation_schema.ElicitationSchemaBuilder.string_property nameInto fOnce self
      «name» f ⦃ (result : ElicitationSchemaBuilder) =>
      result.required = self.required ∧ result.title = self.title ∧
        result.description = self.description ∧
        PropertyInserted self.properties n (.String s) result.properties ⦄ :=
  rmcp.model.elicitation_schema.ElicitationSchemaBuilder.string_property_spec nameInto fOnce self
    «name» f n s h_name_into h_f

/--
info: 'Theorems.elicitation_schema.ElicitationSchemaBuilder.string_property' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.elicitation_schema.ElicitationSchemaBuilder.string_property

/-- X50 `ElicitationSchemaBuilder::required_string_property` (top-level → Specs): `n =
name.into()` appended to the required list and property `n` set to `String(s)`, `s` the closure
applied to the default string schema (upstream lines 1449–1461, patched 1439–1451). **H20**.

Premises: caller code, (R). Not covered: (I), (M), (A). -/
theorem Theorems.elicitation_schema.ElicitationSchemaBuilder.required_string_property
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
        PropertyInserted self.properties n (.String s) result.properties ⦄ :=
  rmcp.model.elicitation_schema.ElicitationSchemaBuilder.required_string_property_spec nameInto
    fOnce self «name» f n s h_name_into h_f h_required_len

/--
info: 'Theorems.elicitation_schema.ElicitationSchemaBuilder.required_string_property' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.elicitation_schema.ElicitationSchemaBuilder.required_string_property

/-- X51 `ElicitationSchemaBuilder::integer_property` (top-level → Specs): property `n =
name.into()` set to `Integer(i)`, `i` the closure applied to the default integer schema; the
required list, title and description unchanged (upstream lines 1492–1502, patched 1482–1492).

Premise: caller code. Not covered: (I), (M), (A). -/
theorem Theorems.elicitation_schema.ElicitationSchemaBuilder.integer_property {NameLike F : Type}
    (nameInto : core.convert.Into NameLike String)
    (fOnce : core.ops.function.FnOnce F IntegerSchema IntegerSchema)
    (self : ElicitationSchemaBuilder) («name» : NameLike) (f : F) (n : String) (i : IntegerSchema)
    (h_name_into : nameInto.into «name» = ok n)
    (h_f : fOnce.call_once f defaultIntegerSchema = ok i) :
    rmcp.model.elicitation_schema.ElicitationSchemaBuilder.integer_property nameInto fOnce self
      «name» f ⦃ (result : ElicitationSchemaBuilder) =>
      result.required = self.required ∧ result.title = self.title ∧
        result.description = self.description ∧
        PropertyInserted self.properties n (.Integer i) result.properties ⦄ :=
  rmcp.model.elicitation_schema.ElicitationSchemaBuilder.integer_property_spec nameInto fOnce self
    «name» f n i h_name_into h_f

/--
info: 'Theorems.elicitation_schema.ElicitationSchemaBuilder.integer_property' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.elicitation_schema.ElicitationSchemaBuilder.integer_property

/-- X52 `ElicitationSchemaBuilder::required_integer_property` (top-level → Specs): `n` appended
to the required list and property `n` set to `Integer(i)`, `i` the closure applied to the
default integer schema (upstream lines 1505–1517, patched 1495–1507). **H20**.

Premises: caller code, (R). Not covered: (I), (M), (A). -/
theorem Theorems.elicitation_schema.ElicitationSchemaBuilder.required_integer_property
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
        PropertyInserted self.properties n (.Integer i) result.properties ⦄ :=
  rmcp.model.elicitation_schema.ElicitationSchemaBuilder.required_integer_property_spec nameInto
    fOnce self «name» f n i h_name_into h_f h_required_len

/--
info: 'Theorems.elicitation_schema.ElicitationSchemaBuilder.required_integer_property' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.elicitation_schema.ElicitationSchemaBuilder.required_integer_property

/-- X53 `ElicitationSchemaBuilder::bool_property` (top-level → Specs): property `n =
name.into()` set to `Boolean(b)`, `b` the closure applied to the default boolean schema; the
required list, title and description unchanged (upstream lines 1520–1530, patched 1510–1520).

Premise: caller code. Not covered: (I), (M), (A). -/
theorem Theorems.elicitation_schema.ElicitationSchemaBuilder.bool_property {NameLike F : Type}
    (nameInto : core.convert.Into NameLike String)
    (fOnce : core.ops.function.FnOnce F BooleanSchema BooleanSchema)
    (self : ElicitationSchemaBuilder) («name» : NameLike) (f : F) (n : String) (b : BooleanSchema)
    (h_name_into : nameInto.into «name» = ok n)
    (h_f : fOnce.call_once f defaultBooleanSchema = ok b) :
    rmcp.model.elicitation_schema.ElicitationSchemaBuilder.bool_property nameInto fOnce self
      «name» f ⦃ (result : ElicitationSchemaBuilder) =>
      result.required = self.required ∧ result.title = self.title ∧
        result.description = self.description ∧
        PropertyInserted self.properties n (.Boolean b) result.properties ⦄ :=
  rmcp.model.elicitation_schema.ElicitationSchemaBuilder.bool_property_spec nameInto fOnce self
    «name» f n b h_name_into h_f

/--
info: 'Theorems.elicitation_schema.ElicitationSchemaBuilder.bool_property' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.elicitation_schema.ElicitationSchemaBuilder.bool_property

/-- X54 `ElicitationSchemaBuilder::required_bool_property` (top-level → Specs): `n` appended to
the required list and property `n` set to `Boolean(b)`, `b` the closure applied to the default
boolean schema (upstream lines 1533–1545, patched 1523–1535). **H20**.

Premises: caller code, (R). Not covered: (I), (M), (A). -/
theorem Theorems.elicitation_schema.ElicitationSchemaBuilder.required_bool_property
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
        PropertyInserted self.properties n (.Boolean b) result.properties ⦄ :=
  rmcp.model.elicitation_schema.ElicitationSchemaBuilder.required_bool_property_spec nameInto fOnce
    self «name» f n b h_name_into h_f h_required_len

/--
info: 'Theorems.elicitation_schema.ElicitationSchemaBuilder.required_bool_property' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.elicitation_schema.ElicitationSchemaBuilder.required_bool_property

/-- X55 `ElicitationSchemaBuilder::required_string` (top-level → Specs): `n = name.into()`
required, with the default string schema (upstream lines 1552–1554, patched 1542–1544). **H20**.

Premises: caller code, (R). Not covered: (I), (M), (A). -/
theorem Theorems.elicitation_schema.ElicitationSchemaBuilder.required_string {NameLike : Type}
    (nameInto : core.convert.Into NameLike String) (self : ElicitationSchemaBuilder)
    («name» : NameLike) (n : String) (h_name_into : nameInto.into «name» = ok n)
    (h_required_len : self.required.val.length < Usize.max) :
    rmcp.model.elicitation_schema.ElicitationSchemaBuilder.required_string nameInto self «name» ⦃
      (result : ElicitationSchemaBuilder) =>
      result.required.val = self.required.val ++ [n] ∧ result.title = self.title ∧
        result.description = self.description ∧
        PropertyInserted self.properties n (.String defaultStringSchema) result.properties ⦄ :=
  rmcp.model.elicitation_schema.ElicitationSchemaBuilder.required_string_spec nameInto self «name» n
    h_name_into h_required_len

/--
info: 'Theorems.elicitation_schema.ElicitationSchemaBuilder.required_string' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.elicitation_schema.ElicitationSchemaBuilder.required_string

/-- X56 `ElicitationSchemaBuilder::optional_string` (top-level → Specs): property `n =
name.into()` with the default string schema, not required (upstream lines 1557–1559, patched
1547–1549).

Premise: caller code. Not covered: (I), (M), (A). -/
theorem Theorems.elicitation_schema.ElicitationSchemaBuilder.optional_string {NameLike : Type}
    (nameInto : core.convert.Into NameLike String) (self : ElicitationSchemaBuilder)
    («name» : NameLike) (n : String) (h_name_into : nameInto.into «name» = ok n) :
    rmcp.model.elicitation_schema.ElicitationSchemaBuilder.optional_string nameInto self «name» ⦃
      (result : ElicitationSchemaBuilder) =>
      result.required = self.required ∧ result.title = self.title ∧
        result.description = self.description ∧
        PropertyInserted self.properties n (.String defaultStringSchema) result.properties ⦄ :=
  rmcp.model.elicitation_schema.ElicitationSchemaBuilder.optional_string_spec nameInto self «name» n
    h_name_into

/--
info: 'Theorems.elicitation_schema.ElicitationSchemaBuilder.optional_string' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.elicitation_schema.ElicitationSchemaBuilder.optional_string

/-- X57 `ElicitationSchemaBuilder::required_email` (top-level → Specs): `n = name.into()`
required, a string with format `Email` (upstream lines 1562–1567, patched 1552–1557). **H20**.

Premises: caller code, (R). Not covered: (I), (M), (A). -/
theorem Theorems.elicitation_schema.ElicitationSchemaBuilder.required_email {NameLike : Type}
    (nameInto : core.convert.Into NameLike String) (self : ElicitationSchemaBuilder)
    («name» : NameLike) (n : String) (h_name_into : nameInto.into «name» = ok n)
    (h_required_len : self.required.val.length < Usize.max) :
    rmcp.model.elicitation_schema.ElicitationSchemaBuilder.required_email nameInto self «name» ⦃
      (result : ElicitationSchemaBuilder) =>
      result.required.val = self.required.val ++ [n] ∧ result.title = self.title ∧
        result.description = self.description ∧
        PropertyInserted self.properties n
          (.String { defaultStringSchema with format := some .Email }) result.properties ⦄ :=
  rmcp.model.elicitation_schema.ElicitationSchemaBuilder.required_email_spec nameInto self «name» n
    h_name_into h_required_len

/--
info: 'Theorems.elicitation_schema.ElicitationSchemaBuilder.required_email' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.elicitation_schema.ElicitationSchemaBuilder.required_email

/-- X58 `ElicitationSchemaBuilder::optional_email` (top-level → Specs): property `n =
name.into()`, a string with format `Email`, not required (upstream lines 1570–1575, patched
1560–1565).

Premise: caller code. Not covered: (I), (M), (A). -/
theorem Theorems.elicitation_schema.ElicitationSchemaBuilder.optional_email {NameLike : Type}
    (nameInto : core.convert.Into NameLike String) (self : ElicitationSchemaBuilder)
    («name» : NameLike) (n : String) (h_name_into : nameInto.into «name» = ok n) :
    rmcp.model.elicitation_schema.ElicitationSchemaBuilder.optional_email nameInto self «name» ⦃
      (result : ElicitationSchemaBuilder) =>
      result.required = self.required ∧ result.title = self.title ∧
        result.description = self.description ∧
        PropertyInserted self.properties n
          (.String { defaultStringSchema with format := some .Email }) result.properties ⦄ :=
  rmcp.model.elicitation_schema.ElicitationSchemaBuilder.optional_email_spec nameInto self «name» n
    h_name_into

/--
info: 'Theorems.elicitation_schema.ElicitationSchemaBuilder.optional_email' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.elicitation_schema.ElicitationSchemaBuilder.optional_email

/-- X59 `ElicitationSchemaBuilder::required_string_with` (top-level → Specs): `n` required, with
`String(s)`, `s` the closure applied to the default string schema (upstream lines 1578–1587,
patched 1568–1577; the closure is called before `name.into()`). **H20**.

Premises: caller code, (R). Not covered: (I), (M), (A). -/
theorem Theorems.elicitation_schema.ElicitationSchemaBuilder.required_string_with
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
        PropertyInserted self.properties n (.String s) result.properties ⦄ :=
  rmcp.model.elicitation_schema.ElicitationSchemaBuilder.required_string_with_spec nameInto fOnce
    self «name» f n s h_name_into h_f h_required_len

/--
info: 'Theorems.elicitation_schema.ElicitationSchemaBuilder.required_string_with' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.elicitation_schema.ElicitationSchemaBuilder.required_string_with

/-- X60 `ElicitationSchemaBuilder::optional_string_with` (top-level → Specs): property `n` set to
`String(s)`, not required (upstream lines 1590–1599, patched 1580–1589).

Premise: caller code. Not covered: (I), (M), (A). -/
theorem Theorems.elicitation_schema.ElicitationSchemaBuilder.optional_string_with
    {NameLike F : Type} (nameInto : core.convert.Into NameLike String)
    (fOnce : core.ops.function.FnOnce F StringSchema StringSchema)
    (self : ElicitationSchemaBuilder) («name» : NameLike) (f : F) (n : String) (s : StringSchema)
    (h_name_into : nameInto.into «name» = ok n)
    (h_f : fOnce.call_once f defaultStringSchema = ok s) :
    rmcp.model.elicitation_schema.ElicitationSchemaBuilder.optional_string_with nameInto fOnce
      self «name» f ⦃ (result : ElicitationSchemaBuilder) =>
      result.required = self.required ∧ result.title = self.title ∧
        result.description = self.description ∧
        PropertyInserted self.properties n (.String s) result.properties ⦄ :=
  rmcp.model.elicitation_schema.ElicitationSchemaBuilder.optional_string_with_spec nameInto fOnce
    self «name» f n s h_name_into h_f

/--
info: 'Theorems.elicitation_schema.ElicitationSchemaBuilder.optional_string_with' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.elicitation_schema.ElicitationSchemaBuilder.optional_string_with

/-- X61 `ElicitationSchemaBuilder::required_integer` (top-level → Specs): for `min ≤ max`, `n`
required, an integer with both bounds (`IntegerSchema::new().range(min, max)`, upstream lines
1646–1651, patched 1636–1641). **H20**.

Premises: caller code, (R), (B). Not covered: (I), (M), (A). The case `min > max` is
`ElicitationSchemaBuilder.required_integer_fail`. -/
theorem Theorems.elicitation_schema.ElicitationSchemaBuilder.required_integer {NameLike : Type}
    (nameInto : core.convert.Into NameLike String) (self : ElicitationSchemaBuilder)
    («name» : NameLike) (min max : I64) (n : String) (h_name_into : nameInto.into «name» = ok n)
    (h_le : min.val ≤ max.val) (h_required_len : self.required.val.length < Usize.max) :
    rmcp.model.elicitation_schema.ElicitationSchemaBuilder.required_integer nameInto self «name»
      min max ⦃ (result : ElicitationSchemaBuilder) =>
      result.required.val = self.required.val ++ [n] ∧ result.title = self.title ∧
        result.description = self.description ∧
        PropertyInserted self.properties n
          (.Integer { defaultIntegerSchema with minimum := some min, maximum := some max })
          result.properties ⦄ :=
  rmcp.model.elicitation_schema.ElicitationSchemaBuilder.required_integer_spec nameInto self «name»
    min max n h_name_into h_le h_required_len

/--
info: 'Theorems.elicitation_schema.ElicitationSchemaBuilder.required_integer' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.elicitation_schema.ElicitationSchemaBuilder.required_integer

/-- X61, failing case (top-level → Specs): for `min > max` the `assert!` of `range` panics before
the name is converted (upstream line 420). No premise. -/
theorem Theorems.elicitation_schema.ElicitationSchemaBuilder.required_integer_fail
    {NameLike : Type} (nameInto : core.convert.Into NameLike String)
    (self : ElicitationSchemaBuilder) («name» : NameLike) (min max : I64)
    (h_gt : max.val < min.val) :
    rmcp.model.elicitation_schema.ElicitationSchemaBuilder.required_integer nameInto self «name»
      min max = fail .assertionFailure :=
  rmcp.model.elicitation_schema.ElicitationSchemaBuilder.required_integer_fail nameInto self «name»
    min max h_gt

/--
info: 'Theorems.elicitation_schema.ElicitationSchemaBuilder.required_integer_fail' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.elicitation_schema.ElicitationSchemaBuilder.required_integer_fail

/-- X62 `ElicitationSchemaBuilder::optional_integer` (top-level → Specs): for `min ≤ max`,
property `n` an integer with both bounds, not required (upstream lines 1654–1659, patched
1644–1649).

Premises: caller code, (B). Not covered: (I), (M), (A). The case `min > max` is
`ElicitationSchemaBuilder.optional_integer_fail`. -/
theorem Theorems.elicitation_schema.ElicitationSchemaBuilder.optional_integer {NameLike : Type}
    (nameInto : core.convert.Into NameLike String) (self : ElicitationSchemaBuilder)
    («name» : NameLike) (min max : I64) (n : String) (h_name_into : nameInto.into «name» = ok n)
    (h_le : min.val ≤ max.val) :
    rmcp.model.elicitation_schema.ElicitationSchemaBuilder.optional_integer nameInto self «name»
      min max ⦃ (result : ElicitationSchemaBuilder) =>
      result.required = self.required ∧ result.title = self.title ∧
        result.description = self.description ∧
        PropertyInserted self.properties n
          (.Integer { defaultIntegerSchema with minimum := some min, maximum := some max })
          result.properties ⦄ :=
  rmcp.model.elicitation_schema.ElicitationSchemaBuilder.optional_integer_spec nameInto self «name»
    min max n h_name_into h_le

/--
info: 'Theorems.elicitation_schema.ElicitationSchemaBuilder.optional_integer' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.elicitation_schema.ElicitationSchemaBuilder.optional_integer

/-- X62, failing case (top-level → Specs): for `min > max` the `assert!` of `range` panics. No
premise. -/
theorem Theorems.elicitation_schema.ElicitationSchemaBuilder.optional_integer_fail
    {NameLike : Type} (nameInto : core.convert.Into NameLike String)
    (self : ElicitationSchemaBuilder) («name» : NameLike) (min max : I64)
    (h_gt : max.val < min.val) :
    rmcp.model.elicitation_schema.ElicitationSchemaBuilder.optional_integer nameInto self «name»
      min max = fail .assertionFailure :=
  rmcp.model.elicitation_schema.ElicitationSchemaBuilder.optional_integer_fail nameInto self «name»
    min max h_gt

/--
info: 'Theorems.elicitation_schema.ElicitationSchemaBuilder.optional_integer_fail' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.elicitation_schema.ElicitationSchemaBuilder.optional_integer_fail

/-- X63 `ElicitationSchemaBuilder::required_integer_with` (top-level → Specs): `n` required, with
`Integer(i)`, `i` the closure applied to the default integer schema (upstream lines 1662–1671,
patched 1652–1661). **H20**; the closure may set `minimum > maximum` (H21).

Premises: caller code, (R). Not covered: (I), (M), (A). -/
theorem Theorems.elicitation_schema.ElicitationSchemaBuilder.required_integer_with
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
        PropertyInserted self.properties n (.Integer i) result.properties ⦄ :=
  rmcp.model.elicitation_schema.ElicitationSchemaBuilder.required_integer_with_spec nameInto fOnce
    self «name» f n i h_name_into h_f h_required_len

/--
info: 'Theorems.elicitation_schema.ElicitationSchemaBuilder.required_integer_with' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.elicitation_schema.ElicitationSchemaBuilder.required_integer_with

/-- X64 `ElicitationSchemaBuilder::optional_integer_with` (top-level → Specs): property `n` set to
`Integer(i)`, not required (upstream lines 1674–1683, patched 1664–1673).

Premise: caller code. Not covered: (I), (M), (A). -/
theorem Theorems.elicitation_schema.ElicitationSchemaBuilder.optional_integer_with
    {NameLike F : Type} (nameInto : core.convert.Into NameLike String)
    (fOnce : core.ops.function.FnOnce F IntegerSchema IntegerSchema)
    (self : ElicitationSchemaBuilder) («name» : NameLike) (f : F) (n : String) (i : IntegerSchema)
    (h_name_into : nameInto.into «name» = ok n)
    (h_f : fOnce.call_once f defaultIntegerSchema = ok i) :
    rmcp.model.elicitation_schema.ElicitationSchemaBuilder.optional_integer_with nameInto fOnce
      self «name» f ⦃ (result : ElicitationSchemaBuilder) =>
      result.required = self.required ∧ result.title = self.title ∧
        result.description = self.description ∧
        PropertyInserted self.properties n (.Integer i) result.properties ⦄ :=
  rmcp.model.elicitation_schema.ElicitationSchemaBuilder.optional_integer_with_spec nameInto fOnce
    self «name» f n i h_name_into h_f

/--
info: 'Theorems.elicitation_schema.ElicitationSchemaBuilder.optional_integer_with' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.elicitation_schema.ElicitationSchemaBuilder.optional_integer_with

/-- X65 `ElicitationSchemaBuilder::required_bool` (top-level → Specs): `n` required, with the
default boolean schema (upstream lines 1688–1693, patched 1678–1683). **H20**.

Premises: caller code, (R). Not covered: (I), (M), (A). -/
theorem Theorems.elicitation_schema.ElicitationSchemaBuilder.required_bool {NameLike : Type}
    (nameInto : core.convert.Into NameLike String) (self : ElicitationSchemaBuilder)
    («name» : NameLike) (n : String) (h_name_into : nameInto.into «name» = ok n)
    (h_required_len : self.required.val.length < Usize.max) :
    rmcp.model.elicitation_schema.ElicitationSchemaBuilder.required_bool nameInto self «name» ⦃
      (result : ElicitationSchemaBuilder) =>
      result.required.val = self.required.val ++ [n] ∧ result.title = self.title ∧
        result.description = self.description ∧
        PropertyInserted self.properties n (.Boolean defaultBooleanSchema) result.properties ⦄ :=
  rmcp.model.elicitation_schema.ElicitationSchemaBuilder.required_bool_spec nameInto self «name» n
    h_name_into h_required_len

/--
info: 'Theorems.elicitation_schema.ElicitationSchemaBuilder.required_bool' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.elicitation_schema.ElicitationSchemaBuilder.required_bool

/-- X66 `ElicitationSchemaBuilder::optional_bool` (top-level → Specs): property `n` a boolean
with default `default`, not required (upstream lines 1696–1701, patched 1686–1691).

Premise: caller code. Not covered: (I), (M), (A). -/
theorem Theorems.elicitation_schema.ElicitationSchemaBuilder.optional_bool {NameLike : Type}
    (nameInto : core.convert.Into NameLike String) (self : ElicitationSchemaBuilder)
    («name» : NameLike) (default : Bool) (n : String)
    (h_name_into : nameInto.into «name» = ok n) :
    rmcp.model.elicitation_schema.ElicitationSchemaBuilder.optional_bool nameInto self «name»
      default ⦃ (result : ElicitationSchemaBuilder) =>
      result.required = self.required ∧ result.title = self.title ∧
        result.description = self.description ∧
        PropertyInserted self.properties n
          (.Boolean { defaultBooleanSchema with default := some default }) result.properties ⦄ :=
  rmcp.model.elicitation_schema.ElicitationSchemaBuilder.optional_bool_spec nameInto self «name»
    default n h_name_into

/--
info: 'Theorems.elicitation_schema.ElicitationSchemaBuilder.optional_bool' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.elicitation_schema.ElicitationSchemaBuilder.optional_bool

/-- X67 `ElicitationSchemaBuilder::required_bool_with` (top-level → Specs): `n` required, with
`Boolean(b)`, `b` the closure applied to the default boolean schema (upstream lines 1704–1713,
patched 1694–1703). **H20**.

Premises: caller code, (R). Not covered: (I), (M), (A). -/
theorem Theorems.elicitation_schema.ElicitationSchemaBuilder.required_bool_with
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
        PropertyInserted self.properties n (.Boolean b) result.properties ⦄ :=
  rmcp.model.elicitation_schema.ElicitationSchemaBuilder.required_bool_with_spec nameInto fOnce self
    «name» f n b h_name_into h_f h_required_len

/--
info: 'Theorems.elicitation_schema.ElicitationSchemaBuilder.required_bool_with' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.elicitation_schema.ElicitationSchemaBuilder.required_bool_with

/-- X68 `ElicitationSchemaBuilder::optional_bool_with` (top-level → Specs): property `n` set to
`Boolean(b)`, not required (upstream lines 1716–1725, patched 1706–1715).

Premise: caller code. Not covered: (I), (M), (A). -/
theorem Theorems.elicitation_schema.ElicitationSchemaBuilder.optional_bool_with
    {NameLike F : Type} (nameInto : core.convert.Into NameLike String)
    (fOnce : core.ops.function.FnOnce F BooleanSchema BooleanSchema)
    (self : ElicitationSchemaBuilder) («name» : NameLike) (f : F) (n : String) (b : BooleanSchema)
    (h_name_into : nameInto.into «name» = ok n)
    (h_f : fOnce.call_once f defaultBooleanSchema = ok b) :
    rmcp.model.elicitation_schema.ElicitationSchemaBuilder.optional_bool_with nameInto fOnce
      self «name» f ⦃ (result : ElicitationSchemaBuilder) =>
      result.required = self.required ∧ result.title = self.title ∧
        result.description = self.description ∧
        PropertyInserted self.properties n (.Boolean b) result.properties ⦄ :=
  rmcp.model.elicitation_schema.ElicitationSchemaBuilder.optional_bool_with_spec nameInto fOnce self
    «name» f n b h_name_into h_f

/--
info: 'Theorems.elicitation_schema.ElicitationSchemaBuilder.optional_bool_with' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.elicitation_schema.ElicitationSchemaBuilder.optional_bool_with

/-- X69 `ElicitationSchemaBuilder::required_enum_schema` (top-level → Specs): `n` required, with
`Enum(enum_schema)` stored unchanged (upstream lines 1730–1732, patched 1720–1722). **H20**.
Recorded behaviour (not a bug, decision XS4): the enum schema is stored unchecked
(`ConsistentEnumSchema` is not required).

Premises: caller code, (R). Not covered: (I), (M), (A). -/
theorem Theorems.elicitation_schema.ElicitationSchemaBuilder.required_enum_schema
    {NameLike : Type} (nameInto : core.convert.Into NameLike String)
    (self : ElicitationSchemaBuilder) («name» : NameLike) (enum_schema : EnumSchema) (n : String)
    (h_name_into : nameInto.into «name» = ok n)
    (h_required_len : self.required.val.length < Usize.max) :
    rmcp.model.elicitation_schema.ElicitationSchemaBuilder.required_enum_schema nameInto self
      «name» enum_schema ⦃ (result : ElicitationSchemaBuilder) =>
      result.required.val = self.required.val ++ [n] ∧ result.title = self.title ∧
        result.description = self.description ∧
        PropertyInserted self.properties n (.Enum enum_schema) result.properties ⦄ :=
  rmcp.model.elicitation_schema.ElicitationSchemaBuilder.required_enum_schema_spec nameInto self
    «name» enum_schema n h_name_into h_required_len

/--
info: 'Theorems.elicitation_schema.ElicitationSchemaBuilder.required_enum_schema' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.elicitation_schema.ElicitationSchemaBuilder.required_enum_schema

/-- X70 `ElicitationSchemaBuilder::optional_enum_schema` (top-level → Specs): property `n` set to
`Enum(enum_schema)`, not required (upstream lines 1735–1737, patched 1725–1727). Recorded
behaviour (not a bug, decision XS4): the enum schema is stored unchecked (`ConsistentEnumSchema`
is not required).

Premise: caller code. Not covered: (I), (M), (A). -/
theorem Theorems.elicitation_schema.ElicitationSchemaBuilder.optional_enum_schema
    {NameLike : Type} (nameInto : core.convert.Into NameLike String)
    (self : ElicitationSchemaBuilder) («name» : NameLike) (enum_schema : EnumSchema) (n : String)
    (h_name_into : nameInto.into «name» = ok n) :
    rmcp.model.elicitation_schema.ElicitationSchemaBuilder.optional_enum_schema nameInto self
      «name» enum_schema ⦃ (result : ElicitationSchemaBuilder) =>
      result.required = self.required ∧ result.title = self.title ∧
        result.description = self.description ∧
        PropertyInserted self.properties n (.Enum enum_schema) result.properties ⦄ :=
  rmcp.model.elicitation_schema.ElicitationSchemaBuilder.optional_enum_schema_spec nameInto self
    «name» enum_schema n h_name_into

/--
info: 'Theorems.elicitation_schema.ElicitationSchemaBuilder.optional_enum_schema' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.elicitation_schema.ElicitationSchemaBuilder.optional_enum_schema

/-- X71 `ElicitationSchemaBuilder::mark_required` (top-level → Specs): `n = name.into()`
appended to the required list, everything else unchanged (upstream lines 1740–1743, patched
1730–1733). **H20** (decision XS5): `n` need not be a property ("Mark an existing property" is
not checked here) and is appended even if already required. A name that is not a property breaks
(Q) until a property of that name is added (the check is made by `build`, upstream lines
1766–1772); if it is still missing when `build` runs, X74 returns `Err` and X75
`build_unchecked` panics (`build_unchecked_fail`).

Premises: caller code, (R). Not covered: (I), (A). The case `self.required.val.length =
Usize.max` is `ElicitationSchemaBuilder.mark_required_fail`. -/
theorem Theorems.elicitation_schema.ElicitationSchemaBuilder.mark_required {NameLike : Type}
    (nameInto : core.convert.Into NameLike String) (self : ElicitationSchemaBuilder)
    («name» : NameLike) (n : String) (h_name_into : nameInto.into «name» = ok n)
    (h_required_len : self.required.val.length < Usize.max) :
    rmcp.model.elicitation_schema.ElicitationSchemaBuilder.mark_required nameInto self «name» ⦃
      (result : ElicitationSchemaBuilder) =>
      result.required.val = self.required.val ++ [n] ∧ result.properties = self.properties ∧
        result.title = self.title ∧ result.description = self.description ⦄ :=
  rmcp.model.elicitation_schema.ElicitationSchemaBuilder.mark_required_spec nameInto self «name» n
    h_name_into h_required_len

/--
info: 'Theorems.elicitation_schema.ElicitationSchemaBuilder.mark_required' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.elicitation_schema.ElicitationSchemaBuilder.mark_required

/-- X71, failing case (top-level → Specs): a required list of `Usize.max` names makes the Aeneas
model of `Vec::push` fail (no Rust `Vec<String>` is that long).

Premise: caller code. -/
theorem Theorems.elicitation_schema.ElicitationSchemaBuilder.mark_required_fail
    {NameLike : Type} (nameInto : core.convert.Into NameLike String)
    (self : ElicitationSchemaBuilder) («name» : NameLike) (n : String)
    (h_name_into : nameInto.into «name» = ok n) (h_full : self.required.val.length = Usize.max) :
    rmcp.model.elicitation_schema.ElicitationSchemaBuilder.mark_required nameInto self «name» =
      fail .maximumSizeExceeded :=
  rmcp.model.elicitation_schema.ElicitationSchemaBuilder.mark_required_fail nameInto self «name» n
    h_name_into h_full

/--
info: 'Theorems.elicitation_schema.ElicitationSchemaBuilder.mark_required_fail' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.elicitation_schema.ElicitationSchemaBuilder.mark_required_fail

/-- X72 `ElicitationSchemaBuilder::title` (top-level → Specs): sets the title to
`c = title.into()` (upstream lines 1746–1749, patched 1736–1739).

Premise: caller code. Not covered: (I). -/
theorem Theorems.elicitation_schema.ElicitationSchemaBuilder.title {TitleLike : Type}
    (titleInto : core.convert.Into TitleLike (rmcp.alloc.borrow.Cow Str String))
    (self : ElicitationSchemaBuilder) (title : TitleLike) (c : rmcp.alloc.borrow.Cow Str String)
    (h_title_into : titleInto.into title = ok c) :
    rmcp.model.elicitation_schema.ElicitationSchemaBuilder.impl.title titleInto self title ⦃
      (result : ElicitationSchemaBuilder) =>
      result = { self with title := some c } ⦄ :=
  rmcp.model.elicitation_schema.ElicitationSchemaBuilder.impl.title_spec titleInto self title c
    h_title_into

/--
info: 'Theorems.elicitation_schema.ElicitationSchemaBuilder.title' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.elicitation_schema.ElicitationSchemaBuilder.title

/-- X73 `ElicitationSchemaBuilder::description` (top-level → Specs): sets the description to
`c = description.into()` (upstream lines 1752–1755, patched 1742–1745).

Premise: caller code. Not covered: (I). -/
theorem Theorems.elicitation_schema.ElicitationSchemaBuilder.description {DescriptionLike : Type}
    (descriptionInto : core.convert.Into DescriptionLike (rmcp.alloc.borrow.Cow Str String))
    (self : ElicitationSchemaBuilder) (description : DescriptionLike)
    (c : rmcp.alloc.borrow.Cow Str String)
    (h_description_into : descriptionInto.into description = ok c) :
    rmcp.model.elicitation_schema.ElicitationSchemaBuilder.impl.description descriptionInto self
      description ⦃ (result : ElicitationSchemaBuilder) =>
      result = { self with description := some c } ⦄ :=
  rmcp.model.elicitation_schema.ElicitationSchemaBuilder.impl.description_spec descriptionInto self
    description c h_description_into

/--
info: 'Theorems.elicitation_schema.ElicitationSchemaBuilder.description' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.elicitation_schema.ElicitationSchemaBuilder.description

/-- X75 `ElicitationSchemaBuilder::build_unchecked` (top-level → Specs; linkage patch-08, as it
calls X74): when every required name is a property, the schema of X74 (upstream lines 1795–1797,
patched 1788–1790). **H19**, **H20** as X74. Builders a caller holds can violate (Q) (pub fields,
X71), and then this function panics: see `build_unchecked_fail`.

Premises: (L), (Q). Not covered: (A). The other inputs are
`ElicitationSchemaBuilder.build_unchecked_fail`. -/
theorem Theorems.elicitation_schema.ElicitationSchemaBuilder.build_unchecked
    (self : ElicitationSchemaBuilder) (h_fit : PropertiesFit self.properties)
    (h_required : RequiredPropertiesExist self) :
    rmcp.model.elicitation_schema.ElicitationSchemaBuilder.build_unchecked self ⦃
      (result : ElicitationSchema) =>
      result.schema = none ∧ result.title = self.title ∧ result.properties = self.properties ∧
        result.property_order.map (·.val) = some (propertyNames self.properties) ∧
        result.required = (if self.required.val = [] then none else some self.required) ∧
        result.description = self.description ⦄ :=
  rmcp.model.elicitation_schema.ElicitationSchemaBuilder.build_unchecked_spec self h_fit h_required

/--
info: 'Theorems.elicitation_schema.ElicitationSchemaBuilder.build_unchecked' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.elicitation_schema.ElicitationSchemaBuilder.build_unchecked

/-- X75, failing case (top-level → Specs): `build_unchecked` panics exactly when a required name
is not a property when it runs (`expect`, upstream line 1796; message not modelled, (D)), as
after X71 `mark_required` of a name for which no property was added afterwards (H20), or a direct
write to the `pub` field `required`, or, in the model, when the key list does not fit (L). -/
theorem Theorems.elicitation_schema.ElicitationSchemaBuilder.build_unchecked_fail
    (self : ElicitationSchemaBuilder)
    (h_bad : ¬ (PropertiesFit self.properties ∧ RequiredPropertiesExist self)) :
    rmcp.model.elicitation_schema.ElicitationSchemaBuilder.build_unchecked self = fail .panic :=
  rmcp.model.elicitation_schema.ElicitationSchemaBuilder.build_unchecked_fail self h_bad

/--
info: 'Theorems.elicitation_schema.ElicitationSchemaBuilder.build_unchecked_fail' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.elicitation_schema.ElicitationSchemaBuilder.build_unchecked_fail

/-! ## Compositions: enum builders -/

/-- Composition X39: the builder of `EnumSchema::builder` meets the enum builder invariant (it is
untitled and has no default). No premise. -/
theorem Theorems.elicitation_schema.EnumSchema.builder_valid (values : alloc.vec.Vec String) :
    rmcp.model.elicitation_schema.EnumSchema.builder values ⦃
      (result : EnumSchemaBuilder SingleSelect) =>
      ValidEnumSchemaBuilder result ⦄ :=
  rmcp.model.elicitation_schema.EnumSchema.builder_valid values

/--
info: 'Theorems.elicitation_schema.EnumSchema.builder_valid' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.elicitation_schema.EnumSchema.builder_valid

/-- Composition X26: `title` keeps both enum builder invariants.

Premise: caller code. Not covered: (I). -/
theorem Theorems.elicitation_schema.EnumSchemaBuilder.title_valid {T ValueLike : Type}
    (valueInto : core.convert.Into ValueLike (rmcp.alloc.borrow.Cow Str String))
    (self : EnumSchemaBuilder T) (value : ValueLike) (c : rmcp.alloc.borrow.Cow Str String)
    (h_value_into : valueInto.into value = ok c) :
    rmcp.model.elicitation_schema.EnumSchemaBuilder.impl.title valueInto self value ⦃
      (result : EnumSchemaBuilder T) =>
      (ValidEnumSchemaBuilder self → ValidEnumSchemaBuilder result) ∧
        (ValidMultiSelectBuilder self → ValidMultiSelectBuilder result) ⦄ :=
  rmcp.model.elicitation_schema.EnumSchemaBuilder.title_valid valueInto self value c h_value_into

/--
info: 'Theorems.elicitation_schema.EnumSchemaBuilder.title_valid' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.elicitation_schema.EnumSchemaBuilder.title_valid

/-- Composition X27: `description` keeps both enum builder invariants.

Premise: caller code. Not covered: (I). -/
theorem Theorems.elicitation_schema.EnumSchemaBuilder.description_valid {T ValueLike : Type}
    (valueInto : core.convert.Into ValueLike (rmcp.alloc.borrow.Cow Str String))
    (self : EnumSchemaBuilder T) (value : ValueLike) (c : rmcp.alloc.borrow.Cow Str String)
    (h_value_into : valueInto.into value = ok c) :
    rmcp.model.elicitation_schema.EnumSchemaBuilder.impl.description valueInto self value ⦃
      (result : EnumSchemaBuilder T) =>
      (ValidEnumSchemaBuilder self → ValidEnumSchemaBuilder result) ∧
        (ValidMultiSelectBuilder self → ValidMultiSelectBuilder result) ⦄ :=
  rmcp.model.elicitation_schema.EnumSchemaBuilder.description_valid valueInto self value c
    h_value_into

/--
info: 'Theorems.elicitation_schema.EnumSchemaBuilder.description_valid' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.elicitation_schema.EnumSchemaBuilder.description_valid

/-- Composition X28: `untitled` keeps both enum builder invariants. No premise. -/
theorem Theorems.elicitation_schema.EnumSchemaBuilder.untitled_valid {T : Type}
    (self : EnumSchemaBuilder T) :
    rmcp.model.elicitation_schema.EnumSchemaBuilder.untitled self ⦃
      (result : EnumSchemaBuilder T) =>
      (ValidEnumSchemaBuilder self → ValidEnumSchemaBuilder result) ∧
        (ValidMultiSelectBuilder self → ValidMultiSelectBuilder result) ⦄ :=
  rmcp.model.elicitation_schema.EnumSchemaBuilder.untitled_valid self

/--
info: 'Theorems.elicitation_schema.EnumSchemaBuilder.untitled_valid' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.elicitation_schema.EnumSchemaBuilder.untitled_valid

/-- Composition X29: an accepted `enum_titles` keeps both enum builder invariants (its check makes
the titled builder have as many titles as values). No premise. -/
theorem Theorems.elicitation_schema.EnumSchemaBuilder.enum_titles_valid {T : Type}
    (self : EnumSchemaBuilder T) (titles : alloc.vec.Vec String) :
    rmcp.model.elicitation_schema.EnumSchemaBuilder.impl.enum_titles self titles ⦃
      (result : core.result.Result (EnumSchemaBuilder T) String) =>
      ∀ b, result = .Ok b →
        (ValidEnumSchemaBuilder self → ValidEnumSchemaBuilder b) ∧
          (ValidMultiSelectBuilder self → ValidMultiSelectBuilder b) ⦄ :=
  rmcp.model.elicitation_schema.EnumSchemaBuilder.enum_titles_valid self titles

/--
info: 'Theorems.elicitation_schema.EnumSchemaBuilder.enum_titles_valid' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.elicitation_schema.EnumSchemaBuilder.enum_titles_valid

/-- Composition X31: `multiselect` turns a valid builder into a valid multi-select builder (no
item bounds, no default).

Premise: (V). -/
theorem Theorems.elicitation_schema.EnumSchemaBuilderSingleSelect.multiselect_valid
    (self : EnumSchemaBuilder SingleSelect) (h_valid : ValidEnumSchemaBuilder self) :
    rmcp.model.elicitation_schema.EnumSchemaBuilderSingleSelect.multiselect self ⦃
      (result : EnumSchemaBuilder MultiSelect) =>
      ValidMultiSelectBuilder result ⦄ :=
  rmcp.model.elicitation_schema.EnumSchemaBuilderSingleSelect.multiselect_valid self h_valid

/--
info: 'Theorems.elicitation_schema.EnumSchemaBuilderSingleSelect.multiselect_valid' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.elicitation_schema.EnumSchemaBuilderSingleSelect.multiselect_valid

/-- Composition X32: an accepted single-select default keeps the enum builder invariant.

Premises: caller code, (V). Not covered: (I). -/
theorem Theorems.elicitation_schema.EnumSchemaBuilderSingleSelect.with_default_valid
    {DefaultLike : Type} (defaultInto : core.convert.Into DefaultLike String)
    (self : EnumSchemaBuilder SingleSelect) (default_value : DefaultLike) (v : String)
    (h_default_into : defaultInto.into default_value = ok v)
    (h_valid : ValidEnumSchemaBuilder self) :
    rmcp.model.elicitation_schema.EnumSchemaBuilderSingleSelect.with_default defaultInto self
      default_value ⦃ (result : core.result.Result (EnumSchemaBuilder SingleSelect) String) =>
      ∀ b, result = .Ok b → ValidEnumSchemaBuilder b ⦄ :=
  rmcp.model.elicitation_schema.EnumSchemaBuilderSingleSelect.with_default_valid defaultInto self
    default_value v h_default_into h_valid

/--
info: 'Theorems.elicitation_schema.EnumSchemaBuilderSingleSelect.with_default_valid' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.elicitation_schema.EnumSchemaBuilderSingleSelect.with_default_valid

/-- Composition X33: a valid single-select builder builds a consistent enum schema (its default,
if any, is an enum value) and, if titled, the options carry exactly the values and the titles,
in order (titles match values).

Premise: (V). Not covered: (A), (C). -/
theorem Theorems.elicitation_schema.EnumSchemaBuilderSingleSelect.build_consistent
    (self : EnumSchemaBuilder SingleSelect) (h_valid : ValidEnumSchemaBuilder self) :
    rmcp.model.elicitation_schema.EnumSchemaBuilderSingleSelect.build self ⦃
      (result : EnumSchema) =>
      ConsistentEnumSchema result ∧
        ∀ t, result = .Single (.Titled t) →
          t.one_of.val.map (·.const_) = self.enum_values.val ∧
            t.one_of.val.map (·.title) = self.enum_titles.val ⦄ :=
  rmcp.model.elicitation_schema.EnumSchemaBuilderSingleSelect.build_consistent self h_valid

/--
info: 'Theorems.elicitation_schema.EnumSchemaBuilderSingleSelect.build_consistent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.elicitation_schema.EnumSchemaBuilderSingleSelect.build_consistent

/-- Composition X34: `single_select` turns a builder meeting the enum builder invariant into one
meeting it again (the default is cleared).

Premise: (V). -/
theorem Theorems.elicitation_schema.EnumSchemaBuilderMultiSelect.single_select_valid
    (self : EnumSchemaBuilder MultiSelect) (h_valid : ValidEnumSchemaBuilder self) :
    rmcp.model.elicitation_schema.EnumSchemaBuilderMultiSelect.single_select self ⦃
      (result : EnumSchemaBuilder SingleSelect) =>
      ValidEnumSchemaBuilder result ⦄ :=
  rmcp.model.elicitation_schema.EnumSchemaBuilderMultiSelect.single_select_valid self h_valid

/--
info: 'Theorems.elicitation_schema.EnumSchemaBuilderMultiSelect.single_select_valid' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.elicitation_schema.EnumSchemaBuilderMultiSelect.single_select_valid

/-- Composition X35: an accepted multi-select default keeps the multi-select invariant.

Premise: (V). -/
theorem Theorems.elicitation_schema.EnumSchemaBuilderMultiSelect.with_default_valid
    (self : EnumSchemaBuilder MultiSelect) (default_values : alloc.vec.Vec String)
    (h_valid : ValidMultiSelectBuilder self) :
    rmcp.model.elicitation_schema.EnumSchemaBuilderMultiSelect.with_default self default_values ⦃
      (result : core.result.Result (EnumSchemaBuilder MultiSelect) String) =>
      ∀ b, result = .Ok b → ValidMultiSelectBuilder b ⦄ :=
  rmcp.model.elicitation_schema.EnumSchemaBuilderMultiSelect.with_default_valid self default_values
    h_valid

/--
info: 'Theorems.elicitation_schema.EnumSchemaBuilderMultiSelect.with_default_valid' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.elicitation_schema.EnumSchemaBuilderMultiSelect.with_default_valid

/-- Composition X36: an accepted `min_items` keeps the multi-select invariant (minimum at most
the maximum; a non-empty default has at least the minimum).

Premise: (V). -/
theorem Theorems.elicitation_schema.EnumSchemaBuilderMultiSelect.min_items_valid
    (self : EnumSchemaBuilder MultiSelect) (value : U64) (h_valid : ValidMultiSelectBuilder self) :
    rmcp.model.elicitation_schema.EnumSchemaBuilderMultiSelect.min_items self value ⦃
      (result : core.result.Result (EnumSchemaBuilder MultiSelect) String) =>
      ∀ b, result = .Ok b → ValidMultiSelectBuilder b ⦄ :=
  rmcp.model.elicitation_schema.EnumSchemaBuilderMultiSelect.min_items_valid self value h_valid

/--
info: 'Theorems.elicitation_schema.EnumSchemaBuilderMultiSelect.min_items_valid' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.elicitation_schema.EnumSchemaBuilderMultiSelect.min_items_valid

/-- Composition X37: an accepted `max_items` keeps the multi-select invariant.

Premise: (V). -/
theorem Theorems.elicitation_schema.EnumSchemaBuilderMultiSelect.max_items_valid
    (self : EnumSchemaBuilder MultiSelect) (value : U64) (h_valid : ValidMultiSelectBuilder self) :
    rmcp.model.elicitation_schema.EnumSchemaBuilderMultiSelect.max_items self value ⦃
      (result : core.result.Result (EnumSchemaBuilder MultiSelect) String) =>
      ∀ b, result = .Ok b → ValidMultiSelectBuilder b ⦄ :=
  rmcp.model.elicitation_schema.EnumSchemaBuilderMultiSelect.max_items_valid self value h_valid

/--
info: 'Theorems.elicitation_schema.EnumSchemaBuilderMultiSelect.max_items_valid' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.elicitation_schema.EnumSchemaBuilderMultiSelect.max_items_valid

/-- Composition X38: a valid multi-select builder builds a consistent enum schema (minimum at
most maximum, a default that is non-empty, made of enum values and within the bounds) and, if
titled, the options carry exactly the values and the titles, in order. **H22**: neither a minimum
above the number of values nor duplicate defaults are excluded.

Premise: (V). Not covered: (A), (C). -/
theorem Theorems.elicitation_schema.EnumSchemaBuilderMultiSelect.build_consistent
    (self : EnumSchemaBuilder MultiSelect) (h_valid : ValidMultiSelectBuilder self) :
    rmcp.model.elicitation_schema.EnumSchemaBuilderMultiSelect.build self ⦃
      (result : EnumSchema) =>
      ConsistentEnumSchema result ∧
        ∀ t, result = .Multi (.Titled t) →
          t.items.any_of.val.map (·.const_) = self.enum_values.val ∧
            t.items.any_of.val.map (·.title) = self.enum_titles.val ⦄ :=
  rmcp.model.elicitation_schema.EnumSchemaBuilderMultiSelect.build_consistent self h_valid

/--
info: 'Theorems.elicitation_schema.EnumSchemaBuilderMultiSelect.build_consistent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.elicitation_schema.EnumSchemaBuilderMultiSelect.build_consistent

/-! ## Compositions: elicitation schemas -/

/-- Composition X40 (top-level → Specs): `ElicitationSchema::new` gives a consistent schema (no
required list; the property order is the property names).

Premise: (L). Not covered: (A). -/
theorem Theorems.elicitation_schema.ElicitationSchema.new_consistent
    (properties : alloc.collections.btree.map.BTreeMap String PrimitiveSchemaDefinition
      alloc.alloc.Global)
    (h_fit : PropertiesFit properties) :
    rmcp.model.elicitation_schema.ElicitationSchema.new properties ⦃
      (result : ElicitationSchema) =>
      ConsistentElicitationSchema result ⦄ :=
  rmcp.model.elicitation_schema.ElicitationSchema.new_consistent properties h_fit

/--
info: 'Theorems.elicitation_schema.ElicitationSchema.new_consistent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.elicitation_schema.ElicitationSchema.new_consistent

/-- Composition X75 (top-level → Specs): the schema `build_unchecked` returns is consistent (its
map is the builder's). **H19**, **H20**.

Premises: (L), (Q). Not covered: (A). -/
theorem Theorems.elicitation_schema.ElicitationSchemaBuilder.build_unchecked_consistent
    (self : ElicitationSchemaBuilder) (h_fit : PropertiesFit self.properties)
    (h_required : RequiredPropertiesExist self) :
    rmcp.model.elicitation_schema.ElicitationSchemaBuilder.build_unchecked self ⦃
      (result : ElicitationSchema) =>
      ConsistentElicitationSchema result ⦄ :=
  rmcp.model.elicitation_schema.ElicitationSchemaBuilder.build_unchecked_consistent self h_fit
    h_required

/--
info: 'Theorems.elicitation_schema.ElicitationSchemaBuilder.build_unchecked_consistent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.elicitation_schema.ElicitationSchemaBuilder.build_unchecked_consistent

/-- Composition X45+X75 (top-level → Specs), **H19**: `build_unchecked` on
`ElicitationSchema::builder()` returns (does not panic) a schema with no property and no required
list. No premise. -/
theorem Theorems.elicitation_schema.ElicitationSchema.builder_build_unchecked_empty :
    (do
      let b ← rmcp.model.elicitation_schema.ElicitationSchema.builder
      rmcp.model.elicitation_schema.ElicitationSchemaBuilder.build_unchecked b) ⦃
      (result : ElicitationSchema) =>
      result.properties.entries = [] ∧ result.required = none ⦄ :=
  rmcp.model.elicitation_schema.ElicitationSchema.builder_build_unchecked_empty

/--
info: 'Theorems.elicitation_schema.ElicitationSchema.builder_build_unchecked_empty' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Theorems.elicitation_schema.ElicitationSchema.builder_build_unchecked_empty
