/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
module
public import Rmcp.Funs
public import Defs.ElicitationSchema
public import Proofs.External.ElicitationSchema
public import Proofs.External.String
public import Proofs.External.Std
public import Proofs.External.WP
public import Proofs.Model.RequestStateWire.Common
public import Proofs.Model.Skill.Verify
public import Proofs.Transport.MetadataResolver.Common

@[expose] public section

/-!
# Helpers for the spec theorems of `elicitation_schema.rs` (X01–X75)

The map invariant `KeysSorted` as `SortedByKey` and the laws of `PropertyInserted` for the
`BTreeMap::insert` model (from the `String`-order and lookup lemmas of `Proofs.Model.Skill`), and
equations for the translated helpers that several targets of
`crates/rmcp/src/model/elicitation_schema.rs` share: the `all` checks of `build` (X74) and of the
multi-select `with_default` (X35) with their membership closures, `ElicitationSchemaBuilder::new`
(X46) as the empty builder, the patch-only `const_titles` (translation patch 08, hunk E2) as
`constTitles` through its loop, and the first failing checks of the multi-select setters
(`multiSelectDefaultError?`, `minItemsError?`, `maxItemsError?`) as conditions.

Source: "crates/rmcp/src/model/elicitation_schema.rs", in the patched copy (translation patches
01–08 on upstream `7caec76`).
-/

open Aeneas Aeneas.Std Result
open Defs (utf8Bytes)
open Defs.ElicitationSchema
open rmcp.model.elicitation_schema (StringSchema StringFormat IntegerSchema BooleanSchema
  ConstTitle EnumSchema EnumSchemaBuilder SingleSelect MultiSelect PrimitiveSchemaDefinition
  ElicitationSchema ElicitationSchemaBuilder)

namespace Proofs.Model.ElicitationSchema

open ExtModel Proofs.External.ElicitationSchema

/-- `KeysSorted` is the `SortedByKey` of the entries. -/
theorem keysSorted_iff_sortedByKey {V A : Type}
    (m : alloc.collections.btree.map.BTreeMap String V A) :
    KeysSorted m ↔ Proofs.External.Skill.SortedByKey m.entries := by
  unfold KeysSorted Proofs.External.Skill.SortedByKey
  simp only [Proofs.Model.Skill.bytesLt_eq_true_iff_lt, Proofs.External.Utf8.utf8Bytes_eq_utf8]

/-- The entry list `mapInsert k v old.entries` meets `PropertyInserted old k v`. -/
theorem propertyInserted_mapInsert
    (old : alloc.collections.btree.map.BTreeMap String PrimitiveSchemaDefinition
      alloc.alloc.Global) (k : String) (v : PrimitiveSchemaDefinition) :
    PropertyInserted old k v { entries := (mapInsert k v old.entries).2 } := by
  refine ⟨fun k' => ?_, fun h => ?_⟩
  · exact Proofs.Model.Skill.map_snd_find?_mapInsert k v k' old.entries
  · rw [keysSorted_iff_sortedByKey] at h ⊢
    exact Proofs.External.Skill.sortedByKey_mapInsert k v _ h

open rmcp.model.elicitation_schema.ElicitationSchemaBuilder.build.closure in
/-- The check of `build`: `all` over the required names with the membership closure. -/
theorem build_all_eq (required names : alloc.vec.Vec String) :
    ∃ it, core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.all
        Insts.CoreOpsFunctionFnMutTupleShared0StringBool
        ⟨alloc.vec.Vec.deref required, 0⟩ names =
      ok (decide (∀ r ∈ required.val, r ∈ names.val), it) := by
  have h := core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.all_spec
    Insts.CoreOpsFunctionFnMutTupleShared0StringBool
    (fun x => decide (x ∈ names.val)) ⟨alloc.vec.Vec.deref required, 0⟩ names
    (fun x => by
      simp only [Insts.CoreOpsFunctionFnMutTupleShared0StringBool.call_mut,
        Proofs.Transport.MetadataResolver.contains_string, bind_ok, alloc.vec.Vec.deref,
        Slice.from_val])
  obtain ⟨⟨b, it⟩, hr, hb⟩ := Proofs.External.WP.exists_ok_of_spec h
  refine ⟨it, ?_⟩
  rw [hr]
  dsimp only at hb
  subst hb
  simp only [alloc.vec.Vec.deref, Slice.from_val, List.drop_zero]
  congr 2
  rw [Bool.eq_iff_iff, List.all_eq_true, decide_eq_true_iff]
  simp

/-- `ElicitationSchemaBuilder::new` is the empty builder, as an equation. -/
theorem elicitationSchemaBuilder_new_eq :
    rmcp.model.elicitation_schema.ElicitationSchemaBuilder.new =
      ok emptyElicitationSchemaBuilder := by
  simp [rmcp.model.elicitation_schema.ElicitationSchemaBuilder.new,
    rmcp.model.elicitation_schema.ElicitationSchemaBuilder.Insts.CoreDefaultDefault.default,
    alloc.collections.btree.map.BTreeMapKVGlobal.Insts.CoreDefaultDefault.default,
    alloc.vec.Vec.Insts.CoreDefaultDefault.default,
    core.option.Option.Insts.CoreDefaultDefault.default, emptyElicitationSchemaBuilder]

open rmcp.model.elicitation_schema.EnumSchemaBuilderMultiSelect.with_default.closure in
/-- The check of `with_default`: `all` over the defaults with the membership closure. -/
theorem withDefault_all_eq (ds values : alloc.vec.Vec String) :
    ∃ it, core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.all
        Insts.CoreOpsFunctionFnMutTupleShared0StringBool
        ⟨alloc.vec.Vec.deref ds, 0⟩ values =
      ok (ds.val.all (fun d => decide (d ∈ values.val)), it) := by
  have h := core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.all_spec
    Insts.CoreOpsFunctionFnMutTupleShared0StringBool
    (fun x => decide (x ∈ values.val)) ⟨alloc.vec.Vec.deref ds, 0⟩ values
    (fun x => by
      simp only [Insts.CoreOpsFunctionFnMutTupleShared0StringBool.call_mut,
        Proofs.Transport.MetadataResolver.contains_string, bind_ok, alloc.vec.Vec.deref,
        Slice.from_val])
  obtain ⟨⟨b, it⟩, hr, hb⟩ := Proofs.External.WP.exists_ok_of_spec h
  refine ⟨it, ?_⟩
  rw [hr]
  dsimp only at hb
  subst hb
  simp only [alloc.vec.Vec.deref, Slice.from_val, List.drop_zero]

/-- The loop of `const_titles`: from the output `out`, it appends the titled options of the
remaining titles `ts` and values (`constTitles`), as long as the output fits. -/
theorem const_titles_loop_eq :
    ∀ (ts : List String) (iter values : alloc.vec.into_iter.IntoIter String)
      (out : alloc.vec.Vec ConstTitle),
      iter.val = ts → out.val.length + values.val.length ≤ Usize.max →
      ∃ r, rmcp.model.elicitation_schema.const_titles_loop iter values out = ok r ∧
        r.val = out.val ++ constTitles ts values.val
  | [], iter, values, out, hiter, _ => by
    refine ⟨out, ?_, by simp [constTitles]⟩
    unfold rmcp.model.elicitation_schema.const_titles_loop
    apply loop_eq_of_done
    show rmcp.model.elicitation_schema.const_titles_loop.body iter values out = _
    simp [rmcp.model.elicitation_schema.const_titles_loop.body, next_eq_none iter hiter]
  | t :: ts, iter, values, out, hiter, hlen => by
    obtain ⟨iter1, hn1, hiter1⟩ := next_eq_some iter t ts hiter
    cases hv : values.val with
    | nil =>
      refine ⟨out, ?_, by simp [constTitles]⟩
      unfold rmcp.model.elicitation_schema.const_titles_loop
      apply loop_eq_of_done
      show rmcp.model.elicitation_schema.const_titles_loop.body iter values out = _
      simp [rmcp.model.elicitation_schema.const_titles_loop.body, hn1, next_eq_none values hv]
    | cons v vs =>
      obtain ⟨values1, hn2, hvalues1⟩ := next_eq_some values v vs hv
      have hpush : out.val.length < Usize.max := by
        rw [hv] at hlen; simp at hlen; omega
      obtain ⟨r, hr, hrv⟩ := const_titles_loop_eq ts iter1 values1
        (alloc.vec.Vec.from (out.val ++ [{ const_ := v, title := t }])
          (by rw [List.length_append]; exact hpush)) hiter1
        (by
          rw [hvalues1, alloc.vec.Vec.from_val, List.length_append]
          rw [hv] at hlen; simp at hlen; simp; omega)
      refine ⟨r, ?_, ?_⟩
      · unfold rmcp.model.elicitation_schema.const_titles_loop
        rw [loop_eq_of_cont _ _ (iter1, values1,
          alloc.vec.Vec.from (out.val ++ [{ const_ := v, title := t }])
          (by rw [List.length_append]; exact hpush))]
        · exact hr
        · show rmcp.model.elicitation_schema.const_titles_loop.body iter values out = _
          simp [rmcp.model.elicitation_schema.const_titles_loop.body, hn1, hn2,
            Proofs.External.WP.push_eq_ok _ _ hpush]
      · rw [hrv, alloc.vec.Vec.from_val, hvalues1]
        simp [constTitles]

/-- `const_titles` (patch 08) gives `constTitles` of the titles and the values. -/
theorem const_titles_eq (titles values : alloc.vec.Vec String) :
    ∃ r, rmcp.model.elicitation_schema.const_titles titles values = ok r ∧
      r.val = constTitles titles.val values.val := by
  obtain ⟨r, hr, hrv⟩ := const_titles_loop_eq titles.val titles values
    (alloc.vec.Vec.new ConstTitle) rfl (by simp [alloc.vec.Vec.new])
  refine ⟨r, ?_, by simpa [alloc.vec.Vec.new] using hrv⟩
  rw [rmcp.model.elicitation_schema.const_titles, Proofs.External.WP.bind_into_iter,
    Proofs.External.WP.bind_into_iter]
  exact hr

/-- For as many titles as values, the options of `constTitles` carry exactly the values and the
titles, in order. -/
theorem map_const_constTitles :
    ∀ (ts vs : List String), ts.length = vs.length →
      (constTitles ts vs).map (·.const_) = vs ∧ (constTitles ts vs).map (·.title) = ts
  | [], [], _ => ⟨rfl, rfl⟩
  | t :: ts, v :: vs, h => by
    obtain ⟨h1, h2⟩ := map_const_constTitles ts vs (by simpa using h)
    simp [constTitles] at h1 h2 ⊢
    exact ⟨h1, h2⟩

/-- The checks of a multi-select default pass exactly when every default is an enum value and a
non-empty default is within the item bounds. -/
theorem multiSelectDefaultError?_eq_none_iff {T : Type} (b : EnumSchemaBuilder T)
    (ds : List String) :
    multiSelectDefaultError? b ds = none ↔
      (∀ d ∈ ds, d ∈ b.enum_values.val) ∧
        (ds ≠ [] → (∀ lo, b.min_items = some lo → lo.val ≤ ds.length) ∧
          ∀ hi, b.max_items = some hi → ds.length ≤ hi.val) := by
  unfold multiSelectDefaultError?
  cases hmin : b.min_items <;> cases hmax : b.max_items <;>
    by_cases hds : ds = [] <;> simp [hds] <;> split_ifs <;> simp_all

/-- The checks of `min_items` pass exactly when the minimum is at most the maximum and at most
the length of a non-empty default. -/
theorem minItemsError?_eq_none_iff {T : Type} (b : EnumSchemaBuilder T) (value : U64) :
    minItemsError? b value = none ↔
      (∀ hi, b.max_items = some hi → value.val ≤ hi.val) ∧
        (b.default.val ≠ [] → value.val ≤ b.default.length) := by
  unfold minItemsError?
  cases hmax : b.max_items <;> simp
  split_ifs <;> simp_all

/-- The checks of `max_items` pass exactly when the maximum is at least the minimum and the
length of a non-empty default. -/
theorem maxItemsError?_eq_none_iff {T : Type} (b : EnumSchemaBuilder T) (value : U64) :
    maxItemsError? b value = none ↔
      (∀ lo, b.min_items = some lo → lo.val ≤ value.val) ∧
        (b.default.val ≠ [] → b.default.length ≤ value.val) := by
  unfold maxItemsError?
  cases hmin : b.min_items <;> simp
  split_ifs <;> simp_all

end Proofs.Model.ElicitationSchema
