/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
module
public import Rmcp.Funs
public import Defs.ElicitationSchema
public import Proofs.External.Skill
public import Proofs.External.String
public import Proofs.External.WP

@[expose] public section

/-!
# Laws and specs of the externals of the elicitation schema builders (X01–X75, translation patch 08)

Spec theorems for the models of `formal/trusted/Rmcp/FunsExternal.lean`, section "Elicitation
schema builders" (human decision XD1, 2026-11-28): the two `elicitation_schema::prim` wrappers
that translation patch 08 adds and the seven `core`/`alloc` functions that the targets X01–X75
reach. Each external has a theorem named after it with `_spec`.

Section "`String` order" proves that `ExtModel.bytesCmp`, the model of `Ord for String` on the
UTF-8 bytes, is a total order that agrees with `ExtModel.bytesLt` and with equality
(`bytesCmp_eq_lt_iff`, `bytesCmp_eq_eq_iff`, `bytesCmp_eq_gt_iff`, `Ordering.swap_bytesCmp`).
Section "`BTreeMap::insert` with `String` keys" proves that the generic insertion model
`ExtModel.btreeInsert`, instantiated with the generated `Ord` instance of `String`, is the
reviewed `serde_json::Map` insertion `ExtModel.mapInsert` (`btreeInsert_stringOrd_eq_ok`), so
the `BTreeMap` model keeps its entries sorted by key with distinct keys
(`Proofs.External.Skill.sortedByKey_mapInsert`): every map the targets build from
`BTreeMap::default` meets the invariant that the model of `BTreeMap::insert` assumes (its stated
exception).
-/

open Aeneas Aeneas.Std Result
open rmcp

namespace Proofs.External.ElicitationSchema

open ExtModel Proofs.External.Skill

/-! ### `String` order -/

/-- `bytesCmp` is `lt` exactly when `bytesLt` holds. -/
theorem bytesCmp_eq_lt_iff (a b : List U8) : bytesCmp a b = .lt ↔ bytesLt a b = true := by
  unfold bytesCmp
  by_cases h : bytesLt a b = true
  · simp [h]
  · simp only [h, Bool.false_eq_true, ↓reduceIte, iff_false]
    split <;> simp

/-- `bytesCmp` is `eq` exactly on equal byte lists. -/
theorem bytesCmp_eq_eq_iff (a b : List U8) : bytesCmp a b = .eq ↔ a = b := by
  unfold bytesCmp
  by_cases h : bytesLt a b = true
  · have hne : a ≠ b := by
      rintro rfl
      rw [bytesLt_self] at h
      exact Bool.false_ne_true h
    simp [h, hne]
  · simp only [h, Bool.false_eq_true, ↓reduceIte]
    split <;> simp_all

/-- `bytesCmp` is `gt` exactly when `bytesLt` holds with the arguments swapped. -/
theorem bytesCmp_eq_gt_iff (a b : List U8) : bytesCmp a b = .gt ↔ bytesLt b a = true := by
  unfold bytesCmp
  by_cases h : bytesLt a b = true
  · simp only [h, ↓reduceIte, reduceCtorEq, false_iff]
    intro h'
    have := bytesLt_trans h h'
    rw [bytesLt_self] at this
    exact Bool.false_ne_true this
  · simp only [h, Bool.false_eq_true, ↓reduceIte]
    by_cases hab : a = b
    · subst hab
      simp [bytesLt_self]
    · simp only [hab, ↓reduceIte, true_iff]
      rcases bytesLt_or_bytesLt_of_ne hab with h' | h'
      · exact absurd h' h
      · exact h'

/-- Swapping the arguments of `bytesCmp` swaps the result (antisymmetry). -/
theorem _root_.Ordering.swap_bytesCmp (a b : List U8) : (bytesCmp a b).swap = bytesCmp b a := by
  cases h : bytesCmp a b
  · rw [bytesCmp_eq_lt_iff] at h
    exact ((bytesCmp_eq_gt_iff b a).2 h).symm
  · rw [bytesCmp_eq_eq_iff] at h
    subst h
    exact ((bytesCmp_eq_eq_iff a a).2 rfl).symm
  · rw [bytesCmp_eq_gt_iff] at h
    exact ((bytesCmp_eq_lt_iff b a).2 h).symm

/-- On the UTF-8 bytes of two strings, `bytesCmp` is `eq` exactly for equal strings. -/
theorem bytesCmp_utf8_eq_eq_iff (a b : String) : bytesCmp (utf8 a) (utf8 b) = .eq ↔ a = b :=
  (bytesCmp_eq_eq_iff _ _).trans ⟨Proofs.External.Utf8.utf8_injective, congrArg utf8⟩

/-! ### `BTreeMap::insert` with `String` keys -/

/-- The generated `Ord` instance of `String` compares with the model `ExtModel.bytesCmp` of the
UTF-8 bytes. -/
theorem stringOrd_cmp (a b : String) :
    (rmcp.alloc.string.String.Insts.CoreCmpOrd).cmp a b = ok (bytesCmp (utf8 a) (utf8 b)) :=
  rfl

/-- With the `Ord` instance of `String`, the `BTreeMap` insertion model is the `serde_json::Map`
insertion `ExtModel.mapInsert`: the comparisons never fail, and `lt`, `eq`, `gt` of `bytesCmp`
are `bytesLt`, equality and the remaining case. -/
theorem btreeInsert_stringOrd_eq_ok {V : Type} (k : String) (v : V) :
    ∀ l : List (String × V),
      btreeInsert rmcp.alloc.string.String.Insts.CoreCmpOrd k v l = ok (mapInsert k v l)
  | [] => rfl
  | (k', v') :: rest => by
    rw [btreeInsert, stringOrd_cmp, bind_ok, mapInsert]
    by_cases h : k' = k
    · subst h
      rw [(bytesCmp_eq_eq_iff _ _).2 rfl]
      simp
    · rw [ite_eq_right h]
      by_cases hlt : bytesLt (utf8 k) (utf8 k') = true
      · rw [(bytesCmp_eq_lt_iff _ _).2 hlt, ite_eq_left hlt]
      · have hgt : bytesCmp (utf8 k) (utf8 k') = .gt := by
          rw [bytesCmp_eq_gt_iff]
          rcases bytesLt_or_bytesLt_of_ne (a := utf8 k') (b := utf8 k)
              (fun he => h (Proofs.External.Utf8.utf8_injective he)) with h' | h'
          · exact h'
          · exact absurd h' hlt
        rw [hgt, ite_eq_right hlt]
        simp only [btreeInsert_stringOrd_eq_ok k v rest, bind_ok]
        generalize mapInsert k v rest = p
        rcases p with ⟨o, r⟩
        rfl

end Proofs.External.ElicitationSchema

open ExtModel Proofs.External.Skill Proofs.External.ElicitationSchema

/-! ## `BTreeMap`, `Vec` and `String` order -/

/-- **Spec theorem for `BTreeMap::default`**: the empty map. -/
@[step]
theorem alloc.collections.btree.map.BTreeMapKVGlobal.Insts.CoreDefaultDefault.default_spec
    (K V : Type) :
    alloc.collections.btree.map.BTreeMapKVGlobal.Insts.CoreDefaultDefault.default K V
      ⦃ (result : alloc.collections.btree.map.BTreeMap K V alloc.alloc.Global) =>
        result.entries = [] ⦄ := by
  simp only [alloc.collections.btree.map.BTreeMapKVGlobal.Insts.CoreDefaultDefault.default,
    WP.spec_ok]

/-- **Spec theorem for `BTreeMap::insert` with `String` keys**: for entries sorted by key
(every map built by `BTreeMap::default` and `BTreeMap::insert`), returns the old value of `k`
(`none` if `k` had none) and the entries with `k` mapped to `v` at its sorted position
(`ExtModel.mapInsert`), still sorted. -/
@[step]
theorem alloc.collections.btree.map.BTreeMap.insert_string_spec {V A : Type}
    (coreallocAllocatorCloneInst : core.alloc.AllocatorClone A)
    (self : alloc.collections.btree.map.BTreeMap String V A) (k : String) (v : V)
    (hsorted : SortedByKey self.entries) :
    alloc.collections.btree.map.BTreeMap.insert coreallocAllocatorCloneInst
        rmcp.alloc.string.String.Insts.CoreCmpOrd self k v
      ⦃ (result : Option V × alloc.collections.btree.map.BTreeMap String V A) =>
        result.1 = (self.entries.find? (fun e => e.1 == k)).map Prod.snd ∧
          result.2.entries = (mapInsert k v self.entries).2 ∧ SortedByKey result.2.entries ⦄ := by
  have hfst := mapInsert_fst_of_sortedByKey k v _ hsorted
  have hsnd := sortedByKey_mapInsert k v _ hsorted
  simp only [alloc.collections.btree.map.BTreeMap.insert, btreeInsert_stringOrd_eq_ok, bind_ok]
  revert hfst hsnd
  generalize mapInsert k v self.entries = p
  rcases p with ⟨o, r⟩
  intro hfst hsnd
  exact (WP.spec_ok _).2 ⟨hfst, rfl, hsnd⟩

/-- **Spec theorem for `<String as Ord>::cmp`**: the order of the UTF-8 bytes; `Equal` exactly
for equal strings (`bytesCmp_utf8_eq_eq_iff`). -/
@[step]
theorem alloc.string.String.Insts.CoreCmpOrd.cmp_spec (self other : String) :
    alloc.string.String.Insts.CoreCmpOrd.cmp self other
      ⦃ (result : Ordering) => result = bytesCmp (utf8 self) (utf8 other) ⦄ := by
  simp only [alloc.string.String.Insts.CoreCmpOrd.cmp, WP.spec_ok]

/-- **Spec theorem for `<String as PartialOrd>::partial_cmp`**: `some` of the `Ord` result. -/
@[step]
theorem alloc.string.String.Insts.CoreCmpPartialOrdString.partial_cmp_spec (self other : String) :
    alloc.string.String.Insts.CoreCmpPartialOrdString.partial_cmp self other
      ⦃ (result : Option Ordering) => result = some (bytesCmp (utf8 self) (utf8 other)) ⦄ := by
  simp only [alloc.string.String.Insts.CoreCmpPartialOrdString.partial_cmp, WP.spec_ok]

/-- **Spec theorem for `Vec::default`**: the empty vector. -/
@[step]
theorem alloc.vec.Vec.Insts.CoreDefaultDefault.default_spec (T : Type) :
    alloc.vec.Vec.Insts.CoreDefaultDefault.default T
      ⦃ (result : alloc.vec.Vec T) => result.val = [] ⦄ := by
  simp only [alloc.vec.Vec.Insts.CoreDefaultDefault.default, WP.spec_ok]
  rfl

/-- **Spec theorem for `<str as Debug>::fmt`** (a total, not exact, model; stated exception):
`Ok(())` with the formatter unchanged. -/
@[step]
theorem Str.Insts.CoreFmtDebug.fmt_spec (self : Str) (f : core.fmt.Formatter) :
    Str.Insts.CoreFmtDebug.fmt self f
      ⦃ (result : core.result.Result Unit core.fmt.Error × core.fmt.Formatter) =>
        result = (core.result.Result.Ok (), f) ⦄ := by
  simp only [Str.Insts.CoreFmtDebug.fmt, WP.spec_ok]

/-- **Spec theorem for `<slice::Iter<'_, T> as Iterator>::all`**

For a closure that computes `p` without changing its state, the result is whether `p` holds
for every remaining element. -/
theorem core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.all_spec {T F : Type}
    (opsfunctionFnMutFTupleSharedATBoolInst : core.ops.function.FnMut F T Bool) (p : T → Bool)
    (self : core.slice.iter.Iter T) (f : F)
    (hf : ∀ x, opsfunctionFnMutFTupleSharedATBoolInst.call_mut f x = ok (p x, f)) :
    core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.all
        opsfunctionFnMutFTupleSharedATBoolInst self f
      ⦃ (result : Bool × core.slice.iter.Iter T) =>
        result.1 = (self.slice.val.drop self.i).all p ⦄ := by
  obtain ⟨n, hn⟩ := exists_sliceIterAll_eq_ok opsfunctionFnMutFTupleSharedATBoolInst p f hf
    (self.slice.val.drop self.i)
  simp only [core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.all, hn, bind_ok]
  exact (WP.spec_ok _).2 rfl

/-! ## The `elicitation_schema::prim` wrappers -/

/-- **Spec theorem for `prim::titles_mismatch_message`**: the message of `enum_titles` with
both counts in decimal. -/
@[step]
theorem model.elicitation_schema.prim.titles_mismatch_message_spec (expected got : Usize) :
    model.elicitation_schema.prim.titles_mismatch_message expected got
      ⦃ (result : String) =>
        result = "Provided number of titles do not match number of values: expected " ++
          toString expected.val ++ ", but got " ++ toString got.val ⦄ := by
  simp only [model.elicitation_schema.prim.titles_mismatch_message, WP.spec_ok]

/-- **Spec theorem for `prim::sorted_keys`**: the keys of the entries, in order, when the
`Vec<String>` fits (`24` bytes per element within `isize::MAX`). -/
@[step]
theorem model.elicitation_schema.prim.sorted_keys_spec
    (properties : alloc.collections.btree.map.BTreeMap String
      model.elicitation_schema.PrimitiveSchemaDefinition alloc.alloc.Global)
    (hlen : 24 * properties.entries.length ≤ maxStringBytes) :
    model.elicitation_schema.prim.sorted_keys properties
      ⦃ (result : alloc.vec.Vec String) => result.val = properties.entries.map Prod.fst ⦄ := by
  obtain ⟨r, hr, hv⟩ := exists_collectVec_eq_ok 24 (properties.entries.map Prod.fst)
    (by decide) (by rw [List.length_map]; exact hlen)
  simp only [model.elicitation_schema.prim.sorted_keys, hr, WP.spec_ok]
  exact hv

/-- `prim::sorted_keys` panics when the `Vec<String>` would exceed `isize::MAX` bytes. -/
theorem model.elicitation_schema.prim.sorted_keys_eq_fail
    (properties : alloc.collections.btree.map.BTreeMap String
      model.elicitation_schema.PrimitiveSchemaDefinition alloc.alloc.Global)
    (hlen : maxStringBytes < 24 * properties.entries.length) :
    model.elicitation_schema.prim.sorted_keys properties = fail Error.panic := by
  rw [model.elicitation_schema.prim.sorted_keys]
  exact collectVec_eq_fail 24 _ (by rw [List.length_map]; exact hlen)

/-! ## Helpers for the elicitation schema targets

Lemmas about the external models that the spec theorems of
`Proofs.Model.ElicitationSchema.*` use: `BTreeMap::insert` with `String` keys as an equation (no
sortedness premise), `prim::sorted_keys`, `str::to_owned` of a literal, `vec::IntoIter::next` and
Aeneas `loop`. (The `String` order as a list order, lookups after `ExtModel.mapInsert`,
`<[String]>::contains` and the `usize as u64` cast are the existing lemmas of the
modules `Proofs.Model.Skill.Verify`, `Proofs.Transport.MetadataResolver.Common` and
`Proofs.Model.RequestStateWire.Common`, used from `Proofs.Model.ElicitationSchema.Common`.) -/

namespace Proofs.External.ElicitationSchema

open ExtModel Proofs.External.Skill Defs.ElicitationSchema

/-- `BTreeMap::insert` with `String` keys, as an equation, for any entry list (no sortedness
premise): the old value at `k` and the entries `mapInsert k v self.entries`. -/
theorem insert_string_eq {V A : Type} (inst : rmcp.core.alloc.AllocatorClone A)
    (self : alloc.collections.btree.map.BTreeMap String V A) (k : String) (v : V) :
    alloc.collections.btree.map.BTreeMap.insert inst
        rmcp.alloc.string.String.Insts.CoreCmpOrd self k v =
      ok ((mapInsert k v self.entries).1, { entries := (mapInsert k v self.entries).2 }) := by
  simp only [alloc.collections.btree.map.BTreeMap.insert, btreeInsert_stringOrd_eq_ok, bind_ok]
  generalize mapInsert k v self.entries = p
  rcases p with ⟨o, r⟩
  rfl

/-- The key list of a map that fits (`PropertiesFit`), as an equation. -/
theorem sorted_keys_eq_ok
    (properties : alloc.collections.btree.map.BTreeMap String
      rmcp.model.elicitation_schema.PrimitiveSchemaDefinition alloc.alloc.Global)
    (h : PropertiesFit properties) :
    ∃ names : alloc.vec.Vec String,
      model.elicitation_schema.prim.sorted_keys properties = ok names ∧
        names.val = propertyNames properties :=
  Proofs.External.WP.exists_ok_of_spec
    (model.elicitation_schema.prim.sorted_keys_spec properties h)

/-- `to_owned` of a string literal is the literal. -/
theorem to_owned_toStr (s : String) (h : s.toByteArray.size ≤ U32.max) :
    Str.Insts.AllocBorrowToOwnedString.to_owned (toStr s h) = ok s := by
  obtain ⟨r, hr, hrv⟩ := Proofs.External.WP.exists_ok_of_spec
    (Str.Insts.AllocBorrowToOwnedString.to_owned_spec (toStr s h) s
      (Proofs.External.Utf8.toStr_val s h))
  rw [hr, hrv]

/-! The four lemmas below are generic (`vec::IntoIter::next` and the Aeneas `loop`, not specific to
this file); they are candidates for a shared module. -/

/-- `vec::IntoIter::next` on an exhausted iterator. -/
theorem next_eq_none {T : Type} (it : alloc.vec.into_iter.IntoIter T) (h : it.val = []) :
    alloc.vec.into_iter.IteratorIntoIter.next it = ok (none, it) := by
  unfold alloc.vec.into_iter.IteratorIntoIter.next
  split
  · rfl
  · rename_i hd tl heq; rw [h] at heq; cases heq

/-- `vec::IntoIter::next` on a non-empty iterator: its head, and the iterator over its tail. -/
theorem next_eq_some {T : Type} (it : alloc.vec.into_iter.IntoIter T) (hd : T) (tl : List T)
    (h : it.val = hd :: tl) :
    ∃ it', alloc.vec.into_iter.IteratorIntoIter.next it = ok (some hd, it') ∧ it'.val = tl := by
  unfold alloc.vec.into_iter.IteratorIntoIter.next
  split
  · rename_i heq; rw [h] at heq; cases heq
  · rename_i hd' tl' heq
    rw [h] at heq
    cases heq
    exact ⟨_, rfl, alloc.vec.Vec.from_val ..⟩

/-- An Aeneas `loop` whose body continues with `y` from `x` is the loop from `y`. -/
theorem loop_eq_of_cont {α β : Type} (body : α → Result (ControlFlow α β)) (x y : α)
    (h : body x = ok (.cont y)) : loop body x = loop body y := by
  rw [loop, h, bind_ok]

/-- An Aeneas `loop` whose body stops with `y` from `x` returns `y`. -/
theorem loop_eq_of_done {α β : Type} (body : α → Result (ControlFlow α β)) (x : α) (y : β)
    (h : body x = ok (.done y)) : loop body x = ok y := by
  rw [loop, h, bind_ok]

end Proofs.External.ElicitationSchema
