/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.Tree.Decode

/-!
# Finite tree excursions

A Łukasiewicz tree word has integer increments at least `-1`, total sum `-1`,
and nonnegative sums at every strict prefix. The increment decoder checks the
lower bound before converting increments to natural outdegrees.
-/

@[expose] public section

namespace BGW

/-- Integer increment words of finite plane trees, with the empty prefix included
and the terminal prefix excluded from the nonnegativity condition. -/
def IsTreeExcursion (xs : List ℤ) : Prop :=
  (∀ x ∈ xs, -1 ≤ x) ∧ xs.sum = -1 ∧ ∀ i < xs.length, 0 ≤ (xs.take i).sum

namespace PlaneTree

/-- Reconstruct a tree from integer increments, rejecting values below `-1`
before converting them to outdegrees. The degree decoder accepts one tree only. -/
def ofIncrements? (xs : List ℤ) : Option PlaneTree :=
  if ∀ x ∈ xs, -1 ≤ x then ofDegrees? (xs.map (fun (x : ℤ) => (x + 1).toNat))
  else none

/-- The degree word recovered from the increments of a tree is unchanged. -/
private theorem map_toNat_add_one_increments (t : PlaneTree) :
    t.increments.map (fun (x : ℤ) => (x + 1).toNat) = t.degrees := by
  simp only [increments, List.map_map, Function.comp_def, Int.sub_add_cancel,
    Int.toNat_natCast]
  exact List.map_id _

private theorem map_degree_increments (xs : List ℤ) (h : ∀ x ∈ xs, -1 ≤ x) :
    (xs.map (fun (x : ℤ) => (x + 1).toNat)).map (fun (d : ℕ) => (d : ℤ) - 1) =
      xs := by
  rw [List.map_map]
  change xs.map (fun (x : ℤ) => ((x + 1).toNat : ℤ) - 1) = xs
  calc
    _ = xs.map (fun (x : ℤ) => x) := by
      apply List.map_congr_left
      intro x hx
      have hx' : 0 ≤ x + 1 := by have := h x hx; omega
      rw [Int.toNat_of_nonneg hx']
      omega
    _ = xs := List.map_id xs

/-- The forward DFS code satisfies exactly the finite-excursion conditions. -/
theorem isTreeExcursion_increments (t : PlaneTree) : IsTreeExcursion t.increments :=
  ⟨fun _ hx => neg_one_le_increment t hx, sum_increments t,
    fun _ hi => sum_take_increments_nonneg t hi⟩

/-- Decoding the increment word of a tree recovers that tree. -/
@[simp] theorem ofIncrements?_increments (t : PlaneTree) :
    ofIncrements? t.increments = some t := by
  rw [ofIncrements?, ite_eq_left (fun _ hx => neg_one_le_increment t hx),
    map_toNat_add_one_increments, ofDegrees?_degrees]

/-- A successful increment parse reproduces the entire input word. -/
theorem increments_ofIncrements? {xs : List ℤ} {t : PlaneTree}
    (h : ofIncrements? xs = some t) : t.increments = xs := by
  by_cases hb : ∀ x ∈ xs, -1 ≤ x
  · rw [ofIncrements?, ite_eq_left hb] at h
    have hd := ofDegrees?_eq_some_iff.mp h
    rw [increments, hd]
    exact map_degree_increments xs hb
  · simp [ofIncrements?, hb] at h

theorem ofIncrements?_eq_some_iff {xs : List ℤ} {t : PlaneTree} :
    ofIncrements? xs = some t ↔ t.increments = xs := by
  constructor
  · exact increments_ofIncrements?
  · intro h
    rw [← h, ofIncrements?_increments]

theorem increments_injective : Function.Injective increments := by
  intro s t h
  have he := congrArg ofIncrements? h
  simpa using he

private def GoodSuffix (ds : List ℕ) : Prop :=
  ∀ i < ds.length, (ds.drop i).sum < (ds.drop i).length

private theorem exists_ofDegrees?_eq_some_of_goodSuffix (ds : List ℕ) :
    GoodSuffix ds → ∃ ts, PlaneForest.ofDegrees? ds = some ts := by
  induction ds with
  | nil => intro _; exact ⟨[], rfl⟩
  | cons d ds ih =>
    intro h
    have ht : GoodSuffix ds := by
      intro i hi
      simpa only [List.drop_succ_cons] using
        h (i + 1) (by simpa using Nat.succ_lt_succ hi)
    obtain ⟨ts, hts⟩ := ih ht
    have hcount := PlaneForest.length_add_sum_of_ofDegrees?_eq_some hts
    have hzero : d + ds.sum < ds.length + 1 := by
      simpa only [List.drop_zero, List.sum_cons, List.length_cons] using h 0 (by simp)
    have hd : d ≤ ts.length := by omega
    refine ⟨node (ts.take d) :: ts.drop d, ?_⟩
    rw [PlaneForest.ofDegrees?_cons, hts, Option.bind_some, ite_eq_left hd]

private theorem sum_map_toNat_add_one (xs : List ℤ) :
    (∀ x ∈ xs, -1 ≤ x) →
    ((xs.map (fun (x : ℤ) => (x + 1).toNat)).sum : ℤ) =
      xs.sum + (xs.length : ℤ) := by
  induction xs with
  | nil => intro _; simp
  | cons x xs ih =>
    intro h
    have hx : 0 ≤ x + 1 := by have := h x (by simp); omega
    have ht := ih (fun y hy => h y (by simp [hy]))
    simp only [List.map_cons, List.sum_cons, List.length_cons, Int.natCast_add,
      Int.natCast_one, Int.toNat_of_nonneg hx]
    omega

private theorem goodSuffix_of_isTreeExcursion {xs : List ℤ} (h : IsTreeExcursion xs) :
    GoodSuffix (xs.map (fun (x : ℤ) => (x + 1).toNat)) := by
  intro i hi
  have hi' : i < xs.length := by simpa only [List.length_map] using hi
  have hp := h.2.2 i hi'
  have hsplit := List.sum_take_add_sum_drop xs i
  have htotal := h.2.1
  have hsuffix : (xs.drop i).sum ≤ -1 := by omega
  have hcast := sum_map_toNat_add_one (xs.drop i)
    (fun x hx => h.1 x (List.mem_of_mem_drop hx))
  simp only [← List.map_drop, List.length_map]
  omega

/-- Every valid tree excursion parses successfully as one tree. -/
theorem exists_ofIncrements?_eq_some (xs : List ℤ) (h : IsTreeExcursion xs) :
    ∃ t, ofIncrements? xs = some t := by
  let ds := xs.map (fun (x : ℤ) => (x + 1).toNat)
  obtain ⟨ts, hts⟩ := exists_ofDegrees?_eq_some_of_goodSuffix ds
    (goodSuffix_of_isTreeExcursion h)
  have hcount := PlaneForest.length_add_sum_of_ofDegrees?_eq_some hts
  have hsum := sum_map_toNat_add_one xs h.1
  change (ds.sum : ℤ) = xs.sum + (xs.length : ℤ) at hsum
  have hlen : ds.length = xs.length := by simp [ds]
  have htotal := h.2.1
  have hsingle : ts.length = 1 := by omega
  obtain ⟨t, rfl⟩ := List.length_eq_one_iff.mp hsingle
  refine ⟨t, ?_⟩
  rw [ofIncrements?, ite_eq_left h.1]
  exact ofDegrees?_eq_some_iff_forest.mpr hts

/-- Integer Łukasiewicz excursions are precisely the codes of unique finite plane trees. -/
theorem isTreeExcursion_iff_existsUnique (xs : List ℤ) :
    IsTreeExcursion xs ↔ ∃! t : PlaneTree, t.increments = xs := by
  constructor
  · intro h
    obtain ⟨t, ht⟩ := exists_ofIncrements?_eq_some xs h
    have hcode := increments_ofIncrements? ht
    refine ⟨t, hcode, ?_⟩
    intro s hs
    exact increments_injective (hs.trans hcode.symm)
  · rintro ⟨t, ht, _⟩
    rw [← ht]
    exact isTreeExcursion_increments t

end PlaneTree
end BGW
