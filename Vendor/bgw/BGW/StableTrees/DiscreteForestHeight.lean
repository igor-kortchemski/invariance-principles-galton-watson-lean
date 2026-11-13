/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.DiscreteForestBasic
import Mathlib.Data.Finset.Max

/-!
# The deterministic shifted-height identity

Separate records preceding the shift from records inside the shifted interval.
The former attain their final count at the first minimum of the intervening walk.
-/

@[expose] public section

open scoped Classical

namespace BGW.StableTrees.DiscreteForest

private noncomputable def oldRecords (ω : ℕ → ℕ) (m k : ℕ) : Finset ℕ :=
  (Finset.range m).filter
    (fun j => ∀ l, j ≤ l → l ≤ m + k → walk ω j ≤ walk ω l)

private theorem height_split (ω : ℕ → ℕ) (m k : ℕ) :
    forestHeight ω (m + k) =
      (oldRecords ω m k).card + forestHeight (shiftSeq m ω) k := by
  simp only [forestHeight, oldRecords, Finset.card_eq_sum_ones, Finset.sum_filter,
    Finset.sum_range_add]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  apply propext
  constructor
  · intro h l hil hlk
    rw [walk_shiftSeq, walk_shiftSeq]
    have hl := h (m + l) (by omega) (by omega)
    omega
  · intro h l hil hlmk
    have hl := h (l - m) (by omega) (by omega)
    rw [walk_shiftSeq, walk_shiftSeq, Nat.add_sub_of_le (by omega : m ≤ l)] at hl
    omega

private theorem oldRecords_antitone (ω : ℕ → ℕ) (m : ℕ) {i k : ℕ} (hik : i ≤ k) :
    oldRecords ω m k ⊆ oldRecords ω m i := by
  intro j hj
  simp only [oldRecords, Finset.mem_filter, Finset.mem_range] at hj ⊢
  exact ⟨hj.1, fun l hjl hli => hj.2 l hjl (by omega)⟩

private theorem exists_first_min (ω : ℕ → ℕ) (m k : ℕ) :
    ∃ t ≤ k, (∀ i ≤ k, walk ω (m + t) ≤ walk ω (m + i)) ∧
      ∀ i < t, walk ω (m + t) < walk ω (m + i) := by
  obtain ⟨u, hu, hmin⟩ := (Finset.range (k + 1)).exists_min_image
    (fun i => walk ω (m + i)) ⟨0, by simp⟩
  have hu' : u ≤ k := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hu
  have hex : ∃ t, t ≤ k ∧ ∀ i ≤ k, walk ω (m + t) ≤ walk ω (m + i) :=
    ⟨u, hu', fun i hi => hmin i (by simp; omega)⟩
  refine ⟨Nat.find hex, (Nat.find_spec hex).1, (Nat.find_spec hex).2, ?_⟩
  intro i hi
  have hbound : Nat.find hex ≤ k := (Nat.find_spec hex).1
  have hik : i ≤ k := by omega
  have hle := (Nat.find_spec hex).2 i hik
  by_contra hn
  have he : walk ω (m + i) = walk ω (m + Nat.find hex) := by omega
  have hbad := Nat.find_min hex hi
  apply hbad
  refine ⟨hik, ?_⟩
  intro j hj
  rw [he]
  exact (Nat.find_spec hex).2 j hj

private theorem oldRecords_at_min (ω : ℕ → ℕ) (m k t : ℕ) (ht : t ≤ k)
    (hmin : ∀ i ≤ k, walk ω (m + t) ≤ walk ω (m + i)) :
    oldRecords ω m t = oldRecords ω m k := by
  apply Finset.Subset.antisymm _ (oldRecords_antitone ω m ht)
  intro j hj
  simp only [oldRecords, Finset.mem_filter, Finset.mem_range] at hj ⊢
  refine ⟨hj.1, fun l hjl hlk => ?_⟩
  by_cases hl : l ≤ m + t
  · exact hj.2 l hjl hl
  · have hle := (hj.2 (m + t) (by omega) (le_refl _)).trans
      (hmin (l - m) (by omega))
    simpa only [Nat.add_sub_of_le (by omega : m ≤ l)] using hle

private theorem height_at_first_min (ω : ℕ → ℕ) (m t : ℕ)
    (hfirst : ∀ i < t, walk ω (m + t) < walk ω (m + i)) :
    forestHeight (shiftSeq m ω) t = 0 := by
  apply Finset.card_eq_zero.mpr
  apply Finset.filter_eq_empty_iff.mpr
  intro i hi hrecord
  have hit : i < t := Finset.mem_range.mp hi
  have hle := hrecord t hit.le (le_refl _)
  rw [walk_shiftSeq, walk_shiftSeq] at hle
  have hlt := hfirst i hit
  omega

/-- (Finding 3, deterministic) `H_{m+k} - min_{m≤j≤m+k} H_j = H_k` of the shifted sequence,
for every `ω`, `m`, `k`. -/
theorem shiftedHeight_eq (ω : ℕ → ℕ) (m k : ℕ) :
    shiftedHeight ω m k = (forestHeight (shiftSeq m ω) k : ℤ) := by
  obtain ⟨t, ht, hmin, hfirst⟩ := exists_first_min ω m k
  have hat : forestHeight ω (m + t) = (oldRecords ω m k).card := by
    rw [height_split, height_at_first_min ω m t hfirst, add_zero,
      oldRecords_at_min ω m k t ht hmin]
  have hminimum : minHeight ω m k = (oldRecords ω m k).card := by
    apply le_antisymm
    · exact (Finset.inf'_le _ (by simp; omega)).trans_eq hat
    · apply Finset.le_inf'
      intro i hi
      have hik : i ≤ k := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hi
      have hcard := Finset.card_le_card (oldRecords_antitone ω m hik)
      rw [height_split]
      omega
  unfold shiftedHeight
  rw [hminimum, height_split, Nat.cast_add]
  omega

end BGW.StableTrees.DiscreteForest
