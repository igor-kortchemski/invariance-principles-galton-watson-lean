/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.ForestLocalLimitKaramata
import BGW.StableTrees.RegularVariation.Consequences

/-!
# Residue-class form of the exact Karamata tail

The first point of the residue class strictly above the cutoff is asymptotic to
that cutoff. Reindexing the arithmetic progression gives the periodic sum.

Reference: J.-F. Le Gall, *Random trees and applications*, Probab. Surveys 2 (2005),
Section 1.
-/

@[expose] public section

open Filter Set
open scoped Topology

namespace BGW.StableTrees

private def nextResidue (d n : ℕ) : ℕ := d * ((n - 1) / d + 1) + 1

private theorem nextResidue_bounds {d n : ℕ} (hd : 0 < d) (hn : 1 ≤ n) :
    n < nextResidue d n ∧ nextResidue d n ≤ n + d := by
  have hm := Nat.mod_lt (n - 1) hd
  have he := Nat.mod_add_div (n - 1) d
  unfold nextResidue
  rw [Nat.mul_add, Nat.mul_one]
  omega

private theorem nextResidue_dvd (d n m : ℕ) :
    (d : ℤ) ∣ (nextResidue d n + d * m : ℕ) - (1 : ℤ) := by
  refine ⟨(((n - 1) / d + 1 + m : ℕ) : ℤ), ?_⟩
  simp only [nextResidue, Nat.cast_add, Nat.cast_mul, Nat.cast_one]
  ring

private theorem nextResidue_range {d n k : ℕ} (hn : 1 ≤ n)
    (hkn : n < k) (hdk : (d : ℤ) ∣ (k : ℤ) - 1) :
    ∃ m : ℕ, nextResidue d n + d * m = k := by
  have hk1 : 1 ≤ k := by omega
  have hnat : d ∣ k - 1 := by
    apply Int.natCast_dvd_natCast.1
    simpa only [Nat.cast_sub hk1, Nat.cast_one] using hdk
  have he : d * ((k - 1) / d) + 1 = k := by
    have hh := Nat.div_mul_cancel hnat
    rw [Nat.mul_comm] at hh
    omega
  have hbase : d * ((n - 1) / d) ≤ n - 1 := by
    have hh := Nat.mod_add_div (n - 1) d
    omega
  have hq : (n - 1) / d + 1 ≤ (k - 1) / d := by
    by_contra H
    have hh := Nat.mul_le_mul_left d (show (k - 1) / d ≤ (n - 1) / d by omega)
    omega
  refine ⟨(k - 1) / d - ((n - 1) / d + 1), ?_⟩
  have hmul := Nat.mul_le_mul_left d hq
  unfold nextResidue
  rw [Nat.mul_sub]
  omega

private theorem residue_strict_tail {ρ : ℝ} {B : ℕ → ℝ}
    (hrv : RegularlyVaryingSeq ρ B) (hmono : Monotone B)
    (hpos : ∀ n, 1 ≤ n → 0 < B n) (hρ : 0 < ρ) {d : ℕ} (hd : 0 < d) :
    Tendsto (fun n : ℕ => B n * ∑' k : ℕ,
      if n < k ∧ (d : ℤ) ∣ (k : ℤ) - 1 then (d : ℝ) / ((k : ℝ) * B k) else 0)
      atTop (𝓝 (1 / ρ)) := by
  classical
  have hs : Tendsto (fun n : ℕ => (nextResidue d n : ℝ) / n) atTop (𝓝 1) := by
    have hu := (tendsto_const_nhds (x := (1 : ℝ))).add
      (tendsto_const_div_atTop_nhds_zero_nat (d : ℝ))
    rw [add_zero] at hu
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu
    · filter_upwards [eventually_ge_atTop 1] with n hn
      have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
      apply (le_div_iff₀ hnR).2
      simpa only [one_mul] using
        (show (n : ℝ) ≤ nextResidue d n by exact_mod_cast (nextResidue_bounds hd hn).1.le)
    · filter_upwards [eventually_ge_atTop 1] with n hn
      have hnR : (n : ℝ) ≠ 0 := by positivity
      rw [← div_self hnR, ← add_div]
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
      exact_mod_cast (nextResidue_bounds hd hn).2
  have ht := regularVariation_progression_tail hrv hmono hpos hρ hd hs
  refine ht.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  congr 1
  let F : ℕ → ℝ := fun k =>
    if n < k ∧ (d : ℤ) ∣ (k : ℤ) - 1 then 1 / ((k : ℝ) * B k) else 0
  have hinj : Function.Injective (fun m : ℕ => nextResidue d n + d * m) := by
    intro i j hij
    exact Nat.eq_of_mul_eq_mul_left hd (Nat.add_left_cancel hij)
  have hrange : Function.support F ⊆ Set.range (fun m : ℕ => nextResidue d n + d * m) := by
    intro k hk
    have hh : n < k ∧ (d : ℤ) ∣ (k : ℤ) - 1 := by
      by_contra H
      exact hk (by simp [F, H])
    exact nextResidue_range hn hh.1 hh.2
  have heq := hinj.tsum_eq hrange
  have hterm (m : ℕ) : F (nextResidue d n + d * m) =
      1 / (((nextResidue d n + d * m : ℕ) : ℝ) * B (nextResidue d n + d * m)) := by
    have hk : n < nextResidue d n + d * m :=
      (nextResidue_bounds hd hn).1.trans_le (Nat.le_add_right _ _)
    exact ite_eq_left ⟨hk, nextResidue_dvd d n m⟩
  simp_rw [hterm] at heq
  rw [heq, ← tsum_mul_left]
  apply tsum_congr
  intro k
  dsimp only [F]
  split_ifs <;> ring

/-- The exact Karamata tail on `d ∣ k - 1`, including its mesh factor `d`. -/
theorem regularVariation_residue_tail {ρ : ℝ} {B : ℕ → ℝ}
    (hrv : RegularlyVaryingSeq ρ B) (hmono : Monotone B)
    (hpos : ∀ n, 1 ≤ n → 0 < B n) (hρ : 0 < ρ) {d : ℕ} (hd : 0 < d) :
    Tendsto (fun n : ℕ => B n * ∑' k : ℕ,
      if n ≤ k ∧ (d : ℤ) ∣ (k : ℤ) - 1 then (d : ℝ) / ((k : ℝ) * B k) else 0)
      atTop (𝓝 (1 / ρ)) := by
  have hsub : Tendsto (fun n : ℕ => ((n - 1 : ℕ) : ℝ) / n) atTop (𝓝 1) := by
    have ht := (tendsto_const_nhds (x := (1 : ℝ))).sub
      (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ))
    rw [sub_zero] at ht
    refine ht.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hnR : (n : ℝ) ≠ 0 := by positivity
    rw [Nat.cast_sub hn, Nat.cast_one, sub_div, div_self hnR]
  have hratio := (hrv.tendsto_ratio_of_tendsto_div hmono hpos zero_lt_one hsub).inv₀
    (by simp)
  simp only [Real.one_rpow, inv_one, inv_div] at hratio
  have ht := hratio.mul ((residue_strict_tail hrv hmono hpos hρ hd).comp
    (tendsto_sub_atTop_nat 1))
  rw [one_mul] at ht
  refine ht.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hB := (hpos (n - 1) (by omega)).ne'
  dsimp only [Function.comp_apply]
  rw [← mul_assoc, div_mul_cancel₀ _ hB]
  congr 1
  apply tsum_congr
  intro k
  have he : n - 1 < k ↔ n ≤ k := by omega
  simp only [he]

end BGW.StableTrees
