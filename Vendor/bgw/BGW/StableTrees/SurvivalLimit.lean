/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.SurvivalIntegralScale

/-!
# Inverting the survival time change

The limiting time change is a strictly decreasing power function. Comparison at fixed
positive scaled arguments identifies the limit for every sequence of generation indices.
-/

@[expose] public section

open MeasureTheory Filter
open scoped Topology

namespace BGW.StableTrees.Survival

/-- The CSBP survival function is positive at positive times and index greater than one. -/
theorem csbpSurvival_pos {θ δ : ℝ} (hθ : 1 < θ) (hδ : 0 < δ) :
    0 < csbpSurvival θ δ := Real.rpow_pos_of_pos (mul_pos (by linarith) hδ) _

/-- Substitution of the CSBP survival function into the limiting time change. -/
theorem csbpSurvival_time {θ δ : ℝ} (hθ : 1 < θ) (hδ : 0 < δ) :
    csbpSurvival θ δ ^ (1 - θ) / (θ - 1) = δ := by
  have hr : θ - 1 ≠ 0 := by linarith
  have hbase : 0 ≤ (θ - 1) * δ := (mul_pos (by linarith) hδ).le
  rw [csbpSurvival, ← Real.rpow_mul hbase,
    show (-1 / (θ - 1)) * (1 - θ) = 1 by field_simp; ring, Real.rpow_one]
  field_simp

/-- A positive height-scale limit forces the generation indices to infinity. -/
theorem tendsto_generation_atTop {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ}
    (h : StableDomain μ θ B) {δ : ℝ} (hδ : 0 < δ) {k : ℕ → ℕ}
    (hk : Tendsto (fun n : ℕ => (k n : ℝ) * B n / n) atTop (𝓝 δ)) :
    Tendsto k atTop atTop := by
  have hsmall : Tendsto (fun n : ℕ => B n / n) atTop (𝓝[>] 0) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨tendsto_B_div_n h, ?_⟩
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact div_pos (h.pos n hn) (by exact_mod_cast (by omega : 0 < n))
  have ht := hk.pos_mul_atTop hδ hsmall.inv_tendsto_nhdsGT_zero
  have hkR : Tendsto (fun n => (k n : ℝ)) atTop atTop := by
    apply ht.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hB := (h.pos n hn).ne'
    have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
    dsimp only [Pi.inv_apply]
    field_simp
  rw [tendsto_atTop_atTop]
  intro N
  apply eventually_atTop.1
  exact (hkR.eventually_ge_atTop (N : ℝ)).mono fun n hn => by exact_mod_cast hn

/-- **Survival at the height scale.**  If `k_n B_n / n → δ > 0`, then
`B_n s(k_n) → ((θ-1) δ)^(-1/(θ-1))`. -/
theorem tendsto_survivalProb_scaled {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ} (h : StableDomain μ θ B)
    {δ : ℝ} (hδ : 0 < δ) {k : ℕ → ℕ}
    (hk : Tendsto (fun n : ℕ => (k n : ℝ) * B n / n) atTop (𝓝 δ)) :
    Tendsto (fun n : ℕ => B n * survivalProb μ (k n)) atTop (𝓝 (csbpSurvival θ δ)) := by
  have hkTop := tendsto_generation_atTop h hδ hk
  have hv := csbpSurvival_pos h.alpha_mem.1 hδ
  have hθ : 0 < θ - 1 := by linarith [h.alpha_mem.1]
  have htime : Tendsto (fun n : ℕ => (B n / n) * survivalTime μ (survivalProb μ (k n)))
      atTop (𝓝 δ) := by
    have ht := ((tendsto_survivalTime_div_natCast h).comp hkTop).mul hk
    simp only [one_mul] at ht
    apply ht.congr'
    filter_upwards [hkTop.eventually_ge_atTop 1] with n hn
    have hkn : (k n : ℝ) ≠ 0 := by exact_mod_cast (by omega : k n ≠ 0)
    dsimp only [Function.comp_def]
    field_simp
  have hstrict : StrictAntiOn (fun y : ℝ => y ^ (1 - θ) / (θ - 1)) (Set.Ioi 0) := by
    intro a ha b hb hab
    exact (div_lt_div_iff_of_pos_right hθ).mpr
      (Real.rpow_lt_rpow_of_neg ha hab (by linarith))
  apply tendsto_order.mpr
  constructor
  · intro a ha
    by_cases ha0 : 0 < a
    · have hgap : δ < a ^ (1 - θ) / (θ - 1) := by
        rw [← csbpSurvival_time h.alpha_mem.1 hδ]
        exact hstrict ha0 hv ha
      have hcmp := htime.eventually_lt (tendsto_survivalTime_scaled h ha0) hgap
      filter_upwards [hcmp, (tendsto_B_atTop h).eventually_gt_atTop a,
        eventually_ge_atTop 1] with n hn hBn hn1
      have hB : 0 < B n := ha0.trans hBn
      have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
      have hcoeff : 0 < B n / n := div_pos hB hnR
      by_contra hnot
      have hle : survivalProb μ (k n) ≤ a / B n := by
        rw [le_div_iff₀ hB]
        simpa [mul_comm] using le_of_not_gt hnot
      have hanti := survivalTime_antitoneOn h.critical h.nondegenerate
        ⟨survivalProb_pos h.critical h.nondegenerate _, (survivalProb_mem_Icc μ _).2⟩
        ⟨div_pos ha0 hB, (div_le_one hB).mpr hBn.le⟩ hle
      have hmul := mul_le_mul_of_nonneg_left hanti hcoeff.le
      linarith
    · filter_upwards [(tendsto_B_atTop h).eventually_gt_atTop 0] with n hn
      exact lt_of_le_of_lt (le_of_not_gt ha0)
        (mul_pos hn (survivalProb_pos h.critical h.nondegenerate _))
  · intro b hb
    have hb0 : 0 < b := hv.trans hb
    have hgap : b ^ (1 - θ) / (θ - 1) < δ := by
      rw [← csbpSurvival_time h.alpha_mem.1 hδ]
      exact hstrict hv hb0 hb
    have hcmp := (tendsto_survivalTime_scaled h hb0).eventually_lt htime hgap
    filter_upwards [hcmp, (tendsto_B_atTop h).eventually_gt_atTop b,
      eventually_ge_atTop 1] with n hn hBn hn1
    have hB : 0 < B n := hb0.trans hBn
    have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hcoeff : 0 < B n / n := div_pos hB hnR
    by_contra hnot
    have hle : b / B n ≤ survivalProb μ (k n) := by
      rw [div_le_iff₀ hB]
      simpa [mul_comm] using le_of_not_gt hnot
    have hanti := survivalTime_antitoneOn h.critical h.nondegenerate
      ⟨div_pos hb0 hB, (div_le_one hB).mpr hBn.le⟩
      ⟨survivalProb_pos h.critical h.nondegenerate _, (survivalProb_mem_Icc μ _).2⟩ hle
    have hmul := mul_le_mul_of_nonneg_left hanti hcoeff.le
    linarith

end BGW.StableTrees.Survival
