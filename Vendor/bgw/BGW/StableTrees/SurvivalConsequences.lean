/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.SurvivalRegularity
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Elementary consequences of the scaled survival limit

The lemmas in this file isolate the real-analytic part of the floor and extinction-step
corollaries, independently of the recursion argument used to establish the scaled survival
limit itself.
-/

@[expose] public section

open MeasureTheory Filter ProbabilityTheory
open scoped Topology ENNReal

namespace BGW.StableTrees.Survival

/-- Convergence implies an eventual upper bound with an arbitrary sign for the limit. -/
theorem exists_pos_eventually_le_of_tendsto {F : ℕ → ℝ} {v : ℝ}
    (hF : Tendsto F atTop (𝓝 v)) : ∃ C : ℝ, 0 < C ∧ ∀ᶠ n in atTop, F n ≤ C := by
  let C := max (v + 1) 1
  have hv : v < C := lt_of_lt_of_le (by linarith) (le_max_left _ _)
  refine ⟨C, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  exact (hF.eventually (Iio_mem_nhds hv)).mono fun n hn => hn.le

/-- The elementary floor multiplier attached to a scaled survival limit. -/
theorem tendsto_floor_mul_of_scaled {B : ℕ → ℝ} {s : ℕ → ℝ} {v a : ℝ}
    (hB : Tendsto B atTop atTop) (hs : Tendsto (fun n : ℕ => B n * s n) atTop (𝓝 v))
    (ha : 0 ≤ a) :
    Tendsto (fun n : ℕ => (⌊a * B n⌋₊ : ℝ) * s n) atTop (𝓝 (a * v)) := by
  have hf := (tendsto_nat_floor_mul_div_atTop (R := ℝ) ha).comp hB
  have hprod := hf.mul hs
  apply hprod.congr'
  filter_upwards [hB.eventually_gt_atTop 0] with n hn
  dsimp only [Function.comp_def]
  field_simp

/-- The exponential extinction limit attached to a scaled survival limit. -/
theorem tendsto_extinction_pow_of_scaled {B : ℕ → ℝ} {s : ℕ → ℝ} {v a : ℝ}
    (hB : Tendsto B atTop atTop) (hs : Tendsto (fun n : ℕ => B n * s n) atTop (𝓝 v))
    (hv : 0 < v) (ha : 0 ≤ a) :
    Tendsto (fun n : ℕ => (1 - s n) ^ ⌊a * B n⌋₊) atTop (𝓝 (Real.exp (-(a * v)))) := by
  have hs0 : Tendsto s atTop (𝓝 0) := by
    have ht := hs.div_atTop hB
    apply ht.congr'
    filter_upwards [hB.eventually_gt_atTop 0] with n hn
    field_simp
  have hm := tendsto_floor_mul_of_scaled hB hs ha
  have hspos : ∀ᶠ n in atTop, 0 < s n := by
    filter_upwards [hs.eventually (lt_mem_nhds (show v / 2 < v by linarith)),
      hB.eventually_gt_atTop 0] with n hn hnB
    exact (mul_pos_iff_of_pos_left hnB).mp ((by linarith : (0 : ℝ) < v / 2).trans hn)
  have hs1 : ∀ᶠ n in atTop, s n < 1 := hs0.eventually (gt_mem_nhds zero_lt_one)
  have hs0' : Tendsto s atTop (𝓝[≠] 0) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨hs0, hspos.mono fun n hn => hn.ne'⟩
  have hderiv : HasDerivAt (fun x : ℝ => Real.log (1 - x)) (-1) 0 := by
    have hi : HasDerivAt (fun x : ℝ => 1 - x) (-1) 0 := by
      convert (hasDerivAt_id (0 : ℝ)).const_sub 1 using 1; simp
    simpa only [sub_zero, div_one] using hi.log (by norm_num : (1 : ℝ) - 0 ≠ 0)
  have hslope := hasDerivAt_iff_tendsto_slope.mp hderiv
  have hlog : Tendsto (fun x : ℝ => Real.log (1 - x) / x) (𝓝[≠] 0) (𝓝 (-1)) := by
    apply hslope.congr
    intro x
    simp [slope_def_field]
  have hlogn := hlog.comp hs0'
  have hscaled := hm.mul hlogn
  have hlogs : Tendsto (fun n : ℕ => (⌊a * B n⌋₊ : ℝ) * Real.log (1 - s n)) atTop
      (𝓝 (-(a * v))) := by
    have ht' : Tendsto (fun n : ℕ => (⌊a * B n⌋₊ : ℝ) * Real.log (1 - s n)) atTop
        (𝓝 (a * v * -1)) := by
      apply hscaled.congr'
      filter_upwards [hspos] with n hn
      dsimp only [Function.comp_def]
      field_simp
    simpa only [mul_neg, mul_one, neg_neg] using ht'
  apply hlogs.rexp.congr'
  filter_upwards [hs1] with n hn
  have hbase : 0 < 1 - s n := sub_pos.mpr hn
  calc
    Real.exp ((⌊a * B n⌋₊ : ℝ) * Real.log (1 - s n)) =
        (Real.exp (Real.log (1 - s n))) ^ ⌊a * B n⌋₊ :=
      Real.exp_nat_mul (Real.log (1 - s n)) ⌊a * B n⌋₊
    _ = (1 - s n) ^ ⌊a * B n⌋₊ := by rw [Real.exp_log hbase]

end BGW.StableTrees.Survival
