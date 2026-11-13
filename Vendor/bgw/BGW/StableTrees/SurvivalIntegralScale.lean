/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.SurvivalIntegral
public import BGW.StableTrees.SurvivalPotter
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Scaling the reciprocal-defect integral

A Potter bound extended to the whole unit interval gives an integrable majorant for the
rescaled reciprocal defect.
-/

@[expose] public section

open MeasureTheory Filter
open scoped Topology

namespace BGW.StableTrees.Survival

/-- A lower Potter estimate valid up to the endpoint one, with a fixed positive constant. -/
theorem exists_offspringDefect_potter_unit {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ}
    (h : StableDomain μ θ B) {p : ℝ} (hp0 : 0 ≤ p) (hp : p < θ) :
    ∃ v₀ C : ℝ, 0 < v₀ ∧ v₀ ≤ 1 ∧ 0 < C ∧ ∀ u v : ℝ,
      0 < u → u ≤ v₀ → u ≤ v → v ≤ 1 →
      C * (v / u) ^ p * offspringDefect μ u ≤ offspringDefect μ v := by
  obtain ⟨v₀, hv₀, hv₀1, hd⟩ := exists_offspringDefect_potter_lower h hp0 hp
  let C := (v₀ / 2) ^ p
  have hC : 0 < C := Real.rpow_pos_of_pos (by positivity) _
  have hC1 : C ≤ (1 / 2 : ℝ) ^ p := by
    apply Real.rpow_le_rpow (by positivity) _ hp0
    linarith
  refine ⟨v₀, C, hv₀, hv₀1, hC, ?_⟩
  intro u v hu huv₀ huv hv1
  have hDu : 0 ≤ offspringDefect μ u := offspringDefect_nonneg h.critical hu.le
    (huv₀.trans hv₀1)
  have hratio : 1 ≤ v / u := (le_div_iff₀ hu).mpr (by simpa using huv)
  by_cases hv : v ≤ v₀
  · have hd' := hd u (v / u) hu hratio (by simpa [hu.ne'] using hv)
    have hpow : C * (v / u) ^ p ≤ ((v / u) / 2) ^ p := by
      rw [show (v / u) / 2 = (1 / 2) * (v / u) by ring,
        Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 1 / 2) (by positivity)]
      exact mul_le_mul_of_nonneg_right hC1 (Real.rpow_nonneg (by positivity) _)
    exact (mul_le_mul_of_nonneg_right hpow hDu).trans (by simpa [hu.ne'] using hd')
  · have hv' : v₀ ≤ v := (lt_of_not_ge hv).le
    have hd' := hd u (v₀ / u) hu ((le_div_iff₀ hu).mpr (by simpa using huv₀))
      (by simp [hu.ne'])
    have hpow : C * (v / u) ^ p ≤ ((v₀ / u) / 2) ^ p := by
      rw [← Real.mul_rpow (by positivity : 0 ≤ v₀ / 2) (by positivity)]
      apply Real.rpow_le_rpow (by positivity) _ hp0
      rw [show v₀ / 2 * (v / u) = v * (v₀ / u / 2) by ring]
      exact mul_le_of_le_one_left (by positivity) hv1
    calc
      C * (v / u) ^ p * offspringDefect μ u ≤
          (v₀ / u / 2) ^ p * offspringDefect μ u :=
        mul_le_mul_of_nonneg_right hpow hDu
      _ ≤ offspringDefect μ v₀ := by simpa [hu.ne'] using hd'
      _ ≤ offspringDefect μ v := offspringDefect_monotoneOn h.critical
        ⟨hv₀.le, hv₀1⟩ ⟨hu.le.trans huv, hv1⟩ hv'

/-- The reciprocal-defect integral at a fixed stable-scale point has its power-law limit. -/
theorem tendsto_survivalTime_scaled {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ}
    (h : StableDomain μ θ B) {y : ℝ} (hy : 0 < y) :
    Tendsto (fun n : ℕ => (B n / n) * survivalTime μ (y / B n)) atTop
      (𝓝 (y ^ (1 - θ) / (θ - 1))) := by
  let p := (1 + θ) / 2
  have hp : 1 < p := by dsimp [p]; linarith [h.alpha_mem.1]
  have hpθ : p < θ := by dsimp [p]; linarith [h.alpha_mem.1]
  obtain ⟨v₀, C, hv₀, hv₀1, hC, hpot⟩ :=
    exists_offspringDefect_potter_unit h (by linarith : 0 ≤ p) hpθ
  let A := y ^ θ / 2
  have hA : 0 < A := by dsimp [A]; positivity
  let D := y ^ p / (C * A)
  have hD : 0 < D := by dsimp [D]; positivity
  let F : ℕ → ℝ → ℝ := fun n =>
    (Set.Ioc y (B n)).indicator (fun x => ((n : ℝ) * offspringDefect μ (x / B n))⁻¹)
  let F₀ : ℝ → ℝ := (Set.Ioi y).indicator (fun x => x ^ (-θ))
  let M : ℝ → ℝ := (Set.Ioi y).indicator (fun x => D * x ^ (-p))
  have hnorm : Tendsto (fun n : ℕ => (n : ℝ) * offspringDefect μ (y / B n))
      atTop (𝓝 (y ^ θ)) := tendsto_realGF_expansion h hy
  have hsmall : ∀ᶠ n in atTop, y / B n ≤ v₀ :=
    (tendsto_const_nhds.div_atTop (tendsto_B_atTop h)).eventually
      (gt_mem_nhds hv₀) |>.mono (fun _ hn => hn.le)
  have hmajor : ∀ᶠ n in atTop, ∀ x : ℝ, ‖F n x‖ ≤ M x := by
    filter_upwards [hsmall, (tendsto_B_atTop h).eventually_gt_atTop y,
      hnorm.eventually (lt_mem_nhds (show A < y ^ θ by
        dsimp [A]; nlinarith [Real.rpow_pos_of_pos hy θ])),
      eventually_ge_atTop 1] with n hsn hBn hnA hn1 x
    have hB : 0 < B n := hy.trans hBn
    by_cases hx : x ∈ Set.Ioc y (B n)
    · have hx0 : 0 < x := hy.trans hx.1
      have hu : 0 < y / B n := div_pos hy hB
      have hv : x / B n ≤ 1 := (div_le_one hB).mpr hx.2
      have hpot' := hpot (y / B n) (x / B n) hu hsn
        (div_le_div_of_nonneg_right hx.1.le hB.le) hv
      have hrat : (x / B n) / (y / B n) = x / y := by field_simp
      rw [hrat] at hpot'
      have hDpos : 0 < offspringDefect μ (x / B n) :=
        offspringDefect_pos h.critical h.nondegenerate (div_pos hx0 hB) hv
      have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
      have hlow : C * A * (x / y) ^ p ≤ (n : ℝ) * offspringDefect μ (x / B n) := by
        have hmul := mul_le_mul_of_nonneg_left hpot' hnR.le
        have hpow : 0 ≤ (x / y) ^ p := Real.rpow_nonneg (by positivity) _
        nlinarith [mul_le_mul_of_nonneg_left hnA.le (mul_nonneg hC.le hpow)]
      have hmaj : ((n : ℝ) * offspringDefect μ (x / B n))⁻¹ ≤ D * x ^ (-p) := by
        calc
          ((n : ℝ) * offspringDefect μ (x / B n))⁻¹ ≤ (C * A * (x / y) ^ p)⁻¹ :=
            inv_anti₀ (by positivity) hlow
          _ = D * x ^ (-p) := by
            dsimp [D]
            rw [Real.div_rpow hx0.le hy.le, Real.rpow_neg hx0.le]
            field_simp
      simp only [F, M, Set.indicator_of_mem hx,
        Set.indicator_of_mem (show x ∈ Set.Ioi y from hx.1)]
      rw [Real.norm_of_nonneg (inv_nonneg.mpr (mul_nonneg hnR.le hDpos.le))]
      exact hmaj
    · rw [show F n x = 0 from Set.indicator_of_notMem hx _, norm_zero]
      by_cases hxy : y < x
      · simp only [M, Set.indicator_of_mem (show x ∈ Set.Ioi y from hxy)]
        exact mul_nonneg hD.le (Real.rpow_nonneg (hy.trans hxy).le _)
      · simp only [M, Set.indicator_of_notMem (show x ∉ Set.Ioi y from hxy), le_refl]
  have hmeas : ∀ᶠ n in atTop, AEStronglyMeasurable (F n) volume := by
    filter_upwards [(tendsto_B_atTop h).eventually_gt_atTop y,
      eventually_ge_atTop 1] with n hBn hn1
    have hB : 0 < B n := hy.trans hBn
    rw [aestronglyMeasurable_indicator_iff measurableSet_Ioc]
    apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioc
    apply ContinuousOn.inv₀
    · apply continuousOn_const.mul
      apply (continuousOn_offspringDefect μ).comp (by fun_prop)
      intro x hx
      exact ⟨(div_pos (hy.trans hx.1) hB).le, (div_le_one hB).mpr hx.2⟩
    · intro x hx
      exact mul_ne_zero (by exact_mod_cast (by omega : n ≠ 0))
        (offspringDefect_pos h.critical h.nondegenerate (div_pos (hy.trans hx.1) hB)
          ((div_le_one hB).mpr hx.2)).ne'
  have hpoint (x : ℝ) : Tendsto (fun n => F n x) atTop (𝓝 (F₀ x)) := by
    by_cases hx : y < x
    · have hx0 : 0 < x := hy.trans hx
      have ht := (tendsto_realGF_expansion h hx0).inv₀
        (Real.rpow_pos_of_pos hx0 θ).ne'
      simp only [← Real.rpow_neg hx0.le] at ht
      simp only [F₀, Set.indicator_of_mem (show x ∈ Set.Ioi y from hx)]
      apply ht.congr'
      filter_upwards [(tendsto_B_atTop h).eventually_ge_atTop x] with n hn
      simp only [F, Set.indicator_of_mem (show x ∈ Set.Ioc y (B n) from ⟨hx, hn⟩),
        offspringDefect]
    · simp [F, F₀, Set.mem_Ioc, hx]
  have hMint : Integrable M volume := by
    rw [integrable_indicator_iff measurableSet_Ioi]
    exact (integrableOn_Ioi_rpow_of_lt (by linarith : -p < -1) hy).const_mul D
  have ht := tendsto_integral_filter_of_dominated_convergence M hmeas
    (hmajor.mono fun n hn => Eventually.of_forall hn) hMint (Eventually.of_forall hpoint)
  have hlim : (∫ x, F₀ x) = y ^ (1 - θ) / (θ - 1) := by
    rw [show F₀ = (Set.Ioi y).indicator (fun x : ℝ => x ^ (-θ)) from rfl,
      integral_indicator measurableSet_Ioi,
      integral_Ioi_rpow_of_lt (by linarith [h.alpha_mem.1] : -θ < -1) hy]
    rw [show -θ + 1 = 1 - θ by ring]
    have hden : θ - 1 ≠ 0 := by linarith [h.alpha_mem.1]
    have hden' : 1 - θ ≠ 0 := by linarith [h.alpha_mem.1]
    field_simp
    ring
  rw [hlim] at ht
  apply ht.congr'
  filter_upwards [(tendsto_B_atTop h).eventually_gt_atTop y] with n hBn
  have hB : 0 < B n := hy.trans hBn
  dsimp only [F]
  rw [integral_indicator measurableSet_Ioc,
    ← intervalIntegral.integral_of_le hBn.le]
  have he : (∫ x in y..B n, ((n : ℝ) * offspringDefect μ (x / B n))⁻¹) =
      (n : ℝ)⁻¹ * ∫ x in y..B n, (offspringDefect μ (x / B n))⁻¹ := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x _
    simp [mul_inv_rev, mul_comm]
  rw [he, intervalIntegral.integral_comp_div (fun u => (offspringDefect μ u)⁻¹) hB.ne']
  simp only [div_self hB.ne', smul_eq_mul, survivalTime]
  ring

end BGW.StableTrees.Survival
