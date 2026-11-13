/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.SurvivalExpansion
import BGW.StableTrees.Attraction.Norming

/-!
# Stable-scale comparison for the offspring generating function

This file finishes the expansion below index two and in the infinite-variance Gaussian case.
-/

@[expose] public section

open MeasureTheory Filter ProbabilityTheory
open scoped Topology ENNReal

namespace BGW.StableTrees.Survival

open BGW.StableTrees.Attraction
open BGW.StableTrees.Attraction.LaplaceExpansion

private theorem tendsto_natCast_div_norming_sq_of_index_lt {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ}
    (h : StableDomain μ θ B) (hθ : θ < 2) :
    Tendsto (fun n : ℕ => (n : ℝ) / (B n) ^ 2) atTop (𝓝 0) := by
  let ρ : ℝ := 1 / θ
  let p : ℝ := ρ - (ρ - 1 / 2) / 2
  have hθ0 : 0 < θ := by linarith [h.alpha_mem.1]
  have hρ : 1 / 2 < ρ := (one_div_lt_one_div (by norm_num) hθ0).mpr hθ
  have hp : 1 / 2 < p := by dsimp [p]; linarith
  have hγ : 1 - 2 * p < 0 := by linarith
  apply tendsto_zero_of_le_mul_rpow le_rfl (C := 1) hγ
  · filter_upwards [eventually_ge_atTop 1] with n hn
    exact div_nonneg (Nat.cast_nonneg n) (sq_nonneg (B n))
  · filter_upwards [(Scalar.regularlyVaryingSeq h).eventually_rpow_le_le h.monotone h.pos
      (by positivity) (half_pos (sub_pos.mpr hρ)), eventually_ge_atTop 1]
      with n hn hn1
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn1
    have hBn : 0 < B n := h.pos n hn1
    have hlow : (n : ℝ) ^ p ≤ B n := by
      convert hn.1 using 1
    have hcalc : (n : ℝ) / (B n) ^ 2 ≤ (n : ℝ) / ((n : ℝ) ^ p) ^ 2 := by
      apply div_le_div_of_nonneg_left hnR.le (by positivity)
      exact pow_le_pow_left₀ (Real.rpow_nonneg hnR.le p) hlow 2
    apply hcalc.trans
    have heq : ((n : ℝ) ^ p) ^ 2 = (n : ℝ) ^ (2 * p) := by
      rw [← Real.rpow_two, ← Real.rpow_mul hnR.le]
      congr 1
      ring
    have heq' : (n : ℝ) / ((n : ℝ) ^ p) ^ 2 = (n : ℝ) ^ (1 - 2 * p) := by
      rw [heq, Real.rpow_sub hnR, Real.rpow_one]
    rw [heq']
    simp

private theorem tendsto_natCast_div_norming_sq_infiniteVariance {μ : PMF ℕ} {B : ℕ → ℝ}
    (h : StableDomain μ 2 B)
    (hsq : ¬ Integrable (fun z : ℤ => (z : ℝ) ^ 2) (stepLaw μ)) :
    Tendsto (fun n : ℕ => (n : ℝ) / (B n) ^ 2) atTop (𝓝 0) := by
  let ν := stepLaw μ
  let A := norming ν 2
  have hstep : ν {z : ℤ | z < -1} = 0 := stepLaw_lt_neg_one μ
  have hint : Integrable (fun z : ℤ => (z : ℝ)) ν := integrable_stepLaw h.critical
  have hatt : IsStableAttracted ν 2 (mean ν) B := by
    change IsStableAttracted (stepLaw μ) 2 (mean (stepLaw μ)) B
    rw [mean_stepLaw h.critical]
    exact stableDomain_isStableAttracted h
  obtain ⟨hK, hKinf⟩ := DomainCriterion.truncSecondMoment_slowlyVarying_unbounded hatt hint hsq
  have hA : Tendsto A atTop atTop :=
    CanonicalAttraction.gaussian_norming_tendsto_atTop hK hKinf
  have hnum := CanonicalAttraction.gaussian_norming_moment_limit hK hKinf one_pos
  have hden : Tendsto (fun n => truncSecondMoment ν (A n)) atTop atTop := hKinf.comp hA
  have hbase0 := hnum.div_atTop hden
  have hbase : Tendsto (fun n : ℕ => (n : ℝ) / (A n) ^ 2) atTop (𝓝 0) := by
    apply hbase0.congr'
    filter_upwards [hden.eventually_gt_atTop 0] with n hn
    field_simp
    rfl
  have hr : Tendsto (fun n => A n / B n) atTop (𝓝 1) :=
    Norming.norming_isEquivalent ν hstep hint hatt
  have ht := hbase.mul (hr.mul hr)
  simp only [zero_mul] at ht
  apply ht.congr'
  filter_upwards [hA.eventually_gt_atTop 0, (tendsto_B_atTop h).eventually_gt_atTop 0]
    with n hAn hBn
  field_simp

private theorem tendsto_realGF_expansion_of_sq {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ}
    (h : StableDomain μ θ B)
    (hsq : Tendsto (fun n : ℕ => (n : ℝ) / (B n) ^ 2) atTop (𝓝 0))
    {lam : ℝ} (hlam : 0 < lam) :
    Tendsto (fun n : ℕ => (n : ℝ) * (realGF μ (1 - lam / B n) - (1 - lam / B n))) atTop
      (𝓝 (lam ^ θ)) := by
  let u : ℕ → ℝ := fun n => lam / B n
  have hCL := tendsto_centeredLaplace_stableDomain h hlam
  have hu : Tendsto u atTop (𝓝 0) := tendsto_const_nhds.div_atTop (tendsto_B_atTop h)
  have hu0 : ∀ᶠ n in atTop, 0 ≤ u n := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact div_nonneg hlam.le (h.pos n hn).le
  have hu1 : ∀ᶠ n in atTop, u n ≤ 1 := hu.eventually_le_const (by norm_num)
  have hnormsq := hsq.const_mul (4 * lam ^ 2)
  rw [mul_zero] at hnormsq
  have hnormsq' : Tendsto (fun n : ℕ => 4 * ((n : ℝ) * (u n) ^ 2)) atTop (𝓝 0) := by
    apply hnormsq.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hB := (h.pos n hn).ne'
    dsimp only [u]
    field_simp
  have hzero : Tendsto (fun n : ℕ => (n : ℝ) *
      (centeredLaplace (stepLaw μ) (u n) - 1 -
        (realGF μ (1 - u n) - (1 - u n)))) atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ hnormsq'
    filter_upwards [hu0, hu1] with n hn0 hn1
    rw [norm_mul, Real.norm_of_nonneg (Nat.cast_nonneg n)]
    calc
      (n : ℝ) * |centeredLaplace (stepLaw μ) (u n) - 1 -
          (realGF μ (1 - u n) - (1 - u n))| ≤ (n : ℝ) * (4 * (u n) ^ 2) :=
        mul_le_mul_of_nonneg_left (centeredLaplace_realGF_difference_bound μ h.critical hn0 hn1)
          (Nat.cast_nonneg n)
      _ ≤ 4 * ((n : ℝ) * (u n) ^ 2) := by ring_nf; exact le_rfl
  have ht := hCL.sub hzero
  have ht' : Tendsto (fun n : ℕ =>
      (n : ℝ) * (realGF μ (1 - lam / B n) - (1 - lam / B n))) atTop
      (𝓝 (lam ^ θ - 0)) := by
    apply ht.congr
    intro n
    dsimp only [u]
    ring
  simpa only [sub_zero] using ht'

/-- `n (g(1 - λ/B_n) - (1 - λ/B_n)) → λ^θ` for every `λ > 0`. -/
theorem tendsto_realGF_expansion {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ} (h : StableDomain μ θ B)
    {lam : ℝ} (hlam : 0 < lam) :
    Tendsto (fun n : ℕ => (n : ℝ) * (realGF μ (1 - lam / B n) - (1 - lam / B n))) atTop
      (𝓝 (lam ^ θ)) := by
  by_cases hsq : Integrable (fun z : ℤ => (z : ℝ) ^ 2) (stepLaw μ)
  · have hθ : θ = 2 := by
      have hatt := stableDomain_isStableAttracted h
      exact DomainCriterion.index_eq_two_of_integrable_sq hatt (integrable_stepLaw h.critical) hsq
    subst θ
    have hCL := tendsto_centeredLaplace_stableDomain h hlam
    have hzero := tendsto_realGF_difference_zero_finiteVariance h hsq hlam
    have ht := hCL.sub hzero
    have ht' : Tendsto (fun n : ℕ =>
        (n : ℝ) * (realGF μ (1 - lam / B n) - (1 - lam / B n))) atTop
        (𝓝 (lam ^ (2 : ℝ) - 0)) := by
      apply ht.congr
      intro n
      ring
    simpa only [sub_zero] using ht'

  · rcases lt_or_eq_of_le h.alpha_mem.2 with hθ | hθ
    · exact tendsto_realGF_expansion_of_sq h (tendsto_natCast_div_norming_sq_of_index_lt h hθ) hlam
    · subst θ
      exact tendsto_realGF_expansion_of_sq h
        (tendsto_natCast_div_norming_sq_infiniteVariance h hsq) hlam

end BGW.StableTrees.Survival
