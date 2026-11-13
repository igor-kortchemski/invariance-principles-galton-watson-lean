/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.DiscreteHeightApproxRenewalBound
import Mathlib.Analysis.Calculus.Deriv.Slope
import BGW.StableTrees.SurvivalBasic

/-!
# Stable scaling of the weak ladder renewal bound

A fixed positive Laplace parameter controls the moving natural ceiling. The
normalized offspring PGF gap supplies the denominator asymptotic.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal Classical
open BGW.StableTrees.DiscreteForest

namespace BGW.StableTrees.DiscreteHeightApprox

/-- Dividing a natural ceiling at a diverging scale removes the rounding error. -/
theorem tendsto_ceil_scale {B : ℕ → ℝ} (hB : Tendsto B atTop atTop)
    {ε : ℝ} (hε : 0 ≤ ε) :
    Tendsto (fun n : ℕ => (⌈ε * B n⌉₊ : ℝ) / B n) atTop (𝓝 ε) := by
  have hpos := hB.eventually_gt_atTop 0
  have hinv : Tendsto (fun n : ℕ => 1 / B n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hB
  have hup : Tendsto (fun n : ℕ => ε + 1 / B n) atTop (𝓝 ε) := by
    simpa only [add_zero] using tendsto_const_nhds.add hinv
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup
  · filter_upwards [hpos] with n hn
    exact (le_div_iff₀ hn).mpr (Nat.le_ceil (ε * B n))
  · filter_upwards [hpos] with n hn
    calc
      _ ≤ (ε * B n + 1) / B n :=
        div_le_div_of_nonneg_right (Nat.ceil_lt_add_one (mul_nonneg hε hn.le)).le hn.le
      _ = _ := by field_simp

/-- The elementary exponential difference has its normalized first-order limit. -/
theorem tendsto_norming_one_sub_exp {B : ℕ → ℝ} (hB : Tendsto B atTop atTop)
    {lam : ℝ} (hlam : 0 < lam) :
    Tendsto (fun n : ℕ => B n * (1 - Real.exp (-lam / B n))) atTop (𝓝 lam) := by
  let v (n : ℕ) : ℝ := -lam / B n
  have hv : Tendsto v atTop (𝓝 0) := tendsto_const_nhds.div_atTop hB
  have hpos := hB.eventually_gt_atTop 0
  have hvne : ∀ᶠ n in atTop, v n ≠ 0 := by
    filter_upwards [hpos] with n hn
    exact div_ne_zero (neg_ne_zero.mpr hlam.ne') hn.ne'
  have hv' : Tendsto v atTop (𝓝[≠] 0) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨hv, hvne⟩
  have hd := (Real.hasDerivAt_exp 0).tendsto_slope_zero.comp hv'
  simp only [Function.comp_def, zero_add, Real.exp_zero, smul_eq_mul] at hd
  have ht := hd.const_mul lam
  rw [mul_one] at ht
  apply ht.congr'
  filter_upwards [hpos] with n hn
  dsimp only [v]
  field_simp [hn.ne', hlam.ne']
  ring

/-- The exponential renewal majorant has its stable-domain limit at every fixed band. -/
theorem limsup_scaled_weakLadderRenewal_le {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ}
    (h : StableDomain μ θ B) {ε : ℝ} (hε : 0 < ε) :
    limsup (fun n : ℕ => ENNReal.ofReal ((B n / (n : ℝ)) *
      (weakLadderRenewal μ ⌈ε * B n⌉₊).toReal)) atTop ≤
        ENNReal.ofReal (Real.exp 1 * ε ^ (θ - 1)) := by
  let lam := 1 / ε
  have hlam : 0 < lam := one_div_pos.mpr hε
  let R (n : ℕ) : ℝ :=
    Real.exp (lam * (⌈ε * B n⌉₊ : ℝ) / B n) *
      (B n * (1 - Real.exp (-lam / B n))) /
        ((n : ℝ) * (offspringPGFReal μ (Real.exp (-lam / B n)) - Real.exp (-lam / B n)))
  have hB := Survival.tendsto_B_atTop h
  have hceil := (tendsto_ceil_scale hB hε.le).const_mul lam
  have he : Tendsto (fun n : ℕ => Real.exp (lam * (⌈ε * B n⌉₊ : ℝ) / B n)) atTop
      (𝓝 (Real.exp (lam * ε))) := by
    apply (Real.continuous_exp.continuousAt.tendsto.comp hceil).congr
    intro n
    change Real.exp (lam * ((⌈ε * B n⌉₊ : ℝ) / B n)) =
      Real.exp (lam * (⌈ε * B n⌉₊ : ℝ) / B n)
    congr 1
    ring
  have hnum := tendsto_norming_one_sub_exp hB hlam
  have hden := norming_offspringPGF_gap h hlam
  have hR : Tendsto R atTop (𝓝 (Real.exp 1 * ε ^ (θ - 1))) := by
    have ht := (he.mul hnum).div hden (Real.rpow_pos_of_pos hlam θ).ne'
    have hc : Real.exp (lam * ε) * lam / lam ^ θ = Real.exp 1 * ε ^ (θ - 1) := by
      dsimp only [lam]
      rw [one_div_mul_cancel hε.ne', Real.rpow_sub hε, Real.rpow_one,
        one_div, Real.inv_rpow hε.le, div_inv_eq_mul]
      ring
    rw [hc] at ht
    exact ht
  have hbound : ∀ᶠ n : ℕ in atTop,
      (B n / (n : ℝ)) * (weakLadderRenewal μ ⌈ε * B n⌉₊).toReal ≤ R n := by
    have hdenpos := hden.eventually (lt_mem_nhds (Real.rpow_pos_of_pos hlam θ))
    filter_upwards [eventually_ge_atTop 1, hdenpos] with n hn hdn
    have hBn := h.pos n hn
    have hnR : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
    have hgap : 0 < offspringPGFReal μ (Real.exp (-lam / B n)) - Real.exp (-lam / B n) := by
      nlinarith
    have hb := weakLadderRenewal_toReal_le_exp μ h.critical h.nondegenerate ⌈ε * B n⌉₊
      (div_pos hlam hBn)
    have hb' := mul_le_mul_of_nonneg_left hb (div_nonneg hBn.le hnR.le)
    refine hb'.trans_eq ?_
    dsimp only [R]
    have hexp : (lam / B n) * (⌈ε * B n⌉₊ : ℝ) = lam * (⌈ε * B n⌉₊ : ℝ) / B n := by ring
    rw [hexp]
    simp only [neg_div]
    field_simp [hBn.ne', hnR.ne', hgap.ne']
  have hENN : Tendsto (fun n : ℕ => ENNReal.ofReal (R n)) atTop
      (𝓝 (ENNReal.ofReal (Real.exp 1 * ε ^ (θ - 1)))) :=
    ENNReal.continuous_ofReal.continuousAt.tendsto.comp hR
  exact (limsup_le_limsup (hbound.mono fun n hn => ENNReal.ofReal_le_ofReal hn)).trans_eq
    hENN.limsup_eq

end BGW.StableTrees.DiscreteHeightApprox
