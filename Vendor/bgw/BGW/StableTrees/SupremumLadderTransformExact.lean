/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.SupremumLadderTransformMeanLimit
public import BGW.StableTrees.SupremumLadderTransformExponential
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Exact ascending ladder transform

The finite positive boundary potential identifies the semigroup rate, fixing the
normalization without an adjustable multiplicative constant.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees

/-- **Exact normalization for `q > 0`**: `φ(z) = exp(-z κ(q,λ))`, `c = 1`. -/
theorem supLadderLaplace_eq_of_pos {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {q lam : ℝ} (hq : 0 < q)
    (hlam : 0 ≤ lam) (z : ℝ≥0) :
    supLadderLaplace θ q lam z = Real.exp (-(z : ℝ) * supLadderExponent θ q lam) := by
  obtain ⟨k, hk, hφ⟩ := exists_supLadderLaplace_eq_exp hθ hq.le hlam
  have hpot := lintegral_supLadderLaplace_eq hθ hq.le hlam
  rw [lintegral_supBoundaryPotential hθ hq hlam] at hpot
  have hkpos : 0 < k := by
    by_contra hn
    have he : k = 0 := le_antisymm (not_lt.mp hn) hk
    simp_rw [hφ, he, mul_zero, Real.exp_zero, ENNReal.ofReal_one] at hpot
    have ht : (⊤ : ℝ≥0∞) = ENNReal.ofReal (supLadderExponent θ q lam)⁻¹ := by
      simpa only [lintegral_const, Measure.restrict_apply_univ, Real.volume_Ioi, one_mul]
        using hpot
    exact ENNReal.ofReal_ne_top ht.symm
  have hreal : (∫ z in Ioi (0 : ℝ), Real.exp (-k * z)) = k⁻¹ := by
    rw [integral_exp_mul_Ioi (neg_neg_of_pos hkpos), mul_zero, Real.exp_zero]
    ring
  have hlin : (∫⁻ z in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-k * z))) =
      ENNReal.ofReal k⁻¹ := by
    rw [← ofReal_integral_eq_lintegral_ofReal
      (integrableOn_exp_mul_Ioi (neg_neg_of_pos hkpos) 0)
      (ae_of_all _ fun z => (Real.exp_pos _).le), hreal]
  have hint : (∫⁻ z in Ioi (0 : ℝ),
      ENNReal.ofReal (supLadderLaplace θ q lam z.toNNReal)) = ENNReal.ofReal k⁻¹ := by
    rw [← hlin]
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
    rw [hφ, Real.coe_toNNReal _ hz.le]
    congr 2
    ring
  rw [hint] at hpot
  have hκpos := supLadderExponent_pos hθ hq hlam
  have hr := congrArg ENNReal.toReal hpot
  simp only [ENNReal.toReal_ofReal (inv_nonneg.mpr hk),
    ENNReal.toReal_ofReal (inv_nonneg.mpr hκpos.le)] at hr
  have he : k = supLadderExponent θ q lam := inv_injective hr
  rw [hφ, he]

/-- **Exact transform for all `q, λ ≥ 0`** (including `q = 0` and `(0,0)`). -/
theorem supLadderLaplace_eq {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {q lam : ℝ} (hq : 0 ≤ q)
    (hlam : 0 ≤ lam) (z : ℝ≥0) :
    supLadderLaplace θ q lam z = Real.exp (-(z : ℝ) * supLadderExponent θ q lam) := by
  rcases eq_or_lt_of_le hq with hzero | hpos
  · subst q
    have hκ := Real.continuous_exp.continuousAt.tendsto.comp
      ((tendsto_supLadderExponent_zero hθ hlam).const_mul (-(z : ℝ)))
    have hφ := tendsto_supLadderLaplace_zero_rate hθ hlam z
    apply tendsto_nhds_unique hφ
    apply hκ.congr'
    filter_upwards [self_mem_nhdsWithin] with q hq
    exact (supLadderLaplace_eq_of_pos hθ hq hlam z).symm
  · exact supLadderLaplace_eq_of_pos hθ hpos hlam z

/-- **Diagonal value**: `E exp(-q A_z - q^{1/θ} B_z) = exp(-z θ q^{1-1/θ})`
(from `supLadderExponent_diagonal`). -/
theorem supLadderLaplace_diagonal {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {q : ℝ} (hq : 0 ≤ q)
    (z : ℝ≥0) :
    supLadderLaplace θ q (q ^ (1 / θ)) z = Real.exp (-(z : ℝ) * (θ * q ^ (1 - 1 / θ))) := by
  rw [supLadderLaplace_eq hθ hq (Real.rpow_nonneg hq _) z,
    supLadderExponent_diagonal]

/-- **Joint ladder transform** (normalization `c = 1`)
at every deterministic level `z ≥ 0`, and its two marginals (`κ(q,0) = q^{1-1/θ}`,
`κ(0,λ) = λ^{θ-1}`): `E exp(-q A_z - λ B_z) = exp(-z κ(q, λ))` for `q, λ ≥ 0`.

References: Bertoin, *Lévy Processes*, Chapter VI; Kyprianou, *Fluctuations of Lévy Processes
with Applications*, Chapter 6. -/
theorem integral_exp_neg_supLadder {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (z : ℝ≥0) {q lam : ℝ}
    (hq : 0 ≤ q) (hlam : 0 ≤ lam) :
    (∫ f, Real.exp (-q * (supLadderTime θ z f : ℝ) - lam * supLadderHeight θ z f)
          ∂(stableLocalLaw θ : Measure DLoc) =
        Real.exp (-(z : ℝ) * supLadderExponent θ q lam)) ∧
      (∫ f, Real.exp (-q * (supLadderTime θ z f : ℝ)) ∂(stableLocalLaw θ : Measure DLoc) =
        Real.exp (-(z : ℝ) * q ^ (1 - 1 / θ))) ∧
      (∫ f, Real.exp (-lam * supLadderHeight θ z f) ∂(stableLocalLaw θ : Measure DLoc) =
        Real.exp (-(z : ℝ) * lam ^ (θ - 1))) := by
  refine ⟨supLadderLaplace_eq hθ hq hlam z, ?_, ?_⟩
  · have h := supLadderLaplace_eq hθ hq (le_refl (0 : ℝ)) z
    simpa only [supLadderLaplace, zero_mul, sub_zero,
      supLadderExponent_zero_right hθ hq] using h
  · have h := supLadderLaplace_eq hθ (le_refl (0 : ℝ)) hlam z
    simpa only [supLadderLaplace, neg_zero, zero_mul, zero_sub, ← neg_mul,
      supLadderExponent_zero_left hθ hlam] using h

end BGW.StableTrees
