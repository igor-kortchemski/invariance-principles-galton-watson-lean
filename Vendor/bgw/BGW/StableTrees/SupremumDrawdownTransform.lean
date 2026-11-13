/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.SupremumDrawdownClock
public import BGW.StableTrees.SupremumDrawdownEvaluation
public import BGW.StableTrees.SupremumDrawdownAnalytic
import Mathlib.Probability.Independence.Integration
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-! # The scalar supremum transform, including the removable diagonal

Reference: J. Bertoin, *Lévy Processes*, Cambridge University Press, 1996, Chapters IV and VI.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees

/-- Independence and the process transform give the supremum transform identity below
its first singular parameter. -/
theorem supremumLaplace_identity_below {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    {q lam : ℝ} (hq : 0 < q) (hlam : 0 ≤ lam) (hlt : lam < q ^ (1 / θ)) :
    q ^ (1 / θ) * (q - lam ^ θ) * supremumLaplace θ q lam =
      q * (q ^ (1 / θ) - lam) := by
  let := isProbabilityMeasure_expClockLaw θ hq
  have hPhi : 0 < q ^ (1 / θ) := Real.rpow_pos_of_pos hq _
  have hθ0 : 0 < θ := zero_lt_one.trans hθ.1
  have hroot : (q ^ (1 / θ)) ^ θ = q := by
    rw [← Real.rpow_mul hq.le, one_div_mul_cancel hθ0.ne', Real.rpow_one]
  have hc : lam ^ θ < q := by
    rw [← hroot]
    exact Real.rpow_lt_rpow hlam hlt hθ0
  have hS : Measurable (fun p : DLoc × ℝ =>
      Real.exp (-lam * supRunning p.1 p.2.toNNReal)) :=
    (measurable_supRunning_expTime.const_mul (-lam)).exp
  have hR : Measurable (fun p : DLoc × ℝ =>
      Real.exp (lam * supReflected p.1 p.2.toNNReal)) :=
    (measurable_supReflected_expTime.const_mul lam).exp
  have hInd := (indepFun_supRunning_supReflected_expTime hθ hq).comp
    (by fun_prop : Measurable (fun s : ℝ => Real.exp (-lam * s)))
    (by fun_prop : Measurable (fun r : ℝ => Real.exp (lam * r)))
  have he := hInd.integral_fun_mul_eq_mul_integral hS.aestronglyMeasurable
    hR.aestronglyMeasurable
  have hEval : (fun p : DLoc × ℝ => Real.exp (-lam * supRunning p.1 p.2.toNNReal) *
      Real.exp (lam * supReflected p.1 p.2.toNNReal)) =
      (fun p : DLoc × ℝ => Real.exp (-lam * p.1.1 p.2.toNNReal)) := by
    funext p
    rw [← Real.exp_add]
    congr 1
    dsimp [supReflected]
    ring
  have hRI : (∫ p : DLoc × ℝ, Real.exp (lam * supReflected p.1 p.2.toNNReal)
      ∂expClockLaw θ q) = q ^ (1 / θ) / (q ^ (1 / θ) - lam) := by
    have hm : Measurable (fun r : ℝ => Real.exp (lam * r)) := by fun_prop
    rw [← integral_map measurable_supReflected_expTime.aemeasurable hm.aestronglyMeasurable,
      law_supReflected_expTime hθ hq]
    exact (integral_exp_mul_expMeasure hPhi hlt).2
  simp only [Function.comp_apply] at he
  rw [hEval, (integral_exp_neg_eval_expTime hθ hq hlam hlt).2, hRI] at he
  change q / (q - lam ^ θ) = supremumLaplace θ q lam *
    (q ^ (1 / θ) / (q ^ (1 / θ) - lam)) at he
  field_simp [ne_of_gt (sub_pos.mpr hc), ne_of_gt (sub_pos.mpr hlt)] at he
  nlinarith only [he]

/-- The denominator-free supremum identity holds at every positive parameter. -/
theorem supremumLaplace_identity {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    {q lam : ℝ} (hq : 0 < q) (hlam : 0 < lam) :
    q ^ (1 / θ) * (q - lam ^ θ) * supremumLaplace θ q lam =
      q * (q ^ (1 / θ) - lam) :=
  supremumLaplace_identity_of_interval hθ hq
    (fun _ hpos hlt => supremumLaplace_identity_below hθ hq hpos.le hlt) lam hlam

/-- **Scalar supremum transform, off the diagonal.** For every `λ ≥ 0`, `λ ≠ q^{1/θ}`:
`E e^{-λ S_{e_q}} = q (Φ-λ) / (Φ (q-λ^θ))`, `Φ = q^{1/θ}`. -/
theorem integral_exp_neg_supRunning_expTime {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {q lam : ℝ}
    (hq : 0 < q) (hlam : 0 ≤ lam) (hne : lam ≠ q ^ (1 / θ)) :
    ∫ p, Real.exp (-lam * supRunning p.1 p.2.toNNReal) ∂expClockLaw θ q =
      q * (q ^ (1 / θ) - lam) / (q ^ (1 / θ) * (q - lam ^ θ)) := by
  let := isProbabilityMeasure_expClockLaw θ hq
  have hPhi : 0 < q ^ (1 / θ) := Real.rpow_pos_of_pos hq _
  have hθ0 : 0 < θ := zero_lt_one.trans hθ.1
  have hroot : (q ^ (1 / θ)) ^ θ = q := by
    rw [← Real.rpow_mul hq.le, one_div_mul_cancel hθ0.ne', Real.rpow_one]
  have hden : q - lam ^ θ ≠ 0 := by
    apply sub_ne_zero.mpr
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hh := Real.rpow_lt_rpow hlam hlt hθ0
      rw [hroot] at hh
      exact hh.ne'
    · have hh := Real.rpow_lt_rpow hPhi.le hgt hθ0
      rw [hroot] at hh
      exact hh.ne
  rcases eq_or_lt_of_le hlam with rfl | hpos
  · rw [Real.zero_rpow hθ0.ne']
    simp only [neg_zero, zero_mul, Real.exp_zero, integral_const,
      smul_eq_mul, mul_one, sub_zero]
    rw [measureReal_def, measure_univ, ENNReal.toReal_one]
    field_simp [hPhi.ne', hq.ne']
  · apply (eq_div_iff (mul_ne_zero hPhi.ne' hden)).mpr
    have he := supremumLaplace_identity hθ hq hpos
    change supremumLaplace θ q lam * (q ^ (1 / θ) * (q - lam ^ θ)) = _
    nlinarith only [he]

/-- **Diagonal value** `F_q(Φ) = 1/θ` (removable singularity of the formula above). -/
theorem integral_exp_neg_supRunning_expTime_diag {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {q : ℝ}
    (hq : 0 < q) :
    ∫ p, Real.exp (-(q ^ (1 / θ)) * supRunning p.1 p.2.toNNReal) ∂expClockLaw θ q =
      1 / θ := by
  let Phi := q ^ (1 / θ)
  have hPhi : 0 < Phi := Real.rpow_pos_of_pos hq _
  have hθ0 : 0 < θ := zero_lt_one.trans hθ.1
  have hroot : Phi ^ θ = q := by
    dsimp [Phi]
    rw [← Real.rpow_mul hq.le, one_div_mul_cancel hθ0.ne', Real.rpow_one]
  have hL := (analyticAt_supremumLaplace hθ hq hPhi).differentiableAt.hasDerivAt
  have hpow := Real.hasDerivAt_rpow_const (x := Phi) (p := θ) (Or.inl hPhi.ne')
  have hd := ((hasDerivAt_const Phi Phi).mul ((hasDerivAt_const Phi q).sub hpow)).mul hL
  have hr := (hasDerivAt_const Phi q).mul ((hasDerivAt_const Phi Phi).sub (hasDerivAt_id Phi))
  have hEq : (fun l : ℝ => Phi * (q - l ^ θ) * supremumLaplace θ q l) =ᶠ[𝓝 Phi]
      (fun l : ℝ => q * (Phi - l)) := by
    filter_upwards [Ioi_mem_nhds hPhi] with l hl
    exact supremumLaplace_identity hθ hq hl
  have he := hd.unique (hr.congr_of_eventuallyEq hEq)
  change ((0 * (q - Phi ^ θ) + Phi * (0 - θ * Phi ^ (θ - 1))) *
    supremumLaplace θ q Phi + (Phi * (q - Phi ^ θ)) *
      deriv (supremumLaplace θ q) Phi) = (0 * (Phi - Phi) + q * (0 - 1)) at he
  rw [hroot] at he
  simp only [sub_self, zero_mul, mul_zero, zero_add, zero_sub, mul_neg, mul_one] at he
  rw [Real.rpow_sub_one hPhi.ne', hroot] at he
  have hscale : Phi * (θ * (q / Phi)) = θ * q := by
    field_simp
  rw [hscale] at he
  have heq : q * (θ * supremumLaplace θ q Phi) = q * 1 := by
    nlinarith only [he]
  have he' : θ * supremumLaplace θ q Phi = 1 := mul_left_cancel₀ hq.ne' heq
  apply (eq_div_iff hθ0.ne').mpr
  change supremumLaplace θ q Phi * θ = 1
  nlinarith only [he']

end BGW.StableTrees
