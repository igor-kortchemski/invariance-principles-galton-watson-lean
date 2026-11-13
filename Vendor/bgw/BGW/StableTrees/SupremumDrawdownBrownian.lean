/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.SupremumDrawdownTransform
import BGW.StableTrees.StablePassageSubordinatorLaplace

/-! # The Brownian specialization and the non-exponentiality guard

Reference: J. Bertoin, *Lévy Processes*, Cambridge University Press, 1996, Chapters IV and VI.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees

/-- **Brownian case**: for `θ = 2`, `S_{e_q} ~ Exp(√q)` (`Φ = q^{1/2}`). -/
theorem law_supRunning_expTime_two {q : ℝ} (hq : 0 < q) :
    (expClockLaw 2 q).map (fun p : DLoc × ℝ => supRunning p.1 p.2.toNNReal) =
      expMeasure (q ^ (1 / (2 : ℝ))) := by
  let := isProbabilityMeasure_expClockLaw 2 hq
  have hPhi : 0 < q ^ (1 / (2 : ℝ)) := Real.rpow_pos_of_pos hq _
  let := isProbabilityMeasure_expMeasure hPhi
  have hθ : 1 < (2 : ℝ) ∧ (2 : ℝ) ≤ 2 := by norm_num
  have hμ : ((expClockLaw 2 q).map
      (fun p : DLoc × ℝ => supRunning p.1 p.2.toNNReal)) (Iio 0) = 0 := by
    rw [Measure.map_apply measurable_supRunning_expTime measurableSet_Iio,
      measure_eq_zero_iff_ae_notMem]
    filter_upwards [ae_nonneg_supRunning_supReflected_expTime hθ hq] with p hp
    exact not_lt_of_ge hp.1
  have hν : expMeasure (q ^ (1 / (2 : ℝ))) (Iio 0) = 0 := by
    apply measure_mono_null Iio_subset_Iic_self
    rw [← ofReal_cdf, cdf_expMeasure_eq hPhi]
    simp
  apply measure_eq_of_laplace_on_nonneg hμ hν
  intro lam hlam
  have hm : Measurable (fun s : ℝ => Real.exp (-lam * s)) := by fun_prop
  rw [integral_map measurable_supRunning_expTime.aemeasurable hm.aestronglyMeasurable,
    (integral_exp_mul_expMeasure hPhi (c := -lam) (by linarith)).2]
  by_cases heq : lam = q ^ (1 / (2 : ℝ))
  · rw [heq, integral_exp_neg_supRunning_expTime_diag hθ hq]
    field_simp
    ring
  · rw [integral_exp_neg_supRunning_expTime hθ hq hlam.le heq, Real.rpow_two]
    have hsquare : (q ^ (1 / (2 : ℝ))) ^ 2 = q := by
      rw [← Real.rpow_two, ← Real.rpow_mul hq.le]
      norm_num
    have hden : q - lam ^ 2 =
        (q ^ (1 / (2 : ℝ)) - lam) * (q ^ (1 / (2 : ℝ)) + lam) := by
      nlinarith only [hsquare]
    rw [hden, sub_neg_eq_add]
    have hplus : 0 < q ^ (1 / (2 : ℝ)) + lam := add_pos hPhi hlam
    field_simp [hPhi.ne', sub_ne_zero.mpr (Ne.symm heq), hplus.ne']
    nlinarith only [hsquare]

/-- **Guard**: for `θ < 2`, the supremum is not exponential with rate `q^{1/θ}`. -/
theorem law_supRunning_expTime_ne_exp {θ : ℝ} (hθ : 1 < θ ∧ θ < 2) {q : ℝ} (hq : 0 < q) :
    (expClockLaw θ q).map (fun p : DLoc × ℝ => supRunning p.1 p.2.toNNReal) ≠
      expMeasure (q ^ (1 / θ)) := by
  intro hlaw
  have hPhi : 0 < q ^ (1 / θ) := Real.rpow_pos_of_pos hq _
  have hθ0 : 0 < θ := zero_lt_one.trans hθ.1
  have hm : Measurable (fun s : ℝ => Real.exp (-(q ^ (1 / θ)) * s)) := by fun_prop
  have he := congrArg (fun μ : Measure ℝ =>
    ∫ s, Real.exp (-(q ^ (1 / θ)) * s) ∂μ) hlaw
  rw [integral_map measurable_supRunning_expTime.aemeasurable hm.aestronglyMeasurable,
    integral_exp_neg_supRunning_expTime_diag ⟨hθ.1, hθ.2.le⟩ hq,
    (integral_exp_mul_expMeasure hPhi (c := -(q ^ (1 / θ))) (by linarith)).2] at he
  field_simp [hθ0.ne', hPhi.ne'] at he
  nlinarith [hθ.2]

end BGW.StableTrees
