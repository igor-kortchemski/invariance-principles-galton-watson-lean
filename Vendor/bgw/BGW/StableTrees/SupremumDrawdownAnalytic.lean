/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.SupremumFactorization
public import Mathlib.Analysis.Analytic.Basic
import Mathlib.Probability.Moments.MGFAnalytic
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-! # Analyticity of the scalar supremum Laplace transform

Reference: J. Bertoin, *Lévy Processes*, Cambridge University Press, 1996, Chapters IV and VI.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees

/-- The scalar Laplace transform of the supremum at the exponential clock. -/
noncomputable def supremumLaplace (θ q lam : ℝ) : ℝ :=
  ∫ p, Real.exp (-lam * supRunning p.1 p.2.toNNReal) ∂expClockLaw θ q

/-- Nonnegative Laplace parameters give a bounded, integrable test of the supremum. -/
theorem integrable_exp_neg_supRunning_expTime {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    {q lam : ℝ} (hq : 0 < q) (hlam : 0 ≤ lam) :
    Integrable (fun p : DLoc × ℝ => Real.exp (-lam * supRunning p.1 p.2.toNNReal))
      (expClockLaw θ q) := by
  let := isProbabilityMeasure_expClockLaw θ hq
  apply Integrable.of_bound
    ((measurable_supRunning_expTime.const_mul (-lam)).exp).aestronglyMeasurable 1
  filter_upwards [ae_nonneg_supRunning_supReflected_expTime hθ hq] with p hp
  rw [Real.norm_of_nonneg (Real.exp_pos _).le]
  exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hlam) hp.1)

/-- The supremum Laplace transform is real analytic at every strictly positive parameter. -/
theorem analyticAt_supremumLaplace {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    {q lam : ℝ} (hq : 0 < q) (hlam : 0 < lam) :
    AnalyticAt ℝ (supremumLaplace θ q) lam := by
  let P := expClockLaw θ q
  let S : DLoc × ℝ → ℝ := fun p => supRunning p.1 p.2.toNNReal
  have hI : Iio (0 : ℝ) ⊆ integrableExpSet S P := by
    intro a ha
    have ha0 : a < 0 := ha
    have hi := integrable_exp_neg_supRunning_expTime hθ hq (lam := -a)
      (neg_nonneg.mpr ha0.le)
    change Integrable (fun p => Real.exp (a * S p)) P
    simpa only [S, P, neg_neg] using hi
  have hinterior : Iio (0 : ℝ) ⊆ interior (integrableExpSet S P) :=
    interior_maximal hI isOpen_Iio
  have hm : AnalyticAt ℝ (mgf S P) (-lam) :=
    analyticAt_mgf (hinterior (show -lam < 0 from neg_neg_of_pos hlam))
  have hn : AnalyticAt ℝ (fun l : ℝ => -l) lam := analyticAt_id.neg
  exact hm.comp hn

private theorem analyticAt_positive_rpow (θ : ℝ) {x : ℝ} (hx : 0 < x) :
    AnalyticAt ℝ (fun l : ℝ => l ^ θ) x := by
  have h : AnalyticAt ℝ (fun l : ℝ => Real.exp (Real.log l * θ)) x :=
    ((analyticAt_log hx).mul
      (analyticAt_const : AnalyticAt ℝ (fun _ : ℝ => θ) x)).rexp
  apply h.congr
  filter_upwards [Ioi_mem_nhds hx] with l hl
  exact (Real.rpow_def_of_pos hl θ).symm

/-- An identity for the supremum transform on the initial interval extends to all positive
parameters after multiplication by the removable denominator. -/
theorem supremumLaplace_identity_of_interval {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    {q : ℝ} (hq : 0 < q)
    (hshort : ∀ lam : ℝ, 0 < lam → lam < q ^ (1 / θ) →
      q ^ (1 / θ) * (q - lam ^ θ) * supremumLaplace θ q lam =
        q * (q ^ (1 / θ) - lam)) :
    ∀ lam : ℝ, 0 < lam →
      q ^ (1 / θ) * (q - lam ^ θ) * supremumLaplace θ q lam =
        q * (q ^ (1 / θ) - lam) := by
  have hPhi : 0 < q ^ (1 / θ) := Real.rpow_pos_of_pos hq _
  have hf : AnalyticOnNhd ℝ
      (fun l : ℝ => q ^ (1 / θ) * (q - l ^ θ) * supremumLaplace θ q l) (Ioi 0) := by
    intro l hl
    exact (analyticAt_const.mul (analyticAt_const.sub (analyticAt_positive_rpow θ hl))).mul
      (analyticAt_supremumLaplace hθ hq hl)
  have hg : AnalyticOnNhd ℝ (fun l : ℝ => q * (q ^ (1 / θ) - l)) (Ioi 0) := by
    intro l _hl
    exact analyticAt_const.mul (analyticAt_const.sub analyticAt_id)
  have hmem : q ^ (1 / θ) / 2 ∈ Ioi (0 : ℝ) := half_pos hPhi
  have he : (fun l : ℝ => q ^ (1 / θ) * (q - l ^ θ) * supremumLaplace θ q l) =ᶠ[
      𝓝 (q ^ (1 / θ) / 2)] (fun l : ℝ => q * (q ^ (1 / θ) - l)) := by
    filter_upwards [Ioo_mem_nhds hmem (half_lt_self hPhi)] with l hl
    exact hshort l hl.1 hl.2
  exact fun l hl => hf.eqOn_of_preconnected_of_eventuallyEq hg
    (convex_Ioi (0 : ℝ)).isPreconnected hmem he hl

end BGW.StableTrees
