/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.SupremumLadderTransformOccupation
public import BGW.StableTrees.SupremumLadderTransformTail

/-!
# Finite weighted clock integrals

Half-rate potentials justify conversion of the cumulative Tonelli identities to real
integrals. All integrability assertions precede the corresponding real identities.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees

/-- A nonnegative measurable integral is determined by its finite extended integral.

Reference: Bertoin, *Lévy Processes*, Chapter VI. -/
theorem integrable_of_lintegral_eq_ofReal {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f : α → ℝ} (hf : AEStronglyMeasurable f μ)
    (h0 : 0 ≤ᵐ[μ] f) {a : ℝ}
    (he : (∫⁻ x, ENNReal.ofReal (f x) ∂μ) = ENNReal.ofReal a) : Integrable f μ :=
  ⟨hf, (hasFiniteIntegral_iff_ofReal h0).mpr (he ▸ ENNReal.ofReal_lt_top)⟩

/-- The exponential Stieltjes potential of occupation is the ordinary discounted occupation.

Reference: Bertoin, *Lévy Processes*, Chapter VI. -/
theorem integral_exp_supOccupation_clock {q ε : ℝ} (hq : 0 < q) (hε : 0 < ε)
    (f : DLoc) (hf : f.1 0 = 0) :
    IntegrableOn (fun t : ℝ => Real.exp (-q * t)) (Ioi 0)
        (pathStieltjes (supOccupation ε f)).measure ∧
      (∫ t in Ioi (0 : ℝ), Real.exp (-q * t)
        ∂(pathStieltjes (supOccupation ε f)).measure) = supAuxOccupationTail q ε 0 f := by
  have he := lintegral_supOccupation_supWeight hq (le_refl (0 : ℝ)) hε f hf
  simp only [zero_mul, sub_zero] at he
  have hi := integrableOn_supAuxKernel_exp hq hε 0 f
  have hright : (∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal
      (Real.exp (-q * t) * supOccKernel ε (supReflected f t.toNNReal))) =
      ENNReal.ofReal (supAuxOccupationTail q ε 0 f) := by
    simp_rw [← supReflectedFrom_zero_apply hf]
    exact (ofReal_integral_eq_lintegral_ofReal hi
      (ae_of_all _ fun t => mul_nonneg (Real.exp_pos _).le
        (supOccKernel_mem_Icc hε _).1)).symm
  rw [hright] at he
  have h0 : ∀ᵐ t ∂((pathStieltjes (supOccupation ε f)).measure.restrict (Ioi (0 : ℝ))),
      0 ≤ Real.exp (-q * t) := ae_of_all _ fun t => (Real.exp_pos _).le
  have hci := integrable_of_lintegral_eq_ofReal (by fun_prop) h0 he
  refine ⟨hci, ?_⟩
  rw [← ofReal_integral_eq_lintegral_ofReal hci h0] at he
  have h := congrArg ENNReal.toReal he
  have ht0 : 0 ≤ supAuxOccupationTail q ε 0 f := integral_nonneg fun t =>
    mul_nonneg (Real.exp_pos _).le (supOccKernel_mem_Icc hε _).1
  simpa only [ENNReal.toReal_ofReal (integral_nonneg fun t => (Real.exp_pos _).le),
    ENNReal.toReal_ofReal ht0] using h

/-- A finite half-rate clock potential makes the weighted clock and cumulative integrals
integrable and identifies their real values.

Reference: Bertoin, *Lévy Processes*, Chapter VI. -/
theorem integral_supWeight_eq_cumulative {q lam : ℝ} (hq : 0 < q) (hlam : 0 ≤ lam)
    {f : DLoc} (hf : f.1 0 = 0) {m : ℝ≥0 → ℝ}
    (hm : Monotone m ∧ Continuous m) (hm0 : m 0 = 0)
    (hi : IntegrableOn (fun t : ℝ => Real.exp (-(q / 2) * t)) (Ioi 0)
      (pathStieltjes m).measure) :
    IntegrableOn (fun t : ℝ => Real.exp (-q * t - lam * supRunning f t.toNNReal)) (Ioi 0)
        (pathStieltjes m).measure ∧
      (∫ t in Ioi (0 : ℝ), Real.exp (-q * t - lam * supRunning f t.toNNReal)
        ∂(pathStieltjes m).measure) =
      ∫ s in Ioi (0 : ℝ), m s.toNNReal
        ∂(supWeightStieltjes q lam hq.le hlam f).measure := by
  have hmi := (integrable_clock_and_integral_tail_le hm hm0
    (supWeightStieltjes q lam hq.le hlam f).measure hq
    (fun t ht => supWeightStieltjes_measure_Ioi_le hq hlam hf ht) hi).1
  have hWm : Measurable (fun t : ℝ => Real.exp (-q * t - lam * supRunning f t.toNNReal)) :=
    ((measurable_const.mul measurable_id).sub
      (measurable_const.mul ((monotone_supRunning f).measurable.comp
        measurable_real_toNNReal))).exp
  have hWi : IntegrableOn
      (fun t : ℝ => Real.exp (-q * t - lam * supRunning f t.toNNReal)) (Ioi 0)
      (pathStieltjes m).measure := by
    apply hi.mono' hWm.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    apply Real.exp_le_exp.mpr
    have hs : 0 ≤ supRunning f t.toNNReal := by
      simpa only [hf] using eval_le_supRunning f (u := 0) (zero_le : 0 ≤ t.toNNReal)
    nlinarith [mul_nonneg hlam hs, mul_nonneg hq.le ht.le]
  refine ⟨hWi, ?_⟩
  have he := pathStieltjes_lintegral_supWeight hq hlam hf hm hm0
  have hn (s : ℝ) : 0 ≤ m s.toNNReal := by
    simpa only [hm0] using hm.1 (zero_le : 0 ≤ s.toNNReal)
  rw [← ofReal_integral_eq_lintegral_ofReal hWi (ae_of_all _ fun t => (Real.exp_pos _).le),
    ← ofReal_integral_eq_lintegral_ofReal hmi (ae_of_all _ hn)] at he
  have h := congrArg ENNReal.toReal he
  simpa only [ENNReal.toReal_ofReal (integral_nonneg fun t => (Real.exp_pos _).le),
    ENNReal.toReal_ofReal (integral_nonneg hn)] using h

end BGW.StableTrees
