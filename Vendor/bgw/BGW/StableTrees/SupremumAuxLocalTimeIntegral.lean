/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.SupremumAuxLocalTimeStieltjes
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Discounted integrals of continuous clock paths

A Fubini argument relates the actual Stieltjes integral to an integral of clock increments.
Integrability of the latter is an explicit hypothesis and yields integrability of the former;
no value of a totalized, potentially nonintegrable real integral is used as an estimate.

## References

* J. Bertoin, *Lévy Processes*, Cambridge University Press, 1996, Chapter IV.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal

namespace BGW.StableTrees

/-- A discounted cumulative-integral bound gives finiteness and the Fubini formula for the
actual Stieltjes future integral of a continuous monotone clock. -/
theorem pathStieltjes_integral_exp {m : ℝ≥0 → ℝ} (hm : Monotone m ∧ Continuous m)
    {q : ℝ} (hq : 0 < q) (s : ℝ≥0)
    (hi : IntegrableOn (fun t : ℝ => Real.exp (-q * t) * (m t.toNNReal - m s))
      (Ioi (s : ℝ))) :
    IntegrableOn (fun t => Real.exp (-q * t)) (Ioi (s : ℝ)) (pathStieltjes m).measure ∧
      (∫ t in Ioi (s : ℝ), Real.exp (-q * t) ∂(pathStieltjes m).measure) =
        q * ∫ t in Ioi (s : ℝ), Real.exp (-q * t) * (m t.toNNReal - m s) := by
  let μ := (pathStieltjes m).measure.restrict (Ioi (s : ℝ))
  let ν := volume.restrict (Ioi (s : ℝ))
  let k : ℝ × ℝ → ℝ := fun p => if p.1 ≤ p.2 then Real.exp (-q * p.2) else 0
  have hkm : Measurable k :=
    (Real.measurable_exp.comp (measurable_const.mul measurable_snd)).ite
      (measurableSet_le measurable_fst measurable_snd) measurable_const
  have hk0 (p : ℝ × ℝ) : 0 ≤ k p := by
    dsimp [k]
    split_ifs <;> positivity
  have hslice (u : ℝ) : Integrable (fun t => k (t, u)) μ := by
    change Integrable ((Iic u).indicator (fun _ : ℝ => Real.exp (-q * u))) μ
    apply integrable_indicator_iff measurableSet_Iic |>.mpr
    exact integrableOn_const (by
      show μ (Iic u) ≠ ⊤
      rw [Measure.restrict_apply measurableSet_Iic, Iic_inter_Ioi,
        pathStieltjes_measure_Ioc hm]
      exact ENNReal.ofReal_ne_top)
  have hsliceeq (u : ℝ) (hu : (s : ℝ) < u) :
      (∫ t, k (t, u) ∂μ) = Real.exp (-q * u) * (m u.toNNReal - m s) := by
    change (∫ t, (Iic u).indicator (fun _ : ℝ => Real.exp (-q * u)) t ∂μ) = _
    rw [integral_indicator_const _ measurableSet_Iic, smul_eq_mul,
      measureReal_restrict_apply measurableSet_Iic, Iic_inter_Ioi,
      measureReal_def, pathStieltjes_measure_Ioc hm, Real.toNNReal_coe,
      ENNReal.toReal_ofReal, mul_comm]
    apply sub_nonneg.mpr
    apply hm.1
    apply NNReal.coe_le_coe.mp
    rw [Real.coe_toNNReal _ (s.coe_nonneg.trans hu.le)]
    exact hu.le
  have hki : Integrable (fun p : ℝ × ℝ => k (p.2, p.1)) (ν.prod μ) := by
    apply (integrable_prod_iff (hkm.comp measurable_swap).aestronglyMeasurable).2
    refine ⟨ae_of_all _ hslice, ?_⟩
    apply hi.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hn : (fun t => ‖k (t, u)‖) = fun t => k (t, u) := by
      funext t
      exact (Real.norm_eq_abs _).trans (abs_of_nonneg (hk0 _))
    change Real.exp (-q * u) * (m u.toNNReal - m s) = ∫ t, ‖k (t, u)‖ ∂μ
    rw [hn]
    exact (hsliceeq u hu).symm
  have hprod : Integrable k (μ.prod ν) := by
    simpa only [Function.comp_def, Prod.swap, Prod.eta] using hki.swap
  have hinner (t : ℝ) (ht : (s : ℝ) < t) :
      (∫ u, k (t, u) ∂ν) = Real.exp (-q * t) / q := by
    change (∫ u, (Ici t).indicator (fun u => Real.exp (-q * u)) u ∂ν) = _
    rw [integral_indicator measurableSet_Ici, Measure.restrict_restrict measurableSet_Ici,
      inter_eq_left.mpr (Ici_subset_Ioi.mpr ht), integral_Ici_eq_integral_Ioi,
      integral_exp_mul_Ioi (neg_neg_of_pos hq)]
    ring
  have heint : Integrable (fun t => Real.exp (-q * t) / q) μ := by
    apply hprod.integral_prod_left.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact hinner t ht
  refine ⟨?_, ?_⟩
  · change Integrable (fun t => Real.exp (-q * t)) μ
    simpa only [div_mul_cancel₀ _ hq.ne'] using heint.mul_const q
  · have hswap := integral_integral_swap (f := fun t u : ℝ => k (t, u)) hprod
    have hleft : (∫ t, ∫ u, k (t, u) ∂ν ∂μ) =
        (∫ t, Real.exp (-q * t) ∂μ) / q := by
      rw [← integral_div]
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact hinner t ht
    have hright : (∫ u, ∫ t, k (t, u) ∂μ ∂ν) =
        ∫ u, Real.exp (-q * u) * (m u.toNNReal - m s) ∂ν := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      exact hsliceeq u hu
    rw [hleft, hright] at hswap
    exact (div_eq_iff hq.ne').mp hswap |>.trans (mul_comm _ _)

end BGW.StableTrees
