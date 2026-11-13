/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.SupremumAuxLocalTimeOccupation
public import BGW.StableTrees.SupremumAuxLocalTimeLaplace

/-!
# Ordinary primitive formula for discounted occupation

The time kernel is bounded at each positive cutoff. Tonelli's cumulative formula therefore
identifies the discounted occupation tail with the discounted primitive, path by path.

## References

* J. Bertoin, *Lévy Processes*, Cambridge University Press, 1996, Chapter IV.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees

/-- The reflected kernel is integrable on every bounded half-open time interval. -/
theorem integrableOn_supAuxKernel_Ioc {ε : ℝ} (hε : 0 < ε) (f : DLoc) (a b : ℝ) :
    IntegrableOn (fun t => supOccKernel ε (supReflectedFrom 0 f t.toNNReal)) (Ioc a b) := by
  have hfconst : Measurable (fun _ : ℝ => f) := measurable_const
  have hm := (measurable_supAuxKernel ε).comp (measurable_id.prodMk hfconst)
  dsimp only [Function.comp_def] at hm
  apply (integrableOn_const (C := ε⁻¹) (by simp)).mono' hm.aestronglyMeasurable
  filter_upwards with t
  rw [Real.norm_eq_abs, abs_of_nonneg (supOccKernel_mem_Icc hε _).1]
  exact (supOccKernel_mem_Icc hε _).2

/-- An increment of the cumulative occupation is the time kernel integral on that interval. -/
theorem supOccupation_sub_eq_integral {ε : ℝ} (hε : 0 < ε) (f : DLoc) (hf : f.1 0 = 0)
    {s t : ℝ≥0} (hst : s ≤ t) :
    supOccupation ε f t - supOccupation ε f s =
      ∫ u in Ioc (s : ℝ) t, supOccKernel ε (supReflectedFrom 0 f u.toNNReal) := by
  have hh := setIntegral_union (Ioc_disjoint_Ioc_of_le (le_refl (s : ℝ))) measurableSet_Ioc
    (integrableOn_supAuxKernel_Ioc hε f 0 s) (integrableOn_supAuxKernel_Ioc hε f s t)
  rw [Ioc_union_Ioc_eq_Ioc s.coe_nonneg (NNReal.coe_le_coe.mpr hst)] at hh
  rw [supOccupation_eq_integral_supOccKernel f hf t,
    supOccupation_eq_integral_supOccKernel f hf s]
  linarith only [hh]

/-- Discounted occupation tails are discounted cumulative increments, path by path. -/
theorem supAuxOccupationTail_eq_cumulative {q ε : ℝ} (hq : 0 < q) (hε : 0 < ε)
    (f : DLoc) (hf : f.1 0 = 0) (s : ℝ≥0) :
    supAuxOccupationTail q ε s f =
      q * ∫ t in Ioi (s : ℝ), Real.exp (-q * t) *
        (supOccupation ε f t.toNNReal - supOccupation ε f s) := by
  have hfconst : Measurable (fun _ : ℝ => f) := measurable_const
  have hm := (measurable_supAuxKernel ε).comp (measurable_id.prodMk hfconst)
  dsimp only [Function.comp_def] at hm
  have he := (integral_exp_mul_eq_primitive hm
    (fun t => (supOccKernel_mem_Icc hε _).1) hq (s : ℝ)
    (integrableOn_supAuxKernel_Ioc hε f s) (integrableOn_supAuxKernel_exp hq hε s f)).2
  refine he.trans (congrArg (fun x : ℝ => q * x) ?_)
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have hst : s ≤ t.toNNReal := by
    apply NNReal.coe_le_coe.mp
    rw [Real.coe_toNNReal _ (s.coe_nonneg.trans ht.le)]
    exact ht.le
  rw [supOccupation_sub_eq_integral hε f hf hst,
    Real.coe_toNNReal _ (s.coe_nonneg.trans ht.le)]
  simp only [id_eq]

end BGW.StableTrees
