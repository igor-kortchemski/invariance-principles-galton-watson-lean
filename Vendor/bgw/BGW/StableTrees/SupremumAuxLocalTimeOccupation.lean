/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.SupremumAuxLocalTimeBasic
public import BGW.StableTrees.SupremumPotential
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import BGW.Probability.DoobL2ResolventMoment

/-!
# Discounted occupation bounds before recurrence

The reflected resolvent is an unnormalised time integral. Its uniform bound controls
first moments of the cumulative occupations at an arbitrary positive rate.

## References

* J. Bertoin, *Lévy Processes*, Cambridge University Press, 1996, Chapter IV.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod
open BGW.Probability

namespace BGW.StableTrees

/-- The ordinary time integral of the discounted reflected occupation kernel. -/
noncomputable def supAuxOccupationTail (q ε : ℝ) (s : ℝ≥0) (f : DLoc) : ℝ :=
  ∫ t in Ioi (s : ℝ), Real.exp (-q * t) * supOccKernel ε (supReflectedFrom 0 f t.toNNReal)

/-- The reflected occupation kernel is jointly measurable in real time and path. -/
theorem measurable_supAuxKernel (ε : ℝ) :
    Measurable (fun p : ℝ × DLoc => supOccKernel ε (supReflectedFrom 0 p.2 p.1.toNNReal)) :=
  (measurable_supOccKernel ε).comp (measurable_supReflectedFrom_uncurry.comp
    (measurable_const.prodMk (measurable_snd.prodMk
      (measurable_real_toNNReal.comp measurable_fst))))

/-- The discounted occupation tail is measurable for every rate and cutoff. -/
theorem measurable_supAuxOccupationTail (q ε : ℝ) (s : ℝ≥0) :
    Measurable (supAuxOccupationTail q ε s) := by
  exact (measurable_integral_tail
    ((Real.measurable_exp.comp (measurable_const.mul measurable_fst)).mul
      (measurable_supAuxKernel ε))).comp (measurable_const.prodMk measurable_id)

/-- A positive cutoff has an integrable discounted kernel on the time-path product. -/
theorem integrable_supAuxKernel_exp {θ q ε : ℝ} (hq : 0 < q) (hε : 0 < ε) (s : ℝ≥0) :
    Integrable (fun p : ℝ × DLoc =>
      Real.exp (-q * p.1) * supOccKernel ε (supReflectedFrom 0 p.2 p.1.toNNReal))
      ((volume.restrict (Ioi (s : ℝ))).prod (stableLocalLaw θ : Measure DLoc)) := by
  exact integrable_exp_mul_bounded_prod (measurable_supAuxKernel ε) (neg_neg_of_pos hq)
    (fun p => by
      rw [abs_of_nonneg (supOccKernel_mem_Icc hε _).1]
      exact (supOccKernel_mem_Icc hε _).2)

/-- The discounted occupation tail is integrable under the local stable law. -/
theorem integrable_supAuxOccupationTail (θ : ℝ) {q ε : ℝ} (hq : 0 < q) (hε : 0 < ε)
    (s : ℝ≥0) :
    Integrable (supAuxOccupationTail q ε s) (stableLocalLaw θ : Measure DLoc) :=
  (integrable_supAuxKernel_exp (θ := θ) hq hε s).integral_prod_right

/-- At zero the occupation tail has exactly the `supOccupationResolvent` mean,
without a rate factor. -/
theorem integral_supAuxOccupationTail_zero (θ q ε : ℝ) :
    ∫ f, supAuxOccupationTail q ε 0 f ∂(stableLocalLaw θ : Measure DLoc) =
      supOccupationResolvent θ q ε 0 := by
  simp only [supAuxOccupationTail, supOccupationResolvent, reflectedResolvent,
    Real.toNNReal_zero, NNReal.coe_zero]

/-- Discounted occupation kernels are integrable on every individual path. -/
theorem integrableOn_supAuxKernel_exp {q ε : ℝ} (hq : 0 < q) (hε : 0 < ε)
    (s : ℝ≥0) (f : DLoc) :
    IntegrableOn (fun t => Real.exp (-q * t) *
      supOccKernel ε (supReflectedFrom 0 f t.toNNReal)) (Ioi (s : ℝ)) := by
  have hd := (integrableOn_exp_mul_Ioi (neg_neg_of_pos hq) (s : ℝ)).mul_const ε⁻¹
  apply hd.mono' (by
    exact ((Real.measurable_exp.comp (measurable_const.mul measurable_id)).mul
      ((measurable_supAuxKernel ε).comp
        (measurable_id.prodMk measurable_const))).aestronglyMeasurable)
  filter_upwards with t
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _),
    abs_of_nonneg (supOccKernel_mem_Icc hε _).1]
  exact mul_le_mul_of_nonneg_left (supOccKernel_mem_Icc hε _).2 (Real.exp_pos _).le

/-- Every fixed-time occupation is integrable, using its deterministic cutoff bound. -/
theorem integrable_supOccupation (θ : ℝ) {ε : ℝ} (hε : 0 < ε) (T : ℝ≥0) :
    Integrable (fun f : DLoc => supOccupation ε f T) (stableLocalLaw θ : Measure DLoc) := by
  apply Integrable.of_bound
    ((measurable_supOccupation_uncurry.comp
      (measurable_const.prodMk (measurable_const.prodMk measurable_id))).aestronglyMeasurable)
    (ε⁻¹ * T)
  filter_upwards with f
  change ‖supOccupation ε f T‖ ≤ ε⁻¹ * T
  rw [Real.norm_eq_abs, abs_of_nonneg (supOccupation_nonneg hε.le f T)]
  have hh := (supOccupation_sub_mem hε f (zero_le : (0 : ℝ≥0) ≤ T)).2
  simpa only [supOccupation_zero, sub_zero, NNReal.coe_zero] using hh

/-- Removing the discount on a finite interval costs at most `exp (q T)`. -/
theorem supOccupation_le_exp_mul_tail {q ε : ℝ} (hq : 0 < q) (hε : 0 < ε)
    (f : DLoc) (hf : f.1 0 = 0) (T : ℝ≥0) :
    supOccupation ε f T ≤ Real.exp (q * T) * supAuxOccupationTail q ε 0 f := by
  let k := fun t : ℝ => supOccKernel ε (supReflectedFrom 0 f t.toNNReal)
  have hki : IntegrableOn k (Ioc (0 : ℝ) T) := by
    have hfconst : Measurable (fun _ : ℝ => f) := measurable_const
    have hm := (measurable_supAuxKernel ε).comp (measurable_id.prodMk hfconst)
    dsimp only [Function.comp_def] at hm
    apply (integrableOn_const (C := ε⁻¹) (by simp)).mono' hm.aestronglyMeasurable
    filter_upwards with t
    rw [Real.norm_eq_abs, abs_of_nonneg (supOccKernel_mem_Icc hε _).1]
    exact (supOccKernel_mem_Icc hε _).2
  have hwi := integrableOn_supAuxKernel_exp hq hε 0 f
  have hwic : IntegrableOn (fun t => Real.exp (-q * t) * k t) (Ioc (0 : ℝ) T) :=
    hwi.mono_set Ioc_subset_Ioi_self
  rw [supOccupation_eq_integral_supOccKernel f hf T]
  calc
    _ ≤ ∫ t in Ioc (0 : ℝ) T, Real.exp (q * T) * (Real.exp (-q * t) * k t) := by
      apply integral_mono_ae hki (hwic.const_mul _)
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      have he : 1 ≤ Real.exp (q * T) * Real.exp (-q * t) := by
        rw [← Real.exp_add, Real.one_le_exp_iff]
        nlinarith [ht.2]
      simpa only [mul_assoc, one_mul] using
        mul_le_mul_of_nonneg_right he (supOccKernel_mem_Icc hε _).1
    _ ≤ Real.exp (q * T) * supAuxOccupationTail q ε 0 f := by
      rw [integral_const_mul]
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      exact setIntegral_mono_set hwi
        (ae_of_all _ fun t => mul_nonneg (Real.exp_pos _).le (supOccKernel_mem_Icc hε _).1)
        (Eventually.of_forall Ioc_subset_Ioi_self)

/-- An arbitrary positive resolvent rate gives a cutoff-uniform first-moment growth bound. -/
theorem integral_supOccupation_le_exp {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {q ε : ℝ}
    (hq : 0 < q) (hε : 0 < ε) (T : ℝ≥0) :
    (∫ f, supOccupation ε f T ∂(stableLocalLaw θ : Measure DLoc)) ≤
      Real.exp (q * T) * (q ^ (1 / θ) / q) := by
  calc
    _ ≤ ∫ f, Real.exp (q * T) * supAuxOccupationTail q ε 0 f
        ∂(stableLocalLaw θ : Measure DLoc) := by
      apply integral_mono_ae (integrable_supOccupation θ hε T)
        ((integrable_supAuxOccupationTail θ hq hε 0).const_mul _)
      filter_upwards [ae_eval_zero_stableLocalLaw hθ] with f hf
      exact supOccupation_le_exp_mul_tail hq hε f hf T
    _ = Real.exp (q * T) * supOccupationResolvent θ q ε 0 := by
      rw [integral_const_mul, integral_supAuxOccupationTail_zero]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (supOccupationResolvent_mem_Icc hθ hq hε 0).2 (Real.exp_pos _).le

end BGW.StableTrees
