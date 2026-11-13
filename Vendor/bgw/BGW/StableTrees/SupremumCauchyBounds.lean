/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.SupremumCauchyEstimates

/-!
# Deterministic bounds for compact occupation errors

The same zero-start event gives the discount-removal bound at every horizon.

## References

* [J. Bertoin, *Lévy Processes*, Cambridge University Press, 1996, Chapter IV]
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees

private theorem occupation_le {ε : ℝ} (hε : 0 < ε) (f : DLoc) (t : ℝ≥0) :
    supOccupation ε f t ≤ ε⁻¹ * (t : ℝ) := by
  simpa only [supOccupation_zero, sub_zero, NNReal.coe_zero] using
    (supOccupation_sub_mem hε f (s := 0) (t := t) (zero_le : (0 : ℝ≥0) ≤ t)).2

private theorem error_bound {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η)
    (T : ℝ≥0) (f : DLoc) (s : Set.Iic T) :
    |supOccupation ε f s - supOccupation η f s| ≤ (ε⁻¹ + η⁻¹) * (T : ℝ) := by
  calc
    _ ≤ |supOccupation ε f s| + |supOccupation η f s| := abs_sub _ _
    _ = supOccupation ε f s + supOccupation η f s := by
      rw [abs_of_nonneg (supOccupation_nonneg hε.le _ _),
        abs_of_nonneg (supOccupation_nonneg hη.le _ _)]
    _ ≤ ε⁻¹ * (s : ℝ≥0) + η⁻¹ * (s : ℝ≥0) :=
      add_le_add (occupation_le hε _ _) (occupation_le hη _ _)
    _ ≤ (ε⁻¹ + η⁻¹) * (T : ℝ) := by
      rw [← add_mul]
      exact mul_le_mul_of_nonneg_left (by exact_mod_cast s.2) (by positivity)

/-- The compact error is nonnegative on every path. -/
theorem compactError_nonneg {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) (T : ℝ≥0) (f : DLoc) :
    0 ≤ compactError ε η T f := by
  have hb : BddAbove (range (fun s : Set.Iic T =>
      |supOccupation ε f s - supOccupation η f s|)) :=
    ⟨(ε⁻¹ + η⁻¹) * T, by rintro _ ⟨s, rfl⟩; exact error_bound hε hη T f s⟩
  exact (abs_nonneg _).trans (le_ciSup hb (⟨0, (zero_le : (0 : ℝ≥0) ≤ T)⟩ : Set.Iic T))

/-- A deterministic bound for the compact occupation error. -/
theorem compactError_le {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) (T : ℝ≥0) (f : DLoc) :
    compactError ε η T f ≤ (ε⁻¹ + η⁻¹) * (T : ℝ) := by
  exact ciSup_le (error_bound hε hη T f)

/-- Compact occupation errors have integrable squares at every pair of positive cutoffs. -/
theorem integrable_sq_compactError (θ : ℝ) {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) (T : ℝ≥0) :
    Integrable (fun f => compactError ε η T f ^ 2) (stableLocalLaw θ : Measure DLoc) := by
  apply Integrable.of_bound ((measurable_compactError hε hη T).aestronglyMeasurable.pow 2)
    (((ε⁻¹ + η⁻¹) * (T : ℝ)) ^ 2)
  apply ae_of_all
  intro f
  change ‖compactError ε η T f ^ 2‖ ≤ _
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact pow_le_pow_left₀ (compactError_nonneg hε hη T f) (compactError_le hε hη T f) 2

private theorem kernel_abs_le {ε : ℝ} (hε : 0 < ε) (r : ℝ) : |supOccKernel ε r| ≤ ε⁻¹ := by
  rw [abs_of_nonneg (supOccKernel_mem_Icc hε r).1]
  exact (supOccKernel_mem_Icc hε r).2

/-- An all-path compact bound for the explicit martingale. -/
theorem abs_occupationDiffMartingale_le {θ ε η D : ℝ} (hε : 0 < ε) (hη : 0 < η)
    (hD : ∀ y : ℝ, |supOccupationResolvent θ 1 ε y - supOccupationResolvent θ 1 η y| ≤ D)
    {s T : ℝ≥0} (hs : s ≤ T) (f : DLoc) :
    |occupationDiffMartingale θ ε η s f| ≤ (ε⁻¹ + η⁻¹) * (T : ℝ) + D := by
  have hD0 : 0 ≤ D := (abs_nonneg _).trans (hD 0)
  have hb (u : ℝ) : |supOccKernel ε (supReflectedFrom 0 f u.toNNReal) -
      supOccKernel η (supReflectedFrom 0 f u.toNNReal)| ≤ ε⁻¹ + η⁻¹ :=
    (abs_sub _ _).trans (add_le_add (kernel_abs_le hε _) (kernel_abs_le hη _))
  have hi : |∫ u in Ioc (0 : ℝ) s, Real.exp (-u) *
      (supOccKernel ε (supReflectedFrom 0 f u.toNNReal) -
        supOccKernel η (supReflectedFrom 0 f u.toNNReal))| ≤ (ε⁻¹ + η⁻¹) * (s : ℝ) := by
    have hh := norm_setIntegral_le_of_norm_le_const (μ := (volume : Measure ℝ))
      (f := fun u : ℝ => Real.exp (-u) *
        (supOccKernel ε (supReflectedFrom 0 f u.toNNReal) -
          supOccKernel η (supReflectedFrom 0 f u.toNNReal)))
      (s := Ioc (0 : ℝ) s) (C := ε⁻¹ + η⁻¹) (by simp) (fun u hu => ?_)
    · simpa [Real.norm_eq_abs, Measure.real, Real.volume_Ioc, s.coe_nonneg] using hh
    · rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      have he : Real.exp (-u) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [hu.1])
      exact (mul_le_mul_of_nonneg_left (hb u) (Real.exp_pos _).le).trans
        (mul_le_of_le_one_left (by positivity) he)
  have hv : |Real.exp (-(s : ℝ)) * (supOccupationResolvent θ 1 ε (supReflectedFrom 0 f s) -
      supOccupationResolvent θ 1 η (supReflectedFrom 0 f s))| ≤ D := by
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    exact (mul_le_mul_of_nonneg_left (hD _) (Real.exp_pos _).le).trans
      (mul_le_of_le_one_left hD0 (Real.exp_le_one_iff.mpr (neg_nonpos.mpr s.coe_nonneg)))
  have hmul : (ε⁻¹ + η⁻¹) * (s : ℝ) ≤ (ε⁻¹ + η⁻¹) * (T : ℝ) :=
    mul_le_mul_of_nonneg_left (by exact_mod_cast hs) (by positivity)
  exact (abs_add_le _ _).trans ((add_le_add hi hv).trans (by linarith only [hmul]))

/-- Discount removal on each zero-start path, simultaneously in the horizon. -/
theorem compactError_le_of_zero_start {θ ε η D : ℝ} (hε : 0 < ε) (hη : 0 < η)
    (hD : ∀ y : ℝ, |supOccupationResolvent θ 1 ε y - supOccupationResolvent θ 1 η y| ≤ D)
    (f : DLoc) (h0 : f.1 0 = 0) (T : ℝ≥0) :
    compactError ε η T f ≤
      2 * Real.exp (T : ℝ) * ((⨆ t : Set.Iic T, |occupationDiffMartingale θ ε η t f|) + D) := by
  let H := ⨆ t : Set.Iic T, |occupationDiffMartingale θ ε η t f|
  have hJb : BddAbove (range (fun t : Set.Iic T => |occupationDiffMartingale θ ε η t f|)) :=
    ⟨(ε⁻¹ + η⁻¹) * (T : ℝ) + D, by
      rintro _ ⟨t, rfl⟩
      exact abs_occupationDiffMartingale_le hε hη hD t.2 f⟩
  have hH0 : 0 ≤ H := (abs_nonneg _).trans
    (le_ciSup hJb (⟨0, (zero_le : (0 : ℝ≥0) ≤ T)⟩ : Set.Iic T))
  have hD0 : 0 ≤ D := (abs_nonneg _).trans (hD 0)
  let k := fun s : ℝ => supOccKernel ε (supReflectedFrom 0 f s.toNNReal) -
    supOccKernel η (supReflectedFrom 0 f s.toNNReal)
  have hR : Measurable (fun s : ℝ => supReflectedFrom 0 f s.toNNReal) :=
    measurable_supReflectedFrom_uncurry.comp
      (measurable_const.prodMk (measurable_const.prodMk measurable_real_toNNReal))
  have hk : Measurable k :=
    ((measurable_supOccKernel ε).sub (measurable_supOccKernel η)).comp hR
  have hki (t : ℝ≥0) : IntegrableOn k (Icc 0 (t : ℝ)) := by
    apply Measure.integrableOn_of_bounded (by simp) hk.aestronglyMeasurable
    apply ae_of_all
    intro u
    simpa only [Real.norm_eq_abs] using (abs_sub _ _).trans
      (add_le_add (kernel_abs_le hε _) (kernel_abs_le hη _))
  apply ciSup_le
  intro t
  have hKt (s : ℝ) (hs : s ∈ Icc 0 (t : ℝ)) :
      |∫ u in Ioc 0 s, Real.exp (-u) * k u| ≤ H + D := by
    have hs0 : (s.toNNReal : ℝ) = s := Real.coe_toNNReal _ hs.1
    have hsT : s.toNNReal ≤ T := by
      apply NNReal.coe_le_coe.mp
      rw [hs0]
      exact hs.2.trans (by exact_mod_cast t.2)
    have he : (∫ u in Ioc 0 s, Real.exp (-u) * k u) =
        occupationDiffMartingale θ ε η s.toNNReal f - Real.exp (-s) *
          (supOccupationResolvent θ 1 ε (supReflectedFrom 0 f s.toNNReal) -
            supOccupationResolvent θ 1 η (supReflectedFrom 0 f s.toNNReal)) := by
      dsimp only [occupationDiffMartingale]
      rw [hs0]
      dsimp only [k]
      ring
    rw [he]
    apply (abs_sub _ _).trans (add_le_add (le_ciSup hJb ⟨s.toNNReal, hsT⟩) ?_)
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    exact (mul_le_mul_of_nonneg_left (hD _) (Real.exp_pos _).le).trans
      (mul_le_of_le_one_left hD0 (Real.exp_le_one_iff.mpr (by linarith [hs.1])))
  have he : supOccupation ε f t - supOccupation η f t = ∫ s in Ioc 0 (t : ℝ), k s := by
    rw [supOccupation_eq_integral_supOccKernel f h0,
      supOccupation_eq_integral_supOccKernel f h0]
    apply (integral_sub ?_ ?_).symm
    · exact (Measure.integrableOn_of_bounded (by simp)
        ((measurable_supOccKernel ε).comp hR).aestronglyMeasurable
        (ae_of_all _ fun s => by simpa only [Real.norm_eq_abs] using kernel_abs_le hε _))
    · exact (Measure.integrableOn_of_bounded (by simp)
        ((measurable_supOccKernel η).comp hR).aestronglyMeasurable
        (ae_of_all _ fun s => by simpa only [Real.norm_eq_abs] using kernel_abs_le hη _))
  rw [he]
  exact (abs_integral_le_of_discountedPrimitive_bound t.1.coe_nonneg (hki t) hKt).trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by exact_mod_cast t.2)) (by norm_num))
      (add_nonneg hH0 hD0))

/-- Deterministic integration by parts removes the discount on one common event. -/
theorem ae_compactError_le {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η)
    {D : ℝ}
    (hD : ∀ y : ℝ, |supOccupationResolvent θ 1 ε y - supOccupationResolvent θ 1 η y| ≤ D) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∀ T : ℝ≥0,
      compactError ε η T f ≤
        2 * Real.exp (T : ℝ) * ((⨆ t : Set.Iic T, |occupationDiffMartingale θ ε η t f|) + D) := by
  filter_upwards [ae_eval_zero_stableLocalLaw hθ] with f hf
  exact compactError_le_of_zero_start hε hη hD f hf

end BGW.StableTrees
