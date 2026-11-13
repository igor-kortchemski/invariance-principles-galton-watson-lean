/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.SupremumPotentialMoments
public import BGW.StableTrees.SupremumPotentialOccupation
import BGW.Probability.DoobL2ResolventMoment

/-!
# Uniform numerical occupation moment bounds

The rate-two occupation bound and the generic signed resolvent moment inequality
give the constants required for the occupation Cauchy construction.

Reference: A. E. Kyprianou, *Fluctuations of Lévy Processes with Applications*, 2nd ed.,
Springer, 2014, Chapter 8.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod
open BGW.Probability

namespace BGW.StableTrees

private theorem abs_kernel_bound {ε : ℝ} (hε : 0 < ε) (r : ℝ) : |supOccKernel ε r| ≤ ε⁻¹ := by
  obtain ⟨h0, h1⟩ := supOccKernel_mem_Icc hε r
  rwa [abs_of_nonneg h0]

/-- The absolute rate-two occupation has expectation at most one. -/
theorem integral_exp_neg_two_supOccKernel_le {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (x : ℝ≥0) {ε : ℝ}
    (hε : 0 < ε) :
    ∫ f, (∫ t in Ioi (0 : ℝ), Real.exp (-2 * t) *
        |supOccKernel ε (supReflectedFrom x f t.toNNReal)|) ∂(stableLocalLaw θ : Measure DLoc) ≤
      1 := by
  have hθ0 : 0 < θ := by linarith [hθ.1]
  have hp := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
    ((div_le_one hθ0).2 hθ.1.le : 1 / θ ≤ 1)
  rw [Real.rpow_one] at hp
  have hc : (2 : ℝ) ^ (1 / θ) / 2 ≤ 1 := (div_le_one (by norm_num : (0 : ℝ) < 2)).2 hp
  have hu := (supOccupationResolvent_mem_Icc hθ (by norm_num : (0 : ℝ) < 2) hε (x : ℝ)).2
  have hnonneg (r : ℝ) : |supOccKernel ε r| = supOccKernel ε r :=
    abs_of_nonneg (supOccKernel_mem_Icc hε r).1
  simp_rw [hnonneg]
  simpa only [supOccupationResolvent, reflectedResolvent, Real.toNNReal_coe] using hu.trans hc

private theorem reflected_moment_bound {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (x : ℝ≥0)
    {k : ℝ → ℝ} (hk : Measurable k) (hkb : ∃ C, ∀ r, |k r| ≤ C) {D : ℝ}
    (hD : ∀ y, |reflectedResolvent θ 1 k y| ≤ D) :
    (∫ f, (discountedOccupation (fun t f => supReflectedFrom x f t) k f) ^ 2
      ∂(stableLocalLaw θ : Measure DLoc)) ≤ 2 * D *
      ∫ f, (∫ t in Ioi 0, Real.exp (-2 * t) * |k (supReflectedFrom x f t.toNNReal)|)
        ∂(stableLocalLaw θ : Measure DLoc) := by
  have hV := measurable_reflectedResolvent hθ 1 hk hkb
  have hZ : Measurable (fun p : ℝ≥0 × DLoc => supReflectedFrom x p.2 p.1) :=
    measurable_supReflectedFrom_uncurry.comp
      (measurable_const.prodMk (measurable_snd.prodMk measurable_fst))
  apply integral_sq_discountedOccupation_le hZ hk hV hkb hD
    (fun t => (hk.comp (isStronglyProgressive_supReflectedFrom x t).measurable).stronglyMeasurable)
    (fun t => (hV.comp (isStronglyProgressive_supReflectedFrom x t).measurable).stronglyMeasurable)
  exact resolventMarkov_supReflectedFrom hθ x hk hkb

private theorem weighted_reflected_integrable {θ : ℝ} (x : ℝ≥0) {k : ℝ → ℝ} (hk : Measurable k)
    (hb : ∃ C, ∀ r, |k r| ≤ C) :
    Integrable (fun p : ℝ × DLoc => Real.exp (-2 * p.1) * k (supReflectedFrom x p.2 p.1.toNNReal))
      ((volume.restrict (Ioi 0)).prod (stableLocalLaw θ : Measure DLoc)) := by
  obtain ⟨C, hC⟩ := hb
  have hm : Measurable (fun p : ℝ × DLoc => k (supReflectedFrom x p.2 p.1.toNNReal)) :=
    hk.comp (measurable_supReflectedFrom_uncurry.comp
      (measurable_const.prodMk
        (measurable_snd.prodMk (measurable_real_toNNReal.comp measurable_fst))))
  exact integrable_exp_mul_bounded_prod hm (by norm_num : (-2 : ℝ) < 0) (fun p => hC _)

/-- The second moment of an occupation difference is bounded by four times its potential bound. -/
theorem integral_sq_discountedOccupation_supOccupation_sub_le {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    (x : ℝ≥0) {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) {D : ℝ}
    (hD : ∀ y : ℝ, |supOccupationResolvent θ 1 ε y - supOccupationResolvent θ 1 η y| ≤ D) :
    ∫ f, (discountedOccupation (fun t f => supReflectedFrom x f t)
        (fun r => supOccKernel ε r - supOccKernel η r) f) ^ 2 ∂(stableLocalLaw θ : Measure DLoc) ≤
      4 * D := by
  let k := fun r => supOccKernel ε r - supOccKernel η r
  have hk : Measurable k := (measurable_supOccKernel ε).sub (measurable_supOccKernel η)
  have hkb : ∃ C, ∀ r, |k r| ≤ C := ⟨ε⁻¹ + η⁻¹, fun r =>
    (abs_sub _ _).trans (add_le_add (abs_kernel_bound hε r) (abs_kernel_bound hη r))⟩
  have hV (y : ℝ) : |reflectedResolvent θ 1 k y| ≤ D := by
    rw [show reflectedResolvent θ 1 k y = supOccupationResolvent θ 1 ε y -
      supOccupationResolvent θ 1 η y from reflectedResolvent_sub hθ zero_lt_one
        (measurable_supOccKernel ε) (measurable_supOccKernel η)
        ⟨ε⁻¹, abs_kernel_bound hε⟩ ⟨η⁻¹, abs_kernel_bound hη⟩ y]
    exact hD y
  have hD0 : 0 ≤ D := (abs_nonneg _).trans (hD 0)
  have hεb : ∃ C, ∀ r, |abs (supOccKernel ε r)| ≤ C := ⟨ε⁻¹, fun r => by
    simpa only [abs_abs] using abs_kernel_bound hε r⟩
  have hηb : ∃ C, ∀ r, |abs (supOccKernel η r)| ≤ C := ⟨η⁻¹, fun r => by
    simpa only [abs_abs] using abs_kernel_bound hη r⟩
  have hεm : Measurable (fun r => |supOccKernel ε r|) := by
    simpa only [Real.norm_eq_abs] using (measurable_supOccKernel ε).norm
  have hηm : Measurable (fun r => |supOccKernel η r|) := by
    simpa only [Real.norm_eq_abs] using (measurable_supOccKernel η).norm
  have hkm : Measurable (fun r => |k r|) := by simpa only [Real.norm_eq_abs] using hk.norm
  have hAk := weighted_reflected_integrable (θ := θ) x hkm
    (by obtain ⟨C, hC⟩ := hkb; exact ⟨C, fun r => by simpa only [abs_abs] using hC r⟩)
  have hAε := weighted_reflected_integrable (θ := θ) x hεm hεb
  have hAη := weighted_reflected_integrable (θ := θ) x hηm hηb
  have hh := integral_mono hAk (hAε.add hAη) (fun p => ?_)
  · dsimp only [Pi.add_apply] at hh
    rw [integral_add hAε hAη, integral_prod_symm _ hAk,
      integral_prod_symm _ hAε, integral_prod_symm _ hAη] at hh
    have hb : (∫ f, (∫ t in Ioi 0, Real.exp (-2 * t) * |k (supReflectedFrom x f t.toNNReal)|)
        ∂(stableLocalLaw θ : Measure DLoc)) ≤ 2 :=
      hh.trans (by linarith [integral_exp_neg_two_supOccKernel_le hθ x hε,
        integral_exp_neg_two_supOccKernel_le hθ x hη])
    calc
      _ ≤ 2 * D * _ := reflected_moment_bound hθ x hk hkb hV
      _ ≤ 2 * D * 2 := mul_le_mul_of_nonneg_left hb (by positivity)
      _ = _ := by ring
  · exact (mul_le_mul_of_nonneg_left (abs_sub _ _) (Real.exp_pos _).le).trans_eq (mul_add _ _ _)

/-- The second moment of a single positive occupation cutoff is at most two. -/
theorem integral_sq_discountedOccupation_supOccupation_le_two {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    (x : ℝ≥0) {ε : ℝ} (hε : 0 < ε) :
    ∫ f, (discountedOccupation (fun t f => supReflectedFrom x f t) (supOccKernel ε) f) ^ 2
        ∂(stableLocalLaw θ : Measure DLoc) ≤ 2 := by
  have hb : ∃ C, ∀ r, |supOccKernel ε r| ≤ C := ⟨ε⁻¹, abs_kernel_bound hε⟩
  have hV (y : ℝ) : |reflectedResolvent θ 1 (supOccKernel ε) y| ≤ 1 := by
    obtain ⟨h0, h1⟩ := supOccupationResolvent_mem_Icc hθ zero_lt_one hε y
    change |supOccupationResolvent θ 1 ε y| ≤ 1
    rw [abs_of_nonneg h0]
    simpa using h1
  have hh := reflected_moment_bound hθ x (measurable_supOccKernel ε) hb hV
  have hb2 := integral_exp_neg_two_supOccKernel_le hθ x hε
  norm_num only [mul_one] at hh
  linarith

end BGW.StableTrees
