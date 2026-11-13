/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module
public import BGW.StableTrees.StableLaw
public import BGW.StableTrees.Scalar.Density
import Mathlib.MeasureTheory.Measure.WithDensity

/-! # Public stable-density adapters

Public forms of the pointwise and integral facts about the stable transition density.

Reference: V. M. Zolotarev, *One-dimensional Stable Distributions* (1986); K. Sato (1999), §14.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace BGW.StableTrees

/-- The transition density is nonnegative at positive times. -/
theorem stableDensityAt_nonneg {θ t : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (ht : 0 < t) (x : ℝ) :
    0 ≤ stableDensityAt θ t x := by
  obtain ⟨μ, a, h⟩ := exists_stableDomain hθ
  rw [stableDensityAt]
  exact mul_nonneg (Real.rpow_nonneg (le_of_lt ht) _)
    (Scalar.stableDensity_nonneg h _)

/-- The transition density is continuous in its spatial variable. -/
theorem stableDensityAt_continuous {θ t : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    Continuous (stableDensityAt θ t) := by
  change Continuous (fun x => t ^ (-1 / θ) *
    Scalar.stableDensity θ (t ^ (-1 / θ) * x))
  exact continuous_const.mul ((Scalar.continuous_stableDensity hθ).comp
    (continuous_const.mul continuous_id))

/-- The transition density integrates to one at positive times. -/
theorem integral_stableDensityAt {θ t : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (ht : 0 < t) :
    ∫ x, stableDensityAt θ t x = 1 := by
  obtain ⟨μ, a, h⟩ := exists_stableDomain hθ
  let c : ℝ := t ^ (-1 / θ)
  have hcpos : 0 < c := Real.rpow_pos_of_pos ht _
  have hc : c ≠ 0 := hcpos.ne'
  calc
    ∫ x, stableDensityAt θ t x = c * ∫ x, Scalar.stableDensity θ (c * x) := by
      simp [stableDensityAt, c, integral_const_mul]
    _ = c * (|c⁻¹| * ∫ y, Scalar.stableDensity θ y) := by
      simpa [smul_eq_mul] using congrArg (fun z : ℝ => c * z)
        (Measure.integral_comp_mul_left (fun y : ℝ => Scalar.stableDensity θ y) c)
    _ = 1 := by
      rw [Scalar.integral_stableDensity h, abs_of_pos (inv_pos.mpr hcpos)]
      field_simp [hc]

/-- The transition density is integrable at every positive time. -/
theorem integrable_stableDensityAt {θ t : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (ht : 0 < t) :
    Integrable (stableDensityAt θ t) := by
  obtain ⟨μ, a, h⟩ := exists_stableDomain hθ
  let c : ℝ := t ^ (-1 / θ)
  have hcpos : 0 < c := Real.rpow_pos_of_pos ht _
  have hcomp : Integrable (fun x => Scalar.stableDensity θ (c * x)) :=
    (integrable_comp_mul_left_iff _ hcpos.ne').2 (Scalar.integrable_stableDensity h)
  have hfun : stableDensityAt θ t = fun x =>
      c * Scalar.stableDensity θ (c * x) := by
    funext x
    simp [stableDensityAt, c, mul_comm]
  rw [hfun]
  exact hcomp.const_mul c

/-- For times bounded below by `t₀ > 0`, the transition densities have a common upper bound. -/
theorem stableDensityAt_le_of_ge {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {t₀ : ℝ} (ht₀ : 0 < t₀) :
    ∃ C : ℝ, ∀ t, t₀ ≤ t → ∀ x, stableDensityAt θ t x ≤ C := by
  obtain ⟨M, hM0, hM⟩ := Scalar.exists_stableDensity_le (α := θ)
  refine ⟨t₀ ^ (-1 / θ) * M, fun t ht x => ?_⟩
  have htpos : 0 < t := lt_of_lt_of_le ht₀ ht
  have he : -1 / θ ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by norm_num)
    (le_of_lt (by linarith [hθ.1]))
  have hc : t ^ (-1 / θ) ≤ t₀ ^ (-1 / θ) :=
    Real.rpow_le_rpow_of_nonpos ht₀ ht he
  rw [stableDensityAt]
  calc
    t ^ (-1 / θ) * Scalar.stableDensity θ (t ^ (-1 / θ) * x) ≤
        t ^ (-1 / θ) * M :=
      mul_le_mul_of_nonneg_left (le_trans (le_abs_self _) (hM _))
        (Real.rpow_nonneg (le_of_lt htpos) _)
    _ ≤ t₀ ^ (-1 / θ) * M := mul_le_mul_of_nonneg_right hc hM0

/-- The stable transition law has no atoms at positive times. -/
theorem stableLawAt_singleton {θ t : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (ht : 0 < t) (x : ℝ) :
    (stableLawAt θ t : Measure ℝ) {x} = 0 := by
  rw [stableLawAt_eq_withDensity hθ ht, withDensity_apply _ (measurableSet_singleton x)]
  simp

/-- At time one, the transition density is the normalized stable density. -/
theorem stableDensityAt_one (θ x : ℝ) :
    stableDensityAt θ 1 x = Scalar.stableDensity θ x := by
  simp [stableDensityAt]

/-- Joint continuity of the transition density in positive time and space. -/
theorem stableDensityAt_jointContinuous {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ContinuousOn (fun z : ℝ × ℝ => stableDensityAt θ z.1 z.2) {z | 0 < z.1} := by
  have hrpow : ContinuousOn (fun t : ℝ => t ^ (-1 / θ)) {t | 0 < t} := by
    exact ContinuousOn.rpow_const (by fun_prop) (by
      intro t ht
      exact Or.inl (ne_of_gt ht))
  have hscale : ContinuousOn (fun z : ℝ × ℝ => z.1 ^ (-1 / θ) * z.2)
      {z | 0 < z.1} := by
    exact (hrpow.comp continuousOn_fst fun z hz => hz).mul continuousOn_snd
  have hbase : ContinuousOn (fun z : ℝ × ℝ => Scalar.stableDensity θ
      (z.1 ^ (-1 / θ) * z.2)) {z | 0 < z.1} :=
    (Scalar.continuous_stableDensity hθ).continuousOn.comp hscale fun z hz => Set.mem_univ _
  change ContinuousOn (fun z : ℝ × ℝ => z.1 ^ (-1 / θ) *
    Scalar.stableDensity θ (z.1 ^ (-1 / θ) * z.2)) {z | 0 < z.1}
  exact (hrpow.comp continuousOn_fst fun z hz => hz).mul hbase

end BGW.StableTrees
