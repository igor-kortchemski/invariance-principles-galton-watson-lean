/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.SupremumPotentialResolvent

/-!
# Second moments of reflected occupation resolvents

The signed occupation identity is the generic resolvent moment theorem specialized
to the reflected family.

Reference: A. E. Kyprianou, *Fluctuations of Lévy Processes with Applications*, 2nd ed.,
Springer, 2014, Chapter 8.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod
open BGW.Probability

namespace BGW.StableTrees

/-- Signed second-moment identity for the difference of two positive occupation cutoffs. -/
theorem integral_sq_discountedOccupation_supOccupation_sub {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    (x : ℝ≥0) {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) :
    ∫ f, (discountedOccupation (fun t f => supReflectedFrom x f t)
        (fun r => supOccKernel ε r - supOccKernel η r) f) ^ 2 ∂(stableLocalLaw θ : Measure DLoc) =
      2 * ∫ f, (∫ t in Ioi (0 : ℝ), Real.exp (-2 * t) *
        ((supOccKernel ε (supReflectedFrom x f t.toNNReal) -
            supOccKernel η (supReflectedFrom x f t.toNNReal)) *
          (supOccupationResolvent θ 1 ε (supReflectedFrom x f t.toNNReal) -
            supOccupationResolvent θ 1 η (supReflectedFrom x f t.toNNReal))))
        ∂(stableLocalLaw θ : Measure DLoc) := by
  let k := fun r => supOccKernel ε r - supOccKernel η r
  let V := fun y => supOccupationResolvent θ 1 ε y - supOccupationResolvent θ 1 η y
  have hεb (r : ℝ) : |supOccKernel ε r| ≤ ε⁻¹ := by
    obtain ⟨h0, h1⟩ := supOccKernel_mem_Icc hε r
    rwa [abs_of_nonneg h0]
  have hηb (r : ℝ) : |supOccKernel η r| ≤ η⁻¹ := by
    obtain ⟨h0, h1⟩ := supOccKernel_mem_Icc hη r
    rwa [abs_of_nonneg h0]
  have hk : Measurable k := (measurable_supOccKernel ε).sub (measurable_supOccKernel η)
  have hkb : ∃ C, ∀ r, |k r| ≤ C :=
    ⟨ε⁻¹ + η⁻¹, fun r => (abs_sub _ _).trans (add_le_add (hεb r) (hηb r))⟩
  have hV : Measurable V :=
    (measurable_reflectedResolvent hθ 1 (measurable_supOccKernel ε) ⟨ε⁻¹, hεb⟩).sub
      (measurable_reflectedResolvent hθ 1 (measurable_supOccKernel η) ⟨η⁻¹, hηb⟩)
  have hVb : ∃ C, ∀ y, |V y| ≤ C := by
    refine ⟨ε⁻¹ + η⁻¹, fun y => ?_⟩
    have hbε := abs_reflectedResolvent_le hθ zero_lt_one (measurable_supOccKernel ε) hεb y
    have hbη := abs_reflectedResolvent_le hθ zero_lt_one (measurable_supOccKernel η) hηb y
    exact (abs_sub _ _).trans (add_le_add
      (by simpa only [div_one, supOccupationResolvent] using hbε)
      (by simpa only [div_one, supOccupationResolvent] using hbη))
  have hZ : Measurable (fun p : ℝ≥0 × DLoc => supReflectedFrom x p.2 p.1) :=
    measurable_supReflectedFrom_uncurry.comp
      (measurable_const.prodMk (measurable_snd.prodMk measurable_fst))
  have hpk : IsStronglyProgressive DLoc.filtration (fun t f => k (supReflectedFrom x f t)) := by
    intro t
    exact (hk.comp (isStronglyProgressive_supReflectedFrom x t).measurable).stronglyMeasurable
  have hpV : IsStronglyProgressive DLoc.filtration (fun t f => V (supReflectedFrom x f t)) := by
    intro t
    exact (hV.comp (isStronglyProgressive_supReflectedFrom x t).measurable).stronglyMeasurable
  exact integral_sq_discountedOccupation hZ hk hV hkb hVb hpk hpV
    (resolventMarkov_supReflectedFrom_sub hθ x hε hη)

end BGW.StableTrees
