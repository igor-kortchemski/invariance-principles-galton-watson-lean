/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.ExcursionMeasureWindow

/-! Independent Poisson counts of finite-intensity excursion boxes.

See Bertoin, *Lévy Processes*, Chapter IV.
-/

@[expose] public section

open MeasureTheory MeasurableSpace Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod
open BGW.Probability

namespace BGW.StableTrees

/-- **Poisson theorem** (counts): for every measurable modification `ξ`, counts of boxes
`(s i, t i] × A i` with `N (A i) < ∞` and pairwise disjoint boxes are independent Poisson with means
`(t i - s i) * N (A i)`. -/
theorem excursionCounts_poisson_independent {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    {ξ : DLoc → Measure (ℝ≥0 × Excursion)} (hξ : Measurable ξ)
    (hae : ξ =ᵐ[(stableLocalLaw θ : Measure DLoc)] excursionPointMeasure)
    {k : ℕ} (A : Fin k → Set Excursion) (hA : ∀ i, MeasurableSet (A i))
    (hfin : ∀ i, excursionMeasure θ (A i) < ⊤) (s t : Fin k → ℝ≥0) (hst : ∀ i, s i ≤ t i)
    (hdisj : Pairwise (Function.onFun Disjoint fun i => Ioc (s i) (t i) ×ˢ A i)) :
    (stableLocalLaw θ : Measure DLoc).map
        (fun f i => natCount (ξ f) (Ioc (s i) (t i) ×ˢ A i)) =
      Measure.pi (fun i => poissonMeasure ((t i - s i) * (excursionMeasure θ (A i)).toNNReal)) :=
  by
  have hlevy := (isTimeSimpleLevy_of_ae_eq_excursionPointMeasure hθ hξ hae).1
  have hrate (i : Fin k) : IsFiniteRate (stableLocalLaw θ : Measure DLoc) ξ (A i) := by
    refine ⟨hA i, fun u => ?_⟩
    apply ae_lt_top (measurable_count hξ (measurable_box (hA i)))
    rw [lintegral_windowMark_eq hθ hξ hae ((show 0 ≤ u from bot_le)) (hA i)]
    exact (ENNReal.mul_lt_top ENNReal.coe_lt_top (hfin i)).ne
  have hr (i : Fin k) :
      markRate (stableLocalLaw θ : Measure DLoc) ξ (A i) = excursionMeasure θ (A i) :=
    (excursionMeasure_apply_of_ae_eq hθ hξ hae (hA i)).2.symm
  simpa only [hr] using counts_poisson_independent hlevy A hrate s t hst hdisj

/-- The same law for the unmodified `excursionPointMeasure` (the map is a.e. equal to the one of
`ξ`, so no measurable modification needs to be named). -/
theorem excursionCounts_poisson_independent_pointMeasure {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    {k : ℕ} (A : Fin k → Set Excursion) (hA : ∀ i, MeasurableSet (A i))
    (hfin : ∀ i, excursionMeasure θ (A i) < ⊤) (s t : Fin k → ℝ≥0) (hst : ∀ i, s i ≤ t i)
    (hdisj : Pairwise (Function.onFun Disjoint fun i => Ioc (s i) (t i) ×ˢ A i)) :
    (stableLocalLaw θ : Measure DLoc).map
        (fun f i => natCount (excursionPointMeasure f) (Ioc (s i) (t i) ×ˢ A i)) =
      Measure.pi (fun i => poissonMeasure ((t i - s i) * (excursionMeasure θ (A i)).toNNReal)) :=
  by
  obtain ⟨ξ, hξ, hae⟩ := exists_measurable_modification_excursionPointMeasure hθ
  rw [← excursionCounts_poisson_independent hθ hξ hae A hA hfin s t hst hdisj]
  apply Measure.map_congr
  filter_upwards [hae] with f hf
  exact congrArg (fun μ i => natCount μ (Ioc (s i) (t i) ×ˢ A i)) hf.symm

end BGW.StableTrees
