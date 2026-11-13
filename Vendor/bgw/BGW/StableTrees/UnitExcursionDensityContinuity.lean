/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.UnitExcursionDensityGoodTimes
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Finite-dimensional continuity of the scaled unit law

At a good time, càdlàg paths are continuous. Exact excursion scaling and bounded
convergence give continuity of bounded continuous cylinder tests at lifetime one.

## References

* L. Chaumont, *Excursion normalisée, méandre et pont pour les processus de Lévy stables*,
  Bull. Sci. Math. 121 (1997), 377–403.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees

/-- Continuity of finite-dimensional tests under scaling at lifetime one. -/
theorem excursionAt_finiteDim_continuousAt_one {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {n : ℕ}
    (t : Fin n → ℝ≥0) (ht : ∀ i, t i ≤ 1) (hgood : ∀ i, NoFixedJumpUnit θ (t i))
    (φ : (Fin n → ℝ) → ℝ) (hφ : Continuous φ) (hφb : ∃ C : ℝ, ∀ x, |φ x| ≤ C) :
    ContinuousAt
      (fun u : Set.Ioi (0 : ℝ) => ∫ e, φ (fun i => e.path.1 (t i)) ∂(excursionAt θ u))
      ⟨1, Set.mem_Ioi.2 one_pos⟩ := by
  -- Scaling continuity only needs the good-time hypotheses, at any finite set of times.
  -- `hθ` and `ht` are part of the stated interface; the argument does not use them.
  have _hθ := hθ
  have _ht := ht
  have hm : Measurable (fun e : Excursion => φ (fun i => e.path.1 (t i))) :=
    hφ.measurable.comp (Measurable.of_eval fun i => measurable_excursion_eval (t i))
  have heq (u : Ioi (0 : ℝ)) :
      (∫ e, φ (fun i => e.path.1 (t i)) ∂excursionAt θ u) =
        ∫ e, φ (fun i => (excursionScale θ u e).path.1 (t i))
          ∂(unitExcursionLaw θ : Measure Excursion) :=
    integral_map (measurable_excursionScale θ u).aemeasurable hm.aestronglyMeasurable
  simp_rw [heq]
  obtain ⟨C, hC⟩ := hφb
  apply continuousAt_of_dominated (bound := fun _ => C)
  · exact Eventually.of_forall fun u =>
      (hm.comp (measurable_excursionScale θ u)).aestronglyMeasurable
  · exact Eventually.of_forall fun u => Eventually.of_forall fun e => hC _
  · exact integrable_const _
  · have hj : ∀ᵐ e ∂(unitExcursionLaw θ : Measure Excursion),
        ∀ i, Function.leftLim e.path.1 (t i) = e.path.1 (t i) :=
      ae_all_iff.mpr hgood
    filter_upwards [hj] with e he
    apply hφ.continuousAt.comp
    apply continuousAt_pi.mpr
    intro i
    have hc : ContinuousAt e.path.1 (t i) := by
      rw [continuousAt_iff_continuous_left'_right']
      constructor
      · change Tendsto e.path.1 (𝓝[<] t i) (𝓝 (e.path.1 (t i)))
        simpa only [he i] using e.path.2.tendsto_nhdsLT_leftLim (t i)
      · exact e.path.2.isRightContinuous (t i)
    have hs : ContinuousAt (fun u : Ioi (0 : ℝ) => t i / (u : ℝ).toNNReal)
        ⟨1, Set.mem_Ioi.mpr one_pos⟩ := by
      apply continuousAt_const.div
        (continuous_real_toNNReal.comp continuous_subtype_val).continuousAt
      norm_num
    have hv := ContinuousAt.comp
      (f := fun u : Ioi (0 : ℝ) => t i / (u : ℝ).toNNReal)
      (by simpa using hc) hs
    have hp : ContinuousAt (fun u : Ioi (0 : ℝ) => (u : ℝ) ^ (1 / θ))
        ⟨1, Set.mem_Ioi.mpr one_pos⟩ :=
      continuous_subtype_val.continuousAt.rpow_const (by simp)
    convert hp.mul hv using 1
    rfl

end BGW.StableTrees
