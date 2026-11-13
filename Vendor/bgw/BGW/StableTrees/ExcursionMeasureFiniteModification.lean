/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.ExcursionMeasureCompensationStep

/-! Everywhere finite measurable modifications on bounded lifetime-truncated boxes.

See Bertoin, *Lévy Processes*, Chapter IV.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod
open BGW.Probability

namespace BGW.StableTrees

/-- On a bounded time window and a positive lifetime slab, the restricted excursion measure
has a measurable modification which is a finite measure at every sample path. -/
theorem exists_finite_modification_excursionPointMeasure {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    (K ε : ℝ≥0) (hε : 0 < ε) :
    ∃ ν : DLoc → Measure (ℝ≥0 × Excursion), Measurable ν ∧
      (∀ f, IsFiniteMeasure (ν f)) ∧
      ν =ᵐ[(stableLocalLaw θ : Measure DLoc)]
        (fun f => (excursionPointMeasure f).restrict
          (Ioc 0 K ×ˢ {e : Excursion | ε < e.lifetime})) := by
  classical
  obtain ⟨ξ, hξ, hae⟩ := exists_measurable_modification_excursionPointMeasure hθ
  let E := Ioc 0 K ×ˢ {e : Excursion | ε < e.lifetime}
  have hE : MeasurableSet E :=
    measurable_box (measurableSet_lt measurable_const measurable_excursion_lifetime)
  let ν := fun f => if ξ f E < ⊤ then (ξ f).restrict E else 0
  have hν : Measurable ν :=
    (measurable_restrict_pointMeasure hξ hE).piecewise
      (measurableSet_lt (measurable_count hξ hE) measurable_const) measurable_const
  refine ⟨ν, hν, ?_, ?_⟩
  · intro f
    dsimp [ν]
    split_ifs with hf
    · exact ⟨by simpa only [Measure.restrict_apply MeasurableSet.univ, univ_inter] using hf⟩
    · infer_instance
  · have hfin := (isTimeSimpleLevy_of_ae_eq_excursionPointMeasure hθ hξ hae).2 ε hε
    filter_upwards [hae, hfin.2.2 K] with f hf hfinite
    dsimp [ν]
    rw [ite_eq_left hfinite, hf]

end BGW.StableTrees
