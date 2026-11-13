/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.HeightContinuityBasic
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Topology.UniformSpace.CompactConvergence
import Mathlib.Topology.Metrizable.Uniformity
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic

public import BGW.Probability.MeasurableReconstruction

/-!
# Borel reconstruction from rational heights

The rational evaluation map is an injective Borel map from the Polish space of continuous
functions. Its range is Borel and its inverse is measurable. This controls the choice in both
height reconstructions, for every parameter and every input path.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal Classical
open BGW.Skorokhod
open BGW.Probability

namespace BGW.StableTrees

private theorem countable_rationalTime : Countable {t : ℝ≥0 // IsRationalTime t} := by
  apply Function.Injective.countable (f := fun t : {t : ℝ≥0 // IsRationalTime t} =>
    Classical.choose t.2)
  intro a b hab
  apply Subtype.ext
  apply NNReal.coe_injective
  exact (Classical.choose_spec a.2).symm.trans
    ((congrArg (fun q : ℚ => (q : ℝ)) hab).trans (Classical.choose_spec b.2))

/-- The bundled continuous height is measurable, including the zero branch. -/
theorem measurable_heightLoc (θ : ℝ) :
    Measurable (fun f : DLoc => (⟨heightLoc θ f, continuous_heightLoc θ f⟩ : C(ℝ≥0, ℝ))) := by
  let : TopologicalSpace.MetrizableSpace C(ℝ≥0, ℝ) := UniformSpace.metrizableSpace
  let : PolishSpace C(ℝ≥0, ℝ) := inferInstance
  let D : Set ℝ≥0 := {t | IsRationalTime t}
  let : Countable D := countable_rationalTime
  let a (f : DLoc) (t : D) : ℝ := heightUniv θ f t
  have ha : Measurable a := Measurable.of_eval fun t =>
    Measurable.comp (g := fun p : ℝ≥0 × DLoc => heightUniv θ p.2 p.1)
      (f := fun f : DLoc => (t, f)) (measurable_heightUniv_uncurry θ)
      (measurable_const.prodMk measurable_id)
  have hm := measurable_continuous_reconstruction D dense_isRationalTime a ha
  convert hm using 1
  funext f
  symm
  apply ContinuousMap.ext
  intro t
  unfold heightLoc
  have he : (∃ g : C(ℝ≥0, ℝ), ∀ t : D, g t = a f t) ↔
      ∃ g : C(ℝ≥0, ℝ), ∀ t : ℝ≥0, IsRationalTime t → g t = heightUniv θ f t := by
    simp only [D, a, Subtype.forall, mem_ofPred_eq]
  by_cases h : ∃ g : C(ℝ≥0, ℝ), ∀ t : D, g t = a f t
  · have h' := he.mp h
    rw [dite_eq_left h]
    change Classical.choose h t =
      (if h : ∃ g : C(ℝ≥0, ℝ), ∀ t : ℝ≥0,
        IsRationalTime t → g t = heightUniv θ f t then ⇑(Classical.choose h) else fun _ => 0) t
    rw [dite_eq_left h']
    exact congrFun (Continuous.ext_on dense_isRationalTime
      (Classical.choose h).continuous (Classical.choose h').continuous
      (fun u hu => (Classical.choose_spec h ⟨u, hu⟩).trans
        (Classical.choose_spec h' u hu).symm)) t
  · have h' : ¬ ∃ g : C(ℝ≥0, ℝ), ∀ t : ℝ≥0,
        IsRationalTime t → g t = heightUniv θ f t := fun hh => h (he.mpr hh)
    rw [dite_eq_right h]
    change (0 : C(ℝ≥0, ℝ)) t =
      (if h : ∃ g : C(ℝ≥0, ℝ), ∀ t : ℝ≥0,
        IsRationalTime t → g t = heightUniv θ f t then ⇑(Classical.choose h) else fun _ => 0) t
    rw [dite_eq_right h']
    rfl

/-- Joint evaluation of the reconstructed height is measurable. -/
theorem measurable_heightLoc_uncurry (θ : ℝ) :
    Measurable (fun p : ℝ≥0 × DLoc => heightLoc θ p.2 p.1) := by
  exact measurable_uncurry_of_continuous_of_measurable (continuous_heightLoc θ)
    (fun t => (ContinuousMap.measurable_eval t).comp (measurable_heightLoc θ))

/-- The continuous prefix reconstruction is Borel measurable. -/
theorem measurable_heightPrefix (θ : ℝ) (T : ℝ≥0) : Measurable (heightPrefix θ T) := by
  let Q : Set (Set.Icc (0 : ℝ) T) := {t | ∃ q : ℚ, (q : ℝ) = t}
  let : Countable Q := by
    apply Function.Injective.countable (f := fun t : Q => Classical.choose t.2)
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    exact (Classical.choose_spec a.2).symm.trans
      ((congrArg (fun q : ℚ => (q : ℝ)) hab).trans (Classical.choose_spec b.2))
  let a (g : D (T : ℝ) ℝ) (t : Q) : ℝ :=
    heightUniv θ (extendConst T g) ⟨t, t.1.2.1⟩
  have ha : Measurable a := Measurable.of_eval fun t =>
    Measurable.comp (g := fun p : ℝ≥0 × DLoc => heightUniv θ p.2 p.1)
      (f := fun g : BGW.Skorokhod.D (T : ℝ) ℝ =>
        (⟨t, t.1.2.1⟩, extendConst T g)) (measurable_heightUniv_uncurry θ)
      (measurable_const.prodMk (measurable_extendConst T))
  have hm := measurable_continuous_reconstruction Q (dense_prefix_rationals T) a ha
  convert hm using 1
  funext g
  symm
  unfold heightPrefix
  have he : (∃ c : C(Set.Icc (0 : ℝ) T, ℝ), ∀ t : Q, c t = a g t) ↔
      ∃ c : C(Set.Icc (0 : ℝ) T, ℝ), ∀ t : Set.Icc (0 : ℝ) T,
        (∃ q : ℚ, (q : ℝ) = t) →
          c t = heightUniv θ (extendConst T g) ⟨t, t.2.1⟩ := by
    simp only [Q, a, Subtype.forall, mem_ofPred_eq]
  by_cases h : ∃ c : C(Set.Icc (0 : ℝ) T, ℝ), ∀ t : Q, c t = a g t
  · have h' := he.mp h
    rw [dite_eq_left h, dite_eq_left h']
    apply continuousMap_ext_rational T
    intro t ht
    exact (Classical.choose_spec h ⟨t, ht⟩).trans (Classical.choose_spec h' t ht).symm
  · have h' := mt he.mpr h
    rw [dite_eq_right h, dite_eq_right h']

end BGW.StableTrees
