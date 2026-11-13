/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.Topology.UniformSpace.CompactConvergence
import Mathlib.Topology.Metrizable.Uniformity
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic

/-!
# Measurable reconstruction from a dense trace

A continuous real function is reconstructed Borel-measurably from its values on a countable
dense subset, with the zero function on the branch where no continuous reconstruction exists.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped Classical

namespace BGW.Probability

/-- Reconstruction of a continuous function from a countable dense trace is Borel. -/
theorem measurable_continuous_reconstruction {X Ω : Type*} [TopologicalSpace X]
    [MeasurableSpace Ω] [PolishSpace C(X, ℝ)]
    (D : Set X) [Countable D] (hD : Dense D) (a : Ω → D → ℝ)
    (ha : Measurable a) :
    Measurable (fun ω =>
      if h : ∃ g : C(X, ℝ), ∀ t : D, g t = a ω t then Classical.choose h else 0) := by
  let E (g : C(X, ℝ)) : D → ℝ := fun t => g t
  have hEcont : Continuous E := continuous_pi fun t =>
    (show Continuous (fun g : C(X, ℝ) => g (t : X)) from continuous_eval_const _)
  have hEinj : Function.Injective E := by
    intro c d he
    apply DFunLike.coe_injective
    exact Continuous.ext_on hD c.continuous d.continuous
      (fun t ht => congrFun he ⟨t, ht⟩)
  have hE : MeasurableEmbedding E := hEcont.measurableEmbedding hEinj
  have hex (ω : Ω) : (∃ g : C(X, ℝ), ∀ t : D, g t = a ω t) ↔ a ω ∈ range E := by
    simp only [mem_range, E, funext_iff]
  have hmeas : Measurable (fun ω =>
      if a ω ∈ range E then hE.invFun (a ω) else (0 : C(X, ℝ))) :=
    Measurable.ite (ha hE.measurableSet_range) (hE.measurable_invFun.comp ha) measurable_const
  convert hmeas using 1
  funext ω
  symm
  by_cases h : ∃ g : C(X, ℝ), ∀ t : D, g t = a ω t
  · rw [ite_eq_left ((hex ω).mp h), dite_eq_left h]
    have he : E (Classical.choose h) = a ω := funext (Classical.choose_spec h)
    exact (congrArg hE.invFun he.symm).trans (hE.leftInverse_invFun _)
  · rw [ite_eq_right (fun hh => h ((hex ω).mpr hh)), dite_eq_right h]

end BGW.Probability
