/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.LocallyFinite.Prune
public import BGW.LocallyFinite.Topology
public import Mathlib.Probability.ProductMeasure

/-!
# The Bienaymé–Galton–Watson law on locally finite trees

For an arbitrary probability measure `μ` on `ℕ`, `offspringFieldLaw μ` makes the potential
offspring counts at all addresses independent with law `μ`, and `bienaymeLaw μ` is the law of the
pruned tree. Nothing is assumed about the mean or support of `μ`; the tree may be infinite.
This is the general part of `Freezing1/PlaneBienaymeLaw.lean`, without its geometric
specialization.

The branching property, uniqueness and the law of the finite trees are in `Branching.lean`,
`Unique.lean` and `Atoms.lean`.
-/

@[expose] public section

namespace BGW.LocallyFinite

open MeasureTheory

/-- Independent potential offspring counts, one for each address.

The probability hypothesis is not used by the formula, but it fixes the domain of the definition:
`Measure.infinitePi` is the zero measure unless every component is a probability measure, so
without it the definition would expose that default value instead of an offspring law. -/
@[nolint unusedArguments]
noncomputable def offspringFieldLaw (μ : Measure ℕ) [IsProbabilityMeasure μ] :
    Measure Offspring :=
  Measure.infinitePi (fun _ : Address => μ)

instance offspringFieldLaw_probability (μ : Measure ℕ) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (offspringFieldLaw μ) := by
  unfold offspringFieldLaw
  infer_instance

/-- The Bienaymé–Galton–Watson law with offspring law `μ`. -/
noncomputable def bienaymeLaw (μ : Measure ℕ) [IsProbabilityMeasure μ] : Measure Tree :=
  (offspringFieldLaw μ).map prune

instance bienaymeLaw_probability (μ : Measure ℕ) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (bienaymeLaw μ) := by
  unfold bienaymeLaw
  infer_instance

theorem bienaymeLaw_apply (μ : Measure ℕ) [IsProbabilityMeasure μ] {A : Set Tree}
    (hA : MeasurableSet A) : bienaymeLaw μ A = offspringFieldLaw μ (prune ⁻¹' A) :=
  Measure.map_apply measurable_prune hA

theorem measurePreserving_prune (μ : Measure ℕ) [IsProbabilityMeasure μ] :
    MeasurePreserving prune (offspringFieldLaw μ) (bienaymeLaw μ) :=
  ⟨measurable_prune, rfl⟩

/-- The root degree has the offspring law. -/
theorem bienaymeLaw_map_degree (μ : Measure ℕ) [IsProbabilityMeasure μ] :
    (bienaymeLaw μ).map degree = μ := by
  rw [bienaymeLaw, Measure.map_map continuous_degree.measurable measurable_prune]
  exact Measure.infinitePi_map_eval (fun _ : Address => μ) []

/-- The root is a leaf with probability `μ {0}`. -/
theorem bienaymeLaw_leaf (μ : Measure ℕ) [IsProbabilityMeasure μ] :
    bienaymeLaw μ {leaf} = μ {0} := by
  have h := congrArg (fun ν : Measure ℕ => ν {0}) (bienaymeLaw_map_degree μ)
  have hd : degree ⁻¹' {0} = {leaf} := by
    ext T
    exact degree_zero_iff T
  simpa only [Measure.map_apply continuous_degree.measurable (measurableSet_singleton 0), hd]
    using h

end BGW.LocallyFinite
