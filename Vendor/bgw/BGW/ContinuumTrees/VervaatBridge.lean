/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.ContinuumTrees.BrownianBridge
public import BGW.ContinuumTrees.Vervaat
public import BGW.ContinuumTrees.CodingStability

/-!
# The Vervaat image of the constructed Brownian bridge

The anchored Brownian bridge gives a measurable continuous loop for every outcome on the
constructed source probability space. Applying the deterministic Vervaat transformation gives
an actual probability law on nonnegative continuous paths with zero endpoints.

The rooted measured tree law is the genuine image under coding by twice this path. Its root
is represented by time zero, and its mass is the existing Lebesgue pushforward from the coding
construction. The normalization is therefore explicitly `T_(2e)`.

These are laws of the constructed Vervaat path and its coded tree. Almost-sure uniqueness of
the bridge minimizer, strict interior positivity, and identification with the standard Brownian
excursion and classical Brownian CRT laws are separate, unproved probabilistic statements.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory BGW.MetricMeasure
open scoped NNReal

namespace BGW.ContinuumTrees.VervaatBridge

/-- The deterministic Vervaat transform of the anchored Brownian bridge path. -/
noncomputable def path (ω : ℝ≥0 → ℝ) : C(unitInterval, ℝ) :=
  Vervaat.vervaat ⟨BrownianBridge.path ω,
    (BrownianBridge.path_zero ω).trans (BrownianBridge.path_one ω).symm⟩

@[fun_prop] theorem measurable_path : Measurable path :=
  Vervaat.measurable_vervaat.comp
    (BrownianBridge.measurable_path.subtype_mk
      (h := fun ω => (BrownianBridge.path_zero ω).trans (BrownianBridge.path_one ω).symm))

theorem path_nonneg (ω : ℝ≥0 → ℝ) (t : unitInterval) : 0 ≤ path ω t :=
  Vervaat.vervaat_nonneg _ t

@[simp] theorem path_zero (ω : ℝ≥0 → ℝ) : path ω 0 = 0 := by
  rw [path, Vervaat.vervaat_apply]
  exact Vervaat.vervaat_zero _

@[simp] theorem path_one (ω : ℝ≥0 → ℝ) : path ω 1 = 0 := by
  rw [path, Vervaat.vervaat_apply]
  exact Vervaat.vervaat_one _

/-- The actual Vervaat path law on the continuous-path space. -/
noncomputable def law : ProbabilityMeasure C(unitInterval, ℝ) :=
  ⟨Measure.map path gaussianLimit, inferInstance⟩

@[simp] theorem coe_law :
    (law : Measure C(unitInterval, ℝ)) = Measure.map path gaussianLimit := rfl

theorem law_apply {A : Set C(unitInterval, ℝ)} (hA : MeasurableSet A) :
    (law : Measure C(unitInterval, ℝ)) A = gaussianLimit (path ⁻¹' A) :=
  Measure.map_apply measurable_path hA

theorem hasLaw_path : HasLaw path (law : Measure C(unitInterval, ℝ)) gaussianLimit where
  aemeasurable := measurable_path.aemeasurable
  map_eq := rfl

/-- The rooted measured isometry class coded by twice the constructed Vervaat path. -/
noncomputable def tree (ω : ℝ≥0 → ℝ) : RootedMeasuredGHSpace.{0} :=
  Coding.rootedMeasuredGHSpace ((2 : ℝ) • path ω)

private theorem continuous_treeCoding :
    Continuous (fun e : C(unitInterval, ℝ) => Coding.rootedMeasuredGHSpace ((2 : ℝ) • e)) :=
  Coding.continuous_rootedMeasuredGHSpace.comp (continuous_id.const_smul (2 : ℝ))

@[fun_prop] theorem measurable_tree : Measurable tree :=
  continuous_treeCoding.measurable.comp measurable_path

/-- Each underlying coded carrier is a genuine compact real tree by the deterministic coding API. -/
theorem isRealTree (ω : ℝ≥0 → ℝ) : RealTree.IsRealTree (Coding.Space ((2 : ℝ) • path ω)) :=
  Coding.isRealTree _

/-- The genuine probability law of the rooted measured tree coded by `2 • path`. -/
noncomputable def treeLaw : ProbabilityMeasure RootedMeasuredGHSpace.{0} :=
  ⟨Measure.map tree gaussianLimit, inferInstance⟩

@[simp] theorem coe_treeLaw :
    (treeLaw : Measure RootedMeasuredGHSpace.{0}) = Measure.map tree gaussianLimit := rfl

theorem treeLaw_apply {A : Set RootedMeasuredGHSpace.{0}} (hA : MeasurableSet A) :
    (treeLaw : Measure RootedMeasuredGHSpace.{0}) A = gaussianLimit (tree ⁻¹' A) :=
  Measure.map_apply measurable_tree hA

theorem hasLaw_tree : HasLaw tree (treeLaw : Measure RootedMeasuredGHSpace.{0}) gaussianLimit where
  aemeasurable := measurable_tree.aemeasurable
  map_eq := rfl

/-- Coding the actual path law agrees with the direct image of the source probability measure. -/
theorem treeLaw_eq_map :
    treeLaw = law.map (fun e => Coding.rootedMeasuredGHSpace ((2 : ℝ) • e)) := by
  apply ProbabilityMeasure.toMeasure_injective
  change Measure.map tree gaussianLimit =
    Measure.map (fun e => Coding.rootedMeasuredGHSpace ((2 : ℝ) • e))
      (Measure.map path gaussianLimit)
  rw [Measure.map_map continuous_treeCoding.measurable measurable_path]
  rfl

end BGW.ContinuumTrees.VervaatBridge
