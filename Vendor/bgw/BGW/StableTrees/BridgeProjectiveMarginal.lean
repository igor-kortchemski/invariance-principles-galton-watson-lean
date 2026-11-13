/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.BridgeProjectiveReversal
import Mathlib.MeasureTheory.Group.LIntegral

/-!
# One-dimensional marginals of the projective bridge

Restriction consistency identifies every strict prefix. The endpoint marginal has density
`p_a(x) p_{1-a}(-x) / p_1(0)`; reflection interchanges the two times.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open BGW.Skorokhod
open scoped ENNReal

namespace BGW.StableTrees

/-- A strict prefix of an open path, read from a sufficiently large coordinate. -/
noncomputable def BridgeOpen.prefix (a : ℝ) (ha1 : a < 1) (f : BridgeOpen) : D a ℝ :=
  restrict (Nat.find_spec (exists_bridgeHorizon_ge ha1))
    (f.1 (Nat.find (exists_bridgeHorizon_ge ha1)))

/-- Strict-prefix restriction is measurable. -/
theorem BridgeOpen.measurable_prefix (a : ℝ) (ha1 : a < 1) :
    Measurable (BridgeOpen.prefix a ha1) :=
  (measurable_restrict _).comp
    (CompatiblePaths.measurable_coord bridgeHorizon strictMono_bridgeHorizon _)

/-- Prefix evaluation agrees with open evaluation. -/
theorem BridgeOpen.prefix_eval (a : ℝ) (ha1 : a < 1) (f : BridgeOpen)
    (t : Icc (0 : ℝ) a) : f.prefix a ha1 t = f.eval t := by
  exact (BridgeOpen.eval_eq_coord f _
    ⟨t, t.property.1, t.property.2.trans (Nat.find_spec (exists_bridgeHorizon_ge ha1))⟩).symm

/-- Every strict prefix of an abstract projective bridge has the tilted law. -/
theorem map_prefix_bridgeOpen {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    (P : ∀ a : ℝ, ProbabilityMeasure (D a ℝ))
    (hP : ∀ a, 0 < a → a < 1 → IsStableLevyLaw θ a (P a))
    (Q : ProbabilityMeasure BridgeOpen)
    (hQ : ∀ n, (Q : Measure BridgeOpen).map (CompatiblePaths.coord n) =
      bridgePrefixLaw θ (bridgeHorizon n) (bridgeHorizon_pos n).le
        (P (bridgeHorizon n) : Measure (D (bridgeHorizon n) ℝ)))
    {a : ℝ} (ha : 0 < a) (ha1 : a < 1) :
    (Q : Measure BridgeOpen).map (BridgeOpen.prefix a ha1) =
      bridgePrefixLaw θ a ha.le (P a : Measure (D a ℝ)) := by
  change (Q : Measure BridgeOpen).map
    (restrict (Nat.find_spec (exists_bridgeHorizon_ge ha1)) ∘
      CompatiblePaths.coord (Nat.find (exists_bridgeHorizon_ge ha1))) = _
  rw [← Measure.map_map (measurable_restrict _)
    (CompatiblePaths.measurable_coord bridgeHorizon strictMono_bridgeHorizon _), hQ]
  exact bridgePrefix_consistent hθ ha (Nat.find_spec (exists_bridgeHorizon_ge ha1))
    (bridgeHorizon_lt_one _) (hP a ha ha1)
    (hP _ (bridgeHorizon_pos _) (bridgeHorizon_lt_one _))

private theorem map_withDensity_comp {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) {f : α → β} (hf : Measurable f) {w : β → ℝ≥0∞}
    (hw : Measurable w) :
    (μ.withDensity (w ∘ f)).map f = (μ.map f).withDensity w := by
  apply Measure.ext
  intro A hA
  rw [Measure.map_apply hf hA, withDensity_apply _ (hf hA), withDensity_apply _ hA,
    ← lintegral_indicator (hf hA), ← lintegral_indicator hA,
    lintegral_map (hw.indicator hA) hf]
  apply lintegral_congr
  intro x
  by_cases hx : f x ∈ A <;> simp [hx]

/-- The endpoint marginal of a tilted prefix has the product of the two increment densities. -/
theorem map_endpoint_bridgePrefixLaw {θ a : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    (ha : 0 < a) {P : ProbabilityMeasure (D a ℝ)} (hP : IsStableLevyLaw θ a P) :
    (bridgePrefixLaw θ a ha.le (P : Measure (D a ℝ))).map
        (fun f => f ⟨a, ha.le, le_rfl⟩) =
      volume.withDensity (fun x => ENNReal.ofReal (stableDensityAt θ a x) *
        ENNReal.ofReal (stableDensityAt θ (1 - a) (-x) / Scalar.stableDensity θ 0)) := by
  have hPeq : P = stableProcessLaw θ a :=
    hP.unique hθ ha (isStableLevyLaw_stableProcessLaw hθ ha)
  let e : D a ℝ → ℝ := fun f => f ⟨a, ha.le, le_rfl⟩
  let w : ℝ → ℝ≥0∞ := fun x =>
    ENNReal.ofReal (stableDensityAt θ (1 - a) (-x) / Scalar.stableDensity θ 0)
  have he : Measurable e := BGW.Skorokhod.measurable_eval _
  have hw : Measurable w :=
    (((stableDensityAt_continuous hθ).measurable.comp measurable_neg).div_const _).ennreal_ofReal
  change ((P : Measure (D a ℝ)).withDensity (w ∘ e)).map e = _
  rw [map_withDensity_comp _ he hw, hPeq,
    map_eval_stableProcessLaw hθ ha _ ha, stableLawAt_eq_withDensity hθ ha]
  exact (withDensity_mul volume (stableDensityAt_continuous hθ).measurable.ennreal_ofReal hw).symm

/-- One-dimensional endpoint reflection for complementary bridge times. -/
theorem bridgePrefix_endpoint_abs_tail_symm {θ a ε : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    (ha : 0 < a) (ha1 : a < 1)
    {P : ProbabilityMeasure (D a ℝ)} (hP : IsStableLevyLaw θ a P)
    {P' : ProbabilityMeasure (D (1 - a) ℝ)} (hP' : IsStableLevyLaw θ (1 - a) P') :
    bridgePrefixLaw θ a ha.le (P : Measure (D a ℝ))
        {f | ε < |f ⟨a, ha.le, le_rfl⟩|} =
      bridgePrefixLaw θ (1 - a) (by linarith) (P' : Measure (D (1 - a) ℝ))
        {f | ε < |f ⟨1 - a, by linarith, le_rfl⟩|} := by
  have hb : 0 < 1 - a := sub_pos.mpr ha1
  let A : Set ℝ := {x | ε < |x|}
  have hA : MeasurableSet A := measurableSet_lt measurable_const continuous_abs.measurable
  change bridgePrefixLaw θ a ha.le (P : Measure (D a ℝ))
      ((fun f : D a ℝ => f ⟨a, ha.le, le_rfl⟩) ⁻¹' A) =
    bridgePrefixLaw θ (1 - a) hb.le (P' : Measure (D (1 - a) ℝ))
      ((fun f : D (1 - a) ℝ => f ⟨1 - a, hb.le, le_rfl⟩) ⁻¹' A)
  rw [← Measure.map_apply (BGW.Skorokhod.measurable_eval _) hA,
    ← Measure.map_apply (BGW.Skorokhod.measurable_eval _) hA,
    map_endpoint_bridgePrefixLaw hθ ha hP, map_endpoint_bridgePrefixLaw hθ hb hP',
    withDensity_apply _ hA, withDensity_apply _ hA, ← lintegral_indicator hA,
    ← lintegral_indicator hA]
  rw [← lintegral_neg_eq_self (μ := (volume : Measure ℝ))]
  apply lintegral_congr
  intro x
  simp only [indicator_apply, A, mem_ofPred_eq, abs_neg, neg_neg,
    show 1 - (1 - a) = a by ring]
  split_ifs
  · rw [ENNReal.ofReal_div_of_pos (Scalar.stableDensity_zero_pos hθ),
      ENNReal.ofReal_div_of_pos (Scalar.stableDensity_zero_pos hθ)]
    simp only [div_eq_mul_inv]
    ac_rfl
  · rfl

end BGW.StableTrees
