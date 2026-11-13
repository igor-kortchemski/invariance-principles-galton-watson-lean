/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.BridgeProjectiveOpen
public import BGW.StableTrees.StableProcessReversal

/-!
# Reversal of tilted bridge prefixes

Reversing the increments of a strict prefix preserves its tilted law, since the tilt depends
only on its endpoint. This reversal is centered at the prefix endpoint.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open BGW.Skorokhod
open scoped ENNReal

namespace BGW.StableTrees

/-- The bridge prefix is absolutely continuous with respect to its underlying path law. -/
theorem bridgePrefixLaw_absolutelyContinuous (θ a : ℝ) (ha : 0 ≤ a)
    (P : Measure (D a ℝ)) : bridgePrefixLaw θ a ha P ≪ P :=
  withDensity_absolutelyContinuous _ _

/-- A bridge prefix starts at zero almost surely. -/
theorem bridgePrefixLaw_ae_zero {θ a : ℝ} (ha : 0 ≤ a)
    {P : ProbabilityMeasure (D a ℝ)} (hP : IsStableLevyLaw θ a P) :
    ∀ᵐ f ∂bridgePrefixLaw θ a ha (P : Measure (D a ℝ)), f ⟨0, le_rfl, ha⟩ = 0 :=
  (bridgePrefixLaw_absolutelyContinuous θ a ha P).ae_le (hP.start ha)

/-- The open stable bridge starts at zero almost surely. -/
theorem bridgeOpenLaw_ae_zero {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(bridgeOpenLaw θ : Measure BridgeOpen), f.eval 0 = 0 := by
  have hzero := bridgePrefixLaw_ae_zero (bridgeHorizon_pos 0).le
    (isStableLevyLaw_stableProcessLaw hθ (bridgeHorizon_pos 0))
  rw [← map_coord_bridgeOpenLaw hθ 0] at hzero
  have hs : MeasurableSet {g : D (bridgeHorizon 0) ℝ |
      g ⟨0, le_rfl, (bridgeHorizon_pos 0).le⟩ = 0} :=
    (BGW.Skorokhod.measurable_eval _) (measurableSet_singleton 0)
  have hz := (ae_map_iff
    (CompatiblePaths.measurable_coord bridgeHorizon strictMono_bridgeHorizon 0).aemeasurable
    hs).mp hzero
  filter_upwards [hz] with f hf
  rw [BridgeOpen.eval_eq_coord f 0 ⟨0, le_rfl, (bridgeHorizon_pos 0).le⟩]
  exact hf

/-- Reversal centered at the prefix endpoint preserves the tilted prefix law. -/
theorem map_reverseIncrements_bridgePrefixLaw {θ a : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    (ha : 0 < a) {P : ProbabilityMeasure (D a ℝ)} (hP : IsStableLevyLaw θ a P) :
    (bridgePrefixLaw θ a ha.le (P : Measure (D a ℝ))).map (reverseIncrements ha.le) =
      bridgePrefixLaw θ a ha.le (P : Measure (D a ℝ)) := by
  classical
  let R := reverseIncrements ha.le
  let w : D a ℝ → ℝ≥0∞ := fun f => ENNReal.ofReal (bridgePrefixWeight θ a ha.le f)
  have hR : Measurable R := measurable_reverseIncrements ha.le
  have hw : Measurable w := (measurable_bridgePrefixWeight hθ ha.le).ennreal_ofReal
  have hmap : (P : Measure (D a ℝ)).map R = (P : Measure (D a ℝ)) :=
    congrArg (fun Q : ProbabilityMeasure (D a ℝ) => (Q : Measure (D a ℝ)))
      (hP.map_reverseIncrements hθ ha)
  have hweight : ∀ᵐ f ∂(P : Measure (D a ℝ)), w (R f) = w f := by
    filter_upwards [hP.start ha.le] with f hf
    have hbot : IsBot (⟨0, le_rfl, ha.le⟩ : Set.Icc (0 : ℝ) a) := fun t => t.property.1
    have hleft := leftLim_eq_of_isBot (f := f) hbot
    have hend : R f ⟨a, ha.le, le_rfl⟩ = f ⟨a, ha.le, le_rfl⟩ := by
      dsimp [R]
      rw [reverseIncrements_apply]
      simp only [sub_self, hleft, hf, sub_zero]
    simp only [w, bridgePrefixWeight, hend]
  apply Measure.ext
  intro A hA
  change ((P : Measure (D a ℝ)).withDensity w).map R A =
    ((P : Measure (D a ℝ)).withDensity w) A
  rw [Measure.map_apply hR hA, withDensity_apply _ (hR hA), withDensity_apply _ hA]
  calc
    (∫⁻ f in R ⁻¹' A, w f ∂(P : Measure (D a ℝ))) =
        ∫⁻ f, A.indicator w (R f) ∂(P : Measure (D a ℝ)) := by
      rw [← lintegral_indicator (hR hA)]
      apply lintegral_congr_ae
      filter_upwards [hweight] with f hf
      by_cases hmem : R f ∈ A <;> simp [hmem, hf]
    _ = ∫⁻ f, A.indicator w f ∂(P : Measure (D a ℝ)).map R :=
      (lintegral_map (hw.indicator hA) hR).symm
    _ = ∫⁻ f in A, w f ∂(P : Measure (D a ℝ)) := by
      rw [hmap, lintegral_indicator hA]

end BGW.StableTrees
