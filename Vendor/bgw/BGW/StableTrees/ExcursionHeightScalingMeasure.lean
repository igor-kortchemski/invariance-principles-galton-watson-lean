/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.ExcursionHeightScalingApprox
public import BGW.StableTrees.ExcursionHeightAgeIdentification
import BGW.StableTrees.ExcursionLifetimeScaling

public import BGW.Probability.ConvergenceInMeasure

/-!
# Dilation of surviving excursion age measures

Continuous real tests preserve convergence in measure along countably generated filters.
Time dilation and excursion scaling preserve null sets. Restricting their product to
surviving bounded age windows gives the transfer needed for universal-subsequence limits.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal Classical
open BGW.Skorokhod

namespace BGW.StableTrees

/-- Joint age/mark dilation preserves null sets on the corresponding surviving age windows. -/
theorem quasiMeasurePreserving_excursion_age_scale {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    (c : Ioi (0 : ℝ)) (S : ℝ≥0) :
    QuasiMeasurePreserving
      (fun p : ℝ × Excursion => ((c : ℝ) * p.1, excursionScale θ c p.2))
      (heightExcursionAgeMeasure θ S)
      (heightExcursionAgeMeasure θ ((c : ℝ).toNNReal * S)) := by
  let := sigmaFinite_excursionMeasure hθ
  have ht : QuasiMeasurePreserving (fun s : ℝ => (c : ℝ) * s) volume volume := by
    refine ⟨measurable_const.mul measurable_id, ?_⟩
    rw [Real.map_volume_mul_left c.2.ne']
    exact Measure.smul_absolutelyContinuous
  have ht' : QuasiMeasurePreserving (fun s : ℝ => (c : ℝ) * s)
      (volume.restrict (Ioo (0 : ℝ) (S : ℝ)))
      (volume.restrict (Ioo (0 : ℝ) (((c : ℝ).toNNReal * S : ℝ≥0) : ℝ))) := by
    apply ht.restrict
    intro s hs
    rw [NNReal.coe_mul, Real.coe_toNNReal _ c.2.le]
    exact ⟨mul_pos c.2 hs.1, mul_lt_mul_of_pos_left hs.2 c.2⟩
  have he : QuasiMeasurePreserving (excursionScale θ c) (excursionMeasure θ)
      (excursionMeasure θ) := by
    refine ⟨measurable_excursionScale θ c, ?_⟩
    rw [map_excursionScale_excursionMeasure hθ c]
    exact Measure.smul_absolutelyContinuous
  rw [heightExcursionAgeMeasure, heightExcursionAgeMeasure]
  apply (ht'.prodMap he).restrict
  intro p hp
  change ((c : ℝ) * p.1).toNNReal < (excursionScale θ c p.2).lifetime
  rw [Real.toNNReal_mul c.2.le]
  change (c : ℝ).toNNReal * p.1.toNNReal < (c : ℝ).toNNReal * p.2.lifetime
  exact mul_lt_mul_of_pos_left hp (Real.toNNReal_pos.mpr c.2)

end BGW.StableTrees
