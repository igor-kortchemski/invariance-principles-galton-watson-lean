/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.ExcursionHeightIdentification
public import BGW.StableTrees.ExcursionHeightUnitVersion

/-!
# Fixed-age unit identification through the common prefix graph

The finite prefix density transfers full-filter convergence after both laws' continuous
heights have been identified with the same measurable prefix functional.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal Classical
open BGW.Skorokhod
open BGW.Probability

namespace BGW.StableTrees

/-- **Identification under the unit law** at ages `0 < t < 1`. -/
theorem heightApprox_tendstoInMeasure_excursionHeight_unit {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    (t : ℝ≥0) (ht0 : 0 < t) (ht1 : t < 1) :
    TendstoInMeasure (unitExcursionLaw θ : Measure Excursion)
      (fun (ε : ℝ) (e : Excursion) => heightApprox ε e.path t) (𝓝[>] (0 : ℝ))
      (fun e => excursionHeight θ e t) := by
  let v : Icc (0 : ℝ) (t : ℝ) := ⟨t, t.2, le_rfl⟩
  let F : D (t : ℝ) ℝ → ℝ := fun g => heightPrefixAE θ t g v
  have hF : Measurable F :=
    (ContinuousMap.measurable_eval v).comp (measurable_heightPrefixAE θ t)
  have hN := heightApprox_tendstoInMeasure_excursionHeight hθ t ht0
  have heqN : (fun e => excursionHeight θ e t) =ᵐ[
      (excursionMeasure θ).restrict {e : Excursion | t < e.lifetime}]
      (fun e => F (excursionRestrict t e)) := by
    filter_upwards [ae_restrict_heightPrefixAE_excursionRestrict hθ t] with e he
    exact (he v).symm
  have hbase := (tendstoInMeasure_map_iff (measurable_excursionRestrict t)
    (fun ε => measurable_horizonHeightApprox ε t) hF).mpr
    (show TendstoInMeasure
      ((excursionMeasure θ).restrict {e : Excursion | t < e.lifetime})
      (fun ε e => horizonHeightApprox ε t (excursionRestrict t e))
      (𝓝[>] (0 : ℝ)) (fun e => F (excursionRestrict t e)) from by
        simpa only [excursionRestrict, horizonHeightApprox_restrict] using
          TendstoInMeasure.congr_right heqN hN)
  let : IsFiniteMeasure (unitPrefix θ t) := by unfold unitPrefix; infer_instance
  have hu := tendstoInMeasure_of_absolutelyContinuous
    (unitPrefix_absolutelyContinuous_excursion hθ t ht0 ht1)
    (fun ε => measurable_horizonHeightApprox ε t) hbase
  have hunit := (tendstoInMeasure_map_iff (measurable_excursionRestrict t)
    (fun ε => measurable_horizonHeightApprox ε t) hF).mp hu
  have heq : (fun e => F (excursionRestrict t e)) =ᵐ[
      (unitExcursionLaw θ : Measure Excursion)] (fun e => excursionHeight θ e t) := by
    filter_upwards [ae_heightPrefixAE_unitExcursionLaw hθ,
      ae_lifetime_unitExcursionLaw hθ] with e he hl
    exact he t (hl ▸ ht1) v
  simpa only [excursionRestrict, horizonHeightApprox_restrict] using
    TendstoInMeasure.congr_right heq hunit

end BGW.StableTrees
