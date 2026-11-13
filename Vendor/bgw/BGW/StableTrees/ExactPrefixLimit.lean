/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.ExactPrefixWeights
public import BGW.StableTrees.PathTail
import BGW.StableTrees.GammaIdentity
import BGW.Skorokhod.MeasurableJumps

/-!
# Good endpoints of tail-excursion prefixes

The absence of fixed jumps under the excursion measure transfers to its normalized tail.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal Classical
open BGW.StableTrees.DiscreteBridge (endValue)
open BGW.StableTrees.PathTail (tailPrefixLimit)

namespace BGW.StableTrees.ExactPrefix

open BGW BGW.Skorokhod

/-- The tail-excursion prefix is almost surely continuous at `a` with positive value
(`N_noFixedJump`, `tailExcursionLaw ≪ N`, positivity before the end). -/
theorem ae_tailPrefix_continuousAt_pos {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (a : ℝ≥0)
    (ha : a ∈ Ioo (0 : ℝ≥0) 1) :
    ∀ᵐ x : D (a : ℝ) ℝ ∂(tailPrefixLimit θ a : Measure (D (a : ℝ) ℝ)),
      ContinuousAt x ⟨(a : ℝ), a.coe_nonneg, le_rfl⟩ ∧ 0 < endValue a x := by
  let t : Icc (0 : ℝ) a := ⟨a, a.coe_nonneg, le_rfl⟩
  have hleft : ∀ᵐ x : D (a : ℝ) ℝ ∂(tailPrefixLimit θ a : Measure (D (a : ℝ) ℝ)),
      Function.leftLim x t = x t := by
    change ∀ᵐ x ∂((tailExcursionLaw θ : Measure Excursion).map (excursionRestrict a)), _
    apply (ae_map_iff (measurable_excursionRestrict a).aemeasurable
      (measurableSet_eq_fun (measurable_leftLim_eval t) (measurable_eval t))).mpr
    rw [coe_tailExcursionLaw hθ, tailExcursionMeasure]
    apply Measure.ae_smul_measure
    have hj := ae_restrict_of_ae (s := {e : Excursion | (1 : ℝ) < (e.lifetime : ℝ)})
      (N_noFixedJump hθ a ha.1)
    filter_upwards [hj] with e he
    rw [leftLim_excursionRestrict a a ha.1 le_rfl e]
    exact he
  have hpos : ∀ᵐ x ∂(tailPrefixLimit θ a : Measure (D (a : ℝ) ℝ)),
      0 < endValue a x := ae_evalEnd_pos_tailPrefix hθ a ha
  filter_upwards [hleft, hpos] with x hl hp
  refine ⟨?_, hp⟩
  rw [continuousAt_iff_continuous_left'_right']
  refine ⟨?_, (isCadlag x).isRightContinuous _⟩
  change Tendsto x (𝓝[<] t) (𝓝 (x t))
  simpa only [hl] using (isCadlag x).tendsto_nhdsLT_leftLim t

end BGW.StableTrees.ExactPrefix
