/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.SupremumLocalTimeIdent
import BGW.StableTrees.SupremumStoppedEnergy

/-!
# Stopped occupation estimates for the public supremum local time

The almost sure identifications of the public clock and its ladder times with their
auxiliary counterparts transfer the stopped second moments and full-filter convergence.

Reference: J. Bertoin, *Lévy Processes*, Cambridge University Press, 1996, Chapter IV.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees

/-- **Stopped second-moment bound**: for each level `z` there is `C` bounding, uniformly in
`ε ∈ (0, 1]`, the second moment of the approximation stopped at the ladder time `A_z`; the
squared approximation is integrable. -/
theorem supOccupation_stopped_L2_bound {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (z : ℝ≥0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      Integrable (fun f => (supOccupation ε f (supLadderTime θ z f)) ^ 2)
          (stableLocalLaw θ : Measure DLoc) ∧
      ∫ f, (supOccupation ε f (supLadderTime θ z f)) ^ 2 ∂(stableLocalLaw θ : Measure DLoc) ≤ C :=
  by
  obtain ⟨C, hC, hbound⟩ := supOccupation_stopped_L2_bound_aux hθ z
  refine ⟨C, hC, fun ε hε hε1 => ?_⟩
  have he : (fun f => (supOccupation ε f (supAuxLadderTime θ z f)) ^ 2) =ᵐ[
      (stableLocalLaw θ : Measure DLoc)]
      (fun f => (supOccupation ε f (supLadderTime θ z f)) ^ 2) := by
    filter_upwards [ae_supLadder_eq_aux hθ] with f hf
    rw [(hf z).1]
  exact ⟨(hbound ε hε hε1).1.congr he,
    (integral_congr_ae he).symm.trans_le (hbound ε hε hε1).2⟩

/-- **Stopped `L²` convergence**: `E[(supOccupation ε f (A_z) - z)²] → 0` as `ε ↓ 0`,
consistent with `M(A_z) = z`. The auxiliary clock is constructed from compact-time estimates
before the public choice of `supEps`; this public stopped theorem follows by the
identification of the public local time and the stopped energy estimate. -/
theorem supOccupation_stopped_L2_tendsto {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (z : ℝ≥0) :
    (∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      Integrable (fun f => (supOccupation ε f (supLadderTime θ z f) - (z : ℝ)) ^ 2)
        (stableLocalLaw θ : Measure DLoc)) ∧
    Tendsto (fun ε : ℝ =>
        ∫ f, (supOccupation ε f (supLadderTime θ z f) - (z : ℝ)) ^ 2
          ∂(stableLocalLaw θ : Measure DLoc)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have he (ε : ℝ) :
      (fun f => (supOccupation ε f (supAuxLadderTime θ z f) - (z : ℝ)) ^ 2) =ᵐ[
        (stableLocalLaw θ : Measure DLoc)]
      (fun f => (supOccupation ε f (supLadderTime θ z f) - (z : ℝ)) ^ 2) := by
    filter_upwards [ae_supLadder_eq_aux hθ] with f hf
    rw [(hf z).1]
  obtain ⟨hi, ht⟩ := supOccupation_stopped_L2_tendsto_aux hθ z
  refine ⟨fun ε hε hε1 => (hi ε hε hε1).congr (he ε), ?_⟩
  exact (tendsto_congr (fun ε => (integral_congr_ae (he ε)).symm)).mpr ht

/-- **Stopped Cauchy bound**: the approximations stopped at `A_z` converge to `M(A_z) = z`
uniformly over the stopped time interval, in probability, as `ε ↓ 0` along the full filter. -/
theorem supOccupation_stopped_uniform_tendstoInMeasure {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (z : ℝ≥0)
    (δ : ℝ) (hδ : 0 < δ) :
    Tendsto (fun ε : ℝ =>
        (stableLocalLaw θ : Measure DLoc)
          {f | δ ≤ ⨆ t : Set.Iic (supLadderTime θ z f),
              |supOccupation ε f t - supLocalTime θ f t|})
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have he (ε : ℝ) :
      (stableLocalLaw θ : Measure DLoc)
          {f | δ ≤ ⨆ t : Set.Iic (supLadderTime θ z f),
            |supOccupation ε f t - supLocalTime θ f t|} =
        (stableLocalLaw θ : Measure DLoc)
          {f | δ ≤ ⨆ t : Set.Iic (supAuxLadderTime θ z f),
            |supOccupation ε f t - supAuxLocalTime θ f t|} := by
    apply measure_congr
    filter_upwards [ae_supLadder_eq_aux hθ, ae_supLocalTime_eq_aux hθ] with f hA hM
    have hclock : supLocalTime θ f = supAuxLocalTime θ f := funext hM
    rw [(hA z).1, hclock]
  exact (tendsto_congr he).mpr
    (supOccupation_stopped_uniform_tendstoInMeasure_aux hθ z δ hδ)

end BGW.StableTrees
