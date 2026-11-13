/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.SupremumAuxLocalTimeMeanBounds
public import BGW.StableTrees.ExcursionLifetimeScaling

/-!
# Scaling of the auxiliary clock

Deterministic scaling of the occupations and convergence in mean identify the clock under
stable path dilation. The selected cutoff sequence need not be preserved by dilation.

## References

* J. Bertoin, *Lévy Processes*, Cambridge University Press, 1996, Chapter IV.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees

/-- The running supremum commutes with positive stable path dilation. -/
theorem supRunning_scaleLoc (θ : ℝ) (c : Ioi (0 : ℝ)) (f : DLoc) (t : ℝ≥0) :
    supRunning (scaleLoc θ c f) t = (c : ℝ) ^ (1 / θ) *
      supRunning f (t / (c : ℝ).toNNReal) := by
  have hc : 0 < (c : ℝ).toNNReal := Real.toNNReal_pos.mpr c.2
  have ha : 0 < (c : ℝ) ^ (1 / θ) := Real.rpow_pos_of_pos c.2 _
  apply le_antisymm
  · apply supRunning_le
    intro u
    change (c : ℝ) ^ (1 / θ) * f.1 (u.1 / (c : ℝ).toNNReal) ≤ _
    exact mul_le_mul_of_nonneg_left
      (eval_le_supRunning f ((div_le_div_iff_of_pos_right hc).mpr u.2)) ha.le
  · have hS : supRunning f (t / (c : ℝ).toNNReal) ≤
        supRunning (scaleLoc θ c f) t / (c : ℝ) ^ (1 / θ) := by
      apply supRunning_le
      intro u
      apply (le_div_iff₀ ha).mpr
      have hut : u.1 * (c : ℝ).toNNReal ≤ t := (le_div_iff₀ hc).mp u.2
      have hh := eval_le_supRunning (scaleLoc θ c f) hut
      change (c : ℝ) ^ (1 / θ) * f.1 ((u.1 * (c : ℝ).toNNReal) /
        (c : ℝ).toNNReal) ≤ _ at hh
      rw [mul_div_cancel_right₀ _ hc.ne'] at hh
      simpa only [mul_comm] using hh
    simpa only [mul_comm] using (le_div_iff₀ ha).mp hS

/-- Reflection at the supremum commutes with stable path dilation. -/
theorem supReflected_scaleLoc (θ : ℝ) (c : Ioi (0 : ℝ)) (f : DLoc) (t : ℝ≥0) :
    supReflected (scaleLoc θ c f) t = (c : ℝ) ^ (1 / θ) *
      supReflected f (t / (c : ℝ).toNNReal) := by
  rw [supReflected, supRunning_scaleLoc]
  change (c : ℝ) ^ (1 / θ) * supRunning f (t / (c : ℝ).toNNReal) -
    (c : ℝ) ^ (1 / θ) * f.1 (t / (c : ℝ).toNNReal) = _
  exact (mul_sub _ _ _).symm

/-- Scaling changes the occupation cutoff and contributes the local-time homogeneity factor. -/
theorem supOccupation_scaleLoc (θ ε : ℝ) (c : Ioi (0 : ℝ)) (f : DLoc) (t : ℝ≥0) :
    supOccupation ε (scaleLoc θ c f) t =
      ((c : ℝ) / (c : ℝ) ^ (1 / θ)) *
        supOccupation (ε / (c : ℝ) ^ (1 / θ)) f (t / (c : ℝ).toNNReal) := by
  let a := (c : ℝ) ^ (1 / θ)
  have ha : 0 < a := Real.rpow_pos_of_pos c.2 _
  have htime : ((t / (c : ℝ).toNNReal : ℝ≥0) : ℝ) = (t : ℝ) / (c : ℝ) := by
    rw [NNReal.coe_div, Real.coe_toNNReal _ c.2.le]
  have hset : {u : ℝ | 0 ≤ u ∧ u ≤ (t : ℝ) ∧
      supReflected (scaleLoc θ c f) u.toNNReal < ε} =
      (fun u : ℝ => (c : ℝ)⁻¹ * u) ⁻¹'
        {u : ℝ | 0 ≤ u ∧ u ≤ ((t / (c : ℝ).toNNReal : ℝ≥0) : ℝ) ∧
          supReflected f u.toNNReal < ε / a} := by
    ext u
    by_cases hu : 0 ≤ u
    · have hnn : ((c : ℝ)⁻¹ * u).toNNReal = u.toNNReal / (c : ℝ).toNNReal := by
        rw [← div_eq_inv_mul, Real.toNNReal_div hu]
      simp only [mem_preimage, mem_ofPred_eq, htime, hnn, supReflected_scaleLoc]
      constructor
      · rintro ⟨_, hut, hr⟩
        refine ⟨mul_nonneg (inv_pos.mpr c.2).le hu, ?_, ?_⟩
        · simpa only [div_eq_inv_mul] using (div_le_div_iff_of_pos_right c.2).mpr hut
        · apply (lt_div_iff₀ ha).mpr
          simpa only [a, mul_comm] using hr
      · rintro ⟨_, hut, hr⟩
        refine ⟨hu, ?_, ?_⟩
        · apply (div_le_div_iff_of_pos_right c.2).mp
          simpa only [div_eq_inv_mul] using hut
        · have hh := (lt_div_iff₀ ha).mp hr
          simpa only [a, mul_comm] using hh
    · have hn : (c : ℝ)⁻¹ * u < 0 :=
        mul_neg_of_pos_of_neg (inv_pos.mpr c.2) (lt_of_not_ge hu)
      simp only [mem_preimage, mem_ofPred_eq, hu, not_le.mpr hn, false_and]
  unfold supOccupation
  rw [hset, Real.volume_preimage_mul_left (inv_ne_zero c.2.ne'), inv_inv,
    abs_of_pos c.2, ENNReal.toReal_mul, ENNReal.toReal_ofReal c.2.le]
  rw [inv_div]
  dsimp only [a]
  have hane : (c : ℝ) ^ (1 / θ) ≠ 0 := ha.ne'
  field_simp [hane]

end BGW.StableTrees
