/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.SupremumLocalTimeIdentInverse

/-!
# Identification of the public local time at the supremum

Every simultaneous occupation sequence converges locally uniformly to the auxiliary clock.
The public clock inherits its Stieltjes support and ladder geometry. Its inverse has an
everywhere measurable representative and an almost surely equal stopping-time representative.

## References

* J. Bertoin, *Lévy Processes*, Cambridge University Press, 1996, Chapters IV and VI.
* T. Duquesne and J.-F. Le Gall, *Random Trees, Lévy Processes and Spatial Branching Processes*,
  Astérisque 281 (2002), Section 1.1.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees

private theorem inverse_eq_aux {θ : ℝ} {f : DLoc}
    (he : ∀ t, supLocalTime θ f t = supAuxLocalTime θ f t) (z : ℝ≥0) :
    supLocalTimeInverse θ f z = supAuxInverse θ f z := by
  unfold supLocalTimeInverse supAuxInverse
  simp_rw [he]

private theorem ladderTime_eq_aux {θ : ℝ} {f : DLoc}
    (he : ∀ t, supLocalTime θ f t = supAuxLocalTime θ f t) (z : ℝ≥0) :
    supLadderTime θ z f = supAuxLadderTime θ z f := by
  unfold supLadderTime supAuxLadderTime
  rw [inverse_eq_aux he]

private theorem ladderHeight_eq_aux {θ : ℝ} {f : DLoc}
    (he : ∀ t, supLocalTime θ f t = supAuxLocalTime θ f t) (z : ℝ≥0) :
    supLadderHeight θ z f = supAuxLadderHeight θ z f := by
  unfold supLadderHeight supAuxLadderHeight
  rw [ladderTime_eq_aux he]

/-- The public ladder processes equal the auxiliary ones at every level simultaneously. -/
theorem ae_supLadder_eq_aux {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∀ z : ℝ≥0,
      supLadderTime θ z f = supAuxLadderTime θ z f ∧
        supLadderHeight θ z f = supAuxLadderHeight θ z f := by
  filter_upwards [ae_supLocalTime_eq_aux hθ] with f he
  exact fun z => ⟨ladderTime_eq_aux he z, ladderHeight_eq_aux he z⟩

/-- Simultaneous finiteness, monotonicity, right continuity and inversion of the public ladder. -/
theorem ae_supLadder_spec {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc),
      (∀ z : ℝ≥0, supLocalTimeInverse θ f z = (supLadderTime θ z f : WithTop ℝ≥0)) ∧
        supLadderTime θ 0 f = 0 ∧ Monotone (fun z => supLadderTime θ z f) ∧
        (∀ z, ContinuousWithinAt (fun z => supLadderTime θ z f) (Ici z) z) ∧
        Monotone (fun z => supLadderHeight θ z f) ∧
        ∀ z : ℝ≥0, supLocalTime θ f (supLadderTime θ z f) = z := by
  filter_upwards [ae_supLocalTime_eq_aux hθ, ae_supAuxLadder_spec hθ] with f he hf
  simp_rw [inverse_eq_aux he, ladderTime_eq_aux he, ladderHeight_eq_aux he, he]
  exact ⟨hf.1, hf.2.1, hf.2.2.1, hf.2.2.2.1, hf.2.2.2.2.2.1,
    hf.2.2.2.2.2.2.1⟩

/-- Extra simultaneous geometry: unbounded ladder time, finite stopping representatives,
contact at ladder times, evaluation of ladder height, and right continuity of ladder height. -/
theorem ae_supLadder_geometry {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc),
      Tendsto (fun z => supLadderTime θ z f) atTop atTop ∧
      (∀ z : ℝ≥0, supHitting θ z f = (supLadderTime θ z f : ℝ≥0∞)) ∧
      (∀ z : ℝ≥0, supReflected f (supLadderTime θ z f) = 0) ∧
      (∀ z : ℝ≥0, supLadderHeight θ z f = f.1 (supLadderTime θ z f)) ∧
      ∀ z : ℝ≥0, ContinuousWithinAt (fun z => supLadderHeight θ z f) (Ici z) z := by
  filter_upwards [ae_supLocalTime_eq_aux hθ, ae_supLocalTimeENN_eq_aux hθ,
    ae_supAuxLadder_spec hθ] with f he hENN hf
  have hfin : ∀ t, supLocalTimeENN θ f t ≠ ⊤ := by
    intro t
    rw [hENN t]
    exact ENNReal.ofReal_ne_top
  have hA : Monotone (fun z => supLadderTime θ z f) := by
    simpa only [ladderTime_eq_aux he] using hf.2.2.1
  have hright (z : ℝ≥0) : ContinuousWithinAt (fun z => supLadderTime θ z f) (Ici z) z := by
    simpa only [ladderTime_eq_aux he] using hf.2.2.2.1 z
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa only [ladderTime_eq_aux he] using hf.2.2.2.2.1
  · intro z
    rw [supHitting_eq_inverse_of_finite θ f z hfin, inverse_eq_aux he,
      hf.1 z, ladderTime_eq_aux he]
    rfl
  · intro z
    rw [ladderTime_eq_aux he]
    exact hf.2.2.2.2.2.2.2.1 z
  · intro z
    simpa only [ladderTime_eq_aux he, ladderHeight_eq_aux he] using hf.2.2.2.2.2.2.2.2 z
  · intro z
    have hS : ContinuousWithinAt (supRunning f) (Ici (supLadderTime θ z f))
        (supLadderTime θ z f) :=
      continuousWithinAt_Ioi_iff_Ici.mp ((isCadlag_supRunning f).isRightContinuous _)
    change ContinuousWithinAt (fun u => supRunning f (supLadderTime θ u f)) (Ici z) z
    exact ContinuousWithinAt.comp (f := fun u : ℝ≥0 => supLadderTime θ u f)
      (g := supRunning f) (s := Ici z) hS (hright z) (fun u hu => hA hu)

end BGW.StableTrees
