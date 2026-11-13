/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.HeightProcess
public import BGW.StableTrees.HeightBridgesExcursionLimit
public import BGW.StableTrees.HeightBridgesUnitTransfer
public import BGW.StableTrees.HeightBridgesExcursionMoment
public import BGW.StableTrees.HeightBridgesUniversalLimits
public import BGW.StableTrees.HeightBridgesTail
import BGW.StableTrees.StableLocalMarkov

/-!
# Height bridges from exploration erasure

The common reversed clock identifies the surviving support top and the fresh height.
Erasure preserves every upper support bound, including complete erasure.
The approximation has measurable limits under the excursion and unit laws. Predicate
diagonalization supplies one sequence for the stable, excursion and unit laws, both at rational
ages and at almost every age. The universal height is the literal limsup along that sequence.
The erased-height tail uses the ancestral source, a passage-stopped reversed clock, independence
of the fresh depth, and the full stable ladder transform. No continuation of the reversed path
is constructed.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees

/-- A mass-free upper tail bounds the support top after erasure. -/
theorem topHeight_eraseMass_le {ρ : Measure ℝ≥0} {R : ℝ≥0}
    (hρ : ρ (Ioi R) = 0) (m : ℝ≥0∞) : topHeight (eraseMass m ρ) ≤ R := by
  exact csSup_le' fun _ hh => support_le_of_mass_above_zero (eraseMass_Ioi_eq_zero hρ m) hh

/-- **Erasure decomposition** (fixed `t`, `r`): with `m` the mass erased by the future infimum
and `K` the height of what survives erasure, a.s. `0 ≤ K ≤ H_t` and `H_{t+r} = K + H'_r`. -/
theorem ae_height_erasure_decomposition {θ : ℝ}
    (hθ : 1 < θ ∧ θ ≤ 2) (t r : ℝ≥0) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc),
      let m := ENNReal.ofReal (-(futureInf (DLoc.shift t f) r 0))
      let K := (topHeight (eraseMass m (exploration θ f t)) : ℝ)
      0 ≤ K ∧ K ≤ height θ f t ∧
        height θ f (t + r) = K + height θ (DLoc.shift t f) r := by
  by_cases hr : r = 0
  · subst r
    filter_upwards [ae_topHeight_exploration hθ t] with f hf
    have hI : futureInf (DLoc.shift t f) 0 0 = 0 := by
      rw [futureInf_self]
      change f.1 (t + 0) - f.1 t = 0
      simp
    simp only [hI, neg_zero, ENNReal.ofReal_zero, eraseMass_zero, add_zero, height_zero]
    exact ⟨NNReal.coe_nonneg _, hf.le, hf.symm⟩
  have hrpos : 0 < r := pos_iff_ne_zero.mpr hr
  filter_upwards [ae_topHeight_erased_exploration hθ t r hrpos,
    ae_continuousAt_stableLocalLaw hθ t, ae_exploration_above_height hθ t,
    ae_heightRaw_eq hθ t] with f htop ht habove hheight
  dsimp only
  refine ⟨NNReal.coe_nonneg _, ?_, ?_⟩
  · exact (NNReal.coe_le_coe.mpr (topHeight_eraseMass_le habove _)).trans_eq
      (Real.coe_toNNReal _ hheight.1)
  · have hleft : Function.leftLim f.1 t = f.1 t := ht.continuousWithinAt.leftLim_eq
    change supLocalTime θ (reversedAt (t + r) f) (t + r) = _
    rw [htop, height, supLocalTime_reversedAt_shift_prefix θ f t r hleft le_rfl]
    ring

end BGW.StableTrees
