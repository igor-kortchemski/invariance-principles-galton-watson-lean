/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.Skorokhod.Jump
public import BGW.StableTrees.WalkPathTightness
import Mathlib.Topology.Order.LeftRightLim

/-!
# Negative jumps and the offspring step-path bound

Negation preserves J1 distance. An offspring walk has steps at least `-1`, so its normalized
step paths have negative jumps bounded by the reciprocal normalizer, including at the horizon.
The jump functional is that of Billingsley, *Convergence of Probability Measures*, 2nd ed.,
1999, Section 13.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology

namespace BGW.Skorokhod

/-- Negation of a real càdlàg path. -/
def negPath {T : ℝ} (f : D T ℝ) : D T ℝ :=
  ⟨fun t => -f t, (isCadlag f).continuous_comp continuous_neg⟩

/-- Negation preserves the J1 metric. -/
theorem isometry_negPath {T : ℝ} : Isometry (negPath (T := T)) := by
  apply Isometry.of_dist_eq
  intro f g
  simp only [dist_eq_j1Dist, j1Dist, negPath, coe_mk, dist_neg_neg]

/-- The largest negative jump of a real càdlàg path. -/
noncomputable def maxNegativeJump {T : ℝ} (f : D T ℝ) : ℝ := maxJump (negPath f)

/-- The largest negative jump is continuous in J1. -/
theorem continuous_maxNegativeJump {T : ℝ} : Continuous (maxNegativeJump (T := T)) :=
  lipschitzWith_two_maxJump.continuous.comp isometry_negPath.continuous

private theorem leftLim_negPath {T : ℝ} (f : D T ℝ) (t : Icc (0 : ℝ) T) :
    Function.leftLim (negPath f) t = -Function.leftLim f t := by
  rcases eq_or_neBot (𝓝[<] t) with ht | ht
  · rw [leftLim_eq_of_eq_bot _ ht, leftLim_eq_of_eq_bot _ ht]
    rfl
  · exact leftLim_eq_of_tendsto ((isCadlag f).tendsto_nhdsLT_leftLim t).neg

private theorem bddAbove_negative_jump {T : ℝ} (f : D T ℝ) :
    BddAbove (range fun t => max (Function.leftLim f t - f t) 0) := by
  obtain ⟨C, hC⟩ := Metric.isBounded_range_iff.mp (isBounded_range f)
  refine ⟨max C 0, ?_⟩
  rintro _ ⟨t, rfl⟩
  apply max_le _ (le_max_right _ _)
  rcases eq_or_neBot (𝓝[<] t) with ht | ht
  · rw [leftLim_eq_of_eq_bot _ ht, sub_self]
    exact le_max_right _ _
  · have hbound : dist (Function.leftLim f t) (f t) ≤ C :=
      isClosed_Iic.mem_of_tendsto
        (((isCadlag f).tendsto_nhdsLT_leftLim t).dist tendsto_const_nhds)
        (Eventually.of_forall fun s => hC s t)
    rw [Real.dist_eq] at hbound
    exact (le_abs_self _).trans (hbound.trans (le_max_left _ _))

/-- A uniform bound on all negative jumps is equivalent to a bound on their maximum. -/
theorem maxNegativeJump_le_iff {T c : ℝ} (hT : 0 ≤ T) (hc : 0 ≤ c) (f : D T ℝ) :
    maxNegativeJump f ≤ c ↔ ∀ t, Function.leftLim f t - f t ≤ c := by
  have : Nonempty (Icc (0 : ℝ) T) := ⟨⟨0, le_rfl, hT⟩⟩
  have heq : maxNegativeJump f = ⨆ t, max (Function.leftLim f t - f t) 0 := by
    unfold maxNegativeJump maxJump
    apply iSup_congr
    intro t
    rw [leftLim_negPath]
    change max (-f t - -Function.leftLim f t) 0 = _
    congr 1
    ring
  rw [heq]
  constructor
  · intro h t
    exact (le_max_left _ _).trans ((le_ciSup (bddAbove_negative_jump f) t).trans h)
  · intro h
    exact ciSup_le fun t => max_le (h t) hc

/-- For steps at least `-1` and a positive normalizer, every negative jump of the step path
is at most the reciprocal normalizer. -/
theorem leftLim_sub_realStepPath_le {T b : ℝ} (n : ℕ) (hb : 0 < b)
    (ω : ℕ → ℝ) (hω : ∀ i, -1 ≤ ω i) (t : Icc (0 : ℝ) T) :
    Function.leftLim (realStepPath T n b ω) t - realStepPath T n b ω t ≤ 1 / b := by
  let f := realStepPath T n b ω
  rcases eq_or_neBot (𝓝[<] t) with ht | ht
  · rw [leftLim_eq_of_eq_bot _ ht, sub_self]
    positivity
  · let k := ⌊(n : ℝ) * (t : ℝ)⌋₊
    have hk : (k : ℝ) - 1 < (n : ℝ) * (t : ℝ) := by
      have hh := Nat.floor_le (mul_nonneg (Nat.cast_nonneg n) t.property.1)
      change (k : ℝ) ≤ (n : ℝ) * (t : ℝ) at hh
      linarith
    have hnear : ∀ᶠ s : Icc (0 : ℝ) T in 𝓝[<] t,
        (k : ℝ) - 1 < (n : ℝ) * (s : ℝ) :=
      by
        have hmul : Continuous (fun s : Icc (0 : ℝ) T => (n : ℝ) * (s : ℝ)) := by
          fun_prop
        have hh : ∀ᶠ s : Icc (0 : ℝ) T in 𝓝 t,
            (k : ℝ) - 1 < (n : ℝ) * (s : ℝ) :=
          (hmul.tendsto t).eventually (lt_mem_nhds hk)
        exact hh.filter_mono nhdsWithin_le_nhds
    have hbound : ∀ᶠ s in 𝓝[<] t, f s - f t ≤ 1 / b := by
      filter_upwards [hnear, self_mem_nhdsWithin] with s hs hst
      let j := ⌊(n : ℝ) * (s : ℝ)⌋₊
      have hjk : j ≤ k := Nat.floor_mono
        (mul_le_mul_of_nonneg_left (le_of_lt hst) (Nat.cast_nonneg n))
      have hkj : k ≤ j + 1 := by
        have hj := Nat.lt_floor_add_one ((n : ℝ) * (s : ℝ))
        change (n : ℝ) * (s : ℝ) < (j : ℝ) + 1 at hj
        have hh : (k : ℝ) < (j + 2 : ℕ) := by push_cast; linarith
        have hh' : k < j + 2 := by exact_mod_cast hh
        omega
      have hsum : BGW.Probability.RealWalk.partialSum ω j -
          BGW.Probability.RealWalk.partialSum ω k ≤ 1 := by
        rcases Nat.eq_or_lt_of_le hjk with heq | hlt
        · rw [heq, sub_self]
          norm_num
        · have heq : k = j + 1 := by omega
          rw [heq]
          simp only [BGW.Probability.RealWalk.partialSum, Finset.sum_range_succ]
          linarith [hω j]
      change BGW.Probability.RealWalk.partialSum ω j / b -
        BGW.Probability.RealWalk.partialSum ω k / b ≤ 1 / b
      rw [← sub_div]
      exact div_le_div_of_nonneg_right hsum hb.le
    exact isClosed_Iic.mem_of_tendsto
      (((isCadlag f).tendsto_nhdsLT_leftLim t).sub tendsto_const_nhds) hbound

end BGW.Skorokhod
