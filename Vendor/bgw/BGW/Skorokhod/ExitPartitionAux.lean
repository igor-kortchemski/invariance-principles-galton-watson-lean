/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.Skorokhod.Tightness
public import BGW.Probability.RealWalk
import Mathlib.Topology.Algebra.Order.Floor

/-!
# Auxiliary lemmas for real step paths

The rescaled step path of a real walk is càdlàg; first-exit and last-exit facts used by the
exit-partition bound on Billingsley's modulus.
-/

@[expose] public section

open Filter Set
open scoped Topology

namespace BGW.Skorokhod

open BGW.Probability.RealWalk

private theorem tendsto_natFloor_right (x : ℝ) :
    Tendsto (fun y : ℝ => ⌊y⌋₊) (𝓝[≥] x) (pure ⌊x⌋₊) := by
  have h : Tendsto (fun y : ℝ => ⌊y⌋₊) (𝓝[≥] x) (pure ⌊x⌋₊) := by
    rw [← Int.floor_toNat]
    exact (tendsto_pure_pure (fun z : ℤ => z.toNat) _).comp
      (tendsto_floor_right_pure_floor x)
  exact h

private theorem isCadlag_realStep (n : ℕ) (b : ℝ) (ω : ℕ → ℝ) (hn : 0 < n) :
    IsCadlag (fun t : ℝ => partialSum ω ⌊(n : ℝ) * t⌋₊ / b) := by
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  constructor
  · intro x
    have hx : Tendsto (fun y : ℝ => (n : ℝ) * y) (𝓝[>] x)
        (𝓝[≥] ((n : ℝ) * x)) := by
      apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      · exact (continuous_const.mul continuous_id).continuousAt.continuousWithinAt
      · filter_upwards [self_mem_nhdsWithin] with y hy
        change (n : ℝ) * x ≤ (n : ℝ) * y
        exact mul_le_mul_of_nonneg_left hy.le hn'.le
    have h := (tendsto_natFloor_right ((n : ℝ) * x)).comp hx
    have h' := (tendsto_pure_nhds (fun k : ℕ => partialSum ω k / b) _).comp h
    exact h'
  · intro x
    have hx : Tendsto (fun y : ℝ => (n : ℝ) * y) (𝓝[<] x)
        (𝓝[<] ((n : ℝ) * x)) := by
      apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      · exact (continuous_const.mul continuous_id).continuousAt.continuousWithinAt
      · filter_upwards [self_mem_nhdsWithin] with y hy
        change (n : ℝ) * y < (n : ℝ) * x
        exact mul_lt_mul_of_pos_left hy hn'
    have hf := (tendsto_floor_left_pure_ceil_sub_one ((n : ℝ) * x)).comp hx
    have hf' := (tendsto_pure_pure (fun z : ℤ =>
      partialSum ω z.toNat / b) _).comp hf
    exact ⟨partialSum ω (⌈(n : ℝ) * x⌉ - 1).toNat / b,
      hf'.mono_right (pure_le_nhds _)⟩

/-- The floor-step path on a compact interval is càdlàg. -/
theorem isCadlag_stepPath {T : ℝ} (n : ℕ) (b : ℝ) (ω : ℕ → ℝ) :
    IsCadlag (fun t : Set.Icc (0 : ℝ) T =>
      partialSum ω ⌊(n : ℝ) * (t : ℝ)⌋₊ / b) := by
  by_cases hn : n = 0
  · subst n
    simp only [Nat.cast_zero, zero_mul, Nat.floor_zero]
    exact (IsCadlag.const :
      IsCadlag (fun _ : Set.Icc (0 : ℝ) T => partialSum ω 0 / b))
  · have hpos : 0 < n := Nat.pos_of_ne_zero hn
    constructor
    · intro x
      have h := (isCadlag_realStep n b ω hpos).isRightContinuous (x : ℝ)
      have hc : Tendsto (fun y : Set.Icc (0 : ℝ) T => (y : ℝ))
          (𝓝[>] x) (𝓝[>] (x : ℝ)) := by
        apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
        · exact continuous_subtype_val.continuousAt.continuousWithinAt
        · filter_upwards [self_mem_nhdsWithin] with y hy
          exact hy
      exact Filter.Tendsto.comp h hc
    · intro x
      obtain ⟨l, hl⟩ := (isCadlag_realStep n b ω hpos).tendsto_nhdsLT (x : ℝ)
      refine ⟨l, hl.comp ?_⟩
      apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      · exact continuous_subtype_val.continuousAt.continuousWithinAt
      · filter_upwards [self_mem_nhdsWithin] with y hy
        exact hy

end BGW.Skorokhod
