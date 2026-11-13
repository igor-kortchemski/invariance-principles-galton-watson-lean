/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import Mathlib.Topology.UnitInterval
public import Mathlib.Topology.ContinuousMap.Basic
public import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.Linarith

/-!
# The pseudodistance coded by a continuous function

For a continuous real function `g` on the unit interval, `intervalMin g s t` is its minimum
between `s` and `t`, and `codingDist g s t = g s + g t - 2 * intervalMin g s t`. We prove
attainment of the minimum, its order properties, the pseudometric identities, and continuity
in the two time variables. No sign or endpoint condition is needed for these results.

These are the deterministic distance formulas of milestone C1. The metric quotient and its
compactness are separate from the further proofs that it is a real tree and carries the
excursion's root and mass measure.
-/

@[expose] public section

open Set

namespace BGW.ContinuumTrees.Coding

/-- The minimum of the coding function on the unordered closed interval between two times. -/
noncomputable def intervalMin (g : C(unitInterval, ℝ)) (s t : unitInterval) : ℝ :=
  sInf (g '' Set.uIcc s t)

/-- The infimum in `intervalMin` is attained on its nonempty compact interval. -/
theorem exists_intervalMin (g : C(unitInterval, ℝ)) (s t : unitInterval) :
    ∃ r ∈ Set.uIcc s t, intervalMin g s t = g r :=
  isCompact_uIcc.exists_sInf_image_eq Set.nonempty_uIcc g.continuous.continuousOn

theorem intervalMin_le (g : C(unitInterval, ℝ)) (s t : unitInterval)
    {r : unitInterval} (hr : r ∈ Set.uIcc s t) : intervalMin g s t ≤ g r :=
  csInf_le (isCompact_uIcc.image g.continuous).bddBelow (Set.mem_image_of_mem g hr)

/-- Any lower bound on the coding function along the interval bounds its minimum. -/
theorem le_intervalMin (g : C(unitInterval, ℝ)) (s t : unitInterval) {a : ℝ}
    (ha : ∀ r ∈ Set.uIcc s t, a ≤ g r) : a ≤ intervalMin g s t := by
  obtain ⟨r, hr, heq⟩ := exists_intervalMin g s t
  rw [heq]
  exact ha r hr

@[simp] theorem intervalMin_self (g : C(unitInterval, ℝ)) (s : unitInterval) :
    intervalMin g s s = g s := by simp [intervalMin]

theorem intervalMin_comm (g : C(unitInterval, ℝ)) (s t : unitInterval) :
    intervalMin g s t = intervalMin g t s := by
  simp only [intervalMin, Set.uIcc_comm]

theorem intervalMin_le_left (g : C(unitInterval, ℝ)) (s t : unitInterval) :
    intervalMin g s t ≤ g s := intervalMin_le g s t Set.left_mem_uIcc

theorem intervalMin_le_right (g : C(unitInterval, ℝ)) (s t : unitInterval) :
    intervalMin g s t ≤ g t := intervalMin_le g s t Set.right_mem_uIcc

/-- Splitting at an arbitrary third time gives the lower bound needed for the triangle inequality. -/
theorem min_intervalMin_le (g : C(unitInterval, ℝ)) (s t u : unitInterval) :
    min (intervalMin g s t) (intervalMin g t u) ≤ intervalMin g s u := by
  apply le_intervalMin
  intro r hr
  have hmem : r ∈ Set.uIcc s t ∪ Set.uIcc t u := Set.uIcc_subset_uIcc_union_uIcc hr
  rcases hmem with h | h
  · exact (min_le_left _ _).trans (intervalMin_le g s t h)
  · exact (min_le_right _ _).trans (intervalMin_le g t u h)

/-- The real-valued pseudodistance coded by `g`. -/
noncomputable def codingDist (g : C(unitInterval, ℝ)) (s t : unitInterval) : ℝ :=
  g s + g t - 2 * intervalMin g s t

theorem codingDist_nonneg (g : C(unitInterval, ℝ)) (s t : unitInterval) :
    0 ≤ codingDist g s t := by
  have hl := intervalMin_le_left g s t
  have hr := intervalMin_le_right g s t
  dsimp [codingDist]
  linarith

@[simp] theorem codingDist_self (g : C(unitInterval, ℝ)) (s : unitInterval) :
    codingDist g s s = 0 := by simp [codingDist, two_mul]

theorem codingDist_comm (g : C(unitInterval, ℝ)) (s t : unitInterval) :
    codingDist g s t = codingDist g t s := by
  simp only [codingDist, intervalMin_comm, add_comm]

theorem codingDist_triangle (g : C(unitInterval, ℝ)) (s t u : unitInterval) :
    codingDist g s u ≤ codingDist g s t + codingDist g t u := by
  have hm := min_intervalMin_le g s t u
  have hl := intervalMin_le_right g s t
  have hr := intervalMin_le_left g t u
  rcases le_total (intervalMin g s t) (intervalMin g t u) with h | h
  · rw [min_eq_left h] at hm
    dsimp [codingDist]
    linarith
  · rw [min_eq_right h] at hm
    dsimp [codingDist]
    linarith

private def clampInterval (s t r : unitInterval) : unitInterval :=
  max (min s t) (min (max s t) r)

private theorem range_clampInterval (s t : unitInterval) :
    Set.range (clampInterval s t) = Set.uIcc s t := by
  ext r
  constructor
  · rintro ⟨v, rfl⟩
    exact ⟨le_max_left _ _, max_le min_le_max (min_le_left _ _)⟩
  · intro hr
    refine ⟨r, ?_⟩
    change max (min s t) (min (max s t) r) = r
    rw [min_eq_right hr.2, max_eq_right hr.1]

private theorem continuous_clampInterval :
    Continuous (fun p : (unitInterval × unitInterval) × unitInterval =>
      clampInterval p.1.1 p.1.2 p.2) :=
  (continuous_fst.fst.min continuous_fst.snd).max
    ((continuous_fst.fst.max continuous_fst.snd).min continuous_snd)

/-- The interval minimum is continuous as both endpoints vary. -/
theorem continuous_intervalMin (g : C(unitInterval, ℝ)) :
    Continuous (fun p : unitInterval × unitInterval => intervalMin g p.1 p.2) := by
  have hcont : Continuous (fun p : (unitInterval × unitInterval) × unitInterval =>
      g (clampInterval p.1.1 p.1.2 p.2)) := g.continuous.comp continuous_clampInterval
  have hmin : Continuous (fun p : unitInterval × unitInterval =>
      sInf ((fun r => g (clampInterval p.1 p.2 r)) '' (Set.univ : Set unitInterval))) :=
    (isCompact_univ : IsCompact (Set.univ : Set unitInterval)).continuous_sInf hcont
  have himage (s t : unitInterval) :
      (fun r => g (clampInterval s t r)) '' (Set.univ : Set unitInterval) =
        g '' Set.uIcc s t := by
    rw [Set.image_univ]
    change Set.range (g ∘ clampInterval s t) = _
    rw [Set.range_comp, range_clampInterval]
  change Continuous (fun p : unitInterval × unitInterval => sInf (g '' Set.uIcc p.1 p.2))
  simpa only [himage] using hmin

/-- The coding pseudodistance is continuous in the original topology of the time interval. -/
theorem continuous_codingDist (g : C(unitInterval, ℝ)) :
    Continuous (fun p : unitInterval × unitInterval => codingDist g p.1 p.2) :=
  ((g.continuous.comp continuous_fst).add (g.continuous.comp continuous_snd)).sub
    (continuous_const.mul (continuous_intervalMin g))

end BGW.ContinuumTrees.Coding
