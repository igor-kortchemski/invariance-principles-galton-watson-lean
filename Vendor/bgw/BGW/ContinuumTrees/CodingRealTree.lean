/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.ContinuumTrees.CodingQuotient
public import BGW.ContinuumTrees.RealTree
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.UniformSpace.Cauchy
import Mathlib.Tactic.Linarith

/-!
# A continuous coding function produces a real tree

The interval minima satisfy the four-point inequality. Midpoints are constructed by applying
the intermediate value theorem to a running interval minimum, and then choosing a point where
that minimum is attained. Compactness supplies completeness, so the real-tree criterion applies.
All three properties are proved for every continuous real coding function; no four-point or
midpoint assumption, nonnegativity condition, or endpoint normalization is imposed.
-/

@[expose] public section

open Set

namespace BGW.ContinuumTrees.Coding

private theorem pair_min_le_of_le {A B C D E F : ℝ} (hab : A ≤ B)
    (h₁ : min C F ≤ A) (h₂ : min E D ≤ A)
    (h₃ : min C E ≤ B) (h₄ : min F D ≤ B) :
    min (C + D) (E + F) ≤ A + B := by
  rcases min_le_iff.mp h₁ with hc | hf
  · by_cases hd : D ≤ B
    · apply (min_le_left _ _).trans
      linarith
    · have he : E ≤ A := (min_le_iff.mp h₂).resolve_right (by linarith)
      have hf : F ≤ B := (min_le_iff.mp h₄).resolve_right hd
      apply (min_le_right _ _).trans
      linarith
  · by_cases he : E ≤ B
    · apply (min_le_right _ _).trans
      linarith
    · have hd : D ≤ A := (min_le_iff.mp h₂).resolve_left (by linarith)
      have hc : C ≤ B := (min_le_iff.mp h₃).resolve_right he
      apply (min_le_left _ _).trans
      linarith

private theorem pair_min_le {A B C D E F : ℝ}
    (h₁ : min C F ≤ A) (h₂ : min E D ≤ A)
    (h₃ : min C E ≤ B) (h₄ : min F D ≤ B) :
    min (C + D) (E + F) ≤ A + B := by
  rcases le_total A B with h | h
  · exact pair_min_le_of_le h h₁ h₂ h₃ h₄
  · have hh := pair_min_le_of_le (A := B) (B := A) (C := C) (D := D)
      (E := F) (F := E) h h₃ h₄ h₁ h₂
    simpa only [add_comm] using hh

private theorem codingDist_fourPoint (g : C(unitInterval, ℝ)) (s t u v : unitInterval) :
    codingDist g s t + codingDist g u v ≤
      max (codingDist g s u + codingDist g t v) (codingDist g s v + codingDist g t u) := by
  have h₁ : min (intervalMin g s u) (intervalMin g t u) ≤ intervalMin g s t := by
    simpa only [intervalMin_comm] using min_intervalMin_le g s u t
  have h₂ : min (intervalMin g s v) (intervalMin g t v) ≤ intervalMin g s t := by
    simpa only [intervalMin_comm] using min_intervalMin_le g s v t
  have h₃ : min (intervalMin g s u) (intervalMin g s v) ≤ intervalMin g u v := by
    simpa only [intervalMin_comm] using min_intervalMin_le g u s v
  have h₄ : min (intervalMin g t u) (intervalMin g t v) ≤ intervalMin g u v := by
    simpa only [intervalMin_comm] using min_intervalMin_le g u t v
  rcases min_le_iff.mp (pair_min_le h₁ h₂ h₃ h₄) with h | h
  · apply le_max_iff.mpr
    left
    dsimp [codingDist]
    linarith
  · apply le_max_iff.mpr
    right
    dsimp [codingDist]
    linarith

/-- The compact coding quotient satisfies the four-point condition. -/
theorem fourPoint (g : C(unitInterval, ℝ)) : RealTree.FourPoint (Space g) := by
  intro x y z w
  obtain ⟨s, rfl⟩ := projection_surjective g x
  obtain ⟨t, rfl⟩ := projection_surjective g y
  obtain ⟨u, rfl⟩ := projection_surjective g z
  obtain ⟨v, rfl⟩ := projection_surjective g w
  simpa only [dist_projection] using codingDist_fourPoint g s t u v

private theorem intervalMin_mono (g : C(unitInterval, ℝ)) {a b c d : unitInterval}
    (h : Set.uIcc a b ⊆ Set.uIcc c d) : intervalMin g c d ≤ intervalMin g a b := by
  apply le_intervalMin
  intro r hr
  exact intervalMin_le g c d (h hr)

private theorem mem_uIcc_right_of_nested {s t r v : unitInterval}
    (hr : r ∈ Set.uIcc s t) (hv : v ∈ Set.uIcc s r) : r ∈ Set.uIcc v t := by
  rcases le_total s t with hst | hts
  · have hr' : s ≤ r ∧ r ≤ t := by simpa only [Set.uIcc_of_le hst, Set.mem_Icc] using hr
    have hv' : s ≤ v ∧ v ≤ r := by simpa only [Set.uIcc_of_le hr'.1, Set.mem_Icc] using hv
    exact Set.mem_uIcc_of_le hv'.2 hr'.2
  · have hr' : t ≤ r ∧ r ≤ s := by simpa only [Set.uIcc_of_ge hts, Set.mem_Icc] using hr
    have hv' : r ≤ v ∧ v ≤ s := by simpa only [Set.uIcc_of_ge hr'.2, Set.mem_Icc] using hv
    exact Set.mem_uIcc_of_ge hr'.1 hv'.1

private theorem exists_codingMidpoint_of_le (g : C(unitInterval, ℝ)) (s t : unitInterval)
    (hst : g t ≤ g s) : ∃ v : unitInterval,
      codingDist g s v = codingDist g s t / 2 ∧ codingDist g v t = codingDist g s t / 2 := by
  let m := intervalMin g s t
  let h := g s - codingDist g s t / 2
  have hmh : m ≤ h := by
    dsimp [m, h, codingDist]
    linarith
  have hhs : h ≤ g s := by
    have hd := codingDist_nonneg g s t
    dsimp [h]
    linarith
  obtain ⟨r₀, hr₀, hmin⟩ := exists_intervalMin g s t
  have hsr₀ : intervalMin g s r₀ = m := by
    apply le_antisymm
    · exact (intervalMin_le_right g s r₀).trans_eq hmin.symm
    · exact intervalMin_mono g (Set.uIcc_subset_uIcc_left hr₀)
  have hf : Continuous (fun r : unitInterval => intervalMin g s r) :=
    (continuous_intervalMin g).comp (continuous_const.prodMk continuous_id)
  have hh : h ∈ Set.uIcc (intervalMin g s s) (intervalMin g s r₀) := by
    rw [intervalMin_self, hsr₀]
    exact Set.mem_uIcc_of_ge hmh hhs
  obtain ⟨r, hr, hrh⟩ :=
    (intermediate_value_uIcc (a := s) (b := r₀) hf.continuousOn) hh
  obtain ⟨v, hv, hvmin⟩ := exists_intervalMin g s r
  have hgv : g v = h := hvmin.symm.trans hrh
  have hvs : v ∈ Set.uIcc s r₀ := (Set.uIcc_subset_uIcc_left hr) hv
  have hvst : v ∈ Set.uIcc s t := (Set.uIcc_subset_uIcc_left hr₀) hvs
  have hminsv : intervalMin g s v = h := by
    apply le_antisymm
    · exact (intervalMin_le_right g s v).trans_eq hgv
    · rw [← hrh]
      exact intervalMin_mono g (Set.uIcc_subset_uIcc_left hv)
  have hr₀vt : r₀ ∈ Set.uIcc v t := mem_uIcc_right_of_nested hr₀ hvs
  have hminvt : intervalMin g v t = m := by
    apply le_antisymm
    · exact (intervalMin_le g v t hr₀vt).trans_eq hmin.symm
    · exact intervalMin_mono g (Set.uIcc_subset_uIcc_right hvst)
  refine ⟨v, ?_, ?_⟩
  · rw [codingDist, hgv, hminsv]
    dsimp [h, codingDist]
    linarith
  · rw [codingDist, hgv, hminvt]
    dsimp [m, h, codingDist]
    linarith

private theorem exists_codingMidpoint (g : C(unitInterval, ℝ)) (s t : unitInterval) :
    ∃ v : unitInterval,
      codingDist g s v = codingDist g s t / 2 ∧ codingDist g v t = codingDist g s t / 2 := by
  rcases le_total (g t) (g s) with h | h
  · exact exists_codingMidpoint_of_le g s t h
  · obtain ⟨v, h₁, h₂⟩ := exists_codingMidpoint_of_le g t s h
    exact ⟨v, by simpa only [codingDist_comm] using h₂,
      by simpa only [codingDist_comm] using h₁⟩

/-- Midpoints are realized by times obtained from a continuous running interval minimum. -/
theorem hasMidpoints (g : C(unitInterval, ℝ)) : RealTree.HasMidpoints (Space g) := by
  intro x y
  obtain ⟨s, rfl⟩ := projection_surjective g x
  obtain ⟨t, rfl⟩ := projection_surjective g y
  obtain ⟨v, h₁, h₂⟩ := exists_codingMidpoint g s t
  exact ⟨projection g v, by simpa only [dist_projection] using h₁,
    by simpa only [dist_projection] using h₂⟩

/-- Every continuous real coding function on the unit interval codes a compact real tree. -/
theorem isRealTree (g : C(unitInterval, ℝ)) : RealTree.IsRealTree (Space g) :=
  RealTree.isRealTree_of_fourPoint (fourPoint g) (hasMidpoints g)

end BGW.ContinuumTrees.Coding
