/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.Tree.Contour
public import Mathlib.Topology.UnitInterval
public import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-!
# Continuous interpolation of the discrete contour

The time interval is normalized by the actual traversal duration, twice the
number of edges. The usual affine interpolation is expressed by the finite
sum of triangular hat functions. This also defines the singleton contour as
the constant zero function, with no division by zero.
-/

@[expose] public section

namespace BGW.PlaneTree

private theorem contour_length_pos (t : PlaneTree) : 0 < t.contour.length :=
  List.length_pos_iff.mpr (contour_ne_nil t)

/-- The time of discrete contour visit `i`, divided by the traversal duration.
The denominator is one for the singleton tree, whose only index is zero. -/
noncomputable def contourTime (t : PlaneTree) (i : Fin t.contour.length) : unitInterval :=
  ⟨(i : ℝ) / (max (t.contour.length - 1) 1 : ℕ), by
    have hden : (0 : ℝ) < (max (t.contour.length - 1) 1 : ℕ) := by
      exact_mod_cast (show 0 < max (t.contour.length - 1) 1 from
        lt_of_lt_of_le Nat.zero_lt_one (le_max_right _ _))
    constructor
    · exact div_nonneg (Nat.cast_nonneg _) hden.le
    · apply (div_le_one₀ hden).mpr
      have hi : i.val ≤ t.contour.length - 1 := by omega
      exact_mod_cast hi.trans (le_max_left _ _)⟩

/-- The polygonal contour as a continuous function on the unit interval. -/
noncomputable def contourFunction (t : PlaneTree) : C(unitInterval, ℝ) where
  toFun s := ∑ i : Fin t.contour.length, (t.contour[i.val] : ℝ) *
    max 0 (1 - |((t.contour.length - 1 : ℕ) : ℝ) * (s : ℝ) - (i : ℝ)|)
  continuous_toFun := by fun_prop

theorem contourFunction_nonneg (t : PlaneTree) (s : unitInterval) :
    0 ≤ t.contourFunction s := by
  change 0 ≤ ∑ i : Fin t.contour.length, (t.contour[i.val] : ℝ) *
    max 0 (1 - |((t.contour.length - 1 : ℕ) : ℝ) * (s : ℝ) - (i : ℝ)|)
  apply Finset.sum_nonneg
  intro i _
  exact mul_nonneg (Nat.cast_nonneg _) (le_max_left _ _)

/-- Multiplying a visit time by the traversal duration recovers its discrete index. -/
theorem duration_mul_contourTime (t : PlaneTree) (i : Fin t.contour.length) :
    ((t.contour.length - 1 : ℕ) : ℝ) * (t.contourTime i : ℝ) = (i : ℝ) := by
  have hi : i.val ≤ t.contour.length - 1 := by omega
  by_cases hN : t.contour.length - 1 = 0
  · have hi0 : i.val = 0 := by omega
    simp [contourTime, hi0]
  · have hNpos : 1 ≤ t.contour.length - 1 := by omega
    have hNr : ((t.contour.length - 1 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hN
    change ((t.contour.length - 1 : ℕ) : ℝ) *
      ((i : ℝ) / (max (t.contour.length - 1) 1 : ℕ)) = _
    rw [max_eq_left hNpos]
    exact mul_div_cancel₀ _ hNr

private theorem hat_at_integer (i j : ℕ) :
    max (0 : ℝ) (1 - |(i : ℝ) - j|) = if j = i then 1 else 0 := by
  by_cases hji : j = i
  · subst j
    simp
  · rw [ite_eq_right hji]
    apply max_eq_left
    have hgap : (1 : ℝ) ≤ |(i : ℝ) - j| := by
      rcases lt_or_gt_of_ne (Ne.symm hji) with hij | hji'
      · have h : (i : ℝ) + 1 ≤ j := by exact_mod_cast Nat.succ_le_of_lt hij
        rw [abs_of_nonpos (by linarith)]
        linarith
      · have h : (j : ℝ) + 1 ≤ i := by exact_mod_cast Nat.succ_le_of_lt hji'
        rw [abs_of_nonneg (by linarith)]
        linarith
    linarith

/-- The continuous contour takes exactly the discrete height at every visit time. -/
@[simp] theorem contourFunction_contourTime (t : PlaneTree) (i : Fin t.contour.length) :
    t.contourFunction (t.contourTime i) = (t.contour[i.val] : ℝ) := by
  change (∑ j : Fin t.contour.length, (t.contour[j.val] : ℝ) *
    max 0 (1 - |((t.contour.length - 1 : ℕ) : ℝ) * (t.contourTime i : ℝ) - (j : ℝ)|)) = _
  simp_rw [duration_mul_contourTime, hat_at_integer]
  have heq (j : Fin t.contour.length) : (j.val = i.val) ↔ j = i := Fin.val_inj
  simp only [heq]
  simp

private theorem hat_on_segment (x : ℝ) (i j : ℕ) (hlo : (i : ℝ) ≤ x)
    (hhi : x ≤ (i : ℝ) + 1) :
    max 0 (1 - |x - j|) =
      if j = i then 1 - (x - i) else if j = i + 1 then x - i else 0 := by
  by_cases hji : j = i
  · subst j
    rw [ite_eq_left rfl, abs_of_nonneg (sub_nonneg.mpr hlo)]
    exact max_eq_right (by linarith)
  · rw [ite_eq_right hji]
    by_cases hjnext : j = i + 1
    · subst j
      rw [ite_eq_left rfl]
      have heq : 1 - |x - ((i + 1 : ℕ) : ℝ)| = x - i := by
        simp only [Nat.cast_add, Nat.cast_one]
        rw [abs_of_nonpos (by linarith)]
        ring
      rw [heq]
      exact max_eq_right (sub_nonneg.mpr hlo)
    · rw [ite_eq_right hjnext]
      apply max_eq_left
      have hgap : (1 : ℝ) ≤ |x - j| := by
        rcases lt_or_gt_of_ne hji with hjlt | hjgt
        · have hjiR : (j : ℝ) + 1 ≤ i := by exact_mod_cast Nat.succ_le_of_lt hjlt
          rw [abs_of_nonneg (by linarith)]
          linarith
        · have hnext : i + 2 ≤ j := by omega
          have hjiR : (i : ℝ) + 2 ≤ j := by exact_mod_cast hnext
          rw [abs_of_nonpos (by linarith)]
          linarith
      linarith

/-- Between consecutive discrete visit times, the contour is their affine interpolation. -/
theorem contourFunction_on_segment (t : PlaneTree) (i : ℕ) (s : unitInterval)
    (hi : i + 1 < t.contour.length)
    (hlo : (i : ℝ) ≤ ((t.contour.length - 1 : ℕ) : ℝ) * (s : ℝ))
    (hhi : ((t.contour.length - 1 : ℕ) : ℝ) * (s : ℝ) ≤ (i : ℝ) + 1) :
    let θ := ((t.contour.length - 1 : ℕ) : ℝ) * (s : ℝ) - i
    t.contourFunction s =
      (1 - θ) * (t.contour[i]'(by omega) : ℝ) +
        θ * (t.contour[i + 1]'hi : ℝ) := by
  classical
  let a : Fin t.contour.length := ⟨i, by omega⟩
  let b : Fin t.contour.length := ⟨i + 1, hi⟩
  have hab : a ≠ b := by
    intro h
    have := congrArg Fin.val h
    dsimp [a, b] at this
    omega
  have hca (j : Fin t.contour.length) : j.val = i ↔ j = a :=
    ⟨fun h => Fin.ext h, fun h => congrArg Fin.val h⟩
  have hcb (j : Fin t.contour.length) : j.val = i + 1 ↔ j = b :=
    ⟨fun h => Fin.ext h, fun h => congrArg Fin.val h⟩
  let x : ℝ := ((t.contour.length - 1 : ℕ) : ℝ) * (s : ℝ)
  change (∑ j : Fin t.contour.length,
    (t.contour[j.val] : ℝ) * max 0 (1 - |x - (j : ℝ)|)) = _
  simp_rw [hat_on_segment x i _ hlo hhi, hca, hcb]
  have hterm (j : Fin t.contour.length) :
      (t.contour[j.val] : ℝ) *
        (if j = a then 1 - (x - i) else if j = b then x - i else 0) =
      (if j = a then (t.contour[a.val] : ℝ) * (1 - (x - i)) else 0) +
        (if j = b then (t.contour[b.val] : ℝ) * (x - i) else 0) := by
    by_cases hja : j = a
    · subst j
      simp [hab]
    · by_cases hjb : j = b
      · subst j
        simp [hja]
      · simp [hja, hjb]
  simp_rw [hterm]
  rw [Finset.sum_add_distrib]
  simp [a, b, x, mul_comm]

@[simp] theorem contourFunction_zero (t : PlaneTree) : t.contourFunction 0 = 0 := by
  let i : Fin t.contour.length := ⟨0, contour_length_pos t⟩
  have ht : t.contourTime i = 0 := by ext; simp [contourTime, i]
  have h := t.contourFunction_contourTime i
  rw [ht] at h
  have hz : t.contour[0]'(contour_length_pos t) = 0 := by
    have hh := head?_contour t
    rw [List.head?_eq_getElem?, List.getElem?_eq_getElem (contour_length_pos t)] at hh
    exact Option.some.inj hh
  simpa only [i, hz, Nat.cast_zero] using h

@[simp] theorem contourFunction_one (t : PlaneTree) : t.contourFunction 1 = 0 := by
  by_cases hN : t.contour.length - 1 = 0
  · have heq : t.contourFunction 1 = t.contourFunction 0 := by
      change (∑ i : Fin t.contour.length, _) = ∑ i : Fin t.contour.length, _
      simp only [hN, Nat.cast_zero, zero_mul]
    exact heq.trans (contourFunction_zero t)
  · let i : Fin t.contour.length := ⟨t.contour.length - 1, by omega⟩
    have ht : t.contourTime i = 1 := by
      ext
      have hNpos : 1 ≤ t.contour.length - 1 := by omega
      change ((t.contour.length - 1 : ℕ) : ℝ) /
        (max (t.contour.length - 1) 1 : ℕ) = 1
      rw [max_eq_left hNpos]
      exact div_self (by exact_mod_cast hN)
    have h := t.contourFunction_contourTime i
    rw [ht] at h
    have hz : t.contour[t.contour.length - 1]'(by omega) = 0 := by
      have hh := getLast?_contour t
      rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at hh
      exact Option.some.inj hh
    simpa only [i, hz, Nat.cast_zero] using h

end BGW.PlaneTree
