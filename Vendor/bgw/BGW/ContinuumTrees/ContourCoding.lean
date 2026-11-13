/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.Tree.ContourMetric
public import BGW.Tree.ContourInterpolation
public import BGW.ContinuumTrees.Coding
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The graph metric coded by the interpolated finite-tree contour

Between grid times, the polygonal contour is a convex combination of its two
endpoint heights. A discrete lower bound and an attaining grid point therefore
identify its continuous interval minimum. Applied between the first visits to
two vertices, this minimum is the depth of their lowest common ancestor, so the
continuous coding distance is their graph distance.

The first-visit grid indices are explicit `Fin` arguments. Equal indices include
the singleton tree; the upper endpoint of each interval is treated before taking
a natural floor, so every interpolation cell used has two valid endpoints.
-/

@[expose] public section

open BGW.PlaneTree

namespace BGW.ContinuumTrees.ContourCoding

private theorem monotone_contourTime (t : PlaneTree) : Monotone t.contourTime := by
  intro a b hab
  change (a : ℝ) / (max (t.contour.length - 1) 1 : ℕ) ≤
    (b : ℝ) / (max (t.contour.length - 1) 1 : ℕ)
  exact div_le_div_of_nonneg_right (by exact_mod_cast hab) (Nat.cast_nonneg _)

private theorem lower_bound_contourFunction_between (t : PlaneTree)
    (a b : Fin t.contour.length) (hab : a ≤ b) (d : ℕ)
    (hlower : ∀ k : Fin t.contour.length, a.val ≤ k.val → k.val ≤ b.val →
      d ≤ t.contour[k.val])
    (s : unitInterval) (hs : s ∈ Set.uIcc (t.contourTime a) (t.contourTime b)) :
    (d : ℝ) ≤ t.contourFunction s := by
  rcases eq_or_lt_of_le hab with rfl | hablt
  · have hs' : s = t.contourTime a := by simpa using hs
    subst s
    rw [contourFunction_contourTime]
    exact_mod_cast hlower a le_rfl le_rfl
  · have htimes : t.contourTime a ≤ t.contourTime b := monotone_contourTime t hab
    rw [Set.uIcc_of_le htimes] at hs
    by_cases hsb : s = t.contourTime b
    · subst s
      rw [contourFunction_contourTime]
      exact_mod_cast hlower b hab le_rfl
    · have hsblt : s < t.contourTime b := lt_of_le_of_ne hs.2 hsb
      have hN : 0 < t.contour.length - 1 := by
        have ha : a.val < b.val := hablt
        have hb := b.isLt
        omega
      have hNR : (0 : ℝ) < ((t.contour.length - 1 : ℕ) : ℝ) := by exact_mod_cast hN
      let x : ℝ := ((t.contour.length - 1 : ℕ) : ℝ) * (s : ℝ)
      have hax : (a.val : ℝ) ≤ x := by
        calc
          (a.val : ℝ) = ((t.contour.length - 1 : ℕ) : ℝ) *
              (t.contourTime a : ℝ) := (duration_mul_contourTime t a).symm
          _ ≤ x := mul_le_mul_of_nonneg_left hs.1 hNR.le
      have hxb : x < (b.val : ℝ) := by
        calc
          x < ((t.contour.length - 1 : ℕ) : ℝ) * (t.contourTime b : ℝ) :=
            mul_lt_mul_of_pos_left hsblt hNR
          _ = (b.val : ℝ) := duration_mul_contourTime t b
      have hx0 : 0 ≤ x := (Nat.cast_nonneg a.val).trans hax
      let k : ℕ := Nat.floor x
      have hak : a.val ≤ k := Nat.le_floor hax
      have hkb : k < b.val := (Nat.floor_lt hx0).mpr hxb
      have hk : k + 1 < t.contour.length := lt_of_le_of_lt (Nat.succ_le_of_lt hkb) b.isLt
      have hxlo : (k : ℝ) ≤ x := Nat.floor_le hx0
      have hxhi : x ≤ (k : ℝ) + 1 := (Nat.lt_floor_add_one x).le
      have hd0 : d ≤ t.contour[k]'(by omega) :=
        hlower ⟨k, by omega⟩ (by change a.val ≤ k; exact hak)
          (by change k ≤ b.val; exact hkb.le)
      have hd1 : d ≤ t.contour[k + 1]'hk :=
        hlower ⟨k + 1, hk⟩ (by change a.val ≤ k + 1; omega)
          (by change k + 1 ≤ b.val; omega)
      have hd0R : (d : ℝ) ≤ (t.contour[k]'(by omega) : ℝ) := by exact_mod_cast hd0
      have hd1R : (d : ℝ) ≤ (t.contour[k + 1]'hk : ℝ) := by exact_mod_cast hd1
      have hlinear := contourFunction_on_segment t k s hk hxlo hxhi
      calc
        (d : ℝ) = (1 - (x - k)) * d + (x - k) * d := by ring
        _ ≤ (1 - (x - k)) * (t.contour[k]'(by omega) : ℝ) +
            (x - k) * (t.contour[k + 1]'hk : ℝ) :=
          add_le_add (mul_le_mul_of_nonneg_left hd0R (by linarith))
            (mul_le_mul_of_nonneg_left hd1R (by linarith))
        _ = t.contourFunction s := hlinear.symm

private theorem intervalMin_contourTime_eq (t : PlaneTree)
    (a b : Fin t.contour.length) (d : ℕ)
    (hlower : ∀ k : Fin t.contour.length,
      min a.val b.val ≤ k.val → k.val ≤ max a.val b.val → d ≤ t.contour[k.val])
    (hattain : ∃ k : Fin t.contour.length, min a.val b.val ≤ k.val ∧
      k.val ≤ max a.val b.val ∧ t.contour[k.val] = d) :
    Coding.intervalMin t.contourFunction (t.contourTime a) (t.contourTime b) = (d : ℝ) := by
  apply le_antisymm
  · obtain ⟨k, hak, hkb, hkd⟩ := hattain
    have htime : t.contourTime k ∈ Set.uIcc (t.contourTime a) (t.contourTime b) := by
      rcases le_total a b with hab | hba
      · have habv : a.val ≤ b.val := hab
        apply Set.mem_uIcc_of_le
        · exact monotone_contourTime t (by
            change a.val ≤ k.val
            simpa only [min_eq_left habv] using hak)
        · exact monotone_contourTime t (by
            change k.val ≤ b.val
            simpa only [max_eq_right habv] using hkb)
      · have hbav : b.val ≤ a.val := hba
        apply Set.mem_uIcc_of_ge
        · exact monotone_contourTime t (by
            change b.val ≤ k.val
            simpa only [min_eq_right hbav] using hak)
        · exact monotone_contourTime t (by
            change k.val ≤ a.val
            simpa only [max_eq_left hbav] using hkb)
    calc
      Coding.intervalMin t.contourFunction (t.contourTime a) (t.contourTime b) ≤
          t.contourFunction (t.contourTime k) := Coding.intervalMin_le _ _ _ htime
      _ = (d : ℝ) := by rw [contourFunction_contourTime, hkd]
  · apply Coding.le_intervalMin
    intro s hs
    rcases le_total a b with hab | hba
    · have habv : a.val ≤ b.val := hab
      apply lower_bound_contourFunction_between t a b hab d ?_ s hs
      intro k hak hkb
      apply hlower k
      · simpa only [min_eq_left habv] using hak
      · simpa only [max_eq_right habv] using hkb
    · have hbav : b.val ≤ a.val := hba
      rw [Set.uIcc_comm] at hs
      apply lower_bound_contourFunction_between t b a hba d ?_ s hs
      intro k hbk hka
      apply hlower k
      · simpa only [min_eq_right hbav] using hbk
      · simpa only [max_eq_left hbav] using hka

private theorem contour_at_first_visit {t : PlaneTree} {i : ℕ} {u : List ℕ}
    (hi : t.vertices[i]? = some u) (a : Fin t.contour.length)
    (ha : a.val = 2 * i - u.length) : t.contour[a.val] = u.length := by
  have h := getElem?_contour_first_visit hi
  rw [← ha, List.getElem?_eq_getElem a.isLt] at h
  exact Option.some.inj h

private theorem contour_at_vertexContour {t : PlaneTree} (a : Fin t.contour.length)
    {u : List ℕ} (ha : t.vertexContour[a.val]? = some u) : t.contour[a.val] = u.length := by
  have h := congrArg (fun cs : List ℕ => cs[a.val]?) (map_length_vertexContour t)
  rw [List.getElem?_map, ha, List.getElem?_eq_getElem a.isLt] at h
  exact (Option.some.inj h).symm

/-- Arbitrary grid visits have continuous interval minimum equal to their LCA depth. -/
theorem intervalMin_contourTime_of_vertices {t : PlaneTree}
    (a b : Fin t.contour.length) {u v : List ℕ}
    (ha : t.vertexContour[a.val]? = some u) (hb : t.vertexContour[b.val]? = some v) :
    Coding.intervalMin t.contourFunction (t.contourTime a) (t.contourTime b) =
      ((lca u v).length : ℝ) := by
  apply intervalMin_contourTime_eq t a b (lca u v).length
  · intro k hlo hhi
    have hmap := congrArg (fun cs : List ℕ => cs[k.val]?) (map_length_vertexContour t)
    rw [List.getElem?_map, List.getElem?_eq_getElem k.isLt] at hmap
    obtain ⟨w, hkw, hlen⟩ := Option.map_eq_some_iff.mp hmap
    exact (lca_prefix_vertexContour_between_visits ha hb hlo hhi hkw).length_le.trans_eq hlen
  · obtain ⟨k, hlo, hhi, hkw⟩ := lca_visit_between_contour_visits ha hb
    have hcontour : t.contour[k]? = some (lca u v).length := by
      rw [← map_length_vertexContour, List.getElem?_map, hkw]
      rfl
    obtain ⟨hk, hval⟩ := List.getElem?_eq_some_iff.mp hcontour
    exact ⟨⟨k, hk⟩, hlo, hhi, hval⟩

/-- Coding distance at any pair of grid visits equals the distance of their addresses. -/
theorem codingDist_contourTime_of_vertices {t : PlaneTree}
    (a b : Fin t.contour.length) {u v : List ℕ}
    (ha : t.vertexContour[a.val]? = some u) (hb : t.vertexContour[b.val]? = some v) :
    Coding.codingDist t.contourFunction (t.contourTime a) (t.contourTime b) =
      (graphDist u v : ℝ) := by
  rw [Coding.codingDist, intervalMin_contourTime_of_vertices a b ha hb,
    contourFunction_contourTime, contourFunction_contourTime,
    contour_at_vertexContour a ha, contour_at_vertexContour b hb]
  have h := congrArg (fun n : ℕ => (n : ℝ)) (graphDist_add_two_lca u v)
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at h
  linarith

/-- The continuous contour minimum between first visits is the depth of the LCA. -/
theorem intervalMin_first_visits {t : PlaneTree} {i j : ℕ} {u v : List ℕ}
    (hi : t.vertices[i]? = some u) (hj : t.vertices[j]? = some v)
    (a b : Fin t.contour.length)
    (ha : a.val = 2 * i - u.length) (hb : b.val = 2 * j - v.length) :
    Coding.intervalMin t.contourFunction (t.contourTime a) (t.contourTime b) =
      ((lca u v).length : ℝ) := by
  apply intervalMin_contourTime_eq t a b (lca u v).length
  · intro k hlo hhi
    have hmap := congrArg (fun cs : List ℕ => cs[k.val]?) (map_length_vertexContour t)
    rw [List.getElem?_map, List.getElem?_eq_getElem k.isLt] at hmap
    obtain ⟨w, hkw, hlen⟩ := Option.map_eq_some_iff.mp hmap
    have hp := lca_prefix_vertexContour_between_first_visits hi hj
      (by simpa only [ha, hb] using hlo) (by simpa only [ha, hb] using hhi) hkw
    exact hp.length_le.trans_eq hlen
  · obtain ⟨k, hlo, hhi, hkw⟩ := lca_visit_between_first_visits hi hj
    have hcontour : t.contour[k]? = some (lca u v).length := by
      rw [← map_length_vertexContour, List.getElem?_map, hkw]
      rfl
    obtain ⟨hk, hval⟩ := List.getElem?_eq_some_iff.mp hcontour
    refine ⟨⟨k, hk⟩, ?_, ?_, hval⟩
    · simpa only [ha, hb] using hlo
    · simpa only [ha, hb] using hhi

/-- The distance coded by the interpolated contour agrees with the vertex graph metric. -/
theorem codingDist_first_visits {t : PlaneTree} {i j : ℕ} {u v : List ℕ}
    (hi : t.vertices[i]? = some u) (hj : t.vertices[j]? = some v)
    (a b : Fin t.contour.length)
    (ha : a.val = 2 * i - u.length) (hb : b.val = 2 * j - v.length) :
    Coding.codingDist t.contourFunction (t.contourTime a) (t.contourTime b) =
      (graphDist u v : ℝ) := by
  rw [Coding.codingDist, intervalMin_first_visits hi hj a b ha hb,
    contourFunction_contourTime, contourFunction_contourTime,
    contour_at_first_visit hi a ha, contour_at_first_visit hj b hb]
  have h := congrArg (fun n : ℕ => (n : ℝ)) (graphDist_add_two_lca u v)
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at h
  linarith

end BGW.ContinuumTrees.ContourCoding
