/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.ExactContourMirror
public import BGW.ContinuumTrees.ContourAdapters
import Mathlib.Data.List.GetD

/-!
# Polygonal contours and the library clock

The unnormalized polygonal contour agrees with the library's hat-function interpolation
when time is multiplied by the number of contour steps.
-/

@[expose] public section

namespace BGW.PlaneTree

/-- The first contour value is zero. -/
theorem contourAt_zero (t : PlaneTree) : t.contourAt 0 = 0 := by
  cases t with
  | node ts => simp [contourAt]

/-- The contour value at its final listed time is zero. -/
theorem contourAt_end (t : PlaneTree) : t.contourAt (2 * (t.size - 1)) = 0 := by
  have hh := contourAt_mirror t (m := 0) (Nat.zero_le _)
  simpa only [Nat.sub_zero, contourAt_zero] using hh.symm

/-- The polygonal contour vanishes at and after the final listed time. -/
theorem contourLin_of_end_le (t : PlaneTree) {s : ℝ}
    (hs : (2 * (t.size - 1) : ℕ) ≤ s) : t.contourLin s = 0 := by
  have hfl : 2 * (t.size - 1) ≤ ⌊s⌋₊ := Nat.le_floor hs
  have hz : t.contourAt ⌊s⌋₊ = 0 := by
    rcases hfl.eq_or_lt with he | he
    · rw [← he, contourAt_end]
    · exact contourAt_of_lt t he
  rw [contourLin, hz, contourAt_of_lt t (by omega)]
  simp

/-- The library contour is the same interpolation at duration times the unit parameter. -/
theorem contourFunction_eq_contourLin (t : PlaneTree) (s : unitInterval) :
    t.contourFunction s = t.contourLin ((2 * (t.size - 1) : ℕ) * (s : ℝ)) := by
  let N := 2 * (t.size - 1)
  have hlen : t.contour.length = N + 1 := t.length_contour
  have hN : ((t.contour.length - 1 : ℕ) : ℝ) = (N : ℝ) := by rw [hlen]; simp
  let x : ℝ := N * (s : ℝ)
  have hx0 : 0 ≤ x := mul_nonneg (Nat.cast_nonneg _) s.property.1
  have hxN : x ≤ N := by
    dsimp [x]
    exact mul_le_of_le_one_right (Nat.cast_nonneg _) s.property.2
  by_cases he : x = N
  · have hh : t.contourFunction s = 0 := by
      by_cases hNz : N = 0
      · have hsize : t.size = 1 := by dsimp [N] at hNz; have := size_pos t; omega
        have hcont : t.contour = [0] := by
          have hp := head?_contour t
          have hl : t.contour.length = 1 := by simpa [hNz] using hlen
          cases hc : t.contour with
          | nil => simp [hc] at hl
          | cons a as =>
            have ha : a = 0 := by simpa [hc] using hp
            have ht : as = [] := List.length_eq_zero_iff.mp (by simpa [hc] using hl)
            simp [ha, ht]
        simp [contourFunction, hcont]
      · have hs1 : (s : ℝ) = 1 := by
          have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hNz
          apply (mul_left_cancel₀ hNr)
          simpa [x] using he
        have hse : s = 1 := Subtype.ext hs1
        rw [hse, contourFunction_one]
    rw [hh]
    exact (contourLin_of_end_le t (by change (N : ℝ) ≤ x; exact he.ge)).symm
  · have hlt : x < N := lt_of_le_of_ne hxN he
    let k := ⌊x⌋₊
    have hk : k < N := (Nat.floor_lt hx0).mpr hlt
    have hk0 : (k : ℝ) ≤ x := Nat.floor_le hx0
    have hk1 : x ≤ (k : ℝ) + 1 := (Nat.lt_floor_add_one x).le
    rw [contourFunction_on_segment t k s (by omega)
      (by rw [hN]; exact hk0) (by rw [hN]; exact hk1)]
    rw [contourLin_cell t k ⟨hk0, hk1⟩, hN]
    simp only [contourAt, List.getD_eq_getElem _ _ (show k < t.contour.length by omega),
      List.getD_eq_getElem _ _ (show k + 1 < t.contour.length by omega)]
    rfl

/-- Consecutive totalized contour values differ by at most one. -/
theorem abs_contourAt_succ_sub_le (t : PlaneTree) (m : ℕ) :
    |(t.contourAt (m + 1) : ℝ) - t.contourAt m| ≤ 1 := by
  by_cases hm : m + 1 < t.contour.length
  · have hh := (List.isChain_iff_getElem.mp (isChain_contour t)) m hm
    simp only [contourAt, List.getD_eq_getElem _ _ hm,
      List.getD_eq_getElem _ _ (show m < t.contour.length by omega)]
    rcases hh with hh | hh
    · have hr : (t.contour[m] : ℝ) + 1 = t.contour[m + 1] := by exact_mod_cast hh
      rw [show (t.contour[m + 1] : ℝ) - t.contour[m] = 1 by linarith]
      norm_num
    · have hr : (t.contour[m + 1] : ℝ) + 1 = t.contour[m] := by exact_mod_cast hh
      rw [show (t.contour[m + 1] : ℝ) - t.contour[m] = -1 by linarith]
      norm_num
  · have hlen := length_contour t
    have hm' : 2 * (t.size - 1) ≤ m := by omega
    have hz : t.contourAt m = 0 := by
      rcases hm'.eq_or_lt with he | he
      · rw [← he, contourAt_end]
      · exact contourAt_of_lt t he
    rw [hz, contourAt_of_lt t (by omega)]
    norm_num

private theorem abs_contourAt_add_sub_le (t : PlaneTree) (m d : ℕ) :
    |(t.contourAt (m + d) : ℝ) - t.contourAt m| ≤ d := by
  induction d with
  | zero => simp
  | succ d ih =>
    have hh := abs_sub_le (t.contourAt (m + d + 1) : ℝ) (t.contourAt (m + d))
      (t.contourAt m)
    have hs := abs_contourAt_succ_sub_le t (m + d)
    push_cast
    simpa only [Nat.add_assoc, add_comm] using hh.trans (add_le_add hs ih)

private theorem abs_contourLin_cell_sub_le (t : PlaneTree) (k : ℕ) {x y : ℝ}
    (hx : x ∈ Set.Icc (k : ℝ) (k + 1)) (hy : y ∈ Set.Icc (k : ℝ) (k + 1)) :
    |t.contourLin x - t.contourLin y| ≤ |x - y| := by
  rw [contourLin_cell t k hx, contourLin_cell t k hy]
  have he : (1 - (x - k)) * (t.contourAt k : ℝ) +
      (x - k) * t.contourAt (k + 1) -
      ((1 - (y - k)) * t.contourAt k + (y - k) * t.contourAt (k + 1)) =
      (x - y) * ((t.contourAt (k + 1) : ℝ) - t.contourAt k) := by ring
  rw [he, abs_mul]
  simpa only [mul_one] using
    mul_le_mul_of_nonneg_left (abs_contourAt_succ_sub_le t k) (abs_nonneg (x - y))

/-- The polygonal contour, continued by zero, has speed at most one at nonnegative times. -/
theorem abs_contourLin_sub_le (t : PlaneTree) {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    |t.contourLin x - t.contourLin y| ≤ |x - y| := by
  wlog hxy : x ≤ y generalizing x y
  · simpa only [abs_sub_comm] using this hy hx (le_of_not_ge hxy)
  let k := ⌊x⌋₊
  let l := ⌊y⌋₊
  have hk : (k : ℝ) ≤ x := Nat.floor_le hx
  have hk' : x ≤ (k : ℝ) + 1 := (Nat.lt_floor_add_one x).le
  have hl : (l : ℝ) ≤ y := Nat.floor_le hy
  have hl' : y ≤ (l : ℝ) + 1 := (Nat.lt_floor_add_one y).le
  have hkl : k ≤ l := Nat.floor_mono hxy
  by_cases he : k = l
  · apply abs_contourLin_cell_sub_le t k ⟨hk, hk'⟩
    simpa only [he, Set.mem_Icc] using And.intro hl hl'
  · have hkl' : k + 1 ≤ l := by omega
    have hklR : (k : ℝ) + 1 ≤ l := by exact_mod_cast hkl'
    have ha := abs_contourLin_cell_sub_le t k ⟨hk, hk'⟩
      (show (k : ℝ) + 1 ∈ Set.Icc (k : ℝ) (k + 1) by constructor <;> linarith)
    have hb := abs_contourLin_cell_sub_le t l
      (show (l : ℝ) ∈ Set.Icc (l : ℝ) (l + 1) by constructor <;> linarith) ⟨hl, hl'⟩
    rw [show (k : ℝ) + 1 = ((k + 1 : ℕ) : ℝ) by push_cast; rfl,
      contourLin_natCast] at ha
    rw [contourLin_natCast] at hb
    have hc := abs_contourAt_add_sub_le t (k + 1) (l - (k + 1))
    rw [Nat.add_sub_of_le hkl', Nat.cast_sub hkl', Nat.cast_add_one] at hc
    rw [abs_sub_comm] at hc
    have hh := (abs_sub_le (t.contourLin x) (t.contourAt (k + 1)) (t.contourLin y)).trans
      (add_le_add_right (abs_sub_le (t.contourAt (k + 1) : ℝ) (t.contourAt l)
        (t.contourLin y)) _)
    rw [abs_of_nonpos (by exact_mod_cast sub_nonpos.mpr hk' :
      x - ((k + 1 : ℕ) : ℝ) ≤ 0)] at ha
    rw [abs_of_nonpos (by linarith : (l : ℝ) - y ≤ 0)] at hb
    rw [abs_of_nonpos (by linarith : x - y ≤ 0)]
    push_cast at ha
    linarith

/-- The paper-clock contour evaluates the original polygonal contour at `2 * size * s`. -/
theorem paperContourFunction_eq_contourLin (t : PlaneTree) (s : unitInterval) :
    t.paperContourFunction s = t.contourLin (2 * (t.size : ℝ) * (s : ℝ)) := by
  let z : ℝ := t.size
  let m : ℝ := ((t.size - 1 : ℕ) : ℝ)
  have hz : 0 < z := by dsimp [z]; exact_mod_cast size_pos t
  have hmz : m = z - 1 := by
    dsimp [m, z]
    rw [Nat.cast_sub (by have := size_pos t; omega)]
    norm_num
  have hd : ((2 * (t.size - 1) : ℕ) : ℝ) = 2 * m := by
    simp [m]
  have hs0 : 0 ≤ (s : ℝ) := s.property.1
  by_cases hs : m / z ≤ (s : ℝ)
  · rw [paperContourFunction_eq_zero t s hs]
    exact (contourLin_of_end_le t (by
      rw [hd]
      have hh := (div_le_iff₀ hz).mp hs
      dsimp [z] at hh
      nlinarith)).symm
  · have hm : 0 < m := by
      have hh := (lt_div_iff₀ hz).mp (lt_of_not_ge hs)
      nlinarith
    have hq0 : 0 ≤ (s : ℝ) * (z / m) := by positivity
    have hq1 : (s : ℝ) * (z / m) ≤ 1 := by
      have hh := (le_div_iff₀ hz).mp (le_of_lt (lt_of_not_ge hs))
      rw [← mul_div_assoc, div_le_one hm]
      exact hh
    have hq : (t.paperTimeChange s : ℝ) = (s : ℝ) * (z / m) := by
      change max 0 (min 1 ((s : ℝ) * (z / m))) = _
      rw [min_eq_right hq1, max_eq_right hq0]
    rw [paperContourFunction, ContinuousMap.comp_apply, contourFunction_eq_contourLin, hd, hq]
    congr 1
    change 2 * m * ((s : ℝ) * (z / m)) = 2 * z * (s : ℝ)
    field_simp

end BGW.PlaneTree
