/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.Tree.ContourBracket
public import BGW.Tree.Weight

/-!
# Reflection of finite plane trees

Mirroring reverses the children at every vertex, preserving sizes and offspring weights.
-/

@[expose] public section

open scoped ENNReal

namespace BGW.PlaneTree

/-- **Mirror image** of a plane tree: the children of every vertex in reverse order
(`mirror (node ts) = node (ts.map mirror).reverse`). -/
def mirror : PlaneTree → PlaneTree := fold fun ts => node ts.reverse

/-- Mirroring a node reverses its children after mirroring each child. -/
theorem mirror_node (ts : List PlaneTree) : (node ts).mirror = node (ts.map mirror).reverse := by
  exact fold_node _ ts

/-- The mirror is an involution. -/
theorem mirror_mirror (t : PlaneTree) : t.mirror.mirror = t := by
  induction t with
  | node ts ih =>
    rw [mirror_node, mirror_node]
    simp only [List.map_reverse, List.map_map, List.reverse_reverse]
    congr 1
    exact (List.map_congr_left fun s hs => ih s hs).trans (List.map_id ts)

/-- The mirror preserves the size. -/
theorem size_mirror (t : PlaneTree) : t.mirror.size = t.size := by
  induction t with
  | node ts ih =>
    rw [mirror_node, size_node, size_node]
    simp only [List.map_reverse, List.sum_reverse, List.map_map]
    congr 2
    exact List.map_congr_left fun s hs => ih s hs

/-- The mirror preserves the offspring-product weight (same multiset of outdegrees). -/
theorem weight_mirror (p : ℕ → ℝ≥0∞) (t : PlaneTree) : weight p t.mirror = weight p t := by
  induction t with
  | node ts ih =>
    rw [mirror_node, weight_node, weight_node]
    simp only [List.length_reverse, List.length_map, List.map_reverse, List.prod_reverse,
      List.map_map]
    congr 2
    exact List.map_congr_left fun s hs => ih s hs

private theorem reverse_contour_blocks (cs : List (List ℕ)) :
    0 :: (cs.reverse.map (fun c => c.reverse.map Nat.succ ++ [0])).flatten =
      (0 :: (cs.map (fun c => c.map Nat.succ ++ [0])).flatten).reverse := by
  induction cs with
  | nil => simp
  | cons c cs ih =>
    have hh := congrArg (fun l => l ++ c.reverse.map Nat.succ ++ [0]) ih
    simp only [List.cons_append, List.append_assoc] at hh
    simpa only [List.reverse_cons, List.map_append, List.map_cons, List.map_nil,
      List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil,
      List.reverse_append, List.reverse_singleton, ← List.map_reverse, List.cons_append,
      List.append_assoc, List.reverse_nil, List.nil_append] using hh

/-- The entire contour word is reversed by mirroring. -/
theorem contour_mirror (t : PlaneTree) : t.mirror.contour = t.contour.reverse := by
  induction t with
  | node ts ih =>
    rw [mirror_node, contour_node, contour_node]
    have hm : ts.map (fun t => t.mirror.contour.map Nat.succ ++ [0]) =
        ts.map (fun t => t.contour.reverse.map Nat.succ ++ [0]) := by
      apply List.map_congr_left
      intro s hs
      rw [ih s hs]
    simp only [List.map_reverse, List.map_map, Function.comp_def]
    rw [hm]
    simpa only [List.map_reverse, List.map_map, Function.comp_def] using
      reverse_contour_blocks (ts.map contour)

/-- **Contour of the mirror**: `C_mirror(m) = C(2(z-1) - m)` for `m ≤ 2(z-1)`. -/
theorem contourAt_mirror (t : PlaneTree) {m : ℕ} (hm : m ≤ 2 * (t.size - 1)) :
    t.mirror.contourAt m = t.contourAt (2 * (t.size - 1) - m) := by
  simp only [contourAt, contour_mirror, List.getD_eq_getElem?_getD]
  rw [List.getElem?_reverse (by rw [length_contour]; omega)]
  simp only [length_contour]
  rw [show 2 * (t.size - 1) + 1 - 1 - m = 2 * (t.size - 1) - m by omega]

/-- On a closed integer cell, contour interpolation is affine between its endpoints. -/
theorem contourLin_cell (t : PlaneTree) (k : ℕ) {s : ℝ}
    (hs : s ∈ Set.Icc (k : ℝ) (k + 1)) :
    t.contourLin s = (1 - (s - k)) * (t.contourAt k : ℝ) +
      (s - k) * (t.contourAt (k + 1) : ℝ) := by
  by_cases he : s = k + 1
  · subst s
    have hf : ⌊(k : ℝ) + 1⌋₊ = k + 1 := by
      rw [← Nat.cast_add_one, Nat.floor_natCast]
    simp [contourLin, hf]
  · have hf : ⌊s⌋₊ = k := (Nat.floor_eq_iff
        (le_trans (Nat.cast_nonneg k) hs.1)).2
      ⟨hs.1, lt_of_le_of_ne hs.2 he⟩
    simp only [contourLin, hf]

/-- **Interpolated contour of the mirror**: `C_mirror(s) = C(2(z-1) - s)` on `[0, 2(z-1)]`. -/
theorem contourLin_mirror (t : PlaneTree) {s : ℝ} (hs0 : 0 ≤ s)
    (hs : s ≤ 2 * ((t.size : ℝ) - 1)) :
    t.mirror.contourLin s = t.contourLin (2 * ((t.size : ℝ) - 1) - s) := by
  let N := 2 * (t.size - 1)
  have hN : (N : ℝ) = 2 * ((t.size : ℝ) - 1) := by
    dsimp [N]
    rw [Nat.cast_mul, Nat.cast_sub (by have := size_pos t; omega)]
    norm_num
  let k := ⌊s⌋₊
  have hk : (k : ℝ) ≤ s := Nat.floor_le hs0
  have hks : s < (k : ℝ) + 1 := Nat.lt_floor_add_one s
  have hkN : k ≤ N := by
    exact_mod_cast hk.trans (hs.trans_eq hN.symm)
  by_cases he : s = (k : ℝ)
  · rw [he, contourLin_natCast, contourAt_mirror t hkN, ← hN,
      ← Nat.cast_sub hkN, contourLin_natCast]
  · have hklt : k < N := by
      have : (k : ℝ) < N := (lt_of_le_of_ne hk (Ne.symm he)).trans_le
        (hs.trans_eq hN.symm)
      exact_mod_cast this
    have hj : ((N - (k + 1) : ℕ) : ℝ) = (N : ℝ) - (k : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega), Nat.cast_add_one]
      ring
    rw [contourLin_cell t.mirror k ⟨hk, hks.le⟩,
      contourAt_mirror t hkN, contourAt_mirror t (by omega),
      contourLin_cell t (N - (k + 1)) (by
        rw [hj, ← hN]
        constructor <;> linarith)]
    rw [show N - (k + 1) + 1 = N - k by omega, hj, ← hN]
    ring

end BGW.PlaneTree
