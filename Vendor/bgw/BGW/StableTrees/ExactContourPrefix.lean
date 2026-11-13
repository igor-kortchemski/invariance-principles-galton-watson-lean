/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.ExactContourMirror

/-!
# Contour bracketing using only a strict height prefix

A height bound at the right endpoint excludes bracket indices beyond that endpoint.
The resulting comparison uses heights and their oscillations only on the larger prefix.
-/

@[expose] public section

namespace BGW.PlaneTree

/-- Along the DFS order, the height can increase by at most the number of steps. -/
theorem heightSeq_add_le (t : PlaneTree) (m d : ℕ) :
    t.heightSeq (m + d) ≤ t.heightSeq m + d := by
  induction d with
  | zero => simp
  | succ d ih =>
    have hh := heightSeq_succ_le t (m + d)
    simpa only [Nat.add_assoc] using hh.trans (Nat.add_le_add_right ih 1)

/-- A height bound at `m` prevents a contour bracket for time `2u` from passing `m`. -/
theorem contourLin_bracket_prefix (t : PlaneTree) {m : ℕ} {u : ℝ}
    (hu0 : 0 ≤ u) (hu : u ≤ t.size)
    (hbuffer : 2 * u + (t.heightSeq m : ℝ) ≤ 2 * m) :
    ∃ i < t.size, i ≤ m ∧ u - 1 ≤ i ∧
      (i : ℝ) ≤ u + (t.heightSeq i : ℝ) / 2 ∧
      |t.contourLin (2 * u) - t.heightSeq i| ≤
        |(t.heightSeq (i + 1) : ℝ) - t.heightSeq i| + 1 := by
  obtain ⟨i, hi, hlo, hhi, hC⟩ :=
    contourLin_bracket t (s := 2 * u) (by positivity) (by linarith)
  have him : i ≤ m := by
    by_contra hnot
    have hmi : m ≤ i := (Nat.lt_of_not_ge hnot).le
    have hh := heightSeq_add_le t m (i - m)
    rw [Nat.add_sub_of_le hmi] at hh
    have hhR : (t.heightSeq i : ℝ) ≤ (t.heightSeq m : ℝ) + ((i - m : ℕ) : ℝ) := by
      exact_mod_cast hh
    rw [Nat.cast_sub hmi] at hhR
    have hmiR : (m : ℝ) < i := by exact_mod_cast Nat.lt_of_not_ge hnot
    linarith
  refine ⟨i, hi, him, ?_, ?_, hC⟩ <;> linarith

/-- Prefix-local contour/height comparison: all height and modulus hypotheses stop at `m+1`. -/
theorem contourLin_two_mul_sub_heightLin_le_prefix (t : PlaneTree) {m : ℕ} {u ω δ : ℝ}
    (hu0 : 0 ≤ u) (hu : u ≤ m + 1) (hm : m + 1 ≤ t.size)
    (hbuffer : 2 * u + (t.heightSeq m : ℝ) ≤ 2 * m) (hω1 : 1 ≤ ω)
    (hω2 : ∀ j : ℕ, j ≤ m → (t.heightSeq j : ℝ) / 2 ≤ ω)
    (hδ : ∀ x y : ℝ, 0 ≤ x → x ≤ m + 1 → 0 ≤ y → y ≤ m + 1 →
      |x - y| ≤ ω → |t.heightLin x - t.heightLin y| ≤ δ) :
    |t.contourLin (2 * u) - t.heightLin u| ≤ 2 * δ + 1 := by
  have hmR : (m : ℝ) + 1 ≤ t.size := by exact_mod_cast hm
  obtain ⟨i, hi, him, hlo, hhi, hC⟩ :=
    contourLin_bracket_prefix t hu0 (hu.trans hmR) hbuffer
  have hiR : (i : ℝ) ≤ m := by exact_mod_cast him
  have hdist : |u - (i : ℝ)| ≤ ω := by
    apply abs_le.mpr
    constructor <;> linarith [hω2 i him]
  have hui := hδ u i hu0 hu (Nat.cast_nonneg i) (by linarith) hdist
  have hunit : |(i : ℝ) - (i + 1 : ℝ)| ≤ ω := by
    rw [show (i : ℝ) - (i + 1 : ℝ) = -1 by ring]
    simpa using hω1
  have hij := hδ i (i + 1) (Nat.cast_nonneg i) (by linarith)
    (by positivity) (by linarith) hunit
  rw [heightLin_natCast] at hui hij
  rw [show (i : ℝ) + 1 = ((i + 1 : ℕ) : ℝ) by push_cast; rfl,
    heightLin_natCast] at hij
  calc
    |t.contourLin (2 * u) - t.heightLin u| ≤
        |t.contourLin (2 * u) - t.heightSeq i| +
        |(t.heightSeq i : ℝ) - t.heightLin u| := abs_sub_le _ _ _
    _ ≤ (|(t.heightSeq (i + 1) : ℝ) - t.heightSeq i| + 1) + δ :=
      add_le_add hC (by simpa only [abs_sub_comm] using hui)
    _ ≤ 2 * δ + 1 := by
      have hj := hij
      rw [abs_sub_comm] at hj
      linarith

end BGW.PlaneTree
