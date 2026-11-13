/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.Skorokhod.VervaatRotationTimeChange

/-!
# Uniform control of aligned Vervaat transforms

After aligning the minimizing times, rotation preserves uniform path control.
The two endpoint values and the infimum account for the additional errors.
-/

@[expose] public section

open Set

namespace BGW.Skorokhod

/-- Rotating an aligned approximation controls both the time and path errors. -/
theorem exists_vervaat_timeChange_bound (u f : D 1 ℝ) (ρ : TimeChange 1)
    (halign : ρ (vervaatTime f) = vervaatTime u) {d e : ℝ}
    (hd : ∀ t, |(ρ t : ℝ) - t| ≤ d)
    (hp : ∀ t, dist (u (ρ t)) (f t) ≤ e)
    (hm : dist (⨅ s, u s) (⨅ s, f s) ≤ e) :
    ∃ μ : TimeChange 1,
      (∀ t, |(μ t : ℝ) - t| ≤ 2 * d + |(vervaatTime u : ℝ) - vervaatTime f|) ∧
      ∀ t, dist (vervaatD u (μ t)) (vervaatD f t) ≤ 4 * e := by
  obtain ⟨μ, hμ, hmove⟩ := exists_rotated_timeChange ρ (vervaatTime f)
    (vervaatTime u) halign hd
  have he : 0 ≤ e := dist_nonneg.trans (hp ⟨0, le_rfl, zero_le_one⟩)
  have hzero : dist (u ⟨0, le_rfl, zero_le_one⟩) (f ⟨0, le_rfl, zero_le_one⟩) ≤ e := by
    simpa only [TimeChange.apply_zero ρ zero_le_one] using hp ⟨0, le_rfl, zero_le_one⟩
  have hone : dist (u ⟨1, zero_le_one, le_rfl⟩) (f ⟨1, zero_le_one, le_rfl⟩) ≤ e := by
    simpa only [TimeChange.apply_top ρ zero_le_one] using hp ⟨1, zero_le_one, le_rfl⟩
  refine ⟨μ, hmove, ?_⟩
  intro t
  change dist (if (vervaatTime u : ℝ) + μ t ≤ 1 then _ else _)
    (if (vervaatTime f : ℝ) + t ≤ 1 then _ else _) ≤ _
  by_cases ht : (vervaatTime f : ℝ) + t ≤ 1
  · let A := projIcc 0 1 zero_le_one ((vervaatTime f : ℝ) + t)
    have htime : (vervaatTime u : ℝ) + μ t = (ρ A : ℝ) := by
      rw [hμ, ite_eq_left ht]
      dsimp [A]
      ring
    have hproj : projIcc 0 1 zero_le_one ((vervaatTime u : ℝ) + μ t) = ρ A := by
      rw [htime, projIcc_val]
    rw [ite_eq_left ht, ite_eq_left (htime ▸ (ρ A).2.2), hproj]
    have hb := (dist_sub_sub_le (u (ρ A)) (⨅ s, u s) (f A) (⨅ s, f s)).trans
      (add_le_add (hp A) hm)
    exact hb.trans (by linarith)
  · let B := projIcc 0 1 zero_le_one ((vervaatTime f : ℝ) + t - 1)
    have hmem : (vervaatTime f : ℝ) + t - 1 ∈ Icc (0 : ℝ) 1 := by
      constructor <;> linarith [(vervaatTime f).2.2, t.2.2]
    have hBpos : (⟨0, le_rfl, zero_le_one⟩ : Icc (0 : ℝ) 1) < B := by
      dsimp [B]
      rw [projIcc_of_mem zero_le_one hmem]
      change (0 : ℝ) < (vervaatTime f : ℝ) + t - 1
      linarith
    have hρpos : (0 : ℝ) < ρ B := by
      have h := ρ.strictMono hBpos
      rw [TimeChange.apply_zero ρ zero_le_one] at h
      exact h
    have htime : (vervaatTime u : ℝ) + μ t - 1 = (ρ B : ℝ) := by
      rw [hμ, ite_eq_right ht]
      dsimp [B]
      ring
    have hucut : ¬ (vervaatTime u : ℝ) + μ t ≤ 1 := by linarith
    have hproj : projIcc 0 1 zero_le_one ((vervaatTime u : ℝ) + μ t - 1) = ρ B := by
      rw [htime, projIcc_val]
    rw [ite_eq_right ht, ite_eq_right hucut, hproj]
    apply le_trans ((dist_sub_sub_le _ _ _ _).trans (add_le_add
      ((dist_sub_sub_le _ _ _ _).trans (add_le_add
        ((dist_add_add_le _ _ _ _).trans (add_le_add (hp B) hone)) hm)) hzero))
    linarith

end BGW.Skorokhod
