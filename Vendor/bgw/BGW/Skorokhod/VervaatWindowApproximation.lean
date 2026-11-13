/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.Skorokhod.VervaatWindow

/-!
# Path estimates for the local window correction

The source and corrected source times remain near the minimum inside the
window. Outside it the original approximation is preserved exactly.
-/

@[expose] public section

open Set

namespace BGW.Skorokhod

/-- Align one time by a local correction, paying only the oscillation in its window. -/
theorem exists_aligned_timeChange (u f : D 1 ℝ) (σ : TimeChange 1)
    (g a : Icc (0 : ℝ) 1) {η d e : ℝ} (hη : 0 < η)
    (hleft : η ≤ (g : ℝ)) (hright : (g : ℝ) + η ≤ 1)
    (hnear : dist (σ.symm a) g < η)
    (hd : ∀ t, |(σ t : ℝ) - t| ≤ d)
    (hp : ∀ t, dist (u (σ t)) (f t) ≤ e)
    (hf : ∀ s, dist s g < 2 * η → dist (f s) (f g) ≤ e) :
    ∃ ρ : TimeChange 1, ρ g = a ∧
      (∀ t, |(ρ t : ℝ) - t| ≤ d + η) ∧
      ∀ t, dist (u (ρ t)) (f t) ≤ 3 * e := by
  obtain ⟨κ, hκg, hκout, hκmove⟩ := exists_local_timeChange g (σ.symm a)
    hη hleft hright (by simpa only [Subtype.dist_eq, Real.dist_eq] using hnear)
  let ρ := κ.trans σ
  have he : 0 ≤ e := dist_nonneg.trans (hp g)
  refine ⟨ρ, ?_, ?_, ?_⟩
  · change σ (κ g) = a
    rw [hκg, OrderIso.apply_symm_apply]
  · intro t
    change |(σ (κ t) : ℝ) - t| ≤ _
    calc
      |(σ (κ t) : ℝ) - t| ≤ |(σ (κ t) : ℝ) - κ t| + |(κ t : ℝ) - t| :=
        abs_sub_le _ _ _
      _ ≤ d + η := add_le_add (hd (κ t)) ((hκmove t).trans
        (by simpa only [Subtype.dist_eq, Real.dist_eq] using hnear.le))
  · intro t
    change dist (u (σ (κ t))) (f t) ≤ _
    by_cases ht : η ≤ |(t : ℝ) - g|
    · rw [hκout t ht]
      exact (hp t).trans (by linarith)
    · have htg : dist t g < η := by
        simpa only [Subtype.dist_eq, Real.dist_eq] using lt_of_not_ge ht
      have hκt : dist (κ t) t < η := by
        exact (show dist (κ t) t ≤ dist (σ.symm a) g from
          hκmove t).trans_lt hnear
      have hκg' : dist (κ t) g < 2 * η :=
        (dist_triangle (κ t) t g).trans_lt (by linarith)
      calc
        dist (u (σ (κ t))) (f t) ≤ dist (u (σ (κ t))) (f (κ t)) +
            dist (f (κ t)) (f g) + dist (f g) (f t) := dist_triangle4 _ _ _ _
        _ ≤ 3 * e := by
          have h1 := hp (κ t)
          have h2 := hf (κ t) hκg'
          have h3 := hf t (htg.trans (by linarith))
          rw [dist_comm (f t)] at h3
          linarith

end BGW.Skorokhod
