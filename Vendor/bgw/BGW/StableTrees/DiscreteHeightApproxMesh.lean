/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.DiscreteHeightApproxJoint
public import BGW.StableTrees.DiscreteHeightApproxOccupationContinuity

/-!
# The step-path occupation mesh

Each integer index between the two endpoint floors is attained inside the real
time window. Consequently its path infimum is a finite minimum of walk values.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal Classical
open BGW.Skorokhod BGW.StableTrees.DiscreteForest BGW.Probability.RealWalk

namespace BGW.StableTrees.DiscreteHeightApprox

/-- A floor-step forest path evaluates to its integer walk value divided by the norming. -/
theorem forestWalkPath_apply_eq_walk (B : ℕ → ℝ) (n : ℕ) (T : ℝ≥0) (ω : ℕ → ℕ)
    (u : Icc (0 : ℝ) (T : ℝ)) :
    forestWalkPath B n T ω u = (walk ω ⌊(n : ℝ) * (u : ℝ)⌋₊ : ℝ) / B n := by
  rw [forestWalkPath, realStepPath_apply]
  congr 1
  simp only [partialSum, walk, Int.cast_sum, Int.cast_sub, Int.cast_one]

/-- Every index between the endpoint floors is attained inside that real time window. -/
theorem exists_time_floor {n l : ℕ} (hn : 0 < n) {s t : ℝ≥0} (hst : s ≤ t)
    (hl : ⌊(n : ℝ) * (s : ℝ)⌋₊ ≤ l ∧ l ≤ ⌊(n : ℝ) * (t : ℝ)⌋₊) :
    ∃ u : ℝ≥0, s ≤ u ∧ u ≤ t ∧ ⌊(n : ℝ) * (u : ℝ)⌋₊ = l := by
  by_cases he : l = ⌊(n : ℝ) * (s : ℝ)⌋₊
  · exact ⟨s, le_rfl, hst, he.symm⟩
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  let u : ℝ≥0 := ⟨(l : ℝ) / n, div_nonneg (Nat.cast_nonneg _) hnR.le⟩
  have hslow := Nat.lt_floor_add_one ((n : ℝ) * (s : ℝ))
  have hjl : (⌊(n : ℝ) * (s : ℝ)⌋₊ + 1 : ℕ) ≤ l := by omega
  have hjlR : (⌊(n : ℝ) * (s : ℝ)⌋₊ : ℝ) + 1 ≤ l := by exact_mod_cast hjl
  have hsu : s ≤ u := by
    change (s : ℝ) ≤ (l : ℝ) / n
    apply (le_div_iff₀ hnR).mpr
    nlinarith only [hslow, hjlR]
  have hhigh := Nat.floor_le (mul_nonneg hnR.le t.2)
  have hltR : (l : ℝ) ≤ ⌊(n : ℝ) * (t : ℝ)⌋₊ := by exact_mod_cast hl.2
  have hut : u ≤ t := by
    change (l : ℝ) / n ≤ (t : ℝ)
    apply (div_le_iff₀ hnR).mpr
    exact (hltR.trans hhigh).trans_eq (mul_comm _ _)
  refine ⟨u, hsu, hut, ?_⟩
  change ⌊(n : ℝ) * ((l : ℝ) / n)⌋₊ = l
  rw [mul_div_cancel₀ _ hnR.ne', Nat.floor_natCast]

/-- A step-path future infimum is the finite minimum between the two endpoint floors. -/
theorem futureInf_forestWalkPath (B : ℕ → ℝ) {n : ℕ} (hn : 0 < n) (T : ℝ≥0)
    (ω : ℕ → ℕ) {s t : ℝ≥0} (hst : s ≤ t) (ht : t ≤ T) :
    futureInf (extendFinitePath T (forestWalkPath B n T ω)) t s =
      (Finset.Icc ⌊(n : ℝ) * (s : ℝ)⌋₊ ⌊(n : ℝ) * (t : ℝ)⌋₊).inf'
        (Finset.nonempty_Icc.mpr (Nat.floor_mono
          (mul_le_mul_of_nonneg_left hst (Nat.cast_nonneg n))))
        (fun l => (walk ω l : ℝ) / B n) := by
  let f := extendFinitePath T (forestWalkPath B n T ω)
  let j := ⌊(n : ℝ) * (s : ℝ)⌋₊
  let k := ⌊(n : ℝ) * (t : ℝ)⌋₊
  have hjk : j ≤ k := Nat.floor_mono (mul_le_mul_of_nonneg_left hst (Nat.cast_nonneg n))
  have hval (u : ℝ≥0) (hu : u ≤ T) : f.1 u = (walk ω ⌊(n : ℝ) * (u : ℝ)⌋₊ : ℝ) / B n := by
    rw [show f = extendFinitePath T (forestWalkPath B n T ω) from rfl,
      extendFinitePath_apply T _ u hu, forestWalkPath_apply_eq_walk]
  have : Nonempty (Icc (min s t) t) := ⟨⟨t, min_le_right _ _, le_rfl⟩⟩
  apply le_antisymm
  · apply Finset.le_inf'
    intro l hl
    obtain ⟨u, hsu, hut, hfloor⟩ := exists_time_floor hn hst (Finset.mem_Icc.mp hl)
    have hb := ciInf_le (futureInf_bddBelow f t s) (⟨u, by rw [min_eq_left hst]; exact ⟨hsu, hut⟩⟩ :
      Icc (min s t) t)
    change futureInf f t s ≤ _
    exact hb.trans_eq (by rw [hval u (hut.trans ht), hfloor])
  · change _ ≤ ⨅ u : Icc (min s t) t, f.1 u
    apply le_ciInf
    intro u
    have hsu : s ≤ u := by simpa only [min_eq_left hst] using u.2.1
    rw [hval u (u.2.2.trans ht)]
    apply Finset.inf'_le
    apply Finset.mem_Icc.mpr
    exact ⟨Nat.floor_mono (mul_le_mul_of_nonneg_left hsu (Nat.cast_nonneg n)),
      Nat.floor_mono (mul_le_mul_of_nonneg_left u.2.2 (Nat.cast_nonneg n))⟩

/-- The step-path occupation test is exactly the discrete future-window test. -/
theorem finiteGap_forestWalkPath_lt_iff (B : ℕ → ℝ) {n : ℕ} (hn : 0 < n)
    (hB : 0 < B n) (T : ℝ≥0) (ω : ℕ → ℕ) {s t : ℝ≥0} (hst : s ≤ t) (ht : t ≤ T)
    (ε : ℝ) :
    finiteGap T t (forestWalkPath B n T ω) s < ε ↔
      ∀ l : ℕ, ⌊(n : ℝ) * (s : ℝ)⌋₊ ≤ l → l ≤ ⌊(n : ℝ) * (t : ℝ)⌋₊ →
        (walk ω ⌊(n : ℝ) * (s : ℝ)⌋₊ : ℝ) - (walk ω l : ℝ) < ε * B n := by
  have hs : (s : ℝ).toNNReal = s := Real.toNNReal_coe
  unfold finiteGap
  rw [hs, extendFinitePath_apply T _ s (hst.trans ht), forestWalkPath_apply_eq_walk,
    futureInf_forestWalkPath B hn T ω hst ht]
  rw [sub_lt_iff_lt_add, ← sub_lt_iff_lt_add', Finset.lt_inf'_iff]
  constructor
  · intro h l hj hl
    have he := h l (Finset.mem_Icc.mpr ⟨hj, hl⟩)
    have hd : ((walk ω ⌊(n : ℝ) * (s : ℝ)⌋₊ : ℝ) - (walk ω l : ℝ)) / B n < ε := by
      rw [sub_div]
      linarith only [he]
    exact (div_lt_iff₀ hB).mp hd
  · intro h l hl
    have hd := (div_lt_iff₀ hB).mpr
      (h l (Finset.mem_Icc.mp hl).1 (Finset.mem_Icc.mp hl).2)
    rw [sub_div] at hd
    linarith only [hd]

end BGW.StableTrees.DiscreteHeightApprox
