/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.DiscreteHeightApproxMesh

/-!
# Lebesgue measure of occupation cells

The floor fibers are disjoint half-open cells of equal length. The only extra
piece after the discrete mesh endpoint is the final incomplete cell.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal Classical
open BGW.Skorokhod BGW.StableTrees.DiscreteForest

namespace BGW.StableTrees.DiscreteHeightApprox

private def meshCell (n j : ℕ) : Set ℝ := Ico ((j : ℝ) / n) (((j : ℝ) + 1) / n)

private theorem mem_meshCell_iff {n j : ℕ} (hn : 0 < n) (s : ℝ) :
    s ∈ meshCell n j ↔ 0 ≤ s ∧ ⌊(n : ℝ) * s⌋₊ = j := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  constructor
  · intro hs
    have hs0 := (div_nonneg (Nat.cast_nonneg j) hnR.le).trans hs.1
    refine ⟨hs0, (Nat.floor_eq_iff (mul_nonneg hnR.le hs0)).mpr ?_⟩
    have h1 := (div_le_iff₀ hnR).mp hs.1
    have h2 := (lt_div_iff₀ hnR).mp hs.2
    constructor <;> nlinarith only [h1, h2]
  · rintro ⟨hs0, he⟩
    have hh := (Nat.floor_eq_iff (mul_nonneg hnR.le hs0)).mp he
    constructor
    · exact (div_le_iff₀ hnR).mpr (by nlinarith only [hh.1])
    · exact (lt_div_iff₀ hnR).mpr (by nlinarith only [hh.2])

private theorem meshCell_disjoint {n : ℕ} (hn : 0 < n) :
    Pairwise (fun j k => Disjoint (meshCell n j) (meshCell n k)) := by
  intro j k hjk
  apply Set.disjoint_left.mpr
  intro s hj hk
  exact hjk (((mem_meshCell_iff hn s).mp hj).2.symm.trans ((mem_meshCell_iff hn s).mp hk).2)

private theorem measureReal_meshCell {n : ℕ} (hn : 0 < n) (j : ℕ) :
    volume.real (meshCell n j) = 1 / (n : ℝ) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  rw [meshCell, Real.volume_real_Ico_of_le
    (div_le_div_of_nonneg_right (by linarith : (j : ℝ) ≤ j + 1) hnR.le)]
  ring

/-- A finite union of distinct mesh cells has length equal to its cardinal divided by `n`. -/
theorem measureReal_meshCells {n : ℕ} (hn : 0 < n) (J : Finset ℕ) :
    volume.real (⋃ j ∈ J, Ico ((j : ℝ) / n) (((j : ℝ) + 1) / n)) = (J.card : ℝ) / n := by
  have hd : PairwiseDisjoint (↑J : Set ℕ) (meshCell n) :=
    fun _ _ _ _ hne => meshCell_disjoint hn hne
  change volume.real (⋃ j ∈ J, meshCell n j) = _
  rw [measureReal_biUnion_finset hd (fun _ _ => measurableSet_Ico)
    (fun _ _ => by rw [meshCell, Real.volume_Ico]; exact ENNReal.ofReal_ne_top)]
  simp only [measureReal_meshCell hn, Finset.sum_const, nsmul_eq_mul]
  ring

private theorem floor_eq_of_mem_tail {n : ℕ} (hn : 0 < n) (t : ℝ≥0) {s : ℝ}
    (hs : s ∈ Icc ((⌊(n : ℝ) * (t : ℝ)⌋₊ : ℝ) / n) (t : ℝ)) :
    ⌊(n : ℝ) * s⌋₊ = ⌊(n : ℝ) * (t : ℝ)⌋₊ := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hs0 : 0 ≤ s := (div_nonneg (Nat.cast_nonneg _) hnR.le).trans hs.1
  have hlow := (div_le_iff₀ hnR).mp hs.1
  have hhi := mul_le_mul_of_nonneg_left hs.2 hnR.le
  apply (Nat.floor_eq_iff (mul_nonneg hnR.le hs0)).mpr
  have hfloor := Nat.lt_floor_add_one ((n : ℝ) * (t : ℝ))
  constructor <;> nlinarith only [hlow, hhi, hfloor]

private theorem occupation_set_eq_cells (B : ℕ → ℝ) {n : ℕ} (hn : 0 < n)
    (hB : 0 < B n) (T : ℝ≥0) (ω : ℕ → ℕ) {t : ℝ≥0} (ht : t ≤ T)
    {ε : ℝ} (hε : 0 < ε) :
    {s : ℝ | 0 ≤ s ∧ s ≤ (t : ℝ) ∧
      (extendFinitePath T (forestWalkPath B n T ω)).1 s.toNNReal <
        futureInf (extendFinitePath T (forestWalkPath B n T ω)) t s.toNNReal + ε} =
      (⋃ j ∈ ((Finset.range ⌊(n : ℝ) * (t : ℝ)⌋₊).filter
        (fun j => ∀ l, j ≤ l → l ≤ ⌊(n : ℝ) * (t : ℝ)⌋₊ →
          (walk ω j : ℝ) - (walk ω l : ℝ) < ε * B n)), meshCell n j) ∪
      Icc ((⌊(n : ℝ) * (t : ℝ)⌋₊ : ℝ) / n) (t : ℝ) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  let k := ⌊(n : ℝ) * (t : ℝ)⌋₊
  have hk : (k : ℝ) ≤ (n : ℝ) * (t : ℝ) := Nat.floor_le (by positivity)
  have hkt : (k : ℝ) / n ≤ (t : ℝ) := (div_le_iff₀ hnR).mpr
    (hk.trans_eq (mul_comm _ _))
  ext s
  constructor
  · rintro ⟨hs0, hst, hgap⟩
    have hst' : s.toNNReal ≤ t := Real.toNNReal_le_iff_le_coe.mpr hst
    have hg : finiteGap T t (forestWalkPath B n T ω) s.toNNReal < ε := by
      change _ - _ < ε
      rw [Real.toNNReal_coe]
      linarith only [hgap]
    have hgood := (finiteGap_forestWalkPath_lt_iff B hn hB T ω hst' ht ε).mp hg
    rw [Real.coe_toNNReal s hs0] at hgood
    by_cases hs : (k : ℝ) / n ≤ s
    · exact Or.inr ⟨hs, hst⟩
    · left
      let j := ⌊(n : ℝ) * s⌋₊
      have hjk : j < k := by
        have hs' := (lt_div_iff₀ hnR).mp (lt_of_not_ge hs)
        have hfj := Nat.floor_le (mul_nonneg hnR.le hs0)
        have hcast : (j : ℝ) < k := by dsimp [j]; nlinarith only [hs', hfj]
        exact_mod_cast hcast
      apply Set.mem_iUnion.mpr
      refine ⟨j, Set.mem_iUnion.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hjk, hgood⟩,
        (mem_meshCell_iff hn s).mpr ⟨hs0, rfl⟩⟩⟩
  · intro hs
    rcases hs with hs | hs
    · rcases Set.mem_iUnion.mp hs with ⟨j, hs⟩
      rcases Set.mem_iUnion.mp hs with ⟨hj, hcell⟩
      obtain ⟨hjk, hgood⟩ := Finset.mem_filter.mp hj
      have hjk' : j + 1 ≤ k := by have := Finset.mem_range.mp hjk; omega
      have hsk : s < (k : ℝ) / n := hcell.2.trans_le
        (div_le_div_of_nonneg_right (by exact_mod_cast hjk') hnR.le)
      have hs0 := ((mem_meshCell_iff hn s).mp hcell).1
      have hsj := ((mem_meshCell_iff hn s).mp hcell).2
      have hst : s ≤ (t : ℝ) := hsk.le.trans hkt
      refine ⟨hs0, hst, ?_⟩
      have hst' : s.toNNReal ≤ t := Real.toNNReal_le_iff_le_coe.mpr hst
      have hgood' : ∀ l, ⌊(n : ℝ) * (s.toNNReal : ℝ)⌋₊ ≤ l → l ≤ k →
          (walk ω ⌊(n : ℝ) * (s.toNNReal : ℝ)⌋₊ : ℝ) - (walk ω l : ℝ) < ε * B n := by
        simpa only [Real.coe_toNNReal s hs0, hsj] using hgood
      have hg := (finiteGap_forestWalkPath_lt_iff B hn hB T ω hst' ht ε).mpr hgood'
      change _ - _ < ε at hg
      rw [Real.toNNReal_coe] at hg
      linarith only [hg]
    · have hs0 := (div_nonneg (Nat.cast_nonneg k) hnR.le).trans hs.1
      refine ⟨hs0, hs.2, ?_⟩
      have hst' : s.toNNReal ≤ t := Real.toNNReal_le_iff_le_coe.mpr hs.2
      have hfloor := floor_eq_of_mem_tail hn t hs
      have hgood : ∀ l, ⌊(n : ℝ) * (s.toNNReal : ℝ)⌋₊ ≤ l → l ≤ k →
          (walk ω ⌊(n : ℝ) * (s.toNNReal : ℝ)⌋₊ : ℝ) - (walk ω l : ℝ) < ε * B n := by
        rw [Real.coe_toNNReal s hs0, hfloor]
        intro l hl hl'
        have he : l = k := by omega
        rw [he, sub_self]
        exact mul_pos hε hB
      have hg := (finiteGap_forestWalkPath_lt_iff B hn hB T ω hst' ht ε).mpr hgood
      change _ - _ < ε at hg
      rw [Real.toNNReal_coe] at hg
      linarith only [hg]

/-- The finite-path occupation equals its discrete mesh count plus the final partial cell. -/
theorem finiteHeightApprox_forestWalkPath (B : ℕ → ℝ) {n : ℕ} (hn : 0 < n)
    (hB : 0 < B n) (T : ℝ≥0) (ω : ℕ → ℕ) {t : ℝ≥0} (ht : t ≤ T)
    {ε : ℝ} (hε : 0 < ε) :
    finiteHeightApprox T t ε (forestWalkPath B n T ω) = discreteOccupation B n ε ω t +
      ((t : ℝ) - (⌊(n : ℝ) * (t : ℝ)⌋₊ : ℝ) / n) / ε := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  let k := ⌊(n : ℝ) * (t : ℝ)⌋₊
  let J := (Finset.range k).filter (fun j => ∀ l, j ≤ l → l ≤ k →
    (walk ω j : ℝ) - (walk ω l : ℝ) < ε * B n)
  let U := ⋃ j ∈ J, meshCell n j
  have hk : (k : ℝ) ≤ (n : ℝ) * (t : ℝ) := Nat.floor_le (by positivity)
  have hkt : (k : ℝ) / n ≤ (t : ℝ) := (div_le_iff₀ hnR).mpr
    (hk.trans_eq (mul_comm _ _))
  have hcell (s : ℝ) (hs : s ∈ U) : 0 ≤ s ∧ s < (k : ℝ) / n := by
    rcases Set.mem_iUnion.mp hs with ⟨j, hs⟩
    rcases Set.mem_iUnion.mp hs with ⟨hj, hsj⟩
    have hjk : j + 1 ≤ k := by
      have := Finset.mem_range.mp (Finset.mem_filter.mp hj).1
      omega
    exact ⟨((mem_meshCell_iff hn s).mp hsj).1, hsj.2.trans_le
      (div_le_div_of_nonneg_right (by exact_mod_cast hjk) hnR.le)⟩
  have hdisj : Disjoint U (Icc ((k : ℝ) / n) (t : ℝ)) := by
    apply Set.disjoint_left.mpr
    intro s hs hs'
    exact (hcell s hs).2.not_ge hs'.1
  have hfinU : volume U ≠ ∞ := by
    apply ne_top_of_le_ne_top (show volume (Icc 0 (t : ℝ)) ≠ ∞ by
      rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
    apply measure_mono
    intro s hs
    exact ⟨(hcell s hs).1, (hcell s hs).2.le.trans hkt⟩
  have hfinTail : volume (Icc ((k : ℝ) / n) (t : ℝ)) ≠ ∞ := by
    rw [Real.volume_Icc]
    exact ENNReal.ofReal_ne_top
  have hU : volume.real U = (J.card : ℝ) / n := measureReal_meshCells hn J
  unfold finiteHeightApprox heightApprox
  change ε⁻¹ * volume.real _ = _
  rw [occupation_set_eq_cells B hn hB T ω ht hε]
  change ε⁻¹ * volume.real (U ∪ Icc ((k : ℝ) / n) (t : ℝ)) = _
  rw [measureReal_union hdisj measurableSet_Icc hfinU hfinTail, hU,
    Real.volume_real_Icc_of_le hkt]
  have hcard : J.card = discreteCount ω k (ε * B n) := rfl
  rw [hcard]
  unfold discreteOccupation
  dsimp only [k]
  ring

/-- The last partial cell contributes less than one mesh cell to the occupation. -/
theorem abs_finiteHeightApprox_sub_discreteOccupation_le (B : ℕ → ℝ) {n : ℕ}
    (hn : 0 < n) (hB : 0 < B n) (T : ℝ≥0) (ω : ℕ → ℕ) {t : ℝ≥0} (ht : t ≤ T)
    {ε : ℝ} (hε : 0 < ε) :
    |finiteHeightApprox T t ε (forestWalkPath B n T ω) - discreteOccupation B n ε ω t| ≤
      1 / ((n : ℝ) * ε) := by
  rw [finiteHeightApprox_forestWalkPath B hn hB T ω ht hε, add_sub_cancel_left]
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hlo := Nat.floor_le (mul_nonneg hnR.le t.2)
  have hhi := Nat.lt_floor_add_one ((n : ℝ) * (t : ℝ))
  have hrem : 0 ≤ (t : ℝ) - (⌊(n : ℝ) * (t : ℝ)⌋₊ : ℝ) / n := by
    apply sub_nonneg.mpr
    exact (div_le_iff₀ hnR).mpr (hlo.trans_eq (mul_comm _ _))
  rw [abs_of_nonneg (div_nonneg hrem hε.le)]
  have hu : (t : ℝ) - (⌊(n : ℝ) * (t : ℝ)⌋₊ : ℝ) / n ≤ 1 / n := by
    apply (le_div_iff₀ hnR).mpr
    have he : ((t : ℝ) - (⌊(n : ℝ) * (t : ℝ)⌋₊ : ℝ) / n) * n =
        (n : ℝ) * (t : ℝ) - ⌊(n : ℝ) * (t : ℝ)⌋₊ := by field_simp
    rw [he]
    linarith only [hhi]
  calc
    _ ≤ (1 / (n : ℝ)) / ε := div_le_div_of_nonneg_right hu hε.le
    _ = _ := by ring

end BGW.StableTrees.DiscreteHeightApprox
