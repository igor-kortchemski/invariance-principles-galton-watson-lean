/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.ExactPairBasic

/-!
# Degree prefixes determine interpolated height prefixes

Record minima recover every height through the degree-prefix index. One extra degree
determines the final interpolation interval, including the test that its vertex exists.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal Classical
open BGW.Skorokhod BGW.StableTrees

namespace BGW.StableTrees.ExactPair

open BGW.StableTrees.DiscreteForest BGW.StableTrees.PathTail BGW.StableTrees.TailPair
  BGW.StableTrees.ExactPrefix

private theorem lukasiewicz_eq_of_take_degrees {t s : BGW.PlaneTree} {m : ℕ}
    (h : t.degrees.take m = s.degrees.take m) {i : ℕ} (hi : i ≤ m) :
    t.lukasiewicz i = s.lukasiewicz i := by
  have hh := congrArg (List.take i) h
  simp only [List.take_take, min_eq_left hi] at hh
  simp only [BGW.PlaneTree.lukasiewicz, BGW.PlaneTree.increments, ← List.map_take, hh]

private theorem lt_size_iff_of_take_degrees {t s : BGW.PlaneTree} {m : ℕ}
    (h : t.degrees.take m = s.degrees.take m) {i : ℕ} (hi : i ≤ m) :
    i < t.size ↔ i < s.size := by
  have imp (t s : BGW.PlaneTree) (he : t.degrees.take m = s.degrees.take m)
      (hit : i < t.size) : i < s.size := by
    by_contra his
    have hsi : s.size ≤ i := by omega
    have heq := lukasiewicz_eq_of_take_degrees he (hsi.trans hi)
    have hpos := BGW.PlaneTree.sum_take_increments_nonneg t
      (i := s.size) (by simpa using hsi.trans_lt hit)
    have hneg : s.lukasiewicz s.size = -1 := by
      rw [BGW.PlaneTree.lukasiewicz, List.take_of_length_le
        (by simp), BGW.PlaneTree.sum_increments]
    rw [hneg] at heq
    change 0 ≤ t.lukasiewicz s.size at hpos
    omega
  exact ⟨imp t s h, imp s t h.symm⟩

private theorem heightSeq_eq_of_take_degrees {t s : BGW.PlaneTree} {m : ℕ}
    (h : t.degrees.take m = s.degrees.take m) {i : ℕ} (hi : i ≤ m) :
    t.heightSeq i = s.heightSeq i := by
  by_cases hit : i < t.size
  · have his := (lt_size_iff_of_take_degrees h hi).mp hit
    rw [BGW.PlaneTree.heightSeq_of_lt t hit, BGW.PlaneTree.heightSeq_of_lt s his,
      BGW.PlaneTree.height_eq_card_recordMin, BGW.PlaneTree.height_eq_card_recordMin]
    congr 1
    apply Finset.filter_congr
    intro j hj
    have hjm : j ≤ m := (Finset.mem_range.mp hj).le.trans hi
    simp only [lukasiewicz_eq_of_take_degrees h hjm]
    constructor <;> intro hh k hjk hki
    · rw [← lukasiewicz_eq_of_take_degrees h (hki.trans hi)]
      exact hh k hjk hki
    · rw [lukasiewicz_eq_of_take_degrees h (hki.trans hi)]
      exact hh k hjk hki
  · have his : ¬ i < s.size := by rwa [← lt_size_iff_of_take_degrees h hi]
    rw [BGW.PlaneTree.heightSeq_of_le t (by omega),
      BGW.PlaneTree.heightSeq_of_le s (by omega)]

/-- **Prefix measurability of the pair** (deterministic repair): the pair on `[0,a]` reads the
walk up to index `⌊an⌋` and the heights up to index `⌊an⌋ + 1`, hence it is a function of the
first `m` DFS degrees for every `m ≥ ⌊an⌋ + 1` (in general not of the first `⌊an⌋`). -/
theorem exists_treePairPath_eq_comp_treePrefix (B : ℕ → ℝ) (n : ℕ) (a : ℝ≥0) {m : ℕ}
    (hm : ⌊(a : ℝ) * n⌋₊ + 1 ≤ m) :
    ∃ G : List ℕ → D (a : ℝ) ℝ × C(Set.Icc (0 : ℝ) (a : ℝ), ℝ),
      ∀ τ : BGW.LocallyFinite.Tree, treePairPath B n a τ = G (treePrefix m τ) := by
  have hfactor : (treePairPath B n a).FactorsThrough (treePrefix m) := by
    intro τ σ he
    have hmpos : 0 < m := by omega
    have hf : BGW.LocallyFinite.FiniteVertices τ ↔ BGW.LocallyFinite.FiniteVertices σ := by
      have imp (τ σ : BGW.LocallyFinite.Tree) (he : treePrefix m τ = treePrefix m σ)
          (hτ : BGW.LocallyFinite.FiniteVertices τ) : BGW.LocallyFinite.FiniteVertices σ := by
        by_contra hσ
        obtain ⟨t, rfl⟩ := (BGW.LocallyFinite.exists_toLocallyFinite_iff τ).mpr hτ
        rw [treePrefix_toLocallyFinite, treePrefix, dite_eq_right hσ] at he
        have hh := congrArg List.length he
        simp only [List.length_take, BGW.PlaneTree.length_degrees, List.length_nil] at hh
        have hp := t.size_pos
        omega
      exact ⟨imp τ σ he, imp σ τ he.symm⟩
    by_cases hτ : BGW.LocallyFinite.FiniteVertices τ
    · have hσ := hf.mp hτ
      obtain ⟨t, rfl⟩ := (BGW.LocallyFinite.exists_toLocallyFinite_iff τ).mpr hτ
      obtain ⟨s, rfl⟩ := (BGW.LocallyFinite.exists_toLocallyFinite_iff σ).mpr hσ
      rw [treePrefix_toLocallyFinite, treePrefix_toLocallyFinite] at he
      have hfloor (u : Icc (0 : ℝ) (a : ℝ)) : ⌊(n : ℝ) * (u : ℝ)⌋₊ + 1 ≤ m := by
        have hh : ⌊(n : ℝ) * (u : ℝ)⌋₊ ≤ ⌊(a : ℝ) * n⌋₊ := by
          apply Nat.floor_mono
          nlinarith [u.2.2, (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
        omega
      apply Prod.ext
      · apply BGW.Skorokhod.ext
        intro u
        change BGW.Probability.RealWalk.partialSum (treeIncrementSeq t.toLocallyFinite)
          ⌊(n : ℝ) * (u : ℝ)⌋₊ / B n =
            BGW.Probability.RealWalk.partialSum (treeIncrementSeq s.toLocallyFinite)
              ⌊(n : ℝ) * (u : ℝ)⌋₊ / B n
        simp only [BGW.Probability.RealWalk.partialSum, treeIncrementSeq,
          ExactPrefix.treeIncrements_toLocallyFinite, sum_range_getD]
        congr 2
        exact lukasiewicz_eq_of_take_degrees he (by have := hfloor u; omega)
      · ext u
        change treeHeightPath B n a t.toLocallyFinite u =
          treeHeightPath B n a s.toLocallyFinite u
        rw [treeHeightPath_toLocallyFinite, treeHeightPath_toLocallyFinite,
          BGW.PlaneTree.heightLin, BGW.PlaneTree.heightLin,
          heightSeq_eq_of_take_degrees he (hfloor u),
          heightSeq_eq_of_take_degrees he (by have := hfloor u; omega)]
    · have hσ : ¬ BGW.LocallyFinite.FiniteVertices σ := fun hh => hτ (hf.mpr hh)
      apply Prod.ext
      · apply BGW.Skorokhod.ext
        intro u
        simp [treePairPath, treePrefixPath, treeIncrementSeq, treeIncrements,
          hτ, hσ, realStepPath_apply, BGW.Probability.RealWalk.partialSum]
      · ext u
        simp [treePairPath, treeHeightPath, continuous_treeHeightLin, treeHeightLin, hτ, hσ]
  exact ⟨Function.extend (treePrefix m) (treePairPath B n a)
    (fun _ => treePairPath B n a BGW.LocallyFinite.leaf),
      fun τ => (hfactor.extend_apply _ τ).symm⟩

end BGW.StableTrees.ExactPair
