/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.LongExtraction

/-!
# Finite-prefix localization of the selected block

A selected long block ending within an observed prefix is unchanged by any modification of
the subsequent increments. This includes its endpoints and closed cut on every output horizon.
-/

@[expose] public section

open Set Filter
open scoped NNReal Classical
open BGW.Skorokhod BGW.Probability.RealWalk

namespace BGW.StableTrees.PathTail

private theorem partialSum_eq_of_prefix {ω ξ : ℕ → ℝ} {N k : ℕ}
    (h : ∀ i < N, ω i = ξ i) (hk : k ≤ N) : partialSum ω k = partialSum ξ k := by
  apply Finset.sum_congr rfl
  intro i hi
  exact h i ((Finset.mem_range.mp hi).trans_le hk)

private theorem walkHitTime_eq_of_prefix {ω ξ : ℕ → ℝ} {N r : ℕ}
    (h : ∀ i < N, ω i = ξ i) (hfin : walkHitTime r ω ≠ ⊤)
    (hend : ladderTime ω r ≤ N) : walkHitTime r ξ = walkHitTime r ω := by
  rw [← ENat.natCast_toNat hfin]
  change walkHitTime r ξ = (ladderTime ω r : ℕ∞)
  rw [walkHitTime, ← iInf_subtype'']
  apply ENat.iInf_eq_natCast_iff.mpr
  refine ⟨⟨⟨ladderTime ω r, ?_⟩, rfl⟩, ?_⟩
  · change partialSum ξ (ladderTime ω r) ≤ -(r : ℝ)
    rw [← partialSum_eq_of_prefix h hend]
    exact partialSum_ladderTime_le hfin
  · rintro ⟨k, hk⟩
    by_contra hnot
    have hklt : k < ladderTime ω r := by exact_mod_cast (lt_of_not_ge hnot)
    have hbefore := lt_partialSum_of_lt_ladderTime hfin hklt
    rw [partialSum_eq_of_prefix h (hklt.le.trans hend)] at hbefore
    exact hbefore.not_ge hk

/-- If a selected long block ends in an observed prefix, modifying later increments does not
change its extracted endpoints or cut path. -/
theorem extractionTriple_eq_of_prefix {ω ξ : ℕ → ℝ} {N n : ℕ}
    (h : ∀ i < N, ω i = ξ i)
    (hmem : firstLongIndex n ω ∈ longBlockSet n ω)
    (hend : ladderTime ω (firstLongIndex n ω + 1) ≤ N) (b : ℝ) (T : ℝ≥0) :
    extractionTriple b n T ξ = extractionTriple b n T ω := by
  let r := firstLongIndex n ω
  change ladderTime ω (r + 1) ≤ N at hend
  have hfin : walkHitTime (r + 1) ω ≠ ⊤ := hmem.1
  have hmono : ladderTime ω r ≤ ladderTime ω (r + 1) :=
    (ladderTime_mono_of_finite (Nat.le_succ r) hfin).2
  have hh (j : ℕ) (hj : j ≤ r + 1) : walkHitTime j ξ = walkHitTime j ω :=
    walkHitTime_eq_of_prefix h (ladderTime_mono_of_finite hj hfin).1
      ((ladderTime_mono_of_finite hj hfin).2.trans hend)
  have ht (j : ℕ) (hj : j ≤ r + 1) : ladderTime ξ j = ladderTime ω j := by
    exact congrArg ENat.toNat (hh j hj)
  have hm (j : ℕ) (hj : j ≤ r) : j ∈ longBlockSet n ξ ↔ j ∈ longBlockSet n ω := by
    simp only [longBlockSet, mem_ofPred_eq, hh (j + 1) (by omega), ht j (by omega),
      ht (j + 1) (by omega)]
  have hmr : r ∈ longBlockSet n ξ := (hm r le_rfl).mpr hmem
  have hr : firstLongIndex n ξ = r := by
    have hle : firstLongIndex n ξ ≤ r := Nat.sInf_le hmr
    apply le_antisymm hle
    by_contra hn
    have hj : firstLongIndex n ξ < r := lt_of_not_ge hn
    have hmξ : firstLongIndex n ξ ∈ longBlockSet n ξ := Nat.sInf_mem ⟨r, hmr⟩
    have hmω := (hm _ hj.le).mp hmξ
    exact Nat.notMem_of_lt_sInf hj hmω
  have hblock : blockIncrements ξ r = blockIncrements ω r := by
    funext i
    simp only [blockIncrements, ht r (by omega), ht (r + 1) le_rfl]
    split_ifs with hi
    · symm
      exact h _ (by omega)
    · rfl
  simp only [extractionTriple, extractionEndpoints, hr, ht r (by omega),
    ht (r + 1) le_rfl, hblock]
  rfl

end BGW.StableTrees.PathTail
