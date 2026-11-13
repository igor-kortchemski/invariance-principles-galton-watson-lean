/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.LongExtractionInfimumLimit

/-!
# Limits of discrete ladder blocks give running-infimum plateaus

The change in the prefix infimum across one skip-free block is precisely one downward mesh.
-/

@[expose] public section

open Filter Topology
open scoped NNReal
open BGW.Skorokhod BGW.Probability.RealWalk

namespace BGW.StableTrees

/-- Limits of finite ladder-block endpoints have the same running infimum.
Reference: Billingsley (1999), Chapter 3. -/
theorem runningInf_eq_of_tendsto_ladderBlocks {M : ℝ≥0}
    {N : ℕ → ℕ} (hN : ∀ᶠ n in atTop, 0 < N n) {B : ℕ → ℝ}
    (hB : Tendsto B atTop atTop) (ω : ℕ → ℕ → ℝ)
    (hω : ∀ n i, IsSkipFreeIncrement (ω n i)) {f : DLoc}
    (hI : Continuous (runningInfLoc f))
    (hu : Tendsto (fun n => realStepPath (M : ℝ) (N n) (B n) (ω n)) atTop
      (𝓝 (DLoc.restrict M f)))
    (r : ℕ → ℕ) (hfin : ∀ᶠ n in atTop, walkHitTime (r n + 1) (ω n) ≠ ⊤)
    (s t : ℕ → Set.Icc (0 : ℝ) (M : ℝ))
    (hs : ∀ n, (s n : ℝ) = (ladderTime (ω n) (r n) : ℝ) / N n)
    (ht : ∀ n, (t n : ℝ) = (ladderTime (ω n) (r n + 1) : ℝ) / N n)
    {a b : ℝ≥0} (hsa : Tendsto (fun n => (s n : ℝ)) atTop (𝓝 (a : ℝ)))
    (htb : Tendsto (fun n => (t n : ℝ)) atTop (𝓝 (b : ℝ))) :
    runningInfLoc f a = runningInfLoc f b := by
  have hIs := tendsto_extractionPrefixInf hI hu hsa
  have hIt := tendsto_extractionPrefixInf hI hu htb
  have heq : ∀ᶠ n in atTop,
      extractionPrefixInf (realStepPath (M : ℝ) (N n) (B n) (ω n)) (t n) -
        extractionPrefixInf (realStepPath (M : ℝ) (N n) (B n) (ω n)) (s n) =
          -(B n)⁻¹ := by
    filter_upwards [hN, hB.eventually (eventually_gt_atTop 0), hfin] with n hn hnB hnfin
    have hsn : s n = ⟨(ladderTime (ω n) (r n) : ℝ) / N n, by positivity,
        by rw [← hs]; exact (s n).2.2⟩ := Subtype.ext (hs n)
    have htn : t n = ⟨(ladderTime (ω n) (r n + 1) : ℝ) / N n, by positivity,
        by rw [← ht]; exact (t n).2.2⟩ := Subtype.ext (ht n)
    have hMs : (ladderTime (ω n) (r n) : ℝ) / N n ≤ M := by
      rw [← hs n]
      exact (s n).2.2
    have hMt : (ladderTime (ω n) (r n + 1) : ℝ) / N n ≤ M := by
      rw [← ht n]
      exact (t n).2.2
    rw [hsn, htn, extractionPrefixInf_at_ladderTime hn hnB hnfin hMt,
      extractionPrefixInf_at_ladderTime hn hnB
        (ladderTime_mono_of_finite (Nat.le_succ _) hnfin).1 hMs,
      partialSum_ladderTime_eq (hω n) hnfin,
      partialSum_ladderTime_eq (hω n)
        (ladderTime_mono_of_finite (Nat.le_succ _) hnfin).1]
    push_cast
    ring
  have hzero : Tendsto (fun n =>
      extractionPrefixInf (realStepPath (M : ℝ) (N n) (B n) (ω n)) (t n) -
        extractionPrefixInf (realStepPath (M : ℝ) (N n) (B n) (ω n)) (s n)) atTop (𝓝 0) := by
    have hinv : Tendsto (fun n => -(B n)⁻¹) atTop (𝓝 (0 : ℝ)) := by
      simpa only [neg_zero, Function.comp_apply] using (tendsto_inv_atTop_zero.comp hB).neg
    exact hinv.congr' (Filter.EventuallyEq.symm heq)
  have hlim : runningInfLoc f b - runningInfLoc f a = 0 :=
    tendsto_nhds_unique (hIt.sub hIs) hzero
  exact (sub_eq_zero.mp hlim).symm

end BGW.StableTrees
