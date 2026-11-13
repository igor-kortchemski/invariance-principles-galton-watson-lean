/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.LongExtractionInterior

/-!
# Running infima under extraction clocks

Prefix infima obey the same uniform error bound as the paths under an increasing time change.
-/

@[expose] public section

open Filter Topology
open scoped NNReal
open BGW.Skorokhod BGW.Probability.RealWalk

namespace BGW.StableTrees

/-- The infimum of a finite-horizon path up to a time in its domain.
Reference: Billingsley (1999), Chapter 3. -/
noncomputable def extractionPrefixInf {M : ℝ} (p : D M ℝ)
    (t : Set.Icc (0 : ℝ) M) : ℝ := ⨅ s : Set.Iic t, p s

/-- A path on a compact horizon is bounded below.
Reference: Billingsley (1999), Chapter 3. -/
private theorem bddBelow_prefixInf {M : ℝ} (p : D M ℝ) (t : Set.Icc (0 : ℝ) M) :
    BddBelow (Set.range fun s : Set.Iic t => p s) := by
  apply (isBounded_range p).bddBelow.mono
  rintro _ ⟨s, rfl⟩
  exact ⟨s, rfl⟩

/-- An aligned uniform path error controls every prefix infimum.
Reference: Billingsley (1999), Chapter 3. -/
theorem extractionPrefixInf_aligned_le {M : ℝ} (p q : D M ℝ) (σ : TimeChange M)
    {ε : ℝ} (hε : ∀ s, dist (p (σ s)) (q s) ≤ ε) (t : Set.Icc (0 : ℝ) M) :
    |extractionPrefixInf p (σ t) - extractionPrefixInf q t| ≤ ε := by
  have hp := bddBelow_prefixInf p (σ t)
  have hq := bddBelow_prefixInf q t
  rw [abs_le]
  constructor
  · have hlow : extractionPrefixInf q t - ε ≤ extractionPrefixInf p (σ t) := by
      apply le_ciInf
      intro s
      let z := σ.symm s.1
      have hzt : z ≤ t := by
        apply σ.le_iff_le.mp
        rw [show σ z = s.1 from σ.apply_symm_apply s.1]
        exact s.2
      have hi : extractionPrefixInf q t ≤ q z := ciInf_le hq ⟨z, hzt⟩
      have he := hε z
      rw [Real.dist_eq, abs_le] at he
      have hz : σ z = s := σ.apply_symm_apply s.1
      rw [hz] at he
      linarith [he.1]
    linarith
  · have hupp : extractionPrefixInf p (σ t) - ε ≤ extractionPrefixInf q t := by
      apply le_ciInf
      intro s
      have hi : extractionPrefixInf p (σ t) ≤ p (σ s) :=
        ciInf_le hp ⟨σ s, σ.monotone s.2⟩
      have he := hε s
      rw [Real.dist_eq, abs_le] at he
      linarith [he.2]
    linarith

/-- Restricting a local path preserves prefix infima.
Reference: Billingsley (1999), Chapter 3. -/
theorem extractionPrefixInf_restrict (M : ℝ≥0) (f : DLoc) (t : Set.Icc (0 : ℝ) (M : ℝ)) :
    extractionPrefixInf (DLoc.restrict M f) t =
      runningInfLoc f ⟨(t : ℝ), t.2.1⟩ := by
  apply le_antisymm
  · refine le_csInf ⟨f.1 ⟨(t : ℝ), t.2.1⟩,
      ⟨⟨⟨(t : ℝ), t.2.1⟩, le_rfl⟩, rfl⟩⟩ ?_
    rintro _ ⟨u, rfl⟩
    let s : Set.Icc (0 : ℝ) (M : ℝ) :=
      ⟨u, u.1.2, by exact_mod_cast u.2.trans (show (⟨(t : ℝ), t.2.1⟩ : ℝ≥0) ≤ M from t.2.2)⟩
    exact ciInf_le (bddBelow_prefixInf (DLoc.restrict M f) t)
      ⟨s, by exact_mod_cast u.2⟩
  · apply le_ciInf
    intro s
    exact runningInfLoc_le_eval f ⟨(t : ℝ), t.2.1⟩
      ⟨⟨(s.1 : ℝ), s.1.2.1⟩, by exact_mod_cast s.2⟩

/-- At a finite ladder time, the scaled path's prefix infimum is its current value.
Reference: Billingsley (1999), Chapter 3. -/
theorem extractionPrefixInf_at_ladderTime {M B : ℝ} {ω : ℕ → ℝ} {n r : ℕ}
    (hn : 0 < n) (hB : 0 < B) (hfin : walkHitTime r ω ≠ ⊤)
    (hM : (ladderTime ω r : ℝ) / n ≤ M) :
    extractionPrefixInf (realStepPath M n B ω)
      ⟨(ladderTime ω r : ℝ) / n, by positivity, hM⟩ =
        partialSum ω (ladderTime ω r) / B := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  let t : Set.Icc (0 : ℝ) M := ⟨(ladderTime ω r : ℝ) / n, by positivity, hM⟩
  have ht : realStepPath M n B ω t = partialSum ω (ladderTime ω r) / B := by
    have hmul : (n : ℝ) * ((ladderTime ω r : ℝ) / n) = ladderTime ω r := by field_simp
    simp only [realStepPath_apply, t, hmul, Nat.floor_natCast]
  apply le_antisymm
  · exact (ciInf_le (bddBelow_prefixInf (realStepPath M n B ω) t) ⟨t, le_rfl⟩).trans_eq ht
  · apply le_ciInf
    intro s
    apply stepPath_ge_at_ladderTime (M := M) (n := n) hB hfin s.1
    have hs : (s.1 : ℝ) ≤ (ladderTime ω r : ℝ) / n := s.2
    simpa only [mul_comm] using (le_div_iff₀ hn').mp hs

end BGW.StableTrees
