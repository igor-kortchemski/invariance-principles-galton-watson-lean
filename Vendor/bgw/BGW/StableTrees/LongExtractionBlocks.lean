/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.LongExtractionLadder

/-!
# Exact skip-free ladder blocks

Finite weak hits of integer barriers are exact. Consecutive hits delimit nonnegative blocks.
-/

@[expose] public section

open Filter Topology
open BGW.Skorokhod BGW.Probability.RealWalk

namespace BGW.StableTrees

/-- Before a finite weak hit, the walk is strictly above its barrier.
Reference: Billingsley (1999), Chapter 3. -/
theorem lt_partialSum_of_lt_ladderTime {ω : ℕ → ℝ} {r k : ℕ}
    (hfin : walkHitTime r ω ≠ ⊤) (hk : k < ladderTime ω r) :
    -(r : ℝ) < partialSum ω k := by
  by_contra h
  have hhit : walkHitTime r ω ≤ (k : ℕ∞) :=
    iInf_le_of_le k (iInf_le _ (le_of_not_gt h))
  rw [← ENat.natCast_toNat hfin] at hhit
  have : ladderTime ω r ≤ k := by exact_mod_cast hhit
  omega

/-- Weak hitting times are monotone in the barrier level.
Reference: Billingsley (1999), Chapter 3. -/
private theorem walkHitTime_mono_level (ω : ℕ → ℝ) : Monotone (fun r => walkHitTime r ω) := by
  intro r s hrs
  apply le_iInf
  intro k
  apply le_iInf
  intro hk
  apply iInf_le_of_le k
  apply iInf_le
  exact (show partialSum ω k ≤ -(s : ℝ) from hk).trans
    (neg_le_neg (by exact_mod_cast hrs))

/-- A finite higher hit makes every lower hit finite and orders the finite readings.
Reference: Billingsley (1999), Chapter 3. -/
theorem ladderTime_mono_of_finite {ω : ℕ → ℝ} {r s : ℕ} (hrs : r ≤ s)
    (hs : walkHitTime s ω ≠ ⊤) :
    walkHitTime r ω ≠ ⊤ ∧ ladderTime ω r ≤ ladderTime ω s := by
  have hle : walkHitTime r ω ≤ walkHitTime s ω := walkHitTime_mono_level ω hrs
  have hr : walkHitTime r ω ≠ ⊤ := ne_top_of_le_ne_top hs hle
  refine ⟨hr, ?_⟩
  rw [← ENat.natCast_toNat hr, ← ENat.natCast_toNat hs] at hle
  exact_mod_cast hle

/-- Partial sums of skip-free increments are integers.
Reference: Billingsley (1999), Chapter 3. -/
private theorem exists_int_partialSum {ω : ℕ → ℝ}
    (hω : ∀ i, IsSkipFreeIncrement (ω i)) (k : ℕ) :
    ∃ z : ℤ, partialSum ω k = (z : ℝ) := by
  induction k with
  | zero => exact ⟨0, by simp [partialSum]⟩
  | succ k ih =>
    obtain ⟨z, hz⟩ := ih
    obtain ⟨a, ha⟩ := hω k
    refine ⟨z + (a : ℤ) - 1, ?_⟩
    simp only [partialSum, Finset.sum_range_succ] at hz ⊢
    rw [hz, ha]
    push_cast
    ring

/-- A finite hit of an integer barrier by a skip-free walk attains the barrier exactly.
Reference: Billingsley (1999), Chapter 3. -/
theorem partialSum_ladderTime_eq {ω : ℕ → ℝ}
    (hω : ∀ i, IsSkipFreeIncrement (ω i)) {r : ℕ} (hfin : walkHitTime r ω ≠ ⊤) :
    partialSum ω (ladderTime ω r) = -(r : ℝ) := by
  apply le_antisymm (partialSum_ladderTime_le hfin)
  generalize hq : ladderTime ω r = q
  cases q with
  | zero => simp [partialSum]
  | succ q =>
    have hprev := lt_partialSum_of_lt_ladderTime hfin
      (show q < ladderTime ω r by omega)
    obtain ⟨a, ha⟩ := exists_int_partialSum hω q
    obtain ⟨b, hb⟩ := exists_int_partialSum hω (q + 1)
    obtain ⟨c, hc⟩ := hω q
    have hsum : (b : ℝ) = (a : ℝ) + (c : ℝ) - 1 := by
      rw [← hb]
      simp only [partialSum, Finset.sum_range_succ] at ha ⊢
      rw [ha, hc]
      ring
    have hsum' : b = a + (c : ℤ) - 1 := by exact_mod_cast hsum
    have hprev' : -(r : ℤ) < a := by rw [ha] at hprev; exact_mod_cast hprev
    rw [hb]
    exact_mod_cast (show -(r : ℤ) ≤ b by omega)

/-- A positive barrier cannot be hit at time zero.
Reference: Billingsley (1999), Chapter 3. -/
private theorem ladderTime_pos {ω : ℕ → ℝ} {r : ℕ} (hr : 0 < r)
    (hfin : walkHitTime r ω ≠ ⊤) : 0 < ladderTime ω r := by
  by_contra h
  have hz : ladderTime ω r = 0 := by omega
  have hval := partialSum_ladderTime_le hfin
  rw [hz] at hval
  simp only [partialSum, Finset.sum_range_zero] at hval
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  linarith

/-- The last increment at a positive skip-free hit is `-1`; the preceding value is one higher.
Reference: Billingsley (1999), Chapter 3. -/
private theorem last_step_ladderTime {ω : ℕ → ℝ}
    (hω : ∀ i, IsSkipFreeIncrement (ω i)) {r : ℕ} (hr : 0 < r)
    (hfin : walkHitTime r ω ≠ ⊤) :
    ω (ladderTime ω r - 1) = -1 ∧
      partialSum ω (ladderTime ω r - 1) = -(r : ℝ) + 1 := by
  have hpos := ladderTime_pos hr hfin
  let q := ladderTime ω r - 1
  have hq : q + 1 = ladderTime ω r := by dsimp [q]; omega
  have hprev := lt_partialSum_of_lt_ladderTime hfin
    (show q < ladderTime ω r by omega)
  obtain ⟨a, ha⟩ := exists_int_partialSum hω q
  obtain ⟨c, hc⟩ := hω q
  have hsum : (a : ℝ) + (c : ℝ) - 1 = -(r : ℝ) := by
    have hval := partialSum_ladderTime_eq hω hfin
    rw [← hq] at hval
    simp only [partialSum, Finset.sum_range_succ] at ha hval
    rw [ha, hc] at hval
    linarith
  have hsum' : a + (c : ℤ) - 1 = -(r : ℤ) := by exact_mod_cast hsum
  have hprev' : -(r : ℤ) < a := by rw [ha] at hprev; exact_mod_cast hprev
  have hc0 : c = 0 := by omega
  have ha' : a = -(r : ℤ) + 1 := by omega
  constructor
  · simpa only [hc0, Nat.cast_zero, zero_sub] using hc
  · change partialSum ω q = _
    rw [ha, ha']
    push_cast
    rfl

/-- Consecutive finite skip-free ladder times are strictly increasing.
Reference: Billingsley (1999), Chapter 3. -/
theorem ladderTime_lt_succ {ω : ℕ → ℝ}
    (hω : ∀ i, IsSkipFreeIncrement (ω i)) {r : ℕ}
    (hfin : walkHitTime (r + 1) ω ≠ ⊤) : ladderTime ω r < ladderTime ω (r + 1) := by
  obtain ⟨hr, hle⟩ := ladderTime_mono_of_finite (Nat.le_succ r) hfin
  apply lt_of_le_of_ne hle
  intro heq
  have h1 := partialSum_ladderTime_eq hω hr
  have h2 := partialSum_ladderTime_eq hω hfin
  rw [heq] at h1
  push_cast at h2
  linarith

/-- Partial sums of the modified block stop just before the final downward step.
Reference: Billingsley (1999), Chapter 3. -/
theorem partialSum_blockIncrements (ω : ℕ → ℝ) (r i : ℕ) :
    partialSum (blockIncrements ω r) i =
      partialSum ω (ladderTime ω r + min i (ladderTime ω (r + 1) - ladderTime ω r - 1)) -
        partialSum ω (ladderTime ω r) := by
  let m := ladderTime ω (r + 1) - ladderTime ω r
  change partialSum (blockIncrements ω r) i =
    partialSum ω (ladderTime ω r + min i (m - 1)) - partialSum ω (ladderTime ω r)
  induction i with
  | zero => simp [partialSum]
  | succ i ih =>
    have hsum : partialSum (blockIncrements ω r) (i + 1) =
        partialSum (blockIncrements ω r) i + blockIncrements ω r i := by
      simp [partialSum, Finset.sum_range_succ]
    rw [hsum, ih]
    by_cases hi : i + 1 < m
    · have hi' : i ≤ m - 1 := by omega
      have hi'' : i + 1 ≤ m - 1 := by omega
      rw [Nat.min_eq_left hi', Nat.min_eq_left hi'']
      have hb : blockIncrements ω r i = ω (ladderTime ω r + i) := ite_eq_left hi
      rw [hb]
      have hsum' : partialSum ω (ladderTime ω r + (i + 1)) =
          partialSum ω (ladderTime ω r + i) + ω (ladderTime ω r + i) := by
        simp [partialSum, ← Nat.add_assoc, Finset.sum_range_succ]
      rw [hsum']
      ring
    · have hi' : m - 1 ≤ i := by omega
      have hi'' : m - 1 ≤ i + 1 := by omega
      rw [Nat.min_eq_right hi', Nat.min_eq_right hi'']
      have hb : blockIncrements ω r i = 0 := ite_eq_right hi
      rw [hb, add_zero]

/-- The extracted block is identically zero after its final step has been removed.
Reference: Billingsley (1999), Chapter 3. -/
theorem partialSum_blockIncrements_eq_zero {ω : ℕ → ℝ}
    (hω : ∀ i, IsSkipFreeIncrement (ω i)) {r : ℕ}
    (hfin : walkHitTime (r + 1) ω ≠ ⊤) {i : ℕ}
    (hi : ladderTime ω (r + 1) - ladderTime ω r - 1 ≤ i) :
    partialSum (blockIncrements ω r) i = 0 := by
  rw [partialSum_blockIncrements, Nat.min_eq_right hi]
  have hlt := ladderTime_lt_succ hω hfin
  have hidx : ladderTime ω r + (ladderTime ω (r + 1) - ladderTime ω r - 1) =
      ladderTime ω (r + 1) - 1 := by omega
  rw [hidx, (last_step_ladderTime hω (Nat.succ_pos r) hfin).2,
    partialSum_ladderTime_eq hω (ladderTime_mono_of_finite (Nat.le_succ r) hfin).1]
  push_cast
  ring

end BGW.StableTrees
