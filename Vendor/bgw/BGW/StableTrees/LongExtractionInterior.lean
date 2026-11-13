/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.LongExtractionBlocks
public import BGW.StableTrees.LongExtractionClocks

/-!
# Excursion interiors contain no discrete ladder times

A positive lower bound on the reflected limit, together with a uniform aligned path bound,
excludes weak record times throughout a compact excursion interior.
-/

@[expose] public section

open Filter Topology
open scoped NNReal
open BGW.Skorokhod BGW.Probability.RealWalk

namespace BGW.StableTrees

/-- Every value up to a finite ladder time is at least the value at that time.
Reference: Billingsley (1999), Chapter 3. -/
theorem stepPath_ge_at_ladderTime {M b : ℝ} {n r : ℕ} {ω : ℕ → ℝ}
    (hb : 0 < b) (hfin : walkHitTime r ω ≠ ⊤) (s : Set.Icc (0 : ℝ) M)
    (hs : (n : ℝ) * (s : ℝ) ≤ ladderTime ω r) :
    partialSum ω (ladderTime ω r) / b ≤ realStepPath M n b ω s := by
  have hj : ⌊(n : ℝ) * (s : ℝ)⌋₊ ≤ ladderTime ω r := by
    simpa only [Nat.floor_natCast] using Nat.floor_le_floor hs
  rw [realStepPath_apply]
  apply (div_le_div_iff_of_pos_right hb).mpr
  rcases hj.eq_or_lt with hj | hj
  · rw [hj]
  · exact (partialSum_ladderTime_le hfin).trans
      (lt_partialSum_of_lt_ladderTime hfin hj).le

/-- A compact reflected-positive interval has no aligned discrete record times.
Reference: Billingsley (1999), Chapter 3. -/
theorem ladderTime_not_mem_aligned_interior {M : ℝ≥0} {f : DLoc}
    (hzero : f.1 0 = 0) {a b : ℝ≥0} (haM : a ≤ M) (hbM : b ≤ M)
    {c : ℝ} (hc : 0 < c)
    (hR : ∀ t : ℝ≥0, a ≤ t → t ≤ b → c ≤ (reflectedFrom 0 f).1 t)
    {n : ℕ} (hn : 0 < n) {B : ℝ} (hB : 0 < B) {ω : ℕ → ℝ}
    (σ : TimeChange (M : ℝ))
    (herr : ∀ t, dist (realStepPath (M : ℝ) n B ω (σ t)) ((DLoc.restrict M f) t) < c / 4)
    {r : ℕ} (hfin : walkHitTime r ω ≠ ⊤) :
    ¬ ((σ ⟨a, a.2, by exact_mod_cast haM⟩ : ℝ) ≤ (ladderTime ω r : ℝ) / n ∧
      (ladderTime ω r : ℝ) / n ≤ (σ ⟨b, b.2, by exact_mod_cast hbM⟩ : ℝ)) := by
  rintro ⟨ha, hb⟩
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  let q : Set.Icc (0 : ℝ) (M : ℝ) :=
    ⟨(ladderTime ω r : ℝ) / n, div_nonneg (Nat.cast_nonneg _) hn'.le,
      hb.trans (σ ⟨b, b.2, by exact_mod_cast hbM⟩).2.2⟩
  let z := σ.symm q
  let zNN : ℝ≥0 := ⟨(z : ℝ), z.2.1⟩
  have haz : a ≤ zNN := by
    have hle : σ ⟨a, a.2, by exact_mod_cast haM⟩ ≤ q := ha
    have hle' := σ.symm.monotone hle
    simp only [OrderIso.symm_apply_apply] at hle'
    exact hle'
  have hzb : zNN ≤ b := by
    have hle : q ≤ σ ⟨b, b.2, by exact_mod_cast hbM⟩ := hb
    have hle' := σ.symm.monotone hle
    simp only [OrderIso.symm_apply_apply] at hle'
    exact hle'
  have hreflect := hR zNN haz hzb
  rw [reflectedFrom_zero_apply hzero] at hreflect
  obtain ⟨u, huz, hu⟩ := exists_eval_lt_of_runningInfLoc_lt
    (show runningInfLoc f zNN < runningInfLoc f zNN + c / 4 by linarith)
  let u' : Set.Icc (0 : ℝ) (M : ℝ) :=
    ⟨u, u.2, by exact_mod_cast huz.trans (show zNN ≤ M from z.2.2)⟩
  have hu'z : u' ≤ z := huz
  have hσu : (σ u' : ℝ) ≤ (ladderTime ω r : ℝ) / n := by
    have h := σ.monotone hu'z
    rw [show σ z = q from σ.apply_symm_apply q] at h
    exact h
  have hbound : (n : ℝ) * (σ u' : ℝ) ≤ ladderTime ω r := by
    simpa only [mul_comm] using (le_div_iff₀ hn').mp hσu
  have hstep := stepPath_ge_at_ladderTime hB hfin (σ u') hbound
  have hgrid : realStepPath (M : ℝ) n B ω (σ z) =
      partialSum ω (ladderTime ω r) / B := by
    have hmul : (n : ℝ) * ((ladderTime ω r : ℝ) / n) = ladderTime ω r := by field_simp
    simp only [z, OrderIso.apply_symm_apply, realStepPath_apply, q, hmul,
      Nat.floor_natCast]
  have hez := herr z
  have heu := herr u'
  rw [hgrid, Real.dist_eq, abs_lt] at hez
  rw [Real.dist_eq, abs_lt] at heu
  change f.1 u < _ at hu
  change c ≤ (DLoc.restrict M f) z - runningInfLoc f zNN at hreflect
  have hueval : (DLoc.restrict M f) u' = f.1 u := rfl
  rw [hueval] at heu
  linarith [hez.1, heu.2]

end BGW.StableTrees
