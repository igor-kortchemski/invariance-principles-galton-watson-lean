/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.LongExtractionStoppedCut
public import BGW.StableTrees.LongExtractionBlocks

/-!
# Adapters between finite stopped cuts and excursion blocks

The continuum cut agrees with the sealed local cut. Removing the last discrete step changes
its stopped cut by at most one spatial mesh.
-/

@[expose] public section

open Set Filter Topology
open scoped NNReal
open BGW.Skorokhod BGW.Probability.RealWalk

namespace BGW.StableTrees

/-- The sealed local cut evaluates by clipping the translated time at its right endpoint.
Reference: Billingsley (1999), Chapter 3. -/
theorem cutPath_min_apply {g d : ℝ≥0} (hgd : g ≤ d) (f : DLoc) (t : ℝ≥0) :
    (cutPath g d f).1 t = f.1 (min (g + t) d) - f.1 g := by
  change f.1 (g + min t (d - g)) - f.1 g = _
  rw [add_min, add_tsub_cancel_of_le hgd]

/-- Finite stopped cuts of a local restriction agree with the sealed local cut.
Reference: Billingsley (1999), Chapter 3. -/
theorem translatedStoppedCut_restrict {M T g d : ℝ≥0} (f : DLoc)
    (hgd : g ≤ d) (hdM : d ≤ M) :
    translatedStoppedCut T (DLoc.restrict M f)
      ⟨g, g.2, by exact_mod_cast hgd.trans hdM⟩
      ⟨d, d.2, by exact_mod_cast hdM⟩ (by exact_mod_cast hgd) =
        DLoc.restrict T (cutPath g d f) := by
  ext t
  rw [translatedStoppedCut_apply]
  change f.1 ⟨min ((g : ℝ) + (t : ℝ)) d, _⟩ - f.1 g =
    (cutPath g d f).1 ⟨(t : ℝ), t.2.1⟩
  exact (cutPath_min_apply hgd f ⟨(t : ℝ), t.2.1⟩).symm

/-- Floor commutes with `min`.
Reference: Billingsley (1999), Chapter 3. -/
private theorem floor_min_real (x y : ℝ) : ⌊min x y⌋₊ = min ⌊x⌋₊ ⌊y⌋₊ := by
  rcases le_total x y with h | h
  · rw [min_eq_left h, min_eq_left (Nat.floor_le_floor h)]
  · rw [min_eq_right h, min_eq_right (Nat.floor_le_floor h)]

/-- Removing the last skip-free step changes the finite stopped cut by at most `1/B`.
Reference: Billingsley (1999), Chapter 3. -/
theorem dist_blockIncrements_translatedStoppedCut_le {M : ℝ} (T : ℝ≥0)
    {ω : ℕ → ℝ} (hω : ∀ i, IsSkipFreeIncrement (ω i)) {r n : ℕ}
    (hfin : walkHitTime (r + 1) ω ≠ ⊤) (hn : 0 < n) {B : ℝ} (hB : 0 < B)
    (g d : Icc (0 : ℝ) M) (hgd : g ≤ d)
    (hg : (g : ℝ) = (ladderTime ω r : ℝ) / n)
    (hd : (d : ℝ) = (ladderTime ω (r + 1) : ℝ) / n) :
    dist (realStepPath (T : ℝ) n B (blockIncrements ω r))
      (translatedStoppedCut T (realStepPath M n B ω) g d hgd) ≤ 1 / B := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hlt := ladderTime_lt_succ hω hfin
  let m := ladderTime ω (r + 1) - ladderTime ω r
  have hm : 0 < m := Nat.sub_pos_of_lt hlt
  have hsum : ladderTime ω r + m = ladderTime ω (r + 1) := Nat.add_sub_of_le hlt.le
  have hnum (i : ℕ) : |partialSum (blockIncrements ω r) i -
      (partialSum ω (ladderTime ω r + min i m) - partialSum ω (ladderTime ω r))| ≤ 1 := by
    by_cases hi : i < m
    · rw [partialSum_blockIncrements, Nat.min_eq_left (by omega : i ≤ m - 1),
        Nat.min_eq_left hi.le, sub_self, abs_zero]
      norm_num
    · rw [partialSum_blockIncrements_eq_zero hω hfin (by dsimp only [m] at hi ⊢; omega),
        Nat.min_eq_right (le_of_not_gt hi), hsum,
        partialSum_ladderTime_eq hω hfin,
        partialSum_ladderTime_eq hω (ladderTime_mono_of_finite (Nat.le_succ r) hfin).1]
      push_cast
      norm_num
  have : Nonempty (Icc (0 : ℝ) (T : ℝ)) := ⟨⟨0, le_rfl, T.2⟩⟩
  apply (dist_le_iSup_dist _ _).trans
  apply ciSup_le
  intro t
  let i := ⌊(n : ℝ) * (t : ℝ)⌋₊
  have hng : (n : ℝ) * (g : ℝ) = ladderTime ω r := by rw [hg]; field_simp
  have hnd : (n : ℝ) * (d : ℝ) = ladderTime ω (r + 1) := by rw [hd]; field_simp
  have hidx : ⌊(n : ℝ) * min ((g : ℝ) + (t : ℝ)) d⌋₊ = ladderTime ω r + min i m := by
    rw [mul_min_of_nonneg _ _ hn'.le, mul_add, hng, hnd, floor_min_real,
      Nat.floor_natCast]
    have hfloor : ⌊(ladderTime ω r : ℝ) + (n : ℝ) * (t : ℝ)⌋₊ = ladderTime ω r + i := by
      rw [add_comm (ladderTime ω r : ℝ), Nat.floor_add_natCast
        (mul_nonneg hn'.le t.2.1)]
      exact Nat.add_comm _ _
    rw [hfloor, ← hsum, min_add_add_left]
  rw [translatedStoppedCut_apply, realStepPath_apply, realStepPath_apply,
    realStepPath_apply, hidx, hng, Nat.floor_natCast, Real.dist_eq]
  have heq : partialSum (blockIncrements ω r) i / B -
      (partialSum ω (ladderTime ω r + min i m) / B - partialSum ω (ladderTime ω r) / B) =
      (partialSum (blockIncrements ω r) i -
        (partialSum ω (ladderTime ω r + min i m) - partialSum ω (ladderTime ω r))) / B := by
    ring
  change |partialSum (blockIncrements ω r) i / B -
    (partialSum ω (ladderTime ω r + min i m) / B - partialSum ω (ladderTime ω r) / B)| ≤ _
  rw [heq, abs_div, abs_of_pos hB]
  exact (div_le_div_iff_of_pos_right hB).mpr (hnum i)

end BGW.StableTrees
