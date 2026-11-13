/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.StableLocalLaw

/-!
# Fine-grid increments of continuous càdlàg paths

Uniform continuity on a compact interval controls all sufficiently fine regular grids.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees

/-- **Deterministic**: a càdlàg path with no jump in `(a, b]` has uniformly small increments on
fine regular grids of `[a, b]`. -/
theorem eventually_grid_increments_le {f : DLoc} {a b : ℝ≥0} (hab : a < b)
    (hf : ∀ s ∈ Set.Ioc a b, Function.leftLim f.1 s = f.1 s) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop, ∀ k < n,
      f.1 (a + ((k : ℝ≥0) + 1) * ((b - a) / (n : ℝ≥0))) -
        f.1 (a + (k : ℝ≥0) * ((b - a) / (n : ℝ≥0))) ≤ δ := by
  have hcont : ContinuousOn f.1 (Set.Icc a b) := by
    intro t ht
    by_cases hta : t = a
    · subst t
      have hr : ContinuousWithinAt f.1 (Set.Ici a) a :=
        continuousWithinAt_Ioi_iff_Ici.mp (f.2.isRightContinuous a)
      exact hr.mono (fun _ hx => hx.1)
    · have hat : a < t := lt_of_le_of_ne ht.1 (Ne.symm hta)
      have hleft : ContinuousWithinAt f.1 (Set.Iio t) t := by
        change Tendsto f.1 (𝓝[<] t) (𝓝 (f.1 t))
        rw [← hf t ⟨hat, ht.2⟩]
        exact f.2.tendsto_nhdsLT_leftLim t
      exact (continuousAt_iff_continuous_left'_right'.mpr
        ⟨hleft, f.2.isRightContinuous t⟩).continuousWithinAt
  obtain ⟨η, hη, hηf⟩ := Metric.uniformContinuousOn_iff.mp
    (isCompact_Icc.uniformContinuousOn_of_continuous hcont) δ hδ
  have hmesh : Tendsto (fun n : ℕ => ((b - a : ℝ≥0) : ℝ) / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat _
  filter_upwards [eventually_gt_atTop 0, (tendsto_order.1 hmesh).2 η hη] with n hn hmeshn
  intro k hk
  let q : ℝ≥0 := (b - a) / (n : ℝ≥0)
  let u : ℝ≥0 := a + (k : ℝ≥0) * q
  let v : ℝ≥0 := a + ((k : ℝ≥0) + 1) * q
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hk1 : (k : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hk
  have hvUpper : v ≤ b := by
    change (v : ℝ) ≤ (b : ℝ)
    have hfrac : (((k : ℝ≥0) + 1 : ℝ≥0) : ℝ) * (q : ℝ) ≤ ((b - a : ℝ≥0) : ℝ) := by
      change ((k : ℝ) + 1) * (((b - a : ℝ≥0) : ℝ) / (n : ℝ)) ≤ ((b - a : ℝ≥0) : ℝ)
      rw [← mul_div_assoc, div_le_iff₀ hnR]
      nlinarith [mul_le_mul_of_nonneg_right hk1
        (show (0 : ℝ) ≤ ((b - a : ℝ≥0) : ℝ) by positivity)]
    change (a : ℝ) + (((k : ℝ≥0) + 1 : ℝ≥0) : ℝ) * (q : ℝ) ≤ (b : ℝ)
    rw [NNReal.coe_sub hab.le] at hfrac
    linarith
  have huv : u ≤ v := by
    change a + (k : ℝ≥0) * q ≤ a + ((k : ℝ≥0) + 1) * q
    simpa [add_comm] using
      (add_le_add_left (mul_le_mul_of_nonneg_right
        (le_add_of_nonneg_right zero_le_one) (by positivity)) a)
  have huMem : u ∈ Set.Icc a b := by
    constructor
    · exact le_add_of_nonneg_right (mul_nonneg (by positivity) (by positivity))
    · exact huv.trans hvUpper
  have hvMem : v ∈ Set.Icc a b := ⟨le_add_of_nonneg_right (by positivity), hvUpper⟩
  have hdist : dist v u = ((b - a : ℝ≥0) : ℝ) / (n : ℝ) := by
    rw [NNReal.dist_eq]
    have heq : (v : ℝ) - (u : ℝ) = ((b - a : ℝ≥0) : ℝ) / (n : ℝ) := by
      change (a : ℝ) + (((k : ℝ≥0) + 1 : ℝ≥0) : ℝ) * (q : ℝ) -
        ((a : ℝ) + (k : ℝ) * (q : ℝ)) = _
      dsimp [q]
      push_cast
      ring
    rw [heq, abs_of_nonneg (by positivity)]
  have hclose : dist (f.1 v) (f.1 u) < δ := by
    apply hηf v hvMem u huMem
    rw [hdist]
    exact hmeshn
  change f.1 v - f.1 u ≤ δ
  exact (le_abs_self _).trans (by simpa [Real.dist_eq] using hclose.le)

end BGW.StableTrees
