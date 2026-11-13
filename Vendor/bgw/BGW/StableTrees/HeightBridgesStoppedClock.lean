/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.HeightBridgesErasedBound

/-!
# Passage-stopped reversed clocks

Rational times approaching strict passage from above identify the stopped bound. The
clock is continuous on the reversed prefix; no continuity of height is used.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees

/-- Rational nonnegative times approach any age from above inside a larger horizon. -/
theorem exists_rational_times_above_tendsto {a b : ℝ≥0} (hab : a < b) :
    ∃ q : ℕ → ℚ, (∀ n, a < (q n : ℝ).toNNReal ∧ (q n : ℝ).toNNReal < b) ∧
      Tendsto (fun n => (q n : ℝ).toNNReal) atTop (𝓝 a) := by
  have hgap (n : ℕ) : (a : ℝ) < min (b : ℝ) (a + 1 / (n + 1 : ℝ)) := by
    exact lt_min hab (lt_add_of_pos_right _ (by positivity))
  choose q hqa hqb using fun n => exists_rat_btwn (hgap n)
  have hpos (n : ℕ) : 0 ≤ (q n : ℝ) := a.2.trans (hqa n).le
  have hbounds (n : ℕ) : a < (q n : ℝ).toNNReal ∧ (q n : ℝ).toNNReal < b := by
    rw [← NNReal.coe_lt_coe, ← NNReal.coe_lt_coe, Real.coe_toNNReal _ (hpos n)]
    exact ⟨hqa n, (hqb n).trans_le (min_le_left _ _)⟩
  refine ⟨q, hbounds, ?_⟩
  apply NNReal.tendsto_coe.mp
  have ht : Tendsto (fun n : ℕ => (a : ℝ) + 1 / (n + 1 : ℝ)) atTop (𝓝 (a : ℝ)) := by
    simpa using (tendsto_const_nhds (x := (a : ℝ))).add
      tendsto_one_div_add_atTop_nhds_zero_nat
  apply tendsto_const_nhds.squeeze ht
  · intro n
    dsimp only
    rw [Real.coe_toNNReal _ (hpos n)]
    exact (hqa n).le
  · intro n
    dsimp only
    rw [Real.coe_toNNReal _ (hpos n)]
    exact ((hqb n).trans_le (min_le_right _ _)).le

/-- The reversed supremum exceeds the barrier at every time strictly after strict passage. -/
theorem barrier_lt_supRunning_of_passage_lt (g : DLoc) {m : ℝ} {u : ℝ≥0}
    (hu : (DLoc.strictPassageAbove m g : ℝ≥0∞) < (u : ℝ≥0∞)) : m < supRunning g u := by
  change DLoc.strictPassageAbove m g < (u : WithTop ℝ≥0) at hu
  obtain ⟨q, _hq0, hqu, hq⟩ := (DLoc.strictPassageAbove_lt_iff m g u).mp hu
  have hqt : (q : ℝ).toNNReal ≤ u := Real.toNNReal_le_iff_le_coe.mpr hqu.le
  exact hq.trans_le (eval_le_supRunning g hqt)

/-- The erased height is bounded by the reversed supremum clock stopped at strict passage. -/
theorem ae_erased_height_le_stopped_clock {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    {t : ℝ≥0} (ht : 0 < t) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∀ m : ℝ≥0,
      height θ f t - (topHeight (eraseMass m (exploration θ f t)) : ℝ) ≤
        supLocalTime θ (reversedAt t f)
          (ENNReal.toNNReal
            (min (DLoc.strictPassageAbove (m : ℝ) (reversedAt t f)) (t : ℝ≥0∞))) := by
  filter_upwards [ae_erased_height_le_clock_rational hθ ht,
    ae_reversed_clock_prefix hθ ht] with f hb hg
  intro m
  let g := reversedAt t f
  let τ : ℝ≥0∞ := DLoc.strictPassageAbove (m : ℝ) g
  by_cases hτ : τ < (t : ℝ≥0∞)
  · have hτfin : τ ≠ ⊤ := ne_top_of_lt hτ
    have hτt : τ.toNNReal < t := by
      simpa using (ENNReal.toNNReal_lt_toNNReal hτfin ENNReal.coe_ne_top).mpr hτ
    obtain ⟨q, hq, hqt⟩ := exists_rational_times_above_tendsto hτt
    have hqclock (n : ℕ) :
        height θ f t - (topHeight (eraseMass m (exploration θ f t)) : ℝ) ≤
          supLocalTime θ g (q n : ℝ).toNNReal := by
      apply hb (q n) (hq n).2.le
      rw [ENNReal.coe_lt_ofReal]
      apply barrier_lt_supRunning_of_passage_lt g
      change τ < _
      exact (ENNReal.toNNReal_lt_toNNReal hτfin ENNReal.coe_ne_top).mp
        (by simpa using (hq n).1)
    have hcg : Continuous (fun u : Iic t => supLocalTime θ g u) := hg.2.1
    have hqsub : Tendsto (fun n => (⟨(q n : ℝ).toNNReal, (hq n).2.le⟩ : Iic t))
        atTop (𝓝 ⟨τ.toNNReal, hτt.le⟩) := tendsto_subtype_rng.mpr hqt
    have hc : Tendsto (fun n => supLocalTime θ g (q n : ℝ).toNNReal) atTop
        (𝓝 (supLocalTime θ g τ.toNNReal)) :=
      Tendsto.comp (g := fun u : Iic t => supLocalTime θ g u)
        (f := fun n : ℕ => (⟨(q n : ℝ).toNNReal, (hq n).2.le⟩ : Iic t))
        (hcg.tendsto ⟨τ.toNNReal, hτt.le⟩) hqsub
    change _ ≤ supLocalTime θ g (min τ (t : ℝ≥0∞)).toNNReal
    rw [min_eq_left hτ.le]
    exact ge_of_tendsto hc (Eventually.of_forall hqclock)
  · change _ ≤ supLocalTime θ g (min τ (t : ℝ≥0∞)).toNNReal
    rw [min_eq_right (not_lt.mp hτ), ENNReal.toNNReal_coe]
    exact sub_le_self _ (NNReal.coe_nonneg _)

end BGW.StableTrees
