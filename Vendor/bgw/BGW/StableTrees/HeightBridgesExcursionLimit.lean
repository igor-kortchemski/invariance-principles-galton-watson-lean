/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.HeightBridgesCompact
public import BGW.StableTrees.HeightBridgesExcursionPrefix
public import BGW.StableTrees.HeightBridgesNearStartBound
public import BGW.StableTrees.HeightBridgesApproximation
public import BGW.StableTrees.HeightBridgesUnitTransfer

/-!
# Height approximation limits under the excursion and unit laws

Interior increment prefixes have absolutely continuous laws, so compact representatives
transfer H02's full-filter convergence to each interior excursion window. This and a uniform
first-moment estimate at the excursion start give the full-filter limit. Prefix absolute
continuity then transfers its existence to the unit law.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod
open BGW.Probability

namespace BGW.StableTrees

/-- Full-filter height approximation on every excursion window starting at a positive age. -/
theorem heightApprox_shift_tendstoInMeasure_excursion {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    (s r : ℝ≥0) (hs : 0 < s) :
    TendstoInMeasure
      ((excursionMeasure θ).restrict {e : Excursion | s + r < e.lifetime})
      (fun (ε : ℝ) (e : Excursion) => heightApprox ε (DLoc.shift s e.path) r)
      (𝓝[>] (0 : ℝ)) (fun e => height θ (DLoc.shift s e.path) r) := by
  let μ := (excursionMeasure θ).restrict {e : Excursion | s + r < e.lifetime}
  have : IsFiniteMeasure μ := ⟨by
    rw [Measure.restrict_apply_univ]
    exact excursionMeasure_lifetime_slab_lt_top hθ
      (hs.trans_le (le_add_of_nonneg_right (show 0 ≤ r from zero_le)))⟩
  have hp : Measurable (fun e : Excursion => DLoc.restrict r (DLoc.shift s e.path)) :=
    (DLoc.measurable_restrict r).comp
      ((DLoc.measurable_shift_fixed s).comp measurable_excursion_path)
  have hconv := tendstoInMeasure_of_absolutelyContinuous
    (excursion_shift_prefix_absolutelyContinuous hθ s r hs)
    (fun ε => measurable_horizonHeightApprox ε r) (horizonHeightApprox_tendstoInMeasure hθ r)
  have hcomp := (tendstoInMeasure_map_iff hp
    (fun ε => measurable_horizonHeightApprox ε r) (measurable_horizonHeight θ r)).mp hconv
  simpa only [horizonHeightApprox_restrict, horizonHeight_restrict] using hcomp

/-- **Approximation under `N`** on the survival event `{t < lifetime}`: convergence in `N`-measure
to some measurable limit. -/
theorem exists_heightApprox_tendstoInMeasure_excursion {θ : ℝ}
    (hθ : 1 < θ ∧ θ ≤ 2) (t : ℝ≥0) (ht : 0 < t) :
    ∃ L : Excursion → ℝ, Measurable L ∧ TendstoInMeasure
      ((excursionMeasure θ).restrict {e : Excursion | t < e.lifetime})
      (fun (ε : ℝ) (e : Excursion) => heightApprox ε e.path t) (𝓝[>] (0 : ℝ)) L := by
  let μ := (excursionMeasure θ).restrict {e : Excursion | t < e.lifetime}
  have : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr
    (excursionMeasure_lifetime_slab_lt_top hθ ht).ne
  let a : ℕ → ℝ≥0 := fun n => (t / 2) / ((n : ℝ≥0) + 1)
  have hapos (n : ℕ) : 0 < a n := by dsimp [a]; positivity
  have halft (n : ℕ) : a n ≤ t / 2 := div_le_self zero_le (by
    simpa only [zero_add] using add_le_add (show (0 : ℝ≥0) ≤ n from zero_le) (le_refl 1))
  have haa (n : ℕ) : a n + a n ≤ t := by
    calc
      _ ≤ t / 2 + t / 2 := add_le_add (halft n) (halft n)
      _ = t := add_halves t
  have hat (n : ℕ) : a n ≤ t :=
    (le_add_of_nonneg_right (show 0 ≤ a n from zero_le)).trans (haa n)
  have ha : Tendsto a atTop (𝓝 0) := by
    simpa only [a, div_eq_mul_inv, one_mul, mul_zero] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ≥0)).const_mul (t / 2)
  obtain ⟨C, _, hbound⟩ := exists_lintegral_heightApprox_sub_shift_le hθ
  let b : ℕ → ℝ≥0∞ := fun n =>
    ENNReal.ofReal (C * ((t : ℝ) / 2) ^ (-1 / θ)) *
      ∫⁻ s in Ioo (0 : ℝ) (a n : ℝ),
        excursionMeasure θ {e : Excursion | s.toNNReal < e.lifetime}
  have hb : Tendsto b atTop (𝓝 0) := by
    simpa only [b, mul_zero] using ENNReal.Tendsto.const_mul
      (tendsto_lintegral_excursion_lifetime_tail_zero hθ t a ha hat)
      (Or.inr ENNReal.ofReal_ne_top)
  let F : ℝ → Excursion → ℝ := fun ε e => heightApprox ε e.path t
  let G : ℕ → ℝ → Excursion → ℝ := fun n ε e =>
    heightApprox ε (DLoc.shift (a n) e.path) (t - a n)
  let L : ℕ → Excursion → ℝ := fun n e => height θ (DLoc.shift (a n) e.path) (t - a n)
  have hF (ε : ℝ) : Measurable (F ε) := by
    exact Measurable.comp (g := fun p : ℝ × ℝ≥0 × DLoc => heightApprox p.1 p.2.2 p.2.1)
      (f := fun e : Excursion => (ε, t, e.path)) measurable_heightApprox_uncurry
      (measurable_const.prodMk (measurable_const.prodMk measurable_excursion_path))
  have hG (n : ℕ) (ε : ℝ) : Measurable (G n ε) := by
    exact Measurable.comp (g := fun p : ℝ × ℝ≥0 × DLoc => heightApprox p.1 p.2.2 p.2.1)
      (f := fun e : Excursion => (ε, t - a n, DLoc.shift (a n) e.path))
      measurable_heightApprox_uncurry
      (measurable_const.prodMk (measurable_const.prodMk
        ((DLoc.measurable_shift_fixed (a n)).comp measurable_excursion_path)))
  have hconv (n : ℕ) : TendstoInMeasure μ (G n) (𝓝[>] (0 : ℝ)) (L n) := by
    have h := heightApprox_shift_tendstoInMeasure_excursion hθ (a n) (t - a n) (hapos n)
    rw [add_tsub_cancel_of_le (hat n)] at h
    exact h
  have herr (n : ℕ) (ε : ℝ) (hε : 0 < ε) :
      (∫⁻ e, ENNReal.ofReal (dist (F ε e) (G n ε e)) ∂μ) ≤ b n := by
    simpa only [F, G, Real.dist_eq] using hbound t (a n) ht (haa n) ε hε
  exact exists_tendstoInMeasure_of_uniform_approximation (μ := μ) F G L b hF hG hconv hb herr

/-- **Approximation under the unit law** at ages `t < 1`. -/
theorem exists_heightApprox_tendstoInMeasure_unit {θ : ℝ}
    (hθ : 1 < θ ∧ θ ≤ 2) (t : ℝ≥0) (ht0 : 0 < t) (ht1 : t < 1) :
    ∃ L : Excursion → ℝ, Measurable L ∧ TendstoInMeasure
      (unitExcursionLaw θ : Measure Excursion)
      (fun (ε : ℝ) (e : Excursion) => heightApprox ε e.path t) (𝓝[>] (0 : ℝ)) L := by
  exact exists_heightApprox_tendstoInMeasure_unit_of_excursion hθ t ht0 ht1
    (exists_heightApprox_tendstoInMeasure_excursion hθ t ht0)

end BGW.StableTrees
