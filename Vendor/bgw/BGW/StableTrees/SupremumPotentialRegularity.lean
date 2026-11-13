/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.SupremumPotentialSeries
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.Calculus.SmoothSeries

/-!
# Regularity of the stable scale series

Compact majorants justify continuity and termwise differentiation.

Reference: A. E. Kyprianou, *Fluctuations of Lévy Processes with Applications*, 2nd ed.,
Springer, 2014, Chapter 8.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace BGW.StableTrees

private theorem term_exponent_pos {θ : ℝ} (hθ : 1 < θ) (n : ℕ) :
    0 < θ * (n + 1) - 1 := by
  have : (1 : ℝ) ≤ n + 1 := by linarith [Nat.cast_nonneg (α := ℝ) n]
  nlinarith

private theorem norm_term_le {θ : ℝ} (hθ : 1 < θ) (q : ℝ) (n : ℕ) {x K : ℝ}
    (hx : 0 ≤ x) (hxK : x ≤ K) :
    ‖stableSeriesTerm θ q n x‖ ≤ stableSeriesTerm θ |q| n K := by
  have he := term_exponent_pos hθ n
  have hg : 0 < Real.Gamma (θ * (n + 1)) := Real.Gamma_pos_of_pos (by linarith)
  simp only [stableSeriesTerm, Real.norm_eq_abs, abs_div, abs_mul, abs_pow,
    abs_of_nonneg (Real.rpow_nonneg hx _), abs_of_pos hg]
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hx hxK he.le) (by positivity)) hg.le

private theorem continuousOn_series_Icc {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (q : ℝ)
    {K : ℝ} (hK : 0 ≤ K) : ContinuousOn (stableSeries θ q) (Icc 0 K) := by
  have hc : ContinuousOn (fun x => ∑' n : ℕ, stableSeriesTerm θ q n x) (Icc 0 K) := by
    refine continuousOn_tsum (fun n => ?_) (summable_stableSeriesTerm hθ |q| hK)
      (fun n x hx => norm_term_le hθ.1 q n hx.1 hx.2)
    exact (continuous_const.mul
      (Real.continuous_rpow_const (term_exponent_pos hθ.1 n).le)).div_const _ |>.continuousOn

  apply hc.congr
  intro x hx
  simp only [stableSeries, ite_eq_left hx.1]

/-- Continuity up to the singular derivative endpoint. -/
theorem continuousOn_stableSeries {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (q : ℝ) :
    ContinuousOn (stableSeries θ q) (Ici 0) := by
  intro x hx
  change 0 ≤ x at hx
  have hc := continuousOn_series_Icc hθ q (K := x + 1) (by linarith [hx])
  apply (hc x ⟨hx, by linarith⟩).mono_of_mem_nhdsWithin
  exact inter_mem self_mem_nhdsWithin
    (mem_nhdsWithin_of_mem_nhds (Iic_mem_nhds (by linarith : x < x + 1)))

private theorem deriv_term {θ : ℝ} (hθ : 1 < θ) (q : ℝ) (n : ℕ) {x : ℝ}
    (hx : 0 < x) : HasDerivAt (stableSeriesTerm θ q n) (stableSeriesDerivTerm θ q n x) x := by
  have he := term_exponent_pos hθ n
  have hd := ((Real.hasDerivAt_rpow_const (Or.inl hx.ne')
    (p := θ * (n + 1) - 1)).const_mul (q ^ n)).div_const (Real.Gamma (θ * (n + 1)))
  have hg : Real.Gamma (θ * (n + 1)) =
      (θ * (n + 1) - 1) * Real.Gamma (θ * (n + 1) - 1) := by
    simpa only [sub_add_cancel] using Real.Gamma_add_one he.ne'
  change HasDerivAt (fun y => q ^ n * y ^ (θ * (n + 1) - 1) /
    Real.Gamma (θ * (n + 1))) (stableSeriesDerivTerm θ q n x) x
  convert hd using 1
  unfold stableSeriesDerivTerm
  rw [hg]
  have hp : θ * (n + 1) - 1 - 1 = θ * (n + 1) - 2 := by ring
  rw [hp]
  field_simp [he.ne']

private theorem norm_derivTerm_le {θ : ℝ} (hθ : 1 < θ) (q : ℝ) (n : ℕ) {a x b : ℝ}
    (ha : 0 < a) (hax : a ≤ x) (hxb : x ≤ b) :
    ‖stableSeriesDerivTerm θ q n x‖ ≤
      stableSeriesDerivTerm θ |q| n a + stableSeriesDerivTerm θ |q| n b := by
  have hx : 0 ≤ x := (ha.trans_le hax).le
  have hb : 0 ≤ b := hx.trans hxb
  have he := term_exponent_pos hθ n
  have hg : 0 < Real.Gamma (θ * (n + 1) - 1) := Real.Gamma_pos_of_pos he
  have hp : x ^ (θ * (n + 1) - 2) ≤
      a ^ (θ * (n + 1) - 2) + b ^ (θ * (n + 1) - 2) := by
    by_cases h : 0 ≤ θ * (n + 1) - 2
    · exact (Real.rpow_le_rpow hx hxb h).trans
        (le_add_of_nonneg_left (Real.rpow_nonneg ha.le _))
    · exact (Real.rpow_le_rpow_of_nonpos ha hax (not_le.mp h).le).trans
        (le_add_of_nonneg_right (Real.rpow_nonneg hb _))
  simp only [stableSeriesDerivTerm, Real.norm_eq_abs, abs_div, abs_mul, abs_pow,
    abs_of_nonneg (Real.rpow_nonneg hx _), abs_of_pos hg]
  calc
    _ ≤ |q| ^ n * (a ^ (θ * (n + 1) - 2) + b ^ (θ * (n + 1) - 2)) /
        Real.Gamma (θ * (n + 1) - 1) := by gcongr
    _ = _ := by ring

/-- Termwise differentiation on `(0,∞)`. -/
theorem hasDerivAt_stableSeries {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (q : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (stableSeries θ q) (stableSeriesDeriv θ q x) x := by
  have ha : 0 < x / 2 := by linarith
  have hb : 0 < x + 1 := by linarith
  have hu := (summable_stableSeriesDerivTerm hθ |q| ha).add
    (summable_stableSeriesDerivTerm hθ |q| hb)
  have ht : x ∈ Ioo (x / 2) (x + 1) := ⟨by linarith, by linarith⟩
  have hd := hasDerivAt_tsum_of_isPreconnected hu isOpen_Ioo (convex_Ioo _ _).isPreconnected
    (fun n y hy => deriv_term hθ.1 q n (ha.trans hy.1))
    (fun n y hy => norm_derivTerm_le hθ.1 q n ha hy.1.le hy.2.le)
    ht (summable_stableSeriesTerm hθ q hx.le) ht
  rw [stableSeriesDeriv, ite_eq_left hx]
  apply hd.congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds hx] with y hy
  simp only [stableSeries, ite_eq_left hy.le]

/-- The derivative series is continuous away from its singular endpoint. -/
theorem continuousOn_stableSeriesDeriv {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (q : ℝ) :
    ContinuousOn (stableSeriesDeriv θ q) (Ioi 0) := by
  intro x hx
  change 0 < x at hx
  have ha : 0 < x / 2 := by linarith
  have hb : 0 < x + 1 := by linarith
  have hu := (summable_stableSeriesDerivTerm hθ |q| ha).add
    (summable_stableSeriesDerivTerm hθ |q| hb)
  have hc : ContinuousOn (fun y => ∑' n : ℕ, stableSeriesDerivTerm θ q n y)
      (Icc (x / 2) (x + 1)) := by
    refine continuousOn_tsum (fun n => ?_) hu (fun n y hy =>
      norm_derivTerm_le hθ.1 q n ha hy.1 hy.2)
    have hp : ContinuousOn (fun y : ℝ => y ^ (θ * (n + 1) - 2))
        (Icc (x / 2) (x + 1)) :=
      continuousOn_id.rpow_const (fun y hy => Or.inl (ne_of_gt (ha.trans_le hy.1)))
    exact (continuousOn_const.mul hp).div_const _

  have hc' : ContinuousOn (stableSeriesDeriv θ q) (Icc (x / 2) (x + 1)) := by
    apply hc.congr
    intro y hy
    simp only [stableSeriesDeriv, ite_eq_left (ha.trans_le hy.1)]
  exact (hc'.continuousAt (Icc_mem_nhds (by linarith) (by linarith))).continuousWithinAt

/-- The scale series is continuous on the whole real line, with its zero extension. -/
theorem continuous_stableSeries {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (q : ℝ) :
    Continuous (stableSeries θ q) := by
  have hc : Continuous (fun x : ℝ => stableSeries θ q (max x 0)) :=
    (continuousOn_stableSeries hθ q).comp_continuous (continuous_id.max continuous_const)
      (fun _ => le_max_right _ _)
  apply hc.congr
  intro x
  by_cases hx : 0 ≤ x
  · rw [max_eq_left hx]
  · rw [max_eq_right (not_le.mp hx).le, stableSeries_zero hθ q]
    simp [stableSeries, hx]

end BGW.StableTrees
