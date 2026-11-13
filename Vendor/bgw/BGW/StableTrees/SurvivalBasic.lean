/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.Defs
public import BGW.LocallyFinite.Normalization
public import BGW.StableTrees.Scalar.Normalization
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.MeasureTheory.Measure.Real

/-!
# Basic survival facts for critical BGW trees

This module defines the survival probability and expresses it through the offspring generating
function. It also records the vanishing of survival in the critical case and the growth of the
stable norming sequence.
-/

@[expose] public section

open MeasureTheory Filter
open scoped Topology ENNReal

namespace BGW.StableTrees.Survival

/-- The real offspring generating function `g(s) = ∑ μ(k) s^k`.  It is used on `[0,1]`, where
the series converges. -/
noncomputable def realGF (μ : PMF ℕ) (s : ℝ) : ℝ := ∑' k : ℕ, (μ k).toReal * s ^ k

/-- Survival to generation `k`: the BGW tree has a vertex at depth `≥ k`, i.e. generation `k`
is nonempty.  `survivalProb μ 0 = 1`. -/
noncomputable def survivalProb (μ : PMF ℕ) (k : ℕ) : ℝ :=
  (BGW.LocallyFinite.bienaymeLaw μ.toMeasure).real (BGW.LocallyFinite.extinctBy k)ᶜ

/-- The survival function `v(δ) = ((θ-1) δ)^(-1/(θ-1))` of the continuous-state branching
process with branching mechanism `λ^θ` (solution of `v' = -v^θ` with `v(0+) = ∞`). -/
noncomputable def csbpSurvival (θ δ : ℝ) : ℝ := ((θ - 1) * δ) ^ (-1 / (θ - 1))

private theorem realGF_eq_toReal_offspringGF (μ : PMF ℕ) {s : ℝ} (hs : 0 ≤ s) :
    realGF μ s = (BGW.offspringGF μ.toMeasure (ENNReal.ofReal s)).toReal := by
  rw [BGW.offspringGF, ENNReal.tsum_toReal_eq]
  · apply tsum_congr
    intro k
    rw [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal hs]
    rw [PMF.toMeasure_apply_singleton μ k (measurableSet_singleton k)]
  · intro k
    exact ENNReal.mul_ne_top (measure_ne_top _ _) (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)

/-- Survival in terms of the iterated generating function. -/
theorem survivalProb_eq_one_sub_iterate (μ : PMF ℕ) (k : ℕ) :
    survivalProb μ k = 1 - ((BGW.offspringGF μ.toMeasure)^[k] 0).toReal := by
  rw [survivalProb, probReal_compl_eq_one_sub
    (BGW.LocallyFinite.measurableSet_extinctBy k)]
  change 1 - ((BGW.LocallyFinite.bienaymeLaw μ.toMeasure)
    (BGW.LocallyFinite.extinctBy k)).toReal = _
  rw [BGW.LocallyFinite.bienaymeLaw_extinctBy]

theorem survivalProb_zero (μ : PMF ℕ) : survivalProb μ 0 = 1 := by
  rw [survivalProb_eq_one_sub_iterate]
  simp

private theorem iterate_offspringGF_le_one (μ : PMF ℕ) (k : ℕ) :
    (BGW.offspringGF μ.toMeasure)^[k] 0 ≤ 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact (BGW.offspringGF_mono _ ih).trans_eq (BGW.offspringGF_one _)

/-- The survival recursion `s(k+1) = 1 - g(1 - s(k))`. -/
theorem survivalProb_succ (μ : PMF ℕ) (k : ℕ) :
    survivalProb μ (k + 1) = 1 - realGF μ (1 - survivalProb μ k) := by
  rw [survivalProb_eq_one_sub_iterate μ (k + 1), survivalProb_eq_one_sub_iterate μ k,
    Function.iterate_succ_apply', sub_sub_cancel,
    realGF_eq_toReal_offspringGF μ ENNReal.toReal_nonneg]
  have hq : (BGW.offspringGF μ.toMeasure)^[k] 0 ≤ 1 := iterate_offspringGF_le_one μ k
  have hqtop : (BGW.offspringGF μ.toMeasure)^[k] 0 ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top hq
  rw [ENNReal.ofReal_toReal hqtop]

theorem survivalProb_mem_Icc (μ : PMF ℕ) (k : ℕ) : survivalProb μ k ∈ Set.Icc (0 : ℝ) 1 := by
  exact ⟨measureReal_nonneg, measureReal_le_one⟩

theorem antitone_survivalProb (μ : PMF ℕ) : Antitone (survivalProb μ) := by
  intro m n hmn
  exact measureReal_mono (Set.compl_subset_compl.mpr (BGW.LocallyFinite.monotone_extinctBy hmn))

/-- Critical non-degenerate trees are almost surely finite. -/
theorem tendsto_survivalProb_zero {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1) :
    Tendsto (survivalProb μ) atTop (𝓝 0) := by
  have hcrit : ∫⁻ k : ℕ, (k : ℝ≥0∞) ∂μ.toMeasure ≤ 1 := by
    rw [lintegral_countable']
    simpa only [PMF.toMeasure_apply_singleton μ _ (measurableSet_singleton _)] using hc.le
  have hne' : μ.toMeasure {1} ≠ 1 := by
    simpa only [PMF.toMeasure_apply_singleton μ 1 (measurableSet_singleton 1)] using hne
  have hfin := BGW.LocallyFinite.bienaymeLaw_finiteVertices_eq_one μ.toMeasure hcrit hne'
  have ht := BGW.LocallyFinite.tendsto_iterate_offspringGF μ.toMeasure
  rw [hfin] at ht
  have hr := (ENNReal.tendsto_toReal (by simp)).comp ht
  simp only [ENNReal.toReal_one] at hr
  have hsub : Tendsto (fun n : ℕ => 1 -
      ((BGW.offspringGF μ.toMeasure)^[n] 0).toReal) atTop (𝓝 (1 - 1)) :=
    tendsto_const_nhds.sub hr
  convert hsub using 1
  · ext n
    exact survivalProb_eq_one_sub_iterate μ n
  · simp

/-- `B_n / n → 0` (regular variation of index `1/θ < 1`). -/
theorem tendsto_B_div_n {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ} (h : StableDomain μ θ B) :
    Tendsto (fun n : ℕ => B n / n) atTop (𝓝 0) := by
  have hθ : 0 < θ := by linarith [h.alpha_mem.1]
  exact (Scalar.regularlyVaryingSeq h).tendsto_div_self h.monotone h.pos
    (one_div_pos.mpr hθ).le ((div_lt_one hθ).mpr h.alpha_mem.1)

/-- `B_n → ∞`. -/
theorem tendsto_B_atTop {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ} (h : StableDomain μ θ B) :
    Tendsto B atTop atTop := by
  exact Scalar.tendsto_atTop h

end BGW.StableTrees.Survival
