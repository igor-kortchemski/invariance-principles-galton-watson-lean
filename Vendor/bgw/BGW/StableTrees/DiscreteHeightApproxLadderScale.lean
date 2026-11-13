/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.DiscreteHeightApproxStoppedError
import BGW.StableTrees.SurvivalBasic

/-!
# The weak ladder-height Laplace scale

At parameter `1/B_n`, the first-height transform has defect asymptotic to `B_n/n`.
This gives an exponential tail for the number of weak epochs below a bounded height.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal Classical
open BGW.StableTrees.DiscreteForest

namespace BGW.StableTrees.DiscreteHeightApprox

/-- The weak ladder transform has its critical stable normalization, with constant one. -/
theorem tendsto_scaled_ladderPGF_defect {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ}
    (h : StableDomain μ θ B) :
    Tendsto (fun n : ℕ => ((n : ℝ) / B n) *
      (1 - (weakLadderPGF μ (ENNReal.ofReal (Real.exp (-1 / B n)))).toReal))
      atTop (𝓝 1) := by
  have hnum := norming_offspringPGF_gap h (show (0 : ℝ) < 1 by norm_num)
  have hden := tendsto_norming_one_sub_exp (Survival.tendsto_B_atTop h)
    (show (0 : ℝ) < 1 by norm_num)
  simp only [Real.one_rpow] at hnum
  have ht := hnum.div hden (by norm_num : (1 : ℝ) ≠ 0)
  rw [div_self (by norm_num : (1 : ℝ) ≠ 0)] at ht
  apply ht.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hB := h.pos n hn
  have hs : Real.exp (-1 / B n) < 1 := Real.exp_lt_one_iff.mpr (div_neg_of_neg_of_pos
    (by norm_num) hB)
  simp only [Pi.div_apply]
  rw [one_sub_weakLadderPGF μ h.critical h.nondegenerate (Real.exp_nonneg _) hs]
  field_simp

/-- Exponential Markov bounds the mass of attained epoch heights below a fixed real level. -/
theorem measure_epochHeight_le (μ : PMF ℕ) (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (N : ℕ) {b : ℝ} (hb : 0 < b) (K : ℝ) :
    (offspringSeqLaw μ).toMeasure {ω | (weakEpochHeight ω N : ℝ) ≤ K * b} ≤
      ENNReal.ofReal (Real.exp K) *
        (weakLadderPGF μ (ENNReal.ofReal (Real.exp (-1 / b)))) ^ N := by
  let s := ENNReal.ofReal (Real.exp (-1 / b))
  calc
    _ = ∫⁻ ω, {ξ | (weakEpochHeight ξ N : ℝ) ≤ K * b}.indicator
        (fun _ => (1 : ℝ≥0∞)) ω ∂(offspringSeqLaw μ).toMeasure :=
      (lintegral_indicator_fun_one (measurableSet_le
        ((measurable_of_countable (fun h : ℕ => (h : ℝ))).comp
          (measurable_weakEpochHeight N)) measurable_const)).symm
    _ ≤ ∫⁻ ω, ENNReal.ofReal (Real.exp K) * s ^ weakEpochHeight ω N
        ∂(offspringSeqLaw μ).toMeasure := by
      apply lintegral_mono
      intro ω
      by_cases hh : (weakEpochHeight ω N : ℝ) ≤ K * b
      · rw [Set.indicator_of_mem (show ω ∈ {ξ | (weakEpochHeight ξ N : ℝ) ≤ K * b} from hh)]
        have he : (1 : ℝ) ≤ Real.exp K * Real.exp (-1 / b) ^ weakEpochHeight ω N := by
          rw [← Real.exp_nat_mul, ← Real.exp_add]
          apply Real.one_le_exp_iff.mpr
          have hh' := (div_le_iff₀ hb).mpr hh
          rw [show K + (weakEpochHeight ω N : ℝ) * (-1 / b) =
            K - (weakEpochHeight ω N : ℝ) / b by ring]
          linarith
        simpa only [s, ENNReal.ofReal_one, ENNReal.ofReal_mul (Real.exp_nonneg _),
          ENNReal.ofReal_pow (Real.exp_nonneg _)] using ENNReal.ofReal_le_ofReal he
      · rw [Set.indicator_of_notMem
          (show ω ∉ {ξ | (weakEpochHeight ξ N : ℝ) ≤ K * b} from hh)]
        exact bot_le
    _ = _ := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        lintegral_epochHeight_pow μ hc hne s N]

/-- At `x*n/B_n` weak epochs, a bounded attained height has an exponentially small tail in `x`. -/
theorem eventual_epochHeight_bound {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ}
    (h : StableDomain μ θ B) {x : ℝ} (hx : 0 < x) (K : ℝ) :
    ∀ᶠ n : ℕ in atTop,
      (offspringSeqLaw μ).toMeasure
        {ω | (weakEpochHeight ω ⌈x * (n : ℝ) / B n⌉₊ : ℝ) ≤ K * B n} ≤
          ENNReal.ofReal (Real.exp (K - x / 2)) := by
  have hhalf := (tendsto_scaled_ladderPGF_defect h).eventually
    (lt_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1))
  filter_upwards [eventually_ge_atTop 1, hhalf] with n hn hh
  have hB := h.pos n hn
  let p := (weakLadderPGF μ (ENNReal.ofReal (Real.exp (-1 / B n)))).toReal
  let N := ⌈x * (n : ℝ) / B n⌉₊
  have hs : Real.exp (-1 / B n) ≤ 1 := Real.exp_le_one_iff.mpr
    (div_nonpos_of_nonpos_of_nonneg (by norm_num) hB.le)
  have hφ := weakLadderPGF_le_one μ (ENNReal.ofReal_le_one.mpr hs)
  have hp : 0 ≤ p := ENNReal.toReal_nonneg
  have hp1 : p ≤ 1 := by
    exact (ENNReal.toReal_mono ENNReal.one_ne_top hφ).trans_eq ENNReal.toReal_one
  have hexp : p ≤ Real.exp (-(1 - p)) := by
    have he := Real.add_one_le_exp (p - 1)
    rw [show p - 1 = -(1 - p) by ring] at he
    linarith
  have hpow : p ^ N ≤ Real.exp (-(x / 2)) := by
    calc
      _ ≤ (Real.exp (-(1 - p))) ^ N := pow_le_pow_left₀ hp hexp N
      _ = Real.exp (-((N : ℝ) * (1 - p))) := by rw [← Real.exp_nat_mul]; congr 1; ring
      _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        have hN := mul_le_mul_of_nonneg_right (Nat.le_ceil (x * (n : ℝ) / B n))
          (sub_nonneg.mpr hp1)
        change (1 / 2 : ℝ) < ((n : ℝ) / B n) * (1 - p) at hh
        have hmul := mul_lt_mul_of_pos_left hh hx
        rw [show x * ((n : ℝ) / B n * (1 - p)) =
          x * (n : ℝ) / B n * (1 - p) by ring] at hmul
        dsimp only [N]
        linarith only [hN, hmul]
  have hfin : weakLadderPGF μ (ENNReal.ofReal (Real.exp (-1 / B n))) ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top hφ
  have hb := measure_epochHeight_le μ h.critical h.nondegenerate N hB K
  rw [← ENNReal.ofReal_toReal hfin] at hb
  refine hb.trans ?_
  rw [← ENNReal.ofReal_pow hp, ← ENNReal.ofReal_mul (Real.exp_nonneg _)]
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ Real.exp K * Real.exp (-(x / 2)) :=
      mul_le_mul_of_nonneg_left hpow (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add]; rfl

end BGW.StableTrees.DiscreteHeightApprox
