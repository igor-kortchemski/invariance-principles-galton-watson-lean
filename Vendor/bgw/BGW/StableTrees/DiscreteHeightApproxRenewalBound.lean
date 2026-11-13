/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.DiscreteHeightApproxLadderPGF

/-!
# An exponential upper bound for weak ladder renewal

A level cutoff is dominated by an exponential weight. The product formula for
attained-height transforms reduces the renewal series to a geometric series.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal Classical
open BGW.StableTrees.DiscreteForest

namespace BGW.StableTrees.DiscreteHeightApprox

private theorem cutoff_le_exp_parameter (m h : ℕ) {u : ℝ} (hu : 0 ≤ u) (hh : h < m) :
    (1 : ℝ≥0∞) ≤ ENNReal.ofReal (Real.exp (u * (m : ℝ))) *
      (ENNReal.ofReal (Real.exp (-u))) ^ h := by
  have hhm : (h : ℝ) ≤ m := by exact_mod_cast hh.le
  have he : (1 : ℝ) ≤ Real.exp (u * (m : ℝ)) * (Real.exp (-u)) ^ h := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    apply Real.one_le_exp
    nlinarith [mul_nonneg hu (show 0 ≤ (m : ℝ) - h by linarith)]
  simpa only [ENNReal.ofReal_one, ENNReal.ofReal_mul (Real.exp_nonneg _),
    ENNReal.ofReal_pow (Real.exp_nonneg _)] using ENNReal.ofReal_le_ofReal he

/-- A free exponential parameter bounds renewal without changing a moving level to a fixed one. -/
theorem weakLadderRenewal_le_exp (μ : PMF ℕ) (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (m : ℕ) {u : ℝ} (hu : 0 ≤ u) :
    weakLadderRenewal μ m ≤ ENNReal.ofReal (Real.exp (u * (m : ℝ))) *
      (1 - weakLadderPGF μ (ENNReal.ofReal (Real.exp (-u))))⁻¹ := by
  let s := ENNReal.ofReal (Real.exp (-u))
  have hterm (i : ℕ) : (offspringSeqLaw μ).toMeasure {ω | weakEpochHeight ω i < m} ≤
      ENNReal.ofReal (Real.exp (u * (m : ℝ))) * (weakLadderPGF μ s) ^ i := by
    calc
      _ = ∫⁻ ω, {ξ | weakEpochHeight ξ i < m}.indicator (fun _ => (1 : ℝ≥0∞)) ω
          ∂(offspringSeqLaw μ).toMeasure :=
        (lintegral_indicator_fun_one (measurableSet_lt (measurable_weakEpochHeight i)
          measurable_const)).symm
      _ ≤ ∫⁻ ω, ENNReal.ofReal (Real.exp (u * (m : ℝ))) * s ^ weakEpochHeight ω i
          ∂(offspringSeqLaw μ).toMeasure := by
        apply lintegral_mono
        intro ω
        by_cases hh : weakEpochHeight ω i < m
        · rw [Set.indicator_of_mem (show ω ∈ {ξ | weakEpochHeight ξ i < m} from hh)]
          exact cutoff_le_exp_parameter m _ hu hh
        · rw [Set.indicator_of_notMem (show ω ∉ {ξ | weakEpochHeight ξ i < m} from hh)]
          exact bot_le
      _ = _ := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_epochHeight_pow μ hc hne s i]
  unfold weakLadderRenewal
  calc
    _ ≤ ∑' i : ℕ, ENNReal.ofReal (Real.exp (u * (m : ℝ))) * (weakLadderPGF μ s) ^ i :=
      ENNReal.tsum_le_tsum hterm
    _ = _ := by rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]

/-- Real renewal bound with an arbitrary positive exponential parameter. -/
theorem weakLadderRenewal_toReal_le_exp (μ : PMF ℕ) (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (m : ℕ) {u : ℝ} (hu : 0 < u) :
    (weakLadderRenewal μ m).toReal ≤ Real.exp (u * (m : ℝ)) * (1 - Real.exp (-u)) /
      (offspringPGFReal μ (Real.exp (-u)) - Real.exp (-u)) := by
  let s := Real.exp (-u)
  have hs0 : 0 ≤ s := Real.exp_nonneg _
  have hs1 : s < 1 := Real.exp_lt_one_iff.mpr (neg_neg_of_pos hu)
  have hφ := weakLadderPGF_lt_one μ hc hne hs0 hs1
  have hsub : 1 - weakLadderPGF μ (ENNReal.ofReal s) ≠ 0 :=
    ne_of_gt (tsub_pos_iff_lt.mpr hφ)
  have hfinite : ENNReal.ofReal (Real.exp (u * (m : ℝ))) *
      (1 - weakLadderPGF μ (ENNReal.ofReal s))⁻¹ ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.inv_ne_top.mpr hsub)
  have he := ENNReal.toReal_mono hfinite (weakLadderRenewal_le_exp μ hc hne m hu.le)
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_nonneg _), ENNReal.toReal_inv,
    ENNReal.toReal_sub_of_le hφ.le ENNReal.one_ne_top, ENNReal.toReal_one,
    one_sub_weakLadderPGF μ hc hne hs0 hs1] at he
  change (weakLadderRenewal μ m).toReal ≤ Real.exp (u * (m : ℝ)) * (1 - s) /
    (offspringPGFReal μ s - s)
  calc
    _ ≤ Real.exp (u * (m : ℝ)) * ((offspringPGFReal μ s - s) / (1 - s))⁻¹ := he
    _ = _ := by rw [inv_div]; ring

end BGW.StableTrees.DiscreteHeightApprox
