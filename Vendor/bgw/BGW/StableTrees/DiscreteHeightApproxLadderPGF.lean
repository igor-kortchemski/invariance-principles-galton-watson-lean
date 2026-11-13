/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.RealAttraction
public import BGW.StableTrees.DiscreteHeightApproxRenewalTransform
import BGW.StableTrees.SurvivalExpansion
import BGW.StableTrees.SurvivalRegularity

/-!
# The weak ladder-height PGF identity

The centered one-step Laplace expansion from `SurvivalExpansion` supplies the normalized
offspring PGF gap at exponential arguments, retaining the index-two infinite-variance
case. The offspring-tail coefficients satisfy a one-step difference identity. Summing
it against powers gives `(1-s) φ(s) = 1-g(s)`, with the atom at zero retained.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal Classical
open BGW.StableTrees.DiscreteForest

namespace BGW.StableTrees.DiscreteHeightApprox

section

open Attraction Attraction.LaplaceExpansion
open Survival (tendsto_B_atTop)

/-- Real-variable offspring PGF (internal interface for the Laplace bridge). -/
noncomputable def offspringPGFReal (μ : PMF ℕ) (s : ℝ) : ℝ :=
  ∑' j : ℕ, (μ j).toReal * s ^ j

private theorem centeredLaplace_pgf (μ : PMF ℕ) (hc : IsCritical μ)
    {u : ℝ} (hu : 0 ≤ u) :
    centeredLaplace (stepLaw μ) u = Real.exp u * offspringPGFReal μ (Real.exp (-u)) := by
  rw [centeredLaplace_eq, mean_stepLaw hc]
  simp only [mul_zero, Real.exp_zero, one_mul]
  rw [stepLaw, integral_map (measurable_of_countable _).aemeasurable (by fun_prop)]
  have hi : Integrable (fun k : ℕ => Real.exp (-u * (((k : ℤ) - 1 : ℤ) : ℝ)))
      μ.toMeasure := by
    apply Integrable.of_bound (by fun_prop) (Real.exp u)
    filter_upwards [] with k
    rw [Real.norm_of_nonneg (Real.exp_nonneg _)]
    apply Real.exp_le_exp.mpr
    simp only [Int.cast_sub, Int.cast_natCast, Int.cast_one]
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    nlinarith [mul_nonneg hu (by linarith : (0 : ℝ) ≤ (k : ℝ) + 1)]
  rw [PMF.integral_eq_tsum μ _ hi, offspringPGFReal, ← tsum_mul_left]
  apply tsum_congr
  intro k
  simp only [smul_eq_mul, Int.cast_sub, Int.cast_natCast, Int.cast_one]
  rw [← Real.exp_nat_mul]
  calc
    (μ k).toReal * Real.exp (-u * ((k : ℝ) - 1)) =
        (μ k).toReal * (Real.exp u * Real.exp ((k : ℝ) * -u)) := by
      congr 1
      rw [← Real.exp_add]
      congr 1
      ring
    _ = Real.exp u * ((μ k).toReal * Real.exp ((k : ℝ) * -u)) := by ring

/-- Laplace bridge from `StableDomain` (finding 3): a real proof obligation. -/
theorem norming_offspringPGF_gap
    {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ}
    (h : StableDomain μ θ B) {lam : ℝ} (hlam : 0 < lam) :
    Tendsto (fun n : ℕ => (n : ℝ) *
      (offspringPGFReal μ (Real.exp (-lam / B n)) -
        Real.exp (-lam / B n))) atTop (𝓝 (lam ^ θ)) := by
  have hu : Tendsto (fun n : ℕ => lam / B n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_B_atTop h)
  have hex : Tendsto (fun n : ℕ => Real.exp (-(lam / B n))) atTop (𝓝 1) := by
    simpa only [Function.comp_def, neg_zero, Real.exp_zero] using
      Real.continuous_exp.continuousAt.tendsto.comp hu.neg
  have ht := (Survival.tendsto_centeredLaplace_stableDomain h hlam).mul hex
  rw [mul_one] at ht
  apply ht.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  rw [centeredLaplace_pgf μ h.critical (le_of_lt (div_pos hlam (h.pos n hn)))]
  have he : Real.exp (lam / B n) * Real.exp (-(lam / B n)) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  simp only [neg_div]
  calc
    _ = (n : ℝ) * (offspringPGFReal μ (Real.exp (-(lam / B n))) *
        (Real.exp (lam / B n) * Real.exp (-(lam / B n))) -
          Real.exp (-(lam / B n))) := by ring
    _ = _ := by rw [he]; ring

end

private noncomputable def tailReal (μ : PMF ℕ) (h : ℕ) : ℝ :=
  (μ.toMeasure (Set.Ici (h + 1))).toReal

private theorem tailReal_succ (μ : PMF ℕ) (h : ℕ) :
    tailReal μ h = (μ (h + 1)).toReal + tailReal μ (h + 1) := by
  have he : Set.Ici (h + 1) = {h + 1} ∪ Set.Ici (h + 1 + 1) := by
    ext k
    simp only [Set.mem_Ici, Set.mem_union, Set.mem_singleton_iff]
    omega
  have hd : Disjoint ({h + 1} : Set ℕ) (Set.Ici (h + 1 + 1)) := by
    apply Set.disjoint_left.mpr
    intro k hk hge
    have hk' := Set.mem_singleton_iff.mp hk
    change h + 1 + 1 ≤ k at hge
    omega
  have hm : μ.toMeasure (Set.Ici (h + 1)) = μ (h + 1) + μ.toMeasure (Set.Ici (h + 1 + 1)) := by
    rw [he, measure_union hd measurableSet_Ici,
      PMF.toMeasure_apply_singleton μ (h + 1) (measurableSet_singleton _)]
  have hr := congrArg ENNReal.toReal hm
  rw [ENNReal.toReal_add (μ.apply_ne_top _) (measure_ne_top _ _)] at hr
  exact hr

private theorem tailReal_zero (μ : PMF ℕ) : (μ 0).toReal + tailReal μ 0 = 1 := by
  have he : ({0} : Set ℕ) ∪ Set.Ici 1 = Set.univ := by
    ext k
    simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_Ici, Set.mem_univ, iff_true]
    omega
  have hd : Disjoint ({0} : Set ℕ) (Set.Ici 1) := by
    apply Set.disjoint_left.mpr
    intro k hk hge
    have hk' := Set.mem_singleton_iff.mp hk
    change 1 ≤ k at hge
    omega
  have hm : μ 0 + μ.toMeasure (Set.Ici 1) = 1 := by
    rw [← PMF.toMeasure_apply_singleton μ 0 (measurableSet_singleton _),
      ← measure_union hd measurableSet_Ici, he, measure_univ]
  have hr := congrArg ENNReal.toReal hm
  simpa only [tailReal, zero_add, ENNReal.toReal_add (μ.apply_ne_top _) (measure_ne_top _ _),
    ENNReal.toReal_one] using hr

private theorem summable_tailReal (μ : PMF ℕ) (hc : IsCritical μ) : Summable (tailReal μ) := by
  apply ENNReal.summable_toReal
  rw [tsum_offspring_tails μ hc]
  exact ENNReal.one_ne_top

private theorem summable_pmfReal (μ : PMF ℕ) : Summable (fun h : ℕ => (μ h).toReal) := by
  apply ENNReal.summable_toReal
  rw [PMF.tsum_coe]
  exact ENNReal.one_ne_top

private theorem summable_tail_power (μ : PMF ℕ) (hc : IsCritical μ) {s : ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) : Summable (fun h : ℕ => tailReal μ h * s ^ h) := by
  apply Summable.of_nonneg_of_le _ _ (summable_tailReal μ hc)
  · intro h
    exact mul_nonneg ENNReal.toReal_nonneg (pow_nonneg hs0 h)
  · intro h
    exact mul_le_of_le_one_right ENNReal.toReal_nonneg (pow_le_one₀ hs0 hs1)

private theorem summable_offspring_power (μ : PMF ℕ) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    Summable (fun h : ℕ => (μ h).toReal * s ^ h) := by
  apply Summable.of_nonneg_of_le _ _ (summable_pmfReal μ)
  · intro h
    exact mul_nonneg ENNReal.toReal_nonneg (pow_nonneg hs0 h)
  · intro h
    exact mul_le_of_le_one_right ENNReal.toReal_nonneg (pow_le_one₀ hs0 hs1)

/-- The ladder PGF is at most one at arguments in the unit interval. -/
theorem weakLadderPGF_le_one (μ : PMF ℕ) {s : ℝ≥0∞} (hs : s ≤ 1) :
    weakLadderPGF μ s ≤ 1 := by
  calc
    _ ≤ ∫⁻ _ω : ℕ → ℕ, (1 : ℝ≥0∞) ∂(offspringSeqLaw μ).toMeasure :=
      lintegral_mono fun _ => pow_le_one₀ (show (0 : ℝ≥0∞) ≤ s from bot_le) hs
    _ = 1 := by simp

private theorem weakLadderPGF_toReal (μ : PMF ℕ) (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    {s : ℝ} (hs0 : 0 ≤ s) :
    (weakLadderPGF μ (ENNReal.ofReal s)).toReal = ∑' h : ℕ, tailReal μ h * s ^ h := by
  rw [weakLadderPGF_eq_tsum μ hc hne,
    ENNReal.tsum_toReal_eq (fun h => ENNReal.mul_ne_top
      (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) (measure_ne_top _ _))]
  apply tsum_congr
  intro h
  simp only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal hs0]
  exact mul_comm _ _

/-- The first ladder PGF has the exact offspring generating-function identity. -/
theorem weakLadderPGF_identity (μ : PMF ℕ) (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    offspringPGFReal μ s + (1 - s) * (weakLadderPGF μ (ENNReal.ofReal s)).toReal = 1 := by
  rw [weakLadderPGF_toReal μ hc hne hs0]
  have hq := summable_tail_power μ hc hs0 hs1
  have hp := summable_offspring_power μ hs0 hs1
  have hqs : Summable (fun h : ℕ => tailReal μ (h + 1) * s ^ (h + 1)) :=
    hq.comp_injective Nat.succ_injective
  have hps : Summable (fun h : ℕ => (μ (h + 1)).toReal * s ^ (h + 1)) :=
    hp.comp_injective Nat.succ_injective
  have hq0 := hq.sum_add_tsum_nat_add 1
  have hp0 := hp.sum_add_tsum_nat_add 1
  simp only [Finset.sum_range_one, pow_zero, mul_one] at hq0 hp0
  have hscomp : (∑' h : ℕ, tailReal μ h * s ^ (h + 1)) =
      (∑' h : ℕ, (μ (h + 1)).toReal * s ^ (h + 1)) +
        ∑' h : ℕ, tailReal μ (h + 1) * s ^ (h + 1) := by
    rw [← hps.tsum_add hqs]
    apply tsum_congr
    intro h
    rw [tailReal_succ μ h]
    ring
  have hsprod : (∑' h : ℕ, tailReal μ h * s ^ (h + 1)) =
      (∑' h : ℕ, tailReal μ h * s ^ h) * s := by
    simp_rw [pow_succ, ← mul_assoc]
    exact tsum_mul_right
  have hzero := tailReal_zero μ
  unfold offspringPGFReal
  nlinarith

/-- The complement of the ladder PGF equals the offspring PGF gap divided by `1-s`. -/
theorem one_sub_weakLadderPGF (μ : PMF ℕ) (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    1 - (weakLadderPGF μ (ENNReal.ofReal s)).toReal =
      (offspringPGFReal μ s - s) / (1 - s) := by
  have he := weakLadderPGF_identity μ hc hne hs0 hs1.le
  apply (eq_div_iff (by linarith : 1 - s ≠ 0)).mpr
  nlinarith

/-- The ladder PGF is strictly less than one below one, for a nondegenerate critical law. -/
theorem weakLadderPGF_lt_one (μ : PMF ℕ) (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) : weakLadderPGF μ (ENNReal.ofReal s) < 1 := by
  have hle := weakLadderPGF_le_one μ (s := ENNReal.ofReal s)
    (ENNReal.ofReal_le_one.mpr hs1.le)
  have hfinite : weakLadderPGF μ (ENNReal.ofReal s) ≠ ∞ := ne_top_of_le_ne_top (by simp) hle
  have hgap : 0 < offspringPGFReal μ s - s := by
    have h := Survival.offspringDefect_pos hc hne (by linarith : 0 < 1 - s)
      (by linarith : 1 - s ≤ 1)
    simpa only [Survival.offspringDefect, sub_sub_cancel, Survival.realGF,
      offspringPGFReal] using h
  have hreal : (weakLadderPGF μ (ENNReal.ofReal s)).toReal < 1 := by
    rw [← sub_pos, one_sub_weakLadderPGF μ hc hne hs0 hs1]
    exact div_pos hgap (by linarith)
  exact (ENNReal.toReal_lt_toReal hfinite ENNReal.one_ne_top).mp (by simpa using hreal)

end BGW.StableTrees.DiscreteHeightApprox
