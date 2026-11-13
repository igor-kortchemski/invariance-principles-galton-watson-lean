/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.DiscreteHeightApproxMaximal
import Mathlib.Probability.Moments.Variance
import BGW.StableTrees.SurvivalBasic

/-!
# Two-limit control of centered cycle maxima

Centering the iid cycle counts gives independent square-integrable increments, with
variances bounded by the uncentered first-cycle second moment. The number of cycles is
of order `n/B_n`. The finite-cutoff maximal bound and the scale-uniform second moment
therefore give an error tending to zero as the band shrinks.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal Classical
open BGW.StableTrees.DiscreteForest
open BGW.Probability

namespace BGW.StableTrees.DiscreteHeightApprox

/-- All cycles have the same second moment. -/
theorem integral_clusterVisits_sq_eq_zero (μ : PMF ℕ) (hc : IsCritical μ)
    (hne : μ 1 ≠ 1) (a : ℝ) (i : ℕ) :
    (∫ ω, (clusterVisits ω a i : ℝ) ^ 2 ∂(offspringSeqLaw μ).toMeasure) =
      ∫ ω, (clusterVisits ω a 0 : ℝ) ^ 2 ∂(offspringSeqLaw μ).toMeasure := by
  have he := congrArg (fun ν : Measure ℕ => ∫ k : ℕ, (k : ℝ) ^ 2 ∂ν)
    (map_clusterVisits_eq_zero μ hc hne a i)
  rw [integral_map (measurable_clusterVisits a i).aemeasurable
      (measurable_of_countable (fun k : ℕ => (k : ℝ) ^ 2)).aestronglyMeasurable,
    integral_map (measurable_clusterVisits a 0).aemeasurable
      (measurable_of_countable (fun k : ℕ => (k : ℝ) ^ 2)).aestronglyMeasurable] at he
  exact he

/-- The centered cycle-sum maximum has a second-moment upper bound with one extra cycle. -/
theorem measure_cluster_partialSum_maximal_le (μ : PMF ℕ) (hc : IsCritical μ)
    (hne : μ 1 ≠ 1) {a r : ℝ} (ha : 0 < a) (hr : 0 < r) (m : ℕ) :
    (offspringSeqLaw μ).toMeasure
      {ω | ∃ N ∈ Finset.range (m + 1), r <
        |(∑ i ∈ Finset.range N, (clusterVisits ω a i : ℝ)) - (N : ℝ) * (⌈a⌉₊ : ℝ)|} ≤
      ENNReal.ofReal (4 * (m + 1 : ℕ) *
        (∫ ω, (clusterVisits ω a 0 : ℝ) ^ 2 ∂(offspringSeqLaw μ).toMeasure) / r ^ 2) := by
  let V (i : ℕ) (ω : ℕ → ℕ) : ℝ := clusterVisits ω a i
  let X (i : ℕ) (ω : ℕ → ℕ) : ℝ := V i ω - (⌈a⌉₊ : ℝ)
  have hmV (i : ℕ) : Measurable (V i) :=
    (measurable_of_countable (fun k : ℕ => (k : ℝ))).comp (measurable_clusterVisits a i)
  have hm (i : ℕ) : StronglyMeasurable (X i) :=
    ((hmV i).sub measurable_const).stronglyMeasurable
  have hmemV (i : ℕ) : MemLp (V i) 2 (offspringSeqLaw μ).toMeasure :=
    (memLp_two_iff_integrable_sq (hmV i).aestronglyMeasurable).mpr
      (integrable_clusterVisits_sq μ hc hne ha i)
  have hmem (i : ℕ) : MemLp (X i) 2 (offspringSeqLaw μ).toMeasure :=
    (hmemV i).sub (memLp_const _)
  have hzero (i : ℕ) : ∫ ω, X i ω ∂(offspringSeqLaw μ).toMeasure = 0 := by
    rw [integral_sub ((hmemV i).integrable (by norm_num)) (integrable_const _),
      clusterVisits_mean μ hc hne ha i]
    simp
  have hi : iIndepFun X (offspringSeqLaw μ).toMeasure := by
    have he := (clusterVisits_iid μ hc hne ha).1.comp
      (fun _ (v : ℕ) => (v : ℝ) - (⌈a⌉₊ : ℝ))
      (fun _ => (measurable_of_countable _))
    simpa only [Function.comp_def] using he
  have hsq (i : ℕ) : (∫ ω, (X i ω) ^ 2 ∂(offspringSeqLaw μ).toMeasure) ≤
      ∫ ω, (clusterVisits ω a 0 : ℝ) ^ 2 ∂(offspringSeqLaw μ).toMeasure := by
    have hv := variance_le_expectation_sq (μ := (offspringSeqLaw μ).toMeasure)
      (hmV i).aestronglyMeasurable
    rw [variance_eq_integral (hmV i).aemeasurable, clusterVisits_mean μ hc hne ha i] at hv
    change (∫ ω, X i ω ^ 2 ∂(offspringSeqLaw μ).toMeasure) ≤
      ∫ ω, (V i ω) ^ 2 ∂(offspringSeqLaw μ).toMeasure at hv
    exact hv.trans_eq (integral_clusterVisits_sq_eq_zero μ hc hne a i)
  have hb := measure_partialSum_maximal_le hm hi hmem hzero m hr
  have he (N : ℕ) (ω : ℕ → ℕ) :
      (∑ i ∈ Finset.range N, X i ω) =
        (∑ i ∈ Finset.range N, (clusterVisits ω a i : ℝ)) - (N : ℝ) * (⌈a⌉₊ : ℝ) := by
    simp only [X, V, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  simp_rw [he] at hb
  refine hb.trans (ENNReal.ofReal_le_ofReal ?_)
  apply div_le_div_of_nonneg_right _ (sq_nonneg r)
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.range (m + 1)) => hsq i)
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hs
  nlinarith only [hs]

private theorem limsup_cluster_maximal_le {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ}
    (h : StableDomain μ θ B) {x δ ε : ℝ} (hx : 0 < x) (hδ : 0 < δ) (hε : 0 < ε) :
    limsup (fun n : ℕ => (offspringSeqLaw μ).toMeasure
      {ω | ∃ N ∈ Finset.range (⌈x * (n : ℝ) / B n⌉₊ + 1),
        δ * ((n : ℝ) * ε) <
          |(∑ i ∈ Finset.range N, (clusterVisits ω (ε * B n) i : ℝ)) -
            (N : ℝ) * (⌈ε * B n⌉₊ : ℝ)|}) atTop ≤
      ENNReal.ofReal (136 * (x + 1) / δ ^ 2 * Real.exp 1 * ε ^ (θ - 1)) := by
  let D := 17 * Real.exp 1 * ε ^ (θ - 1)
  have hD : 0 < D := by dsimp [D]; positivity
  let H (n : ℕ) := (B n / (n : ℝ)) *
    (∫ ω, (clusterVisits ω (ε * B n) 0 : ℝ) ^ 2 ∂(offspringSeqLaw μ).toMeasure) /
      (ε * B n) ^ 2
  have hH : ∀ᶠ n : ℕ in atTop, H n < 2 * D := by
    have hlt : ENNReal.ofReal D < ENNReal.ofReal (2 * D) :=
      (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr (by linarith)
    have he := eventually_lt_of_limsup_lt ((limsup_clusterVisits_sq_le h hε).trans_lt hlt)
    exact he.mono fun n hn => (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mp hn
  have hsmall := (Survival.tendsto_B_div_n h).eventually
    (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  refine limsup_le_of_le (by isBoundedDefault) ?_
  filter_upwards [eventually_ge_atTop 1, hH, hsmall] with n hn hHn hsn
  have hBn := h.pos n hn
  have hnR : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  let m := ⌈x * (n : ℝ) / B n⌉₊
  have hfin := measure_cluster_partialSum_maximal_le μ h.critical h.nondegenerate
    (mul_pos hε hBn) (mul_pos hδ (mul_pos hnR hε)) m
  refine hfin.trans (ENNReal.ofReal_le_ofReal ?_)
  have hceil : (m : ℝ) ≤ x * (n : ℝ) / B n + 1 :=
    (Nat.ceil_lt_add_one (div_nonneg (mul_nonneg hx.le hnR.le) hBn.le)).le
  have hcoeff : ((m + 1 : ℕ) : ℝ) * B n / (n : ℝ) ≤ x + 1 := by
    have hm := mul_le_mul_of_nonneg_right hceil (div_nonneg hBn.le hnR.le)
    have he : (x * (n : ℝ) / B n + 1) * (B n / (n : ℝ)) = x + B n / (n : ℝ) := by
      field_simp
    rw [he] at hm
    push_cast
    rw [show ((m : ℝ) + 1) * B n / (n : ℝ) =
      (m : ℝ) * (B n / (n : ℝ)) + B n / (n : ℝ) by ring]
    linarith only [hm, hsn]
  have hH0 : 0 ≤ H n := div_nonneg (mul_nonneg (div_nonneg hBn.le hnR.le)
    (integral_nonneg fun ω => sq_nonneg _)) (sq_nonneg _)
  have hprod := mul_le_mul_of_nonneg_right hcoeff hH0
  have he : 4 * ((m + 1 : ℕ) : ℝ) *
      (∫ ω, (clusterVisits ω (ε * B n) 0 : ℝ) ^ 2 ∂(offspringSeqLaw μ).toMeasure) /
        (δ * ((n : ℝ) * ε)) ^ 2 =
      (4 / δ ^ 2) * (((m + 1 : ℕ) : ℝ) * B n / (n : ℝ) * H n) := by
    dsimp only [H]
    field_simp
  rw [he]
  have hmul := mul_le_mul_of_nonneg_left hprod (div_nonneg (by norm_num : (0 : ℝ) ≤ 4)
    (sq_nonneg δ))
  have hupper : (4 / δ ^ 2) * ((x + 1) * H n) ≤
      (4 / δ ^ 2) * ((x + 1) * (2 * D)) := by
    gcongr
  calc
    _ ≤ _ := hmul
    _ ≤ _ := hupper
    _ = _ := by dsimp [D]; ring

/-- **Stopped error, uniform over the cutoff** (Kolmogorov maximal inequality from the three
suppliers above): over `N ≤ x n/B_n` cycles the centered cycle sums stay `o(n ε)` as `n → ∞`,
then `ε → 0`. -/
theorem cluster_partialSum_maximal {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ}
    (h : StableDomain μ θ B) {x δ : ℝ} (hx : 0 < x) (hδ : 0 < δ) :
    Tendsto (fun ε : ℝ =>
        limsup (fun n : ℕ => ((offspringSeqLaw μ : ProbabilityMeasure (ℕ → ℕ)) :
          Measure (ℕ → ℕ))
          {ω | ∃ N ∈ Finset.range (⌈x * (n : ℝ) / B n⌉₊ + 1),
            δ * ((n : ℝ) * ε) <
              |(∑ i ∈ Finset.range N, (clusterVisits ω (ε * B n) i : ℝ)) -
                (N : ℝ) * (⌈ε * B n⌉₊ : ℝ)|}) atTop)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hp : 0 < θ - 1 := by linarith [h.alpha_mem.1]
  have hpow : Tendsto (fun ε : ℝ => ε ^ (θ - 1)) (𝓝[>] 0) (𝓝 0) := by
    simpa only [Real.zero_rpow hp.ne'] using
      ((Real.continuous_rpow_const hp.le).tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
  have hmajor : Tendsto (fun ε : ℝ => ENNReal.ofReal
      (136 * (x + 1) / δ ^ 2 * Real.exp 1 * ε ^ (θ - 1))) (𝓝[>] 0) (𝓝 0) := by
    have ht := hpow.const_mul (136 * (x + 1) / δ ^ 2 * Real.exp 1)
    rw [mul_zero] at ht
    simpa only [Function.comp_def, ENNReal.ofReal_zero] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp ht
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hmajor
  · exact Eventually.of_forall fun _ => bot_le
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    exact limsup_cluster_maximal_le h hx hδ hε

end BGW.StableTrees.DiscreteHeightApprox
