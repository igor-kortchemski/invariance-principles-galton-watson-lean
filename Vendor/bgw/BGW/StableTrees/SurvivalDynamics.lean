/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.SurvivalRegularity
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# Local regularity for the survival time change

Continuity of the generating function and the sublinear defect at zero are consequences
of summability of the offspring probabilities and their critical first moment.
-/

@[expose] public section

open MeasureTheory Filter
open scoped Topology ENNReal

namespace BGW.StableTrees.Survival

/-- The real generating function is continuous on the unit interval. -/
theorem continuousOn_realGF (μ : PMF ℕ) : ContinuousOn (realGF μ) (Set.Icc 0 1) := by
  apply continuousOn_tsum (fun k => by fun_prop)
    (ENNReal.summable_toReal (PMF.tsum_coe_ne_top μ))
  intro k x hx
  rw [Real.norm_of_nonneg (mul_nonneg ENNReal.toReal_nonneg (pow_nonneg hx.1 _))]
  exact mul_le_of_le_one_right ENNReal.toReal_nonneg (pow_le_one₀ hx.1 hx.2)

/-- The offspring defect is continuous on the unit interval. -/
theorem continuousOn_offspringDefect (μ : PMF ℕ) :
    ContinuousOn (offspringDefect μ) (Set.Icc 0 1) := by
  apply ContinuousOn.sub _ (by fun_prop)
  apply (continuousOn_realGF μ).comp (by fun_prop)
  intro u hu
  exact ⟨by linarith [hu.2], by linarith [hu.1]⟩

/-- Criticality makes the offspring defect negligible compared with its argument at zero. -/
theorem tendsto_offspringDefect_div_self {μ : PMF ℕ} (hc : IsCritical μ) :
    Tendsto (fun u => offspringDefect μ u / u) (𝓝[>] 0) (𝓝 0) := by
  have hm : Summable (fun k : ℕ => (μ k).toReal * (k : ℝ)) := by
    have hs : (∑' k : ℕ, (k : ℝ≥0∞) * μ k) ≠ ∞ := by
      rw [hc]
      exact ENNReal.one_ne_top
    simpa [ENNReal.toReal_mul, mul_comm] using ENNReal.summable_toReal hs
  have hlim (k : ℕ) : Tendsto (fun u : ℝ =>
      (μ k).toReal * (((1 - u) ^ k - 1 + k * u) / u)) (𝓝[>] 0) (𝓝 0) := by
    have hd : HasDerivAt (fun u : ℝ => (1 - u) ^ k - 1 + k * u) 0 0 := by
      convert ((((hasDerivAt_id (0 : ℝ)).const_sub 1).pow k).sub_const 1).add
        ((hasDerivAt_id (0 : ℝ)).const_mul (k : ℝ)) using 1 <;>
        simp [mul_comm, Pi.add_apply, funext_iff]
    have ht := hd.tendsto_slope_zero_right.const_mul (μ k).toReal
    simpa [smul_eq_mul, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using ht
  have ht := tendsto_tsum_of_dominated_convergence hm hlim (show
      ∀ᶠ u : ℝ in 𝓝[>] 0, ∀ k : ℕ,
        ‖(μ k).toReal * (((1 - u) ^ k - 1 + k * u) / u)‖ ≤
          (μ k).toReal * (k : ℝ) from by
    filter_upwards [self_mem_nhdsWithin,
      (show ∀ᶠ u : ℝ in 𝓝[>] 0, u ≤ 1 from
        (eventually_le_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds)]
      with u hu hu1 k
    change 0 < u at hu
    have hb := one_add_mul_sub_le_pow (a := 1 - u) (by linarith) k
    have hrem : 0 ≤ (1 - u) ^ k - 1 + k * u := by nlinarith [hb]
    rw [Real.norm_of_nonneg (mul_nonneg ENNReal.toReal_nonneg (div_nonneg hrem hu.le))]
    apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
    rw [div_le_iff₀ hu]
    have hp := pow_le_one₀ (by linarith : 0 ≤ 1 - u) (by linarith : 1 - u ≤ 1) (n := k)
    linarith)
  simp only [tsum_zero] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin,
    (show ∀ᶠ u : ℝ in 𝓝[>] 0, u ≤ 1 from
      (eventually_le_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds)]
    with u hu hu1
  change 0 < u at hu
  rw [offspringDefect_eq_tsum μ hc hu.le hu1, ← tsum_div_const]
  apply tsum_congr
  intro k
  ring

private theorem realGF_lt_one {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) : realGF μ t < 1 := by
  obtain ⟨j, hj, hμj⟩ := hc.exists_two_le_ne_zero hne
  have hs : Summable (fun k : ℕ => (μ k).toReal) :=
    ENNReal.summable_toReal (PMF.tsum_coe_ne_top μ)
  have hlt : realGF μ t < ∑' k : ℕ, (μ k).toReal := by
    apply Summable.tsum_lt_tsum_of_nonneg (i := j) _ _ _ hs
    · intro k
      exact mul_nonneg ENNReal.toReal_nonneg (pow_nonneg ht0 k)
    · intro k
      exact mul_le_of_le_one_right ENNReal.toReal_nonneg (pow_le_one₀ ht0 ht1.le)
    · exact mul_lt_of_lt_one_right (ENNReal.toReal_pos hμj (μ.apply_ne_top j))
        (pow_lt_one₀ ht0 ht1 (by omega))
  have hsum : (∑' k : ℕ, (μ k).toReal) = 1 := by
    rw [← ENNReal.tsum_toReal_eq (fun k => μ.apply_ne_top k), PMF.tsum_coe]
    simp
  rwa [hsum] at hlt

/-- A critical nondegenerate tree has positive survival probability at every finite depth. -/
theorem survivalProb_pos {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1) (k : ℕ) :
    0 < survivalProb μ k := by
  induction k with
  | zero => rw [survivalProb_zero]; norm_num
  | succ k ih =>
    rw [survivalProb_succ]
    exact sub_pos.mpr (realGF_lt_one hc hne
      (by linarith [(survivalProb_mem_Icc μ k).2]) (by linarith))

/-- The decrement in one generation is precisely the offspring defect. -/
theorem survivalProb_sub_succ (μ : PMF ℕ) (k : ℕ) :
    survivalProb μ k - survivalProb μ (k + 1) = offspringDefect μ (survivalProb μ k) := by
  rw [survivalProb_succ, offspringDefect]
  ring

/-- Adjacent survival probabilities are asymptotically equivalent. -/
theorem tendsto_survivalProb_succ_div {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1) :
    Tendsto (fun k => survivalProb μ (k + 1) / survivalProb μ k) atTop (𝓝 1) := by
  have hs : Tendsto (survivalProb μ) atTop (𝓝[>] 0) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨tendsto_survivalProb_zero hc hne,
      Eventually.of_forall (survivalProb_pos hc hne)⟩
  have ht := (tendsto_const_nhds (x := (1 : ℝ))).sub ((tendsto_offspringDefect_div_self hc).comp hs)
  simp only [sub_zero] at ht
  apply ht.congr
  intro k
  have hp := survivalProb_pos hc hne k
  have he := survivalProb_sub_succ μ k
  dsimp only [Function.comp_def]
  rw [← he]
  field_simp
  ring

/-- The defect at consecutive survival probabilities also has ratio tending to one. -/
theorem tendsto_offspringDefect_survivalProb_succ_div {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ}
    (h : StableDomain μ θ B) :
    Tendsto (fun k => offspringDefect μ (survivalProb μ (k + 1)) /
      offspringDefect μ (survivalProb μ k)) atTop (𝓝 1) := by
  have hs : Tendsto (survivalProb μ) atTop (𝓝[>] 0) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨tendsto_survivalProb_zero h.critical h.nondegenerate,
      Eventually.of_forall (survivalProb_pos h.critical h.nondegenerate)⟩
  have hpos (k : ℕ) : 0 < offspringDefect μ (survivalProb μ k) :=
    offspringDefect_pos h.critical h.nondegenerate
      (survivalProb_pos h.critical h.nondegenerate k) (survivalProb_mem_Icc μ k).2
  apply tendsto_order.mpr
  constructor
  · intro a ha
    have hc : ContinuousAt (fun c : ℝ => c ^ θ) 1 :=
      Real.continuousAt_rpow_const _ _ (Or.inl one_ne_zero)
    have he : ∀ᶠ c : ℝ in 𝓝[<] 1, a < c ^ θ ∧ 0 < c := by
      apply Filter.Eventually.filter_mono nhdsWithin_le_nhds
      exact (hc.eventually (lt_mem_nhds (by simpa using ha))).and
        (eventually_gt_nhds (by norm_num : (0 : ℝ) < 1))
    obtain ⟨c, ⟨hac, hc0⟩, hc1⟩ := (he.and self_mem_nhdsWithin).exists
    have hr := tendsto_offspringDefect_ratio h hc0
      (Eventually.of_forall (survivalProb_pos h.critical h.nondegenerate)) hs
    filter_upwards [hr.eventually (lt_mem_nhds hac),
      (tendsto_survivalProb_succ_div h.critical h.nondegenerate).eventually
        (lt_mem_nhds hc1)] with k hk hratio
    apply hk.trans_le
    apply div_le_div_of_nonneg_right _ (hpos k).le
    apply offspringDefect_monotoneOn h.critical
      ⟨mul_nonneg hc0.le (survivalProb_mem_Icc μ k).1, (mul_le_of_le_one_left
        (survivalProb_mem_Icc μ k).1 hc1.le).trans (survivalProb_mem_Icc μ k).2⟩
      (survivalProb_mem_Icc μ (k + 1))
    exact ((lt_div_iff₀ (survivalProb_pos h.critical h.nondegenerate k)).mp hratio).le
  · intro b hb
    apply Eventually.of_forall
    intro k
    apply lt_of_le_of_lt _ hb
    rw [div_le_one (hpos k)]
    exact offspringDefect_monotoneOn h.critical (survivalProb_mem_Icc μ (k + 1))
      (survivalProb_mem_Icc μ k) (antitone_survivalProb μ (by omega))

end BGW.StableTrees.Survival
