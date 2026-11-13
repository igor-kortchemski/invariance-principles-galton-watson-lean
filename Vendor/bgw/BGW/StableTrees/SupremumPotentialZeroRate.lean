/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.SupremumPotentialRegularity
import Mathlib.Topology.UniformSpace.HeineCantor

/-!
# Uniform zero-rate limit of the stable scale series

A compact majorant makes the series jointly continuous in its rate and argument.

Reference: A. E. Kyprianou, *Fluctuations of Lévy Processes with Applications*, 2nd ed.,
Springer, 2014, Chapter 8.
-/

@[expose] public section

open MeasureTheory Set Filter Topology

namespace BGW.StableTrees

private theorem stableSeries_rate_zero {θ : ℝ} (hθ : 1 < θ) (x : ℝ) :
    stableSeries θ 0 x = stableScale θ x := by
  -- `hθ` is part of the stated interface; this holds for every θ.
  have _hθ := hθ
  by_cases hx : 0 ≤ x
  · simp only [stableSeries, stableScale, ite_eq_left hx]
    rw [tsum_eq_single 0]
    · simp only [stableSeriesTerm, pow_zero, Nat.cast_zero, zero_add, mul_one, one_mul]
    · intro n hn
      simp [stableSeriesTerm, zero_pow hn]
  · simp [stableSeries, stableScale, hx]

/-- Joint continuity of the rate and spatial argument on compact positive rectangles. -/
theorem continuousOn_stableSeries_rate_argument {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (K : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => stableSeries θ p.1 p.2) (Icc 0 1 ×ˢ Icc 0 K) := by
  let M := max K 0
  have hM : 0 ≤ M := le_max_right _ _
  have hexp (n : ℕ) : 0 < θ * (n + 1) - 1 := by
    have hn : (1 : ℝ) ≤ n + 1 := by linarith [Nat.cast_nonneg (α := ℝ) n]
    nlinarith [hθ.1]
  have hc : ContinuousOn (fun p : ℝ × ℝ => ∑' n : ℕ, stableSeriesTerm θ p.1 n p.2)
      (Icc 0 1 ×ˢ Icc 0 K) := by
    refine continuousOn_tsum (fun n => ?_) (summable_stableSeriesTerm hθ 1 hM)
      (fun n p hp => ?_)
    · exact ((continuous_fst.pow n).mul
        ((Real.continuous_rpow_const (hexp n).le).comp continuous_snd)).div_const _
        |>.continuousOn
    · have hg : 0 < Real.Gamma (θ * (n + 1)) := Real.Gamma_pos_of_pos (by linarith [hexp n])
      simp only [stableSeriesTerm, Real.norm_eq_abs, abs_div, abs_mul,
        abs_of_nonneg (pow_nonneg hp.1.1 n),
        abs_of_nonneg (Real.rpow_nonneg hp.2.1 _), abs_of_pos hg, one_pow, one_mul]
      apply div_le_div_of_nonneg_right _ hg.le
      calc
        _ ≤ 1 * M ^ (θ * (n + 1) - 1) := mul_le_mul
          (pow_le_one₀ hp.1.1 hp.1.2) (Real.rpow_le_rpow hp.2.1
            (hp.2.2.trans (le_max_left _ _)) (hexp n).le)
          (Real.rpow_nonneg hp.2.1 _) zero_le_one
        _ = _ := one_mul _
  apply hc.congr
  intro p hp
  simp only [stableSeries, ite_eq_left hp.2.1]

/-- The scale series tends locally uniformly to the zero-rate scale. -/
theorem tendstoUniformlyOn_stableSeries_zero {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (K : ℝ) :
    TendstoUniformlyOn (fun q x => stableSeries θ q x) (stableScale θ) (𝓝[>] 0) (Icc 0 K) := by
  have hu : UniformContinuousOn (fun p : ℝ × ℝ => stableSeries θ p.1 p.2)
      (Icc 0 1 ×ˢ Icc 0 K) :=
    (isCompact_Icc.prod isCompact_Icc).uniformContinuousOn_of_continuous
      (continuousOn_stableSeries_rate_argument hθ K)
  have ht : TendstoUniformlyOn (fun q x => stableSeries θ q x) (stableSeries θ 0)
      (𝓝[Icc 0 1] 0) (Icc 0 K) := hu.tendstoUniformlyOn ⟨le_rfl, zero_le_one⟩
  have hfilter : 𝓝[>] (0 : ℝ) ≤ 𝓝[Icc 0 1] 0 := by
    apply nhdsWithin_le_of_mem
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds zero_lt_one).filter_mono nhdsWithin_le_nhds] with q hq hq1
    exact ⟨hq.le, hq1.le⟩
  have ht' : TendstoUniformlyOn (fun q x => stableSeries θ q x) (stableSeries θ 0)
      (𝓝[>] 0) (Icc 0 K) :=
    tendstoUniformlyOn_iff_tendstoUniformlyOnFilter.mpr
      (ht.tendstoUniformlyOnFilter.mono_left hfilter)
  exact ht'.congr_right (fun x _ => stableSeries_rate_zero hθ.1 x)

end BGW.StableTrees
