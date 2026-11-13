/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.DiscreteHeightApproxBandMoment
import BGW.StableTrees.SurvivalBasic

/-!
# Scale-uniform cycle second moments

The renewal estimate controls the quadratic term. The remaining linear ceiling
term vanishes at every fixed positive band parameter.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal Classical
open BGW.StableTrees.DiscreteForest

namespace BGW.StableTrees.DiscreteHeightApprox

/-- A fixed positive band has normalized cycle second-moment limsup of order
`ε^(θ-1)`, with a universal numerical constant. -/
theorem limsup_clusterVisits_sq_le {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ}
    (h : StableDomain μ θ B) {ε : ℝ} (hε : 0 < ε) :
    limsup (fun n : ℕ => ENNReal.ofReal
      ((B n / (n : ℝ)) * (∫ ω, (clusterVisits ω (ε * B n) 0 : ℝ) ^ 2
        ∂(offspringSeqLaw μ).toMeasure) / (ε * B n) ^ 2)) atTop ≤
      ENNReal.ofReal (17 * Real.exp 1 * ε ^ (θ - 1)) := by
  let C := Real.exp 1 * ε ^ (θ - 1)
  have hC : 0 < C := mul_pos (Real.exp_pos 1) (Real.rpow_pos_of_pos hε _)
  have hB := Survival.tendsto_B_atTop h
  have hceil := tendsto_ceil_scale hB hε.le
  have hratio : Tendsto (fun n : ℕ => (⌈ε * B n⌉₊ : ℝ) / (ε * B n)) atTop (𝓝 1) := by
    have ht := hceil.div_const ε
    rw [div_self hε.ne'] at ht
    simpa only [div_div, mul_comm ε] using ht
  have hlin : Tendsto (fun n : ℕ =>
      ((⌈ε * B n⌉₊ : ℝ) / B n / ε ^ 2) / (n : ℝ)) atTop (𝓝 0) :=
    (hceil.div_const (ε ^ 2)).div_atTop tendsto_natCast_atTop_atTop
  have hW := limsup_scaled_weakLadderRenewal_le h hε
  have hW' : ∀ᶠ n : ℕ in atTop, (B n / (n : ℝ)) *
      (weakLadderRenewal μ ⌈ε * B n⌉₊).toReal < 2 * C := by
    have hlt : ENNReal.ofReal C < ENNReal.ofReal (2 * C) :=
      (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr (by linarith)
    have he := eventually_lt_of_limsup_lt (hW.trans_lt hlt)
    exact he.mono fun n hn => (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mp hn
  refine limsup_le_of_le (by isBoundedDefault) ?_
  filter_upwards [eventually_ge_atTop 1, hW', hratio.eventually (gt_mem_nhds (by norm_num :
    (1 : ℝ) < 2)), hlin.eventually (gt_mem_nhds hC)] with n hn hWn hr hnlin
  have hBn := h.pos n hn
  have hnR : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have ha : 0 < ε * B n := mul_pos hε hBn
  let m := ⌈ε * B n⌉₊
  let X := (B n / (n : ℝ)) * (weakLadderRenewal μ m).toReal
  let A := ((m : ℝ) / B n / ε ^ 2) / (n : ℝ)
  let r := (m : ℝ) / (ε * B n)
  have hX : 0 ≤ X := mul_nonneg (div_nonneg hBn.le hnR.le) ENNReal.toReal_nonneg
  have hr0 : 0 ≤ r := div_nonneg (Nat.cast_nonneg _) ha.le
  have hr2 : r ^ 2 ≤ 4 := by change r < 2 at hr; nlinarith
  have hmoment := integral_clusterVisits_sq_le_renewal μ h.critical h.nondegenerate ha
  have hkm : (((m - 1 : ℕ) : ℝ)) ^ 2 ≤ (m : ℝ) ^ 2 := by
    have hle : ((m - 1 : ℕ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast Nat.sub_le m 1
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) hle 2
  have hmBound : (∫ ω, (clusterVisits ω (ε * B n) 0 : ℝ) ^ 2
      ∂(offspringSeqLaw μ).toMeasure) ≤
        (m : ℝ) + 2 * (m : ℝ) ^ 2 * (weakLadderRenewal μ m).toReal := by
    have hmul := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hkm (show (0 : ℝ) ≤ 2 by norm_num))
      (show 0 ≤ (weakLadderRenewal μ m).toReal from ENNReal.toReal_nonneg)
    linarith only [hmoment, hmul]
  have hb := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hmBound (div_nonneg hBn.le hnR.le)) (sq_nonneg (ε * B n))
  have he : (B n / (n : ℝ)) * ((m : ℝ) + 2 * (m : ℝ) ^ 2 *
      (weakLadderRenewal μ m).toReal) / (ε * B n) ^ 2 = A + 2 * r ^ 2 * X := by
    dsimp only [A, r, X]
    field_simp
  rw [he] at hb
  have hquad := mul_le_mul_of_nonneg_right hr2 hX
  apply ENNReal.ofReal_le_ofReal
  rw [show 17 * Real.exp 1 * ε ^ (θ - 1) = 17 * C by dsimp [C]; ring]
  change A < C at hnlin
  change X < 2 * C at hWn
  nlinarith only [hb, hquad, hnlin, hWn]

/-- **Scale-free second moment** of a cycle at level `a = ε B_n` against `N ≈ n/B_n` cycles:
`limsup_{ε↓0} limsup_n (B_n/n) E[V_0(εB_n)²] / (ε B_n)² = 0`
(rate `ε^{θ-1}` by the renewal bound). -/
theorem clusterVisits_secondMoment_scaled {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ}
    (h : StableDomain μ θ B) :
    Tendsto (fun ε : ℝ =>
        limsup (fun n : ℕ => ENNReal.ofReal
          ((B n / (n : ℝ)) *
            (∫ ω, (clusterVisits ω (ε * B n) 0 : ℝ) ^ 2
              ∂((offspringSeqLaw μ : ProbabilityMeasure (ℕ → ℕ)) : Measure (ℕ → ℕ))) /
            (ε * B n) ^ 2)) atTop)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hpow : Tendsto (fun ε : ℝ => ε ^ (θ - 1)) (𝓝[>] 0) (𝓝 0) := by
    have hp : 0 < θ - 1 := by linarith [h.alpha_mem.1]
    simpa only [Real.zero_rpow hp.ne'] using
      ((Real.continuous_rpow_const hp.le).tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
  have hmajor : Tendsto (fun ε : ℝ => ENNReal.ofReal (17 * Real.exp 1 * ε ^ (θ - 1)))
      (𝓝[>] 0) (𝓝 0) := by
    have ht := hpow.const_mul (17 * Real.exp 1)
    rw [mul_zero] at ht
    simpa only [Function.comp_def, ENNReal.ofReal_zero] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp ht
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hmajor
  · exact Eventually.of_forall fun _ => bot_le
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    exact limsup_clusterVisits_sq_le h hε

end BGW.StableTrees.DiscreteHeightApprox
