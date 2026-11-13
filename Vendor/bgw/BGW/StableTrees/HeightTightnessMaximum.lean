/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.HeightTightnessRegeneration
import BGW.StableTrees.DiscreteHeightApproxCutoff
import BGW.StableTrees.Survival
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Tightness of the running maximum of the forest height

The first-upcrossing survival bound splits the event into survival among finitely
many blocks and early passage beyond those blocks. Walk-maximum tightness controls
the latter term, and the stable survival asymptotics control the former.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal Classical
open BGW.StableTrees.DiscreteForest

namespace BGW.StableTrees.HeightTightness


/-- A scaled finite-height maximum is controlled by the first-upcrossing event. -/
theorem scaled_height_max_probability_le {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ}
    (h : StableDomain μ θ B) {n : ℕ} (hn : 1 ≤ n) (T δ : ℝ) (l : ℕ) :
    (offspringSeqLaw μ).toMeasure.real
      {ω | δ < B n / n * (((Finset.range (⌊(n : ℝ) * T⌋₊ + 1)).sup
        (fun k => forestHeight ω k) : ℕ) : ℝ)} ≤
      (l : ℝ) * Survival.survivalProb μ ⌊δ * (n : ℝ) / B n⌋₊ +
        (offspringSeqLaw μ).toMeasure.real {ω | ladderTime ω l ≤ ⌊(n : ℝ) * T⌋₊} := by
  apply le_trans (measureReal_mono ?_) (height_hit_probability_le μ h.critical h.nondegenerate
    ⌊δ * (n : ℝ) / B n⌋₊ ⌊(n : ℝ) * T⌋₊ l)
  intro ω hω
  obtain ⟨k, hk, he⟩ := (Finset.range (⌊(n : ℝ) * T⌋₊ + 1)).exists_mem_eq_sup
    ⟨0, by simp⟩ (fun k => forestHeight ω k)
  simp only [Set.mem_ofPred_eq] at hω ⊢
  rw [he] at hω
  refine ⟨k, by simpa using hk, ?_⟩
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hB := h.pos n hn
  have hlt : δ * (n : ℝ) / B n < (forestHeight ω k : ℝ) := by
    apply (div_lt_iff₀ hB).mpr
    have := (lt_div_iff₀ hnR).mp (show δ < B n * (forestHeight ω k : ℝ) / n by
      simpa only [div_mul_eq_mul_div] using hω)
    nlinarith
  exact Nat.floor_le_of_le hlt.le

private theorem passage_probability_le_maxTail {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ}
    (h : StableDomain μ θ B) {n l : ℕ} {T K : ℝ} (hlevel : K * B n < l) :
    (offspringSeqLaw μ).toMeasure.real {ω | ladderTime ω l ≤ ⌊(n : ℝ) * T⌋₊} ≤
      BGW.Probability.RealWalk.maxTail (realOffspringStepLaw μ) ⌊(n : ℝ) * T⌋₊
        (K * B n) := by
  have hs : ∀ᵐ ω ∂(offspringSeqLaw μ).toMeasure,
      ω ∈ {ω | ladderTime ω l ≤ ⌊(n : ℝ) * T⌋₊} →
        ω ∈ {ω | ∃ k ≤ ⌊(n : ℝ) * T⌋₊, K * B n < |(walk ω k : ℝ)|} := by
    filter_upwards [ae_ladderFinite μ h.critical h.nondegenerate] with ω hω hh
    refine ⟨ladderTime ω l, hh, ?_⟩
    rw [walk_ladderTime hω, Int.cast_neg, Int.cast_natCast, abs_neg,
      abs_of_nonneg (Nat.cast_nonneg l)]
    exact hlevel
  have hm := ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hs)
  rw [DiscreteHeightApprox.measure_walk_maximum, ENNReal.toReal_ofReal
    (BGW.Probability.RealWalk.maxTail_nonneg _ _ _)] at hm
  exact hm

/-- **Running maximum** of the normalized height is tight (`sup H / n = O_P(1/B_n)`, used by
K12/K13). -/
theorem forestHeight_sup_tight {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ} (h : StableDomain μ θ B)
    {T : ℝ} (hT : 0 < T) {ε : ℝ} (hε : 0 < ε) :
    ∃ M : ℝ, limsup (fun n : ℕ => ((offspringSeqLaw μ : Measure (ℕ → ℕ))).real
      {ω | M < B n / n * (((Finset.range (⌊(n : ℝ) * T⌋₊ + 1)).sup
        (fun k => forestHeight ω k) : ℕ) : ℝ)}) atTop ≤ ε := by
  obtain ⟨K, hK, N, htail⟩ := h.isRealStableAttracted.horizon_max_tight hT
    (ε / 2) (by positivity)
  let a := K + 1
  have ha : 0 < a := by dsimp [a]; positivity
  have hp : 0 < 1 / (θ - 1) := one_div_pos.mpr (sub_pos.mpr h.alpha_mem.1)
  have hv : Tendsto (fun δ : ℝ => a * Survival.csbpSurvival θ δ) atTop (𝓝 0) := by
    have hx : Tendsto (fun δ : ℝ => (θ - 1) * δ) atTop atTop :=
      tendsto_id.const_mul_atTop (sub_pos.mpr h.alpha_mem.1)
    have hh := ((tendsto_rpow_neg_atTop hp).comp hx).const_mul a
    simpa only [mul_zero, Survival.csbpSurvival, neg_div, Function.comp_def] using hh
  obtain ⟨M, hM, hsmall⟩ := ((eventually_gt_atTop (0 : ℝ)).and
    (hv.eventually (gt_mem_nhds (show (0 : ℝ) < ε / 2 by positivity)))).exists
  have hsurv := Survival.tendsto_floor_mul_survivalProb_floor h hM ha.le
  have hev : ∀ᶠ n in atTop,
      (⌊a * B n⌋₊ : ℝ) * Survival.survivalProb μ ⌊M * (n : ℝ) / B n⌋₊ < ε / 2 :=
    hsurv.eventually (gt_mem_nhds hsmall)
  have hBbig : ∀ᶠ n in atTop, 1 < B n := (Survival.tendsto_B_atTop h).eventually_gt_atTop 1
  refine ⟨M, limsup_le_of_le ?_ ?_⟩
  · exact Filter.isCoboundedUnder_le_of_le atTop fun _ => measureReal_nonneg
  · filter_upwards [eventually_ge_atTop 1, eventually_ge_atTop N, hev, hBbig]
      with n hn hnN hnS hnB
    have hlev : K * B n < (⌊a * B n⌋₊ : ℝ) := by
      have hf := Nat.lt_floor_add_one (a * B n)
      dsimp [a] at hf
      nlinarith
    have hh := passage_probability_le_maxTail h (T := T) hlev
    exact (scaled_height_max_probability_le h hn T M ⌊a * B n⌋₊).trans
      (by linarith [htail n hnN])

end BGW.StableTrees.HeightTightness
