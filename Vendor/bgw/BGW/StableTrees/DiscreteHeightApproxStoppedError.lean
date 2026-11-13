/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.DiscreteHeightApproxMaximalScale
import BGW.StableTrees.SurvivalBasic

/-!
# Stopped band-count errors

The sandwich uses partial sums at both `H` and `H+1`. Doubling the cutoff reserves
the extra cycle; the ceiling contribution is negligible at each fixed positive band.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal Classical
open BGW.StableTrees.DiscreteForest

namespace BGW.StableTrees.DiscreteHeightApprox

/-- A sandwich between the two adjacent cycle sums transfers a uniform centered-sum bound. -/
theorem bandCount_error_le {ω : ℕ → ℕ} (hω : EpochsFinite ω) (k : ℕ) {a r : ℝ}
    (ha : 0 < a)
    (hlo : |(∑ i ∈ Finset.range (weakLadderCount ω k), (clusterVisits ω a i : ℝ)) -
      (weakLadderCount ω k : ℝ) * (⌈a⌉₊ : ℝ)| ≤ r)
    (hhi : |(∑ i ∈ Finset.range (weakLadderCount ω k + 1), (clusterVisits ω a i : ℝ)) -
      (weakLadderCount ω k + 1 : ℕ) * (⌈a⌉₊ : ℝ)| ≤ r) :
    |(bandCount ω k a : ℝ) - (⌈a⌉₊ : ℝ) * (weakLadderCount ω k : ℝ)| ≤
      r + (⌈a⌉₊ : ℝ) + 1 := by
  have hs := bandCount_sandwich hω k ha
  have hl : (∑ i ∈ Finset.range (weakLadderCount ω k), (clusterVisits ω a i : ℝ)) - 1 ≤
      (bandCount ω k a : ℝ) := by
    have hh := hs.1
    exact_mod_cast hh
  have hu : (bandCount ω k a : ℝ) ≤
      ∑ i ∈ Finset.range (weakLadderCount ω k + 1), (clusterVisits ω a i : ℝ) := by
    exact_mod_cast hs.2
  have hmn : (0 : ℝ) ≤ ⌈a⌉₊ := Nat.cast_nonneg _
  rw [abs_le] at hlo hhi ⊢
  push_cast at hhi
  constructor <;> nlinarith only [hlo.1, hhi.2, hl, hu, hmn]

private theorem eventual_band_error_subset {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ}
    (h : StableDomain μ θ B) (t : ℝ≥0) {x δ ε : ℝ}
    (hx : 0 < x) (hδ : 0 < δ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      (offspringSeqLaw μ).toMeasure
        {ω | (weakLadderCount ω ⌊(n : ℝ) * (t : ℝ)⌋₊ : ℝ) ≤ x * (n : ℝ) / B n ∧
          δ * ((n : ℝ) * ε) <
            |(bandCount ω ⌊(n : ℝ) * (t : ℝ)⌋₊ (ε * B n) : ℝ) -
              (⌈ε * B n⌉₊ : ℝ) *
                (weakLadderCount ω ⌊(n : ℝ) * (t : ℝ)⌋₊ : ℝ)|} ≤
      (offspringSeqLaw μ).toMeasure
        {ω | ∃ N ∈ Finset.range (⌈(2 * x) * (n : ℝ) / B n⌉₊ + 1),
          (δ / 2) * ((n : ℝ) * ε) <
            |(∑ i ∈ Finset.range N, (clusterVisits ω (ε * B n) i : ℝ)) -
              (N : ℝ) * (⌈ε * B n⌉₊ : ℝ)|} := by
  have hBn := Survival.tendsto_B_div_n h
  have hsmall := hBn.eventually (gt_mem_nhds hx)
  have htwo : Tendsto (fun n : ℕ => (2 / (n : ℝ)) / ε) atTop (𝓝 0) := by
    simpa only [zero_div] using
      ((tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop).div_const ε :
        Tendsto (fun n : ℕ => (2 / (n : ℝ)) / ε) atTop (𝓝 (0 / ε)))
  have herrT := hBn.add htwo
  rw [add_zero] at herrT
  have herr := herrT.eventually (gt_mem_nhds (show (0 : ℝ) < δ / 2 by positivity))
  filter_upwards [eventually_ge_atTop 1, hsmall, herr] with n hn hsn hen
  have hB := h.pos n hn
  have hnR : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have ha := mul_pos hε hB
  have hr : 0 < (δ / 2) * ((n : ℝ) * ε) := by positivity
  have hsize : (⌈ε * B n⌉₊ : ℝ) + 1 ≤ (δ / 2) * ((n : ℝ) * ε) := by
    have hc := (Nat.ceil_lt_add_one ha.le).le
    have he : B n / (n : ℝ) + 2 / (n : ℝ) / ε =
        (ε * B n + 2) / ((n : ℝ) * ε) := by field_simp
    rw [he] at hen
    have hh := (div_lt_iff₀ (mul_pos hnR hε)).mp hen
    linarith
  have hone : 1 ≤ x * (n : ℝ) / B n := by
    apply (le_div_iff₀ hB).mpr
    have he := (div_lt_iff₀ hnR).mp hsn
    linarith
  apply measure_mono_ae
  filter_upwards [ae_epochsFinite μ h.critical h.nondegenerate] with ω hω
  intro hevent
  by_contra hnot
  have hsafe (N : ℕ) (hN : N ∈ Finset.range (⌈(2 * x) * (n : ℝ) / B n⌉₊ + 1)) :
      |(∑ i ∈ Finset.range N, (clusterVisits ω (ε * B n) i : ℝ)) -
        (N : ℝ) * (⌈ε * B n⌉₊ : ℝ)| ≤ (δ / 2) * ((n : ℝ) * ε) := by
    exact le_of_not_gt (fun hh => hnot ⟨N, hN, hh⟩)
  let k := ⌊(n : ℝ) * (t : ℝ)⌋₊
  let H := weakLadderCount ω k
  have hH : (H : ℝ) ≤ x * (n : ℝ) / B n := hevent.1
  have hceil : 2 * (x * (n : ℝ) / B n) ≤
      (⌈(2 * x) * (n : ℝ) / B n⌉₊ : ℝ) := by
    calc
      _ = (2 * x) * (n : ℝ) / B n := by ring
      _ ≤ _ := Nat.le_ceil _
  have hH1 : H + 1 ≤ ⌈(2 * x) * (n : ℝ) / B n⌉₊ := by
    have hreal : (H : ℝ) + 1 ≤ (⌈(2 * x) * (n : ℝ) / B n⌉₊ : ℝ) := by
      nlinarith only [hH, hone, hceil]
    exact_mod_cast hreal
  have hHmem : H ∈ Finset.range (⌈(2 * x) * (n : ℝ) / B n⌉₊ + 1) := by
    apply Finset.mem_range.mpr
    omega
  have hH1mem : H + 1 ∈ Finset.range (⌈(2 * x) * (n : ℝ) / B n⌉₊ + 1) :=
    Finset.mem_range.mpr (by omega)
  have hb := bandCount_error_le hω k ha (hsafe H hHmem) (hsafe (H + 1) hH1mem)
  have he := hevent.2
  change δ * ((n : ℝ) * ε) <
    |(bandCount ω k (ε * B n) : ℝ) - (⌈ε * B n⌉₊ : ℝ) * (H : ℝ)| at he
  nlinarith only [hb, he, hsize]

/-- **Stopped renewal error for the band count** (cutoff event `H_k ≤ x n/B_n`, `k = ⌊nt⌋`):
`bandCount ω k (ε B_n) ≈ ⌈ε B_n⌉ H_k` up to `δ n ε`, two limits. -/
theorem stopped_bandCount_error {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ}
    (h : StableDomain μ θ B) (t : ℝ≥0) {x δ : ℝ} (hx : 0 < x) (hδ : 0 < δ) :
    Tendsto (fun ε : ℝ =>
        limsup (fun n : ℕ => ((offspringSeqLaw μ : ProbabilityMeasure (ℕ → ℕ)) :
          Measure (ℕ → ℕ))
          {ω | (weakLadderCount ω ⌊(n : ℝ) * (t : ℝ)⌋₊ : ℝ) ≤ x * (n : ℝ) / B n ∧
            δ * ((n : ℝ) * ε) <
              |(bandCount ω ⌊(n : ℝ) * (t : ℝ)⌋₊ (ε * B n) : ℝ) -
                (⌈ε * B n⌉₊ : ℝ) * (weakLadderCount ω ⌊(n : ℝ) * (t : ℝ)⌋₊ : ℝ)|}) atTop)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hx' : 0 < 2 * x := mul_pos (by norm_num) hx
  have hd' : 0 < δ / 2 := by positivity
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (cluster_partialSum_maximal h hx' hd')
  · exact Eventually.of_forall fun _ => bot_le
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    exact limsup_le_limsup (eventual_band_error_subset h t hx hδ hε)

end BGW.StableTrees.DiscreteHeightApprox
