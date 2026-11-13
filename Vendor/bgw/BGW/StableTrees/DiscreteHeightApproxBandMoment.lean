/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.DiscreteHeightApproxRenewalScale
import Mathlib.Algebra.Order.Chebyshev

/-!
# A sharp finite-band second moment

The zero level contributes exactly one. Cauchy--Schwarz on the positive levels,
and the diagonal-corrected Green estimate, give the finite-band bound.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal Classical
open BGW.StableTrees.DiscreteForest

namespace BGW.StableTrees.DiscreteHeightApprox

private noncomputable def levelCount (y : ℕ) (ω : ℕ → ℕ) : ℝ :=
  (((Finset.Ico 0 (weakEpoch ω 1)).filter (fun u => reflGap ω u = (y : ℤ))).card : ℝ)

private theorem levelCount_zero {ω : ℕ → ℕ} (hω : EpochsFinite ω) : levelCount 0 ω = 1 := by
  have he := levelOccupation_eq_card hω 0
  rw [levelOccupation_zero_eq_one] at he
  have he' := congrArg ENNReal.toReal he
  simpa [levelCount] using he'.symm

/-- A finite band has second moment at most its mean plus the squared positive-level
count times twice the weak ladder renewal function. -/
theorem integral_clusterVisits_sq_le_renewal (μ : PMF ℕ) (hc : IsCritical μ)
    (hne : μ 1 ≠ 1) {a : ℝ} (ha : 0 < a) :
    (∫ ω, (clusterVisits ω a 0 : ℝ) ^ 2 ∂(offspringSeqLaw μ).toMeasure) ≤
      (⌈a⌉₊ : ℝ) + 2 * ((⌈a⌉₊ - 1 : ℕ) : ℝ) ^ 2 *
        (weakLadderRenewal μ ⌈a⌉₊).toReal := by
  let m := ⌈a⌉₊
  let k := m - 1
  let L := levelCount
  let S (ω : ℕ → ℕ) : ℝ := ∑ j ∈ Finset.range k, L (j + 1) ω
  let Q (ω : ℕ → ℕ) : ℝ := ∑ j ∈ Finset.range k, (L (j + 1) ω) ^ 2
  let W := (weakLadderRenewal μ m).toReal
  have hm : 0 < m := Nat.ceil_pos.mpr ha
  have hmk : m = k + 1 := by dsimp [k]; omega
  have hL (y : ℕ) : Integrable (L y) (offspringSeqLaw μ).toMeasure :=
    integrable_clusterLevel μ hc hne y
  have hL2 (y : ℕ) : Integrable (fun ω => (L y ω) ^ 2) (offspringSeqLaw μ).toMeasure :=
    integrable_clusterLevel_sq μ hc hne y
  have hS : Integrable S (offspringSeqLaw μ).toMeasure :=
    integrable_finsetSum _ (fun j _ => hL (j + 1))
  have hQ : Integrable Q (offspringSeqLaw μ).toMeasure :=
    integrable_finsetSum _ (fun j _ => hL2 (j + 1))
  have hS2 : Integrable (fun ω => S ω ^ 2) (offspringSeqLaw μ).toMeasure := by
    have hmem (y : ℕ) : MemLp (L y) 2 (offspringSeqLaw μ).toMeasure :=
      (memLp_two_iff_integrable_sq (hL y).aestronglyMeasurable).mpr (hL2 y)
    have hs := memLp_finsetSum (Finset.range k) (fun j _ => hmem (j + 1))
    exact (memLp_two_iff_integrable_sq hs.aestronglyMeasurable).mp hs
  have hES : ∫ ω, S ω ∂(offspringSeqLaw μ).toMeasure = (k : ℝ) := by
    rw [integral_finsetSum _ (fun j _ => hL (j + 1))]
    simp only [L, levelCount, clusterLevelMean μ hc hne, Finset.sum_const,
      Finset.card_range, nsmul_eq_mul, mul_one]
  have hEQ : (∫ ω, Q ω ∂(offspringSeqLaw μ).toMeasure) + (k : ℝ) ≤ 2 * (k : ℝ) * W := by
    have hlevel (j : ℕ) (hj : j ∈ Finset.range k) :
        (∫ ω, (L (j + 1) ω) ^ 2 ∂(offspringSeqLaw μ).toMeasure) + 1 ≤ 2 * W := by
      have hb := integral_clusterLevel_sq_add_one_le μ hc hne (Nat.succ_pos j)
      rw [killedGapGreen_diag_eq_renewal μ hc hne] at hb
      have hjm : j + 1 ≤ m := by have := Finset.mem_range.mp hj; omega
      have hmon := ENNReal.toReal_mono (weakLadderRenewal_lt_top μ hc hne m).ne
        (weakLadderRenewal_mono μ hjm)
      exact hb.trans (mul_le_mul_of_nonneg_left hmon (by norm_num))
    have hs := Finset.sum_le_sum hlevel
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul, mul_one] at hs
    rw [integral_finsetSum _ (fun j _ => hL2 (j + 1))]
    simpa only [mul_comm (k : ℝ), mul_assoc] using hs
  have hCS : (∫ ω, S ω ^ 2 ∂(offspringSeqLaw μ).toMeasure) ≤
      (k : ℝ) * ∫ ω, Q ω ∂(offspringSeqLaw μ).toMeasure := by
    rw [← integral_const_mul]
    apply integral_mono hS2 (hQ.const_mul _)
    intro ω
    simpa only [S, Q, Finset.card_range] using
      (sq_sum_le_card_mul_sum_sq (s := Finset.range k) (f := fun j => L (j + 1) ω))
  have hV : (fun ω => (clusterVisits ω a 0 : ℝ) ^ 2) =ᵐ[(offspringSeqLaw μ).toMeasure]
      (fun ω => 1 + 2 * S ω + S ω ^ 2) := by
    filter_upwards [ae_epochsFinite μ hc hne] with ω hω
    have he := clusterVisits_zero_eq_sum_levels hω a
    have he' : (clusterVisits ω a 0 : ℝ) = 1 + S ω := by
      rw [he, Nat.cast_sum]
      change (∑ y ∈ Finset.range m, L y ω) = _
      rw [hmk, Finset.sum_range_succ']
      rw [show L 0 ω = 1 from levelCount_zero hω]
      dsimp only [S]
      ring
    rw [he']
    ring
  have hEV : (∫ ω, (clusterVisits ω a 0 : ℝ) ^ 2 ∂(offspringSeqLaw μ).toMeasure) =
      1 + 2 * (k : ℝ) + ∫ ω, S ω ^ 2 ∂(offspringSeqLaw μ).toMeasure := by
    have hsum : Integrable (fun ω => 1 + 2 * S ω) (offspringSeqLaw μ).toMeasure :=
      (integrable_const 1).add (hS.const_mul 2)
    rw [integral_congr_ae hV, integral_add hsum hS2,
      integral_add (integrable_const 1) (hS.const_mul 2), integral_const_mul, hES]
    simp
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hkk : (k : ℝ) ≤ (k : ℝ) ^ 2 := by
    rcases k with _ | k
    · norm_num
    · have : (1 : ℝ) ≤ (k + 1 : ℕ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le k)
      nlinarith
  have hmul := mul_le_mul_of_nonneg_left hEQ hk
  have hmR : (m : ℝ) = (k : ℝ) + 1 := by exact_mod_cast hmk
  change _ ≤ (m : ℝ) + 2 * (k : ℝ) ^ 2 * W
  nlinarith only [hEV, hCS, hmul, hkk, hmR]

end BGW.StableTrees.DiscreteHeightApprox
