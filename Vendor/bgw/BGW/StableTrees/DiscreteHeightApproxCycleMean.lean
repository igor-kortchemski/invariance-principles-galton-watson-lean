/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.DiscreteHeightApproxCycleLaw

/-!
# Mean occupation of a weak ascending cycle

Integer gaps strictly below `a` are exactly the nonnegative integers below its
natural ceiling. The exact level mean and stopped restart give every cycle the
mean `⌈a⌉₊`, with no extra normalization constant.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal Classical
open BGW.StableTrees.DiscreteForest

namespace BGW.StableTrees.DiscreteHeightApprox

/-- The first-cycle band count is the sum of its integer-level counts. -/
theorem clusterVisits_zero_eq_sum_levels {ω : ℕ → ℕ} (hω : EpochsFinite ω) (a : ℝ) :
    clusterVisits ω a 0 = ∑ y ∈ Finset.range ⌈a⌉₊,
      ((Finset.Ico 0 (weakEpoch ω 1)).filter (fun u => reflGap ω u = (y : ℤ))).card := by
  let g (u : ℕ) := (reflGap ω u).toNat
  have hg (u : ℕ) : (g u : ℤ) = reflGap ω u := Int.toNat_of_nonneg (reflGap_nonneg ω u)
  calc
    _ = ((Finset.Ico 0 (weakEpoch ω 1)).filter
        (fun u => g u ∈ Finset.range ⌈a⌉₊)).card := by
      unfold clusterVisits
      rw [weakEpoch_zero]
      apply congrArg Finset.card
      apply Finset.filter_congr
      intro u hu
      have hun := (Finset.mem_Ico.mp hu).2
      rw [Finset.mem_range, Nat.lt_ceil]
      have hcast : (g u : ℝ) = (reflGap ω u : ℝ) := by exact_mod_cast hg u
      rw [hcast, reflGap_in_cycle hω (i := 0) (by simp) hun, weakEpoch_zero]
    _ = ∑ y ∈ Finset.range ⌈a⌉₊,
        ((Finset.Ico 0 (weakEpoch ω 1)).filter (fun u => g u = y)).card :=
      (Finset.sum_card_fiberwise_eq_card_filter _ _ g).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro y _
      apply congrArg Finset.card
      apply Finset.filter_congr
      intro u _
      have h := hg u
      omega

/-- Exact-level first-cycle counts are integrable; their integral is the nonzero value one. -/
theorem integrable_clusterLevel (μ : PMF ℕ) (hc : IsCritical μ) (hne : μ 1 ≠ 1) (y : ℕ) :
    Integrable (fun ω =>
      (((Finset.Ico 0 (weakEpoch ω 1)).filter (fun u => reflGap ω u = (y : ℤ))).card : ℝ))
      (offspringSeqLaw μ).toMeasure := by
  by_contra hn
  have he := clusterLevelMean μ hc hne y
  rw [integral_undef hn] at he
  exact zero_ne_one he

/-- The first-cycle band mean is its natural ceiling, for every real band. -/
private theorem clusterVisits_zero_mean (μ : PMF ℕ) (hc : IsCritical μ) (hne : μ 1 ≠ 1) (a : ℝ) :
    ∫ ω, (clusterVisits ω a 0 : ℝ) ∂(offspringSeqLaw μ).toMeasure = (⌈a⌉₊ : ℝ) := by
  have he : (fun ω => (clusterVisits ω a 0 : ℝ)) =ᵐ[(offspringSeqLaw μ).toMeasure]
      (fun ω => ∑ y ∈ Finset.range ⌈a⌉₊,
        (((Finset.Ico 0 (weakEpoch ω 1)).filter (fun u => reflGap ω u = (y : ℤ))).card : ℝ)) := by
    filter_upwards [ae_epochsFinite μ hc hne] with ω hω
    rw [clusterVisits_zero_eq_sum_levels hω, Nat.cast_sum]
  rw [integral_congr_ae he, integral_finsetSum]
  · simp only [clusterLevelMean μ hc hne, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul, mul_one]
  · intro y _
    exact integrable_clusterLevel μ hc hne y

/-- Cycle mean: `E V_i(a) = ⌈a⌉₊` for `a > 0`. -/
theorem clusterVisits_mean (μ : PMF ℕ) (hc : IsCritical μ) (hne : μ 1 ≠ 1) {a : ℝ} (ha : 0 < a)
    (i : ℕ) :
    ∫ ω, (clusterVisits ω a i : ℝ)
      ∂((offspringSeqLaw μ : ProbabilityMeasure (ℕ → ℕ)) : Measure (ℕ → ℕ)) = (⌈a⌉₊ : ℝ) := by
  -- The same identity holds for nonpositive bands; retain the frozen positivity premise.
  have _ha := ha
  have he := congrArg (fun ν : Measure ℕ => ∫ k : ℕ, (k : ℝ) ∂ν)
    (map_clusterVisits_eq_zero μ hc hne a i)
  rw [integral_map (measurable_clusterVisits a i).aemeasurable
      (measurable_of_countable (fun k : ℕ => (k : ℝ))).aestronglyMeasurable,
    integral_map (measurable_clusterVisits a 0).aemeasurable
      (measurable_of_countable (fun k : ℕ => (k : ℝ))).aestronglyMeasurable] at he
  rw [he]
  exact clusterVisits_zero_mean μ hc hne a

end BGW.StableTrees.DiscreteHeightApprox
