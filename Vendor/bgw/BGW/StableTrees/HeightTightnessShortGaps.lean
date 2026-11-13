/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.HeightTightnessRenewalBound
public import BGW.StableTrees.HeightTightnessPassage

/-!
# Uniform short-gap estimates

Each regenerated gap has the first-upcrossing cutoff probability. A finite union
bound and the small-time first-hit estimate control all of the first `L` gaps.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal Classical
open BGW.StableTrees.DiscreteForest
namespace BGW.StableTrees.HeightTightness

/-- A first crossing occurs by `m` exactly when that height is reached by `m`. -/
theorem heightUpcrossingStop_le_natCast_iff (q m : ℕ) (ω : ℕ → ℕ) :
    heightUpcrossingStop q ω ≤ (m : ℕ∞) ↔ ∃ k ≤ m, q ≤ forestHeight ω k := by
  constructor
  · intro hm
    have hfin := ne_top_of_le_ne_top (ENat.natCast_ne_top m) hm
    obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp hfin
    refine ⟨k, ?_, ((heightUpcrossingStop_eq_natCast_iff q k ω).mp hk.symm).1⟩
    exact ENat.natCast_le_natCast.mp (hk ▸ hm)
  · rintro ⟨k, hkm, hq⟩
    exact (iInf_le_of_le ⟨k, hq⟩ le_rfl).trans (ENat.natCast_le_natCast.mpr hkm)

/-- Every regenerated gap has the first-height-hit probability at a finite cutoff. -/
theorem heightRegenerationGap_probability (μ : PMF ℕ) (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (q i m : ℕ) :
    (offspringSeqLaw μ).toMeasure.real {ω | heightRegenerationGap q i ω ≤ m} =
      (offspringSeqLaw μ).toMeasure.real {ω | ∃ k ≤ m, q ≤ forestHeight ω k} := by
  have he := congrArg (fun ν : Measure ℕ => ν (Iic m))
    (map_heightRegenerationGap μ hc hne q i)
  rw [Measure.map_apply (measurable_heightRegenerationGap q i) measurableSet_Iic,
    Measure.map_apply (f := fun ω => (heightUpcrossingStop q ω).toNat)
      ((measurable_of_countable ENat.toNat).comp (measurable_heightUpcrossingStop q))
      measurableSet_Iic] at he
  have ha : {ω | (heightUpcrossingStop q ω).toNat ≤ m} =ᵐ[(offspringSeqLaw μ).toMeasure]
      {ω | ∃ k ≤ m, q ≤ forestHeight ω k} := by
    filter_upwards [ae_heightUpcrossingStop_ne_top μ hc hne q] with ω hω
    apply propext
    rw [← heightUpcrossingStop_le_natCast_iff]
    exact ENat.natCast_le_natCast.symm.trans (by rw [ENat.natCast_toNat hω])
  change (offspringSeqLaw μ).toMeasure {ω | heightRegenerationGap q i ω ≤ m} =
    (offspringSeqLaw μ).toMeasure {ω | (heightUpcrossingStop q ω).toNat ≤ m} at he
  exact congrArg ENNReal.toReal (he.trans (measure_congr ha))

/-- A finite union bound for short gaps among the first `L` regenerated crossings. -/
theorem heightRegenerationGap_union_probability_le (μ : PMF ℕ) (hc : IsCritical μ)
    (hne : μ 1 ≠ 1) (q L m : ℕ) :
    (offspringSeqLaw μ).toMeasure.real {ω | ∃ i < L, heightRegenerationGap q i ω ≤ m} ≤
      (L : ℝ) * (offspringSeqLaw μ).toMeasure.real
        {ω | ∃ k ≤ m, q ≤ forestHeight ω k} := by
  have he : {ω | ∃ i < L, heightRegenerationGap q i ω ≤ m} =
      ⋃ i ∈ Finset.range L, {ω | heightRegenerationGap q i ω ≤ m} := by
    ext ω
    simp only [mem_ofPred_eq, mem_iUnion, Finset.mem_range, exists_prop]
  rw [he]
  exact (measureReal_biUnion_finset_le _ _).trans_eq (by
    simp only [heightRegenerationGap_probability μ hc hne, Finset.sum_const,
      Finset.card_range, nsmul_eq_mul])

/-- Uniform eventual small-time control for all of the first finitely many gaps. -/
theorem exists_pos_eventually_short_gap_probability_small {μ : PMF ℕ} {θ : ℝ}
    {B : ℕ → ℝ} (h : StableDomain μ θ B) {η ε : ℝ} (hη : 0 < η) (hε : 0 < ε) (L : ℕ) :
    ∃ x : ℝ, 0 < x ∧ ∀ᶠ n : ℕ in atTop,
      (offspringSeqLaw μ).toMeasure.real
        {ω | ∃ i < L, heightRegenerationGap ⌊η * (n : ℝ) / B n⌋₊ i ω ≤
          ⌊(n : ℝ) * x⌋₊} ≤ ε := by
  obtain ⟨x, hx, hsmall⟩ := exists_pos_eventually_height_hit_probability_small h hη
    (show 0 < ε / (L + 1) by positivity)
  refine ⟨x, hx, hsmall.mono fun n hn => ?_⟩
  have hb := heightRegenerationGap_union_probability_le μ h.critical h.nondegenerate
    ⌊η * (n : ℝ) / B n⌋₊ L ⌊(n : ℝ) * x⌋₊
  refine hb.trans ((mul_le_mul_of_nonneg_left hn (Nat.cast_nonneg L)).trans ?_)
  have hden : (0 : ℝ) < L + 1 := by positivity
  rw [← mul_div_assoc]
  apply (div_le_iff₀ hden).mpr
  nlinarith [Nat.cast_nonneg (α := ℝ) L]

end BGW.StableTrees.HeightTightness
