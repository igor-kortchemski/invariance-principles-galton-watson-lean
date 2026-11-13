/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.DiscreteHeightApproxGreen

/-!
# Finite second moments of cycle occupations

Ordered pairs of visits reduce level second moments to the killed-gap Green
kernel. Finite bands are finite sums of level counts; stopped restart transfers
square integrability from the first cycle to every cycle.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal Classical
open BGW.StableTrees.DiscreteForest

namespace BGW.StableTrees.DiscreteHeightApprox

private def orderPair (p : ℕ × ℕ) : Bool × (ℕ × ℕ) :=
  if p.1 ≤ p.2 then (false, p.1, p.2 - p.1) else (true, p.2, p.1 - p.2)

private theorem orderPair_injective : Function.Injective orderPair := by
  intro ⟨n, m⟩ ⟨n', m'⟩ he
  unfold orderPair at he
  split_ifs at he <;> simp only [Prod.mk.injEq, Bool.false_eq_true, Bool.true_eq_false,
    false_and] at he <;> apply Prod.ext <;> omega

private theorem level_pair_eq_restart (y n k : ℕ) (hy : 0 < y) :
    negativeLevelEvent y n ∩ negativeLevelEvent y (n + k) =
      negativeLevelEvent y n ∩ shiftSeq n ⁻¹' killedGapEvent y y k := by
  ext ω
  constructor
  · rintro ⟨hn, hnk⟩
    have hnpos : 0 < n := by
      by_contra h
      have he : n = 0 := by omega
      have hw := hn.1
      rw [he] at hw
      simp only [walk, Finset.range_zero, Finset.sum_empty] at hw
      omega
    refine ⟨hn, ?_, fun u hu => ?_⟩
    · rw [walk_shiftSeq, hnk.1, hn.1]
      ring
    · rw [walk_shiftSeq, hn.1]
      have hneg := hnk.2 (n + u) (by omega) (by omega)
      omega
  · rintro ⟨hn, hk⟩
    refine ⟨hn, ?_, fun u hu huk => ?_⟩
    · have hw := hk.1
      rw [walk_shiftSeq, hn.1] at hw
      omega
    · by_cases hun : u ≤ n
      · exact hn.2 u hu hun
      · have ht := hk.2 (u - n) (by omega)
        rw [walk_shiftSeq, Nat.add_sub_of_le (by omega : n ≤ u), hn.1] at ht
        omega

private theorem negativeLevel_restart_mass (μ : PMF ℕ) (y n : ℕ) {A : Set (ℕ → ℕ)}
    (hA : MeasurableSet A) :
    (offspringSeqLaw μ).toMeasure (negativeLevelEvent y n ∩ shiftSeq n ⁻¹' A) =
      (offspringSeqLaw μ).toMeasure (negativeLevelEvent y n) *
        (offspringSeqLaw μ).toMeasure A := by
  have hN : IsSeqStoppingTime (fun _ : ℕ → ℕ => (n : ℕ∞)) :=
    fun _ _ _ hm _ => ⟨hm, Iff.rfl⟩
  have hfin : ∀ᵐ ω ∂(offspringSeqLaw μ).toMeasure, (n : ℕ∞) ≠ ⊤ := by simp
  have h := stoppedRestart μ (fun _ => (n : ℕ∞)) hN hfin
    (preStopped_negativeLevelEvent y n) hA
  have he : {ω : ℕ → ℕ | ∃ m : ℕ, (n : ℕ∞) = m ∧ shiftSeq m ω ∈ A} =
      shiftSeq n ⁻¹' A := by
    ext ω
    constructor
    · rintro ⟨m, hm, hA⟩
      have he : n = m := ENat.natCast_inj.mp hm
      subst m
      exact hA
    · intro hA
      exact ⟨n, rfl, hA⟩
  rwa [he] at h

private theorem ordered_level_pair_mass (μ : PMF ℕ) (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    {y : ℕ} (hy : 0 < y) :
    (∑' n : ℕ, ∑' k : ℕ, (offspringSeqLaw μ).toMeasure
      (negativeLevelEvent y n ∩ negativeLevelEvent y (n + k))) = killedGapGreen μ y y := by
  simp_rw [level_pair_eq_restart y _ _ hy,
    negativeLevel_restart_mass μ y _ (measurableSet_killedGapEvent y y _),
    ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_mul_right, tsum_negativeLevelEvent_mass μ hc hne y, one_mul]
  rfl

private noncomputable def levelIndicator (y n : ℕ) (ω : ℕ → ℕ) : ℝ≥0∞ :=
  (negativeLevelEvent y n).indicator (fun _ => 1) ω

private theorem measurable_levelIndicator (y n : ℕ) : Measurable (levelIndicator y n) :=
  measurable_const.indicator (measurableSet_negativeLevelEvent y n)

private theorem lintegral_levelIndicator_mul (μ : PMF ℕ) (y n m : ℕ) :
    (∫⁻ ω, levelIndicator y n ω * levelIndicator y m ω ∂(offspringSeqLaw μ).toMeasure) =
      (offspringSeqLaw μ).toMeasure (negativeLevelEvent y n ∩ negativeLevelEvent y m) := by
  have he : (fun ω => levelIndicator y n ω * levelIndicator y m ω) =
      (negativeLevelEvent y n ∩ negativeLevelEvent y m).indicator (fun _ => 1) := by
    funext ω
    by_cases hn : ω ∈ negativeLevelEvent y n <;> by_cases hm : ω ∈ negativeLevelEvent y m <;>
      simp [levelIndicator, hn, hm]
  rw [he]
  exact lintegral_indicator_one ((measurableSet_negativeLevelEvent y n).inter
    (measurableSet_negativeLevelEvent y m))

private def orderedPairWithDiagonal : (ℕ × ℕ) ⊕ ℕ → Bool × (ℕ × ℕ)
  | Sum.inl p => orderPair p
  | Sum.inr n => (true, n, 0)

private theorem orderedPairWithDiagonal_injective : Function.Injective orderedPairWithDiagonal := by
  intro p q he
  rcases p with p | n <;> rcases q with q | m
  · exact congrArg Sum.inl (orderPair_injective he)
  · rcases p with ⟨a, b⟩
    change orderPair (a, b) = (true, m, 0) at he
    unfold orderPair at he
    split_ifs at he <;> simp only [Prod.mk.injEq, Bool.false_eq_true, false_and] at he; omega
  · rcases q with ⟨a, b⟩
    change (true, n, 0) = orderPair (a, b) at he
    unfold orderPair at he
    split_ifs at he <;> simp only [Prod.mk.injEq, Bool.true_eq_false, false_and] at he; omega
  · apply congrArg Sum.inr
    exact congrArg (fun p : Bool × (ℕ × ℕ) => p.2.1) he

private theorem tsum_sq_add_le_ordered (f : ℕ → ℝ≥0∞) (hf : ∀ n, f n * f n = f n) :
    (∑' n, f n) ^ 2 + ∑' n, f n ≤ 2 * ∑' n : ℕ, ∑' k : ℕ, f n * f (n + k) := by
  let F (q : Bool × (ℕ × ℕ)) := f q.2.1 * f (q.2.1 + q.2.2)
  let K : (ℕ × ℕ) ⊕ ℕ → ℝ≥0∞ := Sum.elim (fun p => f p.1 * f p.2) f
  have he (p : (ℕ × ℕ) ⊕ ℕ) : K p = F (orderedPairWithDiagonal p) := by
    rcases p with ⟨n, m⟩ | n
    · change f n * f m = F (orderPair (n, m))
      unfold F orderPair
      split_ifs with h
      · rw [Nat.add_sub_of_le h]
      · rw [Nat.add_sub_of_le (by omega : m ≤ n), mul_comm]
    · change f n = f n * f (n + 0)
      simpa only [Nat.add_zero] using (hf n).symm
  have hprod : (∑' n, f n) ^ 2 = ∑' p : ℕ × ℕ, f p.1 * f p.2 := by
    calc
      _ = (∑' n, f n) * ∑' n, f n := pow_two _
      _ = ∑' n, f n * ∑' m, f m := ENNReal.tsum_mul_right.symm
      _ = ∑' n, ∑' m, f n * f m := tsum_congr fun n => ENNReal.tsum_mul_left.symm
      _ = _ := (ENNReal.tsum_prod' (f := fun p : ℕ × ℕ => f p.1 * f p.2)).symm
  have hsum : ∑' p, K p = (∑' n, f n) ^ 2 + ∑' n, f n := by
    rw [ENNReal.summable.tsum_sum ENNReal.summable, hprod]
    rfl
  rw [← hsum]
  calc
    _ = ∑' p, F (orderedPairWithDiagonal p) := tsum_congr he
    _ ≤ ∑' q, F q :=
      ENNReal.tsum_comp_le_tsum_of_injective orderedPairWithDiagonal_injective F
    _ = _ := by
      rw [ENNReal.tsum_prod']
      simp only [F, tsum_bool, ENNReal.tsum_prod', two_mul]

/-- The positive-level occupation second moment plus its mean is at most twice the killed
Green diagonal. -/
theorem lintegral_levelOccupation_sq_add_le (μ : PMF ℕ) (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    {y : ℕ} (hy : 0 < y) :
    (∫⁻ ω, (levelOccupation y ω) ^ 2 ∂(offspringSeqLaw μ).toMeasure) + 1 ≤
      2 * killedGapGreen μ y y := by
  have hmsq : Measurable (fun ω => (levelOccupation y ω) ^ 2) :=
    (measurable_levelOccupation y).pow_const 2
  rw [← lintegral_levelOccupation μ hc hne y, ← lintegral_add_left hmsq]
  calc
    _ ≤ ∫⁻ ω, 2 * ∑' n : ℕ, ∑' k : ℕ,
          levelIndicator y n ω * levelIndicator y (n + k) ω ∂(offspringSeqLaw μ).toMeasure := by
      apply lintegral_mono
      intro ω
      apply tsum_sq_add_le_ordered (fun n => levelIndicator y n ω)
      intro n
      by_cases hmem : ω ∈ negativeLevelEvent y n <;> simp [levelIndicator, hmem]
    _ = 2 * ∑' n : ℕ, ∑' k : ℕ, (offspringSeqLaw μ).toMeasure
        (negativeLevelEvent y n ∩ negativeLevelEvent y (n + k)) := by
      have hmf (n : ℕ) : Measurable (fun ω : ℕ → ℕ =>
          ∑' k : ℕ, levelIndicator y n ω * levelIndicator y (n + k) ω) :=
        Measurable.tsum fun k =>
          (measurable_levelIndicator y n).mul (measurable_levelIndicator y (n + k))
      rw [lintegral_const_mul' _ _ (by norm_num)]
      congr 1
      rw [lintegral_tsum (fun n => (hmf n).aemeasurable)]
      apply tsum_congr
      intro n
      rw [lintegral_tsum (f := fun k (ω : ℕ → ℕ) =>
        levelIndicator y n ω * levelIndicator y (n + k) ω)
        (fun k => ((measurable_levelIndicator y n).mul
          (measurable_levelIndicator y (n + k))).aemeasurable)]
      exact tsum_congr fun k => lintegral_levelIndicator_mul μ y n (n + k)
    _ = _ := by rw [ordered_level_pair_mass μ hc hne hy]

/-- The zero-gap occupation consists of the time-zero visit alone, on every sequence. -/
theorem levelOccupation_zero_eq_one (ω : ℕ → ℕ) : levelOccupation 0 ω = 1 := by
  unfold levelOccupation
  rw [tsum_eq_single 0]
  · simp [negativeLevelEvent, NegativePrefix, walk]
  · intro n hn
    apply Set.indicator_of_notMem
    intro h
    have hneg := h.2 n (by omega) le_rfl
    rw [h.1] at hneg
    norm_num at hneg

/-- Every integer-level occupation has a finite second moment, without a variance assumption. -/
theorem lintegral_levelOccupation_sq_lt_top (μ : PMF ℕ) (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (y : ℕ) : (∫⁻ ω, (levelOccupation y ω) ^ 2 ∂(offspringSeqLaw μ).toMeasure) < ∞ := by
  rcases y with _ | y
  · simp only [levelOccupation_zero_eq_one, one_pow, lintegral_const, measure_univ, mul_one]
    exact ENNReal.one_lt_top
  · exact (le_self_add.trans
      (lintegral_levelOccupation_sq_add_le μ hc hne (Nat.succ_pos y))).trans_lt
      (ENNReal.mul_lt_top (by norm_num) (killedGapGreen_lt_top μ hc hne (y + 1) (y + 1)))

/-- The square of a first-cycle integer-level count is integrable. -/
theorem integrable_clusterLevel_sq (μ : PMF ℕ) (hc : IsCritical μ) (hne : μ 1 ≠ 1) (y : ℕ) :
    Integrable (fun ω =>
      ((((Finset.Ico 0 (weakEpoch ω 1)).filter (fun u => reflGap ω u = (y : ℤ))).card : ℝ)) ^ 2)
      (offspringSeqLaw μ).toMeasure := by
  refine ⟨(integrable_clusterLevel μ hc hne y).aestronglyMeasurable.pow 2,
    (hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun ω => sq_nonneg _)).mpr ?_⟩
  have he : (fun ω => ENNReal.ofReal
      (((((Finset.Ico 0 (weakEpoch ω 1)).filter (fun u => reflGap ω u = (y : ℤ))).card : ℝ)) ^ 2))
      =ᵐ[(offspringSeqLaw μ).toMeasure] (fun ω => (levelOccupation y ω) ^ 2) := by
    filter_upwards [ae_epochsFinite μ hc hne] with ω hω
    rw [levelOccupation_eq_card hω]
    simp
  rw [lintegral_congr_ae he]
  exact lintegral_levelOccupation_sq_lt_top μ hc hne y

private theorem integrable_clusterVisits_zero_sq (μ : PMF ℕ) (hc : IsCritical μ)
    (hne : μ 1 ≠ 1) (a : ℝ) :
    Integrable (fun ω => (clusterVisits ω a 0 : ℝ) ^ 2) (offspringSeqLaw μ).toMeasure := by
  have hm (y : ℕ) : MemLp (fun ω =>
      (((Finset.Ico 0 (weakEpoch ω 1)).filter (fun u => reflGap ω u = (y : ℤ))).card : ℝ))
      2 (offspringSeqLaw μ).toMeasure :=
    (memLp_two_iff_integrable_sq (integrable_clusterLevel μ hc hne y).aestronglyMeasurable).mpr
      (integrable_clusterLevel_sq μ hc hne y)
  have hsum := memLp_finsetSum (Finset.range ⌈a⌉₊) (fun y _ => hm y)
  have he : (fun ω => ∑ y ∈ Finset.range ⌈a⌉₊,
      (((Finset.Ico 0 (weakEpoch ω 1)).filter (fun u => reflGap ω u = (y : ℤ))).card : ℝ))
      =ᵐ[(offspringSeqLaw μ).toMeasure] (fun ω => (clusterVisits ω a 0 : ℝ)) := by
    filter_upwards [ae_epochsFinite μ hc hne] with ω hω
    rw [clusterVisits_zero_eq_sum_levels hω, Nat.cast_sum]
  have hmem : MemLp (fun ω => (clusterVisits ω a 0 : ℝ)) 2 (offspringSeqLaw μ).toMeasure :=
    hsum.ae_eq he
  exact (memLp_two_iff_integrable_sq hmem.aestronglyMeasurable).mp hmem

/-- **Square-integrability supplier** (Sol audit finding 1).  Lean's Bochner integral is
totalized to `0` off integrable functions, so finite second moments are supplied explicitly.
Proof: finite killed-walk Green entries and ordered pairs of level visits. -/
theorem integrable_clusterVisits_sq (μ : PMF ℕ)
    (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    {a : ℝ} (ha : 0 < a) (i : ℕ) :
    Integrable (fun ω => (clusterVisits ω a i : ℝ) ^ 2)
      ((offspringSeqLaw μ : ProbabilityMeasure (ℕ → ℕ)) :
        Measure (ℕ → ℕ)) := by
  have _ha := ha
  have hzero := integrable_clusterVisits_zero_sq μ hc hne a
  have hm (j : ℕ) : AEStronglyMeasurable (fun k : ℕ => (k : ℝ) ^ 2)
      ((offspringSeqLaw μ).toMeasure.map (fun ω => clusterVisits ω a j)) :=
    (measurable_of_countable _).aestronglyMeasurable
  have hmap : Integrable (fun k : ℕ => (k : ℝ) ^ 2)
      ((offspringSeqLaw μ).toMeasure.map (fun ω => clusterVisits ω a 0)) :=
    (integrable_map_measure (hm 0) (measurable_clusterVisits a 0).aemeasurable).mpr hzero
  rw [← map_clusterVisits_eq_zero μ hc hne a i] at hmap
  exact (integrable_map_measure (hm i) (measurable_clusterVisits a i).aemeasurable).mp hmap

/-- The real exact-level second moment plus its mean is at most twice the Green diagonal. -/
theorem integral_clusterLevel_sq_add_one_le (μ : PMF ℕ) (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    {y : ℕ} (hy : 0 < y) :
    (∫ ω, ((((Finset.Ico 0 (weakEpoch ω 1)).filter
        (fun u => reflGap ω u = (y : ℤ))).card : ℝ)) ^ 2
        ∂(offspringSeqLaw μ).toMeasure) + 1 ≤
      2 * (killedGapGreen μ y y).toReal := by
  have hsq : (∫ ω, ((((Finset.Ico 0 (weakEpoch ω 1)).filter
        (fun u => reflGap ω u = (y : ℤ))).card : ℝ)) ^ 2 ∂(offspringSeqLaw μ).toMeasure) =
      (∫⁻ ω, (levelOccupation y ω) ^ 2 ∂(offspringSeqLaw μ).toMeasure).toReal := by
    rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun ω => sq_nonneg _)
      (integrable_clusterLevel_sq μ hc hne y).aestronglyMeasurable]
    congr 1
    apply lintegral_congr_ae
    filter_upwards [ae_epochsFinite μ hc hne] with ω hω
    rw [levelOccupation_eq_card hω]
    simp
  have hfinite := (lintegral_levelOccupation_sq_lt_top μ hc hne y).ne
  have hR := ENNReal.toReal_mono (ENNReal.mul_ne_top (by simp)
    (killedGapGreen_lt_top μ hc hne y y).ne) (lintegral_levelOccupation_sq_add_le μ hc hne hy)
  rw [ENNReal.toReal_add hfinite ENNReal.one_ne_top, ENNReal.toReal_one,
    ENNReal.toReal_mul, ENNReal.toReal_ofNat, ← hsq] at hR
  exact hR

end BGW.StableTrees.DiscreteHeightApprox
