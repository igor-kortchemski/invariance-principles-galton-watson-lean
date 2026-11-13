/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.Probability.SeparableRepresentationBlocks
public import BGW.Probability.SeparableRepresentationReduction
public import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli

import BGW.Probability.SkorokhodRepresentationPartitions

/-!
# Dudley's representation theorem on separable spaces

A single uniform variable is shared by all the conditional couplings. At partition level `k`, a
different-cell event outside one universal null set implies either that this variable exceeds
`1 - 2 ^ (-k)` or that the limiting random variable lies outside a fixed finite family of cells.
These events are summable in `k`. Borel--Cantelli therefore gives small common-cell distance at all
sufficiently large times, hence almost-sure convergence.

## References

* R. M. Dudley, "Distances of probability measures and random variables", Ann. Math. Statist. 39
  (1968), 1563--1572.
* R. M. Dudley, *Real Analysis and Probability*, Cambridge University Press, 2002,
  Theorem 11.7.2.
-/

@[expose] public section

open Filter MeasureTheory Set TopologicalSpace ProbabilityTheory
open scoped Topology ProbabilityTheory ENNReal unitInterval

universe u

namespace BGW.Probability

/-- Dudley's representation theorem in the metric case, with the augmented sample space
`(S × unitInterval) × (ℕ → S)`. -/
theorem exists_probabilitySpace_tendsto_ae_of_tendsto_metric {S : Type u} [MetricSpace S]
    [TopologicalSpace.SeparableSpace S] [MeasurableSpace S] [BorelSpace S]
    {P : ℕ → ProbabilityMeasure S} {Q : ProbabilityMeasure S} (h : Tendsto P atTop (𝓝 Q)) :
    ∃ (Ω : Type u) (_ : MeasurableSpace Ω) (μ : Measure Ω) (_ : IsProbabilityMeasure μ)
      (X : ℕ → Ω → S) (Y : Ω → S),
      (∀ n, Measurable (X n)) ∧ Measurable Y ∧
      (∀ n, Measure.map (X n) μ = (P n : Measure S)) ∧
      Measure.map Y μ = (Q : Measure S) ∧
      ∀ᵐ ω ∂μ, Tendsto (fun n => X n ω) atTop (𝓝 (Y ω)) := by
  classical
  let _ : Nonempty S := Q.nonempty
  have hpart (k : ℕ) : ∃ A : ℕ → Set S,
      (∀ j, MeasurableSet (A j)) ∧ Pairwise (Function.onFun Disjoint A) ∧
      (⋃ j, A j) = univ ∧ (∀ j, (Q : Measure S) (frontier (A j)) = 0) ∧
      ∀ j, ∀ x ∈ A j, ∀ y ∈ A j, dist x y < (2⁻¹ : ℝ) ^ k := by
    exact exists_continuity_partition (Q : Measure S) (pow_pos (by norm_num) _)
  choose A hmeas hdisj hcover hnull hmesh using hpart
  choose M hM using fun k => exists_finite_cell_union (Q : Measure S)
    (hmeas k) (hdisj k) (hcover k) k
  obtain ⟨N, _hNmono, hkN, hN⟩ := exists_strictMono_block_thresholds h hnull M
  let level : ℕ → ℕ := fun n => Nat.findGreatest (fun k => N k ≤ n) n
  have hNlevel {n : ℕ} (hn : N 0 ≤ n) : N (level n) ≤ n := by
    unfold level
    exact Nat.findGreatest_spec (P := fun k => N k ≤ n) (m := 0) (n := n)
      (Nat.zero_le n) hn
  have hlevel : Tendsto level atTop atTop := by
    apply tendsto_atTop.2
    intro k
    filter_upwards [eventually_ge_atTop (N k)] with n hn
    exact Nat.le_findGreatest ((hkN k).trans hn) hn
  obtain ⟨ρ, hρ, hXlaw, hbase, hcoupling⟩ := exists_uniform_coupling_of_partitions
    (fun n => (P n : Measure S)) (Q : Measure S) (fun n => A (level n))
    (fun n => hmeas (level n)) (fun n => hdisj (level n)) (fun n => hcover (level n))
  let _ : IsProbabilityMeasure ρ := hρ
  let G : ℕ → ℕ → Set ((S × I) × (ℕ → S)) := fun n i => {z |
    z.1.1 ∈ A (level n) i ∧
    z.1.2 < cellStayProbability (P n : Measure S) (Q : Measure S) (A (level n)) i ∧
    partitionIndex (A (level n)) (hcover (level n)) z.1.1 ≠
      partitionIndex (A (level n)) (hcover (level n)) (z.2 n)}
  let Z0 : ℕ → ℕ → Set ((S × I) × (ℕ → S)) := fun k i => {z |
    z.1.1 ∈ A k i ∧ (Q : Measure S) (A k i) = 0}
  let Z : Set ((S × I) × (ℕ → S)) := (⋃ n, ⋃ i, G n i) ∪ (⋃ k, ⋃ i, Z0 k i)
  have hG : ρ (⋃ n, ⋃ i, G n i) = 0 := by
    apply measure_iUnion_null
    intro n
    apply measure_iUnion_null
    intro i
    exact hcoupling n i
  have hZ0 : ρ (⋃ k, ⋃ i, Z0 k i) = 0 := by
    apply measure_iUnion_null
    intro k
    apply measure_iUnion_null
    intro i
    by_cases hi : (Q : Measure S) (A k i) = 0
    · have hset : Z0 k i = Prod.fst ⁻¹' {b : S × I | b.1 ∈ A k i} := by
        ext z
        simp [Z0, hi]
      rw [hset]
      calc
        ρ (Prod.fst ⁻¹' {b : S × I | b.1 ∈ A k i}) =
            Measure.map Prod.fst ρ {b : S × I | b.1 ∈ A k i} :=
          (Measure.map_apply (measurable_fst :
            Measurable (Prod.fst : (S × I) × (ℕ → S) → S × I))
            ((hmeas k i).preimage measurable_fst)).symm
        _ = ((Q : Measure S).prod volume) {b : S × I | b.1 ∈ A k i} := by rw [hbase]
        _ = 0 := by
          rw [show {b : S × I | b.1 ∈ A k i} = A k i ×ˢ univ by ext b; simp]
          simp [hi]
    · have hset : Z0 k i = ∅ := by
        ext z
        simp [Z0, hi]
      rw [hset]
      exact measure_empty
  have hZ : ρ Z = 0 := measure_union_null hG hZ0
  let B0 : ℕ → Set (S × I) := fun k =>
    {b | blockThreshold k ≤ b.2} ∪ {b | b.1 ∉ ⋃ i ∈ Finset.range (M k), A k i}
  let B : ℕ → Set ((S × I) × (ℕ → S)) := fun k => Prod.fst ⁻¹' B0 k
  have hUmeas (k : ℕ) : MeasurableSet (⋃ i ∈ Finset.range (M k), A k i) :=
    MeasurableSet.biUnion (Finset.range (M k)).countable_toSet (fun i _ => hmeas k i)
  have hB0 (k : ℕ) : MeasurableSet (B0 k) :=
    (measurableSet_le measurable_const measurable_snd).union
      ((hUmeas k).compl.preimage measurable_fst)
  have hcompl (k : ℕ) : (Q : Measure S) (⋃ i ∈ Finset.range (M k), A k i)ᶜ ≤
      (2⁻¹ : ℝ≥0∞) ^ k := by
    rw [measure_compl (hUmeas k) (measure_ne_top _ _), measure_univ]
    calc
      1 - (Q : Measure S) (⋃ i ∈ Finset.range (M k), A k i) ≤
          1 - (1 - (2⁻¹ : ℝ≥0∞) ^ k) := tsub_le_tsub_left (hM k) 1
      _ = (2⁻¹ : ℝ≥0∞) ^ k :=
        ENNReal.sub_sub_cancel ENNReal.one_ne_top (pow_le_one₀ (by norm_num) (by norm_num))
  have hB (k : ℕ) : ρ (B k) ≤ 2 * (2⁻¹ : ℝ≥0∞) ^ k := by
    have hmap : ρ (B k) = ((Q : Measure S).prod volume) (B0 k) := by
      change ρ (Prod.fst ⁻¹' B0 k) = ((Q : Measure S).prod volume) (B0 k)
      rw [← Measure.map_apply measurable_fst (hB0 k), hbase]
    rw [hmap]
    change ((Q : Measure S).prod volume) ({b : S × I | blockThreshold k ≤ b.2} ∪
      {b | b.1 ∉ ⋃ i ∈ Finset.range (M k), A k i}) ≤ _
    calc
      _ ≤ ((Q : Measure S).prod volume) {b : S × I | blockThreshold k ≤ b.2} +
          ((Q : Measure S).prod volume) {b : S × I |
            b.1 ∉ ⋃ i ∈ Finset.range (M k), A k i} := measure_union_le _ _
      _ = (2⁻¹ : ℝ≥0∞) ^ k +
          (Q : Measure S) (⋃ i ∈ Finset.range (M k), A k i)ᶜ := by
        congr 1
        · rw [show {b : S × I | blockThreshold k ≤ b.2} = univ ×ˢ Ici (blockThreshold k) by
            ext b; simp]
          rw [Measure.prod_prod, measure_univ, one_mul, volume_Ici_blockThreshold]
        · rw [show {b : S × I | b.1 ∉ ⋃ i ∈ Finset.range (M k), A k i} =
            (⋃ i ∈ Finset.range (M k), A k i)ᶜ ×ˢ univ by ext b; simp]
          rw [Measure.prod_prod, measure_univ, mul_one]
      _ ≤ (2⁻¹ : ℝ≥0∞) ^ k + (2⁻¹ : ℝ≥0∞) ^ k := add_le_add_right (hcompl k) _
      _ = 2 * (2⁻¹ : ℝ≥0∞) ^ k := (two_mul _).symm
  have hsum : ∑' k, ρ (B k) ≠ ∞ := by
    apply ne_top_of_le_ne_top (show ∑' k, 2 * (2⁻¹ : ℝ≥0∞) ^ k ≠ ∞ by
      rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric_two]
      norm_num)
    exact ENNReal.tsum_le_tsum hB
  have hgood (z : (S × I) × (ℕ → S)) (hz : z ∉ Z) (n : ℕ) (hn : N 0 ≤ n)
      (hzB : z ∉ B (level n)) : partitionIndex (A (level n)) (hcover (level n)) z.1.1 =
        partitionIndex (A (level n)) (hcover (level n)) (z.2 n) := by
    by_contra hne
    have hyU : z.1.1 ∈ ⋃ i ∈ Finset.range (M (level n)), A (level n) i := by
      have hz0 : z.1 ∉ B0 (level n) := by
        change z.1 ∉ B0 (level n) at hzB
        exact hzB
      simp only [B0, mem_union, mem_ofPred_eq, not_or, not_not] at hz0
      exact hz0.2
    obtain ⟨j, hj⟩ := mem_iUnion.mp hyU
    obtain ⟨hjM, hyj⟩ := mem_iUnion.mp hj
    have hz0 : z.1 ∉ B0 (level n) := by
      change z.1 ∉ B0 (level n) at hzB
      exact hzB
    have hu : z.1.2 < blockThreshold (level n) := by
      simp only [B0, mem_union, mem_ofPred_eq, not_or] at hz0
      exact lt_of_not_ge hz0.1
    by_cases hi : (Q : Measure S) (A (level n) j) = 0
    · apply hz
      apply Or.inr
      exact mem_iUnion.mpr ⟨level n, mem_iUnion.mpr ⟨j, hyj, hi⟩⟩
    · have hmass := hN (level n) n (hNlevel hn) j hjM
      have ht : blockThreshold (level n) ≤ cellStayProbability (P n : Measure S)
          (Q : Measure S) (A (level n)) j :=
        le_cellStayProbability_of_mul_le hi hmass
      apply hz
      apply Or.inl
      refine mem_iUnion.mpr ⟨n, mem_iUnion.mpr ⟨j, hyj, hu.trans_le ht, hne⟩⟩
  refine ⟨(S × I) × (ℕ → S), inferInstance, ρ, hρ, fun n z => z.2 n, fun z => z.1.1,
    fun n => (measurable_pi_apply n).comp measurable_snd,
    measurable_fst.comp measurable_fst, hXlaw, ?_, ?_⟩
  · rw [show (fun z : (S × I) × (ℕ → S) => z.1.1) = Prod.fst ∘ Prod.fst from rfl,
      ← Measure.map_map measurable_fst measurable_fst, hbase]
    exact Measure.fst_prod
  · have hfinite := ae_finite_setOfPred_mem (μ := ρ) (s := B) hsum
    have hZae : ∀ᵐ z ∂ρ, z ∉ Z := by
      rw [ae_iff]
      have hset : {a | ¬a ∉ Z} = Z := by
        ext a
        simp
      rw [hset]
      exact hZ
    filter_upwards [hfinite, hZae] with z hfinite hz
    apply Metric.tendsto_atTop.mpr
    intro ε hε
    obtain ⟨K, hK⟩ := hfinite.exists_le
    have hsmall : Tendsto (fun n => (2⁻¹ : ℝ) ^ level n) atTop (𝓝 0) :=
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).comp hlevel
    apply eventually_atTop.mp
    filter_upwards [hsmall.eventually (Iio_mem_nhds hε), eventually_ge_atTop (N 0),
      hlevel.eventually_ge_atTop (K + 1)] with n hnε hn hnK
    have hzB : z ∉ B (level n) := by
      intro hzB
      have hle := hK (level n) hzB
      omega
    have hidx := hgood z hz n hn hzB
    have hYmem : z.1.1 ∈ A (level n)
        (partitionIndex (A (level n)) (hcover (level n)) z.1.1) := partitionIndex_mem _
    have hXmem : z.2 n ∈ A (level n)
        (partitionIndex (A (level n)) (hcover (level n)) z.1.1) := by
      rw [hidx]
      exact partitionIndex_mem _
    rw [dist_comm]
    exact (hmesh (level n) _ z.1.1 hYmem (z.2 n) hXmem).trans hnε

/-- Dudley (1968): weak convergence of laws on a separable pseudometric space `S` with its Borel
σ-algebra implies a.s. convergent random variables on some probability space (Billingsley 1999,
Theorem 6.7 is the Polish/[0,1] case). -/
theorem exists_probabilitySpace_tendsto_ae_of_tendsto {S : Type u} [PseudoMetricSpace S]
    [TopologicalSpace.SeparableSpace S] [MeasurableSpace S] [BorelSpace S]
    {P : ℕ → ProbabilityMeasure S} {Q : ProbabilityMeasure S} (h : Tendsto P atTop (𝓝 Q)) :
    ∃ (Ω : Type u) (_ : MeasurableSpace Ω) (μ : Measure Ω) (_ : IsProbabilityMeasure μ)
      (X : ℕ → Ω → S) (Y : Ω → S),
      (∀ n, Measurable (X n)) ∧ Measurable Y ∧
      (∀ n, Measure.map (X n) μ = (P n : Measure S)) ∧
      Measure.map Y μ = (Q : Measure S) ∧
      ∀ᵐ ω ∂μ, Tendsto (fun n => X n ω) atTop (𝓝 (Y ω)) :=
  exists_probabilitySpace_tendsto_ae_of_tendsto_of_metric
    (fun hT => exists_probabilitySpace_tendsto_ae_of_tendsto_metric hT) h

end BGW.Probability
