/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

import BGW.Probability.WeakConvergence

/-!
# Reduction from pseudometric spaces to their separation quotients

The canonical section from the separation quotient to a pseudometric space is Borel measurable.
Consequently, a separable-metric representation theorem can be transported back to the original
pseudometric space without changing either the laws or almost-sure convergence.
See Dudley, "Distances of probability measures and random variables" (1968), and *Real
Analysis and Probability* (2002), Theorem 11.7.2.
-/

@[expose] public section

open Filter MeasureTheory Set TopologicalSpace ProbabilityTheory
open scoped Topology ProbabilityTheory ENNReal

universe u

namespace BGW.Probability

/-- The canonical section from the separation quotient to a pseudometric Borel space is
measurable. -/
private theorem measurable_separationQuotient_out {S : Type u} [PseudoMetricSpace S]
    [MeasurableSpace S] [BorelSpace S] :
    @Measurable (SeparationQuotient S) S (borel _) _ Quotient.out := by
  let _ : MeasurableSpace (SeparationQuotient S) := borel _
  let _ : BorelSpace (SeparationQuotient S) := ⟨rfl⟩
  change @Measurable _ _ (borel (SeparationQuotient S)) _ _
  apply measurable_of_isOpen
  intro U hU
  have heq : Quotient.out ⁻¹' U = SeparationQuotient.mk '' U := by
    ext t
    constructor
    · intro ht
      refine ⟨Quotient.out t, ht, ?_⟩
      exact Quotient.out_eq' t
    · rintro ⟨x, hx, rfl⟩
      have heq : SeparationQuotient.mk (Quotient.out (SeparationQuotient.mk x)) =
          SeparationQuotient.mk x := Quotient.out_eq' _
      have hi : Inseparable (Quotient.out (SeparationQuotient.mk x)) x :=
        SeparationQuotient.mk_eq_mk.mp heq
      exact (hi.mem_open_iff hU).mpr hx
  rw [heq]
  exact (SeparationQuotient.isOpenMap_mk U hU).measurableSet

/-- Borel sets of a pseudometric space are saturated by inseparability. -/
private theorem mem_of_inseparable_of_measurable {S : Type u} [PseudoMetricSpace S]
    [MeasurableSpace S] [BorelSpace S] {B : Set S} (hB : MeasurableSet B)
    {x y : S} (hxy : Inseparable x y) : x ∈ B ↔ y ∈ B := by
  induction B, hB using MeasurableSpace.induction_on_inter (BorelSpace.measurable_eq (α := S))
    isPiSystem_isOpen with
  | empty => simp
  | basic B hB => exact hxy.mem_open_iff hB
  | compl B hB ih => simp only [Set.mem_compl_iff, ih]
  | iUnion f hfd hfm ih => simp only [Set.mem_iUnion, ih]

/-- Conditional reduction of the separable representation theorem to the metric case. Any suitable
metric representation can be lifted through the canonical quotient section. -/
theorem exists_probabilitySpace_tendsto_ae_of_tendsto_of_metric {S : Type u}
    [PseudoMetricSpace S] [TopologicalSpace.SeparableSpace S]
    [MeasurableSpace S] [BorelSpace S]
    (hMetric : ∀ {T : Type u} [MetricSpace T] [TopologicalSpace.SeparableSpace T]
      [MeasurableSpace T] [BorelSpace T]
      {P : ℕ → ProbabilityMeasure T} {Q : ProbabilityMeasure T}, Tendsto P atTop (𝓝 Q) →
      ∃ (Ω : Type u) (_ : MeasurableSpace Ω) (μ : Measure Ω) (_ : IsProbabilityMeasure μ)
        (X : ℕ → Ω → T) (Y : Ω → T),
        (∀ n, Measurable (X n)) ∧ Measurable Y ∧
        (∀ n, Measure.map (X n) μ = (P n : Measure T)) ∧
        Measure.map Y μ = (Q : Measure T) ∧
        ∀ᵐ ω ∂μ, Tendsto (fun n => X n ω) atTop (𝓝 (Y ω)))
    {P : ℕ → ProbabilityMeasure S} {Q : ProbabilityMeasure S} (h : Tendsto P atTop (𝓝 Q)) :
    ∃ (Ω : Type u) (_ : MeasurableSpace Ω) (μ : Measure Ω) (_ : IsProbabilityMeasure μ)
      (X : ℕ → Ω → S) (Y : Ω → S),
      (∀ n, Measurable (X n)) ∧ Measurable Y ∧
      (∀ n, Measure.map (X n) μ = (P n : Measure S)) ∧
      Measure.map Y μ = (Q : Measure S) ∧
      ∀ᵐ ω ∂μ, Tendsto (fun n => X n ω) atTop (𝓝 (Y ω)) := by
  let _ : MeasurableSpace (SeparationQuotient S) := borel _
  let _ : BorelSpace (SeparationQuotient S) := ⟨rfl⟩
  let _ : TopologicalSpace.SeparableSpace (SeparationQuotient S) :=
    SeparationQuotient.surjective_mk.denseRange.separableSpace SeparationQuotient.continuous_mk
  let q : S → SeparationQuotient S := SeparationQuotient.mk
  let s : SeparationQuotient S → S := Quotient.out
  have hq : Continuous q := SeparationQuotient.continuous_mk
  have hs : Measurable s := measurable_separationQuotient_out
  have hqs : Function.LeftInverse q s := by
    intro t
    change SeparationQuotient.mk (Quotient.out t) = t
    exact Quotient.out_eq' t
  have hlim : Tendsto (fun n => (P n).map q) atTop (𝓝 (Q.map q)) :=
    ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous P Q h hq
  obtain ⟨Ω, mΩ, μ, hμ, X, Y, hXm, hYm, hXlaw, hYlaw, hconv⟩ :=
    @hMetric (SeparationQuotient S) _ _ _ _ (fun n => (P n).map q) (Q.map q) hlim
  let _ : MeasurableSpace Ω := mΩ
  let _ : IsProbabilityMeasure μ := hμ
  have hmapq (R : ProbabilityMeasure S) :
      Measure.map q (R : Measure S) = ((R.map q : ProbabilityMeasure (SeparationQuotient S)) :
        Measure (SeparationQuotient S)) := rfl
  have hlift (R : ProbabilityMeasure S) : Measure.map s (Measure.map q (R : Measure S)) =
      (R : Measure S) := by
    rw [Measure.map_map hs hq.measurable]
    ext B hB
    rw [Measure.map_apply (hs.comp hq.measurable) hB]
    have hx (x : S) : Inseparable (s (q x)) x :=
      SeparationQuotient.mk_eq_mk.mp (hqs (q x))
    congr 1
    ext x
    exact mem_of_inseparable_of_measurable hB (hx x)
  refine ⟨Ω, mΩ, μ, hμ, fun n => s ∘ X n, s ∘ Y,
    fun n => hs.comp (hXm n), hs.comp hYm, ?_, ?_, ?_⟩
  · intro n
    change Measure.map (s ∘ X n) μ = (P n : Measure S)
    rw [← Measure.map_map hs (hXm n), hXlaw n, ← hmapq]
    exact hlift (P n)
  · simpa only [← Measure.map_map hs hYm, hYlaw, ← hmapq] using hlift Q
  · filter_upwards [hconv] with ω hω
    apply Metric.tendsto_atTop.mpr
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hω ε hε
    refine ⟨N, fun n hn => ?_⟩
    have hd := hN n hn
    change dist (s (X n ω)) (s (Y ω)) < ε
    have heq := SeparationQuotient.dist_mk (s (X n ω)) (s (Y ω))
    change dist (q (s (X n ω))) (q (s (Y ω))) = dist (s (X n ω)) (s (Y ω)) at heq
    rw [hqs (X n ω), hqs (Y ω)] at heq
    rw [← heq]
    exact hd

end BGW.Probability
