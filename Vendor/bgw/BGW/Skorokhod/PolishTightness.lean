/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.Skorokhod.CompleteMetricSpace
public import BGW.Skorokhod.CompleteMetricCompleteness
public import BGW.Skorokhod.Separable
public import BGW.Skorokhod.Measurable
public import BGW.Skorokhod.Tightness
public import BGW.Probability.SkorokhodRepresentation
public import Mathlib.MeasureTheory.Measure.Prokhorov
public import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-!
# Polishness and tightness criteria on Skorokhod space

This file proves Polishness and standard Borelness of `D`, specializes Skorokhod
representation and Prokhorov's theorem to `D`, and gives Billingsley's compactness and
tightness criteria in terms of bounded values and the càdlàg modulus.

## References

* P. Billingsley, *Convergence of Probability Measures*, 2nd ed., Wiley, 1999,
  Sections 5, 6, 12 and 13.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped Topology ENNReal

namespace BGW.Skorokhod

variable {T : ℝ} {E : Type*}

/-- `D([0,T], E)` is Polish for complete separable metric `E` (Billingsley 1999, Theorems
12.1-12.2). -/
theorem polishSpace_D [MetricSpace E] [CompleteSpace E] [TopologicalSpace.SeparableSpace E] :
    PolishSpace (D T E) := by
  infer_instance

/-- `D([0,T], E)` with its Borel σ-algebra is a standard Borel space. -/
theorem standardBorelSpace_D [MetricSpace E] [CompleteSpace E]
    [TopologicalSpace.SeparableSpace E] : StandardBorelSpace (D T E) := by
  infer_instance

/-- Skorokhod representation on `D` (Billingsley 1999, Theorem 6.7): weakly convergent laws on
`D([0,T], E)` are the laws of random variables on `([0,1], Lebesgue)` converging almost surely.
Corollary of `BGW.Probability.exists_tendsto_ae_of_tendsto` and `polishSpace_D`. -/
theorem exists_tendsto_ae_of_tendsto_D [MetricSpace E] [CompleteSpace E]
    [TopologicalSpace.SeparableSpace E]
    {P : ℕ → ProbabilityMeasure (D T E)} {Q : ProbabilityMeasure (D T E)}
    (h : Tendsto P atTop (𝓝 Q)) :
    ∃ (X : ℕ → unitInterval → D T E) (Y : unitInterval → D T E),
      (∀ n, Measurable (X n)) ∧ Measurable Y ∧
      (∀ n, Measure.map (X n) (volume : Measure unitInterval) = (P n : Measure (D T E))) ∧
      Measure.map Y (volume : Measure unitInterval) = (Q : Measure (D T E)) ∧
      ∀ᵐ ω ∂(volume : Measure unitInterval),
        Tendsto (fun n => X n ω) atTop (𝓝 (Y ω)) := by
  exact BGW.Probability.exists_tendsto_ae_of_tendsto h

/-- Prokhorov's theorem on `D`, both directions (Billingsley 1999, Theorems 5.1
and 5.2): a set of
probability laws on `D([0,T], E)` is tight iff it is relatively compact for the topology of weak
convergence. -/
theorem isTightMeasureSet_iff_isCompact_closure_D [MetricSpace E] [CompleteSpace E]
    [TopologicalSpace.SeparableSpace E] (S : Set (ProbabilityMeasure (D T E))) :
    IsTightMeasureSet {((μ : ProbabilityMeasure (D T E)) : Measure (D T E)) | μ ∈ S} ↔
      IsCompact (closure S) := by
  let : MetricSpace (D T E) := TopologicalSpace.completelyMetrizableMetric _
  let : CompleteSpace (D T E) := TopologicalSpace.complete_completelyMetrizableMetric _
  constructor
  · exact isCompact_closure_of_isTightMeasureSet
  · exact isTightMeasureSet_of_isCompact_closure

/-- Billingsley 1999, Theorem 12.3, necessity: a relatively compact set of paths has values in a
bounded set and uniformly vanishing modulus `w'` at thresholds below `T`. (Corollary of
`exists_isBounded_values_of_isCompact` and `exists_uniform_cadlagModulus_of_isCompact` applied to
`closure A`, monotonicity of `f ↦ cadlagModulus f δ` not needed.) -/
theorem bounded_and_modulus_of_isCompact_closure [MetricSpace E] {A : Set (D T E)}
    (hT : 0 < T) (hA : IsCompact (closure A)) :
    (∃ K : Set E, Bornology.IsBounded K ∧ ∀ f ∈ A, ∀ t, f t ∈ K) ∧
    ∀ ε > 0, ∃ δ, 0 < δ ∧ δ < T ∧ ∀ f ∈ A, cadlagModulus f δ ≤ ε := by
  constructor
  · obtain ⟨K, hK, hvalues⟩ := exists_isBounded_values_of_isCompact hA
    exact ⟨K, hK, fun f hf => hvalues f (subset_closure hf)⟩
  · intro ε hε
    obtain ⟨δ, hδ, hδT, hmod⟩ := exists_uniform_cadlagModulus_of_isCompact hA hT hε
    exact ⟨δ, hδ, hδT, fun f hf => hmod f (subset_closure hf)⟩

/-- Billingsley 1999, Theorem 12.3 (iff): `A ⊆ D([0,T], E)`, `E` proper, is relatively compact
iff its values are bounded and `lim_{δ→0} sup_{f ∈ A} w'_f(δ) = 0`. -/
theorem isCompact_closure_iff_bounded_and_modulus [MetricSpace E] [ProperSpace E]
    {A : Set (D T E)} (hT : 0 < T) :
    IsCompact (closure A) ↔
      ((∃ K : Set E, Bornology.IsBounded K ∧ ∀ f ∈ A, ∀ t, f t ∈ K) ∧
        ∀ ε > 0, ∃ δ, 0 < δ ∧ δ < T ∧ ∀ f ∈ A, cadlagModulus f δ ≤ ε) := by
  constructor
  · exact bounded_and_modulus_of_isCompact_closure hT
  · rintro ⟨⟨K, hK, hvalues⟩, hmod⟩
    exact isCompact_closure_of_cadlagModulus hK hvalues hmod

/-- Billingsley 1999, Theorem 13.2 (iff, limsup form): a sequence of probability laws on
`D([0,T], E)`, `E` proper (so `D` is Polish and each single law is tight), is tight iff
(i) for each `η > 0` there is a bounded `K ⊆ E` with `limsup_n P_n(∃ t, f t ∉ K) ≤ η`
(the form of `lim_{a→∞} limsup_n P_n(‖f‖ ≥ a) = 0` for a general metric `E`), and
(ii) for all `ε, η > 0` there is `δ ∈ (0,T)` with `limsup_n P_n(w'_f(δ) > ε) ≤ η`
(equivalent to `lim_{δ→0} limsup_n P_n(w'_f(δ) ≥ ε) = 0`, since `w'` is monotone in `δ`). -/
theorem isTightMeasureSet_range_iff_limsup [MetricSpace E] [ProperSpace E]
    (hT : 0 < T) (P : ℕ → ProbabilityMeasure (D T E)) :
    IsTightMeasureSet (Set.range fun n => (P n : Measure (D T E))) ↔
      ((∀ η > 0, ∃ K : Set E, Bornology.IsBounded K ∧
          limsup (fun n => (P n : Measure (D T E)) {f | ∃ t, f t ∉ K}) atTop ≤
            ENNReal.ofReal η) ∧
        (∀ ε > 0, ∀ η > 0, ∃ δ, 0 < δ ∧ δ < T ∧
          limsup (fun n => (P n : Measure (D T E)) {f | ε < cadlagModulus f δ}) atTop ≤
            ENNReal.ofReal η)) := by
  constructor
  · intro htight
    constructor
    · intro η hη
      obtain ⟨C, hC, hprob⟩ := isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mp
        htight (ENNReal.ofReal η) (ENNReal.ofReal_pos.mpr hη)
      obtain ⟨K, hK, hvalues⟩ := exists_isBounded_values_of_isCompact hC
      refine ⟨K, hK, limsup_le_of_le (by isBoundedDefault) (Filter.Eventually.of_forall ?_)⟩
      intro n
      apply le_trans (measure_mono ?_) (hprob (P n : Measure (D T E)) ⟨n, rfl⟩)
      rintro f ⟨t, ht⟩ hfC
      exact ht (hvalues f hfC t)
    · intro ε hε η hη
      obtain ⟨C, hC, hprob⟩ := isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mp
        htight (ENNReal.ofReal η) (ENNReal.ofReal_pos.mpr hη)
      obtain ⟨δ, hδ, hδT, hmod⟩ := exists_uniform_cadlagModulus_of_isCompact hC hT hε
      refine ⟨δ, hδ, hδT, limsup_le_of_le (by isBoundedDefault)
        (Filter.Eventually.of_forall ?_)⟩
      intro n
      apply le_trans (measure_mono ?_) (hprob (P n : Measure (D T E)) ⟨n, rfl⟩)
      intro f hf hfC
      exact (not_lt_of_ge (hmod f hfC)) hf
  · rintro ⟨hbdd, hmod⟩
    let : MetricSpace (D T E) := TopologicalSpace.completelyMetrizableMetric _
    let : CompleteSpace (D T E) := TopologicalSpace.complete_completelyMetrizableMetric _
    apply isTightMeasureSet_of_cadlagModulus_eventually (fun n => (P n : Measure (D T E)))
    · intro n
      exact isTightMeasureSet_singleton
    · intro η hη
      obtain ⟨K, hK, hlim⟩ := hbdd (η / 2) (half_pos hη)
      have hlt : limsup (fun n => (P n : Measure (D T E)) {f | ∃ t, f t ∉ K}) atTop <
          ENNReal.ofReal η := hlim.trans_lt ((ENNReal.ofReal_lt_ofReal_iff hη).mpr
        (half_lt_self hη))
      obtain ⟨N, hN⟩ := eventually_atTop.mp (eventually_lt_of_limsup_lt hlt)
      exact ⟨K, hK, N, fun n hn => (hN n hn).le⟩
    · intro ε hε η hη
      obtain ⟨δ, hδ, hδT, hlim⟩ := hmod ε hε (η / 2) (half_pos hη)
      have hlt : limsup (fun n => (P n : Measure (D T E))
          {f | ε < cadlagModulus f δ}) atTop < ENNReal.ofReal η :=
        hlim.trans_lt ((ENNReal.ofReal_lt_ofReal_iff hη).mpr (half_lt_self hη))
      obtain ⟨N, hN⟩ := eventually_atTop.mp (eventually_lt_of_limsup_lt hlt)
      exact ⟨δ, hδ, hδT, N, fun n hn => (hN n hn).le⟩

end BGW.Skorokhod
