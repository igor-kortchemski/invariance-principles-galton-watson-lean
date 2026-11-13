/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.LocallyFinite.BridgeLaw

/-!
# The excursion law

Let `μ` be an offspring probability measure and `n` a size. The offspring counts
`ω : Fin n → ℕ` under `Measure.pi (fun _ => μ)` have a Łukasiewicz step word `stepWord ω`; it is a
tree excursion exactly when `ω` lies in `countExcursions n`, the event `{ζ(X) = n}` that the walk
first reaches `-1` at time `n`. The excursion law is the law of the counts given this event.

* `pi_countExcursions`: `P(ζ(X) = n) = P(|T| = n)`, the mass of `countExcursions n` is the mass of
  the size event under the Bienaymé–Galton–Watson law;
* the excursion law is a probability measure exactly at admissible sizes
  (`pi_countExcursions_ne_zero_iff`), and is the zero measure otherwise;
* the atom of the excursion law at the count vector of the code of a tree `t` of size `n` is the
  atom of `t` in the size-conditioned law (`cond_pi_countExcursions_singleton_code`), and vanishes
  off `countExcursions n`;
* for every set `A` of count vectors, the excursion mass of `A` is the expectation over a tree `t`
  drawn from the size-conditioned law of the indicator of `A` at the count vector of its code
  (`cond_pi_countExcursions_apply_eq_tsum`): the code of the conditioned tree has the excursion law.

As for the cyclic shift in `BridgeLaw`, this is stated without a measure on finite trees, which
carry no measurable structure here. No criticality, aperiodicity or positivity hypothesis is made;
both sides vanish at inadmissible sizes and at `n = 0`. Adapted from
`PoissonDeclumping/Lukasiewicz/BridgeLaw.lean` (`map_dfsSeq_conditioned`, `excursionLaw`,
`walkVecLaw_zeta_eq_bienayme`). Local limit theorems are not part of this module.
-/

@[expose] public section

namespace BGW

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- The offspring-count vectors whose step word is a tree excursion: the Łukasiewicz walk first
reaches `-1` at time `n`. -/
def countExcursions (n : ℕ) : Set (Fin n → ℕ) := {ω | IsTreeExcursion (stepWord ω)}

/-- A count vector has a tree excursion as step word iff it lies in `countExcursions n`. -/
theorem stepWord_mem_excursions_iff {n : ℕ} (ω : Fin n → ℕ) :
    stepWord ω ∈ {x : List ℤ | IsTreeExcursion x ∧ x.length = n} ↔ ω ∈ countExcursions n := by
  simp [countExcursions, stepWord]

/-- Reindexing the tree excursions of length `n` by offspring-count vectors. -/
theorem tsum_excursions_walkWeight (p : ℕ → ℝ≥0∞) (n : ℕ) :
    ∑' x : List ℤ, Set.indicator {x : List ℤ | IsTreeExcursion x ∧ x.length = n}
        (walkWeight p) x =
      ∑' ω : Fin n → ℕ, Set.indicator (countExcursions n) (fun ω => ∏ i, p (ω i)) ω := by
  have hrange : Function.support
      (Set.indicator {x : List ℤ | IsTreeExcursion x ∧ x.length = n} (walkWeight p)) ⊆
        Set.range (stepWord (n := n)) := by
    intro x hx
    by_contra hrange
    apply hx
    have hx' : x ∉ {x : List ℤ | IsTreeExcursion x ∧ x.length = n} := fun h =>
      hrange (exists_stepWord_eq_of_entries h.2 h.1.1)
    exact Set.indicator_of_notMem hx' _
  rw [← stepWord_injective.tsum_eq hrange]
  refine tsum_congr fun ω => ?_
  by_cases h : ω ∈ countExcursions n
  · rw [Set.indicator_of_mem ((stepWord_mem_excursions_iff ω).mpr h), Set.indicator_of_mem h,
      walkWeight_stepWord]
  · rw [Set.indicator_of_notMem (mt (stepWord_mem_excursions_iff ω).mp h),
      Set.indicator_of_notMem h]

/-- `P(ζ(X) = n) = P(|T| = n)`: the first passage of the walk to `-1` at time `n` has the mass of
the size event. -/
theorem pi_countExcursions (μ : Measure ℕ) [IsProbabilityMeasure μ] (n : ℕ) :
    Measure.pi (fun _ : Fin n => μ) (countExcursions n) =
      LocallyFinite.bienaymeLaw μ (LocallyFinite.sizeEvent n) := by
  have hmeas : MeasurableSet (countExcursions n) := (Set.to_countable _).measurableSet
  rw [LocallyFinite.bienaymeLaw_sizeEvent_eq_tsum_excursions, tsum_excursions_walkWeight,
    ← Measure.tsum_indicator_apply_singleton (Measure.pi fun _ : Fin n => μ) _ hmeas]
  simp only [Measure.pi_singleton]

/-- The excursion event has positive mass iff the size `n` is admissible. -/
theorem pi_countExcursions_ne_zero_iff (μ : Measure ℕ) [IsProbabilityMeasure μ] (n : ℕ) :
    Measure.pi (fun _ : Fin n => μ) (countExcursions n) ≠ 0 ↔
      LocallyFinite.bienaymeLaw μ (LocallyFinite.sizeEvent n) ≠ 0 := by
  rw [pi_countExcursions]

/-- At an admissible size, the excursion law is a probability measure. -/
theorem isProbabilityMeasure_cond_pi_countExcursions (μ : Measure ℕ) [IsProbabilityMeasure μ]
    {n : ℕ} (h : LocallyFinite.bienaymeLaw μ (LocallyFinite.sizeEvent n) ≠ 0) :
    IsProbabilityMeasure ((Measure.pi fun _ : Fin n => μ)[|countExcursions n]) :=
  cond_isProbabilityMeasure ((pi_countExcursions_ne_zero_iff μ n).mpr h)

/-- At an inadmissible size, the excursion law is the zero measure. -/
theorem cond_pi_countExcursions_eq_zero (μ : Measure ℕ) [IsProbabilityMeasure μ] {n : ℕ}
    (h : LocallyFinite.bienaymeLaw μ (LocallyFinite.sizeEvent n) = 0) :
    (Measure.pi fun _ : Fin n => μ)[|countExcursions n] = 0 :=
  cond_eq_zero_of_meas_eq_zero ((pi_countExcursions μ n).trans h)

/-- The atoms of the excursion law: the point masses of the excursion count vectors divided by the
mass of the excursion event. -/
theorem cond_pi_countExcursions_singleton (μ : Measure ℕ) [IsProbabilityMeasure μ] {n : ℕ}
    (ω : Fin n → ℕ) :
    (Measure.pi fun _ : Fin n => μ)[|countExcursions n] {ω} =
      Set.indicator (countExcursions n)
        (fun ω => (∏ i, μ {ω i}) / Measure.pi (fun _ : Fin n => μ) (countExcursions n)) ω := by
  rw [cond_apply (Set.to_countable _).measurableSet]
  by_cases h : ω ∈ countExcursions n
  · rw [Set.indicator_of_mem h, Set.inter_eq_right.mpr (Set.singleton_subset_iff.mpr h),
      Measure.pi_singleton, ENNReal.div_eq_inv_mul]
  · rw [Set.indicator_of_notMem h, Set.inter_singleton_eq_empty.mpr h, measure_empty, mul_zero]

/-- Decoding the code of a tree of size `n` to counts and re-encoding returns the code. -/
theorem stepWord_countsOfWord_increments {n : ℕ} (t : PlaneTree) (ht : t.size = n) :
    stepWord (countsOfWord n t.increments) = t.increments :=
  stepWord_countsOfWord (by rw [PlaneTree.length_increments, ht])
    fun _ hx => PlaneTree.neg_one_le_increment t hx

/-- **Excursion law, atoms.** The atom of the excursion law at the count vector of the code of a
tree `t` of size `n` is the atom of `t` in the size-conditioned law. -/
theorem cond_pi_countExcursions_singleton_code (μ : Measure ℕ) [IsProbabilityMeasure μ] {n : ℕ}
    (t : PlaneTree) (ht : t.size = n) :
    (Measure.pi fun _ : Fin n => μ)[|countExcursions n] {countsOfWord n t.increments} =
      (LocallyFinite.bienaymeLaw μ)[|LocallyFinite.sizeEvent n] {t.toLocallyFinite} := by
  have hw := stepWord_countsOfWord_increments t ht
  have hmem : countsOfWord n t.increments ∈ countExcursions n := by
    rw [← stepWord_mem_excursions_iff, hw]
    exact ⟨PlaneTree.isTreeExcursion_increments t, by rw [PlaneTree.length_increments, ht]⟩
  rw [cond_pi_countExcursions_singleton, Set.indicator_of_mem hmem,
    ← walkWeight_stepWord (fun d => μ {d}), hw, PlaneTree.walkWeight_increments, pi_countExcursions,
    LocallyFinite.cond_sizeEvent_singleton, ite_eq_left ht]

/-- **Excursion law, law.** For every set `A` of count vectors, the excursion mass of `A` is the
expectation, over a tree `t` drawn from the size-conditioned law, of the indicator of `A` at the
count vector of the code of `t`: the code of the size-conditioned tree has the excursion law. -/
theorem cond_pi_countExcursions_apply_eq_tsum (μ : Measure ℕ) [IsProbabilityMeasure μ] {n : ℕ}
    (A : Set (Fin n → ℕ)) :
    (Measure.pi fun _ : Fin n => μ)[|countExcursions n] A =
      ∑' t : {t : PlaneTree // t.size = n},
        (LocallyFinite.bienaymeLaw μ)[|LocallyFinite.sizeEvent n] {t.1.toLocallyFinite} *
          Set.indicator A 1 (countsOfWord n t.1.increments) := by
  set ν := (Measure.pi fun _ : Fin n => μ)[|countExcursions n] with hν
  set f : {t : PlaneTree // t.size = n} → (Fin n → ℕ) := fun t => countsOfWord n t.1.increments
    with hf
  have hinj : Function.Injective f := fun t t' h => by
    have h' := congrArg stepWord h
    simp only [hf, stepWord_countsOfWord_increments _ t.2,
      stepWord_countsOfWord_increments _ t'.2] at h'
    exact Subtype.ext (PlaneTree.increments_injective h')
  have hrange : Function.support (Set.indicator A fun ω => ν {ω}) ⊆ Set.range f := by
    intro ω hω
    have hne : ν {ω} ≠ 0 := fun h => hω (by
      by_cases hA : ω ∈ A
      · rw [Set.indicator_of_mem hA, h]
      · rw [Set.indicator_of_notMem hA])
    have hmem : ω ∈ countExcursions n := by
      by_contra h
      apply hne
      rw [hν, cond_pi_countExcursions_singleton, Set.indicator_of_notMem h]
    obtain ⟨t, ht, -⟩ := (PlaneTree.isTreeExcursion_iff_existsUnique (stepWord ω)).mp hmem
    have hsize : t.size = n := by
      rw [← PlaneTree.length_increments, ht]
      simp [stepWord]
    refine ⟨⟨t, hsize⟩, ?_⟩
    simp only [hf, ht, countsOfWord_stepWord]
  rw [← Measure.tsum_indicator_apply_singleton ν A (Set.to_countable _).measurableSet,
    ← hinj.tsum_eq hrange]
  refine tsum_congr fun t => ?_
  have hat : ν {f t} = (LocallyFinite.bienaymeLaw μ)[|LocallyFinite.sizeEvent n]
      {t.1.toLocallyFinite} := cond_pi_countExcursions_singleton_code μ t.1 t.2
  by_cases hA : f t ∈ A
  · rw [Set.indicator_of_mem hA, Set.indicator_of_mem (show countsOfWord n t.1.increments ∈ A
      from hA), hat, Pi.one_apply, mul_one]
  · rw [Set.indicator_of_notMem hA, Set.indicator_of_notMem (show countsOfWord n t.1.increments ∉ A
      from hA), mul_zero]

end BGW
