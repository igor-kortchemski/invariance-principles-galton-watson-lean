/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.LocallyFinite.ForestWalkLaw
public import Mathlib.Probability.ConditionalProbability

/-!
# The conditional bridge law and the uniform cyclic shift

Let `μ` be an offspring probability measure and `n` a size. The conditional bridge law is the law of
the offspring counts `ω : Fin n → ℕ` under `Measure.pi (fun _ => μ)` given the bridge event
`countBridges n = {S_n = -1}`. It is a probability measure exactly when `n ≠ 0` and the size `n`
is admissible (`pi_countBridges_ne_zero_iff`); in the other cases it is the zero measure.

The cyclic-shift representation says that the Łukasiewicz code of the size-conditioned tree, rotated
by an independent uniform index of `Fin n`, has the conditional bridge law. It is stated without a
measure on finite trees, which carry no measurable structure here. The atom of the bridge law at the
count vector of a rotation of the code of a tree `t` of size `n` is `n⁻¹` times the atom of `t` in
the size-conditioned law (`cond_pi_countBridges_singleton_shift`). For every set `A` of count
vectors, the conditional bridge mass is the expectation, over a tree `t` drawn from the conditioned
law and a uniform index `i`, of the indicator of `A` at the count vector of the `i`-th rotation of
the code of `t` (`cond_pi_countBridges_apply_eq_tsum`). The proof uses the shift equivalence of the
cycle lemma, which makes the pairs `(t, i)` and the bridge words correspond exactly once, and the
rotation invariance of the walk weight. No criticality, aperiodicity or positivity hypothesis is
made; both sides vanish at inadmissible sizes. `countsOfWord n` is a left inverse of `stepWord`,
and a two-sided inverse on words of length `n` with entries at least `-1`. Adapted from
`PoissonDeclumping/Lukasiewicz/BridgeLaw.lean` (`map_shift_conditioned`). The excursion law, local
limit theorems and the passage to the limit are not part of this module.
-/

@[expose] public section

namespace BGW

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- The offspring counts `x i + 1` read off a word: a left inverse of `stepWord`, and a two-sided
inverse on words of length `n` with entries at least `-1`. -/
def countsOfWord (n : ℕ) (x : List ℤ) : Fin n → ℕ := fun i => ((x.getD i 0) + 1).toNat

theorem countsOfWord_stepWord {n : ℕ} (ω : Fin n → ℕ) : countsOfWord n (stepWord ω) = ω := by
  funext i
  simp [countsOfWord, stepWord]

theorem stepWord_countsOfWord {n : ℕ} {x : List ℤ} (hlen : x.length = n)
    (hge : ∀ a ∈ x, -1 ≤ a) : stepWord (countsOfWord n x) = x := by
  obtain ⟨ω, rfl⟩ := exists_stepWord_eq_of_entries hlen hge
  rw [countsOfWord_stepWord]

/-- Reindexing the bridge words, with a test function of the word, by offspring-count vectors. -/
theorem tsum_bridgeWords_walkWeight_mul (p : ℕ → ℝ≥0∞) (n : ℕ) (g : List ℤ → ℝ≥0∞) :
    ∑' x : List ℤ, Set.indicator (bridgeWords n) (fun x => walkWeight p x * g x) x =
      ∑' ω : Fin n → ℕ,
        Set.indicator (countBridges n) (fun ω => (∏ i, p (ω i)) * g (stepWord ω)) ω := by
  have hrange : Function.support
      (Set.indicator (bridgeWords n) (fun x => walkWeight p x * g x)) ⊆
        Set.range (stepWord (n := n)) := by
    intro x hx
    by_contra hrange
    apply hx
    have hx' : x ∉ bridgeWords n := fun h => hrange (exists_stepWord_eq h)
    exact Set.indicator_of_notMem hx' _
  rw [← stepWord_injective.tsum_eq hrange]
  refine tsum_congr fun ω => ?_
  by_cases h : ω ∈ countBridges n
  · rw [Set.indicator_of_mem ((stepWord_mem_bridgeWords_iff ω).mpr h), Set.indicator_of_mem h,
      walkWeight_stepWord]
  · rw [Set.indicator_of_notMem (mt (stepWord_mem_bridgeWords_iff ω).mp h),
      Set.indicator_of_notMem h]

/-- The pairs (tree of size `n`, rotation index) cover the bridge words exactly once, with the
weight of the tree equal to the walk weight of the rotated code. -/
theorem tsum_shift_weight_mul (p : ℕ → ℝ≥0∞) (n : ℕ) (g : List ℤ → ℝ≥0∞) :
    ∑' q : {t : PlaneTree // t.size = n} × Fin n,
        PlaneTree.weight p q.1.1 * g (q.1.1.increments.rotate q.2) =
      ∑' x : List ℤ, Set.indicator (bridgeWords n) (fun x => walkWeight p x * g x) x := by
  rw [← tsum_subtype (bridgeWords n) (fun x => walkWeight p x * g x),
    ← (PlaneTree.shiftEquiv n).tsum_eq]
  refine tsum_congr fun q => ?_
  have h : (PlaneTree.shiftEquiv n q).1 = q.1.1.increments.rotate q.2 := rfl
  change PlaneTree.weight p q.1.1 * g _ = walkWeight p (PlaneTree.shiftEquiv n q).1 *
    g (PlaneTree.shiftEquiv n q).1
  rw [h, walkWeight_rotate, PlaneTree.walkWeight_increments]

/-- The bridge event has positive mass iff `n ≠ 0` and the size `n` is admissible. -/
theorem pi_countBridges_ne_zero_iff (μ : Measure ℕ) [IsProbabilityMeasure μ] (n : ℕ) :
    Measure.pi (fun _ : Fin n => μ) (countBridges n) ≠ 0 ↔
      n ≠ 0 ∧ LocallyFinite.bienaymeLaw μ (LocallyFinite.sizeEvent n) ≠ 0 := by
  rw [← LocallyFinite.natCast_mul_bienaymeLaw_sizeEvent_eq_pi, mul_ne_zero_iff]
  simp

/-- At an admissible size `n ≠ 0`, the conditional bridge law is a probability measure. -/
theorem isProbabilityMeasure_cond_pi_countBridges (μ : Measure ℕ) [IsProbabilityMeasure μ]
    {n : ℕ} (hn : n ≠ 0) (h : LocallyFinite.bienaymeLaw μ (LocallyFinite.sizeEvent n) ≠ 0) :
    IsProbabilityMeasure ((Measure.pi fun _ : Fin n => μ)[|countBridges n]) :=
  cond_isProbabilityMeasure ((pi_countBridges_ne_zero_iff μ n).mpr ⟨hn, h⟩)

/-- The atoms of the conditional bridge law: the point masses of the bridge count vectors divided
by the mass of the bridge event. -/
theorem cond_pi_countBridges_singleton (μ : Measure ℕ) [IsProbabilityMeasure μ] {n : ℕ}
    (ω : Fin n → ℕ) :
    (Measure.pi fun _ : Fin n => μ)[|countBridges n] {ω} =
      Set.indicator (countBridges n)
        (fun ω => (∏ i, μ {ω i}) / Measure.pi (fun _ : Fin n => μ) (countBridges n)) ω := by
  rw [cond_apply (Set.to_countable _).measurableSet]
  by_cases h : ω ∈ countBridges n
  · rw [Set.indicator_of_mem h, Set.inter_eq_right.mpr (Set.singleton_subset_iff.mpr h),
      Measure.pi_singleton, ENNReal.div_eq_inv_mul]
  · rw [Set.indicator_of_notMem h, Set.inter_singleton_eq_empty.mpr h, measure_empty, mul_zero]

/-- **Uniform cyclic shift, atoms.** If the code of a tree `t` of size `n`, rotated by `i`, is the
step word of the count vector `ω`, then the atom of `ω` in the conditional bridge law is `n⁻¹`
times the atom of `t` in the size-conditioned law. -/
theorem cond_pi_countBridges_singleton_shift (μ : Measure ℕ) [IsProbabilityMeasure μ] {n : ℕ}
    (t : PlaneTree) (ht : t.size = n) (i : Fin n) (ω : Fin n → ℕ)
    (hω : stepWord ω = t.increments.rotate i) :
    (Measure.pi fun _ : Fin n => μ)[|countBridges n] {ω} =
      (n : ℝ≥0∞)⁻¹ * (LocallyFinite.bienaymeLaw μ)[|LocallyFinite.sizeEvent n]
        {t.toLocallyFinite} := by
  have hmem : ω ∈ countBridges n := by
    rw [← stepWord_mem_bridgeWords_iff, hω]
    exact (PlaneTree.shiftEquiv n (⟨t, ht⟩, i)).2
  have hw : ∏ i, μ {ω i} = PlaneTree.weight (fun d => μ {d}) t := by
    rw [← walkWeight_stepWord (fun d => μ {d}), hω, walkWeight_rotate,
      PlaneTree.walkWeight_increments]
  rw [cond_pi_countBridges_singleton, Set.indicator_of_mem hmem, hw,
    ← LocallyFinite.natCast_mul_bienaymeLaw_sizeEvent_eq_pi,
    LocallyFinite.cond_sizeEvent_singleton, ite_eq_left ht, ENNReal.div_eq_inv_mul,
    ENNReal.div_eq_inv_mul, ENNReal.mul_inv (Or.inr (measure_ne_top _ _))
      (Or.inl (ENNReal.natCast_ne_top n)), mul_assoc]

/-- **Uniform cyclic shift, law.** For every set `A` of count vectors, the conditional bridge mass
of `A` is the expectation over `t` drawn from the size-conditioned law and an independent uniform
index `i` of `Fin n` (`n⁻¹` per index) of the indicator of `A` at the count vector of the `i`-th
rotation of the code of `t`. -/
theorem cond_pi_countBridges_apply_eq_tsum (μ : Measure ℕ) [IsProbabilityMeasure μ] {n : ℕ}
    (A : Set (Fin n → ℕ)) :
    (Measure.pi fun _ : Fin n => μ)[|countBridges n] A =
      ∑' q : {t : PlaneTree // t.size = n} × Fin n, (n : ℝ≥0∞)⁻¹ *
        (LocallyFinite.bienaymeLaw μ)[|LocallyFinite.sizeEvent n] {q.1.1.toLocallyFinite} *
          Set.indicator A 1 (countsOfWord n (q.1.1.increments.rotate q.2)) := by
  set P := LocallyFinite.bienaymeLaw μ (LocallyFinite.sizeEvent n) with hP
  set g : List ℤ → ℝ≥0∞ := fun x => Set.indicator A 1 (countsOfWord n x) with hg
  have hterm : ∀ q : {t : PlaneTree // t.size = n} × Fin n, (n : ℝ≥0∞)⁻¹ *
      (LocallyFinite.bienaymeLaw μ)[|LocallyFinite.sizeEvent n] {q.1.1.toLocallyFinite} *
        Set.indicator A 1 (countsOfWord n (q.1.1.increments.rotate q.2)) =
      ((n : ℝ≥0∞)⁻¹ * P⁻¹) * (PlaneTree.weight (fun d => μ {d}) q.1.1 *
        g (q.1.1.increments.rotate q.2)) := by
    intro q
    rw [LocallyFinite.cond_sizeEvent_singleton, ite_eq_left q.1.2, ENNReal.div_eq_inv_mul]
    simp only [hg]
    ring
  simp_rw [hterm]
  rw [ENNReal.tsum_mul_left, tsum_shift_weight_mul, tsum_bridgeWords_walkWeight_mul,
    cond_apply (Set.to_countable _).measurableSet, pi_eq_tsum_indicator μ (countBridges n ∩ A),
    ← ENNReal.mul_inv (Or.inr (measure_ne_top _ _)) (Or.inl (ENNReal.natCast_ne_top n)),
    ← LocallyFinite.natCast_mul_bienaymeLaw_sizeEvent_eq_pi]
  congr 1
  refine tsum_congr fun ω => ?_
  by_cases hω : ω ∈ countBridges n <;> by_cases hA : ω ∈ A
  · rw [Set.indicator_of_mem hω, Set.indicator_of_mem (show ω ∈ countBridges n ∩ A from ⟨hω, hA⟩)]
    simp [hg, countsOfWord_stepWord, hA]
  · rw [Set.indicator_of_mem hω, Set.indicator_of_notMem (fun h => hA h.2)]
    simp [hg, countsOfWord_stepWord, hA]
  · rw [Set.indicator_of_notMem hω, Set.indicator_of_notMem (fun h => hω h.1)]
  · rw [Set.indicator_of_notMem hω, Set.indicator_of_notMem (fun h => hω h.1)]

end BGW
