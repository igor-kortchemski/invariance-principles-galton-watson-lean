/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.LocallyFinite.Atoms
public import BGW.Tree.WalkWeight
public import BGW.Tree.CycleLemma
public import Mathlib.Probability.ConditionalProbability

/-!
# Conditioning the Bienaymé–Galton–Watson law on the number of vertices

`sizeEvent n` is the event that the tree is finite and has exactly `n` present addresses. It is
measurable, empty for `n = 0`, and equals the image of the finite plane trees of size `n` under the
bridge. For every offspring probability measure `μ` (no criticality, no aperiodicity), its mass is
the total weight of the plane trees of size `n`; the size is admissible when this mass is positive,
which holds iff some tree of size `n` has positive weight. At an admissible size the conditioned
law is a probability measure with atoms `weight t / P(size = n)`; at an inadmissible size it is the
zero measure, not a probability law. Through the Łukasiewicz coding, the mass is also the total
walk weight of the tree excursions of length `n`, and `n` times it is the total walk weight of the
bridge words of length `n` (Kemperman–Dwass in weight form, from the cycle lemma). Adapted from
`PoissonDeclumping/Bienayme/Conditioned.lean` with the constructed law in place of the source's
finite-tree measure. The set of admissible sizes and limits along it are not treated here.
-/

@[expose] public section

namespace BGW.LocallyFinite

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- The present addresses of a finite tree's image are the positive addresses of its vertices. -/
theorem present_toLocallyFinite_eq (t : PlaneTree) :
    {u | Present t.toLocallyFinite u} = PlaneTree.positiveAddress '' {u | t.IsVertex u} := by
  ext u
  constructor
  · intro hu
    obtain ⟨v, rfl⟩ := PlaneTree.exists_positiveAddress_of_present hu
    exact ⟨v, (PlaneTree.present_toLocallyFinite t v).mp hu, rfl⟩
  · rintro ⟨v, hv, rfl⟩
    exact (PlaneTree.present_toLocallyFinite t v).mpr hv

/-- The number of present addresses of a finite tree is its size. -/
theorem ncard_present_toLocallyFinite (t : PlaneTree) :
    {u | Present t.toLocallyFinite u}.ncard = t.size := by
  have hinj : Function.Injective PlaneTree.positiveAddress :=
    List.map_injective_iff.mpr Nat.succ_injective
  have hv : {u | t.IsVertex u} = ↑t.vertices.toFinset := by
    ext u
    simp [PlaneTree.mem_vertices_iff]
  rw [present_toLocallyFinite_eq, Set.ncard_image_of_injective _ hinj, hv, Set.ncard_coe_finset,
    List.toFinset_card_of_nodup (PlaneTree.nodup_vertices t), PlaneTree.length_vertices]

/-- The tree is finite and has exactly `n` present addresses (vertices, leaves included). The
finiteness conjunct is needed at `n = 0`: `Set.ncard` of an infinite set is `0`. -/
def sizeEvent (n : ℕ) : Set Tree := {T | FiniteVertices T ∧ {u | Present T u}.ncard = n}

theorem toLocallyFinite_mem_sizeEvent_iff (t : PlaneTree) (n : ℕ) :
    t.toLocallyFinite ∈ sizeEvent n ↔ t.size = n := by
  rw [← ncard_present_toLocallyFinite]
  exact ⟨fun h => h.2, fun h => ⟨t.finiteVertices_toLocallyFinite, h⟩⟩

theorem sizeEvent_eq_image (n : ℕ) :
    sizeEvent n = PlaneTree.toLocallyFinite '' {t : PlaneTree | t.size = n} := by
  ext T
  constructor
  · rintro ⟨hT, hn⟩
    obtain ⟨t, rfl⟩ := (exists_toLocallyFinite_iff T).mpr hT
    exact ⟨t, (toLocallyFinite_mem_sizeEvent_iff t n).mp ⟨hT, hn⟩, rfl⟩
  · rintro ⟨t, ht, rfl⟩
    exact (toLocallyFinite_mem_sizeEvent_iff t n).mpr ht

theorem measurableSet_sizeEvent (n : ℕ) : MeasurableSet (sizeEvent n) := by
  rw [sizeEvent_eq_image]
  exact (Set.to_countable _).image _ |>.measurableSet

/-- A tree has at least one vertex. -/
theorem sizeEvent_zero : sizeEvent 0 = ∅ := by
  ext T
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨hT, hn⟩
  obtain ⟨t, rfl⟩ := (exists_toLocallyFinite_iff T).mpr hT
  have := (toLocallyFinite_mem_sizeEvent_iff t 0).mp ⟨hT, hn⟩
  exact absurd this (PlaneTree.size_pos t).ne'

/-- The mass of the size event is the total weight of the plane trees of that size. -/
theorem bienaymeLaw_sizeEvent (μ : Measure ℕ) [IsProbabilityMeasure μ] (n : ℕ) :
    bienaymeLaw μ (sizeEvent n) =
      ∑' t : PlaneTree, if t.size = n then PlaneTree.weight (fun d => μ {d}) t else 0 := by
  have hA := measurableSet_sizeEvent n
  have hsub : sizeEvent n ⊆ {T | FiniteVertices T} := fun _ hT => hT.1
  have h : bienaymeLaw μ (sizeEvent n) =
      (bienaymeLaw μ).restrict {T | FiniteVertices T} (sizeEvent n) := by
    rw [Measure.restrict_apply hA, Set.inter_eq_left.mpr hsub]
  rw [h, bienaymeLaw_restrict_finiteVertices, Measure.sum_apply _ hA]
  refine tsum_congr fun t => ?_
  rw [Measure.smul_apply, Measure.dirac_apply' _ hA, smul_eq_mul]
  by_cases ht : t.size = n
  · simp [ht, (toLocallyFinite_mem_sizeEvent_iff t n).mpr ht]
  · have hn : t.toLocallyFinite ∉ sizeEvent n :=
      fun h' => ht ((toLocallyFinite_mem_sizeEvent_iff t n).mp h')
    simp [ht, hn]

/-- A size is admissible iff some tree of that size has positive weight. -/
theorem bienaymeLaw_sizeEvent_ne_zero_iff (μ : Measure ℕ) [IsProbabilityMeasure μ] (n : ℕ) :
    bienaymeLaw μ (sizeEvent n) ≠ 0 ↔
      ∃ t : PlaneTree, t.size = n ∧ PlaneTree.weight (fun d => μ {d}) t ≠ 0 := by
  rw [Ne, bienaymeLaw_sizeEvent, ENNReal.tsum_eq_zero]
  push Not
  constructor
  · rintro ⟨t, ht⟩
    by_cases h : t.size = n
    · exact ⟨t, h, by simpa [h] using ht⟩
    · exact absurd (by simp [h]) ht
  · rintro ⟨t, h, ht⟩
    exact ⟨t, by simpa [h] using ht⟩

/-- The mass of the size event is the total walk weight of the tree excursions of length `n`. -/
theorem bienaymeLaw_sizeEvent_eq_tsum_excursions (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (n : ℕ) :
    bienaymeLaw μ (sizeEvent n) = ∑' x : List ℤ,
      Set.indicator {x : List ℤ | IsTreeExcursion x ∧ x.length = n}
        (walkWeight fun d => μ {d}) x := by
  rw [bienaymeLaw_sizeEvent, PlaneTree.tsum_weight_size_eq_tsum_excursions]

/-- Kemperman–Dwass identity in weight form: `n * P(size = n)` is the total walk weight of the
bridge words of length `n`, with no hypothesis on `μ` beyond being a probability measure. -/
theorem natCast_mul_bienaymeLaw_sizeEvent (μ : Measure ℕ) [IsProbabilityMeasure μ] (n : ℕ) :
    (n : ℝ≥0∞) * bienaymeLaw μ (sizeEvent n) =
      ∑' x : List ℤ, Set.indicator (bridgeWords n) (walkWeight fun d => μ {d}) x := by
  rw [bienaymeLaw_sizeEvent, PlaneTree.natCast_mul_tsum_weight_size]

/-- A size is admissible iff some tree excursion of that length has positive walk weight. -/
theorem bienaymeLaw_sizeEvent_ne_zero_iff_excursion (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (n : ℕ) :
    bienaymeLaw μ (sizeEvent n) ≠ 0 ↔
      ∃ x : List ℤ, IsTreeExcursion x ∧ x.length = n ∧ walkWeight (fun d => μ {d}) x ≠ 0 := by
  rw [bienaymeLaw_sizeEvent_ne_zero_iff]
  constructor
  · rintro ⟨t, ht, hw⟩
    exact ⟨t.increments, PlaneTree.isTreeExcursion_increments t,
      by rw [PlaneTree.length_increments, ht], by rwa [PlaneTree.walkWeight_increments]⟩
  · rintro ⟨x, hx, hn, hw⟩
    obtain ⟨t, rfl, -⟩ := (PlaneTree.isTreeExcursion_iff_existsUnique x).mp hx
    exact ⟨t, by rwa [PlaneTree.length_increments] at hn,
      by rwa [PlaneTree.walkWeight_increments] at hw⟩

/-- At an admissible size, conditioning on the size gives a probability measure. -/
theorem isProbabilityMeasure_cond_sizeEvent (μ : Measure ℕ) [IsProbabilityMeasure μ] {n : ℕ}
    (h : bienaymeLaw μ (sizeEvent n) ≠ 0) :
    IsProbabilityMeasure (bienaymeLaw μ)[|sizeEvent n] :=
  cond_isProbabilityMeasure h

/-- At an admissible size, the conditioned law gives mass one to the size event. -/
theorem cond_sizeEvent_self (μ : Measure ℕ) [IsProbabilityMeasure μ] {n : ℕ}
    (h : bienaymeLaw μ (sizeEvent n) ≠ 0) :
    (bienaymeLaw μ)[|sizeEvent n] (sizeEvent n) = 1 :=
  cond_apply_self h (measure_ne_top _ _)

/-- At an inadmissible size, the conditioned measure is zero, not a probability law. -/
theorem cond_sizeEvent_eq_zero (μ : Measure ℕ) [IsProbabilityMeasure μ] {n : ℕ}
    (h : bienaymeLaw μ (sizeEvent n) = 0) : (bienaymeLaw μ)[|sizeEvent n] = 0 :=
  cond_eq_zero_of_meas_eq_zero h

/-- The atom of a finite tree in the conditioned law: its weight divided by the mass of the size
class when it has the right size, and zero otherwise. -/
theorem cond_sizeEvent_singleton (μ : Measure ℕ) [IsProbabilityMeasure μ] (n : ℕ)
    (t : PlaneTree) :
    (bienaymeLaw μ)[|sizeEvent n] {t.toLocallyFinite} =
      if t.size = n then
        PlaneTree.weight (fun d => μ {d}) t / bienaymeLaw μ (sizeEvent n) else 0 := by
  rw [cond_apply (measurableSet_sizeEvent n)]
  by_cases ht : t.size = n
  · rw [ite_eq_left ht, Set.inter_eq_right.mpr
      (Set.singleton_subset_iff.mpr ((toLocallyFinite_mem_sizeEvent_iff t n).mpr ht)),
      bienaymeLaw_toLocallyFinite, ENNReal.div_eq_inv_mul]
  · rw [ite_eq_right ht, Set.inter_singleton_eq_empty.mpr
      fun h => ht ((toLocallyFinite_mem_sizeEvent_iff t n).mp h), measure_empty, mul_zero]

end BGW.LocallyFinite
