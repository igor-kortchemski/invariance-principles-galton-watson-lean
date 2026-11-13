/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.LocallyFinite.Branching
public import BGW.Tree.LocallyFinite
public import BGW.Tree.Weight

/-!
# Finite trees under the Bienaymé–Galton–Watson law

Through the bridge `PlaneTree.toLocallyFinite`, the law of a finite tree `t` is the product, over
all vertices of `t`, of the offspring probability of its outdegree (`bienaymeLaw_toLocallyFinite`).
No criticality or finiteness assumption is made. The finite trees form a measurable set of
probability at most one: its mass is the total weight of finite plane trees, which is the
probability that the tree is finite. Equality with one is not claimed here.

`PlaneTree` carries no `MeasurableSpace` instance. It is countable, so the measurability that the
transport needs is that of singletons and of the finite part in `Tree`, and the law of the finite
part is expressed as a sum of weighted Dirac masses at the images of finite trees. With the
discrete σ-algebra written explicitly, `toLocallyFinite` is a measurable embedding
(`measurableEmbedding_toLocallyFinite`).
-/

@[expose] public section

namespace BGW.LocallyFinite

open MeasureTheory
open scoped ENNReal

/-- The atom of a finite tree: the product of the offspring masses of all its outdegrees. -/
theorem bienaymeLaw_toLocallyFinite (μ : Measure ℕ) [IsProbabilityMeasure μ] (t : PlaneTree) :
    bienaymeLaw μ {t.toLocallyFinite} = PlaneTree.weight (fun d => μ {d}) t := by
  induction t with
  | node ts ih =>
    have hset : ({(PlaneTree.node ts).toLocallyFinite} : Set Tree) =
        childrenEvent ts.length (fun i => {(ts.get i).toLocallyFinite}) := by
      ext S
      constructor
      · rintro rfl
        refine ⟨by simp, fun i => ?_⟩
        have hc : (PlaneTree.node ts).children[i.val]? = some (ts.get i) := by simp
        exact PlaneTree.child_toLocallyFinite i.val hc
      · rintro ⟨hd, hc⟩
        apply eq_of_degree_child_eq (by simpa using hd)
        intro j hj hjd
        obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show j ≠ 0 by omega)
        have hi : i < ts.length := by simpa [hd] using hjd
        have hc' := hc ⟨i, hi⟩
        have hch : (PlaneTree.node ts).children[i]? = some (ts.get ⟨i, hi⟩) := by simp
        exact hc'.trans (PlaneTree.child_toLocallyFinite i hch).symm
    rw [hset, bienaymeLaw_childrenEvent μ _ _ (fun i => measurableSet_singleton _),
      PlaneTree.weight_node]
    congr 1
    have hmap : ts.map (PlaneTree.weight (fun d => μ {d})) =
        List.ofFn (fun i : Fin ts.length => PlaneTree.weight (fun d => μ {d}) (ts.get i)) := by
      rw [show (fun i : Fin ts.length => PlaneTree.weight (fun d => μ {d}) (ts.get i)) =
        PlaneTree.weight (fun d => μ {d}) ∘ ts.get from rfl, ← List.map_ofFn, List.ofFn_get]
    rw [hmap, List.prod_ofFn]
    exact Finset.prod_congr rfl fun i _ => ih _ (List.get_mem ts i)

theorem range_toLocallyFinite :
    Set.range PlaneTree.toLocallyFinite = {T : Tree | FiniteVertices T} :=
  Set.ext fun T => exists_toLocallyFinite_iff T

theorem measurableSet_finiteVertices : MeasurableSet {T : Tree | FiniteVertices T} := by
  rw [← range_toLocallyFinite]
  exact (Set.countable_range _).measurableSet

/-- With the discrete σ-algebra on the countable type `PlaneTree` (not installed as an instance),
the bridge is a measurable embedding into `Tree`. -/
theorem measurableEmbedding_toLocallyFinite :
    @MeasurableEmbedding PlaneTree Tree ⊤ _ PlaneTree.toLocallyFinite :=
  @MeasurableEmbedding.mk PlaneTree Tree ⊤ _ _ PlaneTree.toLocallyFinite_injective
    measurable_from_top fun s _ => (s.to_countable.image _).measurableSet

theorem pairwise_disjoint_singleton_toLocallyFinite :
    Pairwise (Function.onFun Disjoint fun t : PlaneTree => ({t.toLocallyFinite} : Set Tree)) :=
  fun _ _ hst => Set.disjoint_singleton.mpr fun h => hst (PlaneTree.toLocallyFinite_injective h)

/-- The probability that the tree is finite is the total weight of finite plane trees. -/
theorem bienaymeLaw_finiteVertices (μ : Measure ℕ) [IsProbabilityMeasure μ] :
    bienaymeLaw μ {T | FiniteVertices T} =
      ∑' t : PlaneTree, PlaneTree.weight (fun d => μ {d}) t := by
  rw [← range_toLocallyFinite, Set.range_eq_iUnion,
    measure_iUnion pairwise_disjoint_singleton_toLocallyFinite fun _ => measurableSet_singleton _]
  exact tsum_congr (bienaymeLaw_toLocallyFinite μ)

/-- The total weight of finite plane trees is at most one, for every offspring law. -/
theorem tsum_weight_le_one (μ : Measure ℕ) [IsProbabilityMeasure μ] :
    ∑' t : PlaneTree, PlaneTree.weight (fun d => μ {d}) t ≤ 1 := by
  rw [← bienaymeLaw_finiteVertices]
  exact prob_le_one

/-- On finite trees, the law is the sum of the weighted Dirac masses at their images. -/
theorem bienaymeLaw_restrict_finiteVertices (μ : Measure ℕ) [IsProbabilityMeasure μ] :
    (bienaymeLaw μ).restrict {T : Tree | FiniteVertices T} =
      Measure.sum fun t : PlaneTree =>
        PlaneTree.weight (fun d => μ {d}) t • Measure.dirac t.toLocallyFinite := by
  ext A hA
  rw [Measure.restrict_apply hA, Measure.sum_apply _ hA]
  have hA' : A ∩ {T | FiniteVertices T} = ⋃ t : PlaneTree, A ∩ {t.toLocallyFinite} := by
    rw [← range_toLocallyFinite, Set.range_eq_iUnion, Set.inter_iUnion]
  rw [hA', measure_iUnion
    (fun s t hst => (pairwise_disjoint_singleton_toLocallyFinite hst).mono
      Set.inter_subset_right Set.inter_subset_right)
    fun t => hA.inter (measurableSet_singleton _)]
  refine tsum_congr fun t => ?_
  rw [Measure.smul_apply, Measure.dirac_apply' _ hA, smul_eq_mul]
  by_cases h : t.toLocallyFinite ∈ A
  · rw [Set.inter_eq_right.mpr (Set.singleton_subset_iff.mpr h), bienaymeLaw_toLocallyFinite]
    simp [h]
  · rw [Set.inter_singleton_eq_empty.mpr h]
    simp [h]

end BGW.LocallyFinite
