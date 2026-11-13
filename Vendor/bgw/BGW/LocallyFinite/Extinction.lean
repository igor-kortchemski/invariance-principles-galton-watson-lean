/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.LocallyFinite.Atoms
public import BGW.GeneratingFunction
import Lean.Elab.Tactic.Omega

/-!
# Extinction by a finite depth and the least fixed point

`extinctBy n` is the event that every present address has length strictly less than `n`: the
root has depth zero, so `extinctBy 0 = ∅` and `extinctBy 1 = {leaf}`, and `extinctBy n` is
extinction by generation `n`. Under `bienaymeLaw μ`, for every offspring probability measure `μ`
(no mean, nondegeneracy or support condition), the root decomposition and the branching property
give `P(extinctBy (n + 1)) = f (P(extinctBy n))` with `f = offspringGF μ`, hence
`P(extinctBy n) = f^[n] 0`. A tree is finite exactly when it lies in some `extinctBy n`, so the
probability `q` of finiteness is the supremum of these iterates, satisfies `f q = q`, and is the
smallest fixed point of `f` in `[0, 1]`. By `bienaymeLaw_finiteVertices`, it is also the total
weight of the finite plane trees. The fixed-point argument follows
`PoissonDeclumping/Bienayme/Normalization.lean` (`offspringGF_bienayme_univ`) and the height
recursion of `PoissonDeclumping/Bienayme/Basic.lean`, whose convention is shifted by one here.
Classification by the mean, generation sizes and conditioning are not part of this module.
-/

@[expose] public section

namespace BGW.LocallyFinite

open MeasureTheory Filter
open scoped ENNReal Topology

/-- Extinction by generation `n`: no present address of length `n` or more. -/
def extinctBy (n : ℕ) : Set Tree := {T | ∀ u, Present T u → u.length < n}

theorem extinctBy_zero : extinctBy 0 = ∅ := by
  ext T
  exact ⟨fun h => absurd (h [] (present_nil T)) (by simp), fun h => h.elim⟩

theorem extinctBy_one : extinctBy 1 = {leaf} := by
  ext T
  constructor
  · intro h
    have hd : degree T = 0 := by
      by_contra hne
      have := h [1] ⟨le_rfl, by omega, trivial⟩
      simp at this
    exact eq_leaf_of_degree_zero hd
  · rintro rfl u hu
    cases u with
    | nil => simp
    | cons j u =>
      have h1 := hu.1
      have h2 : j ≤ 0 := hu.2.1
      omega

theorem monotone_extinctBy : Monotone extinctBy := fun _ _ hnm _ hT u hu =>
  (hT u hu).trans_le hnm

theorem mem_extinctBy_succ_iff (T : Tree) (n : ℕ) :
    T ∈ extinctBy (n + 1) ↔ ∀ j, 1 ≤ j → j ≤ degree T → child T j ∈ extinctBy n := by
  constructor
  · intro h j hj1 hj2 u hu
    have := h (j :: u) ⟨hj1, hj2, hu⟩
    simpa using this
  · intro h u hu
    cases u with
    | nil => simp
    | cons j u =>
      have := h j hu.1 hu.2.1 u hu.2.2
      simpa using this

theorem extinctBy_succ_eq (n : ℕ) :
    extinctBy (n + 1) = ⋃ k : ℕ, childrenEvent k fun _ => extinctBy n := by
  ext T
  rw [mem_extinctBy_succ_iff, Set.mem_iUnion]
  constructor
  · intro h
    exact ⟨degree T, rfl, fun i => h (i.val + 1) (by omega) (by omega)⟩
  · rintro ⟨k, hk, hc⟩ j hj1 hj2
    obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show j ≠ 0 by omega)
    exact hc ⟨i, by omega⟩

theorem measurableSet_extinctBy (n : ℕ) : MeasurableSet (extinctBy n) := by
  induction n with
  | zero => rw [extinctBy_zero]; exact MeasurableSet.empty
  | succ n ih =>
    rw [extinctBy_succ_eq]
    exact MeasurableSet.iUnion fun k => measurableSet_childrenEvent k _ fun _ => ih

/-! ### Finite trees -/

theorem finiteVertices_child {T : Tree} (hT : FiniteVertices T) {j : ℕ} (h1 : 1 ≤ j)
    (h2 : j ≤ degree T) : FiniteVertices (child T j) :=
  (hT.image List.tail).subset fun u hu => ⟨j :: u, ⟨h1, h2, hu⟩, rfl⟩

/-- A tree is finite iff all of its existing child subtrees are finite. -/
theorem finiteVertices_iff_children (T : Tree) :
    FiniteVertices T ↔ ∀ j, 1 ≤ j → j ≤ degree T → FiniteVertices (child T j) := by
  refine ⟨fun hT j h1 h2 => finiteVertices_child hT h1 h2, fun h => ?_⟩
  have hsub : {u | Present T u} ⊆ {[]} ∪ ⋃ j ∈ Finset.Icc 1 (degree T),
      List.cons j '' {u | Present (child T j) u} := by
    intro u hu
    cases u with
    | nil => exact Or.inl rfl
    | cons j u =>
      refine Or.inr (Set.mem_iUnion₂.mpr ⟨j, Finset.mem_Icc.mpr ⟨hu.1, hu.2.1⟩, u, hu.2.2, rfl⟩)
  exact ((Set.finite_singleton _).union (Set.Finite.biUnion (Finset.finite_toSet _)
    fun j hj => (h j (Finset.mem_Icc.mp hj).1 (Finset.mem_Icc.mp hj).2).image _)).subset hsub

theorem extinctBy_subset_finiteVertices (n : ℕ) {T : Tree} (hT : T ∈ extinctBy n) :
    FiniteVertices T := by
  induction n generalizing T with
  | zero => rw [extinctBy_zero] at hT; exact hT.elim
  | succ n ih =>
    exact (finiteVertices_iff_children T).mpr fun j h1 h2 =>
      ih (((mem_extinctBy_succ_iff T n).mp hT) j h1 h2)

/-- A finite tree is in `extinctBy n` for some `n`, and conversely. -/
theorem iUnion_extinctBy : ⋃ n : ℕ, extinctBy n = {T : Tree | FiniteVertices T} := by
  ext T
  constructor
  · intro h
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp h
    exact extinctBy_subset_finiteVertices n hn
  · intro hT
    obtain ⟨n, hn⟩ := hT.exists_height_bound
    exact Set.mem_iUnion.mpr ⟨n + 1, fun u hu => Nat.lt_succ_of_le (hn u hu)⟩

theorem finiteVertices_eq_iUnion_childrenEvent :
    {T : Tree | FiniteVertices T} =
      ⋃ k : ℕ, childrenEvent k fun _ => {T : Tree | FiniteVertices T} := by
  ext T
  rw [Set.mem_ofPred_eq, Set.mem_iUnion, finiteVertices_iff_children]
  constructor
  · intro h
    exact ⟨degree T, rfl, fun i => h (i.val + 1) (by omega) (by omega)⟩
  · rintro ⟨k, hk, hc⟩ j hj1 hj2
    obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show j ≠ 0 by omega)
    exact hc ⟨i, by omega⟩

/-! ### Probabilities -/

/-- One generation of branching: the mass of "all children in `A`" is the generating function
of the offspring law at the mass of `A`. -/
theorem bienaymeLaw_iUnion_childrenEvent (μ : Measure ℕ) [IsProbabilityMeasure μ] {A : Set Tree}
    (hA : MeasurableSet A) :
    bienaymeLaw μ (⋃ k : ℕ, childrenEvent k fun _ => A) = offspringGF μ (bienaymeLaw μ A) := by
  rw [measure_iUnion
    (fun i j hij => Set.disjoint_left.mpr fun T hi hj => hij (hi.1.symm.trans hj.1))
    fun k => measurableSet_childrenEvent k _ fun _ => hA]
  refine tsum_congr fun k => ?_
  rw [bienaymeLaw_childrenEvent μ k _ fun _ => hA]
  simp

theorem bienaymeLaw_extinctBy_zero (μ : Measure ℕ) [IsProbabilityMeasure μ] :
    bienaymeLaw μ (extinctBy 0) = 0 := by
  rw [extinctBy_zero, measure_empty]

theorem bienaymeLaw_extinctBy_succ (μ : Measure ℕ) [IsProbabilityMeasure μ] (n : ℕ) :
    bienaymeLaw μ (extinctBy (n + 1)) = offspringGF μ (bienaymeLaw μ (extinctBy n)) := by
  rw [extinctBy_succ_eq, bienaymeLaw_iUnion_childrenEvent μ (measurableSet_extinctBy n)]

/-- `P(extinctBy n) = f^[n] 0`. -/
theorem bienaymeLaw_extinctBy (μ : Measure ℕ) [IsProbabilityMeasure μ] (n : ℕ) :
    bienaymeLaw μ (extinctBy n) = (offspringGF μ)^[n] 0 := by
  induction n with
  | zero => exact bienaymeLaw_extinctBy_zero μ
  | succ n ih => rw [bienaymeLaw_extinctBy_succ, ih, Function.iterate_succ_apply']

theorem monotone_iterate_offspringGF (μ : Measure ℕ) :
    Monotone fun n : ℕ => (offspringGF μ)^[n] 0 :=
  (offspringGF_mono μ).monotone_iterate_of_le_map zero_le

/-- The probability that the tree is finite is the supremum of the iterates of the generating
function at `0`. -/
theorem bienaymeLaw_finiteVertices_eq_iSup (μ : Measure ℕ) [IsProbabilityMeasure μ] :
    bienaymeLaw μ {T | FiniteVertices T} = ⨆ n : ℕ, (offspringGF μ)^[n] 0 := by
  rw [← iUnion_extinctBy, Monotone.measure_iUnion monotone_extinctBy]
  exact iSup_congr (bienaymeLaw_extinctBy μ)

theorem tendsto_iterate_offspringGF (μ : Measure ℕ) [IsProbabilityMeasure μ] :
    Tendsto (fun n : ℕ => (offspringGF μ)^[n] 0) atTop
      (𝓝 (bienaymeLaw μ {T | FiniteVertices T})) := by
  rw [bienaymeLaw_finiteVertices_eq_iSup]
  exact tendsto_atTop_iSup (monotone_iterate_offspringGF μ)

/-- The probability that the tree is finite is a fixed point of the generating function. -/
theorem offspringGF_bienaymeLaw_finiteVertices (μ : Measure ℕ) [IsProbabilityMeasure μ] :
    offspringGF μ (bienaymeLaw μ {T | FiniteVertices T}) =
      bienaymeLaw μ {T | FiniteVertices T} := by
  rw [← bienaymeLaw_iUnion_childrenEvent μ measurableSet_finiteVertices,
    ← finiteVertices_eq_iUnion_childrenEvent]

/-- Minimality: every fixed point of the generating function bounds the probability of finiteness
from above. The bound `s ≤ 1` is not needed. -/
theorem bienaymeLaw_finiteVertices_le_of_fixedPoint (μ : Measure ℕ) [IsProbabilityMeasure μ]
    {s : ℝ≥0∞} (hs : offspringGF μ s = s) : bienaymeLaw μ {T | FiniteVertices T} ≤ s := by
  rw [bienaymeLaw_finiteVertices_eq_iSup]
  refine iSup_le fun n => ?_
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact (offspringGF_mono μ ih).trans_eq hs

/-- The probability that the tree is finite is the smallest fixed point of the offspring
generating function in `[0, 1]`. -/
theorem isLeast_bienaymeLaw_finiteVertices (μ : Measure ℕ) [IsProbabilityMeasure μ] :
    IsLeast {s : ℝ≥0∞ | s ≤ 1 ∧ offspringGF μ s = s} (bienaymeLaw μ {T | FiniteVertices T}) :=
  ⟨⟨prob_le_one, offspringGF_bienaymeLaw_finiteVertices μ⟩, fun _ hs =>
    bienaymeLaw_finiteVertices_le_of_fixedPoint μ hs.2⟩

/-- The total weight of the finite plane trees is the smallest fixed point of the generating
function in `[0, 1]`. -/
theorem isLeast_tsum_weight (μ : Measure ℕ) [IsProbabilityMeasure μ] :
    IsLeast {s : ℝ≥0∞ | s ≤ 1 ∧ offspringGF μ s = s}
      (∑' t : PlaneTree, PlaneTree.weight (fun d => μ {d}) t) := by
  rw [← bienaymeLaw_finiteVertices]
  exact isLeast_bienaymeLaw_finiteVertices μ

end BGW.LocallyFinite
