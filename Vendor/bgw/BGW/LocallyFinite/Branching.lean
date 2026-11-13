/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.LocallyFinite.Groups
public import BGW.LocallyFinite.Law
import Lean.Elab.Tactic.Omega

/-!
# The branching property of the Bienaymé–Galton–Watson law

`IsBienayme μ ρ` says that the root degree has law `ρ` and that, conditionally on the root
degree being `k` (when this has positive probability), the `k` ordered child subtrees have the
joint law `μ ⊗ ⋯ ⊗ μ`. The statement is about the whole finite family of children, so no
independence is built into the carrier. The constructed law satisfies it for every offspring
probability measure `ρ`. Adapted from `Freezing1/PlaneTreeBranching.lean` (the definition
`IsBienayme`) and `Freezing1/PlaneBienaymeBranching.lean`, with `childrenEvent` stated directly
instead of through the geometric `FirstChildStructure`.
-/

@[expose] public section

namespace BGW.LocallyFinite

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

/-- Exact root degree `k` together with a rectangle `E i` for the `i`-th child, `i < k`. -/
def childrenEvent (k : ℕ) (E : Fin k → Set Tree) : Set Tree :=
  {T | degree T = k ∧ ∀ i : Fin k, child T (i.val + 1) ∈ E i}

theorem measurableSet_childrenEvent (k : ℕ) (E : Fin k → Set Tree)
    (hE : ∀ i, MeasurableSet (E i)) : MeasurableSet (childrenEvent k E) := by
  apply MeasurableSet.inter
  · exact continuous_degree.measurable (measurableSet_singleton k)
  · have he : {T : Tree | ∀ i : Fin k, child T (i.val + 1) ∈ E i} =
        ⋂ i : Fin k, (fun T => child T (i.val + 1)) ⁻¹' E i := by
      ext T
      simp
    change MeasurableSet {T : Tree | ∀ i : Fin k, child T (i.val + 1) ∈ E i}
    rw [he]
    exact MeasurableSet.iInter fun i => (hE i).preimage (continuous_child (i.val + 1)).measurable

/-- The branching characterization of a Bienaymé–Galton–Watson law with offspring law
`offspringLaw`: the root has the offspring law and, conditionally on its count `k`, the children
are `k` independent copies of the law itself. It is meant for probability measures; the guard
`μ {degree = k} ≠ 0` is needed because conditioning on a null event gives the zero measure. -/
def IsBienayme (μ : Measure Tree) (offspringLaw : Measure ℕ) : Prop :=
  μ.map degree = offspringLaw ∧
    ∀ k : ℕ, μ {T | degree T = k} ≠ 0 →
      (ProbabilityTheory.cond μ {T | degree T = k}).map
        (fun T (i : Fin k) => child T (i.val + 1)) = Measure.pi (fun _ : Fin k => μ)

theorem raw_childrenEvent_measure (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (k : ℕ) (E : Fin k → Set Tree) (hE : ∀ i, MeasurableSet (E i)) :
    offspringFieldLaw μ {f | f [] = k ∧
      ∀ i : Fin k, prune (fun u => f ((i.val + 1) :: u)) ∈ E i} =
      μ {k} * ∏ i : Fin k, bienaymeLaw μ (E i) := by
  let B : Fin (k + 1) → Set Offspring :=
    Fin.cases {f | f [] = k} (fun i => prune ⁻¹' E i)
  have hB : ∀ i, MeasurableSet (B i) := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · change MeasurableSet {f : Offspring | f [] = k}
      exact (measurable_pi_apply [] : Measurable (fun f : Offspring => f []))
        (measurableSet_singleton (k : ℕ) : MeasurableSet ({k} : Set ℕ))
    · exact (hE j).preimage measurable_prune
  have hg := congrArg (fun ν : Measure (Fin (k + 1) → Offspring) =>
    ν (Set.pi Set.univ B)) (iid_branch_groups μ k)
  rw [Measure.map_apply (by fun_prop) (MeasurableSet.univ_pi hB),
    Measure.pi_pi, Fin.prod_univ_succ] at hg
  have he : (fun (f : Offspring) (i : Fin (k + 1)) (u : Address) => f (branchAddress k (i, u))) ⁻¹'
      Set.pi Set.univ B =
      {f | f [] = k ∧ ∀ i : Fin k, prune (fun u => f ((i.val + 1) :: u)) ∈ E i} := by
    ext f
    simp [Set.mem_pi, Fin.forall_fin_succ, B, branchAddress]
  rw [he] at hg
  have hroot : offspringFieldLaw μ (B 0) = μ {k} := by
    have hh := congrArg (fun ν : Measure ℕ => ν {k})
      (Measure.infinitePi_map_eval (fun _ : Address => μ) [])
    rw [Measure.map_apply (measurable_pi_apply [] : Measurable (fun f : Offspring => f []))
      (measurableSet_singleton (k : ℕ) : MeasurableSet ({k} : Set ℕ))] at hh
    exact hh
  calc
    _ = offspringFieldLaw μ (B 0) * ∏ i : Fin k, offspringFieldLaw μ (B i.succ) := hg
    _ = _ := by
      rw [hroot]
      congr 1
      apply Finset.prod_congr rfl
      intro i _
      exact (Measure.map_apply measurable_prune (hE i)).symm

theorem bienaymeLaw_childrenEvent (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (k : ℕ) (E : Fin k → Set Tree) (hE : ∀ i, MeasurableSet (E i)) :
    bienaymeLaw μ (childrenEvent k E) = μ {k} * ∏ i : Fin k, bienaymeLaw μ (E i) := by
  rw [bienaymeLaw, Measure.map_apply measurable_prune (measurableSet_childrenEvent k E hE)]
  have he : prune ⁻¹' childrenEvent k E =
      {f | f [] = k ∧ ∀ i : Fin k, prune (fun u => f ((i.val + 1) :: u)) ∈ E i} := by
    ext f
    change (f [] = k ∧ ∀ i : Fin k, child (prune f) (i.val + 1) ∈ E i) ↔ _
    constructor
    · rintro ⟨hf, hc⟩
      refine ⟨hf, fun i => ?_⟩
      have hi : 1 ≤ i.val + 1 ∧ i.val + 1 ≤ f [] := by
        rw [hf]
        exact ⟨by omega, by omega⟩
      simpa only [child_prune, ite_eq_left hi] using hc i
    · rintro ⟨hf, hc⟩
      refine ⟨hf, fun i => ?_⟩
      have hi : 1 ≤ i.val + 1 ∧ i.val + 1 ≤ f [] := by
        rw [hf]
        exact ⟨by omega, by omega⟩
      simpa only [child_prune, ite_eq_left hi] using hc i
  rw [he]
  exact raw_childrenEvent_measure μ k E hE

/-- For every offspring probability measure, the constructed law has the branching property. -/
theorem isBienayme_bienaymeLaw (μ : Measure ℕ) [IsProbabilityMeasure μ] :
    IsBienayme (bienaymeLaw μ) μ := by
  refine ⟨bienaymeLaw_map_degree μ, fun k hk => ?_⟩
  symm
  apply Measure.pi_eq
  intro E hE
  have hdeg : MeasurableSet {T : Tree | degree T = k} :=
    continuous_degree.measurable (measurableSet_singleton k)
  have hm : bienaymeLaw μ {T | degree T = k} = μ {k} := by
    have hh := congrArg (fun ν : Measure ℕ => ν {k}) (bienaymeLaw_map_degree μ)
    rw [Measure.map_apply continuous_degree.measurable (measurableSet_singleton k)] at hh
    exact hh
  rw [Measure.map_apply (Measurable.of_eval fun i =>
      (continuous_child (i.val + 1)).measurable) (MeasurableSet.univ_pi hE),
    ProbabilityTheory.cond_apply hdeg]
  have he : {T : Tree | degree T = k} ∩
      (fun T (i : Fin k) => child T (i.val + 1)) ⁻¹' Set.pi Set.univ E =
      childrenEvent k E := by
    ext T
    simp [childrenEvent]
  rw [he, bienaymeLaw_childrenEvent μ k E hE, ← hm, ← mul_assoc,
    ENNReal.inv_mul_cancel hk (measure_ne_top _ _), one_mul]

end BGW.LocallyFinite
