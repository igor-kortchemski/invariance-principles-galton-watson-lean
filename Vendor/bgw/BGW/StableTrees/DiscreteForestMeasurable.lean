/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.DiscreteForestBlocks
public import BGW.StableTrees.DiscreteForestPaths

/-!
# Measurability of discrete ladder blocks and selection

The totalized first-hit convention is measurable, including paths that never hit.
All decoding is performed through the countable space of finite degree lists.
The first block of size at least a cutoff, and its measurability, are defined here.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped Classical

namespace BGW.StableTrees.DiscreteForest

/-- The discrete sigma-algebra on degree words, local to this module. -/
local instance blockListMeasurable : MeasurableSpace (List ℕ) := ⊤
/-- Single degree words are measurable in the local discrete sigma-algebra. -/
local instance blockListSingleton : MeasurableSingletonClass (List ℕ) := ⟨fun _ => trivial⟩

private theorem measurable_nat_firstHit {Ω : Type*} [MeasurableSpace Ω]
    (p : Ω → ℕ → Prop) (hp : ∀ k, MeasurableSet {ω | p ω k}) :
    Measurable (fun ω => sInf {k | p ω k}) := by
  apply measurable_to_nat
  intro ω₀
  let n := sInf {k | p ω₀ k}
  change MeasurableSet {ω | sInf {k | p ω k} = n}
  by_cases hn : n = 0
  · rw [hn]
    have heq : {ω | sInf {k | p ω k} = 0} =
        {ω | p ω 0} ∪ ⋂ k, {ω | ¬p ω k} := by
      ext ω
      simp only [Nat.sInf_eq_zero, mem_union, mem_iInter, mem_ofPred_eq,
        Set.eq_empty_iff_forall_notMem]
    rw [heq]
    exact (hp 0).union (MeasurableSet.iInter fun k => (hp k).compl)
  · have heq : {ω | sInf {k | p ω k} = n} =
        {ω | p ω n} ∩ ⋂ k : ℕ, ⋂ (_ : k < n), {ω | ¬p ω k} := by
      ext ω
      simp only [mem_inter_iff, mem_iInter, mem_ofPred_eq]
      constructor
      · intro h
        have hex : Set.Nonempty {k | p ω k} := Nat.nonempty_of_pos_sInf (by omega)
        refine ⟨h ▸ Nat.sInf_mem hex, ?_⟩
        intro k hk
        exact Nat.notMem_of_lt_sInf (h.symm ▸ hk)
      · intro h
        rw [Nat.sInf_def (s := {k | p ω k}) ⟨n, h.1⟩]
        exact (Nat.find_eq_iff _).mpr h
    rw [heq]
    exact (hp n).inter (MeasurableSet.iInter fun k => MeasurableSet.iInter fun _ =>
      (hp k).compl)

/-- A totalized ladder time is measurable even on paths failing to reach the level. -/
theorem measurable_ladderTime (r : ℕ) : Measurable (fun ω => ladderTime ω r) :=
  measurable_nat_firstHit (fun ω k => walk ω k = -(r : ℤ))
    (fun k => measurableSet_eq_fun (measurable_walk k) measurable_const)

private theorem measurable_degreeList (s l : ℕ) :
    Measurable (fun ω : ℕ → ℕ => (List.range l).map (fun i => ω (s + i))) := by
  have heq : (fun ω : ℕ → ℕ => (List.range l).map (fun i => ω (s + i))) =
      (fun a : Fin l → ℕ => List.ofFn a) ∘ (fun ω i => ω (s + i.val)) := by
    funext ω
    apply List.ext_getElem
    · simp
    · intro i hi hi'
      simp
  rw [heq]
  exact (measurable_of_countable _).comp (by fun_prop)

/-- Each finite block degree list is a measurable function of the offspring sequence. -/
theorem measurable_blockDegrees (r : ℕ) : Measurable (fun ω => blockDegrees ω r) := by
  have hm : Measurable (fun p : (ℕ → ℕ) × (ℕ × ℕ) =>
      (List.range p.2.2).map (fun i => p.1 (p.2.1 + i))) :=
    measurable_from_prod_countable_left fun q => measurable_degreeList q.1 q.2
  exact hm.comp (measurable_id.prodMk ((measurable_ladderTime r).prodMk
    ((measurable_of_countable (fun q : ℕ × ℕ => q.1 - q.2)).comp
      ((measurable_ladderTime (r + 1)).prodMk (measurable_ladderTime r)))))

/-- Measurability of the sequence of block trees. -/
theorem measurable_blockLF : Measurable (fun ω r => blockLF ω r) := by
  apply Measurable.of_eval
  intro r
  exact (measurable_of_countable (fun a : List ℕ =>
    ((PlaneTree.ofDegrees? a).getD (PlaneTree.node [])).toLocallyFinite)).comp
      (measurable_blockDegrees r)

/-- The index of the first block of size `≥ n` (junk `0` if there is none). -/
noncomputable def firstLongIndex (n : ℕ) (ω : ℕ → ℕ) : ℕ :=
  sInf {r | n ≤ ladderTime ω (r + 1) - ladderTime ω r}

/-- The first tree among the ladder blocks of size `≥ n`; junk only on a null set. -/
noncomputable def firstLongTree (n : ℕ) (ω : ℕ → ℕ) : BGW.LocallyFinite.Tree :=
  blockLF ω (firstLongIndex n ω)

/-- Measurability of the first long tree. -/
theorem measurable_firstLongTree (n : ℕ) : Measurable (firstLongTree n) := by
  have hi : Measurable (firstLongIndex n) :=
    measurable_nat_firstHit _ (fun r =>
      measurableSet_le measurable_const
        ((measurable_of_countable (fun q : ℕ × ℕ => q.1 - q.2)).comp
          ((measurable_ladderTime (r + 1)).prodMk (measurable_ladderTime r))))
  have hm : Measurable (fun p : (ℕ → ℕ) × ℕ => blockLF p.1 p.2) :=
    measurable_from_prod_countable_left fun r => measurable_blockLF.eval
  exact hm.comp (measurable_id.prodMk hi)

end BGW.StableTrees.DiscreteForest
