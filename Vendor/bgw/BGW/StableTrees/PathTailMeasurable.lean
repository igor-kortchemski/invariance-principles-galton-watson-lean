/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.LongExtractionDefs
public import BGW.StableTrees.WalkPathTightness

/-!
# Measurability of the selected long block

Discrete first hits, selection, endpoints and closed increments are measurable even on
sequences with infinite ladder times, with the sealed totalization conventions.
-/

@[expose] public section

open MeasureTheory Set
open scoped Classical NNReal
open BGW.Skorokhod BGW.Probability.RealWalk

namespace BGW.StableTrees.PathTail

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


private theorem measurable_real_ladderTime (r : ℕ) :
    Measurable (fun ω : ℕ → ℝ => BGW.StableTrees.ladderTime ω r) :=
  (measurable_of_countable ENat.toNat).comp (measurable_walkHitTime r)

private theorem measurable_real_blockLength (r : ℕ) :
    Measurable (fun ω : ℕ → ℝ => ladderTime ω (r + 1) - ladderTime ω r) :=
  (measurable_of_countable (fun q : ℕ × ℕ => q.1 - q.2)).comp
    ((measurable_real_ladderTime (r + 1)).prodMk (measurable_real_ladderTime r))

private theorem measurable_real_firstLongIndex (n : ℕ) : Measurable (firstLongIndex n) := by
  apply measurable_nat_firstHit (fun ω r =>
    walkHitTime (r + 1) ω ≠ ⊤ ∧ n ≤ ladderTime ω (r + 1) - ladderTime ω r)
  intro r
  exact ((measurable_walkHitTime (r + 1)) (measurableSet_singleton ⊤)).compl.inter
    (measurableSet_le measurable_const (measurable_real_blockLength r))

private theorem measurable_countable_eval {Ω β : Type*}
    [MeasurableSpace Ω] [MeasurableSpace β] (f : ℕ → Ω → β)
    (hf : ∀ r, Measurable (f r)) (I : Ω → ℕ) (hI : Measurable I) :
    Measurable (fun ω => f (I ω) ω) := by
  have hm : Measurable (fun p : Ω × ℕ => f p.2 p.1) :=
    measurable_from_prod_countable_left hf
  exact hm.comp (measurable_id.prodMk hI)

private theorem measurable_selected_ladderTime (n j : ℕ) :
    Measurable (fun ω : ℕ → ℝ => ladderTime ω (firstLongIndex n ω + j)) :=
  measurable_countable_eval (fun r ω => ladderTime ω (r + j))
    (fun r => measurable_real_ladderTime (r + j)) (firstLongIndex n)
    (measurable_real_firstLongIndex n)

private theorem measurable_extractionEndpoints (n : ℕ) : Measurable (extractionEndpoints n) := by
  have hm (j : ℕ) : Measurable (fun ω : ℕ → ℝ =>
      (ladderTime ω (firstLongIndex n ω + j) : ℝ) / n) :=
    ((measurable_of_countable (fun k : ℕ => (k : ℝ))).comp
      (measurable_selected_ladderTime n j)).div_const n
  exact (hm 0).prodMk (hm 1)

private theorem measurable_selected_blockIncrements (n : ℕ) :
    Measurable (fun ω : ℕ → ℝ => blockIncrements ω (firstLongIndex n ω)) := by
  apply Measurable.of_eval
  intro i
  have hs := measurable_selected_ladderTime n 0
  have he := measurable_selected_ladderTime n 1
  have hl : Measurable (fun ω : ℕ → ℝ =>
      ladderTime ω (firstLongIndex n ω + 1) - ladderTime ω (firstLongIndex n ω)) :=
    (measurable_of_countable (fun q : ℕ × ℕ => q.1 - q.2)).comp (he.prodMk hs)
  have hv : Measurable (fun ω : ℕ → ℝ => ω (ladderTime ω (firstLongIndex n ω) + i)) := by
    have hm : Measurable (fun p : (ℕ → ℝ) × ℕ => p.1 (p.2 + i)) :=
      measurable_from_prod_countable_left fun r => measurable_pi_apply (r + i)
    exact hm.comp (measurable_id.prodMk hs)
  exact hv.ite (measurableSet_lt measurable_const hl) measurable_const

/-- The selected endpoint/cut triple is measurable for every scale, including junk branches. -/
theorem measurable_extractionTriple (b : ℝ) (n : ℕ) (T : ℝ≥0) :
    Measurable (extractionTriple b n T) :=
  (measurable_extractionEndpoints n).fst.prodMk
    ((measurable_extractionEndpoints n).snd.prodMk
      ((measurable_realStepPath (T : ℝ) n b).comp
        (measurable_selected_blockIncrements n)))

/-- The event that the selected block exists, is long, and ends within a fixed prefix is
measurable, with the sealed finite-hit guard. -/
theorem measurableSet_extractionLocalEvent (N n : ℕ) :
    MeasurableSet {ω : ℕ → ℝ | firstLongIndex n ω ∈ longBlockSet n ω ∧
      ladderTime ω (firstLongIndex n ω + 1) ≤ N} := by
  have hh : Measurable (fun ω : ℕ → ℝ => walkHitTime (firstLongIndex n ω + 1) ω) :=
    measurable_countable_eval (fun r ω => walkHitTime (r + 1) ω)
      (fun r => measurable_walkHitTime (r + 1)) (firstLongIndex n)
      (measurable_real_firstLongIndex n)
  have hs := measurable_selected_ladderTime n 0
  have he := measurable_selected_ladderTime n 1
  have hl : Measurable (fun ω : ℕ → ℝ =>
      ladderTime ω (firstLongIndex n ω + 1) - ladderTime ω (firstLongIndex n ω)) :=
    (measurable_of_countable (fun q : ℕ × ℕ => q.1 - q.2)).comp (he.prodMk hs)
  exact (((hh (measurableSet_singleton ⊤)).compl).inter
    (measurableSet_le measurable_const hl)).inter (measurableSet_le he measurable_const)

end BGW.StableTrees.PathTail
