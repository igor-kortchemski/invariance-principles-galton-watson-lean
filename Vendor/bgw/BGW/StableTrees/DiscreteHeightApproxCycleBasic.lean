/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.DiscreteHeightApproxLevelMean

/-!
# Measurability of weak ascending cycles

The totalized natural epochs and finite cycle occupations are measurable on all
sequences. Prefix agreement determines every walk coordinate in the prefix.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal Classical
open BGW.StableTrees.DiscreteForest

namespace BGW.StableTrees.DiscreteHeightApprox

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

/-- The next-epoch map is jointly measurable in the sequence and starting time. -/
private theorem measurable_nextEpoch :
    Measurable (fun p : (ℕ → ℕ) × ℕ => nextEpoch p.1 p.2) := by
  apply measurable_from_prod_countable_left
  intro s
  exact measurable_nat_firstHit (fun ω u => s < u ∧ walk ω s ≤ walk ω u)
    (fun u => by
      by_cases hsu : s < u
      · simpa only [hsu, true_and] using
          measurableSet_le (measurable_walk s) (measurable_walk u)
      · simp only [hsu, false_and, Set.ofPred_false]
        exact MeasurableSet.empty)

/-- Every totalized natural weak epoch is measurable. -/
theorem measurable_weakEpoch (i : ℕ) : Measurable (fun ω => weakEpoch ω i) := by
  induction i with
  | zero => exact measurable_const
  | succ i ih =>
    simp only [weakEpoch_succ]
    exact measurable_nextEpoch.comp (measurable_id.prodMk ih)

private theorem measurable_fixedCycleCount (a : ℝ) (s t : ℕ) :
    Measurable (fun ω : ℕ → ℕ => ((Finset.Ico s t).filter
      (fun u => (((walk ω s - walk ω u : ℤ)) : ℝ) < a)).card) := by
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
  apply Finset.measurable_sum
  intro u _
  apply Measurable.ite _ measurable_const measurable_const
  exact measurableSet_lt ((measurable_of_countable (fun z : ℤ => (z : ℝ))).comp
    ((measurable_walk s).sub (measurable_walk u))) measurable_const

/-- Every finite cycle occupation is measurable, including its totalized values. -/
theorem measurable_clusterVisits (a : ℝ) (i : ℕ) :
    Measurable (fun ω => clusterVisits ω a i) := by
  let F (p : (ℕ → ℕ) × (ℕ × ℕ)) : ℕ :=
    ((Finset.Ico p.2.1 p.2.2).filter
      (fun u => (((walk p.1 p.2.1 - walk p.1 u : ℤ)) : ℝ) < a)).card
  let G (ω : ℕ → ℕ) := (ω, (weakEpoch ω i, weakEpoch ω (i + 1)))
  have hm : Measurable F :=
    measurable_from_prod_countable_left fun q => measurable_fixedCycleCount a q.1 q.2
  have harg : Measurable G :=
    measurable_id.prodMk ((measurable_weakEpoch i).prodMk (measurable_weakEpoch (i + 1)))
  have he : (fun ω => clusterVisits ω a i) = F ∘ G := by
    funext ω
    apply congrArg Finset.card
    ext u
    simp only [Finset.mem_filter, Finset.mem_Ico]
    rfl
  rw [he]
  exact hm.comp harg

/-- Every finite weak ascending record count is measurable. -/
theorem measurable_weakLadderCount (k : ℕ) : Measurable (fun ω => weakLadderCount ω k) := by
  simp only [weakLadderCount, Finset.card_eq_sum_ones, Finset.sum_filter,
    reflGap_zero_iff_record]
  apply Finset.measurable_sum
  intro u _
  apply Measurable.ite _ measurable_const measurable_const
  simp only [ofPred_forall]
  exact MeasurableSet.iInter fun v => MeasurableSet.iInter fun _ =>
    measurableSet_le (measurable_walk v) (measurable_walk u)

/-- Prefix agreement determines every weak record count within the prefix. -/
theorem weakLadderCount_eq_of_agree {ω ξ : ℕ → ℕ} {n : ℕ}
    (he : ∀ i < n, ω i = ξ i) {u : ℕ} (hu : u ≤ n) :
    weakLadderCount ω u = weakLadderCount ξ u := by
  unfold weakLadderCount
  congr 1
  apply Finset.filter_congr
  intro v hv
  obtain ⟨_, hvu⟩ := Finset.mem_Icc.mp hv
  rw [reflGap_zero_iff_record, reflGap_zero_iff_record]
  have hw (k : ℕ) (hk : k ≤ n) := walk_eq_of_agree he hk
  constructor <;> intro hr k hkv
  · rw [← hw k (by omega), ← hw v (by omega)]
    exact hr k hkv
  · rw [hw k (by omega), hw v (by omega)]
    exact hr k hkv

end BGW.StableTrees.DiscreteHeightApprox
