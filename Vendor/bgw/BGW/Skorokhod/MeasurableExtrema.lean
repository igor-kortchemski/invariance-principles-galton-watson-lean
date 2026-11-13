/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.Skorokhod.Measurable
import Mathlib.Topology.Order.Bornology

/-!
# Measurable extrema of càdlàg paths

Right continuity reduces extrema over intervals to a countable family of evaluations.
-/

@[expose] public section

namespace BGW.Skorokhod

open Set Filter Topology

variable {T : ℝ} {E : Type*}

/-- Countably many interval times detect every open-set visit of every càdlàg path. -/
theorem exists_countable_detecting_times {J : Set (Set.Icc (0 : ℝ) T)}
    (hJ : J.OrdConnected) :
    ∃ K : Set J, K.Countable ∧ ∀ (E : Type*) [MetricSpace E] (f : D T E)
      (U : Set E), IsOpen U → ∀ s : J, f s ∈ U → ∃ q ∈ K, f q ∈ U := by
  classical
  obtain ⟨L, hLc, hLd⟩ := TopologicalSpace.exists_countable_dense J
  let M : Set J := {s | IsTop s}
  have hMc : M.Countable := by
    apply Set.Subsingleton.countable
    intro a ha b hb
    exact le_antisymm (hb a) (ha b)
  refine ⟨L ∪ M, hLc.union hMc, ?_⟩
  intro E _ f U hU s hs
  by_cases htop : IsTop s
  · exact ⟨s, Or.inr htop, hs⟩
  have hex : ∃ v : J, s < v := by
    simpa only [IsTop, not_forall, not_le] using htop
  obtain ⟨v, hv⟩ := hex
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU (f s) hs
  obtain ⟨δ, hδ, hclose⟩ := exists_right_oscillation f s hε
  let d := min δ ((v : Set.Icc (0 : ℝ) T) - (s : Set.Icc (0 : ℝ) T)) / 2
  have hsv : ((s : Set.Icc (0 : ℝ) T) : ℝ) < (v : Set.Icc (0 : ℝ) T) := hv
  have hd : 0 < d := half_pos (lt_min hδ (sub_pos.mpr hsv))
  have hdδ : d < δ := by
    have := min_le_left δ
      ((v : Set.Icc (0 : ℝ) T) - (s : Set.Icc (0 : ℝ) T))
    dsimp [d] at *
    linarith
  have hdv : d < (v : Set.Icc (0 : ℝ) T) - (s : Set.Icc (0 : ℝ) T) := by
    have := min_le_right δ
      ((v : Set.Icc (0 : ℝ) T) - (s : Set.Icc (0 : ℝ) T))
    dsimp [d] at *
    linarith
  let u : Set.Icc (0 : ℝ) T :=
    ⟨(s : Set.Icc (0 : ℝ) T) + d, by linarith [s.val.2.1], by linarith [v.val.2.2]⟩
  have hsu : s.val ≤ u := by change (s.val : ℝ) ≤ (s.val : ℝ) + d; linarith
  have huv : u ≤ v.val := by change (s.val : ℝ) + d ≤ (v.val : ℝ); linarith
  let w : J := ⟨u, hJ.out s.property v.property ⟨hsu, huv⟩⟩
  let V : Set J := {q | (s.val : ℝ) < q.val ∧ (q.val : ℝ) < (s.val : ℝ) + δ}
  have hV : IsOpen V :=
    (isOpen_lt continuous_const (continuous_subtype_val.comp continuous_subtype_val)).inter
      (isOpen_lt (continuous_subtype_val.comp continuous_subtype_val) continuous_const)
  have hw : w ∈ V := by change _ < (s.val : ℝ) + d ∧ _ < _; constructor <;> linarith
  obtain ⟨q, hqL, hqV⟩ := hLd.exists_mem_open hV ⟨w, hw⟩
  exact ⟨q, Or.inl hqL, hball (hclose q (le_of_lt hqV.1) hqV.2)⟩

/-- The supremum of a real path over an interval of times is measurable (C4.4). -/
theorem measurable_iSup_eval {J : Set (Set.Icc (0 : ℝ) T)} (hJ : J.OrdConnected) :
    Measurable (fun f : D T ℝ => ⨆ s : J, f s) := by
  classical
  obtain ⟨K, hKc, hK⟩ := exists_countable_detecting_times hJ
  let : Countable K := hKc
  by_cases hJne : Nonempty J
  · let := hJne
    have hKne : Nonempty K := by
      obtain ⟨s⟩ := hJne
      let f : D T ℝ := ⟨fun _ => 0, continuous_const.isCadlag⟩
      obtain ⟨q, hq, _⟩ := hK ℝ f univ isOpen_univ s (mem_univ _)
      exact ⟨⟨q, hq⟩⟩
    let := hKne
    have heq (f : D T ℝ) : (⨆ s : J, f s) = ⨆ q : K, f q.val := by
      have hb : BddAbove (range (fun s : J => f s)) :=
        (isBounded_range f).bddAbove.mono (by rintro _ ⟨s, rfl⟩; exact ⟨s.val, rfl⟩)
      have hbK : BddAbove (range (fun q : K => f q.val)) :=
        hb.mono (by rintro _ ⟨q, rfl⟩; exact ⟨q.val, rfl⟩)
      apply le_antisymm
      · apply ciSup_le
        intro s
        apply le_of_forall_lt
        intro c hc
        obtain ⟨q, hq, hcq⟩ := hK ℝ f (Ioi c) isOpen_Ioi s hc
        exact hcq.trans_le (le_ciSup hbK ⟨q, hq⟩)
      · exact ciSup_le fun q => le_ciSup hb q.val
    simp_rw [heq]
    exact Measurable.iSup fun q : K => measurable_eval q.val.val
  · have : IsEmpty J := not_nonempty_iff.mp hJne
    simpa only [iSup_of_empty', Real.sSup_empty] using
      (measurable_const : Measurable (fun _ : D T ℝ => (0 : ℝ)))

/-- The infimum of a real path over an interval of times is measurable (C4.4). -/
theorem measurable_iInf_eval {J : Set (Set.Icc (0 : ℝ) T)} (hJ : J.OrdConnected) :
    Measurable (fun f : D T ℝ => ⨅ s : J, f s) := by
  classical
  obtain ⟨K, hKc, hK⟩ := exists_countable_detecting_times hJ
  let : Countable K := hKc
  by_cases hJne : Nonempty J
  · let := hJne
    have hKne : Nonempty K := by
      obtain ⟨s⟩ := hJne
      let f : D T ℝ := ⟨fun _ => 0, continuous_const.isCadlag⟩
      obtain ⟨q, hq, _⟩ := hK ℝ f univ isOpen_univ s (mem_univ _)
      exact ⟨⟨q, hq⟩⟩
    let := hKne
    have heq (f : D T ℝ) : (⨅ s : J, f s) = ⨅ q : K, f q.val := by
      have hb : BddBelow (range (fun s : J => f s)) :=
        (isBounded_range f).bddBelow.mono (by rintro _ ⟨s, rfl⟩; exact ⟨s.val, rfl⟩)
      have hbK : BddBelow (range (fun q : K => f q.val)) :=
        hb.mono (by rintro _ ⟨q, rfl⟩; exact ⟨q.val, rfl⟩)
      apply le_antisymm
      · exact le_ciInf fun q => ciInf_le hb q.val
      · apply le_ciInf
        intro s
        apply le_of_forall_gt
        intro c hc
        obtain ⟨q, hq, hcq⟩ := hK ℝ f (Iio c) isOpen_Iio s hc
        exact (ciInf_le hbK ⟨q, hq⟩).trans_lt hcq
    simp_rw [heq]
    exact Measurable.iInf fun q : K => measurable_eval q.val.val
  · have : IsEmpty J := not_nonempty_iff.mp hJne
    have hz (f : D T ℝ) : (⨅ s : J, f s) = 0 := by
      exact (@iSup_of_empty' ℝᵒᵈ J _ this (fun s => f s)).trans Real.sInf_empty
    simp_rw [hz]
    exact measurable_const

end BGW.Skorokhod
