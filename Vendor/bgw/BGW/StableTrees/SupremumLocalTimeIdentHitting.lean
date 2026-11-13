/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.SupremumLocalTimeIdentBasic

/-!
# Strict hitting times of the totalized clock

An increasing crossing predicate is detected by rational times after the crossing. This
retains raw prefix measurability without assuming continuity of the extended clock.

Reference: J. Bertoin, *Lévy Processes*, Cambridge University Press, 1996, Chapter IV.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees

/-- Strict hitting time `a_z = inf{t | p(t) > z}` of the ENNReal clock (the stopping-time
representative of the inverse; `⊤` if never). -/
noncomputable def supHitting (θ : ℝ) (z : ℝ≥0) (f : DLoc) : ℝ≥0∞ :=
  ⨅ t : ℝ≥0, if (z : ℝ≥0∞) < supLocalTimeENN θ f t then (t : ℝ≥0∞) else ⊤

/-- Blow-up time `b = inf{t | p(t) = ⊤}` (`⊤` if never; `b = ⊤` almost surely). -/
noncomputable def supBlowup (θ : ℝ) (f : DLoc) : ℝ≥0∞ :=
  ⨅ t : ℝ≥0, if supLocalTimeENN θ f t = ⊤ then (t : ℝ≥0∞) else ⊤

private theorem inf_crossing_lt_iff {U : ℝ≥0 → Prop} [DecidablePred U]
    (hU : ∀ s t, s ≤ t → U s → U t) (a : ℝ≥0∞) :
    (⨅ t : ℝ≥0, if U t then (t : ℝ≥0∞) else ⊤) < a ↔
      ∃ q : ℚ, U (Real.toNNReal q) ∧ (Real.toNNReal q : ℝ≥0∞) < a := by
  constructor
  · intro h
    obtain ⟨t, ht⟩ := iInf_lt_iff.mp h
    split_ifs at ht with hUt
    · obtain ⟨v, htv, hva⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp ht
      have htvR : (t : ℝ) < v := by exact_mod_cast htv
      obtain ⟨q, htq, hqv⟩ := exists_rat_btwn htvR
      have hq0 : (0 : ℝ) ≤ q := t.coe_nonneg.trans htq.le
      have htqN : t ≤ Real.toNNReal q := by
        exact_mod_cast (show (t : ℝ) ≤ (Real.toNNReal q : ℝ) by
          rw [Real.coe_toNNReal _ hq0]; exact htq.le)
      have hqvN : Real.toNNReal q < v := by
        exact_mod_cast (show (Real.toNNReal q : ℝ) < v by
          rw [Real.coe_toNNReal _ hq0]; exact hqv)
      exact ⟨q, hU _ _ htqN hUt, (ENNReal.coe_le_coe.mpr hqvN.le).trans_lt hva⟩
    · exact (not_lt_of_ge le_top ht).elim
  · rintro ⟨q, hq, hqa⟩
    exact (iInf_le_of_le (Real.toNNReal q)
      (by simp only [ite_eq_left hq]; exact le_rfl)).trans_lt hqa

private theorem inf_crossing_eq_rat {U : ℝ≥0 → Prop} [DecidablePred U]
    (hU : ∀ s t, s ≤ t → U s → U t) :
    (⨅ t : ℝ≥0, if U t then (t : ℝ≥0∞) else ⊤) =
      ⨅ q : ℚ, if U (Real.toNNReal q) then (Real.toNNReal q : ℝ≥0∞) else ⊤ := by
  apply eq_of_forall_gt_iff
  intro a
  rw [inf_crossing_lt_iff hU, iInf_lt_iff]
  constructor
  · rintro ⟨q, hq, hqa⟩
    exact ⟨q, by simpa only [ite_eq_left hq] using hqa⟩
  · rintro ⟨q, hq⟩
    split_ifs at hq with hUq
    · exact ⟨q, hUq, hq⟩
    · exact (not_lt_of_ge le_top hq).elim

/-- Joint measurability of the strict hitting representative. -/
theorem measurable_supHitting_uncurry (θ : ℝ) :
    Measurable (fun p : ℝ≥0 × DLoc => supHitting θ p.1 p.2) := by
  classical
  have he : (fun p : ℝ≥0 × DLoc => supHitting θ p.1 p.2) =
      (fun p => ⨅ q : ℚ, if (p.1 : ℝ≥0∞) <
        supLocalTimeENN θ p.2 (Real.toNNReal q) then
          (Real.toNNReal q : ℝ≥0∞) else ⊤) := by
    funext p
    exact inf_crossing_eq_rat (fun s t hst hs =>
      hs.trans_le (monotone_supLocalTimeENN θ p.2 hst))
  rw [he]
  apply Measurable.iInf
  intro q
  have hm : Measurable (fun f : DLoc =>
      supLocalTimeENN θ f (Real.toNNReal q)) :=
    (measurable_supLocalTimeENN_filtration θ _).mono (DLoc.filtration.le _) le_rfl
  exact Measurable.ite (measurableSet_lt (by fun_prop) (hm.comp measurable_snd))
    (measurable_const : Measurable (fun _ : ℝ≥0 × DLoc =>
      (Real.toNNReal q : ℝ≥0∞))) measurable_const

/-- Measurability of the blow-up time. -/
theorem measurable_supBlowup (θ : ℝ) : Measurable (supBlowup θ) := by
  classical
  have he : supBlowup θ = (fun f => ⨅ q : ℚ,
      if supLocalTimeENN θ f (Real.toNNReal q) = ⊤ then
        (Real.toNNReal q : ℝ≥0∞) else ⊤) := by
    funext f
    exact inf_crossing_eq_rat (fun s t hst hs =>
      top_le_iff.mp (hs ▸ monotone_supLocalTimeENN θ f hst))
  rw [he]
  apply Measurable.iInf
  intro q
  have hm : Measurable (fun f : DLoc =>
      supLocalTimeENN θ f (Real.toNNReal q)) :=
    (measurable_supLocalTimeENN_filtration θ _).mono (DLoc.filtration.le _) le_rfl
  exact Measurable.ite (measurableSet_eq_fun hm measurable_const)
    (measurable_const : Measurable (fun _ : DLoc =>
      (Real.toNNReal q : ℝ≥0∞))) measurable_const

/-- The strict hitting representative is a stopping time, for every real index. -/
theorem isStoppingTime_supHitting (θ : ℝ) (z : ℝ≥0) :
    IsStoppingTime DLoc.filtration (supHitting θ z) := by
  apply MeasureTheory.isStoppingTime_of_measurableSet_lt_of_isRightContinuous
  intro t
  change MeasurableSet[DLoc.filtration t]
    {f : DLoc | supHitting θ z f < (t : ℝ≥0∞)}
  have hset : {f : DLoc | supHitting θ z f < t} =
      ⋃ q : {q : ℚ // Real.toNNReal q < t},
        {f : DLoc | (z : ℝ≥0∞) < supLocalTimeENN θ f (Real.toNNReal q.1)} := by
    ext f
    change (⨅ u : ℝ≥0, if (z : ℝ≥0∞) < supLocalTimeENN θ f u then
      (u : ℝ≥0∞) else ⊤) < (t : ℝ≥0∞) ↔ _
    rw [inf_crossing_lt_iff (fun s u hsu hs =>
      hs.trans_le (monotone_supLocalTimeENN θ f hsu))]
    simp only [mem_ofPred_eq, mem_iUnion, ENNReal.coe_lt_coe]
    constructor
    · rintro ⟨q, hq, hqt⟩
      exact ⟨⟨q, hqt⟩, hq⟩
    · rintro ⟨q, hq⟩
      exact ⟨q.1, hq, q.2⟩
  rw [hset]
  apply MeasurableSet.iUnion
  intro q
  exact (DLoc.filtration.mono q.2.le) _
    (measurableSet_lt measurable_const (measurable_supLocalTimeENN_filtration θ _))

end BGW.StableTrees
