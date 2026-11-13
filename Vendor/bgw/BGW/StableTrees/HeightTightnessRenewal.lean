/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.HeightTightnessUpcrossings
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-!
# Regenerated height crossings and their iid durations

Crossing times are built by restarting the offspring sequence at each previous
crossing. These are measurable, almost surely finite stopping times. Finite gap
histories are pre-stopped events, so stopped iid restart proves independence
and identifies every gap law with the first height-upcrossing law.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal Classical
open BGW.StableTrees.DiscreteForest
namespace BGW.StableTrees.HeightTightness

/-- First-upcrossing times are measurable, including their infinite value. -/
theorem measurable_heightUpcrossingStop (q : ℕ) : Measurable (heightUpcrossingStop q) := by
  apply ENat.measurable_iff.mpr
  intro n
  have he : (heightUpcrossingStop q) ⁻¹' {(n : ℕ∞)} =
      {ω | q ≤ forestHeight ω n} ∩ {ω | ∀ k < n, forestHeight ω k < q} := by
    ext ω
    exact heightUpcrossingStop_eq_natCast_iff q n ω
  rw [he]
  apply (measurableSet_le measurable_const (measurable_forestHeight n)).inter
  simp only [ofPred_forall]
  exact MeasurableSet.iInter fun k => MeasurableSet.iInter fun _ =>
    measurableSet_lt (measurable_forestHeight k) measurable_const

/-- Advance a stopping time to the next upcrossing of the regenerated height. -/
noncomputable def nextHeightUpcrossing (q : ℕ) (N : (ℕ → ℕ) → ℕ∞) (ω : ℕ → ℕ) : ℕ∞ :=
  N ω + heightUpcrossingStop q (shiftSeq (N ω).toNat ω)

private theorem nextHeightUpcrossing_eq_natCast_iff (q n : ℕ) (N : (ℕ → ℕ) → ℕ∞)
    (ω : ℕ → ℕ) : nextHeightUpcrossing q N ω = n ↔
      ∃ s k : ℕ, N ω = s ∧ heightUpcrossingStop q (shiftSeq s ω) = k ∧ s + k = n := by
  constructor
  · intro hn
    have hN : N ω ≠ ⊤ := by
      intro ht
      simp only [nextHeightUpcrossing, ht, top_add, ENat.top_ne_natCast] at hn
    have hK : heightUpcrossingStop q (shiftSeq (N ω).toNat ω) ≠ ⊤ := by
      intro ht
      simp only [nextHeightUpcrossing, ht, add_top, ENat.top_ne_natCast] at hn
    obtain ⟨s, hs⟩ := ENat.ne_top_iff_exists.mp hN
    obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp hK
    refine ⟨s, k, hs.symm, ?_, ?_⟩
    · simpa only [← hs, ENat.toNat_natCast] using hk.symm
    · dsimp [nextHeightUpcrossing] at hn
      rw [← hk, ← hs, ← Nat.cast_add] at hn
      exact ENat.natCast_inj.mp hn
  · rintro ⟨s, k, hs, hk, hsk⟩
    simp only [nextHeightUpcrossing, hs, ENat.toNat_natCast, hk, ← Nat.cast_add, hsk]

/-- Advancing to a regenerated height upcrossing preserves the stopping-time property. -/
theorem isSeqStoppingTime_nextHeightUpcrossing (q : ℕ) {N : (ℕ → ℕ) → ℕ∞}
    (hN : IsSeqStoppingTime N) : IsSeqStoppingTime (nextHeightUpcrossing q N) := by
  intro n ω ξ hn he
  obtain ⟨s, k, hs, hk, hsk⟩ := (nextHeightUpcrossing_eq_natCast_iff q n N ω).mp hn
  have hs' : N ξ = s := (hN s ω ξ hs (fun i hi => he i (by omega))).1
  have hk' : heightUpcrossingStop q (shiftSeq s ξ) = k :=
    (isSeqStoppingTime_heightUpcrossingStop q k (shiftSeq s ω) (shiftSeq s ξ) hk
      (fun i hi => he (s + i) (by omega))).1
  exact ⟨(nextHeightUpcrossing_eq_natCast_iff q n N ξ).mpr ⟨s, k, hs', hk', hsk⟩, Iff.rfl⟩

private theorem measurable_stoppedShift {N : (ℕ → ℕ) → ℕ∞} (hN : Measurable N) :
    Measurable (fun ω => shiftSeq (N ω).toNat ω) := by
  apply Measurable.of_eval
  intro i
  have hm : Measurable (fun p : ℕ × (ℕ → ℕ) => p.2 (p.1 + i)) :=
    measurable_from_prod_countable_right fun j => measurable_pi_apply (j + i)
  exact hm.comp (((measurable_of_countable ENat.toNat).comp hN).prodMk measurable_id)

/-- Restarting the offspring sequence at a finite stopping time preserves its law. -/
theorem map_stoppedShift_offspringSeqLaw (μ : PMF ℕ) {N : (ℕ → ℕ) → ℕ∞}
    (hNm : Measurable N) (hN : IsSeqStoppingTime N)
    (hfin : ∀ᵐ ω ∂(offspringSeqLaw μ).toMeasure, N ω ≠ ⊤) :
    (offspringSeqLaw μ).toMeasure.map (fun ω => shiftSeq (N ω).toNat ω) =
      (offspringSeqLaw μ).toMeasure := by
  apply Measure.ext
  intro A hA
  rw [Measure.map_apply (measurable_stoppedShift hNm) hA]
  have he : (fun ω => shiftSeq (N ω).toNat ω) ⁻¹' A =ᵐ[(offspringSeqLaw μ).toMeasure]
      Set.univ ∩ {ω | ∃ n : ℕ, N ω = n ∧ shiftSeq n ω ∈ A} := by
    filter_upwards [hfin] with ω hω
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hω
    simp only [← hn, ENat.toNat_natCast, mem_preimage, mem_inter_iff, mem_univ,
      true_and, mem_ofPred_eq, ENat.natCast_inj, exists_eq_left']
  rw [measure_congr he, stoppedRestart μ N hN hfin hN hA, measure_univ, one_mul]

/-- Advancing to a regenerated upcrossing preserves measurability. -/
theorem measurable_nextHeightUpcrossing (q : ℕ) {N : (ℕ → ℕ) → ℕ∞}
    (hN : Measurable N) : Measurable (nextHeightUpcrossing q N) := by
  have hK := (measurable_heightUpcrossingStop q).comp (measurable_stoppedShift hN)
  exact (measurable_of_countable (fun p : ℕ∞ × ℕ∞ => p.1 + p.2)).comp (hN.prodMk hK)

/-- Advancing an almost surely finite stopping time to a height upcrossing remains finite. -/
theorem ae_nextHeightUpcrossing_ne_top (μ : PMF ℕ) (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (q : ℕ) {N : (ℕ → ℕ) → ℕ∞} (hNm : Measurable N) (hN : IsSeqStoppingTime N)
    (hfin : ∀ᵐ ω ∂(offspringSeqLaw μ).toMeasure, N ω ≠ ⊤) :
    ∀ᵐ ω ∂(offspringSeqLaw μ).toMeasure, nextHeightUpcrossing q N ω ≠ ⊤ := by
  have hK := ae_heightUpcrossingStop_ne_top μ hc hne q
  rw [← map_stoppedShift_offspringSeqLaw μ hNm hN hfin] at hK
  have hK' := ae_of_ae_map (measurable_stoppedShift hNm).aemeasurable hK
  filter_upwards [hfin, hK'] with ω hω hω'
  exact (ENat.add_eq_top.not).mpr (not_or.mpr ⟨hω, hω'⟩)

/-- Successive integer stopping times of regenerated height upcrossings. -/
noncomputable def heightRegenerationStop (q : ℕ) : ℕ → (ℕ → ℕ) → ℕ∞
  | 0 => fun _ => 0
  | j + 1 => nextHeightUpcrossing q (heightRegenerationStop q j)

/-- Every regenerated crossing time is a stopping time of the offspring filtration. -/
theorem isSeqStoppingTime_heightRegenerationStop (q j : ℕ) :
    IsSeqStoppingTime (heightRegenerationStop q j) := by
  induction j with
  | zero => intro n ω ξ hn _; exact ⟨hn, Iff.rfl⟩
  | succ j ih => exact isSeqStoppingTime_nextHeightUpcrossing q ih

/-- Every regenerated crossing time is measurable. -/
theorem measurable_heightRegenerationStop (q j : ℕ) :
    Measurable (heightRegenerationStop q j) := by
  induction j with
  | zero => exact measurable_const
  | succ j ih => exact measurable_nextHeightUpcrossing q ih

/-- Every regenerated crossing time is almost surely finite. -/
theorem ae_heightRegenerationStop_ne_top (μ : PMF ℕ) (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (q j : ℕ) : ∀ᵐ ω ∂(offspringSeqLaw μ).toMeasure, heightRegenerationStop q j ω ≠ ⊤ := by
  induction j with
  | zero => exact Eventually.of_forall fun _ => by simp [heightRegenerationStop]
  | succ j ih =>
    exact ae_nextHeightUpcrossing_ne_top μ hc hne q
      (measurable_heightRegenerationStop q j) (isSeqStoppingTime_heightRegenerationStop q j) ih

/-- Crossing times increase with the number of regenerated upcrossings. -/
theorem monotone_heightRegenerationStop (q : ℕ) (ω : ℕ → ℕ) :
    Monotone (fun j => heightRegenerationStop q j ω) := by
  apply monotone_nat_of_le_succ
  intro j
  exact le_add_right le_rfl

/-- The integer duration of a regenerated height crossing, read on finite crossing times. -/
noncomputable def heightRegenerationGap (q j : ℕ) (ω : ℕ → ℕ) : ℕ :=
  (heightRegenerationStop q (j + 1) ω).toNat - (heightRegenerationStop q j ω).toNat

/-- Every regenerated crossing duration is measurable. -/
theorem measurable_heightRegenerationGap (q j : ℕ) : Measurable (heightRegenerationGap q j) :=
  (measurable_of_countable (fun p : ℕ∞ × ℕ∞ => p.1.toNat - p.2.toNat)).comp
    ((measurable_heightRegenerationStop q (j + 1)).prodMk
      (measurable_heightRegenerationStop q j))

private theorem heightRegenerationGap_eq_first {q j : ℕ} {ω : ℕ → ℕ}
    (hfin : heightRegenerationStop q (j + 1) ω ≠ ⊤) :
    heightRegenerationGap q j ω =
      (heightUpcrossingStop q (shiftSeq (heightRegenerationStop q j ω).toNat ω)).toNat := by
  have hh : heightRegenerationStop q j ω ≠ ⊤ ∧
      heightUpcrossingStop q (shiftSeq (heightRegenerationStop q j ω).toNat ω) ≠ ⊤ := by
    exact not_or.mp (ENat.add_eq_top.not.mp hfin)
  change (heightRegenerationStop q j ω +
    heightUpcrossingStop q (shiftSeq (heightRegenerationStop q j ω).toNat ω)).toNat -
      (heightRegenerationStop q j ω).toNat = _
  rw [ENat.toNat_add hh.1 hh.2, Nat.add_sub_cancel_left]

private theorem regenerationStop_eq_of_agree (q : ℕ) {i j n : ℕ} (hj : j ≤ i)
    {ω ξ : ℕ → ℕ} (hn : heightRegenerationStop q i ω = n)
    (he : ∀ k < n, ω k = ξ k) :
    heightRegenerationStop q j ω = heightRegenerationStop q j ξ := by
  have hle : heightRegenerationStop q j ω ≤ (n : ℕ∞) := by
    simpa only [hn] using monotone_heightRegenerationStop q ω hj
  have hfin := ne_top_of_le_ne_top (ENat.natCast_ne_top n) hle
  obtain ⟨r, hr⟩ := ENat.ne_top_iff_exists.mp hfin
  have hrn : r ≤ n := ENat.natCast_le_natCast.mp (hr ▸ hle)
  have hr' := (isSeqStoppingTime_heightRegenerationStop q j r ω ξ hr.symm
    (fun k hk => he k (by omega))).1
  exact hr.symm.trans hr'.symm

private theorem preStopped_gap_history (q i : ℕ) (S : Finset ℕ)
    (hS : ∀ j ∈ S, j < i) (A : ℕ → Set ℕ) :
    PreStopped (heightRegenerationStop q i) {ω | ∀ j ∈ S, heightRegenerationGap q j ω ∈ A j} := by
  intro n ω ξ hn he
  refine ⟨(isSeqStoppingTime_heightRegenerationStop q i n ω ξ hn he).1, ?_⟩
  have hg (j : ℕ) (hj : j ∈ S) : heightRegenerationGap q j ω = heightRegenerationGap q j ξ := by
    unfold heightRegenerationGap
    rw [regenerationStop_eq_of_agree q (show j + 1 ≤ i by have := hS j hj; omega) hn he,
      regenerationStop_eq_of_agree q (hS j hj).le hn he]
  constructor <;> intro h j hj
  · rw [← hg j hj]
    exact h j hj
  · rw [hg j hj]
    exact h j hj

/-- Restart factors each regenerated crossing duration from all preceding finite gap histories. -/
theorem heightRegenerationGap_history_factor (μ : PMF ℕ) (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (q i : ℕ) (S : Finset ℕ) (hS : ∀ j ∈ S, j < i) (A : ℕ → Set ℕ)
    {C : Set ℕ} (hC : MeasurableSet C) :
    (offspringSeqLaw μ).toMeasure
      ({ω | ∀ j ∈ S, heightRegenerationGap q j ω ∈ A j} ∩
        {ω | heightRegenerationGap q i ω ∈ C}) =
      (offspringSeqLaw μ).toMeasure {ω | ∀ j ∈ S, heightRegenerationGap q j ω ∈ A j} *
        (offspringSeqLaw μ).toMeasure {ω | (heightUpcrossingStop q ω).toNat ∈ C} := by
  let N := heightRegenerationStop q i
  let D : Set (ℕ → ℕ) := {ω | (heightUpcrossingStop q ω).toNat ∈ C}
  have hD : MeasurableSet D := ((measurable_of_countable ENat.toNat).comp
    (measurable_heightUpcrossingStop q)) hC
  have hr := stoppedRestart μ N (isSeqStoppingTime_heightRegenerationStop q i)
    (ae_heightRegenerationStop_ne_top μ hc hne q i) (preStopped_gap_history q i S hS A) hD
  have he : {ω | ∃ n : ℕ, N ω = n ∧ shiftSeq n ω ∈ D} =ᵐ[(offspringSeqLaw μ).toMeasure]
      {ω | heightRegenerationGap q i ω ∈ C} := by
    filter_upwards [ae_heightRegenerationStop_ne_top μ hc hne q i,
      ae_heightRegenerationStop_ne_top μ hc hne q (i + 1)] with ω hNi hNi'
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hNi
    have hg := heightRegenerationGap_eq_first hNi'
    rw [show heightRegenerationStop q i ω = n from hn.symm, ENat.toNat_natCast] at hg
    apply propext
    change (∃ m : ℕ, heightRegenerationStop q i ω = m ∧
      (heightUpcrossingStop q (shiftSeq m ω)).toNat ∈ C) ↔ heightRegenerationGap q i ω ∈ C
    rw [← hn]
    simp only [ENat.natCast_inj, exists_eq_left']
    rw [hg]
  rw [measure_congr (Filter.EventuallyEqSet.inter Filter.EventuallyEq.rfl he)] at hr
  exact hr

/-- Every regenerated duration has the law of the first height upcrossing. -/
theorem map_heightRegenerationGap (μ : PMF ℕ) (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (q i : ℕ) :
    (offspringSeqLaw μ).toMeasure.map (heightRegenerationGap q i) =
      (offspringSeqLaw μ).toMeasure.map (fun ω => (heightUpcrossingStop q ω).toNat) := by
  apply Measure.ext
  intro C hC
  rw [Measure.map_apply (measurable_heightRegenerationGap q i) hC,
    Measure.map_apply (f := fun ω => (heightUpcrossingStop q ω).toNat)
      ((measurable_of_countable ENat.toNat).comp
      (measurable_heightUpcrossingStop q)) hC]
  change (offspringSeqLaw μ).toMeasure {ω | heightRegenerationGap q i ω ∈ C} =
    (offspringSeqLaw μ).toMeasure {ω | (heightUpcrossingStop q ω).toNat ∈ C}
  have hh := heightRegenerationGap_history_factor μ hc hne q i ∅ (by simp) (fun _ => univ) hC
  simpa using hh

/-- Durations between successive regenerated height crossings are independent. -/
theorem iIndepFun_heightRegenerationGap (μ : PMF ℕ) (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (q : ℕ) : iIndepFun (fun j => heightRegenerationGap q j) (offspringSeqLaw μ).toMeasure := by
  apply iIndepFun_iff_measure_inter_preimage_eq_mul.mpr
  intro S A hA
  induction S using Finset.induction_on_max with
  | empty => simp
  | insert i S hS ih =>
    have hnot : i ∉ S := by intro hi; exact (hS i hi).false
    have hfac := heightRegenerationGap_history_factor μ hc hne q i S hS A
      (hA i (Finset.mem_insert_self i S))
    have hmarg := congrArg (fun ν : Measure ℕ => ν (A i))
      (map_heightRegenerationGap μ hc hne q i)
    rw [Measure.map_apply (measurable_heightRegenerationGap q i)
      (hA i (Finset.mem_insert_self i S)),
      Measure.map_apply (f := fun ω => (heightUpcrossingStop q ω).toNat)
      ((measurable_of_countable ENat.toNat).comp
        (measurable_heightUpcrossingStop q)) (hA i (Finset.mem_insert_self i S))] at hmarg
    change (offspringSeqLaw μ).toMeasure {ω | heightRegenerationGap q i ω ∈ A i} =
      (offspringSeqLaw μ).toMeasure {ω | (heightUpcrossingStop q ω).toNat ∈ A i} at hmarg
    have he : (⋂ j ∈ insert i S, (heightRegenerationGap q j) ⁻¹' A j) =
        {ω | ∀ j ∈ S, heightRegenerationGap q j ω ∈ A j} ∩
          {ω | heightRegenerationGap q i ω ∈ A i} := by
      ext ω
      simp only [mem_iInter, Finset.mem_insert, mem_preimage, mem_inter_iff, mem_ofPred_eq]
      aesop
    rw [he, hfac, ← hmarg, Finset.prod_insert hnot]
    have ih' := ih (fun j hj => hA j (Finset.mem_insert_of_mem hj))
    have he' : {ω | ∀ j ∈ S, heightRegenerationGap q j ω ∈ A j} =
        ⋂ j ∈ S, (heightRegenerationGap q j) ⁻¹' A j := by ext ω; simp
    rw [he', ih', mul_comm]
    rfl

end BGW.StableTrees.HeightTightness
