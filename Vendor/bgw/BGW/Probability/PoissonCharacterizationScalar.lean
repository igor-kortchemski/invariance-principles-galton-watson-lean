/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module
public import BGW.Probability.PoissonCharacterizationBasic
public import Mathlib.MeasureTheory.Measure.Continuity

/-! Scalar window probabilities and intensities of a time-simple Lévy point measure. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

namespace BGW.Probability

variable {Ω M : Type*} [MeasurableSpace Ω] [MeasurableSpace M]
variable {P : Measure Ω} [IsProbabilityMeasure P] {ξ : Ω → Measure (ℝ≥0 × M)} {A : Set M}

lemma one_le_count_of_ne_zero {μ : Measure (ℝ≥0 × M)} {S : Set (ℝ≥0 × M)}
    (hμ : μ = Measure.sum (fun p : S => Measure.dirac (p : ℝ≥0 × M)))
    {B : Set (ℝ≥0 × M)} (hB : MeasurableSet B) (hne : μ B ≠ 0) : 1 ≤ μ B := by
  rw [hμ, Measure.sum_apply _ hB] at hne ⊢
  have hex : ∃ p : S, (p : ℝ≥0 × M) ∈ B := by
    by_contra h
    push Not at h
    apply hne
    simp [Measure.dirac_apply' _ hB, h]
  obtain ⟨p, hp⟩ := hex
  calc
    1 = Measure.dirac (p : ℝ≥0 × M) B := by simp [Measure.dirac_apply' _ hB, hp]
    _ ≤ _ := ENNReal.le_tsum (f := fun q : S => Measure.dirac (q : ℝ≥0 × M) B) p

omit [IsProbabilityMeasure P] in
lemma ae_one_le_count_of_ne_zero (hξ : IsTimeSimpleLevy P ξ) {B : Set (ℝ≥0 × M)}
    (hB : MeasurableSet B) : ∀ᵐ ω ∂P, ξ ω B ≠ 0 → 1 ≤ ξ ω B := by
  filter_upwards [hξ.counting] with ω hω
  obtain ⟨S, _hS, hμ⟩ := hω
  exact one_le_count_of_ne_zero hμ hB

/-- **Stochastic continuity at zero**: the probability of at least one `A`-mark in `(0,h]`
tends to zero as `h ↓ 0`. -/
theorem tendsto_prob_mark_window (hξ : IsTimeSimpleLevy P ξ) (hA : IsFiniteRate P ξ A) :
    Tendsto (fun h : ℝ≥0 => P {ω | 1 ≤ ξ ω (Ioc 0 h ×ˢ A)}) (𝓝[>] 0) (𝓝 0) := by
  let u : ℕ → ℝ≥0 := fun n => (n + 1 : ℝ≥0)⁻¹
  let E : ℝ≥0 → Set Ω := fun h => {ω | 1 ≤ ξ ω (Ioc 0 h ×ˢ A)}
  have hE (h : ℝ≥0) : MeasurableSet (E h) :=
    measurableSet_Ici.preimage (measurable_count hξ.measurable (measurable_box hA.1))
  have huanti : Antitone u := by
    intro m n hmn
    dsimp [u]
    gcongr
  have hEmono : Monotone E := by
    intro m n hmn ω hω
    exact hω.trans (measure_mono (Set.prod_mono (Ioc_subset_Ioc_right hmn) Subset.rfl))
  have hSiInter : (⋂ n, Ioc 0 (u n) ×ˢ A) = ∅ := by
    apply eq_empty_iff_forall_notMem.2
    intro x hx
    have hpos : 0 < x.1 := (mem_iInter.mp hx 0).1.1
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (K := ℝ≥0) hpos
    have hxle : x.1 ≤ 1 / (n + 1 : ℝ≥0) := by
      simpa [u, one_div] using (mem_iInter.mp hx n).1.2
    exact (not_le_of_gt hn) hxle
  have hnull : P (⋂ n, E (u n)) = 0 := by
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [hA.2 1] with ω hfin
    intro hω
    have hlim := tendsto_measure_iInter_atTop (μ := ξ ω)
      (s := fun n => Ioc 0 (u n) ×ˢ A)
      (fun n => (measurable_box hA.1).nullMeasurableSet)
      (fun m n hmn => Set.prod_mono (Ioc_subset_Ioc_right (huanti hmn)) Subset.rfl)
      ⟨0, by simpa [u] using hfin.ne⟩
    rw [hSiInter, measure_empty] at hlim
    have hge : ∀ n, 1 ≤ ξ ω (Ioc 0 (u n) ×ˢ A) := fun n => mem_iInter.mp hω n
    have hone : (1 : ℝ≥0∞) ≤ 0 := ge_of_tendsto hlim (Eventually.of_forall hge)
    simp at hone
  have hseq : Tendsto (fun n => P (E (u n))) atTop (𝓝 0) := by
    have h := tendsto_measure_iInter_atTop (μ := P) (s := fun n => E (u n))
      (fun n => (hE _).nullMeasurableSet) (hEmono.comp_antitone huanti) ⟨0, measure_ne_top _ _⟩
    rw [hnull] at h
    exact h
  refine tendsto_order.2 ⟨fun a ha => Eventually.of_forall fun _ => ha.trans_le bot_le, ?_⟩
  intro a ha
  obtain ⟨n, hn⟩ := ((tendsto_order.1 hseq).2 a ha).exists
  have hupos : 0 < u n := by dsimp [u]; positivity
  filter_upwards [mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hupos)] with h hh
  exact (measure_mono (hEmono hh.le)).trans_lt hn

lemma windowShift_slice (μ : Measure (ℝ≥0 × M)) {a b u : ℝ≥0}
    (hau : a < u) (hub : u ≤ b) (hA : MeasurableSet A) :
    windowShift a b μ ({u - a} ×ˢ A) = μ ({u} ×ˢ A) := by
  rw [windowShift, Measure.map_apply (by fun_prop) ((measurableSet_singleton _).prod hA),
    windowRestrict, Measure.restrict_apply' (measurableSet_Ioc.prod MeasurableSet.univ)]
  congr 1
  ext p
  simp only [mem_inter_iff, mem_preimage, mem_prod, mem_singleton_iff, mem_Ioc, mem_univ,
    and_true]
  constructor
  · rintro ⟨⟨htime, hpA⟩, hap, -⟩
    have hp : a ≤ p.1 := hap.le
    have hu : a ≤ u := hau.le
    have heq := congrArg (fun x : ℝ≥0 => x + a) htime
    rw [tsub_add_cancel_of_le hp, tsub_add_cancel_of_le hu] at heq
    exact ⟨heq, hpA⟩
  · rintro ⟨hpu, hpA⟩
    subst u
    simp [hau, hub, hpA]

omit [IsProbabilityMeasure P] in
lemma prob_atom_eq_shift (hξ : IsTimeSimpleLevy P ξ) (hA : IsFiniteRate P ξ A)
    {a h u : ℝ≥0} (hau : a < u) (huh : u ≤ a + h) :
    P {ω | ξ ω ({u} ×ˢ A) ≠ 0} = P {ω | ξ ω ({u - a} ×ˢ A) ≠ 0} := by
  let B : Set (ℝ≥0 × M) := {u - a} ×ˢ A
  have hB : MeasurableSet B := (measurableSet_singleton _).prod hA.1
  have hzero : MeasurableSet {ν : Measure (ℝ≥0 × M) | ν B ≠ 0} :=
    (measurableSet_eq_fun (Measure.measurable_coe hB) measurable_const).compl
  have heval := congrArg (fun Q : Measure (Measure (ℝ≥0 × M)) =>
    Q {ν | ν B ≠ 0}) (hξ.stationary a h)
  rw [Measure.map_apply (measurable_windowShift hξ.measurable a (a + h)) hzero,
    Measure.map_apply (measurable_windowShift hξ.measurable 0 h) hzero] at heval
  have hleft : (fun ω => windowShift a (a + h) (ξ ω)) ⁻¹' {ν | ν B ≠ 0} =
      {ω | ξ ω ({u} ×ˢ A) ≠ 0} := by
    ext ω
    simp only [mem_preimage, mem_ofPred_eq]
    rw [windowShift_slice _ hau huh hA.1]
  have hright : (fun ω => windowShift 0 h (ξ ω)) ⁻¹' {ν | ν B ≠ 0} =
      {ω | ξ ω ({u - a} ×ˢ A) ≠ 0} := by
    ext ω
    simp only [mem_preimage, mem_ofPred_eq]
    change windowShift 0 h (ξ ω) ({u - a} ×ˢ A) ≠ 0 ↔ _
    have hs := windowShift_slice (ξ ω) (a := 0) (b := h) (u := u - a)
      (tsub_pos_iff_lt.2 hau) ((tsub_le_iff_right).2 (by simpa [add_comm] using huh)) hA.1
    simp only [tsub_zero] at hs
    rw [hs]
  rw [← hleft, ← hright]
  exact heval

omit [IsProbabilityMeasure P] in
lemma prob_atom_pos_eq (hξ : IsTimeSimpleLevy P ξ) (hA : IsFiniteRate P ξ A)
    {u v : ℝ≥0} (hu : 0 < u) (hv : 0 < v) :
    P {ω | ξ ω ({u} ×ˢ A) ≠ 0} = P {ω | ξ ω ({v} ×ˢ A) ≠ 0} := by
  rcases lt_trichotomy v u with hvu | rfl | huv
  · have h := prob_atom_eq_shift hξ hA (a := u - v) (h := v) (u := u)
      (tsub_lt_self hu hv) (by rw [tsub_add_cancel_of_le hvu.le])
    simpa [tsub_tsub_cancel_of_le hvu.le] using h
  · rfl
  · symm
    have h := prob_atom_eq_shift hξ hA (a := v - u) (h := u) (u := v)
      (tsub_lt_self hv hu) (by rw [tsub_add_cancel_of_le huv.le])
    simpa [tsub_tsub_cancel_of_le huv.le] using h

/-- **No deterministic-time atom** (derived): for fixed `s`, a.s. no mark at label `s`. -/
theorem ae_not_mark_at (hξ : IsTimeSimpleLevy P ξ) (hA : IsFiniteRate P ξ A) (s : ℝ≥0) :
    ∀ᵐ ω ∂P, ξ ω ({s} ×ˢ A) = 0 := by
  rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ s) with hs | hs
  · rw [← hs]
    filter_upwards [hξ.atZero] with ω hω
    exact le_antisymm
      ((measure_mono (Set.prod_mono Subset.rfl (subset_univ A))).trans_eq hω) bot_le
  · have hpos {u : ℝ≥0} (_hu : 0 < u) :
        P {ω | ξ ω ({u} ×ˢ A) ≠ 0} = P {ω | 1 ≤ ξ ω ({u} ×ˢ A)} :=
      measure_congr ((ae_one_le_count_of_ne_zero hξ
        ((measurableSet_singleton _).prod hA.1)).mono fun _ h => propext ⟨h, fun hle h0 => by
          simp [h0] at hle⟩)
    have hbound {u : ℝ≥0} (hu : 0 < u) :
        P {ω | ξ ω ({u} ×ˢ A) ≠ 0} ≤ P {ω | 1 ≤ ξ ω (Ioc 0 u ×ˢ A)} := by
      rw [hpos hu]
      have hsub : ({u} : Set ℝ≥0) ⊆ Ioc 0 u := singleton_subset_iff.2 ⟨hu, le_rfl⟩
      exact measure_mono fun ω hω => hω.trans (measure_mono
        (Set.prod_mono hsub Subset.rfl))
    have hzero : P {ω | ξ ω ({s} ×ˢ A) ≠ 0} = 0 := by
      apply le_antisymm _ bot_le
      apply ge_of_tendsto (tendsto_prob_mark_window hξ hA)
      filter_upwards [self_mem_nhdsWithin] with u hu
      rw [prob_atom_pos_eq hξ hA hs hu]
      exact hbound hu
    exact ae_iff.2 hzero

end BGW.Probability
