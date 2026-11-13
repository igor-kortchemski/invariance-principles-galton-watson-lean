/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module
public import BGW.Probability.PoissonCharacterizationScalar
public import Mathlib.Analysis.SpecialFunctions.Exp

/-! Window-split identities, stationarity, and the no-arrival functional equation. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal Matrix

namespace BGW.Probability

variable {Ω M : Type*} [MeasurableSpace Ω] [MeasurableSpace M]
variable {P : Measure Ω} [IsProbabilityMeasure P] {ξ : Ω → Measure (ℝ≥0 × M)} {A : Set M}

omit [IsProbabilityMeasure P] in
lemma ae_finite_box (hA : IsFiniteRate P ξ A) {s t : ℝ≥0} (_hst : s ≤ t) :
    ∀ᵐ ω ∂P, ξ ω (Ioc s t ×ˢ A) < ⊤ := by
  filter_upwards [hA.2 t] with ω hω
  have hsub : Ioc s t ×ˢ A ⊆ Ioc 0 t ×ˢ A :=
    Set.prod_mono (Ioc_subset_Ioc_left (zero_le : (0 : ℝ≥0) ≤ s)) Subset.rfl
  exact (measure_mono hsub).trans_lt hω

lemma windowShift_box (μ : Measure (ℝ≥0 × M)) (a h : ℝ≥0) (hA : MeasurableSet A) :
    windowShift a (a + h) μ (Ioc 0 h ×ˢ A) = μ (Ioc a (a + h) ×ˢ A) := by
  rw [windowShift, Measure.map_apply (by fun_prop) ((measurableSet_Ioc).prod hA),
    windowRestrict, Measure.restrict_apply' (measurableSet_Ioc.prod MeasurableSet.univ)]
  congr 1
  ext p
  simp only [mem_inter_iff, mem_preimage, mem_prod, mem_Ioc, mem_univ, and_true]
  constructor
  · rintro ⟨⟨⟨hpos, hle⟩, hpA⟩, hap, -⟩
    have hp_le : p.1 ≤ a + h := by
      rw [add_comm]
      exact (tsub_le_iff_right).1 hle
    exact ⟨⟨tsub_pos_iff_lt.1 hpos, hp_le⟩, hpA⟩
  · rintro ⟨⟨hap, hpb⟩, hpA⟩
    exact ⟨⟨⟨tsub_pos_iff_lt.2 hap, (tsub_le_iff_right).2 (by simpa [add_comm] using hpb)⟩,
      hpA⟩, hap, hpb⟩

omit [IsProbabilityMeasure P] in
lemma lintegral_window_stationary (hξ : IsTimeSimpleLevy P ξ) (hA : IsFiniteRate P ξ A)
    (a h : ℝ≥0) : ∫⁻ ω, ξ ω (Ioc a (a + h) ×ˢ A) ∂P =
      ∫⁻ ω, ξ ω (Ioc 0 h ×ˢ A) ∂P := by
  let B : Set (ℝ≥0 × M) := Ioc 0 h ×ˢ A
  have hB : MeasurableSet B := measurableSet_Ioc.prod hA.1
  have h₁ := lintegral_map (Measure.measurable_coe hB)
    (measurable_windowShift hξ.measurable a (a + h)) (μ := P)
  have h₂ := lintegral_map (Measure.measurable_coe hB)
    (measurable_windowShift hξ.measurable 0 h) (μ := P)
  calc
    _ = ∫⁻ ω, windowShift a (a + h) (ξ ω) B ∂P := by
      apply lintegral_congr
      intro ω
      rw [windowShift_box _ _ _ hA.1]
    _ = ∫⁻ ν, ν B ∂P.map (fun ω => windowShift a (a + h) (ξ ω)) := h₁.symm
    _ = ∫⁻ ν, ν B ∂P.map (fun ω => windowShift 0 h (ξ ω)) := by rw [hξ.stationary a h]
    _ = ∫⁻ ω, windowShift 0 h (ξ ω) B ∂P := h₂
    _ = _ := by
      apply lintegral_congr
      intro ω
      dsimp [B]
      have hs := windowShift_box (ξ ω) 0 h hA.1
      simp only [zero_add] at hs
      rw [hs]

lemma count_split (μ : Measure (ℝ≥0 × M)) (hA : MeasurableSet A) {s t u : ℝ≥0}
    (hst : s ≤ t) (htu : t ≤ u) :
    μ (Ioc s u ×ˢ A) = μ (Ioc s t ×ˢ A) + μ (Ioc t u ×ˢ A) := by
  have hdisj : Disjoint (Ioc s t ×ˢ A) (Ioc t u ×ˢ A) := by
    apply Set.disjoint_left.2
    intro p hp₁ hp₂
    exact (not_lt_of_ge hp₁.1.2) hp₂.1.1
  rw [← measure_union hdisj ((measurableSet_Ioc).prod hA)]
  rw [← Set.union_prod, Ioc_union_Ioc_eq_Ioc hst htu]

omit [IsProbabilityMeasure P] in
lemma indep_consecutive_counts (hξ : IsTimeSimpleLevy P ξ) (hA : IsFiniteRate P ξ A)
    (s t : ℝ≥0) :
    IndepFun (fun ω => ξ ω (Ioc 0 s ×ˢ A)) (fun ω => ξ ω (Ioc s (s + t) ×ˢ A)) P := by
  let u : Fin 3 → ℝ≥0 := ![0, s, s + t]
  have hu : Monotone u := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [u, Fin.le_def]
  have hi := hξ.indep 2 u hu
  have hp := hi.indepFun (show (0 : Fin 2) ≠ 1 by decide)
  let B : Set (ℝ≥0 × M) := Ioc 0 (s + t) ×ˢ A
  have hB : MeasurableSet B := measurableSet_Ioc.prod hA.1
  have hc := hp.comp (Measure.measurable_coe hB) (Measure.measurable_coe hB)
  have hfirst : B ∩ (Ioc 0 s ×ˢ univ) = Ioc 0 s ×ˢ A := by
    ext p
    simp only [B, mem_inter_iff, mem_prod, mem_Ioc, mem_univ, and_true]
    constructor
    · rintro ⟨⟨⟨hpos, -⟩, hpA⟩, -, hps⟩
      exact ⟨⟨hpos, hps⟩, hpA⟩
    · rintro ⟨⟨hpos, hps⟩, hpA⟩
      exact ⟨⟨⟨hpos, hps.trans (by simp)⟩, hpA⟩, hpos, hps⟩
  have hsecond : B ∩ (Ioc s (s + t) ×ˢ univ) = Ioc s (s + t) ×ˢ A := by
    ext p
    simp only [B, mem_inter_iff, mem_prod, mem_Ioc, mem_univ, and_true]
    constructor
    · rintro ⟨⟨⟨-, hle⟩, hpA⟩, hs, -⟩
      exact ⟨⟨hs, hle⟩, hpA⟩
    · rintro ⟨⟨hs, hle⟩, hpA⟩
      exact ⟨⟨⟨(zero_le : (0 : ℝ≥0) ≤ s).trans_lt hs, hle⟩, hpA⟩, hs, hle⟩
  simpa [u, windowRestrict, Measure.restrict_apply'
    (measurableSet_Ioc.prod MeasurableSet.univ), hfirst, hsecond,
    Function.comp_def] using hc

omit [IsProbabilityMeasure P] in
lemma prob_noMark_mul (hξ : IsTimeSimpleLevy P ξ) (hA : IsFiniteRate P ξ A) (s t : ℝ≥0) :
    P {ω | ξ ω (Ioc 0 (s + t) ×ˢ A) = 0} =
      P {ω | ξ ω (Ioc 0 s ×ˢ A) = 0} * P {ω | ξ ω (Ioc 0 t ×ˢ A) = 0} := by
  have hstat : P {ω | ξ ω (Ioc s (s + t) ×ˢ A) = 0} = P {ω | ξ ω (Ioc 0 t ×ˢ A) = 0} := by
    let B : Set (ℝ≥0 × M) := Ioc 0 t ×ˢ A
    have hB : MeasurableSet B := measurableSet_Ioc.prod hA.1
    have hz : MeasurableSet {ν : Measure (ℝ≥0 × M) | ν B = 0} :=
      measurableSet_eq_fun (Measure.measurable_coe hB) measurable_const
    have heval := congrArg (fun Q : Measure (Measure (ℝ≥0 × M)) => Q {ν | ν B = 0})
      (hξ.stationary s t)
    rw [Measure.map_apply (measurable_windowShift hξ.measurable s (s + t)) hz,
      Measure.map_apply (measurable_windowShift hξ.measurable 0 t) hz] at heval
    have hleft : (fun ω => windowShift s (s + t) (ξ ω)) ⁻¹' {ν | ν B = 0} =
        {ω | ξ ω (Ioc s (s + t) ×ˢ A) = 0} := by
      ext ω
      simp only [mem_preimage, mem_ofPred_eq]
      change windowShift s (s + t) (ξ ω) (Ioc 0 t ×ˢ A) = 0 ↔ _
      rw [windowShift_box _ _ _ hA.1]
    have hright : (fun ω => windowShift 0 t (ξ ω)) ⁻¹' {ν | ν B = 0} =
        {ω | ξ ω (Ioc 0 t ×ˢ A) = 0} := by
      ext ω
      simp only [mem_preimage, mem_ofPred_eq]
      change windowShift 0 t (ξ ω) (Ioc 0 t ×ˢ A) = 0 ↔ _
      have hs := windowShift_box (ξ ω) 0 t hA.1
      simp only [zero_add] at hs
      rw [hs]
    rw [← hleft, ← hright]
    exact heval
  rw [← hstat]
  have hmeas : MeasurableSet ({0} : Set ℝ≥0∞) := measurableSet_singleton 0
  have hi := (indep_consecutive_counts hξ hA s t).measure_inter_preimage_eq_mul
    {0} {0} hmeas hmeas
  have hset : {ω | ξ ω (Ioc 0 (s + t) ×ˢ A) = 0} =
      (fun ω => ξ ω (Ioc 0 s ×ˢ A)) ⁻¹' {0} ∩
        (fun ω => ξ ω (Ioc s (s + t) ×ˢ A)) ⁻¹' {0} := by
    ext ω
    simp only [mem_inter_iff, mem_preimage, mem_singleton_iff, mem_ofPred_eq]
    rw [count_split _ hA.1 (zero_le : (0 : ℝ≥0) ≤ s) (by simp)]
    simp
  rw [hset, hi]
  change P {ω | ξ ω (Ioc 0 s ×ˢ A) = 0} * P {ω | ξ ω (Ioc s (s + t) ×ˢ A) = 0} = _
  rw [hstat]

lemma prob_noMark_real_eq_one_sub (hξ : IsTimeSimpleLevy P ξ) (hA : IsFiniteRate P ξ A)
    (t : ℝ≥0) : (P {ω | ξ ω (Ioc 0 t ×ˢ A) = 0}).toReal =
      1 - (P {ω | 1 ≤ ξ ω (Ioc 0 t ×ˢ A)}).toReal := by
  let E : Set Ω := {ω | 1 ≤ ξ ω (Ioc 0 t ×ˢ A)}
  have hE : MeasurableSet E :=
    measurableSet_Ici.preimage (measurable_count hξ.measurable (measurable_box hA.1))
  have hcomp : {ω | ξ ω (Ioc 0 t ×ˢ A) = 0} =ᵐ[P] Eᶜ := by
    filter_upwards [ae_one_le_count_of_ne_zero hξ (B := Ioc 0 t ×ˢ A)
      (measurable_box hA.1)] with ω hω
    simp only [E, mem_ofPred_eq, mem_compl_iff]
    by_cases hz : ξ ω (Ioc 0 t ×ˢ A) = 0
    · simp [hz]
    · simp [hz, hω hz]
  rw [measure_congr hcomp]
  have hreal := probReal_add_probReal_compl (μ := P) hE
  dsimp [E] at hreal ⊢
  simp only [Measure.real] at hreal
  linarith

lemma tendsto_prob_noMark_real_zero (hξ : IsTimeSimpleLevy P ξ) (hA : IsFiniteRate P ξ A) :
    Tendsto (fun t : ℝ≥0 => (P {ω | ξ ω (Ioc 0 t ×ˢ A) = 0}).toReal)
      (𝓝[>] 0) (𝓝 1) := by
  have h := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp (tendsto_prob_mark_window hξ hA)
  have hconst : Tendsto (fun _ : ℝ≥0 => (1 : ℝ)) (𝓝[>] 0) (𝓝 1) := tendsto_const_nhds
  have hr := hconst.sub h
  have hr2 : Tendsto (fun t : ℝ≥0 => 1 - (P {ω | 1 ≤ ξ ω (Ioc 0 t ×ˢ A)}).toReal)
      (𝓝[>] 0) (𝓝 1) := by simpa using hr
  apply hr2.congr'
  filter_upwards [self_mem_nhdsWithin] with t _ht
  exact (prob_noMark_real_eq_one_sub hξ hA t).symm

end BGW.Probability
