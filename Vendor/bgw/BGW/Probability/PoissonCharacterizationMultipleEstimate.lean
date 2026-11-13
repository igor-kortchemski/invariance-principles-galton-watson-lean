/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module
public import BGW.Probability.PoissonCharacterizationMultiple

/-! Probability bounds on separated doubles and the multiple-arrival estimate. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal BigOperators

namespace BGW.Probability

variable {Ω M : Type*} [MeasurableSpace Ω] [MeasurableSpace M]
variable {P : Measure Ω} [IsProbabilityMeasure P] {ξ : Ω → Measure (ℝ≥0 × M)} {A : Set M}

omit [IsProbabilityMeasure P] in
lemma prob_inter_grid (hξ : IsTimeSimpleLevy P ξ) (hA : IsFiniteRate P ξ A)
    (h : ℝ≥0) {n : ℕ} (hn : n ≠ 0) {i j : Fin n} (hij : i ≠ j) :
    P.real ({ω | ξ ω (gridBox h n i A) ≠ 0} ∩ {ω | ξ ω (gridBox h n j A) ≠ 0}) =
      P.real {ω | ξ ω (gridBox h n i A) ≠ 0} *
        P.real {ω | ξ ω (gridBox h n j A) ≠ 0} := by
  have hz : MeasurableSet ({0} : Set ℝ≥0∞) := measurableSet_singleton 0
  have hp := (iIndep_grid_counts hξ hA h hn).indepFun hij
  have hp' := hp.measure_inter_preimage_eq_mul {0}ᶜ {0}ᶜ hz.compl hz.compl
  change (P ({ω | ξ ω (gridBox h n i A) ≠ 0} ∩
    {ω | ξ ω (gridBox h n j A) ≠ 0})).toReal =
    (P {ω | ξ ω (gridBox h n i A) ≠ 0}).toReal *
      (P {ω | ξ ω (gridBox h n j A) ≠ 0}).toReal
  change (P ((fun ω => ξ ω (gridBox h n i A)) ⁻¹' {0}ᶜ ∩
    (fun ω => ξ ω (gridBox h n j A)) ⁻¹' {0}ᶜ)).toReal = _
  rw [hp', ENNReal.toReal_mul]
  rfl

lemma probReal_ne_zero (hξ : IsTimeSimpleLevy P ξ) (_hA : IsFiniteRate P ξ A)
    {B : Set (ℝ≥0 × M)} (hB : MeasurableSet B) :
    P.real {ω | ξ ω B ≠ 0} = 1 - P.real {ω | ξ ω B = 0} := by
  have hzero : MeasurableSet {ω | ξ ω B = 0} :=
    measurableSet_eq_fun (measurable_count hξ.measurable hB) measurable_const
  have hreal := probReal_add_probReal_compl (μ := P) hzero
  have hcomp : {ω | ξ ω B ≠ 0} = {ω | ξ ω B = 0}ᶜ := by ext ω; simp
  rw [hcomp]
  linarith

omit [IsProbabilityMeasure P] in
lemma prob_noMark_grid (hξ : IsTimeSimpleLevy P ξ) (hA : IsFiniteRate P ξ A)
    (h : ℝ≥0) {n i : ℕ} (hn : n ≠ 0) {c : ℝ}
    (hnc : ∀ t : ℝ≥0,
      (P {ω | ξ ω (Ioc 0 t ×ˢ A) = 0}).toReal = Real.exp (-(t : ℝ) * c)) :
    P.real {ω | ξ ω (gridBox h n i A) = 0} = Real.exp (-((h : ℝ) / (n : ℝ)) * c) := by
  have hs := prob_noMark_stationary hξ hA (pointGridTime h n i) (h / (n : ℝ≥0))
  rw [← pointGridTime_succ_eq_add h (n := n) (i := i) hn] at hs
  have hb := hnc (h / (n : ℝ≥0))
  change (P {ω | ξ ω (Ioc (pointGridTime h n i) (pointGridTime h n (i + 1)) ×ˢ A) = 0}).toReal = _
  rw [hs, hb]
  congr 3

lemma sum_grid_arrival_le (hξ : IsTimeSimpleLevy P ξ) (hA : IsFiniteRate P ξ A)
    (h : ℝ≥0) {n : ℕ} (hn : n ≠ 0) {c : ℝ} (_hc : 0 ≤ c)
    (hnc : ∀ t : ℝ≥0,
      (P {ω | ξ ω (Ioc 0 t ×ˢ A) = 0}).toReal = Real.exp (-(t : ℝ) * c)) :
    ∑ i : Fin n, P.real {ω | ξ ω (gridBox h n i A) ≠ 0} ≤ c * (h : ℝ) := by
  have hterm (i : Fin n) : P.real {ω | ξ ω (gridBox h n i A) ≠ 0} ≤
      c * ((h : ℝ) / (n : ℝ)) := by
    change P.real {ω | ξ ω (Ioc (pointGridTime h n i) (pointGridTime h n (i + 1)) ×ˢ A) ≠ 0} ≤ _
    have hz : (P {ω | ξ ω (Ioc (pointGridTime h n i) (pointGridTime h n (i + 1)) ×ˢ A) = 0}
        ).toReal =
        Real.exp (-((h : ℝ) / (n : ℝ)) * c) := by
      simpa [gridBox, measureReal_def] using prob_noMark_grid hξ hA h hn hnc
    rw [probReal_ne_zero hξ hA (measurableSet_Ioc.prod hA.1)]
    change 1 - (P {ω | ξ ω
      (Ioc (pointGridTime h n i) (pointGridTime h n (i + 1)) ×ˢ A) = 0}).toReal ≤ _
    rw [hz]
    have hexp := Real.add_one_le_exp (-((h : ℝ) / (n : ℝ)) * c)
    linarith
  calc
    _ ≤ ∑ _i : Fin n, c * ((h : ℝ) / (n : ℝ)) := Finset.sum_le_sum fun i _ => hterm i
    _ = c * (h : ℝ) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
      field_simp [hn']

lemma separatedDoubleNE_real_le (hξ : IsTimeSimpleLevy P ξ) (hA : IsFiniteRate P ξ A)
    (h : ℝ≥0) {n : ℕ} (hn : n ≠ 0) {c : ℝ} (hc : 0 ≤ c)
    (hnc : ∀ t : ℝ≥0,
      (P {ω | ξ ω (Ioc 0 t ×ˢ A) = 0}).toReal = Real.exp (-(t : ℝ) * c)) :
    P.real (separatedDoubleNE ξ h n A) ≤ (c * (h : ℝ)) ^ 2 := by
  let C : Fin n → Set Ω := fun i => {ω | ξ ω (gridBox h n i A) ≠ 0}
  have hE : separatedDoubleNE ξ h n A = ⋃ i, ⋃ j, if i < j then C i ∩ C j else ∅ := by
    ext ω
    simp only [separatedDoubleNE, mem_iUnion, mem_ite, mem_inter_iff, mem_ofPred_eq,
      mem_empty_iff_false, C]
    aesop
  rw [hE]
  calc
    _ ≤ ∑ i : Fin n, P.real (⋃ j, if i < j then C i ∩ C j else ∅) :=
      measureReal_iUnion_fintype_le _
    _ ≤ ∑ i : Fin n, ∑ j : Fin n, P.real (if i < j then C i ∩ C j else ∅) := by
      gcongr with i
      exact measureReal_iUnion_fintype_le _
    _ ≤ ∑ i : Fin n, ∑ j : Fin n, P.real (C i) * P.real (C j) := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      split_ifs with hij
      · dsimp [C]
        exact le_of_eq (prob_inter_grid hξ hA h hn hij.ne)
      · simp only [Measure.real, measure_empty, ENNReal.toReal_zero]
        positivity
    _ = (∑ i : Fin n, P.real (C i)) ^ 2 := by
      simp_rw [← Finset.mul_sum, ← Finset.sum_mul, pow_two]
    _ ≤ _ := by
      have hsum := sum_grid_arrival_le hξ hA h hn hc hnc
      have hnonneg : 0 ≤ ∑ i : Fin n, P.real (C i) :=
        Finset.sum_nonneg fun _ _ => by positivity
      have hch : 0 ≤ c * (h : ℝ) := mul_nonneg hc (by positivity)
      nlinarith

lemma double_real_le_sq (hξ : IsTimeSimpleLevy P ξ) (hA : IsFiniteRate P ξ A)
    (h : ℝ≥0) {N : ℕ} {c : ℝ} (hc : 0 ≤ c)
    (hnc : ∀ t : ℝ≥0,
      (P {ω | ξ ω (Ioc 0 t ×ˢ A) = 0}).toReal = Real.exp (-(t : ℝ) * c)) :
    P.real {ω | 2 ≤ ξ ω (Ioc 0 h ×ˢ A)} ≤ (c * (h : ℝ)) ^ 2 := by
  have hN : 2 ^ N ≠ 0 := pow_ne_zero _ (by norm_num : (2 : ℕ) ≠ 0)
  have hmono : Monotone (fun N : ℕ => separatedDoubleNE ξ h (2 ^ N) A) :=
    separatedDoubleNE_mono h hA.1
  have hlim := tendsto_measure_iUnion_atTop (μ := P) hmono
  have hlimR := (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp hlim
  have hbound := separatedDoubleNE_real_le hξ hA h hN hc hnc
  have hlimR' : Tendsto (fun N : ℕ => P.real (separatedDoubleNE ξ h (2 ^ N) A)) atTop
      (𝓝 (P.real (⋃ N : ℕ, separatedDoubleNE ξ h (2 ^ N) A))) := by
    simpa [Measure.real, Function.comp_def] using hlimR
  have heq : P (⋃ N : ℕ, separatedDoubleNE ξ h (2 ^ N) A) =
      P {ω | 2 ≤ ξ ω (Ioc 0 h ×ˢ A)} :=
        (measure_congr (ae_double_eq_iUnion_separatedNE hξ hA h)).symm
  rw [measureReal_def, heq] at hlimR'
  exact le_of_tendsto hlimR' (Eventually.of_forall fun N' =>
    separatedDoubleNE_real_le hξ hA h (n := 2 ^ N') (pow_ne_zero _ (by norm_num)) hc hnc)

/-- **Small-interval multiple-arrival estimate**: `P(≥ 2 marks in (0,h]) = o(h)`. -/
theorem prob_two_marks_window_isLittleO (hξ : IsTimeSimpleLevy P ξ) (hA : IsFiniteRate P ξ A) :
    Tendsto (fun h : ℝ≥0 => (P {ω | 2 ≤ ξ ω (Ioc 0 h ×ˢ A)}).toReal / (h : ℝ))
      (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨c, hc, hnc⟩ := prob_noMark_exp_exists hξ hA
  let R : ℝ≥0 → ℝ := fun h => (P {ω | 2 ≤ ξ ω (Ioc 0 h ×ˢ A)}).toReal / (h : ℝ)
  have hupper : Tendsto (fun h : ℝ≥0 => c ^ 2 * (h : ℝ)) (𝓝[>] 0) (𝓝 0) := by
    have hh : Tendsto (fun h : ℝ≥0 => (h : ℝ)) (𝓝[>] 0) (𝓝 0) :=
      NNReal.continuous_coe.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    simpa using tendsto_const_nhds.mul hh
  apply squeeze_zero' (g := fun h : ℝ≥0 => c ^ 2 * (h : ℝ))
  · filter_upwards [] with h
    exact div_nonneg (by positivity) (by positivity)
  · filter_upwards [self_mem_nhdsWithin] with h hh
    have hbound := double_real_le_sq hξ hA h (N := 1) hc hnc
    change (P {ω | 2 ≤ ξ ω (Ioc 0 h ×ˢ A)}).toReal / (h : ℝ) ≤ _
    rw [Measure.real] at hbound
    apply (div_le_iff₀ hh).2
    have hsq : (c * (h : ℝ)) ^ 2 = c ^ 2 * (h : ℝ) ^ 2 := by ring
    rw [hsq] at hbound
    calc
      _ ≤ c ^ 2 * (h : ℝ) ^ 2 := hbound
      _ = c ^ 2 * (h : ℝ) * (h : ℝ) := by ring
  · exact hupper

end BGW.Probability
