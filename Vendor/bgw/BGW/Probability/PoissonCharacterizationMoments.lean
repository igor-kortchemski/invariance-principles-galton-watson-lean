/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module
public import BGW.Probability.PoissonCharacterizationMultipleEstimate
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! Truncated first moments of time-simple counting measures. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal BigOperators

namespace BGW.Probability

variable {Ω M : Type*} [MeasurableSpace Ω] [MeasurableSpace M]
variable {P : Measure Ω} [IsProbabilityMeasure P] {ξ : Ω → Measure (ℝ≥0 × M)} {A : Set M}

omit [IsProbabilityMeasure P] in
/-- A counting-measure value cannot lie strictly between one and two. -/
lemma ae_count_le_one_or_two_le (hξ : IsTimeSimpleLevy P ξ)
    {B : Set (ℝ≥0 × M)} (hB : MeasurableSet B) :
    ∀ᵐ ω ∂P, ξ ω B ≤ 1 ∨ 2 ≤ ξ ω B := by
  classical
  filter_upwards [hξ.counting] with ω hω
  obtain ⟨S, _, hμ⟩ := hω
  by_cases h : ξ ω B ≤ 1
  · exact Or.inl h
  right
  obtain ⟨p, q, hpq, hp, hq⟩ := exists_ne_of_one_lt_count hμ hB (lt_of_not_ge h)
  rw [hμ, Measure.sum_apply _ hB]
  calc
    2 = ∑ x ∈ ({p, q} : Finset S), Measure.dirac (x : ℝ≥0 × M) B := by
      simp [Finset.sum_pair hpq, Measure.dirac_apply' _ hB, hp, hq, one_add_one_eq_two]
    _ ≤ _ := ENNReal.sum_le_tsum _

omit [IsProbabilityMeasure P] in
/-- Counts add exactly over a uniform grid partition of a window. -/
lemma sum_grid_counts (hA : MeasurableSet A) (μ : Measure (ℝ≥0 × M))
    (h : ℝ≥0) {n : ℕ} (hn : n ≠ 0) :
    ∑ i : Fin n, μ (gridBox h n i A) = μ (Ioc 0 h ×ˢ A) := by
  have hs (m : ℕ) : ∑ i ∈ Finset.range m, μ (gridBox h n i A) =
      μ (Ioc 0 (pointGridTime h n m) ×ˢ A) := by
    induction m with
    | zero => simp [pointGridTime_start]
    | succ m ih =>
      rw [Finset.sum_range_succ, ih, count_split μ hA (zero_le : (0 : ℝ≥0) ≤ _)
        (pointGridTime_monotone h hn (Nat.le_succ m))]
      rfl
  simpa [← Fin.sum_univ_eq_sum_range, pointGridTime_end h hn] using hs n

private lemma min_add_le (x y K : ℝ≥0∞) : min (x + y) K ≤ min x K + min y K := by
  by_cases hx : x ≤ K
  · by_cases hy : y ≤ K
    · simp [min_eq_left hx, min_eq_left hy]
    · rw [min_eq_right (le_of_not_ge hy)]
      exact (min_le_right _ _).trans (le_add_left le_rfl)
  · rw [min_eq_right (le_of_not_ge hx)]
    exact (min_le_right _ _).trans (le_add_right le_rfl)

private lemma min_sum_le {ι : Type*} (s : Finset ι) (f : ι → ℝ≥0∞) (K : ℝ≥0∞) :
    min (∑ i ∈ s, f i) K ≤ ∑ i ∈ s, min (f i) K := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (min_add_le _ _ _).trans (add_le_add_right ih _)

omit [IsProbabilityMeasure P] in
private lemma lintegral_truncated_count_le (hξ : IsTimeSimpleLevy P ξ)
    {B : Set (ℝ≥0 × M)} (hB : MeasurableSet B) (K : ℝ≥0∞) :
    ∫⁻ ω, min (ξ ω B) K ∂P ≤ P {ω | ξ ω B ≠ 0} + K * P {ω | 2 ≤ ξ ω B} := by
  have hne : MeasurableSet {ω | ξ ω B ≠ 0} :=
    (measurableSet_eq_fun (measurable_count hξ.measurable hB) measurable_const).compl
  have htwo : MeasurableSet {ω | 2 ≤ ξ ω B} :=
    measurableSet_Ici.preimage (measurable_count hξ.measurable hB)
  calc
    _ ≤ ∫⁻ ω, {ω | ξ ω B ≠ 0}.indicator (fun _ => (1 : ℝ≥0∞)) ω +
        {ω | 2 ≤ ξ ω B}.indicator (fun _ => K) ω ∂P := by
      apply lintegral_mono_ae
      filter_upwards [ae_count_le_one_or_two_le hξ hB] with ω hω
      by_cases hz : ξ ω B = 0
      · simp [hz]
      · rw [Set.indicator_of_mem hz]
        rcases hω with hω | hω
        · exact (min_le_left _ _).trans (hω.trans (le_self_add))
        · rw [Set.indicator_of_mem (s := {ω | 2 ≤ ξ ω B}) hω]
          exact (min_le_right _ _).trans le_add_self
    _ = _ := by
      rw [lintegral_add_left (measurable_const.indicator hne),
        lintegral_indicator hne, lintegral_indicator htwo]
      simp

omit [IsProbabilityMeasure P] in
/-- Every nonnegative measurable transform of a window count has stationary expectation. -/
lemma lintegral_window_stationary_comp (hξ : IsTimeSimpleLevy P ξ)
    (hA : IsFiniteRate P ξ A) {f : ℝ≥0∞ → ℝ≥0∞} (hf : Measurable f) (a h : ℝ≥0) :
    ∫⁻ ω, f (ξ ω (Ioc a (a + h) ×ˢ A)) ∂P =
      ∫⁻ ω, f (ξ ω (Ioc 0 h ×ˢ A)) ∂P := by
  have heval := hf.comp (Measure.measurable_coe (measurable_box hA.1 (a := 0) (b := h)))
  have h₁ := lintegral_map heval
    (measurable_windowShift hξ.measurable a (a + h)) (μ := P)
  have h₂ := lintegral_map heval (measurable_windowShift hξ.measurable 0 h) (μ := P)
  calc
    _ = ∫⁻ ω, f (windowShift a (a + h) (ξ ω) (Ioc 0 h ×ˢ A)) ∂P := by
      apply lintegral_congr
      intro ω
      rw [windowShift_box _ _ _ hA.1]
    _ = ∫⁻ ν, f (ν (Ioc 0 h ×ˢ A)) ∂P.map (fun ω => windowShift a (a + h) (ξ ω)) :=
      h₁.symm
    _ = ∫⁻ ν, f (ν (Ioc 0 h ×ˢ A)) ∂P.map (fun ω => windowShift 0 h (ξ ω)) := by
      rw [hξ.stationary a h]
    _ = ∫⁻ ω, f (windowShift 0 h (ξ ω) (Ioc 0 h ×ˢ A)) ∂P := h₂
    _ = _ := by
      apply lintegral_congr
      intro ω
      simpa only [zero_add] using congrArg f (windowShift_box (ξ ω) 0 h hA.1)

omit [IsProbabilityMeasure P] in
private lemma lintegral_truncated_grid_le (hξ : IsTimeSimpleLevy P ξ) (hA : IsFiniteRate P ξ A)
    (h : ℝ≥0) {n : ℕ} (hn : n ≠ 0) (K : ℝ≥0∞) :
    ∫⁻ ω, min (ξ ω (Ioc 0 h ×ˢ A)) K ∂P ≤
      n * (P {ω | ξ ω (Ioc 0 (h / n) ×ˢ A) ≠ 0} +
        K * P {ω | 2 ≤ ξ ω (Ioc 0 (h / n) ×ˢ A)}) := by
  calc
    _ ≤ ∫⁻ ω, ∑ i : Fin n, min (ξ ω (gridBox h n i A)) K ∂P := by
      apply lintegral_mono
      intro ω
      dsimp only
      rw [← sum_grid_counts hA.1 (ξ ω) h hn]
      exact min_sum_le _ _ _
    _ = ∑ i : Fin n, ∫⁻ ω, min (ξ ω (gridBox h n i A)) K ∂P := by
      rw [lintegral_finsetSum]
      intro i _
      exact (measurable_count hξ.measurable (measurable_box hA.1)).min measurable_const
    _ = ∑ _i : Fin n, ∫⁻ ω, min (ξ ω (Ioc 0 (h / n) ×ˢ A)) K ∂P := by
      apply Finset.sum_congr rfl
      intro i _
      simp only [gridBox, pointGridTime_succ_eq_add h hn]
      exact lintegral_window_stationary_comp hξ hA (measurable_id.min measurable_const) _ _
    _ ≤ ∑ _i : Fin n, (P {ω | ξ ω (Ioc 0 (h / n) ×ˢ A) ≠ 0} +
        K * P {ω | 2 ≤ ξ ω (Ioc 0 (h / n) ×ˢ A)}) := by
      exact Finset.sum_le_sum fun _ _ => lintegral_truncated_count_le hξ (measurable_box hA.1) K
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

private lemma prob_nonempty_le (hξ : IsTimeSimpleLevy P ξ) (hA : IsFiniteRate P ξ A)
    {c : ℝ} (hnc : ∀ t : ℝ≥0,
      (P {ω | ξ ω (Ioc 0 t ×ˢ A) = 0}).toReal = Real.exp (-(t : ℝ) * c))
    (hc : 0 ≤ c) (h : ℝ≥0) :
    P {ω | ξ ω (Ioc 0 h ×ˢ A) ≠ 0} ≤ ENNReal.ofReal (c * h) := by
  apply (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) (by positivity)).2
  change P.real {ω | ξ ω (Ioc 0 h ×ˢ A) ≠ 0} ≤ _
  rw [probReal_ne_zero hξ hA (measurable_box hA.1)]
  change 1 - (P {ω | ξ ω (Ioc 0 h ×ˢ A) = 0}).toReal ≤ _
  rw [hnc]
  have := Real.add_one_le_exp (-(h : ℝ) * c)
  linarith

private lemma lintegral_truncated_exp_le (hξ : IsTimeSimpleLevy P ξ) (hA : IsFiniteRate P ξ A)
    {c : ℝ} (hc : 0 ≤ c) (hnc : ∀ t : ℝ≥0,
      (P {ω | ξ ω (Ioc 0 t ×ˢ A) = 0}).toReal = Real.exp (-(t : ℝ) * c))
    (h : ℝ≥0) {n : ℕ} (hn : n ≠ 0) (K : ℕ) :
    ∫⁻ ω, min (ξ ω (Ioc 0 h ×ˢ A)) (K : ℝ≥0∞) ∂P ≤
      ENNReal.ofReal (c * h + K * ((c * h) ^ 2 / n)) := by
  have htwo : P {ω | 2 ≤ ξ ω (Ioc 0 (h / n) ×ˢ A)} ≤
      ENNReal.ofReal ((c * ((h / n : ℝ≥0) : ℝ)) ^ 2) := by
    apply (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) (sq_nonneg _)).2
    exact double_real_le_sq hξ hA (h / n) (N := 0) hc hnc
  calc
    _ ≤ n * (P {ω | ξ ω (Ioc 0 (h / n) ×ˢ A) ≠ 0} +
        (K : ℝ≥0∞) * P {ω | 2 ≤ ξ ω (Ioc 0 (h / n) ×ˢ A)}) :=
      lintegral_truncated_grid_le hξ hA h hn K
    _ ≤ n * (ENNReal.ofReal (c * ((h / n : ℝ≥0) : ℝ)) +
        (K : ℝ≥0∞) * ENNReal.ofReal ((c * ((h / n : ℝ≥0) : ℝ)) ^ 2)) := by
      gcongr
      exact prob_nonempty_le hξ hA hnc hc (h / n)
    _ = _ := by
      rw [← ENNReal.ofReal_natCast n, ← ENNReal.ofReal_natCast K,
        ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity)
          (by positivity), ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      push_cast
      have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
      field_simp

/-- The mean count is at most the rate determined by the no-arrival exponential law. -/
lemma lintegral_count_le_exp_rate (hξ : IsTimeSimpleLevy P ξ) (hA : IsFiniteRate P ξ A)
    {c : ℝ} (hc : 0 ≤ c) (hnc : ∀ t : ℝ≥0,
      (P {ω | ξ ω (Ioc 0 t ×ˢ A) = 0}).toReal = Real.exp (-(t : ℝ) * c))
    (h : ℝ≥0) : ∫⁻ ω, ξ ω (Ioc 0 h ×ˢ A) ∂P ≤ ENNReal.ofReal (c * h) := by
  have hK (K : ℕ) : ∫⁻ ω, min (ξ ω (Ioc 0 h ×ˢ A)) (K : ℝ≥0∞) ∂P ≤
      ENNReal.ofReal (c * h) := by
    have hlim : Tendsto (fun n : ℕ => c * h + K * ((c * h) ^ 2 / (n + 1 : ℝ)))
        atTop (𝓝 (c * h)) := by
      have hh := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul
        ((K : ℝ) * (c * h) ^ 2)
      simpa [div_eq_mul_inv, mul_assoc] using hh.const_add (c * h)
    exact ge_of_tendsto (ENNReal.continuous_ofReal.tendsto _ |>.comp hlim)
      (Eventually.of_forall fun n => lintegral_truncated_exp_le hξ hA hc hnc h
        (Nat.succ_ne_zero n) K |>.trans_eq (by norm_cast))
  calc
    _ = ∫⁻ ω, ⨆ K : ℕ, min (ξ ω (Ioc 0 h ×ˢ A)) (K : ℝ≥0∞) ∂P := by
      congr 1
      funext ω
      rw [← inf_iSup_eq, ENNReal.iSup_natCast, inf_top_eq]
    _ = ⨆ K : ℕ, ∫⁻ ω, min (ξ ω (Ioc 0 h ×ˢ A)) (K : ℝ≥0∞) ∂P := by
      apply lintegral_iSup
      · intro K
        exact (measurable_count hξ.measurable (measurable_box hA.1)).min measurable_const
      · intro i j hij ω
        exact min_le_min_left _ (Nat.cast_le.2 hij)
    _ ≤ _ := iSup_le hK

end BGW.Probability
