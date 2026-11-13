/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module
public import BGW.Probability.PoissonCharacterizationMoments
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! Identification and finiteness of the intensity of a finite-rate mark set. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal BigOperators

namespace BGW.Probability

variable {Ω M : Type*} [MeasurableSpace Ω] [MeasurableSpace M]
variable {P : Measure Ω} [IsProbabilityMeasure P] {ξ : Ω → Measure (ℝ≥0 × M)} {A : Set M}

omit [IsProbabilityMeasure P] in
private lemma prob_nonempty_le_lintegral (hξ : IsTimeSimpleLevy P ξ)
    {B : Set (ℝ≥0 × M)} (hB : MeasurableSet B) :
    P {ω | ξ ω B ≠ 0} ≤ ∫⁻ ω, ξ ω B ∂P := by
  have hne : MeasurableSet {ω | ξ ω B ≠ 0} :=
    (measurableSet_eq_fun (measurable_count hξ.measurable hB) measurable_const).compl
  rw [← lintegral_indicator_one hne]
  apply lintegral_mono_ae
  filter_upwards [ae_one_le_count_of_ne_zero hξ hB] with ω hω
  by_cases hz : ξ ω B = 0
  · simp [hz]
  · simpa [hz] using hω hz

omit [IsProbabilityMeasure P] in
private lemma grid_prob_nonempty_le_lintegral (hξ : IsTimeSimpleLevy P ξ)
    (hA : IsFiniteRate P ξ A) (h : ℝ≥0) {n : ℕ} (hn : n ≠ 0) :
    n * P {ω | ξ ω (Ioc 0 (h / n) ×ˢ A) ≠ 0} ≤
      ∫⁻ ω, ξ ω (Ioc 0 h ×ˢ A) ∂P := by
  calc
    _ ≤ ∑ _i : Fin n, ∫⁻ ω, ξ ω (Ioc 0 (h / n) ×ˢ A) ∂P := by
      simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using
        mul_le_mul (le_refl (n : ℝ≥0∞))
          (prob_nonempty_le_lintegral hξ (measurable_box hA.1)) zero_le zero_le
    _ = ∑ i : Fin n, ∫⁻ ω, ξ ω (gridBox h n i A) ∂P := by
      apply Finset.sum_congr rfl
      intro i _
      simp only [gridBox, pointGridTime_succ_eq_add h hn]
      exact (lintegral_window_stationary hξ hA _ _).symm
    _ = ∫⁻ ω, ∑ i : Fin n, ξ ω (gridBox h n i A) ∂P := by
      rw [lintegral_finsetSum]
      intro i _
      exact measurable_count hξ.measurable (measurable_box hA.1)
    _ = _ := by simp only [sum_grid_counts hA.1 _ h hn]

private lemma tendsto_nat_mul_one_sub_exp (a : ℝ) :
    Tendsto (fun n : ℕ => (n + 1 : ℝ) * (1 - Real.exp (-a / (n + 1 : ℝ))))
      atTop (𝓝 a) := by
  have hd : HasDerivAt (fun x : ℝ => 1 - Real.exp (-a * x)) a 0 := by
    convert (((hasDerivAt_id (0 : ℝ)).const_mul (-a)).exp.const_sub 1) using 1 <;> simp
  have hu : Tendsto (fun n : ℕ => 1 / (n + 1 : ℝ)) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
      Eventually.of_forall fun n => by simp only [mem_Ioi]; positivity⟩
  simpa [Function.comp_def, smul_eq_mul, div_eq_mul_inv] using hd.tendsto_slope_zero_right.comp hu

private lemma exp_rate_le_lintegral_count (hξ : IsTimeSimpleLevy P ξ)
    (hA : IsFiniteRate P ξ A) {c : ℝ}
    (hnc : ∀ t : ℝ≥0,
      (P {ω | ξ ω (Ioc 0 t ×ˢ A) = 0}).toReal = Real.exp (-(t : ℝ) * c))
    (h : ℝ≥0) : ENNReal.ofReal (c * h) ≤ ∫⁻ ω, ξ ω (Ioc 0 h ×ˢ A) ∂P := by
  apply le_of_tendsto (ENNReal.continuous_ofReal.tendsto (c * h) |>.comp
    (tendsto_nat_mul_one_sub_exp (c * h)))
  filter_upwards [] with n
  have hp : P {ω | ξ ω (Ioc 0 (h / (n + 1)) ×ˢ A) ≠ 0} =
      ENNReal.ofReal (1 - Real.exp (-(c * h) / (n + 1 : ℝ))) := by
    rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
    congr 1
    change P.real {ω | ξ ω (Ioc 0 (h / (n + 1)) ×ˢ A) ≠ 0} = _
    rw [probReal_ne_zero hξ hA (measurable_box hA.1)]
    change 1 - (P {ω | ξ ω (Ioc 0 (h / (n + 1)) ×ˢ A) = 0}).toReal = _
    rw [hnc]
    push_cast
    congr 2
    ring
  have hb := grid_prob_nonempty_le_lintegral hξ hA h (n := n + 1) (by omega)
  rw [← ENNReal.ofReal_natCast (n + 1)] at hb
  simp only [Nat.cast_add, Nat.cast_one] at hb
  rw [hp, ← ENNReal.ofReal_mul (by positivity)] at hb
  exact hb

private lemma lintegral_count_eq_exp_rate (hξ : IsTimeSimpleLevy P ξ) (hA : IsFiniteRate P ξ A)
    {c : ℝ} (hc : 0 ≤ c) (hnc : ∀ t : ℝ≥0,
      (P {ω | ξ ω (Ioc 0 t ×ˢ A) = 0}).toReal = Real.exp (-(t : ℝ) * c)) (h : ℝ≥0) :
    ∫⁻ ω, ξ ω (Ioc 0 h ×ˢ A) ∂P = ENNReal.ofReal (c * h) :=
  le_antisymm (lintegral_count_le_exp_rate hξ hA hc hnc h)
    (exp_rate_le_lintegral_count hξ hA hnc h)

/-- **Finite expected intensity** of a finite-rate mark set. -/
theorem markRate_lt_top (hξ : IsTimeSimpleLevy P ξ) (hA : IsFiniteRate P ξ A) :
    markRate P ξ A < ⊤ := by
  obtain ⟨c, hc, hnc⟩ := prob_noMark_exp_exists hξ hA
  unfold markRate
  rw [lintegral_count_eq_exp_rate hξ hA hc hnc]
  exact ENNReal.ofReal_lt_top

/-- **No-arrival exponential law**: `P(no A-mark in (0,t]) = exp(-t λ_A)`, with `λ_A` finite. -/
theorem prob_noMark_window (hξ : IsTimeSimpleLevy P ξ) (hA : IsFiniteRate P ξ A) (t : ℝ≥0) :
    P {ω | ξ ω (Ioc 0 t ×ˢ A) = 0} =
      ENNReal.ofReal (Real.exp (-((t : ℝ) * (markRate P ξ A).toReal))) := by
  obtain ⟨c, hc, hnc⟩ := prob_noMark_exp_exists hξ hA
  have hr : markRate P ξ A = ENNReal.ofReal c := by
    simpa [markRate] using lintegral_count_eq_exp_rate hξ hA hc hnc 1
  rw [hr, ENNReal.toReal_ofReal hc, ← ENNReal.ofReal_toReal (measure_ne_top _ _), hnc]
  simp only [neg_mul]

/-- **Expected count on a window**: `E ξ((s,t] × A) = (t - s) λ_A`. -/
theorem lintegral_count_window (hξ : IsTimeSimpleLevy P ξ) (hA : IsFiniteRate P ξ A)
    {s t : ℝ≥0} (hst : s ≤ t) :
    ∫⁻ ω, ξ ω (Ioc s t ×ˢ A) ∂P = ((t - s : ℝ≥0) : ℝ≥0∞) * markRate P ξ A := by
  obtain ⟨c, hc, hnc⟩ := prob_noMark_exp_exists hξ hA
  have hr : markRate P ξ A = ENNReal.ofReal c := by
    simpa [markRate] using lintegral_count_eq_exp_rate hξ hA hc hnc 1
  rw [← add_tsub_cancel_of_le hst, lintegral_window_stationary hξ hA,
    lintegral_count_eq_exp_rate hξ hA hc hnc, hr]
  simp only [add_tsub_cancel_left]
  rw [mul_comm c, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_coe_nnreal]

end BGW.Probability
