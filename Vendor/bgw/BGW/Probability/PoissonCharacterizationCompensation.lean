/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module
public import BGW.Probability.PoissonCharacterizationExpectation

/-! Natural-history independence and deterministic-time compensation. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal Matrix

namespace BGW.Probability

variable {Ω M : Type*} [MeasurableSpace Ω] [MeasurableSpace M]
variable {P : Measure Ω} [IsProbabilityMeasure P] {ξ : Ω → Measure (ℝ≥0 × M)} {A : Set M}

omit [IsProbabilityMeasure P] in
private lemma ae_historyRestriction_eq_window (hξ : IsTimeSimpleLevy P ξ) (s : ℝ≥0) :
    (fun ω => (ξ ω).restrict (Iic s ×ˢ univ)) =ᵐ[P]
      (fun ω => windowRestrict 0 s (ξ ω)) := by
  filter_upwards [hξ.atZero] with ω hω
  apply Measure.restrict_congr_set
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 hω] with p hp
  have hp0 : p.1 ≠ 0 := by simpa using hp
  simp only [mem_prod, mem_Iic, mem_univ, and_true, mem_Ioc]
  apply propext
  exact ⟨fun hps => ⟨pos_iff_ne_zero.2 hp0, hps⟩, fun hps => hps.2⟩

omit [IsProbabilityMeasure P] in
private lemma indep_history_window (hξ : IsTimeSimpleLevy P ξ) {s t : ℝ≥0} (hst : s ≤ t) :
    IndepFun (fun ω => (ξ ω).restrict (Iic s ×ˢ univ))
      (fun ω => windowRestrict s t (ξ ω)) P := by
  let u : Fin 3 → ℝ≥0 := ![0, s, t]
  have hu : Monotone u := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [u, Fin.le_def]
  have hi := (hξ.indep 2 u hu).indepFun (show (0 : Fin 2) ≠ 1 by decide)
  have hw : IndepFun (fun ω => windowRestrict 0 s (ξ ω))
      (fun ω => windowRestrict s t (ξ ω)) P := by simpa [u] using hi
  exact hw.congr (ae_historyRestriction_eq_window hξ s).symm (Eventually.of_forall fun _ => rfl)

omit [IsProbabilityMeasure P] in
private lemma indep_history_count (hξ : IsTimeSimpleLevy P ξ) (hA : IsFiniteRate P ξ A)
    {s t : ℝ≥0} (hst : s ≤ t) {Y : Ω → ℝ≥0∞} (hY : Measurable[naturalHistory ξ s] Y) :
    IndepFun Y (fun ω => ξ ω (Ioc s t ×ˢ A)) P := by
  have hi := (indep_history_window hξ hst).comp measurable_id
    (Measure.measurable_coe (measurable_box hA.1 (a := s) (b := t)))
  have hi' : IndepFun (fun ω => (ξ ω).restrict (Iic s ×ˢ univ))
      (fun ω => ξ ω (Ioc s t ×ˢ A)) P := by
    simpa [Function.comp_def, windowRestrict, Measure.restrict_apply'
      (measurableSet_Ioc.prod MeasurableSet.univ),
      inter_eq_left.2 (Set.prod_mono Subset.rfl (subset_univ A))] using hi
  exact indep_of_indep_of_le_left hi' (measurable_iff_comap_le.1 hY)

/-- **Deterministic-history compensation** (step tests): for `Y ≥ 0` measurable for the natural
history at time `s`, `E[Y ξ((s,t] × A)] = E[Y] (t - s) λ_A`. -/
theorem lintegral_mul_count_window (hξ : IsTimeSimpleLevy P ξ) (hA : IsFiniteRate P ξ A)
    {s t : ℝ≥0} (hst : s ≤ t) {Y : Ω → ℝ≥0∞} (hY : Measurable[naturalHistory ξ s] Y) :
    ∫⁻ ω, Y ω * ξ ω (Ioc s t ×ˢ A) ∂P =
      (∫⁻ ω, Y ω ∂P) * (((t - s : ℝ≥0) : ℝ≥0∞) * markRate P ξ A) := by
  have hYm : Measurable Y := hY.mono
    (measurable_iff_comap_le.1 (measurable_historyRestriction hξ.measurable s)) le_rfl
  rw [lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun'' hYm.aemeasurable
    (measurable_count hξ.measurable (measurable_box hA.1)).aemeasurable
    (indep_history_count hξ hA hst hY), lintegral_count_window hξ hA hst]

end BGW.Probability
