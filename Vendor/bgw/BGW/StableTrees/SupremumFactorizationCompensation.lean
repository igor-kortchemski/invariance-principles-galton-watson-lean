/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.SupremumFactorizationDiscount
public import BGW.StableTrees.SupremumFactorizationPredictable

/-! # Compensation of discounted excursion occupation

Reference: J. Bertoin, *Lévy Processes*, Cambridge University Press, 1996, Chapters IV and VI.
-/

@[expose] public section

open MeasureTheory MeasurableSpace Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees

/-- The level coordinate is measurable for the stopped-past predictable sigma algebra. -/
theorem measurable_predictable_level : Measurable[predictableSigma]
    (Prod.fst : ℝ≥0 × DLoc → ℝ≥0) := by
  apply measurable_of_Iic
  intro a
  have hzero : MeasurableSet[predictableSigma] (({0} : Set ℝ≥0) ×ˢ (univ : Set DLoc)) := by
    rw [predictableSigma_eq_generate]
    exact measurableSet_generateFrom (mem_insert_of_mem _ (Or.inr ⟨univ, .univ, rfl⟩))
  have hinterval : MeasurableSet[predictableSigma] (Ioc 0 a ×ˢ (univ : Set DLoc)) := by
    rw [predictableSigma_eq_generate]
    exact measurableSet_generateFrom (mem_insert_of_mem _ (Or.inl
      ⟨0, a, univ, bot_le, .univ, rfl⟩))
  convert hzero.union hinterval using 1
  ext p
  simp only [mem_preimage, mem_Iic, mem_union, mem_prod, mem_singleton_iff, mem_univ,
    and_true, mem_Ioc]
  exact ⟨fun h => (eq_or_lt_of_le (bot_le : 0 ≤ p.1)).imp
    (fun hz => hz.symm) (fun hp => ⟨hp, h⟩), fun h => h.elim
      (fun hz => hz ▸ (bot_le : (0 : ℝ≥0) ≤ a)) And.right⟩

/-- On the full-probability event of finite passages, the extended past agrees with its
finite reading, simultaneously at all levels. -/
theorem ae_passagePast_eq_passageTimeMinus {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∀ x : ℝ≥0,
      passagePast x f = (passageTimeMinus x f : ℝ≥0∞) := by
  filter_upwards [ae_passageTime_eq_firstPassageBelow hθ] with f hf
  intro x
  have hb : passagePast x f ≤ (firstPassageBelow x f : ℝ≥0∞) := by
    apply iSup_le
    intro y
    exact firstPassageBelow_mono f y.2.le
  have hn : (passagePast x f : WithTop ℝ≥0) ≠ ⊤ :=
    ne_top_of_le_ne_top (by rw [hf.1 x]; exact WithTop.coe_ne_top) hb
  obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.mp hn
  change passagePast x f = (((passagePast x f : WithTop ℝ≥0).untopD 0 : ℝ≥0) : ℝ≥0∞)
  rw [← ht, WithTop.untopD_coe]
  rfl

/-- The discounted excursion occupation functional is measurable in its excursion mark. -/
theorem measurable_excursionDiscount (q : ℝ) {G : ℝ → ℝ≥0∞} (hG : Measurable G) :
    Measurable (excursionDiscount q G) := by
  have hm : Measurable (fun p : Excursion × ℝ =>
      (Ioo (0 : ℝ) (p.1.lifetime : ℝ)).indicator
        (fun s => ENNReal.ofReal (q * Real.exp (-q * s)) * G (p.1.path.1 s.toNNReal)) p.2) := by
    apply Measurable.ite
    · exact (measurableSet_lt measurable_const measurable_snd).inter
        (measurableSet_lt measurable_snd
          (measurable_excursion_lifetime.coe_nnreal_real.comp measurable_fst))
    · apply Measurable.mul (by fun_prop)
      exact hG.comp (measurable_excursion_eval₂.comp
        (measurable_fst.prodMk (continuous_real_toNNReal.measurable.comp measurable_snd)))
    · exact measurable_const
  unfold excursionDiscount
  convert hm.lintegral_prod_right' (ν := (volume : Measure ℝ)) using 1
  funext e
  exact (lintegral_indicator measurableSet_Ioo _).symm

/-- Compensation separates the infimum level from the reflected position in the
exponentially discounted occupation integral. -/
theorem lintegral_infimum_resolvent_factorization {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    {q : ℝ} (hq : 0 < q) {F G : ℝ → ℝ≥0∞} (hF : Measurable F) (hG : Measurable G) :
    (∫⁻ f, (∫⁻ t in Ici (0 : ℝ), ENNReal.ofReal (q * Real.exp (-q * t)) *
      F (localTime f t.toNNReal) * G ((reflectedFrom 0 f).1 t.toNNReal))
      ∂(stableLocalLaw θ : Measure DLoc)) =
    (∫⁻ f, (∫⁻ x, expNeg (ENNReal.ofReal q * passagePast x f) * F x ∂lebNN)
      ∂(stableLocalLaw θ : Measure DLoc)) *
      ∫⁻ e, excursionDiscount q G e ∂excursionMeasure θ := by
  let := sigmaFinite_lebNN
  let D : ℝ≥0 × DLoc → ℝ≥0∞ := fun p =>
    expNeg (ENNReal.ofReal q * passagePast p.1 p.2) * F p.1
  have hD : Measurable[predictableSigma] D :=
    (measurable_predictable_passagePast_discount q).mul
      (hF.comp (measurable_coe_nnreal_real.comp measurable_predictable_level))
  have hDfull : Measurable D := hD.mono predictableSigma_le_prod le_rfl
  have hDG : Measurable (excursionDiscount q G) := measurable_excursionDiscount q hG
  have hH : @Measurable _ _ (predictableSigma.prod inferInstance) _
      (fun p : (ℝ≥0 × DLoc) × Excursion => D p.1 * excursionDiscount q G p.2) :=
    (hD.comp measurable_fst).mul (hDG.comp measurable_snd)
  calc
    _ = ∫⁻ f, (∫⁻ p, D (p.1, f) * excursionDiscount q G p.2
        ∂excursionPointMeasure f) ∂(stableLocalLaw θ : Measure DLoc) := by
      apply lintegral_congr_ae
      filter_upwards [ae_lintegral_split_excursionDiscount hθ q F hG,
        ae_passagePast_eq_passageTimeMinus hθ] with f hf hp
      rw [hf]
      apply lintegral_congr
      intro p
      dsimp only [D]
      rw [hp p.1]
      have he : expNeg (ENNReal.ofReal q * (passageTimeMinus p.1 f : ℝ≥0∞)) =
          ENNReal.ofReal (Real.exp (-q * (passageTimeMinus p.1 f : ℝ))) := by
        simp [expNeg, ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.coe_ne_top,
          ENNReal.toReal_mul, ENNReal.toReal_ofReal hq.le]
      rw [he]
    _ = ∫⁻ f, (∫⁻ x, (∫⁻ e, D (x, f) * excursionDiscount q G e ∂excursionMeasure θ)
        ∂lebNN) ∂(stableLocalLaw θ : Measure DLoc) :=
      excursion_compensation_predictable_general hθ hH
    _ = _ := by
      simp_rw [lintegral_const_mul _ hDG]
      have htime (f : DLoc) : Measurable (fun x => D (x, f)) :=
        hDfull.comp measurable_prodMk_right
      simp_rw [lintegral_mul_const _ (htime _)]
      exact lintegral_mul_const _ hDfull.lintegral_prod_left'

end BGW.StableTrees
