/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.SupremumFactorizationOccupation
import Mathlib.MeasureTheory.Group.LIntegral

/-! # Discounted occupation split at the excursion containing the clock

Reference: J. Bertoin, *Lévy Processes*, Cambridge University Press, 1996, Chapters IV and VI.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees

private theorem lintegral_Ioo_translate (g d : ℝ) (H : ℝ → ℝ≥0∞) :
    ∫⁻ t in Ioo g d, H t = ∫⁻ s in Ioo 0 (d - g), H (g + s) := by
  rw [← lintegral_indicator measurableSet_Ioo, ← lintegral_indicator measurableSet_Ioo]
  rw [← lintegral_add_left_eq_self ((Ioo g d).indicator H) g]
  apply lintegral_congr
  intro s
  have he : g + s ∈ Ioo g d ↔ s ∈ Ioo 0 (d - g) := by
    constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
  simp only [indicator_apply, he]

/-- The discounted occupation integral of an infimum excursion, as a function of its mark. -/
noncomputable def excursionDiscount (q : ℝ) (G : ℝ → ℝ≥0∞) (e : Excursion) : ℝ≥0∞ :=
  ∫⁻ s in Ioo (0 : ℝ) (e.lifetime : ℝ),
    ENNReal.ofReal (q * Real.exp (-q * s)) * G (e.path.1 s.toNNReal)

/-- The clock density splits at the start of the excursion straddling it. -/
theorem ae_lintegral_split_excursionDiscount {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    (q : ℝ) (F : ℝ → ℝ≥0∞) {G : ℝ → ℝ≥0∞} (hG : Measurable G) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc),
      (∫⁻ t in Ici (0 : ℝ), ENNReal.ofReal (q * Real.exp (-q * t)) *
        F (localTime f t.toNNReal) * G ((reflectedFrom 0 f).1 t.toNNReal)) =
      ∫⁻ p, ENNReal.ofReal (Real.exp (-q * (passageTimeMinus p.1 f : ℝ))) *
        F p.1 * excursionDiscount q G p.2 ∂excursionPointMeasure f := by
  classical
  filter_upwards [ae_lintegral_split_passage_intervals hθ
    (fun t a y => ENNReal.ofReal (q * Real.exp (-q * t)) * F a * G y),
    ae_passageJumpSet_countable hθ, ae_jumpExcursion_spec hθ] with f hsplit hc hs
  rw [hsplit, excursionPointMeasure, ite_eq_left hc]
  simp_rw [lintegral_sum_measure, lintegral_dirac]
  apply tsum_congr
  intro x
  rw [lintegral_Ioo_translate]
  have hlife : ((jumpExcursion x f).lifetime : ℝ) =
      (passageTime x f : ℝ) - (passageTimeMinus x f : ℝ) := by
    rw [(hs x x.2).2.1, NNReal.coe_sub x.2.2.le]
  rw [← hlife]
  have hm : Measurable (fun s : ℝ =>
      ENNReal.ofReal (q * Real.exp (-q * s)) *
        G ((jumpExcursion x f).path.1 s.toNNReal)) := by
    apply Measurable.mul (by fun_prop)
    exact hG.comp (DLoc.measurable_eval₂.comp
      (measurable_const.prodMk continuous_real_toNNReal.measurable))
  rw [excursionDiscount, ← lintegral_const_mul _ hm]
  apply setLIntegral_congr_fun measurableSet_Ioo
  intro s hsi
  have hval : (jumpExcursion x f).path.1 s.toNNReal =
      (reflectedFrom 0 f).1 ((passageTimeMinus x f : ℝ) + s).toNNReal := by
    have hsd : passageTimeMinus x f + s.toNNReal ≤ passageTime x f := by
      rw [← NNReal.coe_le_coe, NNReal.coe_add, Real.coe_toNNReal _ hsi.1.le]
      have hb := hsi.2
      rw [hlife] at hb
      linarith
    have hplus : passageTimeMinus x f + s.toNNReal =
        ((passageTimeMinus x f : ℝ) + s).toNNReal := by
      apply NNReal.coe_injective
      rw [NNReal.coe_add, Real.coe_toNNReal _ hsi.1.le,
        Real.coe_toNNReal _ (add_nonneg (passageTimeMinus x f).coe_nonneg hsi.1.le)]
    exact ((hs x x.2).2.2 s.toNNReal).trans
      (congrArg (fun u => (reflectedFrom 0 f).1 u) ((min_eq_left hsd).trans hplus))
  have hdensity : ENNReal.ofReal (q * Real.exp
      (-q * ((passageTimeMinus x f : ℝ) + s))) =
      ENNReal.ofReal (Real.exp (-q * (passageTimeMinus x f : ℝ))) *
        ENNReal.ofReal (q * Real.exp (-q * s)) := by
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
    congr 1
    rw [mul_add, Real.exp_add]
    ring
  change ENNReal.ofReal (q * Real.exp (-q * ((passageTimeMinus x f : ℝ) + s))) *
      F x * G ((reflectedFrom 0 f).1 ((passageTimeMinus x f : ℝ) + s).toNNReal) = _
  rw [hdensity, ← hval]
  ac_rfl

end BGW.StableTrees
