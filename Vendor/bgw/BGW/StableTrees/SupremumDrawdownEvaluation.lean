/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.SupremumFactorization
public import BGW.StableTrees.SupremumDrawdownExponential

/-! # The stable process transform at an exponential clock

Reference: J. Bertoin, *Lévy Processes*, Cambridge University Press, 1996, Chapters IV and VI.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees

/-- The process value at the independent clock. -/
noncomputable def clockEval (p : DLoc × ℝ) : ℝ := p.1.1 p.2.toNNReal

/-- Joint evaluation at the independent clock is measurable. -/
theorem measurable_clockEval : Measurable clockEval := by
  have hp : Measurable (fun p : DLoc × ℝ => (p.1, p.2.toNNReal)) :=
    measurable_fst.prodMk measurable_snd.real_toNNReal
  exact DLoc.measurable_eval₂.comp hp

private theorem lintegral_exp_neg_eval {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {t : ℝ}
    (ht : 0 < t) {lam : ℝ} (hlam : 0 ≤ lam) :
    (∫⁻ f, ENNReal.ofReal (Real.exp (-lam * f.1 t.toNNReal))
      ∂(stableLocalLaw θ : Measure DLoc)) = ENNReal.ofReal (Real.exp (t * lam ^ θ)) := by
  have htN : 0 < t.toNNReal := Real.toNNReal_pos.mpr ht
  have hm : Measurable (fun x : ℝ => Real.exp (-lam * x)) := by fun_prop
  have hemap : (∫⁻ f, ENNReal.ofReal (Real.exp (-lam * f.1 t.toNNReal))
      ∂(stableLocalLaw θ : Measure DLoc)) =
      ∫⁻ x, ENNReal.ofReal (Real.exp (-lam * x))
        ∂(stableLawAt θ (t.toNNReal : ℝ) : Measure ℝ) := by
    calc
      _ = ∫⁻ x, ENNReal.ofReal (Real.exp (-lam * x))
          ∂(stableLocalLaw θ : Measure DLoc).map (DLoc.eval t.toNNReal) :=
        (lintegral_map hm.ennreal_ofReal (DLoc.measurable_eval t.toNNReal)).symm
      _ = _ := by rw [map_eval_stableLocalLaw hθ htN]
  rw [hemap]
  have hi : Integrable (fun x : ℝ => Real.exp (-lam * x))
      (stableLawAt θ (t.toNNReal : ℝ) : Measure ℝ) := by
    by_contra hn
    have hz := integral_undef hn
    rw [integral_exp_neg_mul_stableLawAt hθ (by positivity) hlam] at hz
    exact (Real.exp_pos _).ne' hz
  rw [← ofReal_integral_eq_lintegral_ofReal hi
    (Eventually.of_forall fun _ => (Real.exp_pos _).le),
    integral_exp_neg_mul_stableLawAt hθ (by positivity) hlam, Real.coe_toNNReal _ ht.le]

private theorem lintegral_exp_neg_clockEval {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    {q lam : ℝ} (hq : 0 < q) (hlam : 0 ≤ lam) (hc : lam ^ θ < q) :
    (∫⁻ p, ENNReal.ofReal (Real.exp (-lam * clockEval p)) ∂expClockLaw θ q) =
      ENNReal.ofReal (q / (q - lam ^ θ)) := by
  let := isProbabilityMeasure_expMeasure hq
  have hm : Measurable (fun p : DLoc × ℝ => ENNReal.ofReal (Real.exp (-lam * clockEval p))) :=
    (measurable_clockEval.const_mul (-lam)).exp.ennreal_ofReal
  rw [lintegral_expClockLaw θ hq hm]
  have he : (∫⁻ t in Ici (0 : ℝ), ENNReal.ofReal (q * Real.exp (-q * t)) *
      ∫⁻ f, ENNReal.ofReal (Real.exp (-lam * clockEval (f, t)))
        ∂(stableLocalLaw θ : Measure DLoc)) =
      ∫⁻ t in Ici (0 : ℝ), ENNReal.ofReal (q * Real.exp (-q * t)) *
        ENNReal.ofReal (Real.exp (t * lam ^ θ)) := by
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_of_ae (volume.ae_ne (0 : ℝ)),
      ae_restrict_mem measurableSet_Ici] with t hne ht
    rw [show (fun f : DLoc => ENNReal.ofReal (Real.exp (-lam * clockEval (f, t)))) =
      (fun f : DLoc => ENNReal.ofReal (Real.exp (-lam * f.1 t.toNNReal))) from rfl,
      lintegral_exp_neg_eval hθ (lt_of_le_of_ne ht hne.symm) hlam]
  rw [he]
  have htime := lintegral_expClockLaw θ hq
    (H := fun p : DLoc × ℝ => ENNReal.ofReal (Real.exp (p.2 * lam ^ θ))) (by fun_prop)
  rw [expClockLaw, lintegral_prod _ (by fun_prop)] at htime
  simp only [lintegral_const, measure_univ, mul_one] at htime
  rw [← htime]
  simpa only [mul_comm] using lintegral_exp_mul_expMeasure hq hc

/-- Input for the division step: `E e^{-λ X_{e_q}} = q/(q-λ^θ)` for `0 ≤ λ < q^{1/θ}`
(spectrally positive: `E e^{-λ X_t} = e^{t λ^θ}`), with integrability. -/
theorem integral_exp_neg_eval_expTime {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {q lam : ℝ} (hq : 0 < q)
    (hlam : 0 ≤ lam) (hlt : lam < q ^ (1 / θ)) :
    Integrable (fun p : DLoc × ℝ => Real.exp (-lam * p.1.1 p.2.toNNReal)) (expClockLaw θ q) ∧
      ∫ p, Real.exp (-lam * p.1.1 p.2.toNNReal) ∂expClockLaw θ q = q / (q - lam ^ θ) := by
  change Integrable (fun p => Real.exp (-lam * clockEval p)) (expClockLaw θ q) ∧
    (∫ p, Real.exp (-lam * clockEval p) ∂expClockLaw θ q) = q / (q - lam ^ θ)
  have hθ0 : 0 < θ := zero_lt_one.trans hθ.1
  have hroot : (q ^ (1 / θ)) ^ θ = q := by
    rw [← Real.rpow_mul hq.le, one_div_mul_cancel (ne_of_gt hθ0), Real.rpow_one]
  have hc : lam ^ θ < q := by
    rw [← hroot]
    exact Real.rpow_lt_rpow hlam hlt hθ0
  have he := lintegral_exp_neg_clockEval hθ hq hlam hc
  have hi : Integrable (fun p => Real.exp (-lam * clockEval p)) (expClockLaw θ q) := by
    refine ⟨((measurable_clockEval.const_mul (-lam)).exp).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun _ => (Real.exp_pos _).le), he]
    exact ENNReal.ofReal_lt_top
  refine ⟨hi, ?_⟩
  rw [← ofReal_integral_eq_lintegral_ofReal hi
    (Eventually.of_forall fun _ => (Real.exp_pos _).le)] at he
  have ht := congrArg ENNReal.toReal he
  simpa only [ENNReal.toReal_ofReal (integral_nonneg fun _ => (Real.exp_pos _).le),
    ENNReal.toReal_ofReal (div_nonneg hq.le (sub_pos.mpr hc).le)] using ht

end BGW.StableTrees
