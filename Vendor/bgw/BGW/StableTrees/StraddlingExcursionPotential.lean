/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.StablePassageSubordinator
import BGW.StableTrees.StablePassageSubordinatorLaplace
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# Potential measure of stable passage times

The passage potential has Laplace transform `q^(-1/θ)`. Exponential tilting reduces
its identification to uniqueness of Laplace transforms for probability measures.

## References

J. Bertoin, *Lévy Processes*, Cambridge University Press, 1996, Chapter IV.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod
namespace BGW.StableTrees
/-- Potential density `s^{1/θ-1}/Γ(1/θ)` of the passage subordinator, on `s > 0`. -/
noncomputable def straddleAgeDensity (θ : ℝ) (s : ℝ) : ℝ≥0∞ :=
  (Ioi (0 : ℝ)).indicator
    (fun s => ENNReal.ofReal (s ^ (1 / θ - 1) / Real.Gamma (1 / θ))) s

private theorem laplace_path {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (x : ℝ≥0)
    {q : ℝ} (hq : 0 ≤ q) :
    ∫⁻ f, ENNReal.ofReal (Real.exp (-q * (passageTime x f : ℝ)))
      ∂(stableLocalLaw θ : Measure DLoc) =
    ENNReal.ofReal (Real.exp (-(x : ℝ) * q ^ (1 / θ))) := by
  have hi : Integrable (fun f : DLoc => Real.exp (-q * (passageTime x f : ℝ)))
      (stableLocalLaw θ : Measure DLoc) := by
    apply (integrable_const (1 : ℝ)).mono'
    · exact ((Real.continuous_exp.measurable.comp
        ((measurable_passageTime x).coe_nnreal_real.const_mul (-q)))).aestronglyMeasurable
    · filter_upwards [] with f
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hq)
        (passageTime x f).2)
  rw [← ofReal_integral_eq_lintegral_ofReal hi
    (Eventually.of_forall fun _ => (Real.exp_pos _).le)]
  congr 1
  rw [← integral_exp_neg_passageLaw hθ x hq, passageLaw, integral_map
    (measurable_passageTime x).coe_nnreal_real.aemeasurable
    (by fun_prop : Measurable (fun s : ℝ => Real.exp (-q * s))).aestronglyMeasurable]

private theorem potential_laplace {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {q : ℝ} (hq : 0 < q) :
    ∫⁻ x in Ioi (0 : ℝ), ∫⁻ f,
      ENNReal.ofReal (Real.exp (-q * (passageTime x.toNNReal f : ℝ)))
      ∂(stableLocalLaw θ : Measure DLoc) = ENNReal.ofReal (q ^ (-(1 / θ))) := by
  simp_rw [laplace_path hθ _ hq.le]
  have ha : 0 < q ^ (1 / θ) := Real.rpow_pos_of_pos hq _
  have heq : (fun x : ℝ => Real.exp (-(x.toNNReal : ℝ) * q ^ (1 / θ))) =ᵐ[
      volume.restrict (Ioi 0)] (fun x => Real.exp (-(q ^ (1 / θ)) * x)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    rw [Real.coe_toNNReal _ hx.le]
    congr 1
    ring
  calc
    _ = ∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-(q ^ (1 / θ)) * x)) :=
      lintegral_congr_ae (heq.fun_comp ENNReal.ofReal)
    _ = _ := by

      rw [← ofReal_integral_eq_lintegral_ofReal
        (integrableOn_exp_mul_Ioi (neg_neg_of_pos ha) 0)
        (Eventually.of_forall fun _ => (Real.exp_pos _).le)]
      congr 1
      rw [integral_exp_mul_Ioi (neg_neg_of_pos ha) 0]
      simp [Real.rpow_neg hq.le]

private theorem measure_eq_of_power_laplace {μ ν : Measure ℝ} {a : ℝ}
    (hμ0 : μ (Iio 0) = 0) (hν0 : ν (Iio 0) = 0)
    (hμ : ∀ q : ℝ, 0 < q → ∫⁻ s, ENNReal.ofReal (Real.exp (-q * s)) ∂μ =
      ENNReal.ofReal (q ^ (-a)))
    (hν : ∀ q : ℝ, 0 < q → ∫⁻ s, ENNReal.ofReal (Real.exp (-q * s)) ∂ν =
      ENNReal.ofReal (q ^ (-a))) : μ = ν := by
  let w : ℝ → ℝ≥0∞ := fun s => ENNReal.ofReal (Real.exp (-s))
  have hw : Measurable w := by fun_prop
  have hprob (ρ : Measure ℝ)
      (hρ : ∫⁻ s, ENNReal.ofReal (Real.exp (-1 * s)) ∂ρ = 1) :
      IsProbabilityMeasure (ρ.withDensity w) := by
    constructor
    rw [withDensity_apply _ MeasurableSet.univ, setLIntegral_univ]
    simpa [w] using hρ
  have hμ1 : IsProbabilityMeasure (μ.withDensity w) :=
    hprob μ (by simpa using hμ 1 zero_lt_one)
  have hν1 : IsProbabilityMeasure (ν.withDensity w) :=
    hprob ν (by simpa using hν 1 zero_lt_one)
  have hzero (ρ : Measure ℝ) (hρ : ρ (Iio 0) = 0) :
      ρ.withDensity w (Iio 0) = 0 := by
    rw [withDensity_apply _ measurableSet_Iio, Measure.restrict_eq_zero.mpr hρ]
    simp
  have htilt : μ.withDensity w = ν.withDensity w := by
    apply measure_eq_of_laplace_on_nonneg (hzero μ hμ0) (hzero ν hν0)
    intro q hq
    have hprod : ∀ s : ℝ, w s * ENNReal.ofReal (Real.exp (-q * s)) =
        ENNReal.ofReal (Real.exp (-(q + 1) * s)) := by
      intro s
      dsimp only [w]
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
      congr 2
      ring
    rw [integral_eq_lintegral_of_nonneg_ae
        (Eventually.of_forall fun _ => (Real.exp_pos _).le)
        (by fun_prop : AEStronglyMeasurable (fun s : ℝ => Real.exp (-q * s))
          (μ.withDensity w)),
      integral_eq_lintegral_of_nonneg_ae
        (Eventually.of_forall fun _ => (Real.exp_pos _).le)
        (by fun_prop : AEStronglyMeasurable (fun s : ℝ => Real.exp (-q * s))
          (ν.withDensity w))]
    rw [lintegral_withDensity_eq_lintegral_mul _ hw (by fun_prop),
      lintegral_withDensity_eq_lintegral_mul _ hw (by fun_prop)]
    simp only [Pi.mul_apply]
    simp_rw [hprod]
    rw [hμ (q + 1) (by linarith), hν (q + 1) (by linarith)]
  have hnz : ∀ s, w s ≠ 0 := fun s => ENNReal.ofReal_ne_zero_iff.mpr (Real.exp_pos _)
  have hnt : ∀ s, w s ≠ ⊤ := fun _ => ENNReal.ofReal_ne_top
  have hback := congrArg (fun ρ : Measure ℝ => ρ.withDensity (fun s => (w s)⁻¹)) htilt
  rwa [withDensity_inv_same hw (Eventually.of_forall hnz) (Eventually.of_forall hnt),
    withDensity_inv_same hw (Eventually.of_forall hnz) (Eventually.of_forall hnt)] at hback

private theorem measurable_straddleAgeDensity (θ : ℝ) :
    Measurable (straddleAgeDensity θ) := by
  apply Measurable.indicator _ measurableSet_Ioi
  fun_prop

private theorem age_laplace {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {q : ℝ} (hq : 0 < q) :
    ∫⁻ s, ENNReal.ofReal (Real.exp (-q * s))
      ∂volume.withDensity (straddleAgeDensity θ) = ENNReal.ofReal (q ^ (-(1 / θ))) := by
  have ha : 0 < 1 / θ := one_div_pos.mpr (lt_trans zero_lt_one hθ.1)
  have hg : 0 < Real.Gamma (1 / θ) := Real.Gamma_pos_of_pos ha
  have hi : IntegrableOn (fun s : ℝ => s ^ (1 / θ - 1) * Real.exp (-q * s)) (Ioi 0) := by
    simpa using integrableOn_rpow_mul_exp_neg_mul_rpow (s := 1 / θ - 1) (p := 1)
      (b := q) (by linarith) zero_lt_one hq
  rw [lintegral_withDensity_eq_lintegral_mul _ (measurable_straddleAgeDensity θ) (by fun_prop)]
  have hfun : (fun s => straddleAgeDensity θ s * ENNReal.ofReal (Real.exp (-q * s))) =
      (Ioi (0 : ℝ)).indicator (fun s => ENNReal.ofReal (s ^ (1 / θ - 1) /
        Real.Gamma (1 / θ)) * ENNReal.ofReal (Real.exp (-q * s))) := by
    funext s
    by_cases hs : 0 < s <;> simp [straddleAgeDensity, hs]
  change (∫⁻ s, straddleAgeDensity θ s * ENNReal.ofReal (Real.exp (-q * s))) = _
  rw [hfun, lintegral_indicator measurableSet_Ioi]
  have hc : (fun s => ENNReal.ofReal (s ^ (1 / θ - 1) / Real.Gamma (1 / θ)) *
      ENNReal.ofReal (Real.exp (-q * s))) =ᵐ[volume.restrict (Ioi 0)]
      (fun s => ENNReal.ofReal ((s ^ (1 / θ - 1) * Real.exp (-q * s)) /
        Real.Gamma (1 / θ))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    rw [← ENNReal.ofReal_mul (div_nonneg (Real.rpow_nonneg hs.le _) hg.le)]
    congr 1
    ring
  calc
    _ = ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal
        ((s ^ (1 / θ - 1) * Real.exp (-q * s)) / Real.Gamma (1 / θ)) :=
      lintegral_congr_ae hc
    _ = _ := by
      rw [← ofReal_integral_eq_lintegral_ofReal (hi.div_const _) (by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
        exact div_nonneg (mul_nonneg (Real.rpow_nonneg hs.le _) (Real.exp_pos _).le) hg.le)]
      congr 1
      rw [integral_div]
      rw [show (∫ s : ℝ in Ioi 0, s ^ (1 / θ - 1) * Real.exp (-q * s)) =
        (1 / q) ^ (1 / θ) * Real.Gamma (1 / θ) by
          simpa only [neg_mul] using Real.integral_rpow_mul_exp_neg_mul_Ioi ha hq]
      rw [mul_div_cancel_right₀ _ hg.ne', one_div, Real.inv_rpow hq.le,
        Real.rpow_neg hq.le]

private noncomputable def passagePotential (θ : ℝ) : Measure ℝ :=
  (((volume : Measure ℝ).restrict (Ioi 0)).prod (stableLocalLaw θ : Measure DLoc)).map
    (fun p => (passageTime p.1.toNNReal p.2 : ℝ))

private theorem measurable_potential_map :
    Measurable (fun p : ℝ × DLoc => (passageTime p.1.toNNReal p.2 : ℝ)) := by
  have hp : Measurable (fun p : ℝ × DLoc => (p.1.toNNReal, p.2)) :=
    (measurable_real_toNNReal.comp measurable_fst).prodMk measurable_snd
  exact (measurable_passageTime_uncurry.comp hp).coe_nnreal_real

private theorem passagePotential_laplace {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    {q : ℝ} (hq : 0 < q) :
    ∫⁻ s, ENNReal.ofReal (Real.exp (-q * s)) ∂passagePotential θ =
      ENNReal.ofReal (q ^ (-(1 / θ))) := by
  rw [passagePotential, lintegral_map (by fun_prop) measurable_potential_map]
  rw [lintegral_prod _
    ((measurable_potential_map.const_mul (-q)).exp.ennreal_ofReal).aemeasurable]
  exact potential_laplace hθ hq

/-- **Potential measure of the passage subordinator**: for measurable `B ⊆ ℝ`,
`∫_0^∞ P(T_x ∈ B) dx = ∫_B s^{1/θ-1}/Γ(1/θ) ds` (Laplace transform `q^{-1/θ}`). -/
theorem passage_potential_measure {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {B : Set ℝ}
    (hB : MeasurableSet B) :
    ∫⁻ x in Ioi (0 : ℝ),
        (stableLocalLaw θ : Measure DLoc) {f | (passageTime x.toNNReal f : ℝ) ∈ B} =
      ∫⁻ s in B, straddleAgeDensity θ s := by
  have hU0 : passagePotential θ (Iio 0) = 0 := by
    rw [passagePotential, Measure.map_apply measurable_potential_map measurableSet_Iio]
    have he : (fun p : ℝ × DLoc => (passageTime p.1.toNNReal p.2 : ℝ)) ⁻¹' Iio 0 = ∅ := by
      ext p
      simp only [mem_preimage, mem_Iio, mem_empty_iff_false, iff_false]
      exact not_lt_of_ge (passageTime p.1.toNNReal p.2).2
    rw [he, measure_empty]
  have hD0 : volume.withDensity (straddleAgeDensity θ) (Iio 0) = 0 := by
    rw [withDensity_apply _ measurableSet_Iio]
    apply lintegral_eq_zero_of_ae_eq_zero
    filter_upwards [ae_restrict_mem measurableSet_Iio] with s hs
    have hs' : s < 0 := hs
    have hn : ¬ 0 < s := not_lt_of_ge hs'.le
    simp only [straddleAgeDensity, mem_Ioi, hn, not_false_eq_true, indicator_of_notMem,
      Pi.zero_apply]
  have heq : passagePotential θ = volume.withDensity (straddleAgeDensity θ) :=
    measure_eq_of_power_laplace hU0 hD0 (fun _ hq => passagePotential_laplace hθ hq)
      (fun _ hq => age_laplace hθ hq)
  rw [← withDensity_apply _ hB, ← heq, passagePotential,
    Measure.map_apply measurable_potential_map hB,
    Measure.prod_apply (measurable_potential_map hB)]
  rfl

/-- Integral form of the passage potential identity for nonnegative measurable functions. -/
theorem lintegral_passage_potential {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    {F : ℝ → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ x in Ioi (0 : ℝ), ∫⁻ f, F (passageTime x.toNNReal f)
      ∂(stableLocalLaw θ : Measure DLoc) = ∫⁻ s, straddleAgeDensity θ s * F s := by
  have heq : passagePotential θ = volume.withDensity (straddleAgeDensity θ) := by
    ext B hB
    rw [passagePotential, Measure.map_apply measurable_potential_map hB,
      Measure.prod_apply (measurable_potential_map hB), withDensity_apply _ hB]
    exact passage_potential_measure hθ hB
  calc
    _ = ∫⁻ s, F s ∂passagePotential θ := by
      rw [passagePotential, lintegral_map hF measurable_potential_map]
      exact (lintegral_prod _ (hF.comp measurable_potential_map).aemeasurable).symm
    _ = _ := by
      rw [heq, lintegral_withDensity_eq_lintegral_mul _ (measurable_straddleAgeDensity θ) hF]
      rfl

end BGW.StableTrees
