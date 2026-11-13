/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.Attraction.LaplaceExpansion
public import BGW.StableTrees.Attraction.GaussianBranch
public import BGW.StableTrees.Attraction.LaplaceContinuity
public import BGW.StableTrees.Attraction.TransformConvergence
public import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
public import Mathlib.Probability.CentralLimitTheorem

/-!
# Canonical attraction

The Gaussian Abelian argument reuses the square-weighted absolute-step measure
and the Taylor/Fubini identities from `LaplaceExpansion`. At Karamata index zero,
its transform is asymptotic to the truncated second moment. Two integrations
supply the factor `1/2`; unboundedness makes the atom and centering corrections
negligible. The one-step expansions then imply attraction through Laplace continuity.
For finite positive variance, a general characteristic-function CLT supplies the
Gaussian limit directly, without a lower support assumption.
Ported from `BGWLeaves/StableAnalysis/CanonicalAttraction.lean` of the author's arXiv:1110.2163v4
formalization (local snapshot of 6 November 2026).
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped Topology ENNReal

namespace BGW.StableTrees.Attraction.CanonicalAttraction

open BGW.StableTrees
open LaplaceExpansion GaussianBranch

variable {ν : Measure ℤ} [IsProbabilityMeasure ν]

omit [IsProbabilityMeasure ν] in
private theorem moment_regularlyVarying_zero
    (hK : SlowlyVarying (truncSecondMoment ν))
    (hKinf : Tendsto (truncSecondMoment ν) atTop atTop) :
    KaramataTransforms.RegularlyVarying
      (KaramataTransforms.cumulative (secondMomentMeasure ν)) 0 := by
  have heq : KaramataTransforms.cumulative (secondMomentMeasure ν) =
      truncSecondMoment ν := funext (secondMomentMeasure_cumulative ν)
  rw [heq, KaramataTransforms.regularlyVarying_zero_iff]
  exact ⟨hKinf.eventually_gt_atTop 0, hK⟩

/-- At the Gaussian boundary the damped second moment is asymptotic to `K`. -/
theorem gaussian_dampedSecondMoment_ratio
    (hK : SlowlyVarying (truncSecondMoment ν))
    (hKinf : Tendsto (truncSecondMoment ν) atTop atTop) :
    Tendsto (fun x : ℝ => KaramataTransforms.laplace (secondMomentMeasure ν) (1 / x) /
      truncSecondMoment ν x) atTop (𝓝 1) := by
  have h := KaramataTransforms.laplace_abelian_ratio (secondMomentMeasure ν)
    (by norm_num : (0 : ℝ) ≤ 0) (by norm_num : (0 : ℝ) < 1)
    (fun _ hs => secondMomentMeasure_laplace_integrable ν hs)
    (moment_regularlyVarying_zero hK hKinf)
  simpa only [secondMomentMeasure_cumulative, add_zero, Real.Gamma_one] using h

/-- The absolute-step exponential remainder on the Gaussian scale. -/
theorem gaussian_absolute_remainder_ratio
    (hint : Integrable (fun z : ℤ => (z : ℝ)) ν)
    (hK : SlowlyVarying (truncSecondMoment ν))
    (hKinf : Tendsto (truncSecondMoment ν) atTop atTop) :
    Tendsto (fun x : ℝ =>
      (∫ z, Real.exp (-(1 / x) * |(z : ℝ)|) - 1 + (1 / x) * |(z : ℝ)| ∂ν) /
        (truncSecondMoment ν x / x ^ 2)) atTop (𝓝 (1 / 2 : ℝ)) := by
  let M := secondMomentMeasure ν
  have hU := moment_regularlyVarying_zero hK hKinf
  have hfinite := fun s hs => secondMomentMeasure_laplace_integrable ν (s := s) hs
  have hi := integrated_laplace_ratio_limit M (by norm_num : (0 : ℝ) ≤ 0)
    (by norm_num : (0 : ℝ) < 1) hfinite hU
  have hprod := hi.mul (gaussian_dampedSecondMoment_ratio hK hKinf)
  norm_num only [sub_zero, one_mul, mul_one] at hprod
  have hF := (KaramataTransforms.laplace_abelian M (by norm_num : (0 : ℝ) ≤ 0)
    (by norm_num : (0 : ℝ) < 1) hfinite hU).1
  apply hprod.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ), hF, hKinf.eventually_gt_atTop 0]
    with x hx hFx hKx
  have hI : (∫ t in Ioo (0 : ℝ) 1, (1 - t) *
      (KaramataTransforms.laplace M (t / x) / KaramataTransforms.laplace M (1 / x))) =
      (∫ t in Ioo (0 : ℝ) 1, (1 - t) * KaramataTransforms.laplace M (t / x)) /
        KaramataTransforms.laplace M (1 / x) := by
    rw [← integral_div]
    apply integral_congr_ae
    exact Eventually.of_forall fun t => by dsimp only; ring
  rw [hI, div_mul_div_cancel₀ hFx.ne']
  have hA := absolute_remainder_eq_integrated_laplace hint (one_div_pos.2 hx)
  simp only [div_mul_eq_mul_div, one_mul] at hA
  rw [← hA]
  field_simp

omit [IsProbabilityMeasure ν] in
/-- Every fixed deterministic quadratic error is negligible when `K → ∞`. -/
theorem gaussian_exp_remainder_ratio_zero
    (hKinf : Tendsto (truncSecondMoment ν) atTop atTop) (m : ℝ) :
    Tendsto (fun x : ℝ => (Real.exp (m / x) - 1 - m / x) /
      (truncSecondMoment ν x / x ^ 2)) atTop (𝓝 0) := by
  apply squeeze_zero_norm' _ (show Tendsto (fun x : ℝ => m ^ 2 / truncSecondMoment ν x)
    atTop (𝓝 0) from tendsto_const_nhds.div_atTop hKinf)
  filter_upwards [eventually_ge_atTop (max |m| 1), hKinf.eventually_gt_atTop 0]
    with x hx hKx
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one ((le_max_right _ _).trans hx)
  have hm : ‖m / x‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hx0, div_le_one hx0]
    exact (le_max_left _ _).trans hx
  have hD : 0 < truncSecondMoment ν x / x ^ 2 := div_pos hKx (sq_pos_of_pos hx0)
  rw [norm_div, Real.norm_eq_abs (truncSecondMoment ν x / x ^ 2), abs_of_pos hD]
  calc
    _ ≤ ‖m / x‖ ^ 2 / (truncSecondMoment ν x / x ^ 2) :=
      div_le_div_of_nonneg_right (Real.norm_exp_sub_one_sub_id_le hm) hD.le
    _ = _ := by
      simp only [norm_div, Real.norm_eq_abs, div_pow, sq_abs]
      field_simp

/-- The uncentered Gaussian Laplace remainder. -/
theorem gaussian_uncentered_remainder_ratio
    (hstep : ν {z : ℤ | z < -1} = 0)
    (hint : Integrable (fun z : ℤ => (z : ℝ)) ν)
    (hK : SlowlyVarying (truncSecondMoment ν))
    (hKinf : Tendsto (truncSecondMoment ν) atTop atTop) :
    Tendsto (fun x : ℝ =>
      ((∫ z, Real.exp (-(1 / x) * (z : ℝ)) ∂ν) - 1 + mean ν / x) /
        (truncSecondMoment ν x / x ^ 2)) atTop (𝓝 (1 / 2 : ℝ)) := by
  have he := ((gaussian_exp_remainder_ratio_zero hKinf 1).sub
    (gaussian_exp_remainder_ratio_zero hKinf (-1))).const_mul (ν.real {(-1 : ℤ)})
  simp only [sub_zero, mul_zero] at he
  have hlim := (gaussian_absolute_remainder_ratio hint hK hKinf).add he
  simp only [add_zero] at hlim
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  have hraw := uncentered_remainder_eq_absolute hstep hint (one_div_pos.2 hx).le
  rw [show mean ν / x = (1 / x) * mean ν by ring, hraw, add_div]
  simp only [one_div, neg_div]
  ring

/-- Gaussian D1: the centered remainder is asymptotic to `K(x)/(2 x²)`. -/
theorem gaussian_centeredLaplace_ratio
    (hstep : ν {z : ℤ | z < -1} = 0)
    (hint : Integrable (fun z : ℤ => (z : ℝ)) ν)
    (hK : SlowlyVarying (truncSecondMoment ν))
    (hKinf : Tendsto (truncSecondMoment ν) atTop atTop) :
    Tendsto (fun x : ℝ => (centeredLaplace ν (1 / x) - 1) /
      (truncSecondMoment ν x / x ^ 2)) atTop (𝓝 (1 / 2 : ℝ)) := by
  have he := gaussian_exp_remainder_ratio_zero hKinf (-mean ν)
  have hm : Tendsto (fun x : ℝ => mean ν / x) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have hexp := Real.continuous_exp.continuousAt.tendsto.comp hm
  simp only [Real.exp_zero] at hexp
  have hlim := hexp.mul ((gaussian_uncentered_remainder_ratio hstep hint hK hKinf).sub he)
  simp only [sub_zero, one_mul] at hlim
  apply hlim.congr
  intro x
  rw [centeredLaplace_eq]
  have hex : Real.exp (mean ν / x) * Real.exp (-mean ν / x) = 1 := by
    rw [← Real.exp_add, show mean ν / x + -mean ν / x = 0 by ring, Real.exp_zero]
  rw [show 1 / x * mean ν = mean ν / x by ring]
  dsimp only [Function.comp_def]
  rw [← sub_div, ← mul_div_assoc]
  congr 1
  rw [neg_div]
  rw [neg_div] at hex
  nlinarith

/-- Gaussian D1 in asymptotic-equivalence form at zero from the right. -/
theorem gaussian_centeredLaplace_isEquivalent
    (hstep : ν {z : ℤ | z < -1} = 0)
    (hint : Integrable (fun z : ℤ => (z : ℝ)) ν)
    (hK : SlowlyVarying (truncSecondMoment ν))
    (hKinf : Tendsto (truncSecondMoment ν) atTop atTop) :
    Asymptotics.IsEquivalent (𝓝[>] (0 : ℝ)) (fun s => centeredLaplace ν s - 1)
      (fun s => s ^ 2 * truncSecondMoment ν (1 / s) / 2) := by
  have h := (gaussian_centeredLaplace_ratio hstep hint hK hKinf).div_const (1 / 2 : ℝ)
  norm_num only [div_self (by norm_num : (1 / 2 : ℝ) ≠ 0)] at h
  have hc := h.comp tendsto_inv_nhdsGT_zero
  apply Asymptotics.isEquivalent_of_tendsto_one
  apply hc.congr
  intro s
  dsimp only [Function.comp_def, Pi.div_apply]
  simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm, inv_pow]

/-- The Gaussian canonical norming diverges. -/
theorem gaussian_norming_tendsto_atTop
    (hK : SlowlyVarying (truncSecondMoment ν))
    (hKinf : Tendsto (truncSecondMoment ν) atTop atTop) :
    Tendsto (norming ν 2) atTop atTop := by
  exact ((gaussQuantile_tendsto_atTop hK hKinf).atTop_div_const
    (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2))).congr'
      ((norming_two_eventually_eq hK hKinf).mono fun _ hn => hn.symm)

omit [IsProbabilityMeasure ν] in
private theorem gaussian_norming_sq
    (hKinf : Tendsto (truncSecondMoment ν) atTop atTop) (n : ℕ) :
    norming ν 2 n ^ 2 = (n : ℝ) * truncSecondMoment ν (gaussQuantile ν n) / 2 := by
  classical
  simp only [norming, ite_eq_right (not_integrable_of_tendsto_atTop hKinf),
    lt_self_iff_false, ite_false]
  exact Real.sq_sqrt (div_nonneg (mul_nonneg (Nat.cast_nonneg _)
    (truncSecondMoment_nonneg' _)) (by norm_num))

/-- Slow variation and the exact Gaussian crossing identify the scaled moment. -/
theorem gaussian_norming_moment_limit
    (hK : SlowlyVarying (truncSecondMoment ν))
    (hKinf : Tendsto (truncSecondMoment ν) atTop atTop)
    {lam : ℝ} (hlam : 0 < lam) :
    Tendsto (fun n : ℕ => (n : ℝ) * truncSecondMoment ν (norming ν 2 n / lam) /
      (norming ν 2 n / lam) ^ 2) atTop (𝓝 (2 * lam ^ 2)) := by
  let c : ℝ := 1 / (Real.sqrt 2 * lam)
  have hc : 0 < c := by dsimp [c]; positivity
  have hlim := ((hK c hc).comp (gaussQuantile_tendsto_atTop hK hKinf)).const_mul
    (2 * lam ^ 2)
  rw [mul_one] at hlim
  apply hlim.congr'
  filter_upwards [norming_two_eventually_eq hK hKinf,
    (truncSecondMoment_gaussQuantile_tendsto_atTop hK hKinf).eventually_gt_atTop 0,
    eventually_gt_atTop (0 : ℕ)] with n hn hKn hn0
  have harg : c * gaussQuantile ν n = norming ν 2 n / lam := by
    rw [hn]
    dsimp [c]
    ring
  dsimp only [Function.comp_def]
  rw [harg, div_pow, gaussian_norming_sq hKinf]
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn0.ne'
  field_simp

/-- Gaussian D1: the one-step limit on the canonical norming. -/
theorem gaussian_norming_centeredLaplace_limit
    (hstep : ν {z : ℤ | z < -1} = 0)
    (hint : Integrable (fun z : ℤ => (z : ℝ)) ν)
    (hK : SlowlyVarying (truncSecondMoment ν))
    (hKinf : Tendsto (truncSecondMoment ν) atTop atTop)
    {lam : ℝ} (hlam : 0 < lam) :
    Tendsto (fun n : ℕ => (n : ℝ) *
      (centeredLaplace ν (lam / norming ν 2 n) - 1)) atTop (𝓝 (lam ^ (2 : ℝ))) := by
  have ha := (gaussian_norming_tendsto_atTop hK hKinf).atTop_div_const hlam
  have hratio := (gaussian_centeredLaplace_ratio hstep hint hK hKinf).comp ha
  have hprod := hratio.mul (gaussian_norming_moment_limit hK hKinf hlam)
  have hc : (1 / 2 : ℝ) * (2 * lam ^ 2) = lam ^ (2 : ℝ) := by
    rw [Real.rpow_two]
    ring
  rw [hc] at hprod
  apply hprod.congr'
  filter_upwards [ha.eventually_gt_atTop 0, ha.eventually (hKinf.eventually_gt_atTop 0)]
    with n hn hKn
  dsimp only [Function.comp_def]
  rw [one_div_div]
  generalize norming ν 2 n / lam = x at hn hKn ⊢
  generalize truncSecondMoment ν x = k at hKn ⊢
  field_simp

/-- A one-step centered Laplace expansion gives attraction after taking powers.
The centering factor here is exactly the one used by the continuity provider. -/
theorem isStableAttracted_of_centered_one_step_limit
    {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    (hstep : ν {z : ℤ | z < -1} = 0)
    (hint : Integrable (fun z : ℤ => (z : ℝ)) ν)
    {b : ℕ → ℝ} (hb : ∀ᶠ n in atTop, 0 < b n)
    (hL : ∀ lam : ℝ, 0 < lam →
      Tendsto (fun n : ℕ => (n : ℝ) * (centeredLaplace ν (lam / b n) - 1))
        atTop (𝓝 (lam ^ θ))) :
    IsStableAttracted ν θ (mean ν) b := by
  apply LaplaceContinuity.isStableAttracted_of_centered_laplace_limit ν hθ hstep hint
    (eventually_atTop.1 hb)
  intro lam hlam
  apply (Real.tendsto_one_add_pow_exp_of_tendsto (hL lam hlam)).congr
  intro n
  rw [add_sub_cancel, centeredLaplace_eq]
  rw [TransformConvergence.stepLaplace]
  congr 1
  ring

/-- D2(i): regularly varying right tail, with index strictly between one and two. -/
theorem isStableAttracted_of_regVary_tail
    (hstep : ν {z : ℤ | z < -1} = 0)
    (hint : Integrable (fun z : ℤ => (z : ℝ)) ν)
    {θ : ℝ} (hθ1 : 1 < θ) (hθ2 : θ < 2)
    (hT : MonotoneDensity.IsRegVaryAtTop
      (fun x : ℝ => ν.real {z : ℤ | x < (z : ℝ)}) (-θ)) :
    IsStableAttracted ν θ (mean ν) (norming ν θ) := by
  have ha : Tendsto (norming ν θ) atTop atTop := by
    rw [norming_eq_tailNorming hstep hθ1 hθ2 hT]
    exact tailNorming_tendsto_atTop hθ1 hθ2 hT
  exact isStableAttracted_of_centered_one_step_limit ⟨hθ1, hθ2.le⟩ hstep hint
    (ha.eventually_gt_atTop 0) fun _ hlam =>
      norming_centeredLaplace_limit hstep hint hθ1 hθ2 hT hlam

/-- D2(ii): the infinite-variance Gaussian criterion. -/
theorem isStableAttracted_of_slowlyVarying_moment
    (hstep : ν {z : ℤ | z < -1} = 0)
    (hint : Integrable (fun z : ℤ => (z : ℝ)) ν)
    (hK : SlowlyVarying (truncSecondMoment ν))
    (hKinf : Tendsto (truncSecondMoment ν) atTop atTop) :
    IsStableAttracted ν 2 (mean ν) (norming ν 2) :=
  isStableAttracted_of_centered_one_step_limit (by norm_num) hstep hint
    ((gaussian_norming_tendsto_atTop hK hKinf).eventually_gt_atTop 0) fun _ hlam =>
      gaussian_norming_centeredLaplace_limit hstep hint hK hKinf hlam

/-- D2(iii) in the critical offspring-law setting already covered by BGW. -/
theorem isStableAttracted_finiteVariance_stepLaw
    {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hfin : MemLp (fun j : ℕ => (j : ℝ)) 2 μ.toMeasure) :
    IsStableAttracted (stepLaw μ) 2 (mean (stepLaw μ)) (norming (stepLaw μ) 2) := by
  rw [mean_stepLaw hc]
  exact stableDomain_isStableAttracted (stableDomain_norming_finiteVariance hc hne hfin)

omit [IsProbabilityMeasure ν] in
private theorem standardized_charFun (m σ u : ℝ) :
    charFun (ν.map (fun z : ℤ => ((z : ℝ) - m) / σ)) u =
      Complex.exp (-((u / σ * m : ℝ) : ℂ) * Complex.I) *
        TransformConvergence.stepCharFun ν (u / σ) := by
  rw [charFun_apply_real, integral_map (by fun_prop) (by fun_prop),
    TransformConvergence.stepCharFun, charFun_apply_real,
    integral_map (by fun_prop) (by fun_prop), ← integral_const_mul]
  apply integral_congr_ae
  exact Eventually.of_forall fun z => by
    dsimp only
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring

/-- D2(iii) for a general integer law of finite, strictly positive variance.
No lower support bound is needed for this CLT proof. Positive variance excludes
the degenerate case, whose canonical norming is identically zero. -/
theorem isStableAttracted_of_finiteVariance
    (hint : Integrable (fun z : ℤ => (z : ℝ)) ν)
    (hsq : Integrable (fun z : ℤ => (z : ℝ) ^ 2) ν)
    (hvar : 0 < variance ν) :
    IsStableAttracted ν 2 (mean ν) (norming ν 2) := by
  let σ : ℝ := Real.sqrt (variance ν)
  have hσ : 0 < σ := Real.sqrt_pos.2 hvar
  have hσsq : σ ^ 2 = variance ν := Real.sq_sqrt hvar.le
  let X : ℤ → ℝ := fun z => ((z : ℝ) - mean ν) / σ
  have h0 : ∫ z, X z ∂ν = 0 := by
    dsimp [X]
    rw [integral_div, integral_sub hint (integrable_const _)]
    simp [mean]
  have h1 : ∫ z, X z ^ 2 ∂ν = 1 := by
    simp only [X, div_pow]
    rw [integral_div, ← variance, hσsq, div_self hvar.ne']
  let P : ℕ → ProbabilityMeasure ℝ :=
    TransformConvergence.centeredScaledWalkProb ν (mean ν) (norming ν 2)
  let Q : ProbabilityMeasure ℝ := ⟨ProbabilityTheory.gaussianReal 0 2, inferInstance⟩
  have hweak : Tendsto P atTop (𝓝 Q) := by
    rw [ProbabilityMeasure.tendsto_iff_tendsto_charFun]
    intro t
    have hclt := ProbabilityTheory.tendsto_charFun_inv_sqrt_mul_pow (P := ν)
      (X := X) (by fun_prop) h0 h1 (Real.sqrt 2 * t)
    have hgauss : Complex.exp (-(((Real.sqrt 2 * t : ℝ) : ℂ) ^ 2) / 2) =
        charFun (ProbabilityTheory.gaussianReal 0 2) t := by
      rw [ProbabilityTheory.charFun_gaussianReal]
      push_cast
      have h2 : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by
        rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]
        norm_num
      rw [mul_pow, h2]
      congr 1
      ring
    rw [hgauss] at hclt
    apply hclt.congr'
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
    have hsn : Real.sqrt (n : ℝ) ≠ 0 := (Real.sqrt_pos.2 hnR).ne'
    have hs2 : Real.sqrt (2 : ℝ) ≠ 0 := (Real.sqrt_pos.2 (by norm_num)).ne'
    have harg : ((Real.sqrt n)⁻¹ * (Real.sqrt 2 * t)) / σ = t / norming ν 2 n := by
      rw [norming_of_integrable_sq hsq, Real.sqrt_div (Nat.cast_nonneg n)]
      change _ = t / (σ * (Real.sqrt (n : ℝ) / Real.sqrt 2))
      field_simp
    change charFun (ν.map (fun z : ℤ => ((z : ℝ) - mean ν) / σ))
        ((Real.sqrt n)⁻¹ * (Real.sqrt 2 * t)) ^ n =
      charFun (TransformConvergence.centeredScaledWalk ν (mean ν) (norming ν 2 n) n) t
    rw [standardized_charFun, harg, mul_pow, ← Complex.exp_nat_mul,
      TransformConvergence.centeredScaledWalk_charFun]
    congr 1
    congr 1
    push_cast
    ring
  refine { alpha_mem := by norm_num, pos := ⟨1, ?_⟩, converges := ?_ }
  · intro n hn
    rw [norming_of_integrable_sq hsq]
    apply mul_pos hσ
    apply Real.sqrt_pos.2
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  · refine ⟨ProbabilityTheory.gaussianReal 0 2, inferInstance, ?_, ?_⟩
    · intro lam _
      have ht := congrFun (ProbabilityTheory.mgf_id_gaussianReal (μ := 0) (v := 2)) (-lam)
      simp only [ProbabilityTheory.mgf, id] at ht
      rw [ht, Real.rpow_two]
      congr 1
      push_cast
      ring
    · intro f
      have h := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 hweak f
      simpa [P, Q, TransformConvergence.centeredScaledWalkProb,
        TransformConvergence.centeredScaledWalk_eq_map] using h

end BGW.StableTrees.Attraction.CanonicalAttraction
