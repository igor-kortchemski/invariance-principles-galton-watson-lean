/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.Attraction.KaramataTransforms
public import BGW.StableTrees.Attraction.MonotoneDensity
public import BGW.StableTrees.Attraction.QuantileInversion
public import BGW.StableTrees.Attraction.Defs

/-!
# Heavy-tail Laplace expansion and canonical tail normalization

The tail convention throughout is the strict right tail. The canonical constant
is `-Gamma (1 - θ)`, which is positive for `1 < θ < 2`.

The proof applies Laplace--Karamata to the square-weighted absolute-step law,
then integrates its transform twice using Taylor's formula and a dyadic power
majorant. The negative atom and deterministic centering give negligible
quadratic corrections. The final theorem supplies the one-step limit for D2.
Ported from `BGWLeaves/StableAnalysis/LaplaceExpansion.lean` of the author's arXiv:1110.2163v4
formalization (local snapshot of 6 November 2026).
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped Topology ENNReal

namespace BGW.StableTrees.Attraction.LaplaceExpansion

open MonotoneDensity QuantileInversion

/-- The centered one-step Laplace transform. -/
noncomputable def centeredLaplace (ν : Measure ℤ) (s : ℝ) : ℝ :=
  ∫ z, Real.exp (-s * ((z : ℝ) - mean ν)) ∂ν

/-- The corrected tail norming, before selecting the variance branch of `norming`. -/
noncomputable def tailNorming (ν : Measure ℤ) (θ : ℝ) (n : ℕ) : ℝ :=
  (-Real.Gamma (1 - θ)) ^ (1 / θ) * tailQuantile ν n

private theorem ae_lower_bound {ν : Measure ℤ} (hstep : ν {z : ℤ | z < -1} = 0) :
    ∀ᵐ z : ℤ ∂ν, (-1 : ℝ) ≤ (z : ℝ) := by
  rw [ae_iff]
  have hset : {z : ℤ | ¬ (-1 : ℝ) ≤ (z : ℝ)} = {z : ℤ | z < -1} := by
    ext z
    norm_cast
    simp
  rwa [hset]

theorem uncenteredLaplace_integrable {ν : Measure ℤ} [IsProbabilityMeasure ν]
    (hstep : ν {z : ℤ | z < -1} = 0) {s : ℝ} (hs : 0 ≤ s) :
    Integrable (fun z : ℤ => Real.exp (-s * (z : ℝ))) ν := by
  refine Integrable.of_bound (by fun_prop) (Real.exp s) ?_
  filter_upwards [ae_lower_bound hstep] with z hz
  rw [Real.norm_of_nonneg (Real.exp_nonneg _)]
  apply Real.exp_le_exp.mpr
  nlinarith [mul_nonneg hs (show 0 ≤ (z : ℝ) + 1 by linarith)]

theorem centeredLaplace_integrable {ν : Measure ℤ} [IsProbabilityMeasure ν]
    (hstep : ν {z : ℤ | z < -1} = 0) {s : ℝ} (hs : 0 ≤ s) :
    Integrable (fun z : ℤ => Real.exp (-s * ((z : ℝ) - mean ν))) ν := by
  convert (uncenteredLaplace_integrable hstep hs).const_mul (Real.exp (s * mean ν)) using 1
  ext z
  rw [← Real.exp_add]
  congr 1
  ring

theorem centeredLaplace_eq (ν : Measure ℤ) (s : ℝ) :
    centeredLaplace ν s =
      Real.exp (s * mean ν) * ∫ z, Real.exp (-s * (z : ℝ)) ∂ν := by
  rw [centeredLaplace, ← integral_const_mul]
  apply integral_congr_ae
  exact Eventually.of_forall fun z => by
    dsimp only
    rw [← Real.exp_add]
    congr 1
    ring

/-- Centering removes the linear term exactly inside the expectation. -/
theorem centeredLaplace_sub_one_eq_integral {ν : Measure ℤ} [IsProbabilityMeasure ν]
    (hstep : ν {z : ℤ | z < -1} = 0)
    (hint : Integrable (fun z : ℤ => (z : ℝ)) ν) {s : ℝ} (hs : 0 ≤ s) :
    centeredLaplace ν s - 1 =
      ∫ z, (Real.exp (-s * ((z : ℝ) - mean ν)) - 1 +
        s * ((z : ℝ) - mean ν)) ∂ν := by
  have hi := centeredLaplace_integrable hstep hs
  have hm : Integrable (fun z : ℤ => s * ((z : ℝ) - mean ν)) ν :=
    (hint.sub (integrable_const _)).const_mul s
  rw [integral_add (f := fun z : ℤ => Real.exp (-s * ((z : ℝ) - mean ν)) - 1)
    (g := fun z : ℤ => s * ((z : ℝ) - mean ν))
    ((centeredLaplace_integrable hstep hs).sub (integrable_const 1))
    hm,
    integral_sub (centeredLaplace_integrable hstep hs) (integrable_const 1),
    integral_const_mul, integral_sub hint (integrable_const _)]
  simp [centeredLaplace, mean]

/-- Convert the ratio-only convention to the positive-function convention. -/
theorem regularlyVarying_of_nonneg {T : ℝ → ℝ} {ρ : ℝ}
    (hnn : ∀ x, 0 ≤ T x) (hT : IsRegVaryAtTop T ρ) :
    KaramataTransforms.RegularlyVarying T ρ := by
  refine ⟨?_, hT⟩
  have h := (hT 1 one_pos).eventually
    (isOpen_ne.mem_nhds (show (1 : ℝ) ^ ρ ≠ 0 by simp))
  filter_upwards [h] with x hx
  have hne : T x ≠ 0 := by
    intro hz
    exact hx (by simp [hz])
  exact lt_of_le_of_ne (hnn x) hne.symm

/-- The slowly varying factor extracted from a regularly varying nonnegative function. -/
theorem slowlyVarying_factor {T : ℝ → ℝ} {θ : ℝ}
    (hnn : ∀ x, 0 ≤ T x) (hT : IsRegVaryAtTop T (-θ)) :
    BGW.StableTrees.SlowlyVarying (fun x : ℝ => x ^ θ * T x) := by
  intro c hc
  have h := (hT c hc).const_mul (c ^ θ)
  have hcθ : c ^ θ * c ^ (-θ) = 1 := by rw [← Real.rpow_add hc]; simp
  rw [hcθ] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ), (regularlyVarying_of_nonneg hnn hT).1]
    with x hx hTx
  rw [Real.mul_rpow hc.le hx.le]
  have hxθ : x ^ θ ≠ 0 := (Real.rpow_pos_of_pos hx _).ne'
  field_simp

/-- Polynomially weighted tails grow when the weight exceeds the tail index. -/
theorem rpow_mul_tail_tendsto_atTop {T : ℝ → ℝ} {θ p : ℝ}
    (hnn : ∀ x, 0 ≤ T x) (hmeas : Measurable T)
    (hT : IsRegVaryAtTop T (-θ)) (hp : θ < p) :
    Tendsto (fun x : ℝ => x ^ p * T x) atTop atTop := by
  have h := SlowVariation.slow_rpow_mul_tendsto_atTop
    ((measurable_id.pow_const θ).mul hmeas)
    (fun x hx => mul_nonneg (Real.rpow_nonneg hx.le _) (hnn x))
    (slowlyVarying_factor hnn hT) (sub_pos.2 hp)
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  dsimp only [Pi.mul_apply, id_eq]
  rw [← mul_assoc, ← Real.rpow_add hx, sub_add_cancel]

/-- Any bounded quadratic correction is negligible on the heavy-tail scale. -/
theorem quadratic_div_tail_tendsto_zero {T : ℝ → ℝ} {θ : ℝ}
    (hnn : ∀ x, 0 ≤ T x) (hmeas : Measurable T)
    (hT : IsRegVaryAtTop T (-θ)) (hθ : θ < 2) (C : ℝ) :
    Tendsto (fun x : ℝ => (C / x ^ 2) / T x) atTop (𝓝 0) := by
  have h : Tendsto (fun x : ℝ => C / (x ^ (2 : ℝ) * T x)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (rpow_mul_tail_tendsto_atTop hnn hmeas hT hθ)
  simp only [Real.rpow_two] at h
  convert h using 1
  ext x
  rw [div_div]

/-- The quadratic Taylor remainder of a deterministic exponential is negligible
relative to a tail of index strictly below two. -/
theorem exp_remainder_div_tail_tendsto_zero {T : ℝ → ℝ} {θ : ℝ}
    (hnn : ∀ x, 0 ≤ T x) (hmeas : Measurable T)
    (hT : IsRegVaryAtTop T (-θ)) (hθ : θ < 2) (m : ℝ) :
    Tendsto (fun x : ℝ => (Real.exp (m / x) - 1 - m / x) / T x)
      atTop (𝓝 0) := by
  apply squeeze_zero_norm' _ (quadratic_div_tail_tendsto_zero hnn hmeas hT hθ (m ^ 2))
  filter_upwards [eventually_ge_atTop (max |m| 1),
    (regularlyVarying_of_nonneg hnn hT).1] with x hx hTx
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one ((le_max_right _ _).trans hx)
  have hm : ‖m / x‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hx0, div_le_one hx0]
    exact (le_max_left _ _).trans hx
  rw [norm_div, Real.norm_eq_abs (T x), abs_of_pos hTx]
  apply div_le_div_of_nonneg_right _ hTx.le
  have hb := Real.norm_exp_sub_one_sub_id_le hm
  simpa only [norm_div, Real.norm_eq_abs, sq_abs, div_pow] using hb

/-- Multiplication by the deterministic centering exponential does not alter the
heavy-tail expansion. The hypothesis concerns only the uncentered remainder. -/
theorem centered_ratio_of_uncentered {ν : Measure ℤ} [IsProbabilityMeasure ν]
    {θ : ℝ} (hθ : θ < 2)
    (hT : IsRegVaryAtTop (fun x : ℝ => ν.real {z : ℤ | x < (z : ℝ)}) (-θ))
    {C : ℝ}
    (hU : Tendsto (fun x : ℝ =>
      ((∫ z, Real.exp (-(1 / x) * (z : ℝ)) ∂ν) - 1 + mean ν / x) /
        ν.real {z : ℤ | x < (z : ℝ)}) atTop (𝓝 C)) :
    Tendsto (fun x : ℝ => (centeredLaplace ν (1 / x) - 1) /
      ν.real {z : ℤ | x < (z : ℝ)}) atTop (𝓝 C) := by
  let T : ℝ → ℝ := fun x => ν.real {z : ℤ | x < (z : ℝ)}
  have hnn : ∀ x, 0 ≤ T x := fun _ => measureReal_nonneg
  have hmeas : Measurable T :=
    (show Antitone T from fun a b hab => measureReal_mono
      (fun _ hz => lt_of_le_of_lt hab hz)).measurable
  have he := exp_remainder_div_tail_tendsto_zero hnn hmeas hT hθ (-mean ν)
  have hm : Tendsto (fun x : ℝ => mean ν / x) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have hexp := Real.continuous_exp.continuousAt.tendsto.comp hm
  simp only [Real.exp_zero] at hexp
  have hlim := hexp.mul (hU.sub he)
  simp only [sub_zero, one_mul] at hlim
  apply hlim.congr
  intro x
  rw [centeredLaplace_eq]
  have hex : Real.exp (mean ν / x) * Real.exp (-mean ν / x) = 1 := by
    rw [← Real.exp_add, show mean ν / x + -mean ν / x = 0 by ring, Real.exp_zero]
  have heq : 1 / x * mean ν = mean ν / x := by ring
  rw [heq]
  dsimp only [T, Function.comp_def]
  rw [← sub_div, ← mul_div_assoc]
  congr 1
  rw [neg_div]
  rw [neg_div] at hex
  nlinarith

/-- The square-weighted law of the absolute step. Its cumulative mass is the
truncated second moment, with no correction for the negative atom. -/
noncomputable def secondMomentMeasure (ν : Measure ℤ) : Measure ℝ :=
  (ν.map (fun z : ℤ => |(z : ℝ)|)).withDensity (fun x => ENNReal.ofReal (x ^ 2))

instance secondMomentMeasure_locallyFinite (ν : Measure ℤ) [IsProbabilityMeasure ν] :
    IsLocallyFiniteMeasure (secondMomentMeasure ν) :=
  IsLocallyFiniteMeasure.withDensity_ofReal (by fun_prop)

theorem secondMomentMeasure_cumulative (ν : Measure ℤ) (x : ℝ) :
    KaramataTransforms.cumulative (secondMomentMeasure ν) x = truncSecondMoment ν x := by
  rw [KaramataTransforms.cumulative, secondMomentMeasure,
    withDensity_real_apply _ measurableSet_Icc,
    ← integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun y : ℝ => sq_nonneg y)
      (by fun_prop), setIntegral_map measurableSet_Icc (by fun_prop) (by fun_prop)]
  have hset : (fun z : ℤ => |(z : ℝ)|) ⁻¹' Icc 0 x =
      {z : ℤ | |(z : ℝ)| ≤ x} := by
    ext z
    simp
  rw [hset]
  simp only [sq_abs, truncSecondMoment]

/-- The truncated second moment is regularly varying with index `2 - θ`, in the
positive-function convention required by Laplace--Karamata. -/
theorem truncatedMoment_regularlyVarying {ν : Measure ℤ} [IsProbabilityMeasure ν]
    (hstep : ν {z : ℤ | z < -1} = 0) {θ : ℝ} (hθ1 : 1 < θ) (hθ2 : θ < 2)
    (hT : IsRegVaryAtTop (fun x : ℝ => ν.real {z : ℤ | x < (z : ℝ)}) (-θ)) :
    KaramataTransforms.RegularlyVarying (truncSecondMoment ν) (2 - θ) := by
  let T : ℝ → ℝ := fun x => ν.real {z : ℤ | x < (z : ℝ)}
  have hTp := (regularlyVarying_of_nonneg (fun _ => measureReal_nonneg) hT).1
  have hbase : KaramataTransforms.RegularlyVarying (fun x : ℝ => x ^ 2 * T x) (2 - θ) := by
    refine ⟨?_, fun c hc => ?_⟩
    · filter_upwards [eventually_gt_atTop (0 : ℝ), hTp] with x hx ht
      exact mul_pos (sq_pos_of_pos hx) ht
    · have h := (hT c hc).const_mul (c ^ 2)
      have heq : c ^ 2 * c ^ (-θ) = c ^ (2 - θ) := by
        rw [← Real.rpow_two, ← Real.rpow_add hc, sub_eq_add_neg]
      rw [heq] at h
      apply h.congr'
      filter_upwards [eventually_gt_atTop (0 : ℝ), hTp] with x hx ht
      dsimp only [T]
      rw [mul_pow]
      field_simp
  exact hbase.of_ratio (by positivity : 0 < θ / (2 - θ))
    (truncSecondMoment_div_tendsto ν hstep hθ1 hθ2 hT)

private theorem sq_mul_exp_neg_le {s y : ℝ} (hs : 0 < s) (hy : 0 ≤ y) :
    y ^ 2 * Real.exp (-s * y) ≤ 2 / s ^ 2 := by
  have h := Real.pow_div_factorial_le_exp (s * y) (mul_nonneg hs.le hy) 2
  norm_num only [Nat.factorial, Nat.cast_ofNat, Nat.cast_one, mul_one] at h
  have hmul := mul_le_mul_of_nonneg_right h (Real.exp_nonneg (-s * y))
  have heq : Real.exp (s * y) * Real.exp (-s * y) = 1 := by
    rw [← Real.exp_add]
    simp
  rw [heq] at hmul
  apply (le_div_iff₀ (sq_pos_of_pos hs)).2
  nlinarith

/-- The weighted measure has a finite Laplace transform at every positive argument,
even when the unweighted law has infinite second moment. -/
theorem secondMomentMeasure_laplace_integrable (ν : Measure ℤ) [IsProbabilityMeasure ν]
    {s : ℝ} (hs : 0 < s) :
    IntegrableOn (fun y => Real.exp (-s * y)) (Ici 0) (secondMomentMeasure ν) := by
  apply Integrable.integrableOn
  rw [secondMomentMeasure, integrable_withDensity_iff_integrable_smul'
    (by fun_prop) (by simp)]
  simp only [ENNReal.toReal_ofReal (sq_nonneg _), smul_eq_mul]
  apply (integrable_map_measure (by fun_prop) (by fun_prop)).2
  refine Integrable.of_bound (by fun_prop) (2 / s ^ 2) ?_
  exact Eventually.of_forall fun z => by
    dsimp only [Function.comp_def]
    rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (Real.exp_nonneg _))]
    exact sq_mul_exp_neg_le hs (abs_nonneg _)

/-- The transform of the square-weighted law is the exponentially damped second
moment of the absolute step. -/
theorem secondMomentMeasure_laplace (ν : Measure ℤ) (s : ℝ) :
    KaramataTransforms.laplace (secondMomentMeasure ν) s =
      ∫ z, (z : ℝ) ^ 2 * Real.exp (-s * |(z : ℝ)|) ∂ν := by
  rw [KaramataTransforms.laplace, secondMomentMeasure,
    setIntegral_withDensity_eq_setIntegral_toReal_smul (by fun_prop) (by simp)
      _ measurableSet_Ici]
  simp only [ENNReal.toReal_ofReal (sq_nonneg _), smul_eq_mul]
  rw [setIntegral_map measurableSet_Ici (by fun_prop) (by fun_prop)]
  have hset : (fun z : ℤ => |(z : ℝ)|) ⁻¹' Ici 0 = univ := by
    ext z
    simp
  rw [hset, setIntegral_univ]
  simp only [sq_abs]

/-- An Abelian second-moment expansion, obtained directly from the proved
Laplace--Karamata provider. This is integrated twice below to obtain the
one-step Laplace remainder. -/
theorem dampedSecondMoment_div_tail_tendsto (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (hstep : ν {z : ℤ | z < -1} = 0) {θ : ℝ} (hθ1 : 1 < θ) (hθ2 : θ < 2)
    (hT : IsRegVaryAtTop (fun x : ℝ => ν.real {z : ℤ | x < (z : ℝ)}) (-θ)) :
    Tendsto (fun x : ℝ =>
      (∫ z, (z : ℝ) ^ 2 * Real.exp (-(1 / x) * |(z : ℝ)|) ∂ν) /
        (x ^ 2 * ν.real {z : ℤ | x < (z : ℝ)})) atTop
      (𝓝 (θ * Real.Gamma (2 - θ))) := by
  have hU : KaramataTransforms.RegularlyVarying
      (KaramataTransforms.cumulative (secondMomentMeasure ν)) (2 - θ) := by
    have heq : KaramataTransforms.cumulative (secondMomentMeasure ν) =
        truncSecondMoment ν := funext (secondMomentMeasure_cumulative ν)
    rw [heq]
    exact truncatedMoment_regularlyVarying hstep hθ1 hθ2 hT
  have h := KaramataTransforms.laplace_abelian_ratio (secondMomentMeasure ν)
    (by linarith : 0 ≤ 2 - θ) (by linarith : 2 - θ < 1)
    (fun _ hs => secondMomentMeasure_laplace_integrable ν hs) hU
  simp only [secondMomentMeasure_cumulative, secondMomentMeasure_laplace] at h
  have hprod := h.mul (truncSecondMoment_div_tendsto ν hstep hθ1 hθ2 hT)
  have hG := Real.Gamma_add_one (s := 2 - θ) (by linarith)
  have hc : Real.Gamma (1 + (2 - θ)) * (θ / (2 - θ)) =
      θ * Real.Gamma (2 - θ) := by
    rw [show 1 + (2 - θ) = (2 - θ) + 1 by ring, hG]
    field_simp
  rw [hc] at hprod
  apply hprod.congr'
  filter_upwards [(truncatedMoment_regularlyVarying hstep hθ1 hθ2 hT).1]
    with x hx
  rw [div_mul_div_cancel₀ hx.ne']

private theorem monotone_dyadic_upper {G : ℝ → ℝ} (hmono : Monotone G)
    {A β : ℝ} (hA : 0 < A) (hβ : 0 ≤ β)
    (hstep : ∀ y, A ≤ y → G (2 * y) ≤ (2 : ℝ) ^ β * G y)
    {x t : ℝ} (hx : A ≤ x) (hGx : 0 < G x) (ht : 0 < t) (ht1 : t ≤ 1) :
    G (x / t) / G x ≤ (2 : ℝ) ^ β * t ^ (-β) := by
  have hx0 := hA.trans_le hx
  have hiter : ∀ n : ℕ, G ((2 : ℝ) ^ n * x) ≤ ((2 : ℝ) ^ β) ^ n * G x := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hy : A ≤ (2 : ℝ) ^ n * x := hx.trans
        (le_mul_of_one_le_left hx0.le (one_le_pow₀ (by norm_num)))
      calc
        G ((2 : ℝ) ^ (n + 1) * x) = G (2 * ((2 : ℝ) ^ n * x)) := by
          congr 1; ring
        _ ≤ (2 : ℝ) ^ β * G ((2 : ℝ) ^ n * x) := hstep _ hy
        _ ≤ (2 : ℝ) ^ β * (((2 : ℝ) ^ β) ^ n * G x) :=
          mul_le_mul_of_nonneg_left ih (by positivity)
        _ = ((2 : ℝ) ^ β) ^ (n + 1) * G x := by ring
  obtain ⟨n, hn, hn'⟩ := exists_nat_pow_near
    (show 1 ≤ t⁻¹ from (one_le_inv₀ ht).2 ht1) (by norm_num : (1 : ℝ) < 2)
  have harg : x / t ≤ (2 : ℝ) ^ (n + 1) * x := by
    rw [div_eq_mul_inv, mul_comm x]
    exact mul_le_mul_of_nonneg_right hn'.le hx0.le
  have hpoweq : ((2 : ℝ) ^ β) ^ n = ((2 : ℝ) ^ n) ^ β := by
    rw [← Real.rpow_natCast ((2 : ℝ) ^ β) n,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
      ← Real.rpow_natCast (2 : ℝ) n,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), mul_comm]
  have hpow : ((2 : ℝ) ^ β) ^ n ≤ t ^ (-β) := by
    rw [hpoweq, Real.rpow_neg ht.le, ← Real.inv_rpow ht.le]
    exact Real.rpow_le_rpow (by positivity) hn hβ
  apply (div_le_iff₀ hGx).2
  calc
    G (x / t) ≤ ((2 : ℝ) ^ β) ^ (n + 1) * G x := (hmono harg).trans (hiter _)
    _ ≤ ((2 : ℝ) ^ β * t ^ (-β)) * G x := by
      rw [pow_succ']
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hpow (by positivity)) hGx.le

/-- Integrating a reciprocal rescaling of a monotone regularly varying function.
The index restriction below one supplies an integrable power majorant at zero. -/
theorem reciprocal_integral_ratio_tendsto {G : ℝ → ℝ} {ρ : ℝ}
    (hnn : ∀ x, 0 ≤ G x) (hmono : Monotone G)
    (hG : KaramataTransforms.RegularlyVarying G ρ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) :
    Tendsto (fun x : ℝ => ∫ t in Ioo (0 : ℝ) 1,
      (1 - t) * (G (x / t) / G x)) atTop
      (𝓝 (∫ t in Ioo (0 : ℝ) 1, (1 - t) * t ^ (-ρ))) := by
  let β := (ρ + 1) / 2
  have hβ : 0 ≤ β := by dsimp [β]; linarith
  have hρβ : ρ < β := by dsimp [β]; linarith
  have hβ1 : β < 1 := by dsimp [β]; linarith
  have hlt : (2 : ℝ) ^ ρ < (2 : ℝ) ^ β :=
    Real.rpow_lt_rpow_of_exponent_lt (by norm_num) hρβ
  obtain ⟨A₀, hA₀⟩ := eventually_atTop.1
    ((hG.2 2 (by norm_num)).eventually (gt_mem_nhds hlt) |>.and hG.1)
  let A := max A₀ 1
  have hA : 0 < A := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hstep : ∀ y, A ≤ y → G (2 * y) ≤ (2 : ℝ) ^ β * G y := by
    intro y hy
    obtain ⟨hr, hp⟩ := hA₀ y ((le_max_left _ _).trans hy)
    exact ((div_lt_iff₀ hp).1 hr).le
  have hbound : ∀ᶠ x in atTop, ∀ t ∈ Ioo (0 : ℝ) 1,
      ‖(1 - t) * (G (x / t) / G x)‖ ≤ (2 : ℝ) ^ β * t ^ (-β) := by
    filter_upwards [eventually_ge_atTop A, hG.1] with x hx hGx t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by linarith [ht.2])
      (div_nonneg (hnn _) hGx.le))]
    calc
      _ ≤ G (x / t) / G x := mul_le_of_le_one_left
        (div_nonneg (hnn _) hGx.le) (by linarith [ht.1])
      _ ≤ _ := monotone_dyadic_upper hmono hA hβ hstep hx hGx ht.1 ht.2.le
  apply tendsto_integral_filter_of_dominated_convergence
    (μ := volume.restrict (Ioo (0 : ℝ) 1)) (fun t => (2 : ℝ) ^ β * t ^ (-β))
  · exact Eventually.of_forall fun x =>
      ((measurable_const.sub measurable_id).mul
        ((hmono.measurable.comp (measurable_const.div measurable_id)).div_const
          (G x))).aestronglyMeasurable
  · exact hbound.mono fun x hx => (ae_restrict_mem measurableSet_Ioo).mono fun t ht => hx t ht
  · exact ((intervalIntegral.integrableOn_Ioo_rpow_iff zero_lt_one).2
      (by linarith : -1 < -β)).const_mul _
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    have h := (hG.2 (1 / t) (one_div_pos.2 ht.1)).const_mul (1 - t)
    have heq : (1 / t) ^ ρ = t ^ (-ρ) := by
      rw [one_div, Real.inv_rpow ht.1.le, Real.rpow_neg ht.1.le]
    rw [heq] at h
    simpa only [one_div_mul_eq_div] using h

private theorem power_kernel_integral {ρ : ℝ} (hρ : ρ < 1) :
    (∫ t in Ioo (0 : ℝ) 1, (1 - t) * t ^ (-ρ)) =
      1 / ((1 - ρ) * (2 - ρ)) := by
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one]
  have h₁ : IntervalIntegrable (fun t : ℝ => t ^ (-ρ)) volume 0 1 :=
    intervalIntegral.intervalIntegrable_rpow' (by linarith)
  have h₂ : IntervalIntegrable (fun t : ℝ => t ^ (1 - ρ)) volume 0 1 :=
    intervalIntegral.intervalIntegrable_rpow' (by linarith)
  have heq : (∫ t in (0 : ℝ)..1, (1 - t) * t ^ (-ρ)) =
      ∫ t in (0 : ℝ)..1, t ^ (-ρ) - t ^ (1 - ρ) := by
    rw [intervalIntegral.integral_of_le zero_le_one,
      intervalIntegral.integral_of_le zero_le_one]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro t ht
    have ht0 : 0 < t := ht.1
    dsimp only
    rw [show 1 - ρ = 1 + -ρ by ring, Real.rpow_add ht0, Real.rpow_one]
    ring
  rw [heq, intervalIntegral.integral_sub h₁ h₂,
    integral_rpow (Or.inl (by linarith : -1 < -ρ)),
    integral_rpow (Or.inl (by linarith : -1 < 1 - ρ))]
  rw [Real.zero_rpow (by linarith : -ρ + 1 ≠ 0),
    Real.zero_rpow (by linarith : 1 - ρ + 1 ≠ 0)]
  simp only [Real.one_rpow, sub_zero]
  rw [show -ρ + 1 = 1 - ρ by ring, show 1 - ρ + 1 = 2 - ρ by ring]
  have h₃ : 1 - ρ ≠ 0 := by linarith
  have h₄ : 2 - ρ ≠ 0 := by linarith
  field_simp [h₃, h₄]
  ring

/-- The explicit constant in the twice-integrated reciprocal rescaling. -/
theorem reciprocal_integral_ratio_limit {G : ℝ → ℝ} {ρ : ℝ}
    (hnn : ∀ x, 0 ≤ G x) (hmono : Monotone G)
    (hG : KaramataTransforms.RegularlyVarying G ρ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) :
    Tendsto (fun x : ℝ => ∫ t in Ioo (0 : ℝ) 1,
      (1 - t) * (G (x / t) / G x)) atTop
      (𝓝 (1 / ((1 - ρ) * (2 - ρ)))) := by
  simpa only [power_kernel_integral hρ1] using
    reciprocal_integral_ratio_tendsto hnn hmono hG hρ0 hρ1

/-- Exact scalar Taylor integral, before taking the step-law expectation. -/
theorem exp_remainder_integral {s : ℝ} (hs : s ≠ 0) (y : ℝ) :
    (∫ t in Ioo (0 : ℝ) 1, (1 - t) * (y ^ 2 * Real.exp (-s * t * y))) =
      (Real.exp (-s * y) - 1 + s * y) / s ^ 2 := by
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one]
  let P : ℝ → ℝ := fun t => (s * y * (t - 1) + 1) * Real.exp (-s * t * y) / s ^ 2
  have hd : ∀ t : ℝ, HasDerivAt P ((1 - t) * (y ^ 2 * Real.exp (-s * t * y))) t := by
    intro t
    have h₁ := (((hasDerivAt_id t).sub_const 1).const_mul (s * y)).add_const 1
    have h₂ := ((((hasDerivAt_id t).const_mul (-s)).mul_const y).exp)
    convert (h₁.mul h₂).div_const (s ^ 2) using 1 <;> dsimp [P]
    all_goals field_simp
    all_goals ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t)
    (Continuous.intervalIntegrable (by fun_prop) 0 1)]
  dsimp [P]
  simp only [sub_self, mul_zero, zero_mul, zero_add, mul_one, Real.exp_zero]
  ring

/-- Fubini's formula for the exponential remainder of the absolute step. Finite
first moment suffices; the second moment need not be finite. -/
theorem absolute_remainder_eq_integrated_laplace {ν : Measure ℤ} [IsProbabilityMeasure ν]
    (hint : Integrable (fun z : ℤ => (z : ℝ)) ν) {s : ℝ} (hs : 0 < s) :
    (∫ z, (Real.exp (-s * |(z : ℝ)|) - 1 + s * |(z : ℝ)|) ∂ν) / s ^ 2 =
      ∫ t in Ioo (0 : ℝ) 1,
        (1 - t) * KaramataTransforms.laplace (secondMomentMeasure ν) (s * t) := by
  let μ : Measure ℝ := volume.restrict (Ioo 0 1)
  let k : ℤ × ℝ → ℝ := fun p =>
    (1 - p.2) * (|(p.1 : ℝ)| ^ 2 * Real.exp (-s * p.2 * |(p.1 : ℝ)|))
  have hexp : Integrable (fun z : ℤ => Real.exp (-s * |(z : ℝ)|)) ν := by
    refine Integrable.of_bound (by fun_prop) 1 (Eventually.of_forall fun z => ?_)
    rw [Real.norm_of_nonneg (Real.exp_nonneg _)]
    exact Real.exp_le_one_iff.2 (by nlinarith [abs_nonneg (z : ℝ)])
  have hR := ((hexp.sub (integrable_const 1)).add (hint.abs.const_mul s)).div_const (s ^ 2)
  have hki : Integrable k (ν.prod μ) := by
    apply (integrable_prod_iff (by fun_prop : AEStronglyMeasurable k (ν.prod μ))).2
    constructor
    · exact Eventually.of_forall fun z =>
        (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).1
          (Continuous.intervalIntegrable (by fun_prop) 0 1)
    · apply hR.congr
      exact Eventually.of_forall fun z => by
        have heq : (∫ t, ‖k (z, t)‖ ∂μ) = ∫ t, k (z, t) ∂μ := by
          apply integral_congr_ae
          filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
          dsimp [k]
          rw [abs_of_nonneg (mul_nonneg (by linarith [ht.2])
            (mul_nonneg (sq_nonneg _) (Real.exp_nonneg _))) ]
        dsimp only [Pi.add_apply, Pi.sub_apply]
        rw [heq]
        exact (exp_remainder_integral hs.ne' |(z : ℝ)|).symm
  have hswap := integral_integral_swap (f := fun z t => k (z, t)) hki
  have hleft : (∫ z, ∫ t, k (z, t) ∂μ ∂ν) =
      (∫ z, Real.exp (-s * |(z : ℝ)|) - 1 + s * |(z : ℝ)| ∂ν) / s ^ 2 := by
    rw [← integral_div]
    exact integral_congr_ae (Eventually.of_forall fun z => by
      simpa only [k, μ] using exp_remainder_integral hs.ne' |(z : ℝ)|)
  rw [hleft] at hswap
  exact hswap.trans (integral_congr_ae (Eventually.of_forall fun t => by
    dsimp only
    rw [secondMomentMeasure_laplace, ← integral_const_mul]
    apply integral_congr_ae
    exact Eventually.of_forall fun z => by
      dsimp [k]
      rw [sq_abs]
      ring_nf))

/-- The integrated Laplace kernel has the universal beta-integral constant. -/
theorem integrated_laplace_ratio_limit (M : Measure ℝ) [IsLocallyFiniteMeasure M]
    {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hfinite : ∀ s : ℝ, 0 < s → IntegrableOn (fun y => Real.exp (-s * y)) (Ici 0) M)
    (hU : KaramataTransforms.RegularlyVarying (KaramataTransforms.cumulative M) ρ) :
    Tendsto (fun x : ℝ => ∫ t in Ioo (0 : ℝ) 1,
      (1 - t) * (KaramataTransforms.laplace M (t / x) /
        KaramataTransforms.laplace M (1 / x))) atTop
      (𝓝 (1 / ((1 - ρ) * (2 - ρ)))) := by
  let G : ℝ → ℝ := fun x => KaramataTransforms.laplace M (1 / max x 1)
  have hmax : ∀ x : ℝ, 0 < max x 1 := fun x => lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hnn : ∀ x, 0 ≤ G x := fun x => integral_nonneg (fun _ => Real.exp_nonneg _)
  have hmono : Monotone G := by
    intro a b hab
    apply setIntegral_mono_on (hfinite _ (by positivity)) (hfinite _ (by positivity))
      measurableSet_Ici
    intro y hy
    apply Real.exp_le_exp.2
    have hinv := one_div_le_one_div_of_le (hmax a) (max_le_max hab le_rfl)
    have hy0 : 0 ≤ y := hy
    nlinarith
  have hratio := KaramataTransforms.laplace_abelian_ratio M hρ0 hρ1 hfinite hU
  have hG : KaramataTransforms.RegularlyVarying G ρ := by
    apply hU.of_ratio (show 0 < Real.Gamma (1 + ρ) from
      Real.Gamma_pos_of_pos (by linarith))
    apply hratio.congr'
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    dsimp [G]
    rw [max_eq_left hx]
  apply (reciprocal_integral_ratio_limit hnn hmono hG hρ0 hρ1).congr'
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  apply setIntegral_congr_fun measurableSet_Ioo
  intro t ht
  have hxt : 1 ≤ x / t := (le_div_iff₀ ht.1).2 (by simpa using ht.2.le.trans hx)
  dsimp [G]
  rw [max_eq_left hx, max_eq_left hxt, one_div_div]

/-- The Abelian expansion for the exponential remainder of the absolute step. -/
theorem absolute_remainder_div_tail_tendsto (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (hstep : ν {z : ℤ | z < -1} = 0)
    (hint : Integrable (fun z : ℤ => (z : ℝ)) ν)
    {θ : ℝ} (hθ1 : 1 < θ) (hθ2 : θ < 2)
    (hT : IsRegVaryAtTop (fun x : ℝ => ν.real {z : ℤ | x < (z : ℝ)}) (-θ)) :
    Tendsto (fun x : ℝ =>
      (∫ z, Real.exp (-(1 / x) * |(z : ℝ)|) - 1 + (1 / x) * |(z : ℝ)| ∂ν) /
        ν.real {z : ℤ | x < (z : ℝ)}) atTop (𝓝 (-Real.Gamma (1 - θ))) := by
  let M := secondMomentMeasure ν
  have hU : KaramataTransforms.RegularlyVarying (KaramataTransforms.cumulative M) (2 - θ) := by
    have heq : KaramataTransforms.cumulative M = truncSecondMoment ν :=
      funext (secondMomentMeasure_cumulative ν)
    rw [heq]
    exact truncatedMoment_regularlyVarying hstep hθ1 hθ2 hT
  have hfinite := fun s hs => secondMomentMeasure_laplace_integrable ν (s := s) hs
  have hi := integrated_laplace_ratio_limit M (by linarith : 0 ≤ 2 - θ)
    (by linarith : 2 - θ < 1) hfinite hU
  have hd : Tendsto (fun x : ℝ => KaramataTransforms.laplace M (1 / x) /
      (x ^ 2 * ν.real {z : ℤ | x < (z : ℝ)})) atTop
      (𝓝 (θ * Real.Gamma (2 - θ))) := by
    simpa only [M, secondMomentMeasure_laplace] using
      dampedSecondMoment_div_tail_tendsto ν hstep hθ1 hθ2 hT
  have hprod := hi.mul hd
  have hc : 1 / ((1 - (2 - θ)) * (2 - (2 - θ))) * (θ * Real.Gamma (2 - θ)) =
      -Real.Gamma (1 - θ) := by
    rw [(negGamma_eq hθ1 hθ2).2.1]
    have ht : θ ≠ 0 := by linarith
    have ht1 : θ - 1 ≠ 0 := by linarith
    rw [show 1 - (2 - θ) = θ - 1 by ring, show 2 - (2 - θ) = θ by ring]
    field_simp
  rw [hc] at hprod
  have hF := (KaramataTransforms.laplace_abelian M (by linarith : 0 ≤ 2 - θ)
    (by linarith : 2 - θ < 1) hfinite hU).1
  apply hprod.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ), hF] with x hx hFx
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
  have ht := ((tailData_of_regVary ν (by linarith) hT).pos x).ne'
  generalize ν.real {z : ℤ | x < (z : ℝ)} = t at ht ⊢
  field_simp

private theorem absolute_remainder_integrable {ν : Measure ℤ} [IsProbabilityMeasure ν]
    (hint : Integrable (fun z : ℤ => (z : ℝ)) ν) {s : ℝ} (hs : 0 ≤ s) :
    Integrable (fun z : ℤ => Real.exp (-s * |(z : ℝ)|) - 1 + s * |(z : ℝ)|) ν := by
  have he : Integrable (fun z : ℤ => Real.exp (-s * |(z : ℝ)|)) ν := by
    refine Integrable.of_bound (by fun_prop) 1 (Eventually.of_forall fun z => ?_)
    rw [Real.norm_of_nonneg (Real.exp_nonneg _)]
    exact Real.exp_le_one_iff.2 (by nlinarith [mul_nonneg hs (abs_nonneg (z : ℝ))])
  exact (he.sub (integrable_const 1)).add (hint.abs.const_mul s)

/-- The bounded negative support contributes just the atom at `-1`. -/
theorem uncentered_remainder_eq_absolute {ν : Measure ℤ} [IsProbabilityMeasure ν]
    (hstep : ν {z : ℤ | z < -1} = 0)
    (hint : Integrable (fun z : ℤ => (z : ℝ)) ν) {s : ℝ} (hs : 0 ≤ s) :
    (∫ z, Real.exp (-s * (z : ℝ)) ∂ν) - 1 + s * mean ν =
      (∫ z, Real.exp (-s * |(z : ℝ)|) - 1 + s * |(z : ℝ)| ∂ν) +
        ν.real {(-1 : ℤ)} * (Real.exp s - Real.exp (-s) - 2 * s) := by
  have hraw : (∫ z, Real.exp (-s * (z : ℝ)) ∂ν) - 1 + s * mean ν =
      ∫ z, Real.exp (-s * (z : ℝ)) - 1 + s * (z : ℝ) ∂ν := by
    rw [integral_add (f := fun z : ℤ => Real.exp (-s * (z : ℝ)) - 1)
      (g := fun z : ℤ => s * (z : ℝ))
      ((uncenteredLaplace_integrable hstep hs).sub (integrable_const 1))
      (hint.const_mul s), integral_sub (uncenteredLaplace_integrable hstep hs)
      (integrable_const 1), integral_const_mul]
    simp [mean]
  rw [hraw]
  have heq : (fun z : ℤ => Real.exp (-s * (z : ℝ)) - 1 + s * (z : ℝ)) =ᵐ[ν]
      fun z => (Real.exp (-s * |(z : ℝ)|) - 1 + s * |(z : ℝ)|) +
        ({(-1 : ℤ)} : Set ℤ).indicator (fun _ => Real.exp s - Real.exp (-s) - 2 * s) z := by
    filter_upwards [ae_lower_bound hstep] with z hz
    by_cases he : z = -1
    · subst z
      simp
      ring
    · have hz0 : (0 : ℝ) ≤ z := by
        have hz1 : (-1 : ℤ) ≤ z := by exact_mod_cast hz
        have : (0 : ℤ) ≤ z := by omega
        exact_mod_cast this
      simp [abs_of_nonneg hz0, he]
  rw [integral_congr_ae heq,
    integral_add (absolute_remainder_integrable hint hs)
      ((integrable_const _).indicator (measurableSet_singleton _)),
    integral_indicator_const _ (measurableSet_singleton _), smul_eq_mul]

/-- The uncentered Laplace remainder has the heavy-tail Gamma constant. -/
theorem uncentered_remainder_div_tail_tendsto (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (hstep : ν {z : ℤ | z < -1} = 0)
    (hint : Integrable (fun z : ℤ => (z : ℝ)) ν)
    {θ : ℝ} (hθ1 : 1 < θ) (hθ2 : θ < 2)
    (hT : IsRegVaryAtTop (fun x : ℝ => ν.real {z : ℤ | x < (z : ℝ)}) (-θ)) :
    Tendsto (fun x : ℝ =>
      ((∫ z, Real.exp (-(1 / x) * (z : ℝ)) ∂ν) - 1 + mean ν / x) /
        ν.real {z : ℤ | x < (z : ℝ)}) atTop (𝓝 (-Real.Gamma (1 - θ))) := by
  let T : ℝ → ℝ := fun x => ν.real {z : ℤ | x < (z : ℝ)}
  have hnn : ∀ x, 0 ≤ T x := fun _ => measureReal_nonneg
  have hmeas : Measurable T :=
    (show Antitone T from fun a b hab => measureReal_mono
      (fun _ hz => lt_of_le_of_lt hab hz)).measurable
  have he₁ := exp_remainder_div_tail_tendsto_zero hnn hmeas hT hθ2 1
  have he₂ := exp_remainder_div_tail_tendsto_zero hnn hmeas hT hθ2 (-1)
  have he := (he₁.sub he₂).const_mul (ν.real {(-1 : ℤ)})
  simp only [sub_zero, mul_zero] at he
  have hlim := (absolute_remainder_div_tail_tendsto ν hstep hint hθ1 hθ2 hT).add he
  simp only [add_zero] at hlim
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  have hraw := uncentered_remainder_eq_absolute hstep hint (one_div_pos.2 hx).le
  have hmean : mean ν / x = (1 / x) * mean ν := by ring
  rw [hmean, hraw, add_div]
  dsimp only [T]
  simp only [one_div, neg_div]
  ring

/-- D1: the centered Laplace expansion, in reciprocal tail-ratio form. -/
theorem centeredLaplace_tail_ratio (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (hstep : ν {z : ℤ | z < -1} = 0)
    (hint : Integrable (fun z : ℤ => (z : ℝ)) ν)
    {θ : ℝ} (hθ1 : 1 < θ) (hθ2 : θ < 2)
    (hT : IsRegVaryAtTop (fun x : ℝ => ν.real {z : ℤ | x < (z : ℝ)}) (-θ)) :
    Tendsto (fun x : ℝ => (centeredLaplace ν (1 / x) - 1) /
      ν.real {z : ℤ | x < (z : ℝ)}) atTop (𝓝 (-Real.Gamma (1 - θ))) :=
  centered_ratio_of_uncentered hθ2 hT
    (uncentered_remainder_div_tail_tendsto ν hstep hint hθ1 hθ2 hT)

/-- D1 expressed at the positive side of zero. -/
theorem centeredLaplace_expansion (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (hstep : ν {z : ℤ | z < -1} = 0)
    (hint : Integrable (fun z : ℤ => (z : ℝ)) ν)
    {θ : ℝ} (hθ1 : 1 < θ) (hθ2 : θ < 2)
    (hT : IsRegVaryAtTop (fun x : ℝ => ν.real {z : ℤ | x < (z : ℝ)}) (-θ)) :
    Tendsto (fun s : ℝ => (centeredLaplace ν s - 1) /
      ν.real {z : ℤ | 1 / s < (z : ℝ)}) (𝓝[>] 0) (𝓝 (-Real.Gamma (1 - θ))) := by
  simpa only [Function.comp_def, one_div, inv_inv] using
    (centeredLaplace_tail_ratio ν hstep hint hθ1 hθ2 hT).comp tendsto_inv_nhdsGT_zero

/-- The usual asymptotic-equivalence form of the centered expansion. -/
theorem centeredLaplace_sub_one_isEquivalent (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (hstep : ν {z : ℤ | z < -1} = 0)
    (hint : Integrable (fun z : ℤ => (z : ℝ)) ν)
    {θ : ℝ} (hθ1 : 1 < θ) (hθ2 : θ < 2)
    (hT : IsRegVaryAtTop (fun x : ℝ => ν.real {z : ℤ | x < (z : ℝ)}) (-θ)) :
    Asymptotics.IsEquivalent (𝓝[>] (0 : ℝ))
      (fun s => centeredLaplace ν s - 1)
      (fun s => (-Real.Gamma (1 - θ)) * ν.real {z : ℤ | 1 / s < (z : ℝ)}) := by
  have h := (centeredLaplace_expansion ν hstep hint hθ1 hθ2 hT).div_const
    (-Real.Gamma (1 - θ))
  rw [div_self (negGamma_eq hθ1 hθ2).2.2.ne'] at h
  apply Asymptotics.isEquivalent_of_tendsto_one
  apply h.congr
  intro s
  dsimp only [Pi.div_apply]
  rw [div_div, mul_comm]

/-- A tail index below two rules out a finite second moment. -/
theorem not_integrable_sq_of_tail {ν : Measure ℤ} [IsProbabilityMeasure ν]
    (hstep : ν {z : ℤ | z < -1} = 0)
    {θ : ℝ} (hθ1 : 1 < θ) (hθ2 : θ < 2)
    (hT : IsRegVaryAtTop (fun x : ℝ => ν.real {z : ℤ | x < (z : ℝ)}) (-θ)) :
    ¬ Integrable (fun z : ℤ => (z : ℝ) ^ 2) ν := by
  let T : ℝ → ℝ := fun x => ν.real {z : ℤ | x < (z : ℝ)}
  have hanti : Antitone T := fun a b hab => measureReal_mono
    (fun _ hz => lt_of_le_of_lt hab hz)
  have hD : Tendsto (fun x : ℝ => x ^ 2 * T x) atTop atTop := by
    simpa only [Real.rpow_two] using rpow_mul_tail_tendsto_atTop
      (fun _ => measureReal_nonneg) hanti.measurable hT hθ2
  have hK' := (truncSecondMoment_div_tendsto ν hstep hθ1 hθ2 hT).pos_mul_atTop
    (by positivity : 0 < θ / (2 - θ)) hD
  have hK : Tendsto (truncSecondMoment ν) atTop atTop := by
    apply hK'.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    have ht := (tailData_of_regVary ν (by linarith) hT).pos x
    exact div_mul_cancel₀ _ (mul_ne_zero (pow_ne_zero _ hx.ne') ht.ne')
  intro hsq
  obtain ⟨x, hx⟩ := (hK.eventually_gt_atTop (∫ z, (z : ℝ) ^ 2 ∂ν)).exists
  have hle : truncSecondMoment ν x ≤ ∫ z, (z : ℝ) ^ 2 ∂ν :=
    setIntegral_le_integral hsq (Eventually.of_forall fun z => sq_nonneg (z : ℝ))
  exact (not_lt_of_ge hle) hx

/-- On a regularly varying tail of index below two, `norming` selects the tail branch. -/
theorem norming_eq_tailNorming {ν : Measure ℤ} [IsProbabilityMeasure ν]
    (hstep : ν {z : ℤ | z < -1} = 0)
    {θ : ℝ} (hθ1 : 1 < θ) (hθ2 : θ < 2)
    (hT : IsRegVaryAtTop (fun x : ℝ => ν.real {z : ℤ | x < (z : ℝ)}) (-θ)) :
    norming ν θ = tailNorming ν θ := by
  classical
  funext n
  simp only [norming, ite_eq_right (not_integrable_sq_of_tail hstep hθ1 hθ2 hT),
    ite_eq_left hθ2, tailNorming]

section Canonical

variable {ν : Measure ℤ} [IsProbabilityMeasure ν] {θ : ℝ}

theorem tailNorming_tendsto_atTop (hθ1 : 1 < θ) (hθ2 : θ < 2)
    (hT : IsRegVaryAtTop (fun x : ℝ => ν.real {z : ℤ | x < (z : ℝ)}) (-θ)) :
    Tendsto (tailNorming ν θ) atTop atTop := by
  exact (tailQuantile_tendsto_atTop (by linarith) hT).const_mul_atTop
    (Real.rpow_pos_of_pos (negGamma_eq hθ1 hθ2).2.2 _)

/-- The corrected Gamma constant cancels the limiting tail intensity. -/
theorem canonical_mul_tail_tendsto (hθ1 : 1 < θ) (hθ2 : θ < 2)
    (hT : IsRegVaryAtTop (fun x : ℝ => ν.real {z : ℤ | x < (z : ℝ)}) (-θ))
    {lam : ℝ} (hlam : 0 < lam) :
    Tendsto (fun n : ℕ => (n : ℝ) * (-Real.Gamma (1 - θ)) *
      ν.real {z : ℤ | tailNorming ν θ n / lam < (z : ℝ)}) atTop (𝓝 (lam ^ θ)) := by
  let C := -Real.Gamma (1 - θ)
  let c := C ^ (1 / θ) / lam
  have hC : 0 < C := (negGamma_eq hθ1 hθ2).2.2
  have hc : 0 < c := div_pos (Real.rpow_pos_of_pos hC _) hlam
  have hq := tailQuantile_tendsto_atTop (by linarith) hT
  have hratio := (hT c hc).comp hq
  have hprod := ((tailQuantile_mul_tail (by linarith) hT).mul hratio).mul_const C
  have hconst : 1 * c ^ (-θ) * C = lam ^ θ := by
    dsimp [c]
    rw [Real.div_rpow (by positivity : 0 ≤ C ^ (1 / θ)) hlam.le,
      ← Real.rpow_mul hC.le]
    have hexp : 1 / θ * -θ = -1 := by field_simp
    rw [hexp, Real.rpow_neg_one, Real.rpow_neg hlam.le]
    field_simp
  rw [hconst] at hprod
  apply hprod.congr
  intro n
  have hne := ((tailData_of_regVary ν (by linarith) hT).pos (tailQuantile ν n)).ne'
  dsimp only [Function.comp_def]
  have heq : c * tailQuantile ν n = tailNorming ν θ n / lam := by
    dsimp [c, tailNorming, C]
    ring
  rw [heq]
  dsimp only [C]
  field_simp

/-- Transfer an asymptotic formula on the reciprocal tail scale to the canonical
sequence. This is a general transfer lemma; it does not assert the Abelian expansion. -/
theorem canonical_limit_of_tail_ratio {F : ℝ → ℝ}
    (hθ1 : 1 < θ) (hθ2 : θ < 2)
    (hT : IsRegVaryAtTop (fun x : ℝ => ν.real {z : ℤ | x < (z : ℝ)}) (-θ))
    (hF : Tendsto (fun x : ℝ => (F (1 / x) - 1) /
      ν.real {z : ℤ | x < (z : ℝ)}) atTop (𝓝 (-Real.Gamma (1 - θ))))
    {lam : ℝ} (hlam : 0 < lam) :
    Tendsto (fun n : ℕ => (n : ℝ) * (F (lam / tailNorming ν θ n) - 1))
      atTop (𝓝 (lam ^ θ)) := by
  have hC := (negGamma_eq hθ1 hθ2).2.2
  have ha : Tendsto (fun n => tailNorming ν θ n / lam) atTop atTop :=
    (tailNorming_tendsto_atTop hθ1 hθ2 hT).atTop_div_const hlam
  have hratio := (hF.comp ha).div_const (-Real.Gamma (1 - θ))
  rw [div_self hC.ne'] at hratio
  have hprod := (canonical_mul_tail_tendsto hθ1 hθ2 hT hlam).mul hratio
  rw [mul_one] at hprod
  apply hprod.congr
  intro n
  have ht := ((tailData_of_regVary ν (by linarith) hT).pos
    (tailNorming ν θ n / lam)).ne'
  dsimp only [Function.comp_def]
  rw [one_div_div]
  generalize ν.real {z : ℤ | tailNorming ν θ n / lam < (z : ℝ)} = t at ht ⊢
  have hG : Real.Gamma (1 - θ) ≠ 0 := neg_ne_zero.mp hC.ne'
  field_simp [ht, hG]

/-- The one-step limit needed by D2, with the corrected canonical tail norming. -/
theorem canonical_centeredLaplace_limit
    (hstep : ν {z : ℤ | z < -1} = 0)
    (hint : Integrable (fun z : ℤ => (z : ℝ)) ν)
    (hθ1 : 1 < θ) (hθ2 : θ < 2)
    (hT : IsRegVaryAtTop (fun x : ℝ => ν.real {z : ℤ | x < (z : ℝ)}) (-θ))
    {lam : ℝ} (hlam : 0 < lam) :
    Tendsto (fun n : ℕ => (n : ℝ) *
      (centeredLaplace ν (lam / tailNorming ν θ n) - 1)) atTop (𝓝 (lam ^ θ)) :=
  canonical_limit_of_tail_ratio hθ1 hθ2 hT
    (centeredLaplace_tail_ratio ν hstep hint hθ1 hθ2 hT) hlam

/-- The same D2 input using the public canonical norming from `Defs`. -/
theorem norming_centeredLaplace_limit
    (hstep : ν {z : ℤ | z < -1} = 0)
    (hint : Integrable (fun z : ℤ => (z : ℝ)) ν)
    (hθ1 : 1 < θ) (hθ2 : θ < 2)
    (hT : IsRegVaryAtTop (fun x : ℝ => ν.real {z : ℤ | x < (z : ℝ)}) (-θ))
    {lam : ℝ} (hlam : 0 < lam) :
    Tendsto (fun n : ℕ => (n : ℝ) *
      (centeredLaplace ν (lam / norming ν θ n) - 1)) atTop (𝓝 (lam ^ θ)) := by
  rw [norming_eq_tailNorming hstep hθ1 hθ2 hT]
  exact canonical_centeredLaplace_limit hstep hint hθ1 hθ2 hT hlam

end Canonical

end BGW.StableTrees.Attraction.LaplaceExpansion
