/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module
public import BGW.StableTrees.Scalar.DensityLaw
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.MeasureTheory.Group.Convolution
public import Mathlib.MeasureTheory.Measure.WithDensity
import BGW.StableTrees.StableLawWitness
import Mathlib.MeasureTheory.Measure.Decomposition.Lebesgue
import Mathlib.Analysis.Convolution
import Mathlib.Analysis.LConvolution

/-! # The unconditional stable law and its convolution semigroup

This module packages the scalar stable density as a probability measure for every
`1 < θ ≤ 2`, identifies its Laplace and characteristic transforms, and proves the time
semigroup for the corresponding laws and densities.

References: V. M. Zolotarev, *One-dimensional Stable Distributions*, 1986; K. Sato, *Lévy
Processes and Infinitely Divisible Distributions*, 1999, §14; W. Feller, *An Introduction to
Probability Theory and Its Applications*, vol. II, ch. XVII.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Complex Set
open scoped NNReal Convolution MeasureTheory

namespace BGW.StableTrees

/-- For every index `1 < θ ≤ 2`, some critical offspring law lies in the normalized θ-stable
domain of attraction (C15.1; witness by an explicit regularly varying tail). -/
theorem exists_stableDomain {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∃ (μ : PMF ℕ) (a : ℕ → ℝ), StableDomain μ θ a :=
  existsStableDomain_pareto hθ

/-- The stable density is nonnegative, unconditionally on `1 < θ ≤ 2` (C15.1). -/
theorem stableDensity_nonneg {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (x : ℝ) :
    0 ≤ Scalar.stableDensity θ x := by
  obtain ⟨μ, a, h⟩ := exists_stableDomain hθ
  exact Scalar.stableDensity_nonneg h x

/-- The stable density integrates to one (C15.1). -/
theorem integral_stableDensity {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∫ x, Scalar.stableDensity θ x = 1 := by
  obtain ⟨μ, a, h⟩ := exists_stableDomain hθ
  exact Scalar.integral_stableDensity h

/-- The spectrally positive θ-stable law, normalized by `E[exp(-λ X)] = exp(λ^θ)`, for
`1 < θ ≤ 2`; the Dirac mass at `0` outside this range (a junk value). -/
noncomputable def stableLaw (θ : ℝ) : ProbabilityMeasure ℝ :=
  if hθ : 1 < θ ∧ θ ≤ 2 then
    ⟨volume.withDensity (fun x => ENNReal.ofReal (Scalar.stableDensity θ x)), by
      obtain ⟨μ, a, h⟩ := exists_stableDomain hθ
      have hi : Integrable (Scalar.stableDensity θ) := Scalar.integrable_stableDensity h
      refine ⟨?_⟩
      rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
      rw [← ofReal_integral_eq_lintegral_ofReal hi
        (Eventually.of_forall (stableDensity_nonneg hθ))]
      rw [integral_stableDensity hθ]
      norm_num⟩
  else ⟨Measure.dirac 0, inferInstance⟩

/-- The stable law has density `Scalar.stableDensity θ` (C15.1). -/
theorem stableLaw_eq_withDensity {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    (stableLaw θ : Measure ℝ) =
      volume.withDensity (fun x => ENNReal.ofReal (Scalar.stableDensity θ x)) := by
  simp [stableLaw, hθ]

/-- Laplace transform of the stable law (C15.1). -/
theorem integral_exp_neg_mul_stableLaw {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {lam : ℝ} (hlam : 0 ≤ lam) :
    ∫ x, Real.exp (-lam * x) ∂(stableLaw θ : Measure ℝ) = Real.exp (lam ^ θ) := by
  rcases eq_or_lt_of_le hlam with hzero | hpos
  · subst lam
    have hθ0 : θ ≠ 0 := ne_of_gt (by linarith [hθ.1])
    simp [hθ0]
  · obtain ⟨μ, a, h⟩ := exists_stableDomain hθ
    obtain ⟨ν, hν, hL, -⟩ := h.converges
    have hEq : ν = (stableLaw θ : Measure ℝ) := by
      rw [stableLaw_eq_withDensity hθ]
      exact Scalar.limitLaw_eq_withDensity h hL
    rw [← hEq]
    exact hL lam hpos

/-- Characteristic function of the stable law: `exp ((-i t)^θ)` (C15.1). -/
theorem charFun_stableLaw {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (t : ℝ) :
    charFun (stableLaw θ : Measure ℝ) t = Scalar.stableCF θ t := by
  rw [stableLaw_eq_withDensity hθ]
  obtain ⟨μ, a, h⟩ := exists_stableDomain hθ
  exact Scalar.charFun_withDensity_stableDensity h t

/-- The stable law is the only probability measure with this Laplace transform (C15.1). -/
theorem eq_stableLaw_of_laplace {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {ν : Measure ℝ}
    [IsProbabilityMeasure ν]
    (hL : ∀ lam : ℝ, 0 < lam → ∫ y, Real.exp (-lam * y) ∂ν = Real.exp (lam ^ θ)) :
    ν = (stableLaw θ : Measure ℝ) := by
  exact Scalar.limitLaw_unique (by linarith [hθ.1]) hL
    (fun lam hlam => integral_exp_neg_mul_stableLaw hθ (le_of_lt hlam))

/-- At `θ = 2` the stable law is the centered Gaussian of variance `2` (C15; §1.1). -/
theorem stableLaw_two : (stableLaw 2 : Measure ℝ) = gaussianReal 0 2 := by
  symm
  apply eq_stableLaw_of_laplace (by norm_num) (ν := gaussianReal 0 2)
  intro lam hlam
  have hm := congrFun (mgf_id_gaussianReal (μ := 0) (v := (2 : ℝ≥0))) (-lam)
  simpa [mgf] using hm

private theorem cpow_pos_scale {α c : ℝ} (hα : α ≠ 0) (hc : 0 < c) (z : ℂ) :
    ((c : ℂ) * z) ^ (α : ℂ) = ((c ^ α : ℝ) : ℂ) * z ^ (α : ℂ) := by
  by_cases hz : z = 0
  · subst z
    simp [Complex.zero_cpow (Complex.ofReal_ne_zero.mpr hα)]
  · have hcn : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc.ne'
    have hcz : (c : ℂ) * z ≠ 0 := mul_ne_zero hcn hz
    rw [Complex.cpow_def_of_ne_zero hcz, Complex.log_ofReal_mul hc hz,
      add_mul, Complex.exp_add]
    have hcPowExp : Complex.exp ((Real.log c : ℂ) * (α : ℂ)) =
        ((c ^ α : ℝ) : ℂ) := by
      calc
        Complex.exp ((Real.log c : ℂ) * (α : ℂ)) =
            Complex.exp ((Real.log c * α : ℝ) : ℂ) := by congr 1; push_cast; ring
        _ = ((Real.exp (Real.log c * α) : ℝ) : ℂ) := by rw [← Complex.ofReal_exp]
        _ = ((c ^ α : ℝ) : ℂ) := by congr 1; rw [Real.rpow_def_of_pos hc]
    rw [hcPowExp, ← Complex.cpow_def_of_ne_zero hz]

private theorem stableCF_scale {α c : ℝ} (hα : α ≠ 0) (hc : 0 < c) (t : ℝ) :
    Scalar.stableCF α (c * t) =
      Complex.exp ((c ^ α : ℝ) * (-(t * I)) ^ (α : ℂ)) := by
  unfold Scalar.stableCF
  rw [show -((c * t : ℝ) * I) = (c : ℂ) * (-(t * I)) by push_cast; ring,
    cpow_pos_scale hα hc]

/-- The density of the stable law at time `t > 0`: `t^{-1/θ} p₁(t^{-1/θ} x)` (C15.4). -/
noncomputable def stableDensityAt (θ t x : ℝ) : ℝ :=
  t ^ (-1 / θ) * Scalar.stableDensity θ (t ^ (-1 / θ) * x)

/-- The stable law at time `t > 0`, image of `stableLaw θ` under `x ↦ t^{1/θ} x` (C15.4). -/
noncomputable def stableLawAt (θ t : ℝ) : ProbabilityMeasure ℝ :=
  (stableLaw θ).map (fun x => t ^ (1 / θ) * x)

private theorem rpow_scale {θ t : ℝ} (hθ : θ ≠ 0) (ht : 0 < t) :
    (t ^ (1 / θ)) ^ θ = t := by
  calc
    (t ^ (1 / θ)) ^ θ = t ^ ((1 / θ) * θ) :=
      (Real.rpow_mul (le_of_lt ht) (1 / θ) θ).symm
    _ = t := by rw [show (1 / θ) * θ = 1 by field_simp [hθ], Real.rpow_one]

private theorem charFun_stableLawAt_aux {θ t : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (ht : 0 < t)
    (u : ℝ) :
    charFun (stableLawAt θ t : Measure ℝ) u =
      Complex.exp ((t : ℂ) * (-(u * I)) ^ (θ : ℂ)) := by
  have hθ0 : θ ≠ 0 := ne_of_gt (by linarith [hθ.1])
  calc
    charFun (stableLawAt θ t : Measure ℝ) u =
        charFun (stableLaw θ : Measure ℝ) (t ^ (1 / θ) * u) := by
      simpa [stableLawAt] using
        (charFun_map_mul_comp (μ := (stableLaw θ : Measure ℝ)) (f := id)
          (by fun_prop) (t ^ (1 / θ)) u)
    _ = Scalar.stableCF θ (t ^ (1 / θ) * u) := charFun_stableLaw hθ _
    _ = Complex.exp ((t : ℂ) * (-(u * I)) ^ (θ : ℂ)) := by
      rw [stableCF_scale hθ0 (Real.rpow_pos_of_pos ht _) u, rpow_scale hθ0 ht]

private theorem stableDensityAt_nonneg {θ t x : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (ht : 0 < t) :
    0 ≤ stableDensityAt θ t x := by
  rw [stableDensityAt]
  exact mul_nonneg (Real.rpow_nonneg (le_of_lt ht) _)
    (stableDensity_nonneg hθ _)

private theorem stableDensityAt_continuous {θ t : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    Continuous (stableDensityAt θ t) := by
  change Continuous (fun x => t ^ (-1 / θ) *
    Scalar.stableDensity θ (t ^ (-1 / θ) * x))
  exact continuous_const.mul ((Scalar.continuous_stableDensity hθ).comp
    (continuous_const.mul continuous_id))

private theorem stableDensityAt_integrable {θ t : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (ht : 0 < t) :
    Integrable (stableDensityAt θ t) := by
  obtain ⟨μ, a, h⟩ := exists_stableDomain hθ
  let c : ℝ := t ^ (-1 / θ)
  have hcpos : 0 < c := Real.rpow_pos_of_pos ht _
  have hcomp : Integrable (fun x => Scalar.stableDensity θ (c * x)) :=
    (integrable_comp_mul_left_iff _ hcpos.ne').2 (Scalar.integrable_stableDensity h)
  have hfun : stableDensityAt θ t = fun x =>
      c * Scalar.stableDensity θ (c * x) := by
    funext x
    simp [stableDensityAt, c, mul_comm]
  rw [hfun]
  exact hcomp.const_mul c

private theorem stableDensityAt_integral {θ t : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (ht : 0 < t) :
    ∫ x, stableDensityAt θ t x = 1 := by
  obtain ⟨μ, a, h⟩ := exists_stableDomain hθ
  let c : ℝ := t ^ (-1 / θ)
  have hcpos : 0 < c := Real.rpow_pos_of_pos ht _
  have hc : c ≠ 0 := hcpos.ne'
  calc
    ∫ x, stableDensityAt θ t x = c * ∫ x, Scalar.stableDensity θ (c * x) := by
      simp [stableDensityAt, c, integral_const_mul]
    _ = c * (|c⁻¹| * ∫ y, Scalar.stableDensity θ y) := by
      simpa [smul_eq_mul] using congrArg (fun z : ℝ => c * z)
        (Measure.integral_comp_mul_left (fun y : ℝ => Scalar.stableDensity θ y) c)
    _ = 1 := by
      rw [integral_stableDensity hθ, abs_of_pos (inv_pos.mpr hcpos)]
      field_simp [hc]

private theorem stableDensityAt_isProbabilityMeasure {θ t : ℝ}
    (hθ : 1 < θ ∧ θ ≤ 2) (ht : 0 < t) :
    IsProbabilityMeasure
      (volume.withDensity (fun x => ENNReal.ofReal (stableDensityAt θ t x))) := by
  refine ⟨?_⟩
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  rw [← ofReal_integral_eq_lintegral_ofReal (stableDensityAt_integrable hθ ht)
    (Eventually.of_forall fun x => stableDensityAt_nonneg (x := x) hθ ht)]
  rw [stableDensityAt_integral hθ ht]
  norm_num

private theorem charFun_withDensity_stableDensityAt {θ t : ℝ}
    (hθ : 1 < θ ∧ θ ≤ 2) (ht : 0 < t) (u : ℝ) :
    charFun (volume.withDensity (fun x => ENNReal.ofReal (stableDensityAt θ t x))) u =
      Scalar.stableCF θ ((t ^ (-1 / θ))⁻¹ * u) := by
  obtain ⟨μ, a, h⟩ := exists_stableDomain hθ
  let c : ℝ := t ^ (-1 / θ)
  have hcpos : 0 < c := Real.rpow_pos_of_pos ht _
  have hnn : ∀ x, 0 ≤ Scalar.stableDensity θ x := stableDensity_nonneg hθ
  have hcont := Scalar.continuous_stableDensity hθ
  have hbase : ∫ y, Scalar.stableDensity θ y * Complex.exp (((c⁻¹ * u) * y) * I) =
      Scalar.stableCF θ (c⁻¹ * u) := by
    have h := Scalar.charFun_withDensity_stableDensity h (c⁻¹ * u)
    rw [charFun_apply_real] at h
    rw [integral_withDensity_eq_integral_toReal_smul
      (f := fun y => ENNReal.ofReal (Scalar.stableDensity θ y))
      (ENNReal.measurable_ofReal.comp hcont.measurable)
      (Eventually.of_forall fun y => ENNReal.ofReal_lt_top)] at h
    simpa [ENNReal.toReal_ofReal (hnn _), smul_eq_mul, mul_comm, mul_left_comm,
      mul_assoc] using h
  have hchange :
      ∫ x, c * Scalar.stableDensity θ (c * x) * Complex.exp ((u * x) * I) =
        ∫ y, Scalar.stableDensity θ y * Complex.exp (((c⁻¹ * u) * y) * I) := by
    calc
      _ = ∫ x, c * (Scalar.stableDensity θ (c * x) * Complex.exp ((u * x) * I)) := by
        congr 1
        funext x
        ring
      _ = c * ∫ x, Scalar.stableDensity θ (c * x) * Complex.exp ((u * x) * I) := by
        rw [integral_const_mul]
      _ = c * (|c⁻¹| * ∫ y, Scalar.stableDensity θ y *
          Complex.exp (((c⁻¹ * u) * y) * I)) := by
        congr 1
        calc
          _ = ∫ x, (fun y => Scalar.stableDensity θ y *
              Complex.exp (((c⁻¹ * u) * y) * I)) (c * x) := by
            congr 1
            funext x
            congr 1
            push_cast
            field_simp [hcpos.ne']
          _ = _ := by
            simpa [smul_eq_mul] using Measure.integral_comp_mul_left
              (fun y : ℝ => Scalar.stableDensity θ y *
                Complex.exp (((c⁻¹ * u) * y) * I)) c
      _ = _ := by
        rw [abs_of_pos (inv_pos.mpr hcpos)]
        rw [← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ hcpos.ne']
        simp
  rw [charFun_apply_real,
    integral_withDensity_eq_integral_toReal_smul
      (f := fun x => ENNReal.ofReal (stableDensityAt θ t x))
      (ENNReal.measurable_ofReal.comp (stableDensityAt_continuous hθ).measurable)
      (Eventually.of_forall fun x => ENNReal.ofReal_lt_top)]
  calc
    _ = ∫ x, stableDensityAt θ t x * Complex.exp ((u * x) * I) := by
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by
        simp [Complex.real_smul,
          ENNReal.toReal_ofReal (stableDensityAt_nonneg (x := x) hθ ht)]
    _ = _ := by
      have hfun : stableDensityAt θ t = fun x =>
          c * Scalar.stableDensity θ (c * x) := by
        funext x
        simp [stableDensityAt, c, mul_comm]
      simpa [hfun] using hchange.trans (by simpa [c] using hbase)

/-- `stableLawAt θ t` has density `stableDensityAt θ t` (C15.4). -/
theorem stableLawAt_eq_withDensity {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {t : ℝ} (ht : 0 < t) :
    (stableLawAt θ t : Measure ℝ) =
      volume.withDensity (fun x => ENNReal.ofReal (stableDensityAt θ t x)) := by
  have : IsProbabilityMeasure
      (volume.withDensity (fun x => ENNReal.ofReal (stableDensityAt θ t x))) :=
    stableDensityAt_isProbabilityMeasure hθ ht
  apply Measure.ext_of_charFun
  funext u
  rw [charFun_stableLawAt_aux hθ ht u, charFun_withDensity_stableDensityAt hθ ht u]
  have hc : t ^ (-1 / θ) * t ^ (1 / θ) = 1 := by
    calc
      t ^ (-1 / θ) * t ^ (1 / θ) = t ^ ((-1 / θ) + (1 / θ)) :=
        (Real.rpow_add ht _ _).symm
      _ = 1 := by rw [show (-1 / θ) + (1 / θ) = 0 by ring, Real.rpow_zero]
  have hinv : (t ^ (-1 / θ))⁻¹ = t ^ (1 / θ) := by
    calc
      (t ^ (-1 / θ))⁻¹ = (t ^ (-1 / θ))⁻¹ *
          (t ^ (-1 / θ) * t ^ (1 / θ)) := by rw [hc]; ring
      _ = t ^ (1 / θ) := by field_simp [ne_of_gt (Real.rpow_pos_of_pos ht _)]
  rw [hinv]
  have hθ0 : θ ≠ 0 := ne_of_gt (by linarith [hθ.1])
  have hcf : Scalar.stableCF θ (t ^ (1 / θ) * u) =
      Complex.exp ((t : ℂ) * (-(u * I)) ^ (θ : ℂ)) := by
    rw [stableCF_scale hθ0 (Real.rpow_pos_of_pos ht _) u, rpow_scale hθ0 ht]
  exact hcf.symm

/-- Laplace transform at time `t`: `E[exp(-λ X_t)] = exp(t λ^θ)` (C15.4). -/
theorem integral_exp_neg_mul_stableLawAt {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {t : ℝ} (ht : 0 < t)
    {lam : ℝ} (hlam : 0 ≤ lam) :
    ∫ x, Real.exp (-lam * x) ∂(stableLawAt θ t : Measure ℝ) = Real.exp (t * lam ^ θ) := by
  rcases eq_or_lt_of_le hlam with hzero | hpos
  · subst lam
    have hθ0 : θ ≠ 0 := ne_of_gt (by linarith [hθ.1])
    simp [hθ0]
  · have hθ0 : θ ≠ 0 := ne_of_gt (by linarith [hθ.1])
    have ha : 0 < t ^ (1 / θ) := Real.rpow_pos_of_pos ht _
    have hpow : (t ^ (1 / θ)) ^ θ = t := rpow_scale hθ0 ht
    calc
      ∫ x, Real.exp (-lam * x) ∂(stableLawAt θ t : Measure ℝ) =
          ∫ x, Real.exp (-(lam * t ^ (1 / θ)) * x) ∂(stableLaw θ : Measure ℝ) := by
        change ∫ x, Real.exp (-lam * x) ∂
            Measure.map (fun x => t ^ (1 / θ) * x) (stableLaw θ : Measure ℝ) = _
        rw [integral_map (by fun_prop) (by fun_prop)]
        congr 1
        funext x
        ring_nf
      _ = Real.exp ((lam * t ^ (1 / θ)) ^ θ) :=
        integral_exp_neg_mul_stableLaw hθ (le_of_lt (mul_pos hpos ha))
      _ = Real.exp (t * lam ^ θ) := by
        congr 1
        rw [Real.mul_rpow hpos.le ha.le, hpow]
        ring

/-- Semigroup property of the stable laws (C15.4). -/
theorem stableLawAt_conv {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    (stableLawAt θ s : Measure ℝ) ∗ (stableLawAt θ t : Measure ℝ) =
      (stableLawAt θ (s + t) : Measure ℝ) := by
  apply Measure.ext_of_charFun
  funext u
  rw [charFun_conv, charFun_stableLawAt_aux hθ hs u,
    charFun_stableLawAt_aux hθ ht u,
    charFun_stableLawAt_aux hθ (add_pos hs ht) u, ← Complex.exp_add]
  congr 1
  calc
    (s : ℂ) * (-(u * I)) ^ (θ : ℂ) + (t : ℂ) * (-(u * I)) ^ (θ : ℂ) =
        (-(u * I)) ^ (θ : ℂ) * (s : ℂ) + (-(u * I)) ^ (θ : ℂ) * (t : ℂ) := by
      rw [mul_comm (s : ℂ), mul_comm (t : ℂ)]
    _ = (-(u * I)) ^ (θ : ℂ) * ((s : ℂ) + (t : ℂ)) := by rw [mul_add]
    _ = (-(u * I)) ^ (θ : ℂ) * ((s + t : ℝ) : ℂ) := by rw [Complex.ofReal_add]
    _ = ((s + t : ℝ) : ℂ) * (-(u * I)) ^ (θ : ℂ) := by rw [mul_comm]

/-- Semigroup property of the stable densities: `p_s * p_t = p_{s+t}` (C15.4). -/
theorem integral_stableDensityAt_mul {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {s t : ℝ} (hs : 0 < s)
    (ht : 0 < t) (x : ℝ) :
    ∫ y, stableDensityAt θ s y * stableDensityAt θ t (x - y) = stableDensityAt θ (s + t) x := by
  let fs : ℝ → ENNReal := fun y => ENNReal.ofReal (stableDensityAt θ s y)
  let ft : ℝ → ENNReal := fun y => ENNReal.ofReal (stableDensityAt θ t y)
  let fr : ℝ → ENNReal := fun y => ENNReal.ofReal (stableDensityAt θ (s + t) y)
  let fconv : ℝ → ENNReal := MeasureTheory.lconvolution fs ft volume
  let convVal : ℝ → ℝ := fun z =>
    ∫ y, stableDensityAt θ s y * stableDensityAt θ t (z - y)
  have hfs : Measurable fs :=
    ENNReal.measurable_ofReal.comp (stableDensityAt_continuous hθ).measurable
  have hft : Measurable ft :=
    ENNReal.measurable_ofReal.comp (stableDensityAt_continuous hθ).measurable
  have hfr : Measurable fr :=
    ENNReal.measurable_ofReal.comp (stableDensityAt_continuous hθ).measurable
  have hmeas : volume.withDensity fs ∗ volume.withDensity ft = volume.withDensity fr := by
    change (volume.withDensity (fun y => ENNReal.ofReal (stableDensityAt θ s y))) ∗
        (volume.withDensity (fun y => ENNReal.ofReal (stableDensityAt θ t y))) =
      volume.withDensity (fun y => ENNReal.ofReal (stableDensityAt θ (s + t) y))
    rw [← stableLawAt_eq_withDensity hθ hs, ← stableLawAt_eq_withDensity hθ ht,
      ← stableLawAt_eq_withDensity hθ (add_pos hs ht)]
    exact stableLawAt_conv hθ hs ht
  have hmeasure : volume.withDensity fconv = volume.withDensity fr := by
    rw [← MeasureTheory.conv_withDensity_eq_lconvolution hfs hft]
    exact hmeas
  have hfconv : AEMeasurable fconv volume := by
    exact MeasureTheory.aemeasurable_lconvolution hfs.aemeasurable hft.aemeasurable
  have hconv_ae : fconv =ᵐ[volume] fr := by
    have hderiv := congrArg (fun m : Measure ℝ => m.rnDeriv volume) hmeasure
    have hleft := Measure.rnDeriv_withDensity₀ volume hfconv
    have hright := Measure.rnDeriv_withDensity₀ volume hfr.aemeasurable
    filter_upwards [hleft, hright] with z hleft hright
    calc
      fconv z = (volume.withDensity fconv).rnDeriv volume z := hleft.symm
      _ = (volume.withDensity fr).rnDeriv volume z := congrFun hderiv z
      _ = fr z := hright
  have hconv_value (z : ℝ) : fconv z = ENNReal.ofReal (convVal z) := by
    have hfirst : Integrable (stableDensityAt θ s) := stableDensityAt_integrable hθ hs
    have hsecond_cont : Continuous (fun y => stableDensityAt θ t (z - y)) :=
      (stableDensityAt_continuous hθ).comp (continuous_const.sub continuous_id)
    obtain ⟨M, -, hM⟩ := Scalar.exists_stableDensity_le (α := θ)
    have hbound : ∀ y, ‖stableDensityAt θ t (z - y)‖ ≤ t ^ (-1 / θ) * M := by
      intro y
      rw [Real.norm_eq_abs, abs_of_nonneg (stableDensityAt_nonneg (x := z - y) hθ ht)]
      rw [stableDensityAt]
      exact mul_le_mul_of_nonneg_left (le_trans (le_abs_self _) (hM _))
        (Real.rpow_nonneg (le_of_lt ht) _)
    have hprod_integrable :
        Integrable (fun y => stableDensityAt θ s y * stableDensityAt θ t (z - y)) := by
      exact hfirst.mul_bdd hsecond_cont.aestronglyMeasurable
        (Eventually.of_forall hbound)
    have hprod_nonneg :
        ∀ y, 0 ≤ stableDensityAt θ s y * stableDensityAt θ t (z - y) := by
      intro y
      exact mul_nonneg (stableDensityAt_nonneg (x := y) hθ hs)
        (stableDensityAt_nonneg (x := z - y) hθ ht)
    change ∫⁻ y, fs y * ft (-y + z) =
      ENNReal.ofReal (∫ y, stableDensityAt θ s y * stableDensityAt θ t (z - y))
    rw [ofReal_integral_eq_lintegral_ofReal hprod_integrable
      (Eventually.of_forall hprod_nonneg)]
    apply lintegral_congr
    intro y
    simp only [fs, ft]
    rw [show -y + z = z - y by ring,
      ← ENNReal.ofReal_mul (stableDensityAt_nonneg (x := y) hθ hs)]
  have hconv_real : convVal =ᵐ[volume] stableDensityAt θ (s + t) := by
    filter_upwards [hconv_ae] with z hz
    have hreal := congrArg ENNReal.toReal hz
    rw [hconv_value z, ENNReal.toReal_ofReal
      (integral_nonneg_of_ae (Eventually.of_forall fun y => mul_nonneg
        (stableDensityAt_nonneg (x := y) hθ hs)
        (stableDensityAt_nonneg (x := z - y) hθ ht))),
      ENNReal.toReal_ofReal (stableDensityAt_nonneg (x := z) hθ (add_pos hs ht))] at hreal
    exact hreal
  let L : ℝ →L[ℝ] ℝ →L[ℝ] ℝ := ContinuousLinearMap.mul ℝ ℝ
  have hbound_range : BddAbove (Set.range fun y => ‖stableDensityAt θ t y‖) := by
    obtain ⟨M, -, hM⟩ := Scalar.exists_stableDensity_le (α := θ)
    refine ⟨t ^ (-1 / θ) * M, ?_⟩
    rintro _ ⟨y, rfl⟩
    change ‖stableDensityAt θ t y‖ ≤ t ^ (-1 / θ) * M
    rw [Real.norm_eq_abs, abs_of_nonneg (stableDensityAt_nonneg (x := y) hθ ht),
      stableDensityAt]
    exact mul_le_mul_of_nonneg_left (le_trans (le_abs_self _) (hM _))
      (Real.rpow_nonneg (le_of_lt ht) _)
  have hconv_cont : Continuous convVal := by
    have h := hbound_range.continuous_convolution_right_of_integrable L
      (stableDensityAt_integrable hθ hs) (stableDensityAt_continuous hθ)
    change Continuous (fun z => (stableDensityAt θ s ⋆[L, volume] stableDensityAt θ t) z)
    exact h
  have hpoint := (Continuous.ae_eq_iff_eq volume hconv_cont
    (stableDensityAt_continuous hθ)).mp hconv_real
  exact congrFun hpoint x

end BGW.StableTrees
