/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.Attraction.Defs

/-!
# Centered walk transforms and convergence of types

The A1 transform identities are followed by A2 convergence of types for arbitrary
**eventually positive** normings. No monotonicity, step lower bound, or moment
assumption is needed for A2. In particular all results apply with centering `mean ν`.

The scale-ratio proof adapts `BGW.StableTrees.Scalar.Normalization` and the private
proof in `BGW.StableTrees.Attraction.LocalLimit`: compactify the ratio as `u / (1 + u)`,
then identify subsequential limits using moving characteristic functions and the
strictly negative stable modulus exponent. The two-norming version also allows a
change of time with positive limiting time ratio.

Divergence follows separately: attraction supplies a frequency with one-step CF
modulus strictly below one. On a convergent bounded subsequence of scales, moving
frequencies turn the normalized CF moduli into powers of that fixed modulus. These
powers tend to zero, contradicting the strictly positive stable CF modulus.
Ported from `BGWLeaves/StableAnalysis/TransformConvergence.lean` of the author's arXiv:1110.2163v4
formalization (local snapshot of 6 November 2026).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Complex Filter Set
open scoped Topology

namespace BGW.StableTrees.Attraction.TransformConvergence

open BGW.StableTrees.Attraction
open BGW.StableTrees.Scalar

private instance intWalk_isProbabilityMeasure (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (n : ℕ) : IsProbabilityMeasure (intWalk ν n) := by
  induction n with
  | zero => simp only [intWalk]; infer_instance
  | succ n ih => simpa only [intWalk] using
      (inferInstance : IsProbabilityMeasure ((intWalk ν n) ∗ ν))

/-- The characteristic function of one integer-valued step, viewed as a real random variable. -/
noncomputable def stepCharFun (ν : Measure ℤ) (t : ℝ) : ℂ :=
  charFun (ν.map (fun z : ℤ => (z : ℝ))) t

/-- The uncentered Laplace transform of one step. -/
noncomputable def stepLaplace (ν : Measure ℤ) (s : ℝ) : ℝ :=
  ∫ z, Real.exp (-s * (z : ℝ)) ∂ν

/-- The characteristic function of the `n`-fold convolution of an integer-valued step law. -/
noncomputable def intWalkCharFun (ν : Measure ℤ) (n : ℕ) (t : ℝ) : ℂ :=
  charFun ((intWalk ν n).map (fun z : ℤ => (z : ℝ))) t

private theorem map_intWalk_cast_succ (ν : Measure ℤ) (n : ℕ) :
    ((intWalk ν (n + 1)).map (fun z : ℤ => (z : ℝ))) =
      ((intWalk ν n).map (fun z : ℤ => (z : ℝ))) ∗
        (ν.map (fun z : ℤ => (z : ℝ))) := by
    simpa only [intWalk, Int.coe_castAddHom] using
    (Measure.map_conv_addMonoidHom (Int.castAddHom ℝ) (by fun_prop) :
      ((intWalk ν n ∗ ν).map (fun z : ℤ => (z : ℝ))) =
        ((intWalk ν n).map (fun z : ℤ => (z : ℝ))) ∗
          (ν.map (fun z : ℤ => (z : ℝ))))

theorem intWalkCharFun_eq_pow (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (n : ℕ) (t : ℝ) : intWalkCharFun ν n t = stepCharFun ν t ^ n := by
  induction n with
  | zero =>
      simp [intWalkCharFun, stepCharFun, intWalk]
  | succ n ih =>
      change charFun ((intWalk ν (n + 1)).map (fun z : ℤ => (z : ℝ))) t = _
      rw [map_intWalk_cast_succ, charFun_conv]
      change intWalkCharFun ν n t * stepCharFun ν t = _
      rw [ih, pow_succ]

private theorem cast_integrable_conv {μ ν : Measure ℤ} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν]
    (hμ : Integrable (fun z : ℤ => (z : ℝ)) μ)
    (hν : Integrable (fun z : ℤ => (z : ℝ)) ν) :
    Integrable (fun z : ℤ => (z : ℝ)) (μ ∗ ν) := by
  rw [Measure.conv]
  apply (integrable_map_measure (measurable_of_countable _).aestronglyMeasurable
    (measurable_of_countable _).aemeasurable).2
  have hprod : Integrable (fun p : ℤ × ℤ => ((p.1 + p.2 : ℤ) : ℝ)) (μ.prod ν) := by
    convert (hμ.comp_fst ν).add (hν.comp_snd μ) using 1
    ext p
    simp
  exact hprod

private theorem cast_integral_conv {μ ν : Measure ℤ} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν]
    (hμ : Integrable (fun z : ℤ => (z : ℝ)) μ)
    (hν : Integrable (fun z : ℤ => (z : ℝ)) ν) :
    (∫ z, (z : ℝ) ∂(μ ∗ ν)) = (∫ z, (z : ℝ) ∂μ) + (∫ z, (z : ℝ) ∂ν) := by
  have hconv := cast_integrable_conv hμ hν
  rw [Measure.conv, integral_map (by fun_prop) (by fun_prop)]
  simp_rw [Int.cast_add]
  rw [integral_add (hμ.comp_fst ν) (hν.comp_snd μ), integral_fun_fst, integral_fun_snd]
  simp

private theorem intWalk_integrable_cast (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (hν : Integrable (fun z : ℤ => (z : ℝ)) ν) (n : ℕ) :
    Integrable (fun z : ℤ => (z : ℝ)) (intWalk ν n) := by
  induction n with
  | zero => simpa [intWalk] using (integrable_dirac (a := 0) (by simp) :
      Integrable (fun z : ℤ => (z : ℝ)) (Measure.dirac 0))
  | succ n ih => simpa only [intWalk] using cast_integrable_conv ih hν

private theorem intWalk_integral_cast (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (hν : Integrable (fun z : ℤ => (z : ℝ)) ν) (n : ℕ) :
    (∫ z, (z : ℝ) ∂(intWalk ν n)) = (n : ℝ) * mean ν := by
  induction n with
  | zero => simp [intWalk, mean]
  | succ n ih =>
      rw [show intWalk ν (n + 1) = intWalk ν n ∗ ν by rfl,
        cast_integral_conv (intWalk_integrable_cast ν hν n) hν, ih, mean]
      push_cast
      ring

private theorem ae_step_lower_bound {ν : Measure ℤ} (hstep : ν {z : ℤ | z < -1} = 0) :
    ∀ᵐ z : ℤ ∂ν, (-1 : ℝ) ≤ (z : ℝ) := by
  rw [ae_iff]
  have hset : {z : ℤ | ¬ (-1 : ℝ) ≤ (z : ℝ)} = {z : ℤ | z < -1} := by
    ext z
    norm_cast
    simp
  rw [hset]
  exact hstep

private theorem stepLaplace_integrable {ν : Measure ℤ} [IsProbabilityMeasure ν]
    (hstep : ν {z : ℤ | z < -1} = 0) {s : ℝ} (hs : 0 ≤ s) :
    Integrable (fun z : ℤ => Real.exp (-s * (z : ℝ))) ν := by
  refine Integrable.of_bound (by fun_prop) (Real.exp s) ?_
  filter_upwards [ae_step_lower_bound hstep] with z hz
  rw [Real.norm_of_nonneg (Real.exp_nonneg _)]
  apply Real.exp_le_exp.mpr
  have := mul_nonneg hs (show 0 ≤ (z : ℝ) + 1 by linarith)
  nlinarith

private theorem exp_integrable_conv {μ ν : Measure ℤ} {s : ℝ}
    (hμ : Integrable (fun z : ℤ => Real.exp (-s * (z : ℝ))) μ)
    (hν : Integrable (fun z : ℤ => Real.exp (-s * (z : ℝ))) ν) :
    Integrable (fun z : ℤ => Real.exp (-s * (z : ℝ))) (μ ∗ ν) := by
  rw [Measure.conv]
  apply (integrable_map_measure (measurable_of_countable _).aestronglyMeasurable
    (measurable_of_countable _).aemeasurable).2
  have hprod := hμ.mul_prod hν
  convert hprod using 1
  ext p
  simp only [Function.comp_apply, Int.cast_add, mul_add, Real.exp_add]

private theorem exp_integral_conv {μ ν : Measure ℤ} {s : ℝ}
    (hμ : Integrable (fun z : ℤ => Real.exp (-s * (z : ℝ))) μ)
    (hν : Integrable (fun z : ℤ => Real.exp (-s * (z : ℝ))) ν) :
    (∫ z, Real.exp (-s * (z : ℝ)) ∂(μ ∗ ν)) =
      (∫ z, Real.exp (-s * (z : ℝ)) ∂μ) *
        (∫ z, Real.exp (-s * (z : ℝ)) ∂ν) := by
  have hconv := exp_integrable_conv hμ hν
  rw [Measure.conv, integral_map (measurable_of_countable _).aemeasurable
    (by fun_prop : AEStronglyMeasurable _ (Measure.map _ _))]
  calc
    (∫ p : ℤ × ℤ, Real.exp (-s * ((p.1 + p.2 : ℤ) : ℝ)) ∂(μ.prod ν)) =
        ∫ p, Real.exp (-s * (p.1 : ℝ)) * Real.exp (-s * (p.2 : ℝ)) ∂(μ.prod ν) := by
          apply integral_congr_ae
          filter_upwards [] with p
          rw [Int.cast_add, mul_add, Real.exp_add]
    _ = (∫ z, Real.exp (-s * (z : ℝ)) ∂μ) *
        (∫ z, Real.exp (-s * (z : ℝ)) ∂ν) := by
          rw [integral_prod_mul (fun z : ℤ => Real.exp (-s * (z : ℝ)))
            (fun z : ℤ => Real.exp (-s * (z : ℝ)))]

private theorem intWalk_exp_integrable (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (hstep : ν {z : ℤ | z < -1} = 0) {s : ℝ} (hs : 0 ≤ s) (n : ℕ) :
    Integrable (fun z : ℤ => Real.exp (-s * (z : ℝ))) (intWalk ν n) := by
  induction n with
  | zero =>
      simpa [intWalk] using (integrable_dirac (a := 0) (by simp) :
        Integrable (fun z : ℤ => Real.exp (-s * (z : ℝ))) (Measure.dirac 0))
  | succ n ih =>
      simpa only [intWalk] using
        (exp_integrable_conv (μ := intWalk ν n) (ν := ν) ih
          (stepLaplace_integrable hstep hs))

private theorem intWalk_exp_integral (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (hstep : ν {z : ℤ | z < -1} = 0) {s : ℝ} (hs : 0 ≤ s) (n : ℕ) :
    (∫ z, Real.exp (-s * (z : ℝ)) ∂(intWalk ν n)) = stepLaplace ν s ^ n := by
  induction n with
  | zero => simp [intWalk, stepLaplace]
  | succ n ih =>
      rw [show intWalk ν (n + 1) = intWalk ν n ∗ ν by rfl]
      rw [exp_integral_conv (μ := intWalk ν n) (ν := ν)
        (intWalk_exp_integrable ν hstep hs n) (stepLaplace_integrable hstep hs), ih]
      simp only [stepLaplace, pow_succ]

/-- The law of the centered walk divided by a positive scale.  It is written as two affine maps
so that the scale and centering contributions to the characteristic function are explicit. -/
noncomputable def centeredScaledWalk (ν : Measure ℤ) (m a : ℝ) (n : ℕ) : Measure ℝ :=
  (((intWalk ν n).map (fun z : ℤ => (z : ℝ) / a)).map
    (fun x : ℝ => x - (n : ℝ) * m / a))

instance centeredScaledWalk_isProbabilityMeasure (ν : Measure ℤ)
    [IsProbabilityMeasure ν] (m a : ℝ) (n : ℕ) :
    IsProbabilityMeasure (centeredScaledWalk ν m a n) := by
  unfold centeredScaledWalk
  infer_instance

theorem centeredScaledWalk_eq_map (ν : Measure ℤ) (m a : ℝ) (n : ℕ) :
    centeredScaledWalk ν m a n =
      (intWalk ν n).map (fun z : ℤ => ((z : ℝ) - n * m) / a) := by
  rw [centeredScaledWalk, Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1
  funext z
  simp only [Function.comp_apply, div_eq_mul_inv]
  ring

/-- Rescaling the same centered walk changes its law by the corresponding scalar map. -/
theorem centeredScaledWalk_change_scale (ν : Measure ℤ) (m a b : ℝ) (n : ℕ)
    (ha : a ≠ 0) (hb : b ≠ 0) :
    centeredScaledWalk ν m a n =
      (centeredScaledWalk ν m b n).map (fun x : ℝ => (b / a) * x) := by
  rw [centeredScaledWalk_eq_map, centeredScaledWalk_eq_map,
    Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1
  funext z
  simp only [Function.comp_apply]
  field_simp [ha, hb]

theorem centeredScaledWalk_charFun_change_scale (ν : Measure ℤ)
    (m a b : ℝ) (n : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) (t : ℝ) :
    charFun (centeredScaledWalk ν m a n) t =
      charFun (centeredScaledWalk ν m b n) (t * (b / a)) := by
  rw [centeredScaledWalk_change_scale ν m a b n ha hb, charFun_map_mul]
  congr 1
  ring

/-- The normalized walk regarded as a bundled probability measure. -/
noncomputable def centeredScaledWalkProb (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (m : ℝ) (a : ℕ → ℝ) (n : ℕ) : ProbabilityMeasure ℝ :=
  ⟨centeredScaledWalk ν m (a n) n,
    centeredScaledWalk_isProbabilityMeasure ν m (a n) n⟩

/-- Weak convergence in `IsStableAttracted` is exactly convergence of the bundled normalized
walk laws. -/
theorem _root_.BGW.StableTrees.Attraction.IsStableAttracted.tendsto_centeredScaledWalkProb
    {ν : Measure ℤ} [IsProbabilityMeasure ν] {θ m : ℝ} {a : ℕ → ℝ}
    (h : IsStableAttracted ν θ m a) :
    ∃ Q : ProbabilityMeasure ℝ,
      (∀ s : ℝ, 0 < s → ∫ x, Real.exp (-s * x) ∂(Q : Measure ℝ) = Real.exp (s ^ θ)) ∧
      Tendsto (fun n => centeredScaledWalkProb ν m a n) atTop (𝓝 Q) := by
  obtain ⟨X, hX, hL, hconv⟩ := h.converges
  let Q : ProbabilityMeasure ℝ := ⟨X, hX⟩
  refine ⟨Q, ?_, ?_⟩
  · exact hL
  · rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
    intro f
    simpa [Q, centeredScaledWalkProb, centeredScaledWalk_eq_map] using hconv f

/-- Weak convergence also controls characteristic functions at moving frequencies. -/
theorem
    _root_.BGW.StableTrees.Attraction.IsStableAttracted.tendsto_centeredScaledWalk_charFun_moving
    {ν : Measure ℤ} [IsProbabilityMeasure ν] {θ m : ℝ} {a : ℕ → ℝ}
    (h : IsStableAttracted ν θ m a)
    {s : ℕ → ℝ} {t : ℝ} (hs : Tendsto s atTop (𝓝 t)) :
    Tendsto (fun n => charFun (centeredScaledWalk ν m (a n) n) (s n)) atTop
      (𝓝 (stableCF θ t)) := by
  obtain ⟨Q, hL, hQ⟩ := h.tendsto_centeredScaledWalkProb
  have hc := tendsto_charFun_moving hQ hs
  rw [charFun_eq_stableCF (by linarith [h.alpha_mem.1] : 0 < θ) hL] at hc
  simpa [centeredScaledWalkProb] using hc

/-- Every nonnegative negative-exponential moment of the centered scaled walk is finite.  The
one-step lower bound makes the step Laplace integrand bounded almost everywhere. -/
theorem centeredScaledWalk_integrable_negExp (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (hstep : ν {z : ℤ | z < -1} = 0) (m a s : ℝ) (n : ℕ)
    (ha : 0 < a) (hs : 0 ≤ s) :
    Integrable (fun x : ℝ => Real.exp (-s * x)) (centeredScaledWalk ν m a n) := by
  rw [centeredScaledWalk_eq_map]
  apply (integrable_map_measure (by fun_prop) (measurable_of_countable _).aemeasurable).2
  have hraw := intWalk_exp_integrable ν hstep (div_nonneg hs ha.le) n
  have hpoint (z : ℤ) :
      Real.exp (-s * (((z : ℝ) - n * m) / a)) =
        Real.exp (s * n * m / a) * Real.exp (-(s / a) * (z : ℝ)) := by
    calc
      Real.exp (-s * (((z : ℝ) - n * m) / a)) =
          Real.exp (s * n * m / a + (-(s / a) * (z : ℝ))) := by
            congr 1
            field_simp
            ring
      _ = Real.exp (s * n * m / a) * Real.exp (-(s / a) * (z : ℝ)) := by
            rw [Real.exp_add]
  have hcomp : Integrable
      (fun z : ℤ => Real.exp (-s * (((z : ℝ) - n * m) / a))) (intWalk ν n) := by
    have hmul := (intWalk_exp_integrable ν hstep (div_nonneg hs ha.le) n).const_mul
      (Real.exp (s * n * m / a))
    exact hmul.congr (ae_of_all _ fun z => (hpoint z).symm)
  simpa only [Function.comp_def] using hcomp

/-- Laplace transform of the centered scaled walk.  Here `stepLaplace` is the uncentered
one-step transform, so the last exponential is the deterministic centering factor. -/
theorem centeredScaledWalk_laplace (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (hstep : ν {z : ℤ | z < -1} = 0) (m a s : ℝ) (n : ℕ)
    (ha : 0 < a) (hs : 0 ≤ s) :
    (∫ x, Real.exp (-s * x) ∂(centeredScaledWalk ν m a n)) =
      stepLaplace ν (s / a) ^ n * Real.exp (s * n * m / a) := by
  have hneg := centeredScaledWalk_integrable_negExp ν hstep m a s n ha hs
  have hraw := intWalk_exp_integrable ν hstep (div_nonneg hs ha.le) n
  have hpoint (z : ℤ) :
      Real.exp (-s * (((z : ℝ) - n * m) / a)) =
        Real.exp (s * n * m / a) * Real.exp (-(s / a) * (z : ℝ)) := by
    calc
      Real.exp (-s * (((z : ℝ) - n * m) / a)) =
          Real.exp (s * n * m / a + (-(s / a) * (z : ℝ))) := by
            congr 1
            field_simp
            ring
      _ = Real.exp (s * n * m / a) * Real.exp (-(s / a) * (z : ℝ)) := by
            rw [Real.exp_add]
  rw [centeredScaledWalk_eq_map,
    integral_map (measurable_of_countable _).aemeasurable (by fun_prop)]
  calc
    (∫ z, Real.exp (-s * (((z : ℝ) - n * m) / a)) ∂(intWalk ν n)) =
        ∫ z, Real.exp (s * n * m / a) * Real.exp (-(s / a) * (z : ℝ)) ∂(intWalk ν n) := by
          apply integral_congr_ae
          exact Eventually.of_forall hpoint
    _ = Real.exp (s * n * m / a) *
        (∫ z, Real.exp (-(s / a) * (z : ℝ)) ∂(intWalk ν n)) := by
          rw [integral_const_mul]
    _ = Real.exp (s * n * m / a) * stepLaplace ν (s / a) ^ n := by
          rw [intWalk_exp_integral ν hstep (div_nonneg hs ha.le) n]
    _ = stepLaplace ν (s / a) ^ n * Real.exp (s * n * m / a) := by ring

/-- The first moment of the centered scaled walk is zero. -/
theorem centeredScaledWalk_integral_eq_zero (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (hν : Integrable (fun z : ℤ => (z : ℝ)) ν) (m a : ℝ) (n : ℕ)
    (hm : m = mean ν) :
    (∫ x, x ∂(centeredScaledWalk ν m a n)) = 0 := by
  have hint := intWalk_integrable_cast ν hν n
  have hwalk := intWalk_integral_cast ν hν n
  rw [centeredScaledWalk_eq_map,
    integral_map (measurable_of_countable _).aemeasurable (by fun_prop)]
  have hfun : (fun z : ℤ => ((z : ℝ) - n * m) / a) =
      fun z : ℤ => a⁻¹ * (z : ℝ) - (n : ℝ) * m / a := by
    funext z
    simp only [div_eq_mul_inv]
    ring
  rw [hfun, integral_sub (hint.const_mul a⁻¹) (integrable_const _), integral_const_mul]
  simp
  rw [hwalk, hm]
  simp only [div_eq_mul_inv]
  ring

/-- Characteristic function of the scaled, centered walk. -/
theorem centeredScaledWalk_charFun (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (m a : ℝ) (n : ℕ) (t : ℝ) :
    charFun (centeredScaledWalk ν m a n) t =
      cexp (-((t * (n : ℝ) * m / a : ℝ) : ℂ) * I) *
        stepCharFun ν (t / a) ^ n := by
  rw [centeredScaledWalk]
  rw [show (fun x : ℝ => x - (n : ℝ) * m / a) =
      (fun x => x + (-(n : ℝ) * m / a)) by
        funext x
        ring]
  rw [charFun_map_add_const]
  have hscale :
      charFun (((intWalk ν n).map (fun z : ℤ => (z : ℝ) / a))) t =
        intWalkCharFun ν n (t / a) := by
    have h := charFun_map_mul_comp
      (μ := intWalk ν n) (f := fun z : ℤ => (z : ℝ))
      (measurable_of_countable _).aemeasurable (a⁻¹) t
    simpa [intWalkCharFun, stepCharFun, div_eq_mul_inv, mul_comm] using h
  rw [hscale, intWalkCharFun_eq_pow]
  have hinner : inner ℝ (-(n : ℝ) * m / a) t = -(t * (n : ℝ) * m / a) := by
    rw [real_inner_comm]
    simp
    ring
  rw [hinner]
  simp only [div_eq_mul_inv, Complex.ofReal_neg]
  ring



private theorem norm_centeredScaledWalk_charFun (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (m a : ℝ) (n : ℕ) (t : ℝ) :
    ‖charFun (centeredScaledWalk ν m a n) t‖ = ‖stepCharFun ν (t / a)‖ ^ n := by
  rw [centeredScaledWalk_charFun, norm_mul, norm_pow]
  have hp : ‖cexp (-((t * (n : ℝ) * m / a : ℝ) : ℂ) * I)‖ = 1 := by
    rw [Complex.norm_exp]
    simp
  rw [hp, one_mul]

private theorem tendsto_norm_stepCharFun_pow (ν : Measure ℤ) [IsProbabilityMeasure ν]
    {θ m : ℝ} {a : ℕ → ℝ} (h : IsStableAttracted ν θ m a) {ψ : ℕ → ℕ}
    (hψ : Tendsto ψ atTop atTop) {s : ℕ → ℝ} {t : ℝ}
    (hs : Tendsto s atTop (𝓝 t)) :
    Tendsto (fun j => ‖stepCharFun ν (s j / a (ψ j))‖ ^ ψ j) atTop
      (𝓝 (Real.exp (Real.cos (Real.pi * θ / 2) * |t| ^ θ))) := by
  obtain ⟨Q, hL, hQ⟩ := h.tendsto_centeredScaledWalkProb
  have hc := tendsto_charFun_moving (hQ.comp hψ) hs
  rw [charFun_eq_stableCF (by linarith [h.alpha_mem.1] : 0 < θ) hL] at hc
  have hn := hc.norm
  rw [norm_stableCF (by linarith [h.alpha_mem.1] : θ ≠ 0)] at hn
  change Tendsto (fun j => ‖charFun (centeredScaledWalk ν m (a (ψ j)) (ψ j)) (s j)‖)
    atTop (𝓝 _) at hn
  simpa only [norm_centeredScaledWalk_charFun] using hn

private theorem rpow_pow_div {x : ℝ} (hx : 0 ≤ x) {n m : ℕ} (hn : n ≠ 0) :
    (x ^ n) ^ ((m : ℝ) / n) = x ^ m := by
  rw [← Real.rpow_natCast x n, ← Real.rpow_mul hx, mul_div_cancel₀ _ (by exact_mod_cast hn),
    Real.rpow_natCast]

private theorem tendsto_natCast_of_div {m' : ℕ → ℕ} {κ : ℝ} (hκ : 0 < κ)
    (hm' : Tendsto (fun n : ℕ => (m' n : ℝ) / n) atTop (𝓝 κ)) :
    Tendsto m' atTop atTop := by
  have h1 : Tendsto (fun n : ℕ => (m' n : ℝ) / n * n) atTop atTop :=
    Tendsto.pos_mul_atTop hκ hm' tendsto_natCast_atTop_atTop
  have h2 : Tendsto (fun n : ℕ => (m' n : ℝ)) atTop atTop := by
    refine h1.congr' ?_
    filter_upwards [eventually_ne_atTop 0] with n hn
    field_simp
  exact tendsto_natCast_atTop_iff.1 h2

/-- Convergence of types for two eventually positive normings, allowing a change of time. -/
theorem tendsto_div_of_tendsto_div (ν : Measure ℤ) [IsProbabilityMeasure ν]
    {θ m : ℝ} {a b : ℕ → ℝ} (h : IsStableAttracted ν θ m a)
    (hb : IsStableAttracted ν θ m b) {m' : ℕ → ℕ} {κ : ℝ} (hκ : 0 < κ)
    (hm' : Tendsto (fun n : ℕ => (m' n : ℝ) / n) atTop (𝓝 κ)) :
    Tendsto (fun n => a n / b (m' n)) atTop (𝓝 (κ ^ (-(1 / θ)))) := by
  have hθ := h.alpha_mem
  have hθ0 : 0 < θ := by linarith
  set c0 : ℝ := Real.cos (Real.pi * θ / 2) with hc0
  have hc0neg : c0 < 0 := cos_pi_mul_div_two_neg hθ
  set G : ℝ → ℝ := fun s => Real.exp (c0 * |s| ^ θ) with hG
  have hm'top := tendsto_natCast_of_div hκ hm'
  set u : ℕ → ℝ := fun n => a n / b (m' n) with hu
  have hposa : ∀ᶠ n in atTop, 0 < a n := by
    obtain ⟨N, hN⟩ := h.pos
    exact (eventually_ge_atTop N).mono hN
  have hposb : ∀ᶠ n in atTop, 0 < b (m' n) := by
    obtain ⟨N, hN⟩ := hb.pos
    exact hm'top.eventually ((eventually_ge_atTop N).mono hN)
  have hposboth := hposa.and hposb |>.and
    ((eventually_ge_atTop 1).and (hm'top.eventually (eventually_ge_atTop 1)))
  have hupos : ∀ᶠ n in atTop, 0 < u n := by
    filter_upwards [hposboth] with n hn
    exact div_pos hn.1.1 hn.1.2
  have E1 : ∀ᶠ n in atTop, ‖stepCharFun ν (1 / b (m' n))‖ ^ m' n =
      (‖stepCharFun ν (u n / a n)‖ ^ n) ^ ((m' n : ℝ) / n) := by
    filter_upwards [hposboth] with n hn
    have ha := hn.1.1.ne'
    have ha' := hn.1.2.ne'
    rw [rpow_pow_div (norm_nonneg _) (by omega)]
    congr 3
    simp only [hu]
    field_simp
  have E2 : ∀ᶠ n in atTop, ‖stepCharFun ν (1 / a n)‖ ^ n =
      (‖stepCharFun ν ((1 / u n) / b (m' n))‖ ^ m' n) ^ ((n : ℝ) / m' n) := by
    filter_upwards [hposboth] with n hn
    have ha := hn.1.1.ne'
    have ha' := hn.1.2.ne'
    rw [rpow_pow_div (norm_nonneg _) (by omega)]
    congr 3
    simp only [hu]
    field_simp
  have hG1 : G 1 < 1 := by
    simp only [hG, abs_one, Real.one_rpow, mul_one]
    exact Real.exp_lt_one_iff.2 hc0neg
  apply tendsto_of_subseq_tendsto
  intro ns hns
  set v : ℕ → ℝ := fun n => u (ns n) / (1 + u (ns n)) with hv
  have hvmem : ∃ᶠ n in atTop, v n ∈ Icc (0 : ℝ) 1 := by
    apply Eventually.frequently
    filter_upwards [hns.eventually hupos] with n hn
    exact ⟨div_nonneg hn.le (by linarith), (div_le_one (by linarith)).2 (by linarith)⟩
  obtain ⟨w, hw, φ, hφ, hvφ⟩ := tendsto_subseq_of_frequently_bounded
    (Metric.isBounded_Icc 0 1) hvmem
  rw [closure_Icc] at hw
  set ψ : ℕ → ℕ := ns ∘ φ with hψ
  have hψtop : Tendsto ψ atTop atTop := hns.comp hφ.tendsto_atTop
  have huψpos : ∀ᶠ n in atTop, 0 < u (ψ n) := hψtop.eventually hupos
  have hrecov : ∀ᶠ n in atTop, u (ψ n) = v (φ n) / (1 - v (φ n)) := by
    filter_upwards [huψpos] with n hn
    simp only [hv, hψ, Function.comp]
    have h2 : 1 - u (ns (φ n)) / (1 + u (ns (φ n))) = 1 / (1 + u (ns (φ n))) := by
      have hupos' : 0 < u (ns (φ n)) := by simpa [ψ] using hn
      have hd : 1 + u (ns (φ n)) ≠ 0 := by linarith
      field_simp [hd]
      ring
    rw [h2]
    have hd : 1 + u (ns (φ n)) ≠ 0 := by
      have hupos' : 0 < u (ns (φ n)) := by simpa [ψ] using hn
      linarith
    field_simp [hd]
  have hratio : Tendsto (fun n => (m' (ψ n) : ℝ) / ψ n) atTop (𝓝 κ) := hm'.comp hψtop
  rcases hw.2.lt_or_eq with hw1 | hw1
  · set ustar : ℝ := w / (1 - w) with hustar
    have hu_t : Tendsto (fun n => u (ψ n)) atTop (𝓝 ustar) := by
      have ht : Tendsto (fun n => v (φ n) / (1 - v (φ n))) atTop (𝓝 (w / (1 - w))) :=
        hvφ.div (tendsto_const_nhds.sub hvφ) (by linarith)
      exact ht.congr' (hrecov.mono fun n hn => hn.symm)
    have hustar0 : 0 ≤ ustar := div_nonneg hw.1 (by linarith)
    have L1 : Tendsto (fun n => ‖stepCharFun ν (1 / b (m' (ψ n)))‖ ^ m' (ψ n))
        atTop (𝓝 (G 1)) := by
      have ht := tendsto_norm_stepCharFun_pow ν hb (hm'top.comp hψtop)
        (s := fun _ : ℕ => (1 : ℝ)) (t := 1) tendsto_const_nhds
      simpa [hG, hc0] using ht
    have L2 : Tendsto
        (fun n => (‖stepCharFun ν (u (ψ n) / a (ψ n))‖ ^ ψ n) ^
          ((m' (ψ n) : ℝ) / ψ n)) atTop (𝓝 (G ustar ^ κ)) := by
      have ht := (tendsto_norm_stepCharFun_pow ν h hψtop
        (s := fun n => u (ψ n)) (t := ustar) hu_t).rpow hratio
        (Or.inl (Real.exp_pos _).ne')
      simpa [hG, hc0] using ht
    have heq : G 1 = G ustar ^ κ := tendsto_nhds_unique L1
      (L2.congr' ((hψtop.eventually E1).mono fun n hn => hn.symm))
    have hval : ustar = κ ^ (-(1 / θ)) := by
      simp only [hG, abs_one, Real.one_rpow, mul_one, ← Real.exp_mul] at heq
      have h1 : c0 = c0 * |ustar| ^ θ * κ := Real.exp_injective heq
      have h2 : |ustar| ^ θ * κ = 1 := by
        have h3 : c0 * (|ustar| ^ θ * κ - 1) = 0 := by linarith
        rcases mul_eq_zero.1 h3 with h3 | h3
        · exact absurd h3 hc0neg.ne
        · linarith
      rw [abs_of_nonneg hustar0] at h2
      have h3 : ustar ^ θ = κ⁻¹ := by field_simp; linarith
      calc ustar = (ustar ^ θ) ^ (1 / θ) := by
              rw [← Real.rpow_mul hustar0, mul_one_div_cancel hθ0.ne', Real.rpow_one]
        _ = κ ^ (-(1 / θ)) := by rw [h3, Real.rpow_neg hκ.le, Real.inv_rpow hκ.le]
    refine ⟨φ, ?_⟩
    rw [← hval]
    exact hu_t
  · exfalso
    have hinv : Tendsto (fun n => 1 / u (ψ n)) atTop (𝓝 0) := by
      have ht : Tendsto (fun n => (1 - v (φ n)) / v (φ n)) atTop
          (𝓝 ((1 - w) / w)) :=
        (tendsto_const_nhds.sub hvφ).div hvφ (by rw [hw1]; norm_num)
      rw [hw1, sub_self, zero_div] at ht
      refine ht.congr' ?_
      filter_upwards [hrecov, huψpos] with n hn hnpos
      rw [hn]
      have hv1 : v (φ n) ≠ 1 := by
        intro h1
        rw [h1, sub_self, div_zero] at hn
        linarith
      have hv0 : v (φ n) ≠ 0 := by
        intro h0
        rw [h0, zero_div] at hn
        linarith
      have hden : 1 - v (φ n) ≠ 0 := sub_ne_zero.2 (Ne.symm hv1)
      field_simp [hv0, hden]
    have L1 : Tendsto (fun n => ‖stepCharFun ν (1 / a (ψ n))‖ ^ ψ n)
        atTop (𝓝 (G 1)) := by
      have ht := tendsto_norm_stepCharFun_pow ν h hψtop
        (s := fun _ : ℕ => (1 : ℝ)) (t := 1) tendsto_const_nhds
      simpa [hG, hc0] using ht
    have hratio' : Tendsto (fun n => (ψ n : ℝ) / m' (ψ n)) atTop (𝓝 κ⁻¹) := by
      have ht := hratio.inv₀ hκ.ne'
      refine ht.congr fun n => ?_
      simp [inv_div]
    have L2 : Tendsto
        (fun n => (‖stepCharFun ν ((1 / u (ψ n)) / b (m' (ψ n)))‖ ^ m' (ψ n)) ^
          ((ψ n : ℝ) / m' (ψ n))) atTop (𝓝 (G 0 ^ κ⁻¹)) := by
      have ht := (tendsto_norm_stepCharFun_pow ν hb (hm'top.comp hψtop)
        (s := fun n => 1 / u (ψ n)) (t := 0) hinv).rpow hratio'
        (Or.inl (Real.exp_pos _).ne')
      simpa [hG, hc0] using ht
    have heq : G 1 = G 0 ^ κ⁻¹ := tendsto_nhds_unique L1
      (L2.congr' ((hψtop.eventually E2).mono fun n hn => hn.symm))
    have hG0 : G 0 = 1 := by simp [hG, Real.zero_rpow hθ0.ne']
    rw [hG0, Real.one_rpow] at heq
    linarith

/-- The reciprocal form: `b (m' n) / a n` tends to `κ ^ (1 / θ)`. -/
theorem tendsto_div_of_tendsto_div' (ν : Measure ℤ) [IsProbabilityMeasure ν]
    {θ m : ℝ} {a b : ℕ → ℝ} (h : IsStableAttracted ν θ m a)
    (hb : IsStableAttracted ν θ m b) {m' : ℕ → ℕ} {κ : ℝ} (hκ : 0 < κ)
    (hm' : Tendsto (fun n : ℕ => (m' n : ℝ) / n) atTop (𝓝 κ)) :
    Tendsto (fun n => b (m' n) / a n) atTop (𝓝 (κ ^ (1 / θ))) := by
  have ht := (tendsto_div_of_tendsto_div ν h hb hκ hm').inv₀
    (Real.rpow_pos_of_pos hκ _).ne'
  rw [Real.rpow_neg hκ.le, inv_inv] at ht
  exact ht.congr fun n => by simp

/-- Every stable norming is regularly varying with index `1 / θ`. -/
theorem regularlyVaryingSeq (ν : Measure ℤ) [IsProbabilityMeasure ν]
    {θ m : ℝ} {a : ℕ → ℝ} (h : IsStableAttracted ν θ m a) :
    BGW.StableTrees.RegularlyVaryingSeq (1 / θ) a := by
  intro c hc
  apply tendsto_div_of_tendsto_div' ν h h hc
  exact (tendsto_nat_floor_mul_div_atTop (R := ℝ) hc.le).comp tendsto_natCast_atTop_atTop

/-- Successive scales are asymptotically equal, even for a nonmonotone norming. -/
theorem tendsto_succ_div (ν : Measure ℤ) [IsProbabilityMeasure ν]
    {θ m : ℝ} {a : ℕ → ℝ} (h : IsStableAttracted ν θ m a) :
    Tendsto (fun n => a (n + 1) / a n) atTop (𝓝 1) := by
  have h1 : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ) / n) atTop (𝓝 1) := by
    have ht : Tendsto (fun n : ℕ => 1 + 1 / (n : ℝ)) atTop (𝓝 (1 + 0)) := by
      exact tendsto_const_nhds.add tendsto_one_div_atTop_nhds_zero_nat
    rw [add_zero] at ht
    refine ht.congr' ?_
    filter_upwards [eventually_ne_atTop 0] with n hn
    push_cast
    field_simp
  have ht := tendsto_div_of_tendsto_div' ν h h one_pos h1
  rwa [Real.one_rpow] at ht

/-- Any two eventually positive normings giving the same normalized stable law are equivalent. -/
theorem norming_ratio_tendsto_one (ν : Measure ℤ) [IsProbabilityMeasure ν]
    {θ m : ℝ} {a b : ℕ → ℝ} (ha : IsStableAttracted ν θ m a)
    (hb : IsStableAttracted ν θ m b) :
    Tendsto (fun n => a n / b n) atTop (𝓝 1) := by
  have ht : Tendsto (fun n : ℕ => (n : ℝ) / n) atTop (𝓝 (1 : ℝ)) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ne_atTop 0] with n hn
    simp [hn]
  simpa using tendsto_div_of_tendsto_div ν ha hb one_pos ht

/-- Attraction forces a strictly contracting one-step characteristic-function modulus
at some frequency. -/
private theorem exists_norm_stepCharFun_lt_one (ν : Measure ℤ) [IsProbabilityMeasure ν]
    {θ m : ℝ} {a : ℕ → ℝ} (h : IsStableAttracted ν θ m a) :
    ∃ t : ℝ, ‖stepCharFun ν t‖ < 1 := by
  by_contra hn
  push Not at hn
  have heq (t : ℝ) : ‖stepCharFun ν t‖ = 1 :=
    le_antisymm (norm_charFun_le_one t) (hn t)
  have ht := tendsto_norm_stepCharFun_pow ν h tendsto_id
    (s := fun _ => 1) tendsto_const_nhds
  simp only [heq, one_pow, abs_one, Real.one_rpow, mul_one] at ht
  have hx := tendsto_nhds_unique ht tendsto_const_nhds
  have hneg := cos_pi_mul_div_two_neg h.alpha_mem
  have hlt := Real.exp_lt_one_iff.mpr hneg
  linarith

/-- Every eventually positive stable norming diverges, without a monotonicity assumption.
A bounded subsequence of scales has a convergent further subsequence; the frequencies
`t * a n` then converge, whereas the corresponding one-step CF powers tend to zero. -/
theorem tendsto_atTop (ν : Measure ℤ) [IsProbabilityMeasure ν]
    {θ m : ℝ} {a : ℕ → ℝ} (h : IsStableAttracted ν θ m a) :
    Tendsto a atTop atTop := by
  obtain ⟨t, ht⟩ := exists_norm_stepCharFun_lt_one ν h
  by_contra hn
  rw [tendsto_atTop_atTop] at hn
  push Not at hn
  obtain ⟨K, hK⟩ := hn
  have hpos : ∀ᶠ n in atTop, 0 < a n := by
    obtain ⟨N, hN⟩ := h.pos
    exact (eventually_ge_atTop N).mono hN
  have hfreq : ∃ᶠ n in atTop, a n ∈ Icc 0 K := by
    have hf : ∃ᶠ n in atTop, a n < K := by
      rw [frequently_atTop]
      exact hK
    exact (hf.and_eventually hpos).mono fun n hn => ⟨hn.2.le, hn.1.le⟩
  obtain ⟨A, _, φ, hφ, hA⟩ := tendsto_subseq_of_frequently_bounded
    (Metric.isBounded_Icc 0 K) hfreq
  have hs : Tendsto (fun j => t * a (φ j)) atTop (𝓝 (t * A)) :=
    tendsto_const_nhds.mul hA
  have hlim := tendsto_norm_stepCharFun_pow ν h hφ.tendsto_atTop hs
  have hid : ∀ᶠ j in atTop, t * a (φ j) / a (φ j) = t := by
    filter_upwards [hφ.tendsto_atTop.eventually hpos] with j hj
    exact mul_div_cancel_right₀ t hj.ne'
  have hlim' : Tendsto (fun j => ‖stepCharFun ν t‖ ^ φ j) atTop
      (𝓝 (Real.exp (Real.cos (Real.pi * θ / 2) * |t * A| ^ θ))) := by
    refine hlim.congr' ?_
    filter_upwards [hid] with j hj
    rw [hj]
  have hzero := (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) ht).comp
    hφ.tendsto_atTop
  exact (Real.exp_pos _).ne' (tendsto_nhds_unique hlim' hzero)

end BGW.StableTrees.Attraction.TransformConvergence
