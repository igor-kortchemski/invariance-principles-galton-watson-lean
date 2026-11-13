module

public import BGWLeaves.StableAnalysis.Defs
public import Mathlib.Data.Int.Lemmas
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

@[expose] public section

open Complex MeasureTheory ProbabilityTheory Filter Set
open BGW.StableTrees.Scalar
open scoped Topology

namespace BGWLeaves.StableAnalysis.StrongLLT

/-- At index two, the Fourier-defined stable density is the `N(0, 2)` density. -/
theorem stableDensity_two (x : ℝ) :
    BGW.StableTrees.Scalar.stableDensity 2 x = BGWLeaves.StableAnalysis.gaussDensity x := by
  have hcf (θ : ℝ) : BGW.StableTrees.Scalar.stableCF 2 θ =
      ((Real.exp (-θ ^ 2) : ℝ) : ℂ) := by
    rw [BGW.StableTrees.Scalar.stableCF]
    have hp : (-((θ : ℂ) * I)) ^ ((2 : ℝ) : ℂ) = ((-(θ ^ 2) : ℝ) : ℂ) := by
      rw [show ((2 : ℝ) : ℂ) = ((2 : ℕ) : ℂ) by norm_num, Complex.cpow_natCast]
      push_cast
      rw [pow_two]
      calc
        (-((θ : ℂ) * I)) * (-((θ : ℂ) * I)) = (θ : ℂ) ^ 2 * I ^ 2 := by ring
        _ = -((θ : ℂ) ^ 2) := by rw [I_sq]; ring
    rw [hp, Complex.ofReal_exp]
  have hfourier := fourierIntegral_gaussian (b := (1 : ℂ)) (by norm_num) (-(x : ℂ))
  have hphase : ∀ θ : ℝ,
      cexp (-((θ : ℂ) * x * I)) * ((Real.exp (-θ ^ 2) : ℝ) : ℂ) =
        cexp (I * (-(x : ℂ)) * (θ : ℂ)) * cexp (-(1 : ℂ) * (θ : ℂ) ^ 2) := by
    intro θ
    rw [Complex.ofReal_exp]
    congr 2 <;> push_cast <;> ring
  have hroot : (Real.pi : ℂ) ^ (1 / 2 : ℂ) = (Real.sqrt Real.pi : ℂ) := by
    have hexp : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by norm_num
    rw [hexp, ← Complex.ofReal_cpow Real.pi_pos.le, Real.sqrt_eq_rpow]
  have hcexp : cexp (-(-(x : ℂ)) ^ 2 / (4 : ℂ)) =
      ((Real.exp (-x ^ 2 / 4) : ℝ) : ℂ) := by
    rw [Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  have hF : ∫ θ : ℝ,
      cexp (-((θ : ℂ) * x * I)) * ((Real.exp (-θ ^ 2) : ℝ) : ℂ) =
      ((Real.sqrt Real.pi * Real.exp (-x ^ 2 / 4) : ℝ) : ℂ) := by
    calc
      _ = ∫ θ : ℝ,
          cexp (I * (-(x : ℂ)) * (θ : ℂ)) * cexp (-(1 : ℂ) * (θ : ℂ) ^ 2) := by
            apply integral_congr_ae
            filter_upwards [] with θ
            exact hphase θ
      _ = _ := by
            rw [hfourier]
            simp only [div_one, mul_one]
            rw [hroot, hcexp]
            exact (Complex.ofReal_mul _ _).symm
  have hI : ∫ θ : ℝ,
      BGW.StableTrees.Scalar.stableCF 2 θ * cexp (-((θ : ℂ) * x * I)) =
      ((Real.sqrt Real.pi * Real.exp (-x ^ 2 / 4) : ℝ) : ℂ) := by
    calc
      _ = ∫ θ : ℝ,
          cexp (-((θ : ℂ) * x * I)) * ((Real.exp (-θ ^ 2) : ℝ) : ℂ) := by
            apply integral_congr_ae
            filter_upwards [] with θ
            rw [hcf θ]
            ring
      _ = _ := hF
  rw [BGW.StableTrees.Scalar.stableDensity, hI]
  unfold BGWLeaves.StableAnalysis.gaussDensity
  simp only [Complex.ofReal_re]
  have hsqrt4 : Real.sqrt (4 * Real.pi) = 2 * Real.sqrt Real.pi := by
    apply (Real.sqrt_eq_iff_mul_self_eq (by positivity) (by positivity)).2
    calc
      4 * Real.pi = (2 * Real.sqrt Real.pi) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt Real.pi_pos.le]
        ring
      _ = 2 * Real.sqrt Real.pi * (2 * Real.sqrt Real.pi) := by ring
  rw [hsqrt4]
  field_simp [Real.pi_ne_zero, (Real.sqrt_pos.2 Real.pi_pos).ne']
  rw [Real.sq_sqrt Real.pi_pos.le]

/-! Finite-variance Fourier infrastructure for the weighted estimate.  The centering
is real throughout: no assumption that the mean is an integer is used. -/

private lemma integrable_cast_of_sq {ρ : Measure ℤ}
    (h : Integrable (fun z : ℤ => (z : ℝ) ^ 2) ρ) :
    Integrable (fun z : ℤ => (z : ℝ)) ρ := by
  apply Integrable.mono' h (measurable_of_countable _).aestronglyMeasurable
  filter_upwards with z
  simp only [Real.norm_eq_abs]
  by_cases hz : z = 0
  · simp [hz]
  have h1 : (1 : ℝ) ≤ |(z : ℝ)| := by
    have : 1 ≤ |z| := by have := abs_pos.mpr hz; omega
    exact_mod_cast this
  nlinarith [sq_abs (z : ℝ)]

private lemma integrable_centered_sq {ρ : Measure ℤ} [IsProbabilityMeasure ρ]
    (h : Integrable (fun z : ℤ => (z : ℝ) ^ 2) ρ) (m : ℝ) :
    Integrable (fun z : ℤ => ((z : ℝ) - m) ^ 2) ρ := by
  have hi := (h.sub ((integrable_cast_of_sq h).const_mul (2 * m))).add
    (integrable_const (m ^ 2))
  convert hi using 1
  funext z
  dsimp
  ring

private noncomputable def centeredCF (ρ : Measure ℤ) (m t : ℝ) : ℂ :=
  ∫ z, cexp (((t * ((z : ℝ) - m) : ℝ) : ℂ) * I) ∂ρ

private noncomputable def centeredCF₁ (ρ : Measure ℤ) (m t : ℝ) : ℂ :=
  ∫ z, (((z : ℝ) - m : ℝ) : ℂ) * I *
    cexp (((t * ((z : ℝ) - m) : ℝ) : ℂ) * I) ∂ρ

private noncomputable def centeredCF₂ (ρ : Measure ℤ) (m t : ℝ) : ℂ :=
  ∫ z, -((((z : ℝ) - m) ^ 2 : ℝ) : ℂ) *
    cexp (((t * ((z : ℝ) - m) : ℝ) : ℂ) * I) ∂ρ

private lemma hasDerivAt_centered_exponential (y t : ℝ) :
    HasDerivAt (fun t : ℝ => cexp (((t * y : ℝ) : ℂ) * I))
      ((y : ℂ) * I * cexp (((t * y : ℝ) : ℂ) * I)) t := by
  simpa only [id_eq, Complex.ofReal_mul, Complex.ofReal_one, one_mul, mul_one,
    mul_comm, mul_left_comm, mul_assoc] using
    (((hasDerivAt_id t).mul_const y).ofReal_comp.mul_const I).cexp

private lemma norm_centered_exponential (y t : ℝ) :
    ‖cexp (((t * y : ℝ) : ℂ) * I)‖ = 1 := by
  exact Complex.norm_exp_ofReal_mul_I _

private lemma hasDerivAt_centeredCF {ρ : Measure ℤ} [IsProbabilityMeasure ρ]
    (h : Integrable (fun z : ℤ => (z : ℝ)) ρ) (m t : ℝ) :
    HasDerivAt (centeredCF ρ m) (centeredCF₁ ρ m t) t := by
  have hi : Integrable (fun z : ℤ => (z : ℝ) - m) ρ := h.sub (integrable_const m)
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := ρ) (s := univ) (bound := fun z : ℤ => |(z : ℝ) - m|)
    (F' := fun t z => (((z : ℝ) - m : ℝ) : ℂ) * I *
      cexp (((t * ((z : ℝ) - m) : ℝ) : ℂ) * I))
    (by simp) (Eventually.of_forall fun _ =>
      (measurable_of_countable _).aestronglyMeasurable) _
    (measurable_of_countable _).aestronglyMeasurable _ hi.abs _).2
  · exact Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable 1
      (Eventually.of_forall fun z => (norm_centered_exponential _ _).le)
  · exact Eventually.of_forall fun z _ _ => by
      simp only [norm_mul, norm_I, norm_centered_exponential, Complex.norm_real,
        Real.norm_eq_abs, mul_one, le_refl]
  · exact Eventually.of_forall fun z t _ => hasDerivAt_centered_exponential _ t

private lemma hasDerivAt_centeredCF₁ {ρ : Measure ℤ} [IsProbabilityMeasure ρ]
    (h : Integrable (fun z : ℤ => (z : ℝ) ^ 2) ρ) (m t : ℝ) :
    HasDerivAt (centeredCF₁ ρ m) (centeredCF₂ ρ m t) t := by
  have hi : Integrable (fun z : ℤ => (z : ℝ) - m) ρ :=
    (integrable_cast_of_sq h).sub (integrable_const m)
  have hsq := integrable_centered_sq h m
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := ρ) (s := univ) (bound := fun z : ℤ => ((z : ℝ) - m) ^ 2)
    (F' := fun t z => -((((z : ℝ) - m) ^ 2 : ℝ) : ℂ) *
      cexp (((t * ((z : ℝ) - m) : ℝ) : ℂ) * I))
    (by simp) (Eventually.of_forall fun _ =>
      (measurable_of_countable _).aestronglyMeasurable) _
    (measurable_of_countable _).aestronglyMeasurable _ hsq _).2
  · apply Integrable.mono' hi.abs (measurable_of_countable _).aestronglyMeasurable
    exact Eventually.of_forall fun z => by
      simp only [norm_mul, norm_I, norm_centered_exponential, Complex.norm_real,
        Real.norm_eq_abs, mul_one, le_refl]
  · exact Eventually.of_forall fun z _ _ => by
      simp only [norm_mul, norm_neg, norm_centered_exponential, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ((z : ℝ) - m)), mul_one, le_refl]
  · exact Eventually.of_forall fun z t _ => by
      convert (hasDerivAt_centered_exponential ((z : ℝ) - m) t).const_mul
        ((((z : ℝ) - m : ℝ) : ℂ) * I) using 1
      push_cast
      ring_nf
      simp [I_sq]
      ring

private lemma continuous_centeredCF₂ {ρ : Measure ℤ} [IsProbabilityMeasure ρ]
    (h : Integrable (fun z : ℤ => (z : ℝ) ^ 2) ρ) (m : ℝ) :
    Continuous (centeredCF₂ ρ m) := by
  apply continuous_of_dominated (bound := fun z : ℤ => ((z : ℝ) - m) ^ 2)
  · exact fun _ => (measurable_of_countable _).aestronglyMeasurable
  · exact fun t => Eventually.of_forall fun z => by
      simp only [norm_mul, norm_neg, norm_centered_exponential, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ((z : ℝ) - m)), mul_one, le_refl]
  · exact integrable_centered_sq h m
  · exact Eventually.of_forall fun z => by fun_prop

private lemma centeredCF_zero (ρ : Measure ℤ) [IsProbabilityMeasure ρ] (m : ℝ) :
    centeredCF ρ m 0 = 1 := by
  simp [centeredCF]

private lemma centeredCF₁_zero {ρ : Measure ℤ} [IsProbabilityMeasure ρ]
    (h : Integrable (fun z : ℤ => (z : ℝ)) ρ) :
    centeredCF₁ ρ (mean ρ) 0 = 0 := by
  simp only [centeredCF₁, zero_mul, Complex.ofReal_zero, Complex.exp_zero, mul_one]
  rw [integral_mul_const, integral_complex_ofReal, integral_sub h (integrable_const _)]
  simp [mean]

private lemma centeredCF₂_zero (ρ : Measure ℤ) :
    centeredCF₂ ρ (mean ρ) 0 = -(variance ρ : ℂ) := by
  simp only [centeredCF₂, zero_mul, Complex.ofReal_zero, Complex.exp_zero, mul_one]
  rw [integral_neg, integral_complex_ofReal]
  rfl

/-- The first centered derivative has precisely its linear variance term. -/
private lemma centeredCF₁_first_order {ρ : Measure ℤ} [IsProbabilityMeasure ρ]
    (h : Integrable (fun z : ℤ => (z : ℝ) ^ 2) ρ) :
    (fun t : ℝ => centeredCF₁ ρ (mean ρ) t + (variance ρ : ℂ) * t)
      =o[𝓝 0] (fun t : ℝ => t) := by
  have hd := (hasDerivAt_centeredCF₁ h (mean ρ) 0).isLittleO
  simpa [centeredCF₁_zero (integrable_cast_of_sq h), centeredCF₂_zero,
    Complex.real_smul, mul_comm] using hd

/-- The finite-variance quadratic remainder, with arbitrary real mean. -/
private lemma centeredCF_second_order {ρ : Measure ℤ} [IsProbabilityMeasure ρ]
    (h : Integrable (fun z : ℤ => (z : ℝ) ^ 2) ρ) :
    (fun t : ℝ => centeredCF ρ (mean ρ) t -
      (1 - (variance ρ : ℂ) * (t : ℂ) ^ 2 / 2))
      =o[𝓝 0] (fun t : ℝ => t ^ 2) := by
  let f : ℝ → ℂ := fun t => centeredCF ρ (mean ρ) t -
    (1 - (variance ρ : ℂ) * (t : ℂ) ^ 2 / 2)
  have hd (t : ℝ) : HasDerivAt f
      (centeredCF₁ ρ (mean ρ) t + (variance ρ : ℂ) * t) t := by
    have hp := (((hasDerivAt_id t).ofReal_comp.pow 2).const_mul
      (variance ρ : ℂ)).div_const 2
    convert (hasDerivAt_centeredCF (integrable_cast_of_sq h) (mean ρ) t).sub
      ((hasDerivAt_const t (1 : ℂ)).sub hp) using 1
    · funext u
      dsimp [f]
    · simp
      ring
  have ho := Convex.isLittleO_pow_succ_real (n := 1) (s := univ) convex_univ
    (mem_univ (0 : ℝ)) (fun t _ => (hd t).hasDerivWithinAt)
    (by simpa using (centeredCF₁_first_order h))
  simpa [f, centeredCF_zero] using ho

private lemma variance_pos_of_nonlattice {ρ : Measure ℤ} [IsProbabilityMeasure ρ]
    (hnl : ¬ IsLatticeLaw ρ)
    (h : Integrable (fun z : ℤ => (z : ℝ) ^ 2) ρ) : 0 < variance ρ := by
  have hnonneg : 0 ≤ variance ρ := integral_nonneg fun _ => sq_nonneg _
  by_contra hn
  have hz : variance ρ = 0 := le_antisymm (le_of_not_gt hn) hnonneg
  have hae : ∀ᵐ (z : ℤ) ∂ρ, (z : ℝ) = mean ρ := by
    have hh := (integral_eq_zero_iff_of_nonneg (fun z : ℤ => sq_nonneg ((z : ℝ) - mean ρ))
      (integrable_centered_sq h (mean ρ))).1 hz
    filter_upwards [hh] with z hz
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp hz)
  obtain ⟨b, hb⟩ := hae.exists
  apply hnl
  refine ⟨b, 2, le_rfl, ?_⟩
  filter_upwards [hae] with z hz
  have heq : z = b := by exact_mod_cast hz.trans hb.symm
  simp [heq]

/-- Weighted centered Fourier kernels all have the same twisted period.  This
also applies to the first two derivative kernels; their endpoint terms cancel
against the translated Fourier phase even when the mean is not an integer. -/
private lemma centered_kernel_twisted_period (ρ : Measure ℤ) (m t : ℝ) (w : ℤ → ℂ) :
    (∫ z, w z * cexp (((((t + 2 * Real.pi) * ((z : ℝ) - m)) : ℝ) : ℂ) * I) ∂ρ) =
      cexp (-(((2 * Real.pi * m : ℝ) : ℂ) * I)) *
        ∫ z, w z * cexp (((t * ((z : ℝ) - m) : ℝ) : ℂ) * I) ∂ρ := by
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact Eventually.of_forall fun z => by
    have hp : cexp (((((t + 2 * Real.pi) * ((z : ℝ) - m)) : ℝ) : ℂ) * I) =
        cexp (-(((2 * Real.pi * m : ℝ) : ℂ) * I)) *
          cexp (((t * ((z : ℝ) - m) : ℝ) : ℂ) * I) := by
      calc
        _ = cexp ((z : ℂ) * (2 * Real.pi * I) +
              (-(((2 * Real.pi * m : ℝ) : ℂ) * I) +
                (((t * ((z : ℝ) - m) : ℝ) : ℂ) * I))) := by
              congr 1
              push_cast
              ring
        _ = _ := by rw [Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I,
          one_mul, Complex.exp_add]
    dsimp only
    rw [hp]
    ring

/-- Two integrations by parts require equality of the phase-weighted endpoint
values, rather than periodicity of the centered function itself. -/
private lemma fourier_second_derivative {F F₁ F₂ : ℝ → ℂ} {a b y : ℝ}
    (hF : ∀ t, HasDerivAt F (F₁ t) t)
    (hF₁ : ∀ t, HasDerivAt F₁ (F₂ t) t) (hF₂ : Continuous F₂)
    (hbd : F b * cexp (((-y * b : ℝ) : ℂ) * I) =
      F a * cexp (((-y * a : ℝ) : ℂ) * I))
    (hbd₁ : F₁ b * cexp (((-y * b : ℝ) : ℂ) * I) =
      F₁ a * cexp (((-y * a : ℝ) : ℂ) * I)) :
    (∫ t in a..b, F₂ t * cexp (((-y * t : ℝ) : ℂ) * I)) =
      -(y : ℂ) ^ 2 * ∫ t in a..b, F t * cexp (((-y * t : ℝ) : ℂ) * I) := by
  let E : ℝ → ℂ := fun t => cexp (((-y * t : ℝ) : ℂ) * I)
  let c : ℂ := (-y : ℝ) * I
  have hE (t : ℝ) : HasDerivAt E (c * E t) t := by
    simpa [E, c, mul_comm] using hasDerivAt_centered_exponential (-y) t
  have hEc : Continuous E := continuous_iff_continuousAt.2 fun t => (hE t).continuousAt
  have hFc : Continuous F := continuous_iff_continuousAt.2 fun t => (hF t).continuousAt
  have hF₁c : Continuous F₁ := continuous_iff_continuousAt.2 fun t => (hF₁ t).continuousAt
  have h1 := intervalIntegral.integral_deriv_mul_eq_sub_of_hasDerivAt
    (a := a) (b := b) hFc.continuousOn hEc.continuousOn
    (fun t _ => hF t) (fun t _ => hE t)
    (hF₁c.intervalIntegrable a b) ((continuous_const.mul hEc).intervalIntegrable a b)
  have h2 := intervalIntegral.integral_deriv_mul_eq_sub_of_hasDerivAt
    (a := a) (b := b) hF₁c.continuousOn hEc.continuousOn
    (fun t _ => hF₁ t) (fun t _ => hE t)
    (hF₂.intervalIntegrable a b) ((continuous_const.mul hEc).intervalIntegrable a b)
  have hi₀ : IntervalIntegrable (fun t => F t * E t) volume a b :=
    (hFc.mul hEc).intervalIntegrable a b
  have hi₁ : IntervalIntegrable (fun t => F₁ t * E t) volume a b :=
    (hF₁c.mul hEc).intervalIntegrable a b
  have hi₂ : IntervalIntegrable (fun t => F₂ t * E t) volume a b :=
    (hF₂.mul hEc).intervalIntegrable a b
  have heq (G : ℝ → ℂ) : (fun t => G t * (c * E t)) =
      (fun t => c * (G t * E t)) := by funext t; ring
  rw [hbd, sub_self, intervalIntegral.integral_add hi₁
    (hi₀.const_mul c |>.congr (fun t _ => by ring)), heq F,
    intervalIntegral.integral_const_mul] at h1
  rw [hbd₁, sub_self, intervalIntegral.integral_add hi₂
    (hi₁.const_mul c |>.congr (fun t _ => by ring)), heq F₁,
    intervalIntegral.integral_const_mul] at h2
  change (∫ t in a..b, F₂ t * E t) = _
  calc
    _ = -c * (∫ t in a..b, F₁ t * E t) := by linear_combination h2
    _ = c ^ 2 * ∫ t in a..b, F t * E t := by linear_combination -c * h1
    _ = _ := by dsimp [c, E]; push_cast; ring_nf; simp [I_sq]

private noncomputable def stepCF (ν : Measure ℤ) (θ : ℝ) : ℂ :=
  ∫ z, cexp (θ * (z : ℂ) * I) ∂ν

private theorem norm_stepCF_le (ν : Measure ℤ) [IsProbabilityMeasure ν] (θ : ℝ) :
    ‖stepCF ν θ‖ ≤ 1 := by
  refine (norm_integral_le_integral_norm _).trans ?_
  simp [Complex.norm_exp]

private theorem continuous_stepCF (ν : Measure ℤ) [IsProbabilityMeasure ν] :
    Continuous (stepCF ν) := by
  apply continuous_of_dominated (bound := fun _ => 1)
  · exact fun θ => (measurable_of_countable _).aestronglyMeasurable
  · exact fun θ => Eventually.of_forall fun z => by simp [Complex.norm_exp]
  · exact integrable_const 1
  · exact Eventually.of_forall fun z => by fun_prop

private lemma centeredCF_eq_phase_mul (ρ : Measure ℤ) (m t : ℝ) :
    centeredCF ρ m t = cexp (-(((t * m : ℝ) : ℂ) * I)) * stepCF ρ t := by
  rw [centeredCF, stepCF, ← integral_const_mul]
  apply integral_congr_ae
  exact Eventually.of_forall fun z => by
    dsimp only
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring

private lemma norm_centeredCF (ρ : Measure ℤ) (m t : ℝ) :
    ‖centeredCF ρ m t‖ = ‖stepCF ρ t‖ := by
  rw [centeredCF_eq_phase_mul, norm_mul]
  have hp : cexp (-(((t * m : ℝ) : ℂ) * I)) = cexp (((-t * m : ℝ) : ℂ) * I) := by
    congr 1
    push_cast
    ring
  rw [hp, norm_centered_exponential, one_mul]

private lemma norm_centeredCF₂_le {ρ : Measure ℤ} [IsProbabilityMeasure ρ]
    (m t : ℝ) : ‖centeredCF₂ ρ m t‖ ≤ ∫ z, ((z : ℝ) - m) ^ 2 ∂ρ := by
  refine (norm_integral_le_integral_norm _).trans_eq ?_
  congr 1
  funext z
  simp only [norm_mul, norm_neg, norm_centered_exponential, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ((z : ℝ) - m)), mul_one]

private lemma norm_centeredCF₁_le {ρ : Measure ℤ} [IsProbabilityMeasure ρ]
    (h : Integrable (fun z : ℤ => (z : ℝ) ^ 2) ρ) (t : ℝ) :
    ‖centeredCF₁ ρ (mean ρ) t‖ ≤ variance ρ * |t| := by
  have hb := convex_univ.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := centeredCF₁ ρ (mean ρ)) (f' := centeredCF₂ ρ (mean ρ))
    (fun x _ => (hasDerivAt_centeredCF₁ h (mean ρ) x).hasDerivWithinAt)
    (fun x _ => norm_centeredCF₂_le (ρ := ρ) (mean ρ) x)
    (mem_univ (0 : ℝ)) (mem_univ t)
  simpa [centeredCF₁_zero (integrable_cast_of_sq h), Real.norm_eq_abs, variance] using hb

/-- The quadratic CF expansion gives a Gaussian bound on a fixed neighborhood. -/
private lemma exists_norm_centeredCF_le_exp {ρ : Measure ℤ} [IsProbabilityMeasure ρ]
    (hnl : ¬ IsLatticeLaw ρ)
    (h : Integrable (fun z : ℤ => (z : ℝ) ^ 2) ρ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, |t| ≤ δ →
      ‖centeredCF ρ (mean ρ) t‖ ≤ Real.exp (-(variance ρ / 4) * t ^ 2) := by
  have hv := variance_pos_of_nonlattice hnl h
  have ho := (centeredCF_second_order h).bound (show 0 < variance ρ / 4 by positivity)
  have hp : ∀ᶠ t : ℝ in 𝓝 0, variance ρ * t ^ 2 / 2 < 1 := by
    have ht : Continuous (fun t : ℝ => variance ρ * t ^ 2 / 2) := by fun_prop
    simpa using (ht.tendsto 0).eventually (gt_mem_nhds (show variance ρ * (0 : ℝ) ^ 2 / 2 < 1 by simp))
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 (ho.and hp)
  refine ⟨δ / 2, by positivity, fun t ht => ?_⟩
  have htd : dist t 0 < δ := by rw [Real.dist_eq, sub_zero]; linarith
  obtain ⟨hr, hpoly⟩ := hball htd
  have hnorm : ‖(1 : ℂ) - (variance ρ : ℂ) * (t : ℂ) ^ 2 / 2‖ =
      1 - variance ρ * t ^ 2 / 2 := by
    rw [show (1 : ℂ) - (variance ρ : ℂ) * (t : ℂ) ^ 2 / 2 =
      ((1 - variance ρ * t ^ 2 / 2 : ℝ) : ℂ) by push_cast; rfl,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
  have hh := norm_add_le (centeredCF ρ (mean ρ) t -
    (1 - (variance ρ : ℂ) * (t : ℂ) ^ 2 / 2))
      (1 - (variance ρ : ℂ) * (t : ℂ) ^ 2 / 2)
  rw [sub_add_cancel, hnorm] at hh
  have hr' : ‖centeredCF ρ (mean ρ) t -
      (1 - (variance ρ : ℂ) * (t : ℂ) ^ 2 / 2)‖ ≤ variance ρ / 4 * t ^ 2 := by
    simpa [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg t)] using hr
  calc
    _ ≤ 1 + (-(variance ρ / 4) * t ^ 2) := by linarith
    _ ≤ _ := by simpa only [add_comm] using Real.add_one_le_exp (-(variance ρ / 4) * t ^ 2)

private def supportDiffs (ν : Measure ℤ) : Set ℤ :=
  {d | ∃ x y : ℤ, ν {x} ≠ 0 ∧ ν {y} ≠ 0 ∧ d = x - y}

private noncomputable def supportDiffGenerator (ν : Measure ℤ) : ℤ :=
  Submodule.IsPrincipal.generator (Ideal.span (supportDiffs ν))

private theorem supportDiffGenerator_dvd (ν : Measure ℤ) {x y : ℤ}
    (hx : ν {x} ≠ 0) (hy : ν {y} ≠ 0) :
    supportDiffGenerator ν ∣ x - y := by
  have hmem : x - y ∈ Ideal.span (supportDiffs ν) :=
    Ideal.subset_span ⟨x, y, hx, hy, rfl⟩
  rw [Submodule.IsPrincipal.mem_iff_eq_smul_generator] at hmem
  obtain ⟨c, hc⟩ := hmem
  rw [hc, smul_eq_mul]
  exact Dvd.intro_left c rfl

private theorem exists_two_atoms (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (hnl : ¬ IsLatticeLaw ν) :
    ∃ x y : ℤ, x ≠ y ∧ 0 < ν {x} ∧ 0 < ν {y} := by
  have hcover : ν (⋃ x : ℤ, ({x} : Set ℤ)) ≠ 0 := by
    have hset : (⋃ x : ℤ, ({x} : Set ℤ)) = Set.univ := by ext y; simp
    rw [hset]
    simp
  obtain ⟨x, hx⟩ := exists_measure_pos_of_not_measure_iUnion_null hcover
  have hcompl : ν ({x}ᶜ) ≠ 0 := by
    intro hzero
    have hxa : ∀ᵐ y ∂ν, y = x := by
      rw [ae_iff_of_countable]
      intro y hy
      by_cases hyx : y = x
      · exact hyx
      · have hsub : ({y} : Set ℤ) ⊆ ({x}ᶜ) := by
          intro z hz
          simp only [Set.mem_singleton_iff] at hz
          simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
          exact fun hzx => hyx (hz.symm.trans hzx)
        have hyzero : ν {y} = 0 := by
          apply le_antisymm _ bot_le
          calc ν {y} ≤ ν ({x}ᶜ) := measure_mono hsub
            _ = 0 := hzero
        exact (hy hyzero).elim
    apply hnl
    refine ⟨x, 2, by norm_num, ?_⟩
    filter_upwards [hxa] with y hy
    simp [hy]
  have hcomplpos : 0 < ν ({x}ᶜ) := bot_lt_iff_ne_bot.mpr hcompl
  have hcover' : (⋃ y : ℤ, (if y = x then (∅ : Set ℤ) else {y})) = ({x}ᶜ) := by
    ext y
    simp
  have hunion : ν (⋃ y : ℤ, (if y = x then (∅ : Set ℤ) else {y})) ≠ 0 := by
    rw [hcover']
    exact hcompl
  obtain ⟨y, hy⟩ := exists_measure_pos_of_not_measure_iUnion_null hunion
  have hyx : y ≠ x := by
    by_contra h
    subst y
    simp at hy
  refine ⟨x, y, Ne.symm hyx, hx, ?_⟩
  simpa [hyx] using hy

private theorem supportDiffGenerator_natAbs_eq_one
    (ν : Measure ℤ) [IsProbabilityMeasure ν] (hnl : ¬ IsLatticeLaw ν) :
    (supportDiffGenerator ν).natAbs = 1 := by
  obtain ⟨b, y, hby, hb, hy⟩ := exists_two_atoms ν hnl
  have hg0 : supportDiffGenerator ν ≠ 0 := by
    intro hg
    have hae : ∀ᵐ x ∂ν, x = b := by
      rw [ae_iff_of_countable]
      intro x hx
      have hd := supportDiffGenerator_dvd ν hx (ne_of_gt hb)
      rw [hg] at hd
      have hzero : x - b = 0 := by simpa using hd
      omega
    apply hnl
    refine ⟨b, 2, by norm_num, ?_⟩
    filter_upwards [hae] with x hx
    simp [hx]
  have hpos : 0 < (supportDiffGenerator ν).natAbs := Int.natAbs_pos.mpr hg0
  by_contra hne
  have htwo : 2 ≤ (supportDiffGenerator ν).natAbs := by omega
  have hdvd : ((supportDiffGenerator ν).natAbs : ℤ) ∣ supportDiffGenerator ν := by
    rw [Int.natCast_natAbs]
    rw [abs_dvd]
  exact hnl (by
    refine ⟨b, (supportDiffGenerator ν).natAbs, htwo, ?_⟩
    rw [ae_iff_of_countable]
    intro x hx
    exact dvd_trans hdvd (supportDiffGenerator_dvd ν hx (ne_of_gt hb)))

private theorem exists_int_of_norm_stepCF_eq_one (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (hnl : ¬ IsLatticeLaw ν) {θ : ℝ} (h : ‖stepCF ν θ‖ = 1) :
    ∃ n : ℤ, θ * (supportDiffGenerator ν : ℝ) = n * (2 * Real.pi) := by
  obtain ⟨z, w, hzw, hzpos, hwpos⟩ := exists_two_atoms ν hnl
  set e : ℤ → ℂ := fun k => cexp (θ * (k : ℂ) * I) with he
  have hen : ∀ k, ‖e k‖ = 1 := by
    intro k
    simp only [he]
    rw [show θ * (k : ℂ) * I = ((θ * (k : ℝ) : ℝ) : ℂ) * I by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I]
  have hφ : stepCF ν θ = ∫ k, e k ∂ν := by rfl
  set u : ℂ := starRingEnd ℂ (stepCF ν θ) with hu
  have hun : ‖u‖ = 1 := by rw [hu, Complex.norm_conj, h]
  have huφ : u * stepCF ν θ = 1 := by
    rw [hu, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, h]
    simp
  have hint : Integrable e ν :=
    Integrable.of_bound (C := 1) (measurable_of_countable _).aestronglyMeasurable
      (Eventually.of_forall fun k => (hen k).le)
  let g : ℤ → ℝ := fun k => 1 - (u * e k).re
  have hg0 : 0 ≤ g := by
    intro k
    change 0 ≤ 1 - (u * e k).re
    rw [sub_nonneg]
    calc (u * e k).re ≤ ‖u * e k‖ := Complex.re_le_norm _
      _ = 1 := by rw [norm_mul, hun, hen, one_mul]
  have hgi : Integrable g ν := (integrable_const 1).sub ((hint.const_mul u).re)
  have hre : ∫ k, (u * e k).re ∂ν = (∫ k, u * e k ∂ν).re := integral_re (hint.const_mul u)
  have hgint : ∫ k, g k ∂ν = 0 := by
    change ∫ k, (1 - (u * e k).re) ∂ν = 0
    rw [integral_sub (f := fun _ : ℤ => (1 : ℝ)) (g := fun k => (u * e k).re)
      (integrable_const 1) ((hint.const_mul u).re), integral_const, probReal_univ,
      one_smul, hre, integral_const_mul, ← hφ, huφ, Complex.one_re, sub_self]
  have hae := (integral_eq_zero_iff_of_nonneg hg0 hgi).1 hgint
  rw [Filter.EventuallyEq, ae_iff_of_countable] at hae
  have heAtom : ∀ k : ℤ, ν {k} ≠ 0 → u * e k = 1 := by
    intro k hk
    have hkr : ν {k} ≠ 0 := hk
    have hz := hae k hkr
    simp only [g, Pi.zero_apply, sub_eq_zero] at hz
    exact eq_one_of_norm_eq_one_of_re_eq_one (by rw [norm_mul, hun, hen, one_mul]) hz.symm
  have hu0 : u ≠ 0 := by
    intro hzero
    have := heAtom z (ne_of_gt hzpos)
    rw [hzero, zero_mul] at this
    exact zero_ne_one this
  have hezw : e z = e w := by
    exact mul_left_cancel₀ hu0 ((heAtom z (ne_of_gt hzpos)).trans (heAtom w (ne_of_gt hwpos)).symm)
  have hphase : cexp (θ * ((z - w : ℤ) : ℂ) * I) = 1 := by
    have hezw' : cexp (θ * (z : ℂ) * I) = cexp (θ * (w : ℂ) * I) := by
      simpa [e] using hezw
    have hsub : cexp (θ * (z : ℂ) * I - θ * (w : ℂ) * I) = 1 := by
      calc cexp (θ * (z : ℂ) * I - θ * (w : ℂ) * I) =
          cexp (θ * (z : ℂ) * I) / cexp (θ * (w : ℂ) * I) := by rw [Complex.exp_sub]
        _ = 1 := by rw [hezw']; exact div_self (Complex.exp_ne_zero _)
    convert hsub using 1
    congr 2
    push_cast
    ring
  have hzw' : ∃ n : ℤ, θ * ((z - w : ℤ) : ℝ) = n * (2 * Real.pi) := by
    rw [Complex.exp_eq_one_iff] at hphase
    obtain ⟨n, hn⟩ := hphase
    refine ⟨n, ?_⟩
    have him := congrArg Complex.im hn
    simpa using him
  have hmem : ∀ d ∈ Ideal.span (supportDiffs ν), cexp (θ * (d : ℂ) * I) = 1 := by
    intro d hd
    induction hd using Submodule.span_induction with
    | mem x hx =>
        obtain ⟨x, y, hx', hy', rfl⟩ := hx
        have h1 := heAtom x hx'
        have h2 := heAtom y hy'
        have hxy : e x = e y := mul_left_cancel₀ hu0 (h1.trans h2.symm)
        have hyne : e y ≠ 0 := by
          intro hz
          have := hen y
          rw [hz, norm_zero] at this
          exact zero_ne_one this
        have : cexp (θ * ((x - y : ℤ) : ℂ) * I) = e x / e y := by
          simp only [he]
          rw [← Complex.exp_sub]
          congr 1
          push_cast
          ring
        rw [this, hxy, div_self hyne]
    | zero => simp
    | add x y _ _ hx hy =>
        rw [show θ * ((x + y : ℤ) : ℂ) * I = θ * (x : ℂ) * I + θ * (y : ℂ) * I by
          push_cast; ring, Complex.exp_add, hx, hy, one_mul]
    | smul c x _ hx =>
        rw [smul_eq_mul,
          show θ * ((c * x : ℤ) : ℂ) * I = (c : ℂ) * (θ * (x : ℂ) * I) by
            push_cast; ring,
          Complex.exp_int_mul, hx, one_zpow]
  have hgmem := hmem _ (Submodule.IsPrincipal.generator_mem (Ideal.span (supportDiffs ν)))
  rw [Complex.exp_eq_one_iff] at hgmem
  obtain ⟨n, hn⟩ := hgmem
  refine ⟨n, ?_⟩
  have hnIm := congrArg Complex.im hn
  simpa [supportDiffGenerator] using hnIm

private theorem norm_stepCF_lt_one (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (hnl : ¬ IsLatticeLaw ν) {θ : ℝ} (h0 : θ ≠ 0) (hθ : |θ| ≤ Real.pi) :
    ‖stepCF ν θ‖ < 1 := by
  rcases (norm_stepCF_le ν θ).lt_or_eq with hlt | heq
  · exact hlt
  · exfalso
    obtain ⟨n, hn⟩ := exists_int_of_norm_stepCF_eq_one ν hnl heq
    have hg := supportDiffGenerator_natAbs_eq_one ν hnl
    have hsq : supportDiffGenerator ν * supportDiffGenerator ν = 1 := by
      have hh : (supportDiffGenerator ν).natAbs = (1 : ℤ).natAbs := by simpa using hg
      have hsquare := (Int.natAbs_eq_iff_sq_eq).1 hh
      nlinarith [hsquare]
    have hg0 : supportDiffGenerator ν ≠ 0 := by
      intro hz
      rw [hz, Int.natAbs_zero] at hg
      norm_num at hg
    have hgpm : supportDiffGenerator ν = 1 ∨ supportDiffGenerator ν = -1 := by
      by_cases hposg : 0 < supportDiffGenerator ν
      · left
        nlinarith
      · right
        have hnegg : supportDiffGenerator ν < 0 :=
          lt_of_le_of_ne (le_of_not_gt hposg) hg0
        nlinarith
    have hval : |θ| = |(n : ℝ)| * (2 * Real.pi) := by
      have hh := congrArg abs hn
      rcases hgpm with hgpm | hgpm
      · rw [hgpm, Int.cast_one, mul_one] at hh
        simpa [abs_mul] using hh
      · rw [hgpm, Int.cast_neg, Int.cast_one] at hh
        simpa [abs_mul] using hh
    have hn0 : n ≠ 0 := by
      intro hnz
      rw [hnz] at hval
      have hθzero : |θ| = 0 := by simpa using hval
      exact h0 (abs_eq_zero.mp hθzero)
    have hn1 : (1 : ℝ) ≤ |(n : ℝ)| := by
      have hnZ : (1 : ℤ) ≤ |n| := Int.one_le_abs hn0
      exact_mod_cast hnZ
    nlinarith [Real.pi_pos]

private theorem exists_norm_stepCF_le_of_le_abs
    (ν : Measure ℤ) [IsProbabilityMeasure ν] (hnl : ¬ IsLatticeLaw ν) {δ : ℝ}
    (hδ : 0 < δ) :
    ∃ q : ℝ, 0 ≤ q ∧ q < 1 ∧ ∀ θ : ℝ, δ ≤ |θ| → |θ| ≤ Real.pi →
      ‖stepCF ν θ‖ ≤ q := by
  let K : Set ℝ := {θ | δ ≤ |θ|} ∩ {θ | |θ| ≤ Real.pi}
  have hKc : IsCompact K := by
    apply Metric.isCompact_of_isClosed_isBounded
    · exact (isClosed_le continuous_const continuous_abs).inter
        (isClosed_le continuous_abs continuous_const)
    · refine (Metric.isBounded_closedBall (x := (0 : ℝ)) (r := Real.pi)).subset ?_
      intro θ hθ
      simpa [Metric.mem_closedBall, Real.dist_eq] using hθ.2
  rcases K.eq_empty_or_nonempty with hKe | hKne
  · refine ⟨0, le_rfl, one_pos, fun θ h1 h2 => ?_⟩
    have : θ ∈ K := ⟨h1, h2⟩
    rw [hKe] at this
    exact absurd this (Set.notMem_empty θ)
  · obtain ⟨θ₀, hθ₀, hmax⟩ := hKc.exists_isMaxOn hKne
      (continuous_norm.comp (continuous_stepCF ν)).continuousOn
    have h0 : θ₀ ≠ 0 := by
      intro h
      change δ ≤ |θ₀| ∧ |θ₀| ≤ Real.pi at hθ₀
      have := hθ₀.1
      rw [h, abs_zero] at this
      linarith
    change δ ≤ |θ₀| ∧ |θ₀| ≤ Real.pi at hθ₀
    refine ⟨‖stepCF ν θ₀‖, norm_nonneg _, norm_stepCF_lt_one ν hnl h0 hθ₀.2,
      fun θ h1 h2 => ?_⟩
    exact hmax ⟨h1, h2⟩



/-- The second derivative of the `n+2` step kernel at scale `√(n+2)`.
Writing the index this way avoids natural-number subtraction at small indices. -/
private noncomputable def secondKernel (ρ : Measure ℤ) (n : ℕ) (t : ℝ) : ℂ :=
  let s := t / Real.sqrt (n + 2)
  ((n + 1 : ℕ) : ℂ) * centeredCF ρ (mean ρ) s ^ n * centeredCF₁ ρ (mean ρ) s ^ 2 +
    centeredCF ρ (mean ρ) s ^ (n + 1) * centeredCF₂ ρ (mean ρ) s

private lemma norm_secondKernel_le {ρ : Measure ℤ} [IsProbabilityMeasure ρ]
    (h : Integrable (fun z : ℤ => (z : ℝ) ^ 2) ρ) (n : ℕ) (t : ℝ) :
    ‖secondKernel ρ n t‖ ≤
      (n + 1 : ℝ) * ‖centeredCF ρ (mean ρ) (t / Real.sqrt (n + 2))‖ ^ n *
        (variance ρ * |t / Real.sqrt (n + 2)|) ^ 2 +
      ‖centeredCF ρ (mean ρ) (t / Real.sqrt (n + 2))‖ ^ (n + 1) * variance ρ := by
  unfold secondKernel
  refine (norm_add_le _ _).trans ?_
  simp only [norm_mul, norm_pow]
  have hc : ‖((n + 1 : ℕ) : ℂ)‖ = (n + 1 : ℝ) := by
    rw [Complex.norm_natCast]
    push_cast
    rfl
  rw [hc]
  gcongr
  · exact norm_centeredCF₁_le h _
  · exact norm_centeredCF₂_le (ρ := ρ) (mean ρ) _

private lemma norm_centeredCF_pow_le_gaussian {ρ : Measure ℤ} [IsProbabilityMeasure ρ]
    {δ : ℝ} (hv : 0 < variance ρ) (_hδ : 0 < δ)
    (hb : ∀ s : ℝ, |s| ≤ δ → ‖centeredCF ρ (mean ρ) s‖ ≤
      Real.exp (-(variance ρ / 4) * s ^ 2))
    {n : ℕ} (hn : 2 ≤ n) {t : ℝ} (ht : |t| ≤ δ * Real.sqrt (n + 2)) :
    ‖centeredCF ρ (mean ρ) (t / Real.sqrt (n + 2))‖ ^ n ≤
      Real.exp (-(variance ρ / 8) * t ^ 2) := by
  have hn0 : (0 : ℝ) < n + 2 := by positivity
  have hs : 0 < Real.sqrt (n + 2 : ℝ) := Real.sqrt_pos.2 hn0
  have hmem : |t / Real.sqrt (n + 2 : ℝ)| ≤ δ := by
    rwa [abs_div, abs_of_pos hs, div_le_iff₀ hs]
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  calc
    _ ≤ (Real.exp (-(variance ρ / 4) * (t / Real.sqrt (n + 2)) ^ 2)) ^ n :=
      pow_le_pow_left₀ (norm_nonneg _) (hb _ hmem) n
    _ = Real.exp (-(variance ρ / 4) * t ^ 2 * ((n : ℝ) / (n + 2))) := by
      rw [← Real.exp_nat_mul]
      congr 1
      rw [div_pow, Real.sq_sqrt hn0.le]
      ring
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      have hratio : (1 / 2 : ℝ) ≤ (n : ℝ) / (n + 2) := by
        rw [le_div_iff₀ hn0]
        linarith
      have hh := mul_le_mul_of_nonpos_left hratio
        (mul_nonpos_of_nonpos_of_nonneg (by linarith : -(variance ρ / 4) ≤ 0) (sq_nonneg t))
      nlinarith

private lemma tendsto_div_sqrt (t : ℝ) :
    Tendsto (fun n : ℕ => t / Real.sqrt (n : ℝ)) atTop (𝓝 0) := by
  simpa only [div_eq_mul_inv, mul_zero, Function.comp_def] using
    (tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp
      tendsto_natCast_atTop_atTop)).const_mul t

private lemma tendsto_centeredCF_pow {ρ : Measure ℤ} [IsProbabilityMeasure ρ]
    (h : Integrable (fun z : ℤ => (z : ℝ) ^ 2) ρ) (t : ℝ) :
    Tendsto (fun n : ℕ => centeredCF ρ (mean ρ) (t / Real.sqrt n) ^ n) atTop
      (𝓝 (cexp (-(variance ρ : ℂ) * (t : ℂ) ^ 2 / 2))) := by
  apply Complex.tendsto_pow_exp_of_isLittleO_sub_add_div
  have ho := (centeredCF_second_order h).comp_tendsto (tendsto_div_sqrt t)
  have aux : (fun n : ℕ => ‖(1 / (n : ℂ))‖) =
      (fun n : ℕ => ‖(1 / (n : ℝ))‖) := by ext n; simp
  rw [← Asymptotics.isLittleO_norm_right, aux, Asymptotics.isLittleO_norm_right]
  refine Asymptotics.IsLittleO.of_const_mul_right (c := t ^ 2) ?_
  convert ho using 2 with n
  · dsimp only [Function.comp_def]
    congr 1
    push_cast
    have hs2 : (Real.sqrt (n : ℝ) : ℂ) ^ 2 = (n : ℂ) := by
      exact_mod_cast Real.sq_sqrt (Nat.cast_nonneg n)
    rw [div_pow, hs2]
    ring
  · rename_i k
    dsimp only [Function.comp_def]
    rw [div_pow, Real.sq_sqrt (Nat.cast_nonneg k)]
    ring

/-- Multiplying the first derivative by the spatial scale yields its linear limit. -/
private lemma tendsto_scaled_centeredCF₁ {ρ : Measure ℤ} [IsProbabilityMeasure ρ]
    (h : Integrable (fun z : ℤ => (z : ℝ) ^ 2) ρ) (t : ℝ) :
    Tendsto (fun n : ℕ => (Real.sqrt n : ℂ) *
      centeredCF₁ ρ (mean ρ) (t / Real.sqrt n)) atTop
      (𝓝 (-(variance ρ : ℂ) * t)) := by
  have ho := (centeredCF₁_first_order h).comp_tendsto (tendsto_div_sqrt t)
  have ho' : (fun n : ℕ => centeredCF₁ ρ (mean ρ) (t / Real.sqrt n) +
      (variance ρ : ℂ) * (t / Real.sqrt n)) =o[atTop]
      (fun n : ℕ => (Real.sqrt (n : ℝ))⁻¹) := by
    apply Asymptotics.IsLittleO.of_const_mul_right (c := t)
    simpa only [div_eq_mul_inv, Function.comp_def, Complex.ofReal_mul,
      Complex.ofReal_inv, Complex.ofReal_div] using ho
  have hh := ho'.tendsto_inv_smul_nhds_zero
  have he : (fun n : ℕ => (Real.sqrt n : ℂ) *
      centeredCF₁ ρ (mean ρ) (t / Real.sqrt n)) =ᶠ[atTop]
      (fun n : ℕ => ((Real.sqrt (n : ℝ))⁻¹)⁻¹ •
        (centeredCF₁ ρ (mean ρ) (t / Real.sqrt n) +
          (variance ρ : ℂ) * (t / Real.sqrt n)) - (variance ρ : ℂ) * t) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hs : (Real.sqrt (n : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_pos.2 (show (0 : ℝ) < n by exact_mod_cast hn)).ne'
    simp only [inv_inv, Complex.real_smul]
    field_simp
    ring
  convert (hh.sub_const ((variance ρ : ℂ) * t)).congr' he.symm using 1
  simp

private lemma norm_secondKernel_le_gaussian {ρ : Measure ℤ} [IsProbabilityMeasure ρ]
    (h : Integrable (fun z : ℤ => (z : ℝ) ^ 2) ρ) {δ : ℝ}
    (hv : 0 < variance ρ) (hδ : 0 < δ)
    (hb : ∀ s : ℝ, |s| ≤ δ → ‖centeredCF ρ (mean ρ) s‖ ≤
      Real.exp (-(variance ρ / 4) * s ^ 2))
    {n : ℕ} (hn : 2 ≤ n) {t : ℝ} (ht : |t| ≤ δ * Real.sqrt (n + 2)) :
    ‖secondKernel ρ n t‖ ≤ (variance ρ ^ 2 * t ^ 2 + variance ρ) *
      Real.exp (-(variance ρ / 8) * t ^ 2) := by
  have hn0 : (0 : ℝ) < n + 2 := by positivity
  have hb1 : ‖centeredCF ρ (mean ρ) (t / Real.sqrt (n + 2))‖ ≤ 1 := by
    rw [norm_centeredCF]
    exact norm_stepCF_le ρ _
  have hpow := norm_centeredCF_pow_le_gaussian hv hδ hb hn ht
  have hpow1 : ‖centeredCF ρ (mean ρ) (t / Real.sqrt (n + 2))‖ ^ (n + 1) ≤
      Real.exp (-(variance ρ / 8) * t ^ 2) := by
    rw [pow_succ]
    exact (mul_le_of_le_one_right (pow_nonneg (norm_nonneg _) _) hb1).trans hpow
  have hcoef : (n + 1 : ℝ) * (variance ρ * |t / Real.sqrt (n + 2)|) ^ 2 ≤
      variance ρ ^ 2 * t ^ 2 := by
    calc
      _ = (variance ρ ^ 2 * t ^ 2) * ((n + 1 : ℝ) / (n + 2)) := by
        rw [mul_pow, sq_abs, div_pow, Real.sq_sqrt hn0.le]
        ring
      _ ≤ (variance ρ ^ 2 * t ^ 2) * 1 := by
        gcongr
        rw [div_le_one hn0]
        linarith
      _ = _ := mul_one _
  calc
    _ ≤ _ := norm_secondKernel_le h n t
    _ ≤ Real.exp (-(variance ρ / 8) * t ^ 2) *
        ((n + 1 : ℝ) * (variance ρ * |t / Real.sqrt (n + 2)|) ^ 2) +
        Real.exp (-(variance ρ / 8) * t ^ 2) * variance ρ := by
      have hmul := mul_le_mul_of_nonneg_right hpow
        (show 0 ≤ (n + 1 : ℝ) * (variance ρ * |t / Real.sqrt (n + 2)|) ^ 2 by positivity)
      have hmul1 := mul_le_mul_of_nonneg_right hpow1 hv.le
      nlinarith [hmul, hmul1]
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_left hcoef
        (Real.exp_pos (-(variance ρ / 8) * t ^ 2)).le
      nlinarith

private noncomputable def gaussianSecondKernel (v t : ℝ) : ℂ :=
  ((v : ℂ) ^ 2 * (t : ℂ) ^ 2 - v) * cexp (-(v : ℂ) * (t : ℂ) ^ 2 / 2)

private lemma tendsto_secondKernel {ρ : Measure ℤ} [IsProbabilityMeasure ρ]
    (h : Integrable (fun z : ℤ => (z : ℝ) ^ 2) ρ) (t : ℝ) :
    Tendsto (fun n => secondKernel ρ n t) atTop
      (𝓝 (gaussianSecondKernel (variance ρ) t)) := by
  let s : ℕ → ℝ := fun n => t / Real.sqrt (n + 2)
  let u : ℕ → ℂ := fun n => centeredCF ρ (mean ρ) (s n)
  let G : ℂ := cexp (-(variance ρ : ℂ) * (t : ℂ) ^ 2 / 2)
  have hs : Tendsto s atTop (𝓝 0) := by
    simpa [s, Function.comp_def, Nat.cast_add, Nat.cast_ofNat] using
      (tendsto_div_sqrt t).comp (tendsto_add_atTop_nat 2)
  have hu : Tendsto u atTop (𝓝 1) := by
    simpa [u, Function.comp_def, centeredCF_zero] using
      ((hasDerivAt_centeredCF (integrable_cast_of_sq h) (mean ρ) 0).continuousAt.tendsto).comp hs
  have hne : ∀ᶠ n in atTop, u n ≠ 0 := hu.eventually (eventually_ne_nhds one_ne_zero)
  have hp : Tendsto (fun n => u n ^ (n + 2)) atTop (𝓝 G) := by
    simpa [u, s, G, Function.comp_def, Nat.cast_add, Nat.cast_ofNat] using
      (tendsto_centeredCF_pow h t).comp (tendsto_add_atTop_nat 2)
  have hp₀ : Tendsto (fun n => u n ^ n) atTop (𝓝 G) := by
    have hh := hp.div (hu.pow 2) (by norm_num : (1 : ℂ) ^ 2 ≠ 0)
    simp only [one_pow, div_one] at hh
    apply hh.congr'
    filter_upwards [hne] with n hn
    dsimp only [Pi.div_apply]
    rw [pow_add, mul_div_cancel_right₀ _ (pow_ne_zero _ hn)]
  have hp₁ : Tendsto (fun n => u n ^ (n + 1)) atTop (𝓝 G) := by
    simpa only [pow_succ, mul_one] using hp₀.mul hu
  have hr : Tendsto (fun n : ℕ => (Real.sqrt (n + 2) : ℂ) *
      centeredCF₁ ρ (mean ρ) (s n)) atTop (𝓝 (-(variance ρ : ℂ) * t)) := by
    simpa [s, Function.comp_def, Nat.cast_add, Nat.cast_ofNat] using
      (tendsto_scaled_centeredCF₁ h t).comp (tendsto_add_atTop_nat 2)
  have hratio : Tendsto (fun n : ℕ => ((n + 1 : ℝ) / (n + 2))) atTop (𝓝 1) := by
    have hh := (tendsto_const_nhds (x := (1 : ℝ))).sub
      (tendsto_inv_atTop_zero.comp
        (tendsto_natCast_atTop_atTop.atTop_add (tendsto_const_nhds (x := (2 : ℝ)))))
    simp only [sub_zero] at hh
    apply hh.congr'
    exact Eventually.of_forall fun n => by
      dsimp only [Function.comp_def]
      field_simp
      ring
  have hlin : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℂ) *
      centeredCF₁ ρ (mean ρ) (s n) ^ 2) atTop
      (𝓝 ((variance ρ : ℂ) ^ 2 * (t : ℂ) ^ 2)) := by
    have hh := (Complex.continuous_ofReal.tendsto 1 |>.comp hratio).mul (hr.pow 2)
    have heq (n : ℕ) : (((n + 1 : ℝ) / (n + 2) : ℝ) : ℂ) *
        ((Real.sqrt (n + 2) : ℂ) * centeredCF₁ ρ (mean ρ) (s n)) ^ 2 =
        ((n + 1 : ℕ) : ℂ) * centeredCF₁ ρ (mean ρ) (s n) ^ 2 := by
      have hs2 : (Real.sqrt (n + 2 : ℝ) : ℂ) ^ 2 = ((n : ℂ) + 2) := by
        exact_mod_cast Real.sq_sqrt (show (0 : ℝ) ≤ n + 2 by positivity)
      have hn0 : (n : ℂ) + 2 ≠ 0 := by exact_mod_cast (show (n : ℝ) + 2 ≠ 0 by positivity)
      push_cast
      rw [mul_pow, hs2]
      field_simp
    simp only [Function.comp_def] at hh
    simp_rw [heq] at hh
    convert hh using 1
    congr 1
    simp only [Complex.ofReal_one, one_mul, neg_mul, neg_sq, mul_pow]
  have h₂ : Tendsto (fun n => centeredCF₂ ρ (mean ρ) (s n)) atTop
      (𝓝 (-(variance ρ : ℂ))) := by
    simpa [Function.comp_def, centeredCF₂_zero] using (continuous_centeredCF₂ h (mean ρ)).tendsto 0 |>.comp hs
  have hh := (hlin.mul hp₀).add (hp₁.mul h₂)
  convert hh using 1
  · funext n
    dsimp [secondKernel, u, s]
    ring
  · congr 1
    dsimp [gaussianSecondKernel, G]
    ring

private lemma norm_secondKernel_le_geometric {ρ : Measure ℤ} [IsProbabilityMeasure ρ]
    (h : Integrable (fun z : ℤ => (z : ℝ) ^ 2) ρ) {q : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) {n : ℕ} {t : ℝ}
    (hcf : ‖centeredCF ρ (mean ρ) (t / Real.sqrt (n + 2))‖ ≤ q)
    (ht : |t / Real.sqrt (n + 2)| ≤ Real.pi) :
    ‖secondKernel ρ n t‖ ≤ ((n + 1 : ℝ) * (variance ρ * Real.pi) ^ 2 + variance ρ) * q ^ n := by
  have hv : 0 ≤ variance ρ := integral_nonneg fun _ => sq_nonneg _
  have hp : ‖centeredCF ρ (mean ρ) (t / Real.sqrt (n + 2))‖ ^ (n + 1) ≤ q ^ n := by
    calc
      _ ≤ q ^ (n + 1) := pow_le_pow_left₀ (norm_nonneg _) hcf _
      _ ≤ q ^ n := by rw [pow_succ]; exact mul_le_of_le_one_right (pow_nonneg hq0 _) hq1
  calc
    _ ≤ _ := norm_secondKernel_le h n t
    _ ≤ (n + 1 : ℝ) * q ^ n * (variance ρ * Real.pi) ^ 2 + q ^ n * variance ρ := by
      gcongr
    _ = _ := by ring

private lemma integrable_gaussianEnvelope (v : ℝ) {c : ℝ} (hc : 0 < c) :
    Integrable (fun t : ℝ => (v ^ 2 * t ^ 2 + v) * Real.exp (-c * t ^ 2)) := by
  have hi₀ : Integrable (fun t : ℝ => Real.exp (-c * t ^ 2)) := by
    simpa using (integrable_rpow_abs_mul_exp_neg (s := 0) (p := 2) (c := c)
      (by norm_num) (by norm_num) hc)
  have hi₂ : Integrable (fun t : ℝ => t ^ 2 * Real.exp (-c * t ^ 2)) := by
    simpa [Real.rpow_two] using (integrable_rpow_abs_mul_exp_neg (s := 2) (p := 2) (c := c)
      (by norm_num) (by norm_num) hc)
  convert (hi₂.const_mul (v ^ 2)).add (hi₀.const_mul v) using 1
  funext t
  dsimp
  ring

private lemma norm_gaussianSecondKernel_le {v : ℝ} (hv : 0 ≤ v) (t : ℝ) :
    ‖gaussianSecondKernel v t‖ ≤ (v ^ 2 * t ^ 2 + v) * Real.exp (-(v / 2) * t ^ 2) := by
  have he : cexp (-(v : ℂ) * (t : ℂ) ^ 2 / 2) =
      (Real.exp (-(v / 2) * t ^ 2) : ℂ) := by
    rw [Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  have hp : (v : ℂ) ^ 2 * (t : ℂ) ^ 2 - v = ((v ^ 2 * t ^ 2 - v : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [gaussianSecondKernel, norm_mul, he, hp, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
  have hh := abs_sub (v ^ 2 * t ^ 2) v
  simpa only [abs_of_nonneg (mul_nonneg (sq_nonneg v) (sq_nonneg t)), abs_of_nonneg hv] using hh

private lemma integrable_gaussianSecondKernel {v : ℝ} (hv : 0 < v) :
    Integrable (gaussianSecondKernel v) := by
  apply Integrable.mono' (integrable_gaussianEnvelope v (by positivity : 0 < v / 2))
    (by unfold gaussianSecondKernel; fun_prop)
  exact Eventually.of_forall fun t => norm_gaussianSecondKernel_le hv.le t

/-- On the annulus, `n` is comparable to `t²`, so the geometric tail also
admits an integrable Gaussian envelope independent of `n`. -/
private lemma norm_secondKernel_annulus {ρ : Measure ℤ} [IsProbabilityMeasure ρ]
    (h : Integrable (fun z : ℤ => (z : ℝ) ^ 2) ρ) {q δ : ℝ}
    (hq0 : 0 < q) (hq1 : q < 1) (hδ : 0 < δ) {n : ℕ} (hn : 2 ≤ n) {t : ℝ}
    (hcf : ‖centeredCF ρ (mean ρ) (t / Real.sqrt (n + 2))‖ ≤ q)
    (htlo : δ ≤ |t / Real.sqrt (n + 2)|)
    (hthi : |t / Real.sqrt (n + 2)| ≤ Real.pi) :
    ‖secondKernel ρ n t‖ ≤
      ((variance ρ * Real.pi) ^ 2 / δ ^ 2 * t ^ 2 + variance ρ) *
        Real.exp (-(-Real.log q / (2 * Real.pi ^ 2)) * t ^ 2) := by
  have hv : 0 ≤ variance ρ := integral_nonneg fun _ => sq_nonneg _
  have hn0 : (0 : ℝ) < n + 2 := by positivity
  have hs : 0 < Real.sqrt (n + 2 : ℝ) := Real.sqrt_pos.2 hn0
  have hl : δ * Real.sqrt (n + 2 : ℝ) ≤ |t| := by
    rwa [abs_div, abs_of_pos hs, le_div_iff₀ hs] at htlo
  have hu : |t| ≤ Real.pi * Real.sqrt (n + 2 : ℝ) := by
    rwa [abs_div, abs_of_pos hs, div_le_iff₀ hs] at hthi
  have hl2 := (sq_le_sq₀ (by positivity : 0 ≤ δ * Real.sqrt (n + 2 : ℝ))
    (abs_nonneg t)).2 hl
  have hu2 := (sq_le_sq₀ (abs_nonneg t)
    (by positivity : 0 ≤ Real.pi * Real.sqrt (n + 2 : ℝ))).2 hu
  rw [mul_pow, Real.sq_sqrt hn0.le, sq_abs] at hl2
  rw [mul_pow, Real.sq_sqrt hn0.le, sq_abs] at hu2
  have hcoef : (n + 1 : ℝ) * (variance ρ * Real.pi) ^ 2 ≤
      (variance ρ * Real.pi) ^ 2 / δ ^ 2 * t ^ 2 := by
    rw [div_mul_eq_mul_div, le_div_iff₀ (sq_pos_of_pos hδ)]
    have hh := mul_le_mul_of_nonneg_left hl2 (sq_nonneg (variance ρ * Real.pi))
    nlinarith [mul_nonneg (sq_nonneg δ) (sq_nonneg (variance ρ * Real.pi))]
  have hqpow : q ^ n ≤ Real.exp (-(-Real.log q / (2 * Real.pi ^ 2)) * t ^ 2) := by
    have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have hratio : t ^ 2 / (2 * Real.pi ^ 2) ≤ (n : ℝ) := by
      rw [div_le_iff₀ (by positivity : 0 < 2 * Real.pi ^ 2)]
      nlinarith [sq_nonneg Real.pi]
    calc
      _ = Real.exp ((n : ℝ) * Real.log q) := by
        rw [Real.exp_nat_mul, Real.exp_log hq0]
      _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        have hh := mul_le_mul_of_nonpos_left hratio (Real.log_neg hq0 hq1).le
        convert hh using 1 <;> ring
  calc
    _ ≤ _ := norm_secondKernel_le_geometric h hq0.le hq1.le hcf hthi
    _ ≤ _ := mul_le_mul (by linarith) hqpow (pow_nonneg hq0.le _)
      (by positivity)

private lemma integrable_quadratic_gaussian (A B : ℝ) {c : ℝ} (hc : 0 < c) :
    Integrable (fun t : ℝ => (A * t ^ 2 + B) * Real.exp (-c * t ^ 2)) := by
  have hi₀ : Integrable (fun t : ℝ => Real.exp (-c * t ^ 2)) := by
    simpa using (integrable_rpow_abs_mul_exp_neg (s := 0) (p := 2) (c := c)
      (by norm_num) (by norm_num) hc)
  have hi₂ : Integrable (fun t : ℝ => t ^ 2 * Real.exp (-c * t ^ 2)) := by
    simpa [Real.rpow_two] using (integrable_rpow_abs_mul_exp_neg (s := 2) (p := 2) (c := c)
      (by norm_num) (by norm_num) hc)
  convert (hi₂.const_mul A).add (hi₀.const_mul B) using 1
  funext t
  dsimp
  ring

private lemma exists_secondKernel_envelope {ρ : Measure ℤ} [IsProbabilityMeasure ρ]
    (hnl : ¬ IsLatticeLaw ρ) (h : Integrable (fun z : ℤ => (z : ℝ) ^ 2) ρ) :
    ∃ D : ℝ → ℝ, Integrable D ∧ (∀ t, 0 ≤ D t) ∧
      ∀ n : ℕ, 2 ≤ n → ∀ t : ℝ, |t| ≤ Real.pi * Real.sqrt (n + 2) →
        ‖secondKernel ρ n t‖ ≤ D t := by
  have hv := variance_pos_of_nonlattice hnl h
  obtain ⟨δ, hδ, hb⟩ := exists_norm_centeredCF_le_exp hnl h
  obtain ⟨q₀, hq₀, hq₀1, hqbd⟩ := exists_norm_stepCF_le_of_le_abs ρ hnl hδ
  let q := (q₀ + 1) / 2
  have hq0 : 0 < q := by dsimp [q]; linarith
  have hq1 : q < 1 := by dsimp [q]; linarith
  have hqq : q₀ ≤ q := by dsimp [q]; linarith
  let c := -Real.log q / (2 * Real.pi ^ 2)
  have hc : 0 < c := div_pos (neg_pos.2 (Real.log_neg hq0 hq1)) (by positivity)
  let A := (variance ρ * Real.pi) ^ 2 / δ ^ 2
  let D : ℝ → ℝ := fun t =>
    (variance ρ ^ 2 * t ^ 2 + variance ρ) * Real.exp (-(variance ρ / 8) * t ^ 2) +
      (A * t ^ 2 + variance ρ) * Real.exp (-c * t ^ 2)
  refine ⟨D, (integrable_quadratic_gaussian _ _ (by positivity : 0 < variance ρ / 8)).add
    (integrable_quadratic_gaussian A (variance ρ) hc), ?_, ?_⟩
  · intro t
    dsimp [D, A]
    positivity
  · intro n hn t ht
    by_cases htδ : |t| ≤ δ * Real.sqrt (n + 2)
    · have hh := norm_secondKernel_le_gaussian h hv hδ hb hn htδ
      have hd : 0 ≤ (A * t ^ 2 + variance ρ) * Real.exp (-c * t ^ 2) := by
        dsimp [A]; positivity
      exact hh.trans (le_add_of_nonneg_right hd)
    · have hs : 0 < Real.sqrt (n + 2 : ℝ) := by positivity
      have hlo : δ ≤ |t / Real.sqrt (n + 2 : ℝ)| := by
        rw [abs_div, abs_of_pos hs, le_div_iff₀ hs]
        exact (lt_of_not_ge htδ).le
      have hhi : |t / Real.sqrt (n + 2 : ℝ)| ≤ Real.pi := by
        rwa [abs_div, abs_of_pos hs, div_le_iff₀ hs]
      have hcf : ‖centeredCF ρ (mean ρ) (t / Real.sqrt (n + 2))‖ ≤ q := by
        rw [norm_centeredCF]
        exact (hqbd _ hlo hhi).trans hqq
      have hh := norm_secondKernel_annulus h hq0 hq1 hδ hn hcf hlo hhi
      have hd : 0 ≤ (variance ρ ^ 2 * t ^ 2 + variance ρ) *
          Real.exp (-(variance ρ / 8) * t ^ 2) := by positivity
      exact hh.trans (le_add_of_nonneg_left hd)

private noncomputable def truncateKernel (K : ℕ → ℝ → ℂ) (n : ℕ) (t : ℝ) : ℂ :=
  (Ioc (-(Real.pi * Real.sqrt (n + 2))) (Real.pi * Real.sqrt (n + 2))).indicator (K n) t

/-- A single global envelope packages both the central and annular estimates. -/
private lemma tendsto_integral_norm_truncateKernel_sub
    {K : ℕ → ℝ → ℂ} {G : ℝ → ℂ} {D : ℝ → ℝ}
    (hK : ∀ n, Continuous (K n)) (hG : Integrable G) (hD : Integrable D)
    (hD0 : ∀ t, 0 ≤ D t)
    (hb : ∀ n : ℕ, 2 ≤ n → ∀ t : ℝ,
      |t| ≤ Real.pi * Real.sqrt (n + 2) → ‖K n t‖ ≤ D t)
    (hl : ∀ t, Tendsto (fun n => K n t) atTop (𝓝 (G t))) :
    Tendsto (fun n => ∫ t, ‖truncateKernel K n t - G t‖) atTop (𝓝 0) := by
  have hat : Tendsto (fun n : ℕ => Real.pi * Real.sqrt (n + 2)) atTop atTop := by
    simpa only [Function.comp_def] using
      (Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop.atTop_add
        (tendsto_const_nhds (x := (2 : ℝ))))).const_mul_atTop Real.pi_pos
  have hzero : (0 : ℝ) = ∫ _ : ℝ, (0 : ℝ) := by simp
  rw [hzero]
  apply tendsto_integral_filter_of_dominated_convergence (fun t => D t + ‖G t‖)
  · exact Eventually.of_forall fun n =>
      (((hK n).aestronglyMeasurable.indicator measurableSet_Ioc).sub
        hG.aestronglyMeasurable).norm
  · filter_upwards [eventually_ge_atTop 2] with n hn
    exact Eventually.of_forall fun t => by
      rw [norm_norm]
      apply (norm_sub_le _ _).trans
      gcongr
      unfold truncateKernel
      by_cases ht : t ∈ Ioc (-(Real.pi * Real.sqrt (n + 2))) (Real.pi * Real.sqrt (n + 2))
      · rw [indicator_of_mem ht]
        apply hb n hn t
        have hh := ht
        simp only [mem_Ioc] at hh
        exact abs_le.2 ⟨hh.1.le, hh.2⟩
      · rw [indicator_of_notMem ht, norm_zero]
        exact hD0 t
  · exact hD.add hG.norm
  · exact Eventually.of_forall fun t => by
      have hev : ∀ᶠ (n : ℕ) in atTop, t ∈
          Ioc (-(Real.pi * Real.sqrt (n + 2))) (Real.pi * Real.sqrt (n + 2)) := by
        filter_upwards [hat.eventually_gt_atTop |t|] with n hn
        exact ⟨by linarith [neg_abs_le t], by linarith [le_abs_self t]⟩
      have hh0 : Tendsto (fun n => K n t - G t) atTop (𝓝 (0 : ℂ)) := by
        simpa only [sub_self] using (hl t).sub_const (G t)
      have hh : Tendsto (fun n => truncateKernel K n t - G t) atTop (𝓝 0) := by
        apply hh0.congr'
        filter_upwards [hev] with n hn
        simp only [truncateKernel, indicator_of_mem hn]
      simpa only [Function.comp_def, norm_zero] using continuous_norm.tendsto 0 |>.comp hh

/-- L¹ convergence of the rescaled second-derivative Fourier kernels. -/
private lemma tendsto_integral_norm_secondKernel_sub {ρ : Measure ℤ} [IsProbabilityMeasure ρ]
    (hnl : ¬ IsLatticeLaw ρ) (h : Integrable (fun z : ℤ => (z : ℝ) ^ 2) ρ) :
    Tendsto (fun n => ∫ t, ‖truncateKernel (secondKernel ρ) n t -
      gaussianSecondKernel (variance ρ) t‖) atTop (𝓝 0) := by
  obtain ⟨D, hDi, hD0, hbd⟩ := exists_secondKernel_envelope hnl h
  apply tendsto_integral_norm_truncateKernel_sub _
    (integrable_gaussianSecondKernel (variance_pos_of_nonlattice hnl h)) hDi hD0 hbd
    (tendsto_secondKernel h)
  intro n
  have hc : Continuous (centeredCF ρ (mean ρ)) := continuous_iff_continuousAt.2
    fun t => (hasDerivAt_centeredCF (integrable_cast_of_sq h) (mean ρ) t).continuousAt
  have hc₁ : Continuous (centeredCF₁ ρ (mean ρ)) := continuous_iff_continuousAt.2
    fun t => (hasDerivAt_centeredCF₁ h (mean ρ) t).continuousAt
  have hc₂ := continuous_centeredCF₂ h (mean ρ)
  unfold secondKernel
  fun_prop

private noncomputable def zerothKernel (ρ : Measure ℤ) (n : ℕ) (t : ℝ) : ℂ :=
  centeredCF ρ (mean ρ) (t / Real.sqrt (n + 2)) ^ (n + 2)

private noncomputable def gaussianKernel (v t : ℝ) : ℂ :=
  cexp (-(v : ℂ) * (t : ℂ) ^ 2 / 2)

private lemma norm_gaussianKernel (v t : ℝ) :
    ‖gaussianKernel v t‖ = Real.exp (-(v / 2) * t ^ 2) := by
  have he : gaussianKernel v t = (Real.exp (-(v / 2) * t ^ 2) : ℂ) := by
    rw [gaussianKernel, Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  rw [he, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]

private lemma integrable_gaussianKernel {v : ℝ} (hv : 0 < v) : Integrable (gaussianKernel v) := by
  apply Integrable.mono' (integrable_quadratic_gaussian 0 1 (by positivity : 0 < v / 2))
    (by unfold gaussianKernel; fun_prop)
  exact Eventually.of_forall fun t => by simp only [norm_gaussianKernel, zero_mul, zero_add, one_mul, le_refl]

private lemma exists_zerothKernel_envelope {ρ : Measure ℤ} [IsProbabilityMeasure ρ]
    (hnl : ¬ IsLatticeLaw ρ) (h : Integrable (fun z : ℤ => (z : ℝ) ^ 2) ρ) :
    ∃ D : ℝ → ℝ, Integrable D ∧ (∀ t, 0 ≤ D t) ∧
      ∀ n : ℕ, 2 ≤ n → ∀ t : ℝ, |t| ≤ Real.pi * Real.sqrt (n + 2) →
        ‖zerothKernel ρ n t‖ ≤ D t := by
  have hv := variance_pos_of_nonlattice hnl h
  obtain ⟨δ, hδ, hb⟩ := exists_norm_centeredCF_le_exp hnl h
  obtain ⟨q₀, hq₀, hq₀1, hqbd⟩ := exists_norm_stepCF_le_of_le_abs ρ hnl hδ
  let q := (q₀ + 1) / 2
  have hq0 : 0 < q := by dsimp [q]; linarith
  have hq1 : q < 1 := by dsimp [q]; linarith
  have hqq : q₀ ≤ q := by dsimp [q]; linarith
  let c := -Real.log q / (2 * Real.pi ^ 2)
  have hc : 0 < c := div_pos (neg_pos.2 (Real.log_neg hq0 hq1)) (by positivity)
  let D : ℝ → ℝ := fun t => Real.exp (-(variance ρ / 8) * t ^ 2) + Real.exp (-c * t ^ 2)
  have hi₁ : Integrable (fun t : ℝ => Real.exp (-(variance ρ / 8) * t ^ 2)) := by
    simpa using integrable_quadratic_gaussian 0 1 (by positivity : 0 < variance ρ / 8)
  have hi₂ : Integrable (fun t : ℝ => Real.exp (-c * t ^ 2)) := by
    simpa using integrable_quadratic_gaussian 0 1 hc
  refine ⟨D, hi₁.add hi₂, fun t => by dsimp [D]; positivity, fun n hn t ht => ?_⟩
  have hn0 : (0 : ℝ) < n + 2 := by positivity
  have hs : 0 < Real.sqrt (n + 2 : ℝ) := Real.sqrt_pos.2 hn0
  have hb1 : ‖centeredCF ρ (mean ρ) (t / Real.sqrt (n + 2))‖ ≤ 1 := by
    rw [norm_centeredCF]; exact norm_stepCF_le ρ _
  have hp : ‖zerothKernel ρ n t‖ ≤ ‖centeredCF ρ (mean ρ) (t / Real.sqrt (n + 2))‖ ^ n := by
    rw [zerothKernel, norm_pow, pow_add]
    exact mul_le_of_le_one_right (pow_nonneg (norm_nonneg _) _) (pow_le_one₀ (norm_nonneg _) hb1)
  by_cases htδ : |t| ≤ δ * Real.sqrt (n + 2)
  · exact hp.trans ((norm_centeredCF_pow_le_gaussian hv hδ hb hn htδ).trans
      (le_add_of_nonneg_right (Real.exp_pos _).le))
  · have hlo : δ ≤ |t / Real.sqrt (n + 2 : ℝ)| := by
      rw [abs_div, abs_of_pos hs, le_div_iff₀ hs]
      exact (lt_of_not_ge htδ).le
    have hhi : |t / Real.sqrt (n + 2 : ℝ)| ≤ Real.pi := by
      rwa [abs_div, abs_of_pos hs, div_le_iff₀ hs]
    have hcf : ‖centeredCF ρ (mean ρ) (t / Real.sqrt (n + 2))‖ ≤ q := by
      rw [norm_centeredCF]
      exact (hqbd _ hlo hhi).trans hqq
    have hu2 := (sq_le_sq₀ (abs_nonneg t)
      (by positivity : 0 ≤ Real.pi * Real.sqrt (n + 2 : ℝ))).2 ht
    rw [sq_abs, mul_pow, Real.sq_sqrt hn0.le] at hu2
    have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have hratio : t ^ 2 / (2 * Real.pi ^ 2) ≤ (n : ℝ) := by
      rw [div_le_iff₀ (by positivity : 0 < 2 * Real.pi ^ 2)]
      nlinarith [sq_nonneg Real.pi]
    have hqpow : q ^ n ≤ Real.exp (-c * t ^ 2) := by
      calc
        _ = Real.exp ((n : ℝ) * Real.log q) := by rw [Real.exp_nat_mul, Real.exp_log hq0]
        _ ≤ _ := by
          apply Real.exp_le_exp.mpr
          have hh := mul_le_mul_of_nonpos_left hratio (Real.log_neg hq0 hq1).le
          dsimp [c]
          convert hh using 1 <;> ring
    exact hp.trans ((pow_le_pow_left₀ (norm_nonneg _) hcf n).trans
      (hqpow.trans (le_add_of_nonneg_left (Real.exp_pos _).le)))

private lemma tendsto_integral_norm_zerothKernel_sub {ρ : Measure ℤ} [IsProbabilityMeasure ρ]
    (hnl : ¬ IsLatticeLaw ρ) (h : Integrable (fun z : ℤ => (z : ℝ) ^ 2) ρ) :
    Tendsto (fun n => ∫ t, ‖truncateKernel (zerothKernel ρ) n t -
      gaussianKernel (variance ρ) t‖) atTop (𝓝 0) := by
  obtain ⟨D, hDi, hD0, hbd⟩ := exists_zerothKernel_envelope hnl h
  have hcK (n : ℕ) : Continuous (zerothKernel ρ n) := by
    have hc : Continuous (centeredCF ρ (mean ρ)) := continuous_iff_continuousAt.2
      fun t => (hasDerivAt_centeredCF (integrable_cast_of_sq h) (mean ρ) t).continuousAt
    unfold zerothKernel
    fun_prop
  have hpt (t : ℝ) : Tendsto (fun n => zerothKernel ρ n t) atTop
      (𝓝 (gaussianKernel (variance ρ) t)) := by
    simpa [zerothKernel, gaussianKernel, Function.comp_def, Nat.cast_add, Nat.cast_ofNat] using
      (tendsto_centeredCF_pow h t).comp (tendsto_add_atTop_nat 2)
  exact tendsto_integral_norm_truncateKernel_sub hcK
    (integrable_gaussianKernel (variance_pos_of_nonlattice hnl h)) hDi hD0 hbd hpt
private noncomputable def walkCF (ν : Measure ℤ) (n : ℕ) (θ : ℝ) : ℂ :=
  ∫ z, cexp (θ * (z : ℂ) * I) ∂(intWalk ν n)

private instance intWalk_isProbabilityMeasure (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (n : ℕ) : IsProbabilityMeasure (intWalk ν n) := by
  induction n with
  | zero => simp only [intWalk]; infer_instance
  | succ n ih => simpa only [intWalk] using (inferInstance : IsProbabilityMeasure ((intWalk ν n) ∗ ν))

private theorem walkCF_eq_pow (ν : Measure ℤ) [IsProbabilityMeasure ν] (n : ℕ) (θ : ℝ) :
    walkCF ν n θ = stepCF ν θ ^ n := by
  induction n with
  | zero =>
      simp only [walkCF, intWalk, integral_dirac]
      simp
  | succ n ih =>
      rw [pow_succ, ← ih, walkCF, intWalk, integral_conv_int]
      have hsum : ∀ p : ℤ × ℤ,
          cexp (θ * ((p.1 + p.2 : ℤ) : ℂ) * I) =
            cexp (θ * (p.1 : ℂ) * I) * cexp (θ * (p.2 : ℂ) * I) := by
        intro p
        rw [← Complex.exp_add]
        congr 1
        push_cast
        ring
      simp_rw [hsum]
      rw [integral_prod_mul (fun x : ℤ => cexp (θ * (x : ℂ) * I))
        (fun y : ℤ => cexp (θ * (y : ℂ) * I))]
      rfl


private noncomputable def truncCF (ν : Measure ℤ) (m : ℝ) (a : ℕ → ℝ)
    (n : ℕ) (t : ℝ) : ℂ :=
  (Ioc (-(Real.pi * a n)) (Real.pi * a n)).indicator
    (fun t => centeredCF ν m (t / a n) ^ n) t

private theorem intWalk_real_singleton (ν : Measure ℤ) [IsProbabilityMeasure ν] (n : ℕ) (k : ℤ) :
    (((intWalk ν n).real {k} : ℝ) : ℂ) =
      (1 / (2 * Real.pi)) * ∫ θ in (-Real.pi)..Real.pi, stepCF ν θ ^ n * cexp (-(θ * k * I)) := by
  rw [intervalIntegral.integral_of_le (by linarith [Real.pi_pos])]
  have hswap : ∫ θ in Ioc (-Real.pi) Real.pi, stepCF ν θ ^ n * cexp (-(θ * k * I)) =
      ∫ z, ∫ θ in Ioc (-Real.pi) Real.pi, cexp (θ * ((z - k : ℤ) : ℝ) * I) ∂volume
        ∂(intWalk ν n) := by
    have h1 : ∀ θ : ℝ, stepCF ν θ ^ n * cexp (-(θ * k * I)) =
        ∫ z, cexp (θ * ((z - k : ℤ) : ℝ) * I) ∂(intWalk ν n) := by
      intro θ
      rw [← walkCF_eq_pow, walkCF, ← integral_mul_const]
      congr 1; funext z
      rw [← Complex.exp_add]; congr 1; push_cast; ring
    simp_rw [h1]
    apply integral_integral_swap
    apply Integrable.of_bound (C := 1)
    · apply Measurable.aestronglyMeasurable
      apply measurable_from_prod_countable_left
      intro z
      fun_prop
    · refine Eventually.of_forall fun p => ?_
      obtain ⟨x, y⟩ := p
      simp only [Function.uncurry_apply_pair]
      rw [show ((x : ℂ) * (((y - k : ℤ) : ℝ) : ℂ) * I) = ((x * ((y - k : ℤ) : ℝ) : ℝ) : ℂ) * I by
        push_cast; ring, Complex.norm_exp_ofReal_mul_I]
  rw [hswap]
  have h2 : ∀ z : ℤ, ∫ θ in Ioc (-Real.pi) Real.pi, cexp (θ * ((z - k : ℤ) : ℝ) * I) =
      ({k} : Set ℤ).indicator (fun _ => ((2 * Real.pi : ℝ) : ℂ)) z := by
    intro z
    rw [← intervalIntegral.integral_of_le (by linarith [Real.pi_pos])]
    have := intervalIntegral_cexp_int_mul_I (z - k)
    push_cast at this ⊢
    rw [this]
    by_cases hz : z = k
    · simp [hz]
    · simp [hz, sub_eq_zero]
  simp_rw [h2]
  rw [integral_indicator_const _ (measurableSet_singleton k)]
  rw [Complex.real_smul]
  push_cast
  field_simp


/-- Centering cancels against the translated Fourier phase. -/
private theorem centeredCF_pow_mul_phase (ν : Measure ℤ) (m : ℝ)
    (a : ℕ → ℝ) (n : ℕ) (k : ℤ) (t : ℝ) :
    centeredCF ν m (t / a n) ^ n *
        cexp (-(t * (((k : ℝ) - n * m) / a n) * I)) =
      stepCF ν (t / a n) ^ n * cexp (-((t / a n) * k * I)) := by
  rw [centeredCF_eq_phase_mul, mul_pow, ← Complex.exp_nat_mul]
  calc
    _ = stepCF ν (t / a n) ^ n *
        (cexp ((n : ℂ) * (-(((t / a n) * m : ℝ) * I))) *
          cexp (-(t * (((k : ℝ) - n * m) / a n) * I))) := by ring
    _ = _ := by
      rw [← Complex.exp_add]
      congr 2
      push_cast
      ring

/-- Fourier inversion after scaling, with the real centering retained in the phase. -/
private theorem mul_intWalk_real_eq (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (m : ℝ) {a : ℕ → ℝ} {n : ℕ} (han : 0 < a n) (k : ℤ) :
    ((a n * (intWalk ν n).real {k} : ℝ) : ℂ) = (1 / (2 * Real.pi)) *
      ∫ t, truncCF ν m a n t *
        cexp (-(t * (((k : ℝ) - n * m) / a n) * I)) := by
  let F : ℝ → ℂ := fun t => stepCF ν t ^ n * cexp (-(t * k * I))
  rw [Complex.ofReal_mul, intWalk_real_singleton]
  set L : ℝ := Real.pi * a n with hL
  have hL0 : 0 ≤ L := by positivity
  have h1 : ∫ θ in (-Real.pi)..Real.pi, F θ =
      (a n)⁻¹ • ∫ t in (-L)..L, F (t / a n) := by
    rw [intervalIntegral.integral_comp_div _ han.ne', smul_smul,
      inv_mul_cancel₀ han.ne', one_smul]
    congr 1 <;> dsimp [L] <;> field_simp
  have h2 : ∫ t in (-L)..L, F (t / a n) =
      ∫ t, truncCF ν m a n t *
        cexp (-(t * (((k : ℝ) - n * m) / a n) * I)) := by
    rw [intervalIntegral.integral_of_le (by linarith), ← integral_indicator measurableSet_Ioc]
    congr 1
    funext t
    unfold truncCF
    by_cases ht : t ∈ Ioc (-L) L
    · rw [indicator_of_mem ht, indicator_of_mem ht]
      simpa only [F, Complex.ofReal_div] using
        (centeredCF_pow_mul_phase ν m a n k t).symm
    · rw [indicator_of_notMem ht, indicator_of_notMem ht, zero_mul]
  change (a n : ℂ) * ((1 / (2 * Real.pi)) * ∫ θ in (-Real.pi)..Real.pi, F θ) = _
  rw [h1, h2, Complex.real_smul]
  have ha : (a n : ℂ) ≠ 0 := by exact_mod_cast han.ne'
  push_cast
  field_simp
  congr 1
  funext t
  congr 2
  ring


private noncomputable def firstKernel (ρ : Measure ℤ) (n : ℕ) (t : ℝ) : ℂ :=
  (Real.sqrt (n + 2) : ℂ) * centeredCF ρ (mean ρ) (t / Real.sqrt (n + 2)) ^ (n + 1) *
    centeredCF₁ ρ (mean ρ) (t / Real.sqrt (n + 2))

private lemma hasDerivAt_zerothKernel {ρ : Measure ℤ} [IsProbabilityMeasure ρ]
    (h : Integrable (fun z : ℤ => (z : ℝ) ^ 2) ρ) (n : ℕ) (t : ℝ) :
    HasDerivAt (zerothKernel ρ n) (firstKernel ρ n t) t := by
  let a := Real.sqrt (n + 2 : ℝ)
  have ha : (a : ℂ) ≠ 0 := by
    have hh : a ≠ 0 := (Real.sqrt_pos.2 (show (0 : ℝ) < n + 2 by positivity)).ne'
    exact Complex.ofReal_ne_zero.mpr hh
  have ha2 : (a : ℂ) ^ 2 = ((n : ℂ) + 2) := by
    have hh : a ^ 2 = (n : ℝ) + 2 := Real.sq_sqrt (show (0 : ℝ) ≤ n + 2 by positivity)
    exact_mod_cast hh
  have hscale : HasDerivAt (fun u : ℝ => u / a) (1 / a) t := by
    simpa only [id_eq] using (hasDerivAt_id t).div_const a
  have hd := ((hasDerivAt_centeredCF (integrable_cast_of_sq h) (mean ρ) (t / a)).scomp t
    hscale).pow (n + 2)
  convert hd using 1
  · rfl
  · dsimp only [firstKernel, Function.comp_def]
    simp only [show Real.sqrt (n + 2 : ℝ) = a from rfl]
    simp only [show n + 2 - 1 = n + 1 by omega, Nat.cast_add, Nat.cast_ofNat,
      one_div, Complex.real_smul, Complex.ofReal_inv]
    rw [← ha2]
    field_simp [ha]

private lemma hasDerivAt_firstKernel {ρ : Measure ℤ} [IsProbabilityMeasure ρ]
    (h : Integrable (fun z : ℤ => (z : ℝ) ^ 2) ρ) (n : ℕ) (t : ℝ) :
    HasDerivAt (firstKernel ρ n) (secondKernel ρ n t) t := by
  let a := Real.sqrt (n + 2 : ℝ)
  have ha : (a : ℂ) ≠ 0 := by
    have hh : a ≠ 0 := (Real.sqrt_pos.2 (show (0 : ℝ) < n + 2 by positivity)).ne'
    exact Complex.ofReal_ne_zero.mpr hh
  have hscale : HasDerivAt (fun u : ℝ => u / a) (1 / a) t := by
    simpa only [id_eq] using (hasDerivAt_id t).div_const a
  have hd₀ := (hasDerivAt_centeredCF (integrable_cast_of_sq h) (mean ρ) (t / a)).scomp t
    hscale
  have hd₁ := (hasDerivAt_centeredCF₁ h (mean ρ) (t / a)).scomp t
    hscale
  convert ((hd₀.pow (n + 1)).const_mul (a : ℂ)).mul hd₁ using 1
  · rfl
  · dsimp only [secondKernel, Function.comp_def]
    simp only [show Real.sqrt (n + 2 : ℝ) = a from rfl]
    simp only [show n + 1 - 1 = n by omega, Nat.cast_add, Nat.cast_one, one_div,
      Complex.real_smul, Complex.ofReal_inv, Pi.pow_apply]
    field_simp [ha]

private lemma fourier_second_derivative_integral {F F₁ F₂ : ℝ → ℂ} (y : ℝ)
    (hF : ∀ t, HasDerivAt F (F₁ t) t) (hF₁ : ∀ t, HasDerivAt F₁ (F₂ t) t)
    (hi₀ : Integrable F) (hi₁ : Integrable F₁) (hi₂ : Integrable F₂) :
    (∫ t, F₂ t * cexp (((-y * t : ℝ) : ℂ) * I)) =
      -(y : ℂ) ^ 2 * ∫ t, F t * cexp (((-y * t : ℝ) : ℂ) * I) := by
  let E : ℝ → ℂ := fun t => cexp (((-y * t : ℝ) : ℂ) * I)
  let c : ℂ := (-y : ℝ) * I
  have hE (t : ℝ) : HasDerivAt E (c * E t) t := by
    simpa [E, c, mul_comm] using hasDerivAt_centered_exponential (-y) t
  have hi (f : ℝ → ℂ) (hf : Integrable f) : Integrable (fun t => f t * E t) :=
    hf.mul_bdd (c := 1) (by dsimp [E]; fun_prop)
      (Eventually.of_forall fun t => by
        dsimp only [E]
        exact (norm_centered_exponential t (-y)).le)
  have heq (f : ℝ → ℂ) : (fun t => f t * (c * E t)) =
      (fun t => c * (f t * E t)) := by funext t; ring
  have h1 := integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := F) (u' := F₁) (v := E) (v' := fun t => c * E t)
    (fun t _ => hF t) (fun t _ => hE t)
    ((hi F hi₀).const_mul c |>.congr (Eventually.of_forall fun t => by dsimp; ring))
    (hi F₁ hi₁) (hi F hi₀)
  have h2 := integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := F₁) (u' := F₂) (v := E) (v' := fun t => c * E t)
    (fun t _ => hF₁ t) (fun t _ => hE t)
    ((hi F₁ hi₁).const_mul c |>.congr (Eventually.of_forall fun t => by dsimp; ring))
    (hi F₂ hi₂) (hi F₁ hi₁)
  rw [heq F, integral_const_mul] at h1
  rw [heq F₁, integral_const_mul] at h2
  change (∫ t, F₂ t * E t) = _
  calc
    _ = c ^ 2 * ∫ t, F t * E t := by linear_combination h2 - c * h1
    _ = _ := by dsimp [c, E]; push_cast; ring_nf; simp [I_sq]

private noncomputable def gaussianFirstKernel (v t : ℝ) : ℂ :=
  -(v : ℂ) * (t : ℂ) * gaussianKernel v t

private lemma hasDerivAt_gaussianKernel (v t : ℝ) :
    HasDerivAt (gaussianKernel v) (gaussianFirstKernel v t) t := by
  have hd := (((hasDerivAt_id t).ofReal_comp.pow 2).const_mul (-(v : ℂ) / 2)).cexp
  convert hd using 1
  · funext u
    dsimp [gaussianKernel]
    congr 1
    ring
  · dsimp [gaussianFirstKernel, gaussianKernel]
    ring_nf

private lemma hasDerivAt_gaussianFirstKernel (v t : ℝ) :
    HasDerivAt (gaussianFirstKernel v) (gaussianSecondKernel v t) t := by
  convert (((hasDerivAt_id t).ofReal_comp).const_mul (-(v : ℂ))).mul
    (hasDerivAt_gaussianKernel v t) using 1
  · rfl
  · dsimp [gaussianFirstKernel, gaussianSecondKernel, gaussianKernel]
    ring

private lemma integrable_gaussianFirstKernel {v : ℝ} (hv : 0 < v) :
    Integrable (gaussianFirstKernel v) := by
  apply Integrable.mono' (integrable_quadratic_gaussian (v ^ 2) 1 (by positivity : 0 < v / 2))
    (by unfold gaussianFirstKernel gaussianKernel; fun_prop)
  exact Eventually.of_forall fun t => by
    simp only [gaussianFirstKernel, norm_mul, norm_neg, Complex.norm_real,
      Real.norm_eq_abs, norm_gaussianKernel]
    apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
    rw [abs_of_pos hv]
    nlinarith [sq_nonneg (v * |t| - 1), sq_abs t]

private lemma gaussianSecondKernel_fourier {v : ℝ} (hv : 0 < v) (y : ℝ) :
    (∫ t, gaussianSecondKernel v t * cexp (((-y * t : ℝ) : ℂ) * I)) =
      -(y : ℂ) ^ 2 * ∫ t, gaussianKernel v t * cexp (((-y * t : ℝ) : ℂ) * I) :=
  fourier_second_derivative_integral y (hasDerivAt_gaussianKernel v)
    (hasDerivAt_gaussianFirstKernel v) (integrable_gaussianKernel hv)
    (integrable_gaussianFirstKernel hv) (integrable_gaussianSecondKernel hv)

private lemma twist_phase (m : ℝ) (d : ℕ) (x : ℤ) :
    cexp (-(((2 * Real.pi * m : ℝ) : ℂ) * I)) ^ d *
      cexp (((-Real.pi * ((x : ℝ) - d * m) : ℝ) : ℂ) * I) =
      cexp (((Real.pi * ((x : ℝ) - d * m) : ℝ) : ℂ) * I) := by
  rw [← Complex.exp_nat_mul, ← Complex.exp_add]
  calc
    _ = cexp ((-(x : ℂ)) * (2 * Real.pi * I) +
        (((Real.pi * ((x : ℝ) - d * m) : ℝ) : ℂ) * I)) := by
      congr 1
      push_cast
      ring
    _ = _ := by rw [Complex.exp_add, show -(x : ℂ) = ((-x : ℤ) : ℂ) by simp,
      Complex.exp_int_mul_two_pi_mul_I, one_mul]

private lemma centeredCF_endpoints (ρ : Measure ℤ) (m : ℝ) :
    centeredCF ρ m Real.pi = cexp (-(((2 * Real.pi * m : ℝ) : ℂ) * I)) *
      centeredCF ρ m (-Real.pi) := by
  have hh := centered_kernel_twisted_period ρ m (-Real.pi) (fun _ => 1)
  have hpi : -Real.pi + 2 * Real.pi = Real.pi := by ring
  simpa only [hpi, one_mul, centeredCF] using hh

private lemma centeredCF₁_endpoints (ρ : Measure ℤ) (m : ℝ) :
    centeredCF₁ ρ m Real.pi = cexp (-(((2 * Real.pi * m : ℝ) : ℂ) * I)) *
      centeredCF₁ ρ m (-Real.pi) := by
  have hh := centered_kernel_twisted_period ρ m (-Real.pi)
    (fun z => (((z : ℝ) - m : ℝ) : ℂ) * I)
  have hpi : -Real.pi + 2 * Real.pi = Real.pi := by ring
  simpa only [hpi, centeredCF₁] using hh

private lemma centered_power_endpoints (ρ : Measure ℤ) (m : ℝ) (d : ℕ) (x : ℤ) :
    centeredCF ρ m Real.pi ^ d *
        cexp (((-Real.pi * ((x : ℝ) - d * m) : ℝ) : ℂ) * I) =
      centeredCF ρ m (-Real.pi) ^ d *
        cexp (((Real.pi * ((x : ℝ) - d * m) : ℝ) : ℂ) * I) := by
  rw [centeredCF_endpoints, mul_pow]
  calc
    _ = centeredCF ρ m (-Real.pi) ^ d *
        (cexp (-(((2 * Real.pi * m : ℝ) : ℂ) * I)) ^ d *
          cexp (((-Real.pi * ((x : ℝ) - d * m) : ℝ) : ℂ) * I)) := by ring
    _ = _ := by rw [twist_phase]

private lemma centered_power_derivative_endpoints (ρ : Measure ℤ) (m : ℝ) (p : ℕ) (x : ℤ) :
    (centeredCF ρ m Real.pi ^ p * centeredCF₁ ρ m Real.pi) *
        cexp (((-Real.pi * ((x : ℝ) - (p + 1) * m) : ℝ) : ℂ) * I) =
      (centeredCF ρ m (-Real.pi) ^ p * centeredCF₁ ρ m (-Real.pi)) *
        cexp (((Real.pi * ((x : ℝ) - (p + 1) * m) : ℝ) : ℂ) * I) := by
  rw [centeredCF_endpoints, centeredCF₁_endpoints, mul_pow]
  calc
    _ = (centeredCF ρ m (-Real.pi) ^ p * centeredCF₁ ρ m (-Real.pi)) *
        (cexp (-(((2 * Real.pi * m : ℝ) : ℂ) * I)) ^ (p + 1) *
          cexp (((-Real.pi * ((x : ℝ) - (p + 1) * m) : ℝ) : ℂ) * I)) := by
      rw [pow_succ]
      ring
    _ = _ := by
      have hh := twist_phase m (p + 1) x
      simp only [Nat.cast_add, Nat.cast_one] at hh
      rw [hh]

private lemma integral_truncateKernel_mul (K : ℕ → ℝ → ℂ) (n : ℕ) (y : ℝ) :
    (∫ t, truncateKernel K n t * cexp (((-y * t : ℝ) : ℂ) * I)) =
      ∫ t in (-(Real.pi * Real.sqrt (n + 2)))..(Real.pi * Real.sqrt (n + 2)),
        K n t * cexp (((-y * t : ℝ) : ℂ) * I) := by
  rw [intervalIntegral.integral_of_le (by
    have hh : 0 ≤ Real.pi * Real.sqrt (n + 2 : ℝ) := by positivity
    linarith), ← integral_indicator measurableSet_Ioc]
  apply integral_congr_ae
  exact Eventually.of_forall fun t => by
    by_cases ht : t ∈ Ioc (-(Real.pi * Real.sqrt (n + 2))) (Real.pi * Real.sqrt (n + 2))
    · simp only [truncateKernel, indicator_of_mem ht]
    · simp only [truncateKernel, indicator_of_notMem ht, zero_mul]

private lemma secondKernel_fourier (ρ : Measure ℤ) [IsProbabilityMeasure ρ]
    (h : Integrable (fun z : ℤ => (z : ℝ) ^ 2) ρ) (n : ℕ) (x : ℤ) :
    let y := ((x : ℝ) - (n + 2) * mean ρ) / Real.sqrt (n + 2)
    (∫ t, truncateKernel (secondKernel ρ) n t * cexp (((-y * t : ℝ) : ℂ) * I)) =
      -(y : ℂ) ^ 2 * ∫ t, truncateKernel (zerothKernel ρ) n t *
        cexp (((-y * t : ℝ) : ℂ) * I) := by
  dsimp only
  rw [integral_truncateKernel_mul, integral_truncateKernel_mul]
  let a := Real.sqrt (n + 2 : ℝ)
  let y := ((x : ℝ) - (n + 2) * mean ρ) / a
  have ha : a ≠ 0 := (Real.sqrt_pos.2 (show (0 : ℝ) < n + 2 by positivity)).ne'
  have haC : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha
  have hplus : (Real.pi * a) / a = Real.pi := mul_div_cancel_right₀ _ ha
  have hminus : -(Real.pi * a) / a = -Real.pi := by rw [neg_div, hplus]
  have heplus : cexp (((-y * (Real.pi * a) : ℝ) : ℂ) * I) =
      cexp (((-Real.pi * ((x : ℝ) - (n + 2) * mean ρ) : ℝ) : ℂ) * I) := by
    congr 1
    dsimp [y]
    push_cast
    field_simp [haC]
  have heminus : cexp (((-y * -(Real.pi * a) : ℝ) : ℂ) * I) =
      cexp (((Real.pi * ((x : ℝ) - (n + 2) * mean ρ) : ℝ) : ℂ) * I) := by
    congr 1
    dsimp [y]
    push_cast
    field_simp [haC]
  apply fourier_second_derivative (hasDerivAt_zerothKernel h n) (hasDerivAt_firstKernel h n)
  · have hc : Continuous (centeredCF ρ (mean ρ)) := continuous_iff_continuousAt.2
      fun t => (hasDerivAt_centeredCF (integrable_cast_of_sq h) (mean ρ) t).continuousAt
    have hc₁ : Continuous (centeredCF₁ ρ (mean ρ)) := continuous_iff_continuousAt.2
      fun t => (hasDerivAt_centeredCF₁ h (mean ρ) t).continuousAt
    have hc₂ := continuous_centeredCF₂ h (mean ρ)
    unfold secondKernel
    fun_prop
  · change zerothKernel ρ n (Real.pi * a) * cexp (((-y * (Real.pi * a) : ℝ) : ℂ) * I) =
      zerothKernel ρ n (-(Real.pi * a)) * cexp (((-y * -(Real.pi * a) : ℝ) : ℂ) * I)
    rw [heplus, heminus]
    dsimp only [zerothKernel]
    simp only [show Real.sqrt (n + 2 : ℝ) = a from rfl]
    rw [hplus, hminus]
    simpa only [Nat.cast_add, Nat.cast_ofNat] using centered_power_endpoints ρ (mean ρ) (n + 2) x
  · change firstKernel ρ n (Real.pi * a) * cexp (((-y * (Real.pi * a) : ℝ) : ℂ) * I) =
      firstKernel ρ n (-(Real.pi * a)) * cexp (((-y * -(Real.pi * a) : ℝ) : ℂ) * I)
    rw [heplus, heminus]
    dsimp only [firstKernel]
    simp only [show Real.sqrt (n + 2 : ℝ) = a from rfl]
    rw [hplus, hminus]
    have hh := centered_power_derivative_endpoints ρ (mean ρ) (n + 1) x
    simp only [Nat.cast_add, Nat.cast_one] at hh
    rw [show (n : ℝ) + 1 + 1 = n + 2 by ring] at hh
    linear_combination (a : ℂ) * hh

private noncomputable def normalDensity (v y : ℝ) : ℝ :=
  (1 / (2 * Real.pi)) * (∫ t, gaussianKernel v t * cexp (((-y * t : ℝ) : ℂ) * I)).re

private lemma stableCF_two_exp (t : ℝ) :
    stableCF 2 t = cexp (-(t : ℂ) ^ 2) := by
  rw [stableCF]
  have hp : (-((t : ℂ) * I)) ^ ((2 : ℝ) : ℂ) = -(t : ℂ) ^ 2 := by
    rw [show ((2 : ℝ) : ℂ) = ((2 : ℕ) : ℂ) by norm_num, Complex.cpow_natCast]
    calc
      _ = (t : ℂ) ^ 2 * I ^ 2 := by ring
      _ = _ := by rw [I_sq]; ring
  rw [hp]

private lemma normalDensity_eq {v c : ℝ} (hc : 0 < c) (hc2 : c ^ 2 = v / 2) (y : ℝ) :
    normalDensity v y = gaussDensity (y / c) / c := by
  let F : ℝ → ℂ := fun u => stableCF 2 u * cexp (((-(y / c) * u : ℝ) : ℂ) * I)
  have hC : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc.ne'
  have hc2C : (c : ℂ) ^ 2 = (v : ℂ) / 2 := by exact_mod_cast hc2
  have hI : (∫ t, gaussianKernel v t * cexp (((-y * t : ℝ) : ℂ) * I)) =
      |c⁻¹| • ∫ u, F u := by
    calc
      _ = ∫ t, F (c * t) := by
        apply integral_congr_ae
        exact Eventually.of_forall fun t => by
          dsimp [F, gaussianKernel]
          rw [stableCF_two_exp]
          congr 1
          · congr 1
            push_cast
            rw [mul_pow, hc2C]
            ring
          · congr 1
            push_cast
            field_simp [hC]
      _ = _ := Measure.integral_comp_mul_left F c
  have hre := congrArg Complex.re hI
  simp only [Complex.real_smul, re_ofReal_mul, abs_inv, abs_of_pos hc] at hre
  calc
    normalDensity v y = c⁻¹ * ((1 / (2 * Real.pi)) * (∫ u, F u).re) := by
      rw [normalDensity, hre]
      ring
    _ = c⁻¹ * stableDensity 2 (y / c) := by
      rw [stableDensity]
      dsimp [F]
      congr 2
      congr 1
      apply integral_congr_ae
      exact Eventually.of_forall fun t => by
        dsimp only
        congr 1
        congr 1
        push_cast
        ring
    _ = _ := by rw [stableDensity_two]; ring

private noncomputable def fourierError (F G : ℝ → ℂ) (y : ℝ) : ℝ :=
  (1 / (2 * Real.pi)) * ((∫ t, F t * cexp (((-y * t : ℝ) : ℂ) * I)) -
    ∫ t, G t * cexp (((-y * t : ℝ) : ℂ) * I)).re

private lemma integrable_mul_phase {F : ℝ → ℂ} (hF : Integrable F) (y : ℝ) :
    Integrable (fun t => F t * cexp (((-y * t : ℝ) : ℂ) * I)) :=
  hF.mul_bdd (c := 1) (by fun_prop)
    (Eventually.of_forall fun t => (norm_centered_exponential t (-y)).le)

private lemma abs_fourierError_le {F G : ℝ → ℂ} (hF : Integrable F) (hG : Integrable G) (y : ℝ) :
    |fourierError F G y| ≤ (1 / (2 * Real.pi)) * ∫ t, ‖F t - G t‖ := by
  rw [fourierError, ← integral_sub (integrable_mul_phase hF y) (integrable_mul_phase hG y),
    abs_mul, abs_of_nonneg (by positivity : 0 ≤ 1 / (2 * Real.pi))]
  apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ 1 / (2 * Real.pi))
  calc
    _ ≤ ‖∫ t, (F t * cexp (((-y * t : ℝ) : ℂ) * I) -
        G t * cexp (((-y * t : ℝ) : ℂ) * I))‖ := Complex.abs_re_le_norm _
    _ ≤ _ := norm_integral_le_integral_norm _
    _ = _ := by
      apply integral_congr_ae
      exact Eventually.of_forall fun t => by
        dsimp only
        rw [← sub_mul, norm_mul, norm_centered_exponential, mul_one]

private lemma fourierError_second {F G F₂ G₂ : ℝ → ℂ} (y : ℝ)
    (hF : (∫ t, F₂ t * cexp (((-y * t : ℝ) : ℂ) * I)) =
      -(y : ℂ) ^ 2 * ∫ t, F t * cexp (((-y * t : ℝ) : ℂ) * I))
    (hG : (∫ t, G₂ t * cexp (((-y * t : ℝ) : ℂ) * I)) =
      -(y : ℂ) ^ 2 * ∫ t, G t * cexp (((-y * t : ℝ) : ℂ) * I)) :
    fourierError F₂ G₂ y = -y ^ 2 * fourierError F G y := by
  rw [fourierError, hF, hG, ← mul_sub, ← Complex.ofReal_pow, ← Complex.ofReal_neg, re_ofReal_mul]
  unfold fourierError
  ring

private lemma integrable_truncateKernel {K : ℕ → ℝ → ℂ} (n : ℕ) (hK : Continuous (K n)) :
    Integrable (truncateKernel K n) := by
  unfold truncateKernel
  exact (integrable_indicator_iff measurableSet_Ioc).2
    (hK.integrableOn_Icc.mono_set Ioc_subset_Icc_self)

private lemma weighted_fourierError_le {F G F₂ G₂ : ℝ → ℂ} (y : ℝ)
    (hiF : Integrable F) (hiG : Integrable G) (hiF₂ : Integrable F₂) (hiG₂ : Integrable G₂)
    (hF : (∫ t, F₂ t * cexp (((-y * t : ℝ) : ℂ) * I)) =
      -(y : ℂ) ^ 2 * ∫ t, F t * cexp (((-y * t : ℝ) : ℂ) * I))
    (hG : (∫ t, G₂ t * cexp (((-y * t : ℝ) : ℂ) * I)) =
      -(y : ℂ) ^ 2 * ∫ t, G t * cexp (((-y * t : ℝ) : ℂ) * I)) :
    max 1 (y ^ 2) * |fourierError F G y| ≤ (1 / (2 * Real.pi)) *
      ((∫ t, ‖F t - G t‖) + ∫ t, ‖F₂ t - G₂ t‖) := by
  have h₀ := abs_fourierError_le hiF hiG y
  have h₂ := abs_fourierError_le hiF₂ hiG₂ y
  rw [fourierError_second y hF hG, abs_mul, abs_neg, abs_of_nonneg (sq_nonneg y)] at h₂
  have hm : max 1 (y ^ 2) ≤ 1 + y ^ 2 := max_le (by nlinarith [sq_nonneg y]) (by linarith)
  have hh := mul_le_mul_of_nonneg_right hm (abs_nonneg (fourierError F G y))
  nlinarith

private lemma continuous_zerothKernel {ρ : Measure ℤ} [IsProbabilityMeasure ρ]
    (h : Integrable (fun z : ℤ => (z : ℝ) ^ 2) ρ) (n : ℕ) : Continuous (zerothKernel ρ n) := by
  have hc : Continuous (centeredCF ρ (mean ρ)) := continuous_iff_continuousAt.2
    fun t => (hasDerivAt_centeredCF (integrable_cast_of_sq h) (mean ρ) t).continuousAt
  unfold zerothKernel
  fun_prop

private lemma continuous_secondKernel {ρ : Measure ℤ} [IsProbabilityMeasure ρ]
    (h : Integrable (fun z : ℤ => (z : ℝ) ^ 2) ρ) (n : ℕ) : Continuous (secondKernel ρ n) := by
  have hc : Continuous (centeredCF ρ (mean ρ)) := continuous_iff_continuousAt.2
    fun t => (hasDerivAt_centeredCF (integrable_cast_of_sq h) (mean ρ) t).continuousAt
  have hc₁ : Continuous (centeredCF₁ ρ (mean ρ)) := continuous_iff_continuousAt.2
    fun t => (hasDerivAt_centeredCF₁ h (mean ρ) t).continuousAt
  have hc₂ := continuous_centeredCF₂ h (mean ρ)
  unfold secondKernel
  fun_prop

private lemma normalized_weighted_error_le (ρ : Measure ℤ) [IsProbabilityMeasure ρ]
    (hnl : ¬ IsLatticeLaw ρ) (h : Integrable (fun z : ℤ => (z : ℝ) ^ 2) ρ) (n : ℕ) (x : ℤ) :
    let y := ((x : ℝ) - (n + 2) * mean ρ) / Real.sqrt (n + 2)
    max 1 (y ^ 2) * |Real.sqrt (n + 2) * intWalkProb ρ (n + 2) x - normalDensity (variance ρ) y| ≤
      (1 / (2 * Real.pi)) *
        ((∫ t, ‖truncateKernel (zerothKernel ρ) n t - gaussianKernel (variance ρ) t‖) +
          ∫ t, ‖truncateKernel (secondKernel ρ) n t - gaussianSecondKernel (variance ρ) t‖) := by
  let y := ((x : ℝ) - (n + 2) * mean ρ) / Real.sqrt (n + 2)
  have hp := mul_intWalk_real_eq ρ (mean ρ) (a := fun k => Real.sqrt k) (n := n + 2)
    (by positivity) x
  simp only [Nat.cast_add, Nat.cast_ofNat] at hp
  have hp' : ((Real.sqrt (n + 2) * intWalkProb ρ (n + 2) x : ℝ) : ℂ) =
      (1 / (2 * Real.pi)) * ∫ t, truncateKernel (zerothKernel ρ) n t *
        cexp (((-y * t : ℝ) : ℂ) * I) := by
    convert hp using 1
    · rfl
    · apply congrArg (fun z : ℂ => (1 / (2 * (Real.pi : ℂ))) * z)
      apply integral_congr_ae
      exact Eventually.of_forall fun t => by
        dsimp only [truncCF, truncateKernel, zerothKernel, y]
        simp only [Nat.cast_add, Nat.cast_ofNat]
        congr 1
        congr 1
        push_cast
        ring
  have hc : (1 / (2 * (Real.pi : ℂ))) = ((1 / (2 * Real.pi) : ℝ) : ℂ) := by push_cast; rfl
  rw [hc] at hp'
  have hre := congrArg Complex.re hp'
  rw [Complex.ofReal_re, re_ofReal_mul] at hre
  have herr : Real.sqrt (n + 2) * intWalkProb ρ (n + 2) x - normalDensity (variance ρ) y =
      fourierError (truncateKernel (zerothKernel ρ) n) (gaussianKernel (variance ρ)) y := by
    rw [fourierError, Complex.sub_re, normalDensity, hre]
    ring
  change max 1 (y ^ 2) * |Real.sqrt (n + 2) * intWalkProb ρ (n + 2) x -
    normalDensity (variance ρ) y| ≤ _
  rw [herr]
  exact weighted_fourierError_le y
    (integrable_truncateKernel n (continuous_zerothKernel h n))
    (integrable_gaussianKernel (variance_pos_of_nonlattice hnl h))
    (integrable_truncateKernel n (continuous_secondKernel h n))
    (integrable_gaussianSecondKernel (variance_pos_of_nonlattice hnl h))
    (secondKernel_fourier ρ h n x) (gaussianSecondKernel_fourier (variance_pos_of_nonlattice hnl h) y)

/-- The weighted local limit theorem, uniformly over all integer endpoints and
with arbitrary real mean. -/
theorem strongLLT (ρ : Measure ℤ) [IsProbabilityMeasure ρ] (hnl : ¬ IsLatticeLaw ρ)
    (hL2 : Integrable (fun z : ℤ => (z : ℝ) ^ 2) ρ) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ x : ℤ,
      max 1 (((x : ℝ) - n * mean ρ) ^ 2 / n) *
        |Real.sqrt (variance ρ) * Real.sqrt (n / 2) * intWalkProb ρ n x -
          gaussDensity (((x : ℝ) - n * mean ρ) / (Real.sqrt (variance ρ) * Real.sqrt (n / 2)))|
        ≤ ε := by
  have hv := variance_pos_of_nonlattice hnl hL2
  let c := Real.sqrt (variance ρ / 2)
  have hc : 0 < c := Real.sqrt_pos.2 (by positivity)
  have hc2 : c ^ 2 = variance ρ / 2 := Real.sq_sqrt (by positivity)
  let E : ℕ → ℝ := fun n => (1 / (2 * Real.pi)) *
    ((∫ t, ‖truncateKernel (zerothKernel ρ) n t - gaussianKernel (variance ρ) t‖) +
      ∫ t, ‖truncateKernel (secondKernel ρ) n t - gaussianSecondKernel (variance ρ) t‖)
  have hl : Tendsto (fun n => c * E n) atTop (𝓝 0) := by
    have hh := ((tendsto_integral_norm_zerothKernel_sub hnl hL2).add
      (tendsto_integral_norm_secondKernel_sub hnl hL2)).const_mul (c * (1 / (2 * Real.pi)))
    simpa only [add_zero, mul_zero, E, mul_assoc] using hh
  obtain ⟨N, hN⟩ := (hl.eventually (gt_mem_nhds hε)).exists_forall_of_atTop
  refine ⟨N + 2, fun d hd x => ?_⟩
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, d = n + 2 := ⟨d - 2, by omega⟩
  have hn : N ≤ n := by omega
  let b := Real.sqrt (n + 2 : ℝ)
  let y := ((x : ℝ) - (n + 2) * mean ρ) / b
  have hb : 0 < b := Real.sqrt_pos.2 (by positivity)
  have hscale : Real.sqrt (variance ρ) * Real.sqrt ((n + 2 : ℝ) / 2) = c * b := by
    dsimp [c, b]
    rw [← Real.sqrt_mul hv.le, ← Real.sqrt_mul (show 0 ≤ variance ρ / 2 by positivity)]
    congr 1
    ring
  have hweight : ((x : ℝ) - (n + 2) * mean ρ) ^ 2 / (n + 2) = y ^ 2 := by
    dsimp [y, b]
    rw [div_pow, Real.sq_sqrt (show (0 : ℝ) ≤ n + 2 by positivity)]
  have harg : ((x : ℝ) - (n + 2) * mean ρ) / (c * b) = y / c := by
    dsimp [y]
    field_simp
  have hnormal : gaussDensity (y / c) = c * normalDensity (variance ρ) y := by
    rw [normalDensity_eq hc hc2 y]
    field_simp [hc.ne']
  have hbound := normalized_weighted_error_le ρ hnl hL2 n x
  change max 1 (y ^ 2) * |b * intWalkProb ρ (n + 2) x - normalDensity (variance ρ) y| ≤ E n at hbound
  simp only [Nat.cast_add, Nat.cast_ofNat]
  rw [hscale, hweight, harg, hnormal,
    show c * b * intWalkProb ρ (n + 2) x - c * normalDensity (variance ρ) y =
      c * (b * intWalkProb ρ (n + 2) x - normalDensity (variance ρ) y) by ring,
    abs_mul, abs_of_pos hc]
  calc
    _ = c * (max 1 (y ^ 2) * |b * intWalkProb ρ (n + 2) x - normalDensity (variance ρ) y|) := by ring
    _ ≤ c * E n := mul_le_mul_of_nonneg_left hbound hc.le
    _ ≤ ε := (hN n hn).le

end BGWLeaves.StableAnalysis.StrongLLT

end
