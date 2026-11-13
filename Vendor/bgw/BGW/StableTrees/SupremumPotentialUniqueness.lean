/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.StablePassageSubordinatorLaplace
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Laplace uniqueness for finite measures on the nonnegative half-line

Two finite measures carried by `[0, ∞)` are equal when their Laplace transforms agree at
all positive parameters.  The proof uses analyticity in the left half-plane and dominated
convergence at its imaginary boundary (W. Feller, *An Introduction to Probability Theory and Its
Applications*, Vol. II, 2nd ed., Wiley, 1971, Section XIII.1).
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal

namespace BGW.StableTrees

private lemma integrable_exp_neg_of_measure_Iio_zero {μ : Measure ℝ} [IsFiniteMeasure μ]
    (hμ : μ (Iio 0) = 0) {q : ℝ} (hq : 0 ≤ q) :
    Integrable (fun t : ℝ => Real.exp (-q * t)) μ := by
  apply (integrable_const (1 : ℝ)).mono'
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).aestronglyMeasurable
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp hμ] with t ht
  have ht0 : 0 ≤ t := not_lt.mp ht
  change |Real.exp (-q * t)| ≤ 1
  rw [abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_one_iff.mpr (by nlinarith)

private lemma eqOn_complexMGF_left {μ ν : Measure ℝ} [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] (hμ : μ (Iio 0) = 0) (hν : ν (Iio 0) = 0)
    (hL : ∀ q : ℝ, 0 < q → (∫ t, Real.exp (-q * t) ∂μ) = ∫ t, Real.exp (-q * t) ∂ν)
    {z : ℂ} (hz : z.re < 0) : complexMGF id μ z = complexMGF id ν z := by
  let U : Set ℂ := {z | z.re < 0}
  have hU : IsPreconnected U := (convex_halfSpace_re_lt 0).isPreconnected
  have hInterior (ρ : Measure ℝ) [IsFiniteMeasure ρ] (hρ : ρ (Iio 0) = 0) :
      Iio (0 : ℝ) ⊆ interior (integrableExpSet id ρ) := by
    apply interior_maximal _ isOpen_Iio
    intro t ht
    have hi := integrable_exp_neg_of_measure_Iio_zero hρ (q := -t) (by simpa using ht.le)
    simpa [integrableExpSet] using hi
  have hf : AnalyticOnNhd ℂ (complexMGF id μ) U := by
    intro w hw
    exact analyticAt_complexMGF (hInterior μ hμ hw)
  have hg : AnalyticOnNhd ℂ (complexMGF id ν) U := by
    intro w hw
    exact analyticAt_complexMGF (hInterior ν hν hw)
  have hmem : (-1 : ℂ) ∈ U := by simp [U]
  have hfreq : ∃ᶠ w in 𝓝[≠] (-1 : ℂ), complexMGF id μ w = complexMGF id ν w := by
    have ht : Tendsto (fun n : ℕ => ((-1 + 1 / ((n : ℝ) + 2) : ℝ) : ℂ)) atTop
        (𝓝[≠] (-1 : ℂ)) := by
      apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      · have hseq : Tendsto (fun n : ℕ => (-1 + 1 / ((n : ℝ) + 2) : ℝ)) atTop (𝓝 (-1 + 0)) := by
          apply Tendsto.add tendsto_const_nhds
          apply Tendsto.div_atTop tendsto_const_nhds
          exact tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
        rw [add_zero] at hseq
        have hc := (Complex.continuous_ofReal.tendsto _).comp hseq
        simpa [Function.comp_def] using hc
      · refine Eventually.of_forall fun n => ?_
        simp only [mem_compl_iff, mem_singleton_iff]
        intro h
        have h2 : (-1 + 1 / ((n : ℝ) + 2) : ℝ) = -1 := by exact_mod_cast h
        have h3 : (0 : ℝ) < 1 / ((n : ℝ) + 2) := by positivity
        linarith
    apply ht.frequently
    refine Frequently.of_forall fun n => ?_
    set t : ℝ := -1 + 1 / ((n : ℝ) + 2)
    have htneg : t < 0 := by
      have hn : (0 : ℝ) < 1 / ((n : ℝ) + 2) := by positivity
      have hn' : 1 / ((n : ℝ) + 2) < 1 := by
        rw [div_lt_one (by positivity)]
        linarith [n.cast_nonneg (α := ℝ)]
      simp only [t]
      linarith
    rw [complexMGF_ofReal, complexMGF_ofReal]
    apply congrArg Complex.ofReal
    change (∫ x : ℝ, Real.exp (t * x) ∂μ) = ∫ x : ℝ, Real.exp (t * x) ∂ν
    simpa only [neg_neg] using hL (-t) (by linarith)
  exact AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq hf hg hU hmem hfreq hz

private lemma tendsto_complexMGF_boundary_of_measure_Iio_zero {μ : Measure ℝ}
    [IsFiniteMeasure μ] (hμ : μ (Iio 0) = 0) (θ : ℝ) :
    Tendsto (fun ε : ℝ => complexMGF id μ (-(ε : ℂ) + θ * Complex.I)) (𝓝[>] 0)
      (𝓝 (complexMGF id μ (θ * Complex.I))) := by
  unfold complexMGF
  apply tendsto_integral_filter_of_dominated_convergence (fun _ => 1)
  · exact Eventually.of_forall fun ε => (by fun_prop : Continuous fun y : ℝ =>
      Complex.exp ((-(ε : ℂ) + θ * Complex.I) * (id y : ℂ))).aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hμ] with y hy
    have hy0 : 0 ≤ y := not_lt.mp hy
    rw [Complex.norm_exp]
    have hre : ((-(ε : ℂ) + θ * Complex.I) * ((id y : ℝ) : ℂ)).re = -ε * y := by
      simp [Complex.mul_re]
    rw [hre]
    have hε0 : 0 < ε := hε
    exact Real.exp_le_one_iff.mpr (by nlinarith)
  · exact integrable_const 1
  · refine Eventually.of_forall fun y => ?_
    apply tendsto_nhdsWithin_of_tendsto_nhds
    have hc : Continuous fun ε : ℝ =>
        Complex.exp ((-(ε : ℂ) + θ * Complex.I) * ((id y : ℝ) : ℂ)) := by fun_prop
    simpa using hc.tendsto 0

/-- Finite measures on `[0, ∞)` have equal laws if their Laplace transforms agree. -/
theorem finiteMeasure_eq_of_laplace_on_nonneg {μ ν : Measure ℝ} [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] (hμ : μ (Iio 0) = 0) (hν : ν (Iio 0) = 0)
    (hL : ∀ q : ℝ, 0 < q → (∫ t, Real.exp (-q * t) ∂μ) = ∫ t, Real.exp (-q * t) ∂ν) :
    μ = ν := by
  apply Measure.ext_of_charFun
  funext θ
  rw [← complexMGF_id_mul_I (μ := μ) θ, ← complexMGF_id_mul_I (μ := ν) θ]
  have hleft : ∀ᶠ ε : ℝ in 𝓝[>] 0,
      complexMGF id μ (-(ε : ℂ) + θ * Complex.I) =
        complexMGF id ν (-(ε : ℂ) + θ * Complex.I) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    apply eqOn_complexMGF_left hμ hν hL
    simp only [Complex.add_re, Complex.neg_re, Complex.ofReal_re, Complex.mul_re,
      Complex.I_re, mul_zero,
      Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero]
    simpa using hε
  exact tendsto_nhds_unique (tendsto_complexMGF_boundary_of_measure_Iio_zero hμ θ)
    ((tendsto_complexMGF_boundary_of_measure_Iio_zero hν θ).congr' (hleft.mono fun _ h => h.symm))

private theorem ofReal_toReal_sub (x : ℝ) :
    (ENNReal.ofReal x).toReal - (ENNReal.ofReal (-x)).toReal = x := by
  by_cases hx : 0 ≤ x
  · rw [ENNReal.toReal_ofReal hx, ENNReal.ofReal_eq_zero.mpr (by linarith), ENNReal.toReal_zero]
    ring
  · rw [ENNReal.ofReal_eq_zero.mpr (not_le.mp hx).le, ENNReal.toReal_zero,
      ENNReal.toReal_ofReal (by linarith : 0 ≤ -x)]
    ring

/-- Signed integrable densities are identified before positivity: equality of their Laplace
integrals with a finite nonnegative measure forces equality of measures and positivity almost
 everywhere on a nonnegative carrier. -/
theorem measure_eq_withDensity_of_laplace {μ ν : Measure ℝ} [IsFiniteMeasure μ]
    (hμ : μ (Iio 0) = 0) (hν : ν (Iio 0) = 0) {f : ℝ → ℝ}
    (hf : Measurable f) (hi : Integrable f ν)
    (hL : ∀ lam : ℝ, 0 < lam → (∫ x, Real.exp (-lam * x) ∂μ) =
      ∫ x, Real.exp (-lam * x) * f x ∂ν) :
    μ = ν.withDensity (fun x => ENNReal.ofReal (f x)) ∧ ∀ᵐ x ∂ν, 0 ≤ f x := by
  let P := ν.withDensity (fun x => ENNReal.ofReal (f x))
  let N := ν.withDensity (fun x => ENNReal.ofReal (-f x))
  have hPf : (∫⁻ x, ENNReal.ofReal (f x) ∂ν) < ∞ := by
    apply lt_of_le_of_lt (lintegral_mono (fun x => ?_)) hi.2
    simpa only [← ofReal_norm, Real.norm_eq_abs] using ENNReal.ofReal_le_ofReal (le_abs_self (f x))
  have hNf : (∫⁻ x, ENNReal.ofReal (-f x) ∂ν) < ∞ := by
    apply lt_of_le_of_lt (lintegral_mono (fun x => ?_)) hi.2
    simpa only [← ofReal_norm, Real.norm_eq_abs, abs_neg] using
      ENNReal.ofReal_le_ofReal (le_abs_self (-f x))
  let := isFiniteMeasure_withDensity hPf.ne
  let := isFiniteMeasure_withDensity hNf.ne
  have hP0 : P (Iio 0) = 0 := withDensity_absolutelyContinuous ν _ hν
  have hN0 : N (Iio 0) = 0 := withDensity_absolutelyContinuous ν _ hν
  have he : μ + N = P := by
    apply finiteMeasure_eq_of_laplace_on_nonneg (by simp [hμ, hN0]) hP0
    intro lam hlam
    have hiμ := integrable_exp_neg_of_measure_Iio_zero hμ hlam.le
    have hiP := integrable_exp_neg_of_measure_Iio_zero hP0 hlam.le
    have hiN := integrable_exp_neg_of_measure_Iio_zero hN0 hlam.le
    have ht (g : ℝ → ℝ) (hg : Measurable g) :
        (∫ x, Real.exp (-lam * x) ∂ν.withDensity (fun x => ENNReal.ofReal (g x))) =
        ∫ x, (ENNReal.ofReal (g x)).toReal * Real.exp (-lam * x) ∂ν := by
      rw [integral_withDensity_eq_integral_toReal_smul hg.ennreal_ofReal
        (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
      rfl
    have hip : Integrable (fun x => (ENNReal.ofReal (f x)).toReal * Real.exp (-lam * x)) ν := by
      exact (integrable_withDensity_iff_integrable_smul' hf.ennreal_ofReal
        (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))).1 hiP
    have hin : Integrable (fun x => (ENNReal.ofReal (-f x)).toReal * Real.exp (-lam * x)) ν := by
      exact (integrable_withDensity_iff_integrable_smul' hf.neg.ennreal_ofReal
        (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))).1 hiN
    have hdiff : (fun x => Real.exp (-lam * x) * f x) =
        (fun x => (ENNReal.ofReal (f x)).toReal * Real.exp (-lam * x) -
          (ENNReal.ofReal (-f x)).toReal * Real.exp (-lam * x)) := by
      funext x
      rw [← sub_mul, ofReal_toReal_sub]
      ring
    rw [integral_add_measure hiμ hiN, hL lam hlam]
    change (∫ x, Real.exp (-lam * x) * f x ∂ν) +
      (∫ x, Real.exp (-lam * x) ∂ν.withDensity (fun x => ENNReal.ofReal (-f x))) =
      ∫ x, Real.exp (-lam * x) ∂ν.withDensity (fun x => ENNReal.ofReal (f x))
    rw [ht f hf, ht (fun x => -f x) hf.neg, hdiff, integral_sub hip hin]
    ring
  have hNP : N ≤ P := he ▸ Measure.le_add_left le_rfl
  have hd : Disjoint N P :=
    Measure.mutuallySingular_iff_disjoint.1 (withDensity_ofReal_mutuallySingular (μ := ν) hf).symm
  have hz : N = 0 := disjoint_self.1 (hd.mono_right hNP)
  refine ⟨?_, ?_⟩
  · simpa only [hz, add_zero] using he
  · have hae := (withDensity_eq_zero_iff hf.neg.ennreal_ofReal.aemeasurable).1 hz
    filter_upwards [hae] with x hx
    have hx' := ENNReal.ofReal_eq_zero.1 hx
    change -f x ≤ 0 at hx'
    linarith

private theorem withDensity_weight_cancel {ν : Measure ℝ} {w f : ℝ → ℝ}
    (hw : Measurable w) (hf : Measurable f) (hp : ∀ x, 0 < w x) :
    (ν.withDensity (fun x => ENNReal.ofReal (w x * f x))).withDensity
      (fun x => (ENNReal.ofReal (w x))⁻¹) = ν.withDensity (fun x => ENNReal.ofReal (f x)) := by
  rw [← withDensity_mul ν (f := fun x => ENNReal.ofReal (w x * f x))
    (g := fun x => (ENNReal.ofReal (w x))⁻¹) (hw.mul hf).ennreal_ofReal hw.ennreal_ofReal.inv]
  apply withDensity_congr_ae
  filter_upwards with x
  change ENNReal.ofReal (w x * f x) * (ENNReal.ofReal (w x))⁻¹ = ENNReal.ofReal (f x)
  rw [ENNReal.ofReal_mul (hp x).le]
  calc
    _ = (ENNReal.ofReal (w x) * (ENNReal.ofReal (w x))⁻¹) * ENNReal.ofReal (f x) := by ac_rfl
    _ = _ := by rw [ENNReal.mul_inv_cancel (ENNReal.ofReal_ne_zero_iff.2 (hp x))
      ENNReal.ofReal_ne_top, one_mul]

/-- Laplace equality on a strict half-line identifies a signed density after exponential tilting.
The sign conclusion concerns the real density before applying `ENNReal.ofReal`. -/
theorem measure_eq_withDensity_of_laplace_halfline {μ ν : Measure ℝ} [IsFiniteMeasure μ]
    (hμ : μ (Iio 0) = 0) (hν : ν (Iio 0) = 0) {f : ℝ → ℝ} (hf : Measurable f)
    {a : ℝ} (ha : 0 < a) (hi : Integrable (fun x => Real.exp (-a * x) * f x) ν)
    (hL : ∀ lam : ℝ, a < lam → (∫ x, Real.exp (-lam * x) ∂μ) =
      ∫ x, Real.exp (-lam * x) * f x ∂ν) :
    μ = ν.withDensity (fun x => ENNReal.ofReal (f x)) ∧ ∀ᵐ x ∂ν, 0 ≤ f x := by
  let w := fun x : ℝ => Real.exp (-a * x)
  have hw : Measurable w := by fun_prop
  have hp (x : ℝ) : 0 < w x := Real.exp_pos _
  have hwi : Integrable w μ := integrable_exp_neg_of_measure_Iio_zero hμ ha.le
  have hfin : (∫⁻ x, ENNReal.ofReal (w x) ∂μ) < ∞ := by
    apply lt_of_le_of_lt (lintegral_mono (fun x => ?_)) hwi.2
    rw [← ofReal_norm, Real.norm_eq_abs, abs_of_pos (hp x)]
  let μa := μ.withDensity (fun x => ENNReal.ofReal (w x))
  let := isFiniteMeasure_withDensity hfin.ne
  have hμa : μa (Iio 0) = 0 := withDensity_absolutelyContinuous μ _ hμ
  have htilt : μa = ν.withDensity (fun x => ENNReal.ofReal (w x * f x)) ∧
      ∀ᵐ x ∂ν, 0 ≤ w x * f x := by
    apply measure_eq_withDensity_of_laplace hμa hν (hw.mul hf) hi
    intro lam hlam
    have hprod (x : ℝ) : w x * Real.exp (-lam * x) = Real.exp (-(a + lam) * x) := by
      dsimp [w]
      rw [← Real.exp_add]
      congr 1
      ring
    have hprod' (x : ℝ) : Real.exp (-lam * x) * (w x * f x) =
        Real.exp (-(a + lam) * x) * f x := by rw [← hprod]; ring
    change (∫ x, Real.exp (-lam * x) ∂μ.withDensity (fun x => ENNReal.ofReal (w x))) = _
    rw [integral_withDensity_eq_integral_toReal_smul hw.ennreal_ofReal
      (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
    change (∫ x, (ENNReal.ofReal (w x)).toReal * Real.exp (-lam * x) ∂μ) =
      ∫ x, Real.exp (-lam * x) * (w x * f x) ∂ν
    simp_rw [ENNReal.toReal_ofReal (hp _).le, hprod, hprod']
    exact hL (a + lam) (by linarith)
  refine ⟨?_, ?_⟩
  · have he := congrArg (fun ρ : Measure ℝ => ρ.withDensity (fun x => (ENNReal.ofReal (w x))⁻¹))
      htilt.1
    have hcancel : μa.withDensity (fun x => (ENNReal.ofReal (w x))⁻¹) = μ :=
      withDensity_inv_same hw.ennreal_ofReal
        (ae_of_all _ (fun x => ENNReal.ofReal_ne_zero_iff.2 (hp x)))
        (ae_of_all _ (fun _ => ENNReal.ofReal_ne_top))
    rwa [hcancel, withDensity_weight_cancel hw hf hp] at he
  · filter_upwards [htilt.2] with x hx
    exact (mul_nonneg_iff_of_pos_left (hp x)).1 hx

end BGW.StableTrees
