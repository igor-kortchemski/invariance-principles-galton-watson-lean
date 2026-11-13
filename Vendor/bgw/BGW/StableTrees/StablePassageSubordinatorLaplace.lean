/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.StableLaw

/-!
# Laplace uniqueness for laws on the nonnegative half-line

Two probability measures carried by `[0, ∞)` are equal when their Laplace transforms agree at
all positive parameters.  The proof uses analyticity in the left half-plane and dominated
convergence at its imaginary boundary (W. Feller, *An Introduction to Probability Theory and Its
Applications*, Vol. II, 2nd ed., Wiley, 1971, Section XIII.1).
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal

namespace BGW.StableTrees

private lemma integrable_exp_neg_of_measure_Iio_zero {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : μ (Iio 0) = 0) {q : ℝ} (hq : 0 ≤ q) :
    Integrable (fun t : ℝ => Real.exp (-q * t)) μ := by
  apply (integrable_const (1 : ℝ)).mono'
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).aestronglyMeasurable
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp hμ] with t ht
  have ht0 : 0 ≤ t := not_lt.mp ht
  change |Real.exp (-q * t)| ≤ 1
  rw [abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_one_iff.mpr (by nlinarith)

private lemma eqOn_complexMGF_left {μ ν : Measure ℝ} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (hμ : μ (Iio 0) = 0) (hν : ν (Iio 0) = 0)
    (hL : ∀ q : ℝ, 0 < q → (∫ t, Real.exp (-q * t) ∂μ) = ∫ t, Real.exp (-q * t) ∂ν)
    {z : ℂ} (hz : z.re < 0) : complexMGF id μ z = complexMGF id ν z := by
  let U : Set ℂ := {z | z.re < 0}
  have hU : IsPreconnected U := (convex_halfSpace_re_lt 0).isPreconnected
  have hInterior (ρ : Measure ℝ) [IsProbabilityMeasure ρ] (hρ : ρ (Iio 0) = 0) :
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
    [IsProbabilityMeasure μ] (hμ : μ (Iio 0) = 0) (θ : ℝ) :
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

/-- Probability measures on `[0, ∞)` have equal laws if their Laplace transforms agree. -/
theorem measure_eq_of_laplace_on_nonneg {μ ν : Measure ℝ} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (hμ : μ (Iio 0) = 0) (hν : ν (Iio 0) = 0)
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

end BGW.StableTrees
