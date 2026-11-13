/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! Integral identities and domination lemmas for signed resolvent moments.

Reference: O. Kallenberg, *Foundations of Modern Probability*, 2nd ed., Springer, 2002.
-/

@[expose] public section

open MeasureTheory Set

namespace BGW.Probability

/-- The square of an integral is twice its integral over strictly ordered pairs. -/
theorem integral_sq_eq_two_mul_tail {ν : Measure ℝ} [SFinite ν] [NullSingletonClass ν]
    {f : ℝ → ℝ} (hf : Integrable f ν) :
    (∫ s, f s ∂ν)^2 = 2 * ∫ s, f s * (∫ t in Ioi s, f t ∂ν) ∂ν := by
  let g : ℝ × ℝ → ℝ := {p | p.1 < p.2}.indicator (fun p => f p.1 * f p.2)
  have hg : Integrable g (ν.prod ν) :=
    (hf.mul_prod hf).indicator (measurableSet_lt measurable_fst measurable_snd)
  have hgl (s : ℝ) : (∫ t, g (s, t) ∂ν) =
      f s * (∫ t in Ioi s, f t ∂ν) := by
    change (∫ t, (Ioi s).indicator (fun t => f s * f t) t ∂ν) = _
    rw [integral_indicator measurableSet_Ioi, integral_const_mul]
  have hgr (t : ℝ) : (∫ s, g (s, t) ∂ν) =
      f t * (∫ s in Iio t, f s ∂ν) := by
    change (∫ s, (Iio t).indicator (fun s => f s * f t) s ∂ν) = _
    rw [integral_indicator measurableSet_Iio, integral_mul_const, mul_comm]
  have hleft : Integrable (fun s => f s * (∫ t in Ioi s, f t ∂ν)) ν := by
    simpa only [hgl] using hg.integral_prod_left
  have hright : Integrable (fun t => f t * (∫ s in Iio t, f s ∂ν)) ν := by
    simpa only [hgr] using hg.integral_prod_right
  have heq : (∫ s, f s * (∫ t in Ioi s, f t ∂ν) ∂ν) =
      ∫ t, f t * (∫ s in Iio t, f s ∂ν) ∂ν := by
    have he := (integral_prod g hg).symm.trans (integral_prod_symm g hg)
    simpa only [hgl, hgr] using he
  have hsplit (s : ℝ) : (∫ t in Iio s, f t ∂ν) + (∫ t in Ioi s, f t ∂ν) =
      ∫ t, f t ∂ν := by
    rw [← integral_Iic_eq_integral_Iio, ← compl_Iic]
    exact integral_add_compl measurableSet_Iic hf
  have hs : (∫ s, f s * (∫ t in Iio s, f t ∂ν) ∂ν) +
      (∫ s, f s * (∫ t in Ioi s, f t ∂ν) ∂ν) = (∫ s, f s ∂ν)^2 := by
    rw [← integral_add hright hleft]
    simp_rw [← mul_add, hsplit]
    rw [integral_mul_const, pow_two]
  linarith

/-- A jointly measurable integrand has a jointly measurable tail integral. -/
theorem measurable_integral_tail {Ω : Type*} [MeasurableSpace Ω] {f : ℝ × Ω → ℝ}
    (hf : Measurable f) :
    Measurable (fun p : ℝ × Ω => ∫ t in Ioi p.1, f (t, p.2)) := by
  have hm : Measurable (fun p : (ℝ × Ω) × ℝ =>
      {q : (ℝ × Ω) × ℝ | q.1.1 < q.2}.indicator
        (fun q => f (q.2, q.1.2)) p) := by
    apply Measurable.indicator
    · exact hf.comp (measurable_snd.prodMk (measurable_snd.comp measurable_fst))
    · exact measurableSet_lt (measurable_fst.comp measurable_fst) measurable_snd
  have hi := hm.stronglyMeasurable.integral_prod_right' (ν := volume)
  have heq : (fun p : ℝ × Ω => ∫ t,
      {q : (ℝ × Ω) × ℝ | q.1.1 < q.2}.indicator
        (fun q => f (q.2, q.1.2)) (p, t)) =
      (fun p : ℝ × Ω => ∫ t in Ioi p.1, f (t, p.2)) := by
    funext p
    change (∫ t, (Ioi p.1).indicator (fun t => f (t, p.2)) t) = _
    exact integral_indicator measurableSet_Ioi
  rw [← heq]
  exact hi.measurable

/-- An exponentially weighted bounded jointly measurable function is integrable. -/
theorem integrable_exp_mul_bounded_prod {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {F : ℝ × Ω → ℝ}
    (hF : Measurable F) {C a b : ℝ} (ha : a < 0)
    (hC : ∀ p, |F p| ≤ C) :
    Integrable (fun p : ℝ × Ω => Real.exp (a * p.1) * F p)
      ((volume.restrict (Ioi b)).prod μ) := by
  have hdom : Integrable (fun p : ℝ × Ω => C * Real.exp (a * p.1))
      ((volume.restrict (Ioi b)).prod μ) := by
    simpa using ((integrableOn_exp_mul_Ioi ha b).const_mul C).mul_prod
      (integrable_const (1 : ℝ) : Integrable (fun _ : Ω => (1 : ℝ)) μ)
  apply hdom.mono' (by fun_prop : Measurable
    (fun p : ℝ × Ω => Real.exp (a * p.1) * F p)).aestronglyMeasurable
  filter_upwards with p
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  exact (mul_le_mul_of_nonneg_left (hC p) (Real.exp_pos _).le).trans_eq (mul_comm _ _)

end BGW.Probability
