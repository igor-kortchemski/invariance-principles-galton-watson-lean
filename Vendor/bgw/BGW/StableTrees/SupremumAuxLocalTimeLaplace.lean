/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.SupremumAuxLocalTimeStieltjes
public import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Extended discounted cumulative-integral formula

Tonelli proves the Laplace formula before any finiteness assertion. In particular no
convergence of Stieltjes measures and no recurrence assumption are needed.

## References

* J. Bertoin, *Lévy Processes*, Cambridge University Press, 1996, Chapter IV.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace BGW.StableTrees

/-- Tonelli's discounted cumulative-integral formula, valid even when both sides are infinite. -/
theorem lintegral_exp_eq_lintegral_cumulative (μ : Measure ℝ) [SFinite μ]
    {q : ℝ} (hq : 0 < q) (s : ℝ) :
    (∫⁻ t in Ioi s, ENNReal.ofReal (Real.exp (-q * t)) ∂μ) =
      ENNReal.ofReal q * ∫⁻ u in Ioi s,
        ENNReal.ofReal (Real.exp (-q * u)) * μ (Ioc s u) := by
  let ν := volume.restrict (Ioi s)
  let ρ := μ.restrict (Ioi s)
  let w : ℝ → ℝ≥0∞ := fun u => ENNReal.ofReal (Real.exp (-q * u))
  let K : ℝ × ℝ → ℝ≥0∞ := fun p => if p.1 ≤ p.2 then w p.2 else 0
  have hw : Measurable w :=
    (Real.measurable_exp.comp (measurable_const.mul measurable_id)).ennreal_ofReal
  have hK : Measurable K := (hw.comp measurable_snd).ite
    (measurableSet_le measurable_fst measurable_snd) measurable_const
  have hinner (t : ℝ) (ht : s < t) :
      (∫⁻ u, K (t, u) ∂ν) = w t * (ENNReal.ofReal q)⁻¹ := by
    change (∫⁻ u, (Ici t).indicator w u ∂ν) = _
    rw [lintegral_indicator measurableSet_Ici, Measure.restrict_restrict measurableSet_Ici,
      inter_eq_left.mpr (Ici_subset_Ioi.mpr ht)]
    have hi : IntegrableOn (fun u => Real.exp (-q * u)) (Ici t) :=
      (integrableOn_Ici_iff_integrableOn_Ioi (by finiteness)).mpr
        (integrableOn_exp_mul_Ioi (neg_neg_of_pos hq) t)
    rw [show w = fun u => ENNReal.ofReal (Real.exp (-q * u)) from rfl,
      ← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ fun u => (Real.exp_pos _).le),
      integral_Ici_eq_integral_Ioi, integral_exp_mul_Ioi (neg_neg_of_pos hq)]
    have he : -Real.exp (-q * t) / -q = Real.exp (-q * t) / q := by ring
    rw [he, ENNReal.ofReal_div_of_pos hq, div_eq_mul_inv]
  have hother (u : ℝ) : (∫⁻ t, K (t, u) ∂ρ) = w u * μ (Ioc s u) := by
    change (∫⁻ t, (Iic u).indicator (fun _ : ℝ => w u) t ∂ρ) = _
    rw [lintegral_indicator measurableSet_Iic, lintegral_const,
      Measure.restrict_apply_univ, Measure.restrict_apply measurableSet_Iic, Iic_inter_Ioi]
  have hswap := lintegral_lintegral_swap (μ := ρ) (ν := ν)
    (f := fun t u : ℝ => K (t, u)) hK.aemeasurable
  have hleft : (∫⁻ t, ∫⁻ u, K (t, u) ∂ν ∂ρ) =
      (∫⁻ t, w t ∂ρ) * (ENNReal.ofReal q)⁻¹ := by
    rw [← lintegral_mul_const _ hw]
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact hinner t ht
  have hright : (∫⁻ u, ∫⁻ t, K (t, u) ∂ρ ∂ν) =
      ∫⁻ u, w u * μ (Ioc s u) ∂ν := by
    simp_rw [hother]
  rw [hleft, hright] at hswap
  rw [← hswap]
  have hq0 : ENNReal.ofReal q ≠ 0 := (ENNReal.ofReal_pos.mpr hq).ne'
  rw [mul_left_comm, ENNReal.mul_inv_cancel hq0 ENNReal.ofReal_ne_top, mul_one]

/-- The extended Stieltjes Laplace formula needs no integrability or boundary hypothesis. -/
theorem pathStieltjes_lintegral_exp {m : ℝ≥0 → ℝ} (hm : Monotone m ∧ Continuous m)
    {q : ℝ} (hq : 0 < q) (s : ℝ≥0) :
    (∫⁻ t in Ioi (s : ℝ), ENNReal.ofReal (Real.exp (-q * t))
      ∂(pathStieltjes m).measure) =
      ENNReal.ofReal q * ∫⁻ t in Ioi (s : ℝ),
        ENNReal.ofReal (Real.exp (-q * t)) * ENNReal.ofReal (m t.toNNReal - m s) := by
  rw [lintegral_exp_eq_lintegral_cumulative _ hq]
  simp only [pathStieltjes_measure_Ioc hm, Real.toNNReal_coe]

/-- The same Tonelli identity for a nonnegative time kernel and its ordinary primitive. -/
theorem lintegral_exp_mul_eq_primitive {k : ℝ → ℝ} (hk : Measurable k)
    (hk0 : ∀ t, 0 ≤ k t) {q : ℝ} (hq : 0 < q) (s : ℝ)
    (hloc : ∀ t, IntegrableOn k (Ioc s t)) :
    (∫⁻ t in Ioi s, ENNReal.ofReal (Real.exp (-q * t) * k t)) =
      ENNReal.ofReal q * ∫⁻ t in Ioi s,
        ENNReal.ofReal (Real.exp (-q * t)) * ENNReal.ofReal (∫ u in Ioc s t, k u) := by
  let μ := volume.withDensity (fun t => ENNReal.ofReal (k t))
  have hw : Measurable (fun t : ℝ => ENNReal.ofReal (Real.exp (-q * t))) :=
    (Real.measurable_exp.comp (measurable_const.mul measurable_id)).ennreal_ofReal
  have hmass (t : ℝ) : μ (Ioc s t) = ENNReal.ofReal (∫ u in Ioc s t, k u) := by
    rw [show μ = volume.withDensity (fun t => ENNReal.ofReal (k t)) from rfl,
      withDensity_apply _ measurableSet_Ioc]
    exact (ofReal_integral_eq_lintegral_ofReal (hloc t) (ae_of_all _ hk0)).symm
  have he := lintegral_exp_eq_lintegral_cumulative μ hq s
  have hleft : (∫⁻ t in Ioi s, ENNReal.ofReal (Real.exp (-q * t)) ∂μ) =
      ∫⁻ t in Ioi s, ENNReal.ofReal (Real.exp (-q * t) * k t) := by
    rw [show μ = volume.withDensity (fun t => ENNReal.ofReal (k t)) from rfl,
      setLIntegral_withDensity_eq_setLIntegral_mul volume hk.ennreal_ofReal hw measurableSet_Ioi]
    apply lintegral_congr
    intro t
    change ENNReal.ofReal (k t) * ENNReal.ofReal (Real.exp (-q * t)) = _
    rw [mul_comm, ← ENNReal.ofReal_mul (Real.exp_pos _).le]
  simpa only [hleft, hmass] using he

/-- A measurable kernel has a measurable primitive with a moving upper endpoint. -/
theorem measurable_integral_Ioc (k : ℝ → ℝ) (hk : Measurable k) (s : ℝ) :
    Measurable (fun t : ℝ => ∫ u in Ioc s t, k u) := by
  have hm : Measurable (fun p : ℝ × ℝ =>
      {p : ℝ × ℝ | s < p.2 ∧ p.2 ≤ p.1}.indicator (fun p => k p.2) p) :=
    (hk.comp measurable_snd).indicator
      ((measurableSet_lt measurable_const measurable_snd).inter
        (measurableSet_le measurable_snd measurable_fst))
  have hi := hm.stronglyMeasurable.integral_prod_right' (ν := volume)
  have he : (fun t : ℝ => ∫ u,
      {p : ℝ × ℝ | s < p.2 ∧ p.2 ≤ p.1}.indicator (fun p => k p.2) (t, u)) =
      (fun t : ℝ => ∫ u in Ioc s t, k u) := by
    funext t
    exact integral_indicator measurableSet_Ioc
  rw [he] at hi
  exact hi.measurable

/-- A finite discounted kernel integral makes the discounted primitive integrable, and
converts the extended Tonelli formula into the ordinary real integral identity. -/
theorem integral_exp_mul_eq_primitive {k : ℝ → ℝ} (hk : Measurable k)
    (hk0 : ∀ t, 0 ≤ k t) {q : ℝ} (hq : 0 < q) (s : ℝ)
    (hloc : ∀ t, IntegrableOn k (Ioc s t))
    (hi : IntegrableOn (fun t => Real.exp (-q * t) * k t) (Ioi s)) :
    IntegrableOn (fun t => Real.exp (-q * t) * (∫ u in Ioc s t, k u)) (Ioi s) ∧
      (∫ t in Ioi s, Real.exp (-q * t) * k t) =
        q * ∫ t in Ioi s, Real.exp (-q * t) * (∫ u in Ioc s t, k u) := by
  let p : ℝ → ℝ := fun t => ∫ u in Ioc s t, k u
  have hp : Measurable p := measurable_integral_Ioc k hk s
  have hp0 (t : ℝ) : 0 ≤ p t := integral_nonneg hk0
  have hP0 : ∀ t, 0 ≤ Real.exp (-q * t) * p t :=
    fun t => mul_nonneg (Real.exp_pos _).le (hp0 t)
  have hK0 : ∀ t, 0 ≤ Real.exp (-q * t) * k t :=
    fun t => mul_nonneg (Real.exp_pos _).le (hk0 t)
  have he := lintegral_exp_mul_eq_primitive hk hk0 hq s hloc
  have hB : (∫⁻ t in Ioi s, ENNReal.ofReal (Real.exp (-q * t) * p t)) < ⊤ := by
    have hA : (∫⁻ t in Ioi s, ENNReal.ofReal (Real.exp (-q * t) * k t)) < ⊤ := by
      rw [← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ hK0)]
      exact ENNReal.ofReal_lt_top
    apply lt_top_iff_ne_top.mpr
    intro h
    have hprod : (∫⁻ t in Ioi s, ENNReal.ofReal (Real.exp (-q * t)) *
        ENNReal.ofReal (p t)) = ⊤ := by
      simpa only [ENNReal.ofReal_mul (Real.exp_pos _).le] using h
    rw [hprod, ENNReal.mul_top (ENNReal.ofReal_pos.mpr hq).ne'] at he
    exact hA.ne he
  have hPi : IntegrableOn (fun t => Real.exp (-q * t) * p t) (Ioi s) := by
    have hPm : Measurable (fun t => Real.exp (-q * t) * p t) :=
      (Real.measurable_exp.comp (measurable_const.mul measurable_id)).mul hp
    refine ⟨hPm.aestronglyMeasurable, ?_⟩
    exact (hasFiniteIntegral_iff_ofReal (ae_of_all _ hP0)).mpr hB
  refine ⟨hPi, ?_⟩
  have hBreal := ofReal_integral_eq_lintegral_ofReal hPi (ae_of_all _ hP0)
  have hAreal := ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ hK0)
  simp_rw [← ENNReal.ofReal_mul (Real.exp_pos _).le] at he
  rw [← hAreal, ← hBreal] at he
  have hr := congrArg ENNReal.toReal he
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hq.le,
    ENNReal.toReal_ofReal (integral_nonneg hK0),
    ENNReal.toReal_ofReal (integral_nonneg hP0)] using hr

end BGW.StableTrees
