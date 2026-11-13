/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.SupremumPotentialLaplace
public import BGW.StableTrees.SupremumPotentialUniqueness
import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# Density of the stable supremum at an exponential clock

The signed tilted density is identified from its Laplace integrals before its
nonnegativity is deduced. Continuity then gives pointwise positivity.

Reference: A. E. Kyprianou, *Fluctuations of Lévy Processes with Applications*, 2nd ed.,
Springer, 2014, Chapter 8.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees

private theorem supremum_density_pair {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {q : ℝ} (hq : 0 < q) :
    ((expClockLaw θ q).map (fun p : DLoc × ℝ => supRunning p.1 p.2.toNNReal) =
      (volume.restrict (Ioi 0)).withDensity (fun x => ENNReal.ofReal
        (q / q ^ (1 / θ) * (stableSeriesDeriv θ q x - q ^ (1 / θ) * stableSeries θ q x)))) ∧
      ∀ᵐ x ∂volume.restrict (Ioi 0),
        0 ≤ q / q ^ (1 / θ) * (stableSeriesDeriv θ q x - q ^ (1 / θ) * stableSeries θ q x) := by
  let := isProbabilityMeasure_expClockLaw θ hq
  let μ := (expClockLaw θ q).map (fun p : DLoc × ℝ => supRunning p.1 p.2.toNNReal)
  have hμ : μ (Iio 0) = 0 := by
    rw [Measure.map_apply measurable_supRunning_expTime measurableSet_Iio,
      measure_eq_zero_iff_ae_notMem]
    filter_upwards [ae_nonneg_supRunning_supReflected_expTime hθ hq] with p hp
    exact not_lt_of_ge hp.1
  have hν : (volume.restrict (Ioi (0 : ℝ))) (Iio 0) = 0 := by
    rw [Measure.restrict_apply measurableSet_Iio]
    have he : Iio (0 : ℝ) ∩ Ioi 0 = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.2
      intro x hx
      have hx0 : x < 0 := hx.1
      have hx1 : 0 < x := hx.2
      linarith
    rw [he, measure_empty]
  have hf : Measurable (fun x => q / q ^ (1 / θ) *
      (stableSeriesDeriv θ q x - q ^ (1 / θ) * stableSeries θ q x)) :=
    measurable_const.mul ((measurable_stableSeriesDeriv hθ q).sub
      (measurable_const.mul (continuous_stableSeries hθ q).measurable))
  have hPhi : 0 < q ^ (1 / θ) := Real.rpow_pos_of_pos hq _
  let a := q ^ (1 / θ) + 1
  have ha : 0 < a := by dsimp [a]; linarith
  have hpa : q ^ (1 / θ) < a := by dsimp [a]; linarith
  have hIa := integral_exp_neg_mul_stableSeries hθ hq hpa
  have hi : Integrable (fun x => Real.exp (-a * x) * (q / q ^ (1 / θ) *
      (stableSeriesDeriv θ q x - q ^ (1 / θ) * stableSeries θ q x))) (volume.restrict (Ioi 0)) := by
    have hh := (hIa.2.1.sub (hIa.1.const_mul (q ^ (1 / θ)))).const_mul (q / q ^ (1 / θ))
    convert hh using 1
    funext x
    dsimp only [Pi.sub_apply]
    ring
  apply measure_eq_withDensity_of_laplace_halfline hμ hν hf ha hi
  intro lam hlam
  have hlp : q ^ (1 / θ) < lam := hpa.trans hlam
  have hl : 0 < lam := ha.trans hlam
  have hlt : q < lam ^ θ := (Real.rpow_inv_lt_iff_of_pos hq.le hl.le
    (by linarith [hθ.1] : 0 < θ)).1 (by simpa only [one_div] using hlp)
  have hm : Measurable (fun x : ℝ => Real.exp (-lam * x)) := by fun_prop
  change (∫ x, Real.exp (-lam * x) ∂(expClockLaw θ q).map
    (fun p : DLoc × ℝ => supRunning p.1 p.2.toNNReal)) = _
  rw [integral_map measurable_supRunning_expTime.aemeasurable hm.aestronglyMeasurable,
    integral_exp_neg_supRunning_expTime hθ hq hl.le hlp.ne']
  have he : (fun x => Real.exp (-lam * x) * (q / q ^ (1 / θ) *
      (stableSeriesDeriv θ q x - q ^ (1 / θ) * stableSeries θ q x))) =
      (fun x => q / q ^ (1 / θ) * (Real.exp (-lam * x) *
        (stableSeriesDeriv θ q x - q ^ (1 / θ) * stableSeries θ q x))) := by funext x; ring
  rw [he, integral_const_mul, integral_exp_neg_mul_stableSeriesDeriv_sub hθ hq hlp]
  field_simp [hPhi.ne', (sub_pos.mpr hlt).ne', (sub_neg.mpr hlt).ne]
  ring

/-- Density of the supremum at an exponential time, with its exact normalization. -/
theorem map_supRunning_expClockLaw {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {q : ℝ} (hq : 0 < q) :
    (expClockLaw θ q).map (fun p : DLoc × ℝ => supRunning p.1 p.2.toNNReal) =
      (volume.restrict (Ioi 0)).withDensity (fun x => ENNReal.ofReal
        (q / q ^ (1 / θ) * (stableSeriesDeriv θ q x - q ^ (1 / θ) * stableSeries θ q x))) := by
  exact (supremum_density_pair hθ hq).1

/-- Positivity of the density (a consequence, not an input). -/
theorem stableSeriesDeriv_sub_nonneg {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {q : ℝ} (hq : 0 < q)
    {x : ℝ} (hx : 0 < x) : 0 ≤ stableSeriesDeriv θ q x - q ^ (1 / θ) * stableSeries θ q x := by
  have hc : ContinuousOn (fun y => stableSeriesDeriv θ q y - q ^ (1 / θ) * stableSeries θ q y)
      (Ioi 0) := (continuousOn_stableSeriesDeriv hθ q).sub
    (((continuousOn_stableSeries hθ q).mono (fun _ hy => le_of_lt hy)).const_mul
      (q ^ (1 / θ)))
  have hcoef : 0 < q / q ^ (1 / θ) := div_pos hq (Real.rpow_pos_of_pos hq _)
  have hae : ∀ᵐ y ∂volume.restrict (Ioi 0),
      0 ≤ stableSeriesDeriv θ q y - q ^ (1 / θ) * stableSeries θ q y :=
    (supremum_density_pair hθ hq).2.mono (fun _ hy => (mul_nonneg_iff_of_pos_left hcoef).1 hy)
  have he := Measure.eqOn_open_of_ae_eq (μ := (volume : Measure ℝ))
    (hae.mono (fun _ hy => (max_eq_left hy).symm)) isOpen_Ioi hc
    (hc.sup continuousOn_const)
  have heq := he hx
  dsimp only at heq
  rw [heq]
  exact le_max_right _ _

/-- The supremum at an exponential time has no atoms. -/
theorem expClockLaw_supRunning_eq {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {q : ℝ} (hq : 0 < q) (x : ℝ) :
    expClockLaw θ q {p | supRunning p.1 p.2.toNNReal = x} = 0 := by
  have he : ((expClockLaw θ q).map
      (fun p : DLoc × ℝ => supRunning p.1 p.2.toNNReal)) {x} = 0 := by
    rw [map_supRunning_expClockLaw hθ hq]
    exact measure_singleton x
  rwa [Measure.map_apply measurable_supRunning_expTime (measurableSet_singleton x)] at he

end BGW.StableTrees
