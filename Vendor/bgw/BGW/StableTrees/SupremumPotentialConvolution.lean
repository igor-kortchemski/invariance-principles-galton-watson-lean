/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.SupremumPotentialClock
public import BGW.StableTrees.SupremumPotentialTail

/-!
# The reflected occupation convolution

Independence at the exponential clock reduces reflection from a level to the
convolution of the supremum tail with the exponential drawdown density.

Reference: A. E. Kyprianou, *Fluctuations of Lévy Processes with Applications*, 2nd ed.,
Springer, 2014, Chapter 8.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees

private theorem tail_eq_real_Ioi {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {q : ℝ} (hq : 0 < q) (z : ℝ) :
    supExpTail θ q z = ((expClockLaw θ q).map
      (fun p : DLoc × ℝ => supRunning p.1 p.2.toNNReal)).real (Ioi z) := by
  rw [supExpTail_eq_measureReal hθ hq, Measure.real, Measure.real]
  congr 1
  apply measure_congr
  apply (Ioi_ae_eq_Ici' ?_).symm
  rw [Measure.map_apply measurable_supRunning_expTime (measurableSet_singleton z)]
  exact expClockLaw_supRunning_eq hθ hq z

private theorem reflected_from_decomposition {y : ℝ} (hy : 0 ≤ y) (f : DLoc) (t : ℝ≥0) :
    supReflectedFrom y.toNNReal f t = max (y - supRunning f t) 0 + supReflected f t := by
  rw [supReflectedFrom, Real.coe_toNNReal _ hy, supReflected]
  rcases le_total y (supRunning f t) with h | h
  · rw [max_eq_right h, max_eq_right (sub_nonpos.mpr h)]
    ring
  · rw [max_eq_left h, max_eq_left (sub_nonneg.mpr h)]
    ring

private theorem integral_kernel_pair {μ : Measure ℝ} (ε y r : ℝ) :
    (∫ s, supOccKernel ε (max (y - s) 0 + r) ∂μ) =
      (Iio ε).indicator (fun r => ε⁻¹ * μ.real (Ioi (y - ε + r))) r := by
  by_cases hr : r < ε
  · have he : (fun s => supOccKernel ε (max (y - s) 0 + r)) =
        (Ioi (y - ε + r)).indicator (fun _ => ε⁻¹) := by
      funext s
      have hh : max (y - s) 0 + r < ε ↔ y - ε + r < s := by
        rw [← lt_sub_iff_add_lt, max_lt_iff]
        constructor
        · intro h
          linarith [h.1]
        · intro h
          constructor <;> linarith
      simp only [supOccKernel, indicator_apply, mem_Iio, mem_Ioi, hh]
    rw [he, integral_indicator measurableSet_Ioi, setIntegral_const,
      indicator_of_mem (s := Iio ε) hr]
    simp only [smul_eq_mul]
    ring
  · have he : (fun s => supOccKernel ε (max (y - s) 0 + r)) = fun _ => 0 := by
      funext s
      have hh : ¬max (y - s) 0 + r < ε := by linarith [le_max_right (y - s) 0]
      simp [supOccKernel, hh]
    rw [he, integral_zero, indicator_of_notMem (s := Iio ε) hr]

/-- Explicit convolution formula for the occupation resolvent at nonnegative starts. -/
theorem supOccupationResolvent_eq {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {q : ℝ} (hq : 0 < q) {ε : ℝ}
    (hε : 0 < ε) {y : ℝ} (hy : 0 ≤ y) :
    supOccupationResolvent θ q ε y =
      ε⁻¹ * ∫ r in Ioc 0 ε, Real.exp (-(q ^ (1 / θ) * (ε - r))) * supPotential θ q (y - r) := by
  let := isProbabilityMeasure_expClockLaw θ hq
  let Φ := q ^ (1 / θ)
  have hΦ : 0 < Φ := Real.rpow_pos_of_pos hq _
  let := isProbabilityMeasure_expMeasure hΦ
  let μ := (expClockLaw θ q).map (fun p : DLoc × ℝ => supRunning p.1 p.2.toNNReal)
  let F := fun p : ℝ × ℝ => supOccKernel ε (max (y - p.1) 0 + p.2)
  have hFb (p : ℝ × ℝ) : |F p| ≤ ε⁻¹ := by
    obtain ⟨h0, h1⟩ := supOccKernel_mem_Icc hε (max (y - p.1) 0 + p.2)
    rwa [abs_of_nonneg h0]
  have hF : Measurable F := (measurable_supOccKernel ε).comp
    (((measurable_const.sub measurable_fst).max measurable_const).add measurable_snd)
  have hi : Integrable F (μ.prod (expMeasure Φ)) := Integrable.of_bound hF.aestronglyMeasurable
    ε⁻¹ (ae_of_all _ (fun p => by simpa only [Real.norm_eq_abs] using hFb p))
  have hj := (indepFun_supRunning_supReflected_expTime hθ hq).map_prod_eq_prod_map_map
    measurable_supRunning_expTime.aemeasurable measurable_supReflected_expTime.aemeasurable
  rw [law_supReflected_expTime hθ hq] at hj
  have hmap : Measurable (fun p : DLoc × ℝ =>
      (supRunning p.1 p.2.toNNReal, supReflected p.1 p.2.toNNReal)) :=
    measurable_supRunning_expTime.prodMk measurable_supReflected_expTime
  have hclock : (∫ p : DLoc × ℝ, supOccKernel ε (supReflectedFrom y.toNNReal p.1 p.2.toNNReal)
      ∂expClockLaw θ q) = ∫ p, F p ∂μ.prod (expMeasure Φ) := by
    calc
      _ = ∫ p : DLoc × ℝ, F (supRunning p.1 p.2.toNNReal, supReflected p.1 p.2.toNNReal)
          ∂expClockLaw θ q := by
        apply integral_congr_ae
        exact ae_of_all _ (fun p => congrArg (supOccKernel ε)
          (reflected_from_decomposition hy p.1 p.2.toNNReal))
      _ = ∫ p, F p ∂(expClockLaw θ q).map (fun p : DLoc × ℝ =>
          (supRunning p.1 p.2.toNNReal, supReflected p.1 p.2.toNNReal)) :=
        (integral_map hmap.aemeasurable hF.aestronglyMeasurable).symm
      _ = _ := by rw [hj]
  have htail (z : ℝ) : μ.real (Ioi z) = supExpTail θ q z := (tail_eq_real_Ioi hθ hq z).symm
  have hprod : (∫ p, F p ∂μ.prod (expMeasure Φ)) = Φ * ε⁻¹ *
      ∫ r in Ioc 0 ε, Real.exp (-Φ * r) * supExpTail θ q (y - ε + r) := by
    rw [integral_prod_symm F hi]
    change (∫ r, (∫ s, supOccKernel ε (max (y - s) 0 + r) ∂μ) ∂expMeasure Φ) = _
    simp_rw [integral_kernel_pair, htail]
    rw [integral_expMeasure_eq hΦ]
    have he : (fun r => Real.exp (-Φ * r) *
        (Iio ε).indicator (fun r => ε⁻¹ * supExpTail θ q (y - ε + r)) r) =
        (Iio ε).indicator (fun r => ε⁻¹ * (Real.exp (-Φ * r) * supExpTail θ q (y - ε + r))) := by
      funext r
      by_cases hr : r < ε <;> simp [hr, mul_comm, mul_left_comm]
    rw [he, integral_indicator measurableSet_Iio, Measure.restrict_restrict measurableSet_Iio]
    have hset : Iio ε ∩ Ioi (0 : ℝ) = Ioo 0 ε := by
      ext r
      simp only [mem_inter_iff, mem_Iio, mem_Ioi, mem_Ioo]
      tauto
    rw [hset, ← integral_Ioc_eq_integral_Ioo, integral_const_mul]
    ring
  have hswap : (∫ r in Ioc 0 ε, Real.exp (-Φ * r) * supExpTail θ q (y - ε + r)) =
      ∫ r in Ioc 0 ε, Real.exp (-(Φ * (ε - r))) * supExpTail θ q (y - r) := by
    rw [← intervalIntegral.integral_of_le hε.le, ← intervalIntegral.integral_of_le hε.le]
    calc
      _ = ∫ r in (0 : ℝ)..ε,
          Real.exp (-Φ * (ε - r)) * supExpTail θ q (y - ε + (ε - r)) := by
        simpa only [sub_self, sub_zero] using
          (intervalIntegral.integral_comp_sub_left
            (fun r => Real.exp (-Φ * r) * supExpTail θ q (y - ε + r)) ε
            (a := (0 : ℝ)) (b := ε)).symm
      _ = _ := by
        apply intervalIntegral.integral_congr
        intro r _
        change Real.exp (-Φ * (ε - r)) * supExpTail θ q (y - ε + (ε - r)) =
          Real.exp (-(Φ * (ε - r))) * supExpTail θ q (y - r)
        rw [show y - ε + (ε - r) = y - r by ring, neg_mul]
  have hb : ∃ C, ∀ r, |supOccKernel ε r| ≤ C := by
    refine ⟨ε⁻¹, fun r => ?_⟩
    obtain ⟨h0, h1⟩ := supOccKernel_mem_Icc hε r
    rwa [abs_of_nonneg h0]
  rw [supOccupationResolvent, reflectedResolvent_eq_expClockLaw hq (measurable_supOccKernel ε) hb,
    hclock, hprod, hswap]
  have he : (fun r => Real.exp (-(q ^ (1 / θ) * (ε - r))) * supPotential θ q (y - r)) =
      (fun r => q ^ (1 / θ) / q *
        (Real.exp (-(q ^ (1 / θ) * (ε - r))) * supExpTail θ q (y - r))) := by
    funext r
    unfold supPotential
    ring
  rw [he, integral_const_mul]
  dsimp [Φ]
  ring

end BGW.StableTrees
