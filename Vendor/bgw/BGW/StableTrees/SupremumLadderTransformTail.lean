/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.SupremumLadderTransformCumulative
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Tail estimates for cumulative clock integrals

Tail domination of the weight measure transfers, by Tonelli, to integrals of a
nondecreasing clock. A half-rate discount makes the estimates uniform at large times.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace BGW.StableTrees

/-- A bound on weight tails controls the cumulative clock integral.

Reference: Bertoin, *Lévy Processes*, Chapter VI. -/
theorem lintegral_clock_le_of_tail_le {m : ℝ≥0 → ℝ}
    (hm : Monotone m ∧ Continuous m) (hm0 : m 0 = 0)
    (ν : Measure ℝ) [SFinite ν] (v : ℝ → ℝ≥0∞) (C : ℝ≥0∞)
    (hv : Measurable v) (hν : ∀ t : ℝ, 0 < t → ν (Ioi t) ≤ C * v t) :
    (∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (m s.toNNReal) ∂ν) ≤
      C * ∫⁻ t in Ioi (0 : ℝ), v t ∂(pathStieltjes m).measure := by
  rw [← pathStieltjes_lintegral_tail hm hm0, ← lintegral_const_mul _ hv]
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact hν t ht

/-- Cumulative mass beyond `T` is bounded by the half-rate clock potential times
`exp(-q T / 2)`. This uses only domination of tails, allowing atoms in the weight measure.

Reference: Bertoin, *Lévy Processes*, Chapter VI. -/
theorem lintegral_clock_tail_le {m : ℝ≥0 → ℝ}
    (hm : Monotone m ∧ Continuous m) (hm0 : m 0 = 0)
    (ν : Measure ℝ) [SFinite ν] {q : ℝ} (hq : 0 < q)
    (hν : ∀ t : ℝ, 0 ≤ t → ν (Ioi t) ≤ ENNReal.ofReal (Real.exp (-q * t)))
    (T : ℝ≥0) :
    (∫⁻ s in Ioi (T : ℝ), ENNReal.ofReal (m s.toNNReal) ∂ν) ≤
      ENNReal.ofReal (Real.exp (-(q / 2) * T)) *
        ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-(q / 2) * t))
          ∂(pathStieltjes m).measure := by
  have hv : Measurable (fun t : ℝ => ENNReal.ofReal (Real.exp (-(q / 2) * t))) := by
    fun_prop
  have hb (t : ℝ) (ht : 0 < t) :
      (ν.restrict (Ioi (T : ℝ))) (Ioi t) ≤
        ENNReal.ofReal (Real.exp (-(q / 2) * T)) *
          ENNReal.ofReal (Real.exp (-(q / 2) * t)) := by
    rw [Measure.restrict_apply measurableSet_Ioi, Ioi_inter_Ioi]
    calc
      _ ≤ ENNReal.ofReal (Real.exp (-q * max t (T : ℝ))) :=
        hν _ (le_max_of_le_left ht.le)
      _ ≤ _ := by
        rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
        apply ENNReal.ofReal_le_ofReal
        apply Real.exp_le_exp.mpr
        have h₁ := le_max_left t (T : ℝ)
        have h₂ := le_max_right t (T : ℝ)
        nlinarith
  have h := lintegral_clock_le_of_tail_le hm hm0 (ν.restrict (Ioi (T : ℝ))) _ _ hv hb
  simpa only [Measure.restrict_restrict measurableSet_Ioi,
    inter_eq_right.mpr (Ioi_subset_Ioi T.coe_nonneg)] using h

/-- A finite half-rate clock potential gives integrability of the cumulative clock
against any measure with the stated tail bound, together with a real tail estimate.

Reference: Bertoin, *Lévy Processes*, Chapter VI. -/
theorem integrable_clock_and_integral_tail_le {m : ℝ≥0 → ℝ}
    (hm : Monotone m ∧ Continuous m) (hm0 : m 0 = 0)
    (ν : Measure ℝ) [SFinite ν] {q : ℝ} (hq : 0 < q)
    (hν : ∀ t : ℝ, 0 ≤ t → ν (Ioi t) ≤ ENNReal.ofReal (Real.exp (-q * t)))
    (hi : IntegrableOn (fun t : ℝ => Real.exp (-(q / 2) * t)) (Ioi 0)
      (pathStieltjes m).measure) :
    IntegrableOn (fun s : ℝ => m s.toNNReal) (Ioi 0) ν ∧
      ∀ T : ℝ≥0, (∫ s in Ioi (T : ℝ), m s.toNNReal ∂ν) ≤
        Real.exp (-(q / 2) * T) *
          ∫ t in Ioi (0 : ℝ), Real.exp (-(q / 2) * t) ∂(pathStieltjes m).measure := by
  have hn (s : ℝ) : 0 ≤ m s.toNNReal := by
    simpa only [hm0] using hm.1 (zero_le : 0 ≤ s.toNNReal)
  have hbound (T : ℝ≥0) := lintegral_clock_tail_le hm hm0 ν hq hν T
  have hfinite : (∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (m s.toNNReal) ∂ν) < ⊤ := by
    have h := hbound 0
    rw [NNReal.coe_zero, mul_zero, Real.exp_zero, ENNReal.ofReal_one, one_mul,
      ← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ fun t => (Real.exp_pos _).le)] at h
    exact h.trans_lt ENNReal.ofReal_lt_top
  have hci : IntegrableOn (fun s : ℝ => m s.toNNReal) (Ioi 0) ν :=
    ⟨(hm.2.measurable.comp measurable_real_toNNReal).aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal (ae_of_all _ hn)).mpr hfinite⟩
  refine ⟨hci, fun T => ?_⟩
  have h := hbound T
  rw [← ofReal_integral_eq_lintegral_ofReal
    (hci.mono_set (Ioi_subset_Ioi T.coe_nonneg)) (ae_of_all _ hn),
    ← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ fun t => (Real.exp_pos _).le),
    ← ENNReal.ofReal_mul (Real.exp_pos _).le] at h
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h

/-- The difference of two cumulative integrals is controlled on a compact interval by
uniform clock error, and outside it by the two half-rate potentials.

Reference: Bertoin, *Lévy Processes*, Chapter VI. -/
theorem abs_integral_clock_sub_le {m n : ℝ≥0 → ℝ}
    (hm : Monotone m ∧ Continuous m) (hm0 : m 0 = 0)
    (hn : Monotone n ∧ Continuous n) (hn0 : n 0 = 0)
    (ν : Measure ℝ) [SFinite ν] {q : ℝ} (hq : 0 < q)
    (hν : ∀ t : ℝ, 0 ≤ t → ν (Ioi t) ≤ ENNReal.ofReal (Real.exp (-q * t)))
    (hmi : IntegrableOn (fun t : ℝ => Real.exp (-(q / 2) * t)) (Ioi 0)
      (pathStieltjes m).measure)
    (hni : IntegrableOn (fun t : ℝ => Real.exp (-(q / 2) * t)) (Ioi 0)
      (pathStieltjes n).measure)
    (T : ℝ≥0) {E : ℝ} (hE : 0 ≤ E) (he : ∀ t ≤ T, |m t - n t| ≤ E) :
    |(∫ s in Ioi (0 : ℝ), m s.toNNReal ∂ν) - ∫ s in Ioi (0 : ℝ), n s.toNNReal ∂ν| ≤
      E + Real.exp (-(q / 2) * T) *
        ((∫ t in Ioi (0 : ℝ), Real.exp (-(q / 2) * t) ∂(pathStieltjes m).measure) +
          ∫ t in Ioi (0 : ℝ), Real.exp (-(q / 2) * t) ∂(pathStieltjes n).measure) := by
  obtain ⟨hmν, hmT⟩ := integrable_clock_and_integral_tail_le hm hm0 ν hq hν hmi
  obtain ⟨hnν, hnT⟩ := integrable_clock_and_integral_tail_le hn hn0 ν hq hν hni
  have hmass : ν (Ioc (0 : ℝ) T) ≤ 1 := by
    have h := (measure_mono (show Ioc (0 : ℝ) (T : ℝ) ⊆ Ioi 0 from Ioc_subset_Ioi_self)).trans
      (hν 0 le_rfl)
    simpa only [mul_zero, Real.exp_zero, ENNReal.ofReal_one] using h
  have hmassR : ν.real (Ioc (0 : ℝ) T) ≤ 1 := by
    exact (ENNReal.toReal_mono ENNReal.one_ne_top hmass).trans_eq ENNReal.toReal_one
  have hcompact : |∫ s in Ioc (0 : ℝ) T, m s.toNNReal - n s.toNNReal ∂ν| ≤ E := by
    have h := norm_setIntegral_le_of_norm_le_const
      (f := fun s : ℝ => m s.toNNReal - n s.toNNReal) (μ := ν) (C := E)
      (hmass.trans_lt (by simp : (1 : ℝ≥0∞) < ⊤)) (fun s hs => ?_)
    · rw [Real.norm_eq_abs] at h
      exact h.trans (mul_le_of_le_one_right hE hmassR)
    · rw [Real.norm_eq_abs]
      apply he s.toNNReal
      apply NNReal.coe_le_coe.mp
      rw [Real.coe_toNNReal _ hs.1.le]
      exact hs.2
  have htail : |∫ s in Ioi (T : ℝ), m s.toNNReal - n s.toNNReal ∂ν| ≤
      Real.exp (-(q / 2) * T) *
        ((∫ t in Ioi (0 : ℝ), Real.exp (-(q / 2) * t) ∂(pathStieltjes m).measure) +
          ∫ t in Ioi (0 : ℝ), Real.exp (-(q / 2) * t) ∂(pathStieltjes n).measure) := by
    rw [integral_sub (hmν.mono_set (Ioi_subset_Ioi T.coe_nonneg))
      (hnν.mono_set (Ioi_subset_Ioi T.coe_nonneg))]
    have hmpos : 0 ≤ ∫ s in Ioi (T : ℝ), m s.toNNReal ∂ν := by
      apply integral_nonneg
      intro s
      change 0 ≤ m s.toNNReal
      rw [← hm0]
      exact hm.1 zero_le
    have hnpos : 0 ≤ ∫ s in Ioi (T : ℝ), n s.toNNReal ∂ν := by
      apply integral_nonneg
      intro s
      change 0 ≤ n s.toNNReal
      rw [← hn0]
      exact hn.1 zero_le
    have h := abs_sub (∫ s in Ioi (T : ℝ), m s.toNNReal ∂ν)
      (∫ s in Ioi (T : ℝ), n s.toNNReal ∂ν)
    rw [abs_of_nonneg hmpos, abs_of_nonneg hnpos] at h
    calc
      _ ≤ _ := h
      _ ≤ _ := by nlinarith only [hmT T, hnT T]
  rw [← integral_sub hmν hnν]
  have hsplit := intervalIntegral.integral_Ioi_sub_Ioi (hmν.sub hnν) T.coe_nonneg
  rw [intervalIntegral.integral_of_le T.coe_nonneg] at hsplit
  simp only [Pi.sub_apply] at hsplit
  have h := norm_add_le (∫ s in Ioc (0 : ℝ) T, m s.toNNReal - n s.toNNReal ∂ν)
    (∫ s in Ioi (T : ℝ), m s.toNNReal - n s.toNNReal ∂ν)
  have heq : (∫ s in Ioi (0 : ℝ), m s.toNNReal - n s.toNNReal ∂ν) =
      (∫ s in Ioc (0 : ℝ) T, m s.toNNReal - n s.toNNReal ∂ν) +
        ∫ s in Ioi (T : ℝ), m s.toNNReal - n s.toNNReal ∂ν := by linarith only [hsplit]
  rw [heq]
  simp only [Real.norm_eq_abs] at h
  exact h.trans (add_le_add hcompact htail)

end BGW.StableTrees
