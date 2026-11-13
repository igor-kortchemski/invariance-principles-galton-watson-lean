/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.Skorokhod.CompleteMetricCore
import Mathlib.Topology.Order.OrderClosed

/-!
# Comparing Billingsley's two distances

On `[0,T]` the comparison has the factor `max 1 T`; the unit-interval formula is its
special case. In particular the logarithmic-slope distance separates paths.
-/

@[expose] public section

open Set Filter
open scoped Topology ENNReal

namespace BGW.Skorokhod

variable {T : ℝ} {E : Type*}

/-- A logarithmic matching of cost at most `r` gives the exponential J1 bound. -/
theorem dist_le_exp_of_completeCost_le [MetricSpace E] (f g : D T E)
    (σ : TimeChange T) {r : ℝ} (hr : 0 ≤ r)
    (hc : completeCost f g σ ≤ ENNReal.ofReal r) :
    dist f g ≤ max 1 T * (Real.exp r - 1) := by
  by_cases hT : 0 ≤ T
  · let : Nonempty (Icc (0 : ℝ) T) := ⟨⟨0, le_rfl, hT⟩⟩
    have hlog : σ.logSlope ≤ ENNReal.ofReal r := (le_max_left _ _).trans hc
    have hpath : ∀ t, dist (f t) (g (σ t)) ≤ r := by
      intro t
      apply (ENNReal.ofReal_le_ofReal_iff hr).mp
      rw [← edist_dist]
      exact (le_iSup (fun s => edist (f s) (g (σ s))) t).trans
        ((le_max_right _ _).trans hc)
    have he : 0 ≤ Real.exp r - 1 := sub_nonneg.mpr (Real.one_le_exp_iff.mpr hr)
    have htime : ∀ t : Icc (0 : ℝ) T,
        |(σ t : ℝ) - t| ≤ max 1 T * (Real.exp r - 1) := by
      intro t
      exact (σ.abs_sub_le_mul_exp_sub_one hr hlog t).trans
        (mul_le_mul_of_nonneg_right (t.2.2.trans (le_max_right _ _)) he)
    have hbound : BddBelow (Set.range fun τ : TimeChange T =>
        max (⨆ t, |(τ t : ℝ) - t|) (⨆ t, dist (f t) (g (τ t)))) := by
      refine ⟨0, ?_⟩
      rintro _ ⟨τ, rfl⟩
      have hb : BddAbove (Set.range fun t : Icc (0 : ℝ) T => |(τ t : ℝ) - t|) :=
        ⟨T, by rintro _ ⟨t, rfl⟩; exact τ.abs_sub_le hT t⟩
      exact (le_ciSup_of_le hb (Classical.arbitrary _) (abs_nonneg _)).trans
        (le_max_left _ _)
    change j1Dist f g ≤ _
    refine (ciInf_le hbound σ).trans (max_le (ciSup_le htime) ?_)
    have hrad : r ≤ max 1 T * (Real.exp r - 1) := by
      have hexp := Real.add_one_le_exp r
      have hmul := mul_le_mul_of_nonneg_right (le_max_left (1 : ℝ) T) he
      nlinarith
    exact ciSup_le fun t => (hpath t).trans hrad
  · have hfg : f = g := by
      ext t
      exact (hT (t.2.1.trans t.2.2)).elim
    rw [hfg, dist_self]
    exact mul_nonneg (le_trans zero_le_one (le_max_left _ _))
      (sub_nonneg.mpr (Real.one_le_exp_iff.mpr hr))

/-- Comparison of the two metrics on `[0,T]`: `d ≤ max 1 T * (exp d° - 1)` (Billingsley 1999,
(12.17), stated there for `T = 1`; the factor `T` comes from `|σ t - t| ≤ t (exp ‖σ‖° - 1)`). -/
theorem dist_le_exp_j1CompleteDist_sub_one [MetricSpace E] (f g : D T E) :
    dist f g ≤ max 1 T * (Real.exp (j1CompleteDist f g) - 1) := by
  have hbound : ∀ r : ℝ, j1CompleteDist f g < r →
      dist f g ≤ max 1 T * (Real.exp r - 1) := by
    intro r hr
    obtain ⟨σ, hσ⟩ := exists_completeCost_lt f g hr
    exact dist_le_exp_of_completeCost_le f g σ
      ((j1CompleteDist_nonneg f g).trans hr.le) hσ.le
  have hcont : Continuous (fun r : ℝ => max 1 T * (Real.exp r - 1)) :=
    continuous_const.mul (Real.continuous_exp.sub continuous_const)
  exact ge_of_tendsto (hcont.continuousWithinAt (s := Ioi (j1CompleteDist f g))
    (x := j1CompleteDist f g))
    (Filter.mem_of_superset self_mem_nhdsWithin fun r hr => hbound r hr)

/-- Zero logarithmic-slope distance implies equality of paths. -/
theorem eq_of_j1CompleteDist_eq_zero [MetricSpace E] {f g : D T E}
    (h : j1CompleteDist f g = 0) : f = g := by
  apply dist_le_zero.mp
  simpa [h] using dist_le_exp_j1CompleteDist_sub_one f g

end BGW.Skorokhod
