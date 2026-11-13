/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.Skorokhod.CompleteMetricInterpolation
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.Order.IntermediateValue

/-!
# Limits of time changes with bounded logarithmic slope

A uniform slope bound prevents degeneration of a pointwise limit: its lower secant bound
remains strictly positive. Logarithmic slope bounds pass to limits of time changes.
-/

@[expose] public section

open Set Filter
open scoped Topology ENNReal

namespace BGW.Skorokhod

variable {T : ℝ}

/-- A logarithmic slope bound is equivalent to exponential two-sided secant bounds. -/
theorem TimeChange.secant_bounds_of_logSlope_le (σ : TimeChange T) {r : ℝ} (hr : 0 ≤ r)
    (hσ : σ.logSlope ≤ ENNReal.ofReal r) {s t : Icc (0 : ℝ) T} (hst : s < t) :
    Real.exp (-r) * ((t : ℝ) - s) ≤ (σ t : ℝ) - σ s ∧
      (σ t : ℝ) - σ s ≤ Real.exp r * ((t : ℝ) - s) := by
  have hpos : 0 < (t : ℝ) - s := sub_pos.mpr hst
  have hratio : 0 < ((σ t : ℝ) - σ s) / ((t : ℝ) - s) :=
    div_pos (sub_pos.mpr (σ.strictMono hst)) hpos
  have habs := (ENNReal.ofReal_le_ofReal_iff hr).mp
    ((σ.ofReal_abs_log_le_logSlope hst).trans hσ)
  exact ⟨(le_div_iff₀ hpos).mp ((Real.le_log_iff_exp_le hratio).mp (abs_le.mp habs).1),
    (div_le_iff₀ hpos).mp ((Real.log_le_iff_le_exp hratio).mp (abs_le.mp habs).2)⟩

/-- Logarithmic slope bounds pass to pointwise limits that are time changes. -/
theorem TimeChange.logSlope_le_of_tendsto {κ : Type*} {l : Filter κ} [l.NeBot]
    (σ : κ → TimeChange T) (τ : TimeChange T)
    (hlim : ∀ t, Tendsto (fun n => (σ n t : ℝ)) l (𝓝 (τ t : ℝ)))
    {r : ℝ} (hr : 0 ≤ r) (hσ : ∀ᶠ n in l, (σ n).logSlope ≤ ENNReal.ofReal r) :
    τ.logSlope ≤ ENNReal.ofReal r := by
  apply τ.logSlope_le_of_secant_bounds
  intro s t hst
  have hdiff := (hlim t).sub (hlim s)
  have hbounds : ∀ᶠ n in l,
      Real.exp (-r) * ((t : ℝ) - s) ≤ (σ n t : ℝ) - σ n s ∧
        (σ n t : ℝ) - σ n s ≤ Real.exp r * ((t : ℝ) - s) := by
    filter_upwards [hσ] with n hn
    exact (σ n).secant_bounds_of_logSlope_le hr hn hst
  exact ⟨ge_of_tendsto hdiff (hbounds.mono fun _ h => h.1),
    le_of_tendsto hdiff (hbounds.mono fun _ h => h.2)⟩

/-- A continuous pointwise limit of time changes with uniformly bounded logarithmic slope
is itself a time change. -/
theorem exists_timeChange_of_tendsto_bounded_logSlope (hT : 0 ≤ T)
    (σ : ℕ → TimeChange T) (f : C(Icc (0 : ℝ) T, Icc (0 : ℝ) T))
    (hlim : ∀ t, Tendsto (fun n => (σ n t : ℝ)) atTop (𝓝 (f t : ℝ)))
    {r : ℝ} (hr : 0 ≤ r) (hσ : ∀ n, (σ n).logSlope ≤ ENNReal.ofReal r) :
    ∃ τ : TimeChange T, ∀ t, τ t = f t := by
  let z : Icc (0 : ℝ) T := ⟨0, le_rfl, hT⟩
  let b : Icc (0 : ℝ) T := ⟨T, hT, le_rfl⟩
  have hfz : (f z : ℝ) = 0 := by
    apply tendsto_nhds_unique (hlim z)
    simpa only [z, TimeChange.apply_zero _ hT] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  have hfb : (f b : ℝ) = T := by
    apply tendsto_nhds_unique (hlim b)
    simpa only [b, TimeChange.apply_top _ hT] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => T) atTop (𝓝 T))
  have hstrict : StrictMono f := by
    intro s t hst
    have hlower : Real.exp (-r) * ((t : ℝ) - s) ≤ (f t : ℝ) - f s :=
      ge_of_tendsto ((hlim t).sub (hlim s)) (Filter.Eventually.of_forall fun n =>
        ((σ n).secant_bounds_of_logSlope_le hr (hσ n) hst).1)
    have hpos := mul_pos (Real.exp_pos (-r)) (sub_pos.mpr (show (s : ℝ) < t from hst))
    change (f s : ℝ) < f t
    linarith
  have hsurj : Function.Surjective f := by
    let : PreconnectedSpace (Icc (0 : ℝ) T) :=
      Subtype.preconnectedSpace isPreconnected_Icc
    intro u
    have hu : (u : ℝ) ∈ Icc (f z : ℝ) (f b : ℝ) := by
      rw [hfz, hfb]
      exact u.2
    obtain ⟨t, ht⟩ := intermediate_value_univ z b
      (continuous_subtype_val.comp f.continuous) hu
    exact ⟨t, Subtype.ext ht⟩
  exact ⟨StrictMono.orderIsoOfSurjective f hstrict hsurj, fun _ => rfl⟩

/-- Composing a càdlàg path with a time change preserves the càdlàg property. -/
theorem isCadlag_comp_timeChange {E : Type*} [TopologicalSpace E] {f : Icc (0 : ℝ) T → E}
    (hf : IsCadlag f) (σ : TimeChange T) : IsCadlag (f ∘ σ) where
  isRightContinuous t := by
    apply (hf.isRightContinuous (σ t)).tendsto.comp
    apply tendsto_nhdsWithin_iff.mpr
    exact ⟨σ.continuous.continuousAt.tendsto.mono_left nhdsWithin_le_nhds,
      eventually_mem_nhdsWithin.mono fun s hs => σ.strictMono hs⟩
  tendsto_nhdsLT t := by
    obtain ⟨a, ha⟩ := hf.tendsto_nhdsLT (σ t)
    refine ⟨a, ha.comp ?_⟩
    apply tendsto_nhdsWithin_iff.mpr
    exact ⟨σ.continuous.continuousAt.tendsto.mono_left nhdsWithin_le_nhds,
      eventually_mem_nhdsWithin.mono fun s hs => σ.strictMono hs⟩

end BGW.Skorokhod
