/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.SupremumLadderTransformWeight
import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Cumulative representation of weighted occupation

Tonelli identifies the ordinary weighted occupation integral with the same cumulative
weight integral used for the limiting clock.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees

/-- The occupation Stieltjes measure integrates a measure tail as the ordinary time kernel.

Reference: Bertoin, *Lévy Processes*, Chapter VI. -/
theorem lintegral_supOccupation_tail {ε : ℝ} (hε : 0 < ε)
    (f : DLoc) (hf : f.1 0 = 0) (ν : Measure ℝ) [SFinite ν] :
    (∫⁻ t in Ioi (0 : ℝ), ν (Ioi t) ∂(pathStieltjes (supOccupation ε f)).measure) =
      ∫⁻ t in Ioi (0 : ℝ), ν (Ioi t) *
        ENNReal.ofReal (supOccKernel ε (supReflectedFrom 0 f t.toNNReal)) := by
  let k : ℝ → ℝ := fun t => supOccKernel ε (supReflectedFrom 0 f t.toNNReal)
  have hk : Measurable k := by
    have hc : Measurable (fun _ : ℝ => f) := measurable_const
    have hh := (measurable_supAuxKernel ε).comp (measurable_id.prodMk hc)
    exact hh
  let μ := volume.withDensity (fun t => ENNReal.ofReal (k t))
  have hmass (s : ℝ) (hs : 0 < s) :
      μ (Ioo (0 : ℝ) s) = ENNReal.ofReal (supOccupation ε f s.toNNReal) := by
    rw [show μ = volume.withDensity (fun t => ENNReal.ofReal (k t)) from rfl,
      withDensity_apply _ measurableSet_Ioo,
      ← ofReal_integral_eq_lintegral_ofReal
        ((integrableOn_supAuxKernel_Ioc hε f 0 s).mono_set Ioo_subset_Ioc_self)
        (ae_of_all _ fun t => (supOccKernel_mem_Icc hε _).1),
      ← integral_Ioc_eq_integral_Ioo,
      supOccupation_eq_integral_supOccKernel f hf, Real.coe_toNNReal _ hs.le]
  have he := lintegral_tail_eq_lintegral_cumulative μ ν 0
  have hright : (∫⁻ s in Ioi (0 : ℝ), μ (Ioo 0 s) ∂ν) =
      ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (supOccupation ε f s.toNNReal) ∂ν := by
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact hmass s hs
  rw [hright] at he
  rw [pathStieltjes_lintegral_tail
    ⟨monotone_supOccupation hε.le f, continuous_supOccupation hε f⟩ (supOccupation_zero ε f),
    ← he]
  have hv : Measurable (fun t : ℝ => ν (Ioi t)) :=
    (show Antitone (fun t : ℝ => ν (Ioi t)) from
      fun s t hst => measure_mono (Ioi_subset_Ioi hst)).measurable
  rw [show μ = volume.withDensity (fun t => ENNReal.ofReal (k t)) from rfl,
    setLIntegral_withDensity_eq_setLIntegral_mul volume hk.ennreal_ofReal hv measurableSet_Ioi]
  apply lintegral_congr
  intro t
  exact mul_comm _ _

/-- The weighted occupation clock integral is the weighted time integral of its kernel.

Reference: Bertoin, *Lévy Processes*, Chapter VI. -/
theorem lintegral_supOccupation_supWeight {q lam ε : ℝ} (hq : 0 < q) (hlam : 0 ≤ lam)
    (hε : 0 < ε) (f : DLoc) (hf : f.1 0 = 0) :
    (∫⁻ t in Ioi (0 : ℝ),
      ENNReal.ofReal (Real.exp (-q * t - lam * supRunning f t.toNNReal))
        ∂(pathStieltjes (supOccupation ε f)).measure) =
      ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal
        (Real.exp (-q * t - lam * supRunning f t.toNNReal) *
          supOccKernel ε (supReflected f t.toNNReal)) := by
  have he := lintegral_supOccupation_tail hε f hf
    (supWeightStieltjes q lam hq.le hlam f).measure
  have ht : ∀ t ∈ Ioi (0 : ℝ),
      (supWeightStieltjes q lam hq.le hlam f).measure (Ioi t) =
        ENNReal.ofReal (Real.exp (-q * t - lam * supRunning f t.toNNReal)) :=
    fun t ht => supWeightStieltjes_measure_Ioi hq hlam hf ht.le
  rw [setLIntegral_congr_fun measurableSet_Ioi ht] at he
  refine he.trans ?_
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t hpos
  rw [ht t hpos, supReflectedFrom_zero_apply hf, ← ENNReal.ofReal_mul (Real.exp_pos _).le]

end BGW.StableTrees
