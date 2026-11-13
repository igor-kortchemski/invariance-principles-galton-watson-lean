/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.SupremumAuxLocalTimeBasic

/-!
# Extended occupation limit for the germ argument

The ENNReal occupation limsup is monotone on every path and prefix measurable.
This local helper uses only `supAuxLimit`, without any identification of the public local time.
Its germ zero-one law does not by itself exclude the zero clock: the mean potential must
first be established independently of recurrence.

## References

* J. Bertoin, *Lévy Processes*, Cambridge University Press, 1996, Chapter IV.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees

/-- The chosen auxiliary cutoffs are positive, including outside the stable index range. -/
theorem supAuxEps_pos (θ : ℝ) (k : ℕ) : 0 < supAuxEps θ k := by
  classical
  by_cases hθ : 1 < θ ∧ θ ≤ 2
  · exact (isSupAuxEpsSeq_supAuxEps hθ).1 k
  · simp only [supAuxEps, dite_eq_right hθ]
    positivity

/-- Extended occupation limsup, used locally to form an everywhere-monotone germ event. -/
noncomputable def supAuxGermClock (θ : ℝ) (f : DLoc) (t : ℝ≥0) : ℝ≥0∞ :=
  limsup (fun k => ENNReal.ofReal (supOccupation (supAuxEps θ k) f t)) atTop

/-- The extended helper is monotone even on paths where the real limsup is unbounded. -/
theorem monotone_supAuxGermClock (θ : ℝ) (f : DLoc) : Monotone (supAuxGermClock θ f) := by
  intro s t hst
  exact limsup_le_limsup (Eventually.of_forall fun k => ENNReal.ofReal_le_ofReal
    (monotone_supOccupation (supAuxEps_pos θ k).le f hst))

/-- The extended helper starts at zero on every path. -/
theorem supAuxGermClock_zero (θ : ℝ) (f : DLoc) : supAuxGermClock θ f 0 = 0 := by
  simp only [supAuxGermClock, supOccupation_zero, ENNReal.ofReal_zero, limsup_const]

/-- The extended helper is jointly measurable. -/
theorem measurable_supAuxGermClock_uncurry (θ : ℝ) :
    Measurable (fun p : ℝ≥0 × DLoc => supAuxGermClock θ p.2 p.1) := by
  exact Measurable.limsup fun k =>
    (measurable_supOccupation_uncurry.comp
      (measurable_const.prodMk measurable_id)).ennreal_ofReal

/-- Every fixed-time extended helper depends measurably only on that time's raw prefix. -/
theorem measurable_rawFiltration_supAuxGermClock (θ : ℝ) (t : ℝ≥0) :
    Measurable[DLoc.rawFiltration t] (fun f : DLoc => supAuxGermClock θ f t) := by
  exact Measurable.limsup fun k =>
    (measurable_rawFiltration_supOccupation (supAuxEps θ k) t).ennreal_ofReal

/-- One event identifies the extended limsup with the finite real clock at every time. -/
theorem ae_supAuxGermClock_eq {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∀ t : ℝ≥0,
      supAuxGermClock θ f t = ENNReal.ofReal (supAuxLocalTime θ f t) := by
  filter_upwards [ae_supAuxLocalTime_continuous hθ,
    ae_tendsto_supOccupation_supAuxEps_uniform hθ] with f hf hu
  intro t
  have hcompact : IsCompact (Iic t) := by
    simpa only [Icc, Iic, zero_le, true_and] using
      (isCompact_Icc : IsCompact (Icc (0 : ℝ≥0) t))
  let : CompactSpace (Iic t) := isCompact_iff_compactSpace.mp hcompact
  have hb (k : ℕ) : BddAbove (range (fun u : Iic t =>
      |supOccupation (supAuxEps θ k) f u - supAuxLocalTime θ f u|)) := by
    exact (isCompact_range
      ((((continuous_supOccupation (supAuxEps_pos θ k) f).sub hf.2.2).abs).comp
        continuous_subtype_val)).bddAbove
  have hc : Tendsto (fun k => supOccupation (supAuxEps θ k) f t) atTop
      (𝓝 (supAuxLocalTime θ f t)) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    simp only [Real.dist_eq]
    exact squeeze_zero (fun k => abs_nonneg _) (fun k => le_ciSup (hb k) ⟨t, le_rfl⟩) (hu t)
  exact (ENNReal.continuous_ofReal.continuousAt.tendsto.comp hc).limsup_eq

end BGW.StableTrees
