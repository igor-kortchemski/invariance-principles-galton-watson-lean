/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.SupremumCorrectionBasic

/-!
# Progressive measurability of the raw error process

Progressiveness of the raw clock follows from measurability of the real limsup on each
restricted product sigma algebra, without modifying exceptional paths.

## References

* J. Bertoin, *Lévy Processes*, Cambridge University Press, 1996, Chapter IV.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees

/-- The occupation process is strongly progressive for each positive width. -/
theorem isStronglyProgressive_supOccupation {ε : ℝ} (hε : 0 < ε) :
    IsStronglyProgressive DLoc.filtration (fun t f => supOccupation ε f t) := by
  have ha : StronglyAdapted DLoc.filtration (fun t f => supOccupation ε f t) := by
    intro t
    exact ((measurable_rawFiltration_supOccupation ε t).mono
      (DLoc.rawFiltration.le_rightCont t) le_rfl).stronglyMeasurable
  exact ha.isStronglyProgressive_of_continuous (continuous_supOccupation hε)

/-- The raw auxiliary clock is strongly progressive, including on exceptional paths. -/
theorem isStronglyProgressive_supAuxLocalTime {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    IsStronglyProgressive DLoc.filtration (fun t f => supAuxLocalTime θ f t) := by
  intro T
  have hm (k : ℕ) :=
    (isStronglyProgressive_supOccupation ((isSupAuxEpsSeq_supAuxEps hθ).1 k) T).measurable
  exact (Measurable.limsup hm).stronglyMeasurable

/-- The error process is strongly progressive for the raw auxiliary clock. -/
theorem isStronglyProgressive_errorMartingale {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {ε : ℝ}
    (hε : 0 < ε) :
    IsStronglyProgressive DLoc.filtration (fun t f => errorMartingale θ ε t f) := by
  have hw : IsStronglyProgressive DLoc.filtration
      (fun t f => occupationCorrection θ ε t f) := by
    intro T
    exact (((measurable_supCorrection θ ε).comp
      (isStronglyProgressive_supReflectedFrom 0 T).measurable).sub
        measurable_const).stronglyMeasurable
  exact ((isStronglyProgressive_supOccupation hε).sub
    (isStronglyProgressive_supAuxLocalTime hθ)).add hw

/-- The error starts at zero almost surely. -/
theorem ae_errorMartingale_zero {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), errorMartingale θ ε 0 f = 0 := by
  have _hε := hε -- interface hypothesis `hε` is kept for uniformity; unused here
  filter_upwards [ae_supAuxLocalTime_continuous hθ, ae_eval_zero_stableLocalLaw hθ] with f hf h0
  have hR : supReflectedFrom 0 f 0 = 0 := by
    simp [supReflectedFrom, supRunning_zero, h0]
  simp [errorMartingale, supOccupation_zero, hf.1, occupationCorrection_eq_zero hR]

/-- The error has right continuous paths on one event of full probability. -/
theorem ae_rightContinuous_errorMartingale {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {ε : ℝ}
    (hε : 0 < ε) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∀ t : ℝ≥0,
      ContinuousWithinAt (fun s => errorMartingale θ ε s f) (Ici t) t := by
  filter_upwards [ae_supAuxLocalTime_continuous hθ] with f hf
  intro t
  have hR : ContinuousWithinAt (supReflectedFrom 0 f) (Ici t) t :=
    continuousWithinAt_Ioi_iff_Ici.mp ((isCadlag_supReflectedFrom 0 f).isRightContinuous t)
  have hv := (continuousOn_supCorrection hθ hε _
    (supReflectedFrom_nonneg 0 f t)).comp hR
      (fun s _ => supReflectedFrom_nonneg 0 f s)
  exact (((continuous_supOccupation hε f).continuousWithinAt.sub
    hf.2.2.continuousWithinAt).add (hv.sub continuousWithinAt_const))

end BGW.StableTrees
