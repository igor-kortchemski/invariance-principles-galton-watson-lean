/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.SupremumLocalTimeIdentUniform
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-!
# Public clock path properties and normalization

Identification transfers the auxiliary clock's continuity, recurrence and Stieltjes support.
The full positive-cutoff normalization follows from convergence in mean.

Reference: J. Bertoin, *Lévy Processes*, Cambridge University Press, 1996, Chapter IV.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees

/-- Full-filter convergence in probability to the public clock. -/
theorem supOccupation_tendstoInMeasure {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (t : ℝ≥0) :
    TendstoInMeasure (stableLocalLaw θ : Measure DLoc)
      (fun (ε : ℝ) (f : DLoc) => supOccupation ε f t) (𝓝[>] (0 : ℝ))
      (fun f => supLocalTime θ f t) := by
  let μ := (stableLocalLaw θ : Measure DLoc)
  have haux : TendstoInMeasure μ (fun (ε : ℝ) (f : DLoc) => supOccupation ε f t)
      (𝓝[>] (0 : ℝ)) (fun f => supAuxLocalTime θ f t) := by
    apply tendstoInMeasure_iff_measureReal_dist.mpr
    intro δ hδ
    have hz := (tendsto_integral_abs_supOccupation_sub hθ t).div_const δ
    apply squeeze_zero' (Eventually.of_forall fun _ => measureReal_nonneg) _
      (by simpa using hz)
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hi := ((integrable_supOccupation θ hε t).sub
      (integrable_supAuxLocalTime hθ t)).abs
    have hb := mul_meas_ge_le_integral_of_nonneg (ae_of_all μ (fun f =>
      abs_nonneg (supOccupation ε f t - supAuxLocalTime θ f t))) hi δ
    simpa only [Real.dist_eq] using (le_div_iff₀ hδ).mpr (by simpa only [mul_comm] using hb)
  apply haux.congr_right
  filter_upwards [ae_supLocalTime_eq_aux hθ] with f hf
  exact (hf t).symm

/-- The public local time starts at zero, is monotone and continuous, and tends to infinity. -/
theorem ae_supLocalTime_spec {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc),
      supLocalTime θ f 0 = 0 ∧ Monotone (supLocalTime θ f) ∧ Continuous (supLocalTime θ f) ∧
        Tendsto (supLocalTime θ f) atTop atTop := by
  filter_upwards [ae_supLocalTime_eq_aux hθ, ae_supAuxLocalTime_spec hθ] with f he hf
  simpa only [funext he] using hf

/-- Immediate positivity of the public local time. -/
theorem ae_supLocalTime_pos {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∀ t : ℝ≥0, 0 < t → 0 < supLocalTime θ f t := by
  filter_upwards [ae_supLocalTime_eq_aux hθ, ae_supAuxLocalTime_pos hθ] with f he hf
  simpa only [funext he] using hf

open scoped Classical in
/-- The Stieltjes function `s ↦ M_{s⁺}` on `ℝ`; junk zero where `M` is not monotone and
continuous (a null set). -/
noncomputable def supLocalTimeStieltjes (θ : ℝ) (f : DLoc) : StieltjesFunction ℝ :=
  if h : Monotone (supLocalTime θ f) ∧ Continuous (supLocalTime θ f) then
    { toFun := fun s => supLocalTime θ f s.toNNReal
      mono' := h.1.comp (fun _ _ hab => Real.toNNReal_mono hab)
      right_continuous' := fun _ =>
        ((h.2.comp continuous_real_toNNReal).continuousAt).continuousWithinAt }
  else
    { toFun := fun _ => 0
      mono' := monotone_const
      right_continuous' := fun _ => continuousWithinAt_const }

/-- On the identification event, the public and auxiliary Stieltjes functions agree. -/
theorem supLocalTimeStieltjes_eq_aux {θ : ℝ} {f : DLoc}
    (he : ∀ t, supLocalTime θ f t = supAuxLocalTime θ f t) :
    supLocalTimeStieltjes θ f = supAuxStieltjes θ f := by
  change pathStieltjes (supLocalTime θ f) = pathStieltjes (supAuxLocalTime θ f)
  rw [funext he]

/-- The public Stieltjes measure is supported on the supremum contact set. -/
theorem ae_supLocalTimeStieltjes_support {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc),
      (supLocalTimeStieltjes θ f).measure
        {s : ℝ | 0 ≤ s ∧ supRunning f s.toNNReal ≠ f.1 s.toNNReal} = 0 := by
  filter_upwards [ae_supLocalTime_eq_aux hθ, ae_supAuxStieltjes_support hθ] with f he hf
  rw [supLocalTimeStieltjes_eq_aux he]
  simpa only [mem_supContact_iff, ne_comm] using hf

/-- The public clock is constant on intervals away from contact, including left limits. -/
theorem ae_supLocalTime_const_of_lt {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∀ s t : ℝ≥0, s < t →
      (∀ u ∈ Icc s t, f.1 u < supRunning f u ∧ Function.leftLim f.1 u < supRunning f u) →
        supLocalTime θ f t = supLocalTime θ f s := by
  filter_upwards [ae_supLocalTime_eq_aux hθ, ae_supAuxLocalTime_const_of_lt hθ]
    with f he hf
  simpa only [funext he] using hf

end BGW.StableTrees
