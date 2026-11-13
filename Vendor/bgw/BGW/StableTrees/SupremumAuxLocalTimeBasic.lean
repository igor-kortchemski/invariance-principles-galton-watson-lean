/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.SupremumCauchy
public import BGW.StableTrees.SupremumAuxLocalTimeStieltjes

/-!
# Auxiliary supremum local time and its Stieltjes measure

The clock is the raw limit `supAuxLimit`. Its Stieltjes extension is constant at negative times.
The potential identities must be established before recurrence is used.

## References

* J. Bertoin, *Lévy Processes*, Cambridge University Press, 1996, Chapter IV.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees

open scoped Classical in
/-- The auxiliary continuous local time `L^aux = M^*` (public name of `supAuxLimit`). -/
noncomputable def supAuxLocalTime (θ : ℝ) (f : DLoc) (t : ℝ≥0) : ℝ := supAuxLimit θ f t

/-- Stieltjes function of the auxiliary local time. -/
noncomputable def supAuxStieltjes (θ : ℝ) (f : DLoc) : StieltjesFunction ℝ :=
  pathStieltjes (supAuxLocalTime θ f)

/-- Discounted future clock `∫_{(s,∞)} e^{-qt} dL^aux_t`. -/
noncomputable def supAuxDiscountedTail (θ q : ℝ) (s : ℝ≥0) (f : DLoc) : ℝ :=
  ∫ t in Ioi (s : ℝ), Real.exp (-q * t) ∂(supAuxStieltjes θ f).measure

/-- Inverse `A^*_z = inf{t | L^aux_t > z}` (raw, as for `supLocalTimeStieltjes`). -/
noncomputable def supAuxInverse (θ : ℝ) (f : DLoc) (z : ℝ≥0) : WithTop ℝ≥0 :=
  sInf {t : WithTop ℝ≥0 | ∃ u : ℝ≥0, t = u ∧ (z : ℝ) < supAuxLocalTime θ f u}

/-- `A^*_z` (finite reading, junk `0` on `⊤`). -/
noncomputable def supAuxLadderTime (θ : ℝ) (z : ℝ≥0) (f : DLoc) : ℝ≥0 :=
  (supAuxInverse θ f z).untopD 0

/-- `B^*_z = S_{A^*_z}`. -/
noncomputable def supAuxLadderHeight (θ : ℝ) (z : ℝ≥0) (f : DLoc) : ℝ :=
  supRunning f (supAuxLadderTime θ z f)

/-- The auxiliary clock is jointly measurable for every index. -/
theorem measurable_supAuxLocalTime_uncurry (θ : ℝ) :
    Measurable (fun p : ℝ≥0 × DLoc => supAuxLocalTime θ p.2 p.1) :=
  measurable_supAuxLimit_uncurry θ

/-- The auxiliary clock is strongly adapted for every index. -/
theorem stronglyAdapted_supAuxLocalTime (θ : ℝ) :
    StronglyAdapted DLoc.filtration (fun t f => supAuxLocalTime θ f t) :=
  stronglyAdapted_supAuxLimit θ

/-- Before recurrence, `supAuxLimit` supplies one event of continuous monotone
zero-started paths. -/
theorem ae_supAuxLocalTime_continuous {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc),
      supAuxLocalTime θ f 0 = 0 ∧ Monotone (supAuxLocalTime θ f) ∧
        Continuous (supAuxLocalTime θ f) :=
  ae_supAuxLimit_spec hθ

/-- The auxiliary clock has integrable squared values. -/
theorem integrable_sq_supAuxLocalTime {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (T : ℝ≥0) :
    Integrable (fun f => supAuxLocalTime θ f T ^ 2) (stableLocalLaw θ : Measure DLoc) :=
  integrable_sq_supAuxLimit hθ T

end BGW.StableTrees
