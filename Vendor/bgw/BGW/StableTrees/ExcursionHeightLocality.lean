/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.ExcursionHeightEndpoints
import BGW.StableTrees.MarkedExcursionsSupport

/-!
# Excursion locality and existence of the continuous version

The continuous host height stopped at the excursion endpoint is a version of each mark.
Translation preserves the host's exceptional time set, and exact cancellation identifies the
interior raw heights. Uniqueness proves locality and the non-junk assertion together.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal Classical
open BGW.Skorokhod

namespace BGW.StableTrees

/-- **Locality and non-junk on one event**: almost surely, for every passage jump level `x`, the
attached excursion has an a.e.-age height version, and its height is the continuous host height
`t ↦ heightLoc θ f (T(x-) + t)` on `[0, T(x) - T(x-)]`, zero after. -/
theorem ae_jumpExcursion_heightVersion {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∀ x ∈ passageJumpSet f,
      (∃ g : C(ℝ≥0, ℝ), IsExcursionHeightVersion θ (jumpExcursion x f) g) ∧
        ∀ t : ℝ≥0, excursionHeight θ (jumpExcursion x f) t =
          if t ≤ passageTime x f - passageTimeMinus x f then
            heightLoc θ f (passageTimeMinus x f + t) else 0 := by
  filter_upwards [ae_heightLoc_eq_heightUniv_ae hθ,
    ae_tendsto_heightApprox_passageTimeMinus hθ, ae_heightLoc_passageEndpoints hθ,
    ae_jumpExcursion_spec hθ] with f hf hpre hend hspec
  intro x hx
  let g := passageTimeMinus x f
  let d := passageTime x f
  let e := jumpExcursion x f
  have hcut : cutValid g d f := (hspec x hx).1
  have hlife : e.lifetime = d - g := (hspec x hx).2.1
  have hz : heightLoc θ f g = 0 ∧ heightLoc θ f d = 0 := hend x hx
  let G : C(ℝ≥0, ℝ) := ⟨fun u => heightLoc θ f (min (g + u) d),
    (continuous_heightLoc θ f).comp ((continuous_const.add continuous_id).min continuous_const)⟩
  have hG : IsExcursionHeightVersion θ e G := by
    refine ⟨?_, ?_, ?_⟩
    · change heightLoc θ f (min (g + 0) d) = 0
      rw [add_zero, min_eq_left hcut.1.le]
      exact hz.1
    · intro u hu
      rw [hlife] at hu
      have hdu : d ≤ g + u := by
        calc
          d = g + (d - g) := (add_tsub_cancel_of_le hcut.1.le).symm
          _ ≤ g + u := add_le_add le_rfl hu
      change heightLoc θ f (min (g + u) d) = 0
      rw [min_eq_right hdu]
      exact hz.2
    · have hh := ae_restrict_of_ae_restrict_of_subset
        (Ioo_subset_Ioi_self : Ioo (0 : ℝ) (e.lifetime : ℝ) ⊆ Ioi 0)
        (ae_positive_translate hf g)
      filter_upwards [hh, ae_restrict_mem measurableSet_Ioo] with s hs hmem
      have hsum : ((g : ℝ) + s).toNNReal = g + s.toNNReal := by
        simpa only [Real.toNNReal_coe] using
          Real.toNNReal_add (show (0 : ℝ) ≤ g from g.2) (show 0 ≤ s from hmem.1.le)
      rw [hsum] at hs
      have hu : s.toNNReal ≤ d - g := by
        rw [← hlife]
        exact Real.toNNReal_le_iff_le_coe.mpr hmem.2.le
      have hgu : g + s.toNNReal ≤ d := by
        calc
          _ ≤ g + (d - g) := add_le_add le_rfl hu
          _ = d := add_tsub_cancel_of_le hcut.1.le
      change heightLoc θ f (min (g + s.toNNReal) d) = heightUniv θ e.path s.toNNReal
      rw [min_eq_left hgu]
      exact hs.trans (heightUniv_jumpExcursion_eq θ x f hcut (hpre x hx) hu).symm
  have heq : excursionHeight θ e = G :=
    excursionHeight_eq_of_isExcursionHeightVersion θ e G hG
  refine ⟨⟨G, hG⟩, ?_⟩
  intro t
  change excursionHeight θ e t = if t ≤ d - g then heightLoc θ f (g + t) else 0
  rw [heq]
  by_cases ht : t ≤ d - g
  · rw [ite_eq_left ht]
    have hgt : g + t ≤ d := by
      calc
        _ ≤ g + (d - g) := add_le_add le_rfl ht
        _ = d := add_tsub_cancel_of_le hcut.1.le
    exact congrArg (heightLoc θ f) (min_eq_left hgt)
  · rw [ite_eq_right ht]
    have hdt : d ≤ g + t := by
      calc
        d = g + (d - g) := (add_tsub_cancel_of_le hcut.1.le).symm
        _ ≤ g + t := add_le_add le_rfl (not_le.mp ht).le
    change heightLoc θ f (min (g + t) d) = 0
    rw [min_eq_right hdt]
    exact hz.2

/-- **Simultaneous excursion locality**: almost surely, for every passage jump level `x` and
every `0 ≤ t ≤ T(x) - T(x-)`, the continuous height of the stable process at `T(x-) + t` is the
height of the excursion attached to `x` at time `t`. -/
theorem ae_heightLoc_jumpExcursion {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∀ x ∈ passageJumpSet f, ∀ t : ℝ≥0,
      t ≤ passageTime x f - passageTimeMinus x f →
        heightLoc θ f (passageTimeMinus x f + t) = excursionHeight θ (jumpExcursion x f) t := by
  filter_upwards [ae_jumpExcursion_heightVersion hθ] with f hf
  intro x hx t ht
  exact ((hf x hx).2 t |>.trans (ite_eq_left ht)).symm

end BGW.StableTrees
