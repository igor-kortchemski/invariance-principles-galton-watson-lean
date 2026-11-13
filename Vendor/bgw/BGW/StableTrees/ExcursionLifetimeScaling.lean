/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.ExcursionMeasureWindow
public import BGW.StableTrees.StableProcessLaw

/-! Scaling invariance of the local stable law and its excursion intensity.

Reference: J. Bertoin, *Lévy Processes*, Cambridge University Press, 1996, Chapters IV and VIII. -/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees

/-- Fixed space-time scaling is measurable on the local path carrier. -/
theorem measurable_scaleLoc (θ : ℝ) (c : Ioi (0 : ℝ)) : Measurable (scaleLoc θ c) := by
  rw [measurable_iff_comap_le]
  change MeasurableSpace.comap (scaleLoc θ c) (⨆ t,
    MeasurableSpace.comap (DLoc.eval t) inferInstance) ≤ _
  rw [MeasurableSpace.comap_iSup, iSup_le_iff]
  intro t
  rw [MeasurableSpace.comap_comp]
  change MeasurableSpace.comap
    (fun f : DLoc => (c : ℝ) ^ (1 / θ) * f.1 (t / (c : ℝ).toNNReal)) _ ≤ _
  exact (measurable_const.mul (DLoc.measurable_eval _)).comap_le

/-- The stable local path law is invariant under its canonical space-time scaling. -/
theorem map_scaleLoc_stableLocalLaw {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (c : Ioi (0 : ℝ)) :
    (stableLocalLaw θ : Measure DLoc).map (scaleLoc θ c) =
      (stableLocalLaw θ : Measure DLoc) := by
  have hm := measurable_scaleLoc θ c
  let Q := (stableLocalLaw θ).map (scaleLoc θ c)
  suffices Q = stableLocalLaw θ by
    exact congrArg ProbabilityMeasure.toMeasure this
  apply (eq_stableLocalLaw_iff hθ).mpr
  intro T hT
  let d : ℝ := (c : ℝ)⁻¹
  have hd : 0 < d := inv_pos.mpr c.2
  have hTR : 0 < (T : ℝ) := hT
  let H : ℝ≥0 := ⟨d * T, (mul_pos hd hTR).le⟩
  let F : D (d * T) ℝ → D (T : ℝ) ℝ := fun f =>
    timeSpaceScale (T : ℝ) (mul_pos hd hTR).le
      (f, d ^ (-(1 / θ)), (⟨d, hd⟩ : Ioi (0 : ℝ)))
  have hF : Measurable F := measurable_timeSpaceScale_fixed hTR hd _
  have hcoeff : d ^ (-(1 / θ)) = (c : ℝ) ^ (1 / θ) := by
    rw [Real.rpow_neg hd.le, Real.inv_rpow c.2.le, inv_inv]
  have hcomp : DLoc.restrict T ∘ scaleLoc θ c = F ∘ DLoc.restrict H := by
    funext f
    apply BGW.Skorokhod.ext
    intro t
    have ht : d * (t : ℝ) ≤ d * T := mul_le_mul_of_nonneg_left t.2.2 hd.le
    change (c : ℝ) ^ (1 / θ) * f.1 (_ / (c : ℝ).toNNReal) =
      d ^ (-(1 / θ)) * f.1 ⟨min (d * (t : ℝ)) (d * T), _⟩
    rw [hcoeff]
    apply congrArg (fun x : ℝ => (c : ℝ) ^ (1 / θ) * x)
    apply congrArg f.1
    apply NNReal.coe_injective
    change (t : ℝ) / ((c : ℝ).toNNReal : ℝ) = min (d * (t : ℝ)) (d * T)
    rw [Real.coe_toNNReal _ c.2.le, min_eq_left ht]
    dsimp only [d]
    ring
  change ((stableLocalLaw θ : Measure DLoc).map (scaleLoc θ c)).map
    (DLoc.restrict T) = _
  rw [Measure.map_map (DLoc.measurable_restrict T) hm, hcomp,
    ← Measure.map_map hF (DLoc.measurable_restrict H)]
  have hsource := map_restrict_stableLocalLaw hθ (show 0 < H from mul_pos hd hTR)
  refine (congrArg (Measure.map F) hsource).trans ?_
  exact congrArg ProbabilityMeasure.toMeasure
    ((eq_stableProcessLaw_iff hθ hTR).mpr
      ((isStableLevyLaw_stableProcessLaw hθ (mul_pos hd hTR)).map_timeSpaceScale hθ hTR hd))

private theorem lintegral_windowMark_raw {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    (b : ℝ≥0) {A : Set Excursion} (hA : MeasurableSet A) :
    (∫⁻ f, excursionPointMeasure f (Ioc 0 b ×ˢ A)
      ∂(stableLocalLaw θ : Measure DLoc)) = (b : ℝ≥0∞) * excursionMeasure θ A := by
  obtain ⟨ξ, hξ, hae⟩ := exists_measurable_modification_excursionPointMeasure hθ
  calc
    _ = ∫⁻ f, ξ f (Ioc 0 b ×ˢ A) ∂(stableLocalLaw θ : Measure DLoc) := by
      apply lintegral_congr_ae
      exact hae.symm.mono fun f hf => congrArg (fun μ => μ (Ioc 0 b ×ˢ A)) hf
    _ = _ := by simpa using lintegral_windowMark_eq hθ hξ hae (show 0 ≤ b from bot_le) hA

/-- **Scaling of `N`** (carrier convention `S_c`: path `c^{1/θ} e(t/c)`, lifetime `c ζ`):
`(S_c)_* N = c^{1/θ} • N` for every `c > 0`. -/
theorem map_excursionScale_excursionMeasure {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (c : Set.Ioi (0 : ℝ)) :
    (excursionMeasure θ).map (excursionScale θ c) =
      ENNReal.ofReal ((c : ℝ) ^ (1 / θ)) • excursionMeasure θ := by
  let w : ℝ≥0 := (c : ℝ).toNNReal ^ (1 / θ)
  have hw : 0 < w := by
    exact NNReal.rpow_pos (Real.toNNReal_pos.mpr c.2)
  have hm := measurable_scaleLoc θ c
  have hS := measurable_excursionScale θ c
  have hM : Measurable (fun p : ℝ≥0 × Excursion =>
      (w * p.1, excursionScale θ c p.2)) :=
    (measurable_const.mul measurable_fst).prodMk (hS.comp measurable_snd)
  apply Measure.ext
  intro A hA
  rw [Measure.map_apply hS hA, Measure.smul_apply, smul_eq_mul]
  have hbox : MeasurableSet (Ioc 0 w ×ˢ A) := measurableSet_Ioc.prod hA
  have hpre : (fun p : ℝ≥0 × Excursion => (w * p.1, excursionScale θ c p.2)) ⁻¹'
      (Ioc 0 w ×ˢ A) = Ioc 0 1 ×ˢ (excursionScale θ c ⁻¹' A) := by
    ext p
    simp only [mem_preimage, mem_prod, mem_Ioc]
    rw [mul_pos_iff_of_pos_left hw]
    have hle : w * p.1 ≤ w ↔ p.1 ≤ 1 := by
      simpa using (mul_le_mul_iff_right₀ hw : w * p.1 ≤ w * 1 ↔ p.1 ≤ 1)
    rw [hle]
  have heq : (w : ℝ≥0∞) * excursionMeasure θ A =
      excursionMeasure θ (excursionScale θ c ⁻¹' A) := by
    calc
      _ = ∫⁻ f, excursionPointMeasure f (Ioc 0 w ×ˢ A)
          ∂(stableLocalLaw θ : Measure DLoc) := (lintegral_windowMark_raw hθ w hA).symm
      _ = ∫⁻ f, excursionPointMeasure (scaleLoc θ c f) (Ioc 0 w ×ˢ A)
          ∂(stableLocalLaw θ : Measure DLoc) := by
        have hmeas : AEMeasurable
            (fun f => excursionPointMeasure f (Ioc 0 w ×ˢ A))
            ((stableLocalLaw θ : Measure DLoc).map (scaleLoc θ c)) := by
          rw [map_scaleLoc_stableLocalLaw hθ c]
          exact aemeasurable_excursionPointMeasure_apply hθ hbox
        have hi := lintegral_map' hmeas hm.aemeasurable
        rw [map_scaleLoc_stableLocalLaw hθ c] at hi
        exact hi
      _ = ∫⁻ f, excursionPointMeasure f (Ioc 0 1 ×ˢ (excursionScale θ c ⁻¹' A))
          ∂(stableLocalLaw θ : Measure DLoc) := by
        apply lintegral_congr_ae
        filter_upwards [ae_excursionPointMeasure_scaleLoc hθ c] with f hf
        rw [hf, Measure.map_apply hM hbox, hpre]
      _ = _ := (excursionMeasure_apply hθ (hS hA)).symm
  rw [← heq]
  congr 1
  rw [← ENNReal.ofReal_coe_nnreal]
  congr 1
  exact NNReal.coe_rpow _ _ |>.trans (by rw [Real.coe_toNNReal _ c.2.le])

end BGW.StableTrees
