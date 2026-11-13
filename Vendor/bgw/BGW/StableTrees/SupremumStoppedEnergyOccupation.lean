/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.SupremumStoppedEnergyLimit

/-!
# Stopped maximal occupation error

The centered correction transfers Doob's estimate from the martingale to the occupation
error. Eventual equality of the stopped suprema removes localization by Fatou.

## References

* J. Bertoin, *Lévy Processes*, Cambridge University Press, 1996, Chapter IV.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees

/-- Almost sure right continuity makes the real compact absolute supremum measurable
up to a null set, even for representatives with exceptional paths. -/
theorem aestronglyMeasurable_sup_Iic_abs_of_ae_rightContinuous {Ω : Type*}
    [MeasurableSpace Ω] {μ : Measure Ω} {X : ℝ≥0 → Ω → ℝ}
    (hX : ∀ s, Measurable (X s))
    (hr : ∀ᵐ ω ∂μ, ∀ s, ContinuousWithinAt (fun u => X u ω) (Ici s) s) (T : ℝ≥0) :
    AEStronglyMeasurable (fun ω => ⨆ s : Set.Iic T, |X s ω|) μ := by
  have hm := aemeasurable_sup_Icc_enorm_of_ae_rightContinuous hX hr T
  have he (ω : Ω) : (⨆ s : Set.Iic T, |X s ω|) =
      (⨆ s ∈ Icc (0 : ℝ≥0) T, ‖X s ω‖ₑ).toReal := by
    have hs : (⨆ s ∈ Icc (0 : ℝ≥0) T, ‖X s ω‖ₑ) =
        ⨆ s : Set.Iic T, ‖X s ω‖ₑ := by
      simp only [mem_Icc, zero_le, true_and, iSup_subtype, mem_Iic]
    rw [hs, ENNReal.toReal_iSup (fun _ => enorm_ne_top)]
    simp only [toReal_enorm, Real.norm_eq_abs]
  exact hm.ennreal_toReal.aestronglyMeasurable.congr (ae_of_all _ (fun ω => (he ω).symm))

private theorem finite_maximal_occupation {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {ε : ℝ}
    (hε : 0 < ε) (z : ℝ≥0) (n : ℕ) (T : ℝ≥0) :
    Integrable (fun f => (⨆ s : Set.Iic T,
      |supOccupation ε f (errStopTime n (supHitting θ z) s f) -
        supAuxLocalTime θ f (errStopTime n (supHitting θ z) s f)|) ^ 2)
      (stableLocalLaw θ : Measure DLoc) ∧
    ∫ f, (⨆ s : Set.Iic T,
      |supOccupation ε f (errStopTime n (supHitting θ z) s f) -
        supAuxLocalTime θ f (errStopTime n (supHitting θ z) s f)|) ^ 2
      ∂(stableLocalLaw θ : Measure DLoc) ≤
      104 * ((z : ℝ) * supCorrectionBound θ ε + supCorrectionBound θ ε ^ 2) := by
  let P : Measure DLoc := stableLocalLaw θ
  let X : ℝ≥0 → DLoc → ℝ := fun s f =>
    supOccupation ε f (errStopTime n (supHitting θ z) s f) -
      supAuxLocalTime θ f (errStopTime n (supHitting θ z) s f)
  let Y : DLoc → ℝ := fun f => ⨆ s : Set.Iic T,
    |errorMartingale θ ε (errStopTime n (supHitting θ z) s f) f|
  let A : DLoc → ℝ := fun f => ⨆ s : Set.Iic T, |X s f|
  have hXm (s : ℝ≥0) : Measurable (X s) :=
    (((stronglyMeasurable_errStopTime_eval (isStronglyProgressive_supOccupation hε) n
      (isStoppingTime_supHitting θ z) s).sub
      (stronglyMeasurable_errStopTime_eval (isStronglyProgressive_supAuxLocalTime hθ) n
        (isStoppingTime_supHitting θ z) s)).mono (DLoc.filtration.le s)).measurable
  have hXc : ∀ᵐ f ∂P, ∀ s, ContinuousWithinAt (fun u => X u f) (Ici s) s := by
    filter_upwards [ae_supAuxLocalTime_spec hθ] with f hf
    have he := continuous_errStopTime n (supHitting θ z) f
    exact fun _ => (((continuous_supOccupation hε f).comp he).sub
      (hf.2.2.1.comp he)).continuousWithinAt
  have hAm : AEStronglyMeasurable A P :=
    aestronglyMeasurable_sup_Iic_abs_of_ae_rightContinuous hXm hXc T
  have hY := integral_sq_sup_errorMartingale_stopped_le hθ hε z n T
  have hdom : ∀ᵐ f ∂P, A f ^ 2 ≤ 2 * Y f ^ 2 + 8 * supCorrectionBound θ ε ^ 2 := by
    filter_upwards [ae_bddAbove_errorMartingale_supAuxLadderTime hθ hε z,
      ae_errStopTime_le_supAuxLadderTime hθ z] with f hf ht
    have hYbdd : BddAbove (range (fun s : Set.Iic T =>
        |errorMartingale θ ε (errStopTime n (supHitting θ z) s f) f|)) := by
      obtain ⟨K, hK⟩ := hf
      refine ⟨K, ?_⟩
      rintro _ ⟨s, rfl⟩
      exact hK ⟨⟨errStopTime n (supHitting θ z) s f, ht n s⟩, rfl⟩
    have hb (s : Set.Iic T) : |X s f| ≤ Y f + 2 * supCorrectionBound θ ε := by
      have he : X s f = errorMartingale θ ε (errStopTime n (supHitting θ z) s f) f -
          occupationCorrection θ ε (errStopTime n (supHitting θ z) s f) f := by
        dsimp only [X, errorMartingale]
        ring
      rw [he]
      exact (abs_sub _ _).trans (add_le_add (le_ciSup hYbdd s)
        (abs_occupationCorrection_le hθ hε _ f))
    have hAbdd : BddAbove (range (fun s : Set.Iic T => |X s f|)) :=
      ⟨_, by rintro _ ⟨s, rfl⟩; exact hb s⟩
    have ha : 0 ≤ A f := (abs_nonneg _).trans
      (le_ciSup hAbdd (⟨0, (zero_le : (0 : ℝ≥0) ≤ T)⟩ : Set.Iic T))
    have hh : A f ≤ Y f + 2 * supCorrectionBound θ ε := ciSup_le hb
    have hs := pow_le_pow_left₀ ha hh 2
    nlinarith [sq_nonneg (Y f - 2 * supCorrectionBound θ ε)]
  have hdomi : Integrable (fun f => 2 * Y f ^ 2 + 8 * supCorrectionBound θ ε ^ 2) P :=
    (hY.1.const_mul 2).add (integrable_const _)
  have hAi : Integrable (fun f => A f ^ 2) P := hdomi.mono' (hAm.pow 2)
    (hdom.mono fun f hf => by rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact hf)
  refine ⟨hAi, ?_⟩
  have hi := integral_mono_ae hAi hdomi hdom
  rw [integral_add (hY.1.const_mul 2) (integrable_const _), integral_const_mul,
    integral_const] at hi
  simp only [probReal_univ, one_smul] at hi
  have hg := Real.Gamma_pos_of_pos (by linarith [hθ.1] : 0 < θ)
  have hV : 0 ≤ supCorrectionBound θ ε := by unfold supCorrectionBound; positivity
  have hzV := mul_nonneg z.coe_nonneg hV
  nlinarith [hY.2]

/-- **Stopped maximal estimate**:
`E sup_{t ≤ A^*_z}|O_ε(t) - M^*_t|² ≤ 104 (z V_ε + V_ε²)` (`O - M^* = D - w`, `|w| ≤ 2V`). -/
theorem integral_sq_sup_supOccupation_sub_supAuxLocalTime_le {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    {ε : ℝ} (hε : 0 < ε) (z : ℝ≥0) :
    Integrable (fun f => (⨆ t : Set.Iic (supAuxLadderTime θ z f),
          |supOccupation ε f t - supAuxLocalTime θ f t|) ^ 2)
        (stableLocalLaw θ : Measure DLoc) ∧
      ∫ f, (⨆ t : Set.Iic (supAuxLadderTime θ z f),
            |supOccupation ε f t - supAuxLocalTime θ f t|) ^ 2
          ∂(stableLocalLaw θ : Measure DLoc) ≤
        104 * ((z : ℝ) * supCorrectionBound θ ε + supCorrectionBound θ ε ^ 2) := by
  have hg := Real.Gamma_pos_of_pos (by linarith [hθ.1] : 0 < θ)
  have hV : 0 ≤ supCorrectionBound θ ε := by unfold supCorrectionBound; positivity
  apply integrable_limit_of_nonneg_integral_le (by positivity)
    (fun n => (finite_maximal_occupation hθ hε z n n).1)
    (fun _ => ae_of_all _ (fun _ => sq_nonneg _)) ?_
    (fun n => (finite_maximal_occupation hθ hε z n n).2)
  filter_upwards [ae_eventually_sup_errStopTime_eq hθ z
    (fun s f => |supOccupation ε f s - supAuxLocalTime θ f s|)] with f hf
  apply tendsto_const_nhds.congr'
  filter_upwards [hf] with n hn
  exact (congrArg (fun x : ℝ => x ^ 2) hn).symm

end BGW.StableTrees
