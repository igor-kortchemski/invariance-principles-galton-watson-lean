/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.SupremumStoppedEnergyMaximal
public import BGW.StableTrees.SupremumStoppedEnergyFatou

/-!
# Removing the inverse-clock localization

Eventual equality on the whole stopped interval transfers bounded martingale estimates
by Fatou. The resulting maximal moment supplies an integrable domination for the means.

## References

* J. Bertoin, *Lévy Processes*, Cambridge University Press, 1996, Chapter IV.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees

private theorem sup_Iic_comp_min (X : ℝ≥0 → ℝ) {A T : ℝ≥0} (hAT : A ≤ T) :
    (⨆ s : Set.Iic T, X (min s A)) = ⨆ s : Set.Iic A, X s := by
  change sSup (range (fun s : Set.Iic T => X (min s A))) =
    sSup (range (fun s : Set.Iic A => X s))
  congr 1
  ext x
  constructor
  · rintro ⟨s, rfl⟩
    exact ⟨⟨min s A, min_le_right _ _⟩, rfl⟩
  · rintro ⟨s, rfl⟩
    refine ⟨⟨s, s.2.trans hAT⟩, ?_⟩
    exact congrArg X (min_eq_left s.2)

/-- Eventually the epoch is the minimum with the auxiliary inverse, at every horizon. -/
theorem ae_eventually_errStopTime_eq_min {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (z : ℝ≥0) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∀ᶠ n : ℕ in atTop,
      supAuxLadderTime θ z f ≤ (n : ℝ≥0) ∧ ∀ s : ℝ≥0,
        errStopTime n (supHitting θ z) s f = min s (supAuxLadderTime θ z f) := by
  filter_upwards [ae_supHitting_eq_supAuxLadderTime hθ z] with f he
  filter_upwards [(ENNReal.tendsto_nhds_top_iff_nnreal.mp (tendsto_errCutoff_top f))
    (supAuxLadderTime θ z f)] with n hn
  have hAn : (supAuxLadderTime θ z f : ℝ≥0∞) ≤ ((n : ℝ≥0) : ℝ≥0∞) := by
    simpa only [ENNReal.coe_natCast] using hn.le.trans (errCutoff_le n f)
  refine ⟨ENNReal.coe_le_coe.mp hAn, ?_⟩
  intro s
  unfold errStopTime
  rw [he, min_eq_left ((min_le_right _ _).trans hn.le),
    ← ENNReal.coe_min, ENNReal.toNNReal_coe]

/-- Any stopped compact supremum eventually equals its supremum up to the inverse clock.
This is equality of ranges, so it does not rely on conditional-completeness bounds. -/
theorem ae_eventually_sup_errStopTime_eq {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (z : ℝ≥0)
    (X : ℝ≥0 → DLoc → ℝ) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∀ᶠ n : ℕ in atTop,
      (⨆ s : Set.Iic (n : ℝ≥0), X (errStopTime n (supHitting θ z) s f) f) =
        ⨆ s : Set.Iic (supAuxLadderTime θ z f), X s f := by
  filter_upwards [ae_eventually_errStopTime_eq_min hθ z] with f hf
  filter_upwards [hf] with n hn
  simp_rw [hn.2]
  exact sup_Iic_comp_min (fun s => X s f) hn.1

private theorem energy_bound_nonneg {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {ε : ℝ} (hε : 0 < ε)
    (z : ℝ≥0) : 0 ≤ 4 * (z : ℝ) * supCorrectionBound θ ε +
      12 * supCorrectionBound θ ε ^ 2 := by
  have hg := Real.Gamma_pos_of_pos (by linarith [hθ.1] : 0 < θ)
  have hV : 0 ≤ supCorrectionBound θ ε := by unfold supCorrectionBound; positivity
  positivity

/-- The martingale maximum up to the finite inverse clock has a finite second moment. -/
theorem integral_sq_sup_errorMartingale_supAuxLadderTime_le {θ : ℝ}
    (hθ : 1 < θ ∧ θ ≤ 2) {ε : ℝ} (hε : 0 < ε) (z : ℝ≥0) :
    Integrable (fun f => (⨆ s : Set.Iic (supAuxLadderTime θ z f),
      |errorMartingale θ ε s f|) ^ 2) (stableLocalLaw θ : Measure DLoc) ∧
      ∫ f, (⨆ s : Set.Iic (supAuxLadderTime θ z f), |errorMartingale θ ε s f|) ^ 2
        ∂(stableLocalLaw θ : Measure DLoc) ≤
      4 * (4 * (z : ℝ) * supCorrectionBound θ ε + 12 * supCorrectionBound θ ε ^ 2) := by
  apply integrable_limit_of_nonneg_integral_le (mul_nonneg (by norm_num)
    (energy_bound_nonneg hθ hε z))
    (fun n => (integral_sq_sup_errorMartingale_stopped_le hθ hε z n n).1)
    (fun _ => ae_of_all _ (fun _ => sq_nonneg _)) ?_
    (fun n => (integral_sq_sup_errorMartingale_stopped_le hθ hε z n n).2)
  filter_upwards [ae_eventually_sup_errStopTime_eq hθ z
    (fun s f => |errorMartingale θ ε s f|)] with f hf
  apply tendsto_const_nhds.congr'
  filter_upwards [hf] with n hn
  exact (congrArg (fun x : ℝ => x ^ 2) hn).symm

/-- **Stopped energy at `A^*_z`**: `E (O_ε(A^*_z) - z)² ≤ 4 z V_ε + 12 V_ε²`. -/
theorem integral_sq_supOccupation_sub_supAuxLadderTime_le {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    {ε : ℝ} (hε : 0 < ε) (z : ℝ≥0) :
    Integrable (fun f => (supOccupation ε f (supAuxLadderTime θ z f) - (z : ℝ)) ^ 2)
        (stableLocalLaw θ : Measure DLoc) ∧
      ∫ f, (supOccupation ε f (supAuxLadderTime θ z f) - (z : ℝ)) ^ 2
          ∂(stableLocalLaw θ : Measure DLoc) ≤
        4 * (z : ℝ) * supCorrectionBound θ ε + 12 * supCorrectionBound θ ε ^ 2 := by
  apply integrable_limit_of_nonneg_integral_le (energy_bound_nonneg hθ hε z)
    (fun n => (integral_sq_errorMartingale_stopped_le hθ hε z n n).1)
    (fun _ => ae_of_all _ (fun _ => sq_nonneg _)) ?_
    (fun n => (integral_sq_errorMartingale_stopped_le hθ hε z n n).2)
  filter_upwards [ae_eventually_errStopTime_eq hθ z, ae_supAuxLadder_spec hθ,
    ae_occupationCorrection_supAuxLadderTime_eq_zero hθ] with f hf hA hw
  have he : errorMartingale θ ε (supAuxLadderTime θ z f) f =
      supOccupation ε f (supAuxLadderTime θ z f) - (z : ℝ) := by
    rw [errorMartingale, hA.2.2.2.2.2.2.1 z, hw ε z, add_zero]
  apply tendsto_const_nhds.congr'
  filter_upwards [hf] with n hn
  rw [hn.2, he]

/-- Every localized epoch lies below the finite inverse, on one event for all indices. -/
theorem ae_errStopTime_le_supAuxLadderTime {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (z : ℝ≥0) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∀ (n : ℕ) (s : ℝ≥0),
      errStopTime n (supHitting θ z) s f ≤ supAuxLadderTime θ z f := by
  filter_upwards [ae_supHitting_eq_supAuxLadderTime hθ z] with f he
  intro n s
  apply ENNReal.coe_le_coe.mp
  change ((min (min (s : ℝ≥0∞) (supHitting θ z f)) (errCutoff n f)).toNNReal : ℝ≥0∞) ≤ _
  rw [ENNReal.coe_toNNReal (ne_top_of_le_ne_top ENNReal.coe_ne_top
    ((min_le_left _ _).trans (min_le_left _ _))), he]
  exact (min_le_left _ _).trans (min_le_right _ _)

/-- The inverse-time martingale supremum is a genuine bounded real supremum almost surely. -/
theorem ae_bddAbove_errorMartingale_supAuxLadderTime {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    {ε : ℝ} (hε : 0 < ε) (z : ℝ≥0) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc),
      BddAbove (range (fun s : Set.Iic (supAuxLadderTime θ z f) =>
        |errorMartingale θ ε s f|)) := by
  filter_upwards [ae_supAuxLocalTime_spec hθ, ae_supAuxLadder_spec hθ] with f hf hA
  refine ⟨supOccupation ε f (supAuxLadderTime θ z f) + z + 2 * supCorrectionBound θ ε, ?_⟩
  rintro _ ⟨s, rfl⟩
  have hm0 : 0 ≤ supAuxLocalTime θ f s := hf.1 ▸ hf.2.1 (zero_le : 0 ≤ (s : ℝ≥0))
  have hms := hf.2.1 s.2
  rw [hA.2.2.2.2.2.2.1 z] at hms
  have hos := monotone_supOccupation hε.le f s.2
  have hOn := supOccupation_nonneg hε.le f s
  unfold errorMartingale
  calc
    _ ≤ |supOccupation ε f s - supAuxLocalTime θ f s| +
        |occupationCorrection θ ε s f| := abs_add_le _ _
    _ ≤ |supOccupation ε f s| + |supAuxLocalTime θ f s| +
        2 * supCorrectionBound θ ε :=
      add_le_add (abs_sub _ _) (abs_occupationCorrection_le hθ hε _ f)
    _ ≤ _ := by
      rw [abs_of_nonneg hOn, abs_of_nonneg hm0]
      linarith only [hms, hos]

/-- **Exact mean**: `E O_ε(A^*_z) = z` (uniform integrability from the `L²` bound; `A^*_z < ∞`
and `R_{A^*_z} = 0`), with integrability. -/
theorem integral_supOccupation_supAuxLadderTime {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {ε : ℝ}
    (hε : 0 < ε) (z : ℝ≥0) :
    Integrable (fun f => supOccupation ε f (supAuxLadderTime θ z f))
        (stableLocalLaw θ : Measure DLoc) ∧
      ∫ f, supOccupation ε f (supAuxLadderTime θ z f) ∂(stableLocalLaw θ : Measure DLoc) =
        (z : ℝ) := by
  let P : Measure DLoc := stableLocalLaw θ
  let D : ℕ → DLoc → ℝ := fun n f =>
    errorMartingale θ ε (errStopTime n (supHitting θ z) n f) f
  let DA : DLoc → ℝ := fun f => errorMartingale θ ε (supAuxLadderTime θ z f) f
  let H : DLoc → ℝ := fun f => ⨆ s : Set.Iic (supAuxLadderTime θ z f),
    |errorMartingale θ ε s f|
  have hHi : Integrable (fun f => 1 + H f ^ 2) P :=
    (integrable_const (1 : ℝ)).add
      (integral_sq_sup_errorMartingale_supAuxLadderTime_le hθ hε z).1
  have hDi (n : ℕ) : Integrable (D n) P :=
    (martingale_errorMartingale_stopped hθ hε n (isStoppingTime_supHitting θ z)).integrable n
  have hlim : ∀ᵐ f ∂P, Tendsto (fun n => D n f) atTop (𝓝 (DA f)) := by
    filter_upwards [ae_eventually_errStopTime_eq hθ z] with f hf
    apply tendsto_const_nhds.congr'
    filter_upwards [hf] with n hn
    dsimp only [D, DA]
    rw [hn.2]
  have hdom (n : ℕ) : ∀ᵐ f ∂P, ‖D n f‖ ≤ 1 + H f ^ 2 := by
    filter_upwards [ae_bddAbove_errorMartingale_supAuxLadderTime hθ hε z,
      ae_errStopTime_le_supAuxLadderTime hθ z] with f hf ht
    have hb := le_ciSup hf (⟨errStopTime n (supHitting θ z) n f, ht n n⟩ :
      Set.Iic (supAuxLadderTime θ z f))
    change |D n f| ≤ H f at hb
    rw [Real.norm_eq_abs]
    nlinarith [sq_nonneg (H f - 1 / 2)]
  have hDAm := aestronglyMeasurable_of_tendsto_ae atTop
    (fun n => (hDi n).aestronglyMeasurable) hlim
  have hDAb : ∀ᵐ f ∂P, ‖DA f‖ ≤ 1 + H f ^ 2 := by
    filter_upwards [ae_bddAbove_errorMartingale_supAuxLadderTime hθ hε z] with f hf
    have hb := le_ciSup hf (⟨supAuxLadderTime θ z f, le_rfl⟩ :
      Set.Iic (supAuxLadderTime θ z f))
    change |DA f| ≤ H f at hb
    rw [Real.norm_eq_abs]
    nlinarith [sq_nonneg (H f - 1 / 2)]
  have hDAi : Integrable DA P := hHi.mono' hDAm hDAb
  have hconv := tendsto_integral_of_dominated_convergence (fun f => 1 + H f ^ 2)
    (fun n => (hDi n).aestronglyMeasurable) hHi hdom hlim
  have hzero : (fun n => ∫ f, D n f ∂P) = fun _ : ℕ => (0 : ℝ) := by
    funext n
    exact integral_errorMartingale_stopped hθ hε n (isStoppingTime_supHitting θ z) n
  rw [hzero] at hconv
  have hmean : ∫ f, DA f ∂P = 0 := tendsto_nhds_unique hconv tendsto_const_nhds
  have he : (fun f => DA f + (z : ℝ)) =ᵐ[P]
      (fun f => supOccupation ε f (supAuxLadderTime θ z f)) := by
    filter_upwards [ae_supAuxLadder_spec hθ,
      ae_occupationCorrection_supAuxLadderTime_eq_zero hθ] with f hf hw
    dsimp only [DA]
    rw [errorMartingale, hf.2.2.2.2.2.2.1 z, hw ε z]
    ring
  refine ⟨(hDAi.add (integrable_const (z : ℝ))).congr he, ?_⟩
  rw [← integral_congr_ae he, integral_add hDAi (integrable_const (z : ℝ)), hmean]
  simp only [integral_const, probReal_univ, one_smul, zero_add]

end BGW.StableTrees
