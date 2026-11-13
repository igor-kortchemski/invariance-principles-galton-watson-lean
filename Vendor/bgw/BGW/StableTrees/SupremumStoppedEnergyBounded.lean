/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.SupremumCorrection
public import BGW.StableTrees.SupremumLocalTimeIdent
public import BGW.StableTrees.SupremumStoppedEnergyMesh

/-!
# Bounded stopped energy at the auxiliary inverse clock

The strict hitting representative agrees almost surely with the finite auxiliary ladder
time. On the same event the stopped clock is bounded by its level, and the localization
eventually disappears on the whole interval up to the ladder time.

The stopped mean bound uses the centered error martingale of
`BGW.StableTrees.SupremumCorrection`. The imported mesh lemmas and dominated convergence
give the bounded-epoch energy estimate with constants 4 and 12. Nonnegativity of the
centered correction allows the clock-increment term to be discarded in the grid inequality.

## References

* J. Bertoin, *Lévy Processes*, Cambridge University Press, 1996, Chapter IV.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees

private theorem monotone_stableScale {θ : ℝ} (hθ : 1 < θ) : Monotone (stableScale θ) := by
  intro x y hxy
  have hg := (Real.Gamma_pos_of_pos (by linarith : 0 < θ)).le
  by_cases hx : 0 ≤ x
  · simp only [stableScale, ite_eq_left hx, ite_eq_left (hx.trans hxy)]
    exact div_le_div_of_nonneg_right (Real.rpow_le_rpow hx hxy (by linarith)) hg
  · rw [stableScale, ite_eq_right hx]
    by_cases hy : 0 ≤ y
    · simp only [stableScale, ite_eq_left hy]
      exact div_nonneg (Real.rpow_nonneg hy _) hg
    · simp [stableScale, hy]

/-- The centered correction is nonnegative on every reflected state. The index-two
constant cancels upon centering, just as it does for the other indices. -/
theorem occupationCorrection_nonneg {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {ε : ℝ} (hε : 0 < ε)
    (t : ℝ≥0) (f : DLoc) : 0 ≤ occupationCorrection θ ε t f := by
  let y := supReflectedFrom 0 f t
  have hzero : (∫ r in Ioc (0 : ℝ) ε, stableScale θ (0 - r)) = 0 := by
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro r hr
    exact stableScale_eq_zero hθ.1 (by linarith [hr.1])
  have hi : IntegrableOn (fun r => stableScale θ (y - r)) (Ioc 0 ε) :=
    ((continuous_stableScale hθ.1).comp (continuous_const.sub continuous_id)).continuousOn
      |>.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hb : (∫ r in Ioc (0 : ℝ) ε, stableScale θ (y - r)) ≤ ε * stableScale θ y := by
    have hh := setIntegral_mono_on hi (integrableOn_const (by simp)) measurableSet_Ioc
      (fun r hr => monotone_stableScale hθ.1 (sub_le_self y hr.1.le))
    simpa only [setIntegral_const, Measure.real, Real.volume_Ioc, sub_zero,
      ENNReal.toReal_ofReal hε.le, smul_eq_mul] using hh
  have hb' := mul_le_mul_of_nonneg_left hb (inv_pos.mpr hε).le
  rw [← mul_assoc, inv_mul_cancel₀ hε.ne', one_mul] at hb'
  dsimp [occupationCorrection, supCorrection]
  rw [stableScale_eq_zero hθ.1 le_rfl, hzero, mul_zero]
  dsimp [y] at hb'
  linarith only [hb']

/-- The stopping representative of `A^*_z` is `A^*_z`, almost surely, and is finite
(`ae_supLadder_geometry` and `ae_supLadder_eq_aux`). -/
theorem ae_supHitting_eq_supAuxLadderTime {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (z : ℝ≥0) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc),
      supHitting θ z f = (supAuxLadderTime θ z f : ℝ≥0∞) := by
  filter_upwards [ae_supLadder_geometry hθ, ae_supLadder_eq_aux hθ] with f hg he
  rw [hg.2.1 z, (he z).1]

private theorem coe_errStopTime (n : ℕ) (σ : DLoc → ℝ≥0∞) (t : ℝ≥0) (f : DLoc) :
    (errStopTime n σ t f : ℝ≥0∞) = min (min (t : ℝ≥0∞) (σ f)) (errCutoff n f) := by
  unfold errStopTime
  exact ENNReal.coe_toNNReal (ne_top_of_le_ne_top ENNReal.coe_ne_top
    ((min_le_left _ _).trans (min_le_left _ _)))

/-- Up to the stopping epoch `τ = σ ∧ t ∧ cutoff_n`, `M^* ≤ z` (monotone, `M^*(A^*_z) = z`),
simultaneously in `n`, `t`. -/
theorem ae_supAuxLocalTime_errStopTime_le {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (z : ℝ≥0) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∀ (n : ℕ) (t : ℝ≥0),
      supAuxLocalTime θ f (errStopTime n (supHitting θ z) t f) ≤ (z : ℝ) := by
  filter_upwards [ae_supHitting_eq_supAuxLadderTime hθ z, ae_supAuxLocalTime_spec hθ,
    ae_supAuxLadder_spec hθ] with f he hm hA
  intro n t
  have ht : errStopTime n (supHitting θ z) t f ≤ supAuxLadderTime θ z f := by
    apply ENNReal.coe_le_coe.mp
    rw [coe_errStopTime, ← he]
    exact (min_le_left _ _).trans (min_le_right _ _)
  exact (hm.2.1 ht).trans_eq (hA.2.2.2.2.2.2.1 z)

/-- The localization is removed for large parameters: almost surely, eventually in `n`,
`errStopTime n (supHitting θ z) s f = s` for every `s ≤ A^*_z`, and at `s = n` it equals
`A^*_z`. -/
theorem ae_eventually_errStopTime_eq {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (z : ℝ≥0) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∀ᶠ n : ℕ in atTop,
      (∀ s : ℝ≥0, s ≤ supAuxLadderTime θ z f →
        errStopTime n (supHitting θ z) s f = s) ∧
      errStopTime n (supHitting θ z) n f = supAuxLadderTime θ z f := by
  filter_upwards [ae_supHitting_eq_supAuxLadderTime hθ z] with f he
  have hcut := (ENNReal.tendsto_nhds_top_iff_nnreal.mp (tendsto_errCutoff_top f))
    (supAuxLadderTime θ z f)
  filter_upwards [hcut] with n hn
  have hAn : (supAuxLadderTime θ z f : ℝ≥0∞) ≤ n := hn.le.trans (errCutoff_le n f)
  constructor
  · intro s hs
    apply ENNReal.coe_injective
    rw [coe_errStopTime, he, min_eq_left (ENNReal.coe_le_coe.mpr hs),
      min_eq_left ((ENNReal.coe_le_coe.mpr hs).trans hn.le)]
  · apply ENNReal.coe_injective
    have hAn' : (supAuxLadderTime θ z f : ℝ≥0∞) ≤ ((n : ℝ≥0) : ℝ≥0∞) := by
      simpa only [ENNReal.coe_natCast] using hAn
    rw [coe_errStopTime, he, min_eq_right hAn', min_eq_left hn.le]

private theorem integrable_stopped_occupation {θ : ℝ} {ε : ℝ} (hε : 0 < ε)
    (z : ℝ≥0) (n : ℕ) (t : ℝ≥0) :
    Integrable (fun f => supOccupation ε f (errStopTime n (supHitting θ z) t f))
      (stableLocalLaw θ : Measure DLoc) := by
  have hm := ((stronglyMeasurable_errStopTime_eval
    (isStronglyProgressive_supOccupation hε) n (isStoppingTime_supHitting θ z) t).mono
      (DLoc.filtration.le t)).aestronglyMeasurable
      (μ := (stableLocalLaw θ : Measure DLoc))
  apply Integrable.of_bound hm ((t : ℝ) / ε)
  filter_upwards with f
  rw [Real.norm_eq_abs, abs_of_nonneg (supOccupation_nonneg hε.le f _)]
  have hb := (supOccupation_sub_mem hε f
    (show (0 : ℝ≥0) ≤ errStopTime n (supHitting θ z) t f from zero_le)).2
  simp only [supOccupation_zero, NNReal.coe_zero, sub_zero] at hb
  exact hb.trans (by
    rw [div_eq_mul_inv, mul_comm]
    exact mul_le_mul_of_nonneg_right
      (NNReal.coe_le_coe.mpr (errStopTime_le n (supHitting θ z) t f))
      (inv_pos.mpr hε).le)

/-- **Mean occupation at the stopped epoch** (`E[O_ε(τ)] ≤ z + 2 V_ε`), with
integrability (`0 ≤ O_ε(τ) ≤ τ/ε ≤ n/ε`). -/
theorem integral_supOccupation_errStopTime_le {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {ε : ℝ} (hε : 0 < ε)
    (z : ℝ≥0) (n : ℕ) (t : ℝ≥0) :
    Integrable (fun f => supOccupation ε f (errStopTime n (supHitting θ z) t f))
        (stableLocalLaw θ : Measure DLoc) ∧
      ∫ f, supOccupation ε f (errStopTime n (supHitting θ z) t f)
        ∂(stableLocalLaw θ : Measure DLoc) ≤ (z : ℝ) + 2 * supCorrectionBound θ ε := by
  refine ⟨integrable_stopped_occupation hε z n t, ?_⟩
  have hmean := (integral_supOccupation_stopped_le hθ hε n
    (isStoppingTime_supHitting θ z) t).2
  have hm := ((stronglyMeasurable_errStopTime_eval
    (isStronglyProgressive_supAuxLocalTime hθ) n (isStoppingTime_supHitting θ z) t).mono
      (DLoc.filtration.le t)).aestronglyMeasurable
      (μ := (stableLocalLaw θ : Measure DLoc))
  have hi : Integrable (fun f => supAuxLocalTime θ f
      (errStopTime n (supHitting θ z) t f)) (stableLocalLaw θ : Measure DLoc) := by
    apply Integrable.of_bound hm (z : ℝ)
    filter_upwards [ae_supAuxLocalTime_spec hθ,
      ae_supAuxLocalTime_errStopTime_le hθ z] with f hf hb
    rw [Real.norm_eq_abs, abs_of_nonneg (hf.1 ▸ hf.2.1 (zero_le : 0 ≤
      errStopTime n (supHitting θ z) t f))]
    exact hb n t
  have hb := integral_mono_ae hi (integrable_const (z : ℝ))
    ((ae_supAuxLocalTime_errStopTime_le hθ z).mono fun _ hf => hf n t)
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at hb
  linarith only [hmean, hb]

/-- The centered correction vanishes almost everywhere for the auxiliary Stieltjes measure
on every bounded positive interval, simultaneously for all widths. -/
theorem ae_occupationCorrection_zero_dSupAux {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∀ (ε : ℝ) (T : ℝ≥0),
      (fun s : ℝ => occupationCorrection θ ε s.toNNReal f) =ᵐ[
        (supAuxStieltjes θ f).measure.restrict (Ioc (0 : ℝ) T)] 0 := by
  filter_upwards [ae_supAuxStieltjes_support hθ, ae_eval_zero_stableLocalLaw hθ]
    with f hs h0
  intro ε T
  apply (ae_restrict_iff' measurableSet_Ioc).mpr
  have hc : ∀ᵐ s ∂(supAuxStieltjes θ f).measure,
      ¬(0 ≤ s ∧ s.toNNReal ∉ supContact f) := by
    simpa only [ae_iff, not_not] using hs
  filter_upwards [hc] with s hc hsT
  apply occupationCorrection_eq_zero
  rw [supReflectedFrom_zero_apply h0]
  have hm : s.toNNReal ∈ supContact f := by
    by_contra hn
    exact hc ⟨hsT.1.le, hn⟩
  exact hm

/-- At the finite auxiliary ladder time the centered correction vanishes, for all widths
and levels on one event of full probability. -/
theorem ae_occupationCorrection_supAuxLadderTime_eq_zero {θ : ℝ}
    (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∀ (ε : ℝ) (z : ℝ≥0),
      occupationCorrection θ ε (supAuxLadderTime θ z f) f = 0 := by
  filter_upwards [ae_supAuxLadder_spec hθ, ae_eval_zero_stableLocalLaw hθ] with f hf h0
  intro ε z
  apply occupationCorrection_eq_zero
  rw [supReflectedFrom_zero_apply h0]
  exact hf.2.2.2.2.2.2.2.1 z

/-- The energy bound vanishes with `ε` (`V_ε → 0`, fixed `z`). -/
theorem tendsto_stopped_energy_bound {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (z : ℝ≥0) :
    Tendsto (fun ε : ℝ =>
        104 * ((z : ℝ) * supCorrectionBound θ ε + supCorrectionBound θ ε ^ 2))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have ht := tendsto_supCorrectionBound hθ
  simpa only [mul_zero, zero_pow (by decide : 2 ≠ 0), add_zero] using
    ((ht.const_mul (z : ℝ)).add (ht.pow 2)).const_mul 104

private theorem errStopTime_eq_min (n : ℕ) (σ : DLoc → ℝ≥0∞) (s : ℝ≥0) (f : DLoc) :
    errStopTime n σ s f = min s (min (σ f) (errCutoff n f)).toNNReal := by
  have hf : min (σ f) (errCutoff n f) ≠ ⊤ :=
    ne_top_of_le_ne_top (by exact_mod_cast ENNReal.coe_ne_top (r := (n : ℝ≥0)))
      ((min_le_right _ _).trans (errCutoff_le n f))
  apply ENNReal.coe_injective
  rw [coe_errStopTime, min_assoc, ENNReal.coe_min, ENNReal.coe_toNNReal hf]

/-- The bounded stopping epoch is monotone in its deterministic horizon. -/
theorem monotone_errStopTime (n : ℕ) (σ : DLoc → ℝ≥0∞) (f : DLoc) :
    Monotone (fun s => errStopTime n σ s f) := by
  simp_rw [errStopTime_eq_min]
  exact monotone_id.min monotone_const

/-- As a function of the deterministic horizon the finite stopping epoch is continuous. -/
theorem continuous_errStopTime (n : ℕ) (σ : DLoc → ℝ≥0∞) (f : DLoc) :
    Continuous (fun s => errStopTime n σ s f) := by
  simp_rw [errStopTime_eq_min]
  exact continuous_id.min continuous_const

/-- **Energy estimate** `E D_τ² ≤ 4 z V_ε + 12 V_ε²` at `τ = A_z ∧ t ∧ cutoff_n`
(summation by parts for the error martingale `D` against the finite-variation `C = O - M^*`;
the `dM^*` term vanishes since `w = 0` on `{R = 0}`). -/
theorem integral_sq_errorMartingale_stopped_le {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {ε : ℝ}
    (hε : 0 < ε) (z : ℝ≥0) (n : ℕ) (t : ℝ≥0) :
    Integrable (fun f => (errorMartingale θ ε (errStopTime n (supHitting θ z) t f) f) ^ 2)
        (stableLocalLaw θ : Measure DLoc) ∧
      ∫ f, (errorMartingale θ ε (errStopTime n (supHitting θ z) t f) f) ^ 2
          ∂(stableLocalLaw θ : Measure DLoc) ≤
        4 * (z : ℝ) * supCorrectionBound θ ε + 12 * supCorrectionBound θ ε ^ 2 := by
  have hσ := isStoppingTime_supHitting θ z
  have hi := integrable_sq_errorMartingale_stopped hθ hε n hσ t
  refine ⟨hi, ?_⟩
  have hO : StronglyAdapted DLoc.filtration
      (fun s f => supOccupation ε f (errStopTime n (supHitting θ z) s f)) :=
    fun s => stronglyMeasurable_errStopTime_eval (isStronglyProgressive_supOccupation hε) n hσ s
  have hM : StronglyAdapted DLoc.filtration
      (fun s f => supAuxLocalTime θ f (errStopTime n (supHitting θ z) s f)) :=
    fun s => stronglyMeasurable_errStopTime_eval (isStronglyProgressive_supAuxLocalTime hθ) n hσ s
  have henergy := integral_sq_le_of_martingale_nonneg_correction
    (martingale_errorMartingale_stopped hθ hε n hσ) hO hM t
    (K := (t : ℝ) / ε) (L := (z : ℝ)) (B := 2 * supCorrectionBound θ ε)
    (by positivity) z.coe_nonneg hi ?_
  · have hV : 0 ≤ supCorrectionBound θ ε := by
      have hg := Real.Gamma_pos_of_pos (by linarith [hθ.1] : 0 < θ)
      unfold supCorrectionBound
      positivity
    have hmean := (integral_supOccupation_errStopTime_le hθ hε z n t).2
    nlinarith [mul_le_mul_of_nonneg_left hmean (show 0 ≤ 4 * supCorrectionBound θ ε by
      positivity)]
  · filter_upwards [ae_supAuxLocalTime_spec hθ, ae_errorMartingale_zero hθ hε,
      ae_supAuxLocalTime_errStopTime_le hθ z] with f hf hD0 hMb
    have he0 : errStopTime n (supHitting θ z) 0 f = 0 := by simp [errStopTime]
    have hep := continuous_errStopTime n (supHitting θ z) f
    refine ⟨by simp only [he0, supOccupation_zero], by simpa only [he0] using hf.1,
      by simpa only [he0] using hD0,
      (monotone_supOccupation hε.le f).comp (monotone_errStopTime n (supHitting θ z) f),
      hf.2.1.comp (monotone_errStopTime n (supHitting θ z) f),
      ((continuous_supOccupation hε f).comp hep).sub (hf.2.2.1.comp hep), ?_, hMb n t, ?_⟩
    · have hb := (supOccupation_sub_mem hε f
        (show (0 : ℝ≥0) ≤ errStopTime n (supHitting θ z) t f from zero_le)).2
      simp only [supOccupation_zero, NNReal.coe_zero, sub_zero] at hb
      exact hb.trans (by
        rw [div_eq_mul_inv, mul_comm]
        exact mul_le_mul_of_nonneg_right
          (NNReal.coe_le_coe.mpr (errStopTime_le n (supHitting θ z) t f))
          (inv_pos.mpr hε).le)
    · intro s _hs
      simp only [errorMartingale, add_sub_cancel_left]
      exact ⟨occupationCorrection_nonneg hθ hε _ f,
        (le_abs_self _).trans (abs_occupationCorrection_le hθ hε _ f)⟩

end BGW.StableTrees
