/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.SupremumPotential
import Mathlib.Topology.Order.IsLUB
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Compact occupation errors and their resolvent martingale

The occupation Cauchy construction uses the reflected resolvent at rate one.
It builds on `BGW.StableTrees.SupremumPotential`, `BGW.StableTrees.SupremumReflectedFamily` and
the Doob estimates of `BGW.Probability.DoobL2Resolvent`.

## References

* [J. Bertoin, *Lévy Processes*, Cambridge University Press, 1996, Chapter IV]
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod
open BGW.Probability

namespace BGW.StableTrees

/-- `sup_{t ≤ T} |O_ε(t) - O_η(t)|`. -/
noncomputable def compactError (ε η : ℝ) (T : ℝ≥0) (f : DLoc) : ℝ :=
  ⨆ t : Set.Iic T, |supOccupation ε f t - supOccupation η f t|

/-- The martingale `J_t = ∫_0^t e^{-s}(g_ε-g_η)(R^0_s)ds + e^{-t}(u¹_ε-u¹_η)(R^0_t)`
(`= E[B_ε - B_η | F_t]`; the explicit version of `martingale_discounted_resolvent`). -/
noncomputable def occupationDiffMartingale (θ ε η : ℝ) (t : ℝ≥0) (f : DLoc) : ℝ :=
  (∫ s in Ioc (0 : ℝ) t, Real.exp (-s) *
      (supOccKernel ε (supReflectedFrom 0 f s.toNNReal) -
        supOccKernel η (supReflectedFrom 0 f s.toNNReal))) +
    Real.exp (-(t : ℝ)) * (supOccupationResolvent θ 1 ε (supReflectedFrom 0 f t) -
      supOccupationResolvent θ 1 η (supReflectedFrom 0 f t))

/-- A fast sequence: positive, strictly decreasing to `0`, and for every `k` and every
`η ∈ (0, ε_k]` the squared compact error on `[0,k]` is integrable with mean `≤ 16⁻ᵏ`
(summable errors on integer horizons; Borel–Cantelli with thresholds `2⁻ᵏ`). -/
def IsSupAuxEpsSeq (θ : ℝ) (ε : ℕ → ℝ) : Prop :=
  (∀ k, 0 < ε k) ∧ StrictAnti ε ∧ Tendsto ε atTop (𝓝 0) ∧
    ∀ k : ℕ, ∀ η : ℝ, 0 < η → η ≤ ε k →
      Integrable (fun f => (compactError (ε k) η k f) ^ 2) (stableLocalLaw θ : Measure DLoc) ∧
      ∫ f, (compactError (ε k) η k f) ^ 2 ∂(stableLocalLaw θ : Measure DLoc) ≤ (1 / 16 : ℝ) ^ k

/-- The compact occupation error is Borel measurable. -/
theorem measurable_compactError {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) (T : ℝ≥0) :
    Measurable (compactError ε η T) := by
  obtain ⟨Q, hQ, hdQ⟩ := TopologicalSpace.exists_countable_dense (Set.Iic T)
  let _ : Countable Q := hQ.to_subtype
  have he (f : DLoc) : compactError ε η T f =
      ⨆ q : Q, |supOccupation ε f q.1 - supOccupation η f q.1| := by
    exact (hdQ.ciSup' (((continuous_supOccupation hε f).sub
      (continuous_supOccupation hη f)).abs.comp continuous_subtype_val)).symm
  rw [show compactError ε η T = _ from funext he]
  apply Measurable.iSup
  intro q
  have h₁ : Measurable (fun f : DLoc => supOccupation ε f q.1) :=
    measurable_supOccupation_uncurry.comp
      (measurable_const.prodMk (measurable_const.prodMk measurable_id))
  have h₂ : Measurable (fun f : DLoc => supOccupation η f q.1) :=
    measurable_supOccupation_uncurry.comp
      (measurable_const.prodMk (measurable_const.prodMk measurable_id))
  simpa only [Pi.sub_apply, Real.norm_eq_abs] using (h₁.sub h₂).norm

/-- Occupation is the time integral of its reflected kernel on zero-start paths. -/
theorem supOccupation_eq_integral_supOccKernel {ε : ℝ} (f : DLoc) (h0 : f.1 0 = 0)
    (t : ℝ≥0) :
    supOccupation ε f t =
      ∫ s in Ioc (0 : ℝ) t, supOccKernel ε (supReflectedFrom 0 f s.toNNReal) := by
  have hm : Measurable (fun s : ℝ => supReflected f s.toNNReal) :=
    measurable_supReflected_uncurry.comp (measurable_real_toNNReal.prodMk measurable_const)
  have hs : MeasurableSet {s : ℝ | supReflected f s.toNNReal < ε} :=
    measurableSet_lt hm measurable_const
  simp_rw [supReflectedFrom_zero_apply h0]
  rw [← integral_Icc_eq_integral_Ioc]
  have he : (fun s : ℝ => supOccKernel ε (supReflected f s.toNNReal)) =
      {s : ℝ | supReflected f s.toNNReal < ε}.indicator (fun _ => ε⁻¹) := by
    ext s
    simp [supOccKernel, indicator_apply]
  rw [he, setIntegral_indicator hs, setIntegral_const]
  have hset : Icc (0 : ℝ) t ∩ {s : ℝ | supReflected f s.toNNReal < ε} =
      {s : ℝ | 0 ≤ s ∧ s ≤ (t : ℝ) ∧ supReflected f s.toNNReal < ε} := by
    ext s
    simp only [mem_inter_iff, mem_Icc, mem_ofPred_eq]
    tauto
  simp only [smul_eq_mul, Measure.real, supOccupation, hset]
  ring

/-- `O_ε(t) = ∫_0^t g_ε(R^0_s) ds` for all `t` simultaneously, almost surely. -/
theorem ae_supOccupation_eq_integral_supOccKernel {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {ε : ℝ}
    (hε : 0 < ε) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∀ t : ℝ≥0,
      supOccupation ε f t =
        ∫ s in Ioc (0 : ℝ) t, supOccKernel ε (supReflectedFrom 0 f s.toNNReal) := by
  -- `hε` is part of the interface (positivity of the cutoff) but is not needed by the proof.
  have _hε := hε
  filter_upwards [ae_eval_zero_stableLocalLaw hθ] with f hf
  exact supOccupation_eq_integral_supOccKernel f hf

private theorem kernel_abs_le {ε : ℝ} (hε : 0 < ε) (y : ℝ) :
    |supOccKernel ε y| ≤ ε⁻¹ := by
  rw [abs_of_nonneg (supOccKernel_mem_Icc hε y).1]
  exact (supOccKernel_mem_Icc hε y).2

-- Elaborating the generic resolvent theorem requires unfolding its process arguments.
/-- The explicit occupation resolvent process is a martingale. -/
theorem martingale_occupationDiffMartingale {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {ε η : ℝ}
    (hε : 0 < ε) (hη : 0 < η) :
    Martingale (fun t f => occupationDiffMartingale θ ε η t f) DLoc.filtration
      (stableLocalLaw θ : Measure DLoc) := by
  have hk : Measurable (fun r => supOccKernel ε r - supOccKernel η r) :=
    (measurable_supOccKernel ε).sub (measurable_supOccKernel η)
  have hkb : ∃ C, ∀ r, |supOccKernel ε r - supOccKernel η r| ≤ C :=
    ⟨ε⁻¹ + η⁻¹, fun r => (abs_sub _ _).trans
      (add_le_add (kernel_abs_le hε r) (kernel_abs_le hη r))⟩
  have hV : Measurable (fun y =>
      supOccupationResolvent θ 1 ε y - supOccupationResolvent θ 1 η y) :=
    (measurable_reflectedResolvent hθ 1 (measurable_supOccKernel ε)
      ⟨ε⁻¹, kernel_abs_le hε⟩).sub
    (measurable_reflectedResolvent hθ 1 (measurable_supOccKernel η)
      ⟨η⁻¹, kernel_abs_le hη⟩)
  have hVb : ∃ C, ∀ y,
      |supOccupationResolvent θ 1 ε y - supOccupationResolvent θ 1 η y| ≤ C := by
    refine ⟨ε⁻¹ + η⁻¹, fun y => (abs_sub _ _).trans (add_le_add ?_ ?_)⟩
    · simpa only [supOccupationResolvent, div_one] using
        abs_reflectedResolvent_le hθ zero_lt_one (measurable_supOccKernel ε) (kernel_abs_le hε) y
    · simpa only [supOccupationResolvent, div_one] using
        abs_reflectedResolvent_le hθ zero_lt_one (measurable_supOccKernel η) (kernel_abs_le hη) y
  have hZ : Measurable (fun p : ℝ≥0 × DLoc => supReflectedFrom 0 p.2 p.1) :=
    measurable_supReflectedFrom_uncurry.comp
      (measurable_const.prodMk (measurable_snd.prodMk measurable_fst))
  simpa only [occupationDiffMartingale] using
    (martingale_discounted_resolvent
      (Z := fun t (f : DLoc) => supReflectedFrom 0 f t)
      (k := fun r => supOccKernel ε r - supOccKernel η r)
      (V := fun y => supOccupationResolvent θ 1 ε y - supOccupationResolvent θ 1 η y)
      hZ hk hV hkb hVb
      (fun t => (hk.comp (isStronglyProgressive_supReflectedFrom 0 t).measurable).stronglyMeasurable)
      (fun t => (hV.comp (isStronglyProgressive_supReflectedFrom 0 t).measurable).stronglyMeasurable)
      (resolventMarkov_supReflectedFrom_sub hθ 0 hε hη))

/-- Every path of the occupation resolvent martingale is right continuous. -/
theorem rightContinuous_occupationDiffMartingale {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {ε η : ℝ}
    (hε : 0 < ε) (hη : 0 < η) (f : DLoc) (t : ℝ≥0) :
    ContinuousWithinAt (fun s : ℝ≥0 => occupationDiffMartingale θ ε η s f) (Ici t) t := by
  let k : ℝ → ℝ := fun s => supOccKernel ε (supReflectedFrom 0 f s.toNNReal) -
    supOccKernel η (supReflectedFrom 0 f s.toNNReal)
  have hk : Measurable k := by
    apply ((measurable_supOccKernel ε).sub (measurable_supOccKernel η)).comp
    exact measurable_supReflectedFrom_uncurry.comp
      (measurable_const.prodMk (measurable_const.prodMk measurable_real_toNNReal))
  have hb (s : ℝ) : ‖k s‖ ≤ ε⁻¹ + η⁻¹ := by
    simpa only [Real.norm_eq_abs] using (abs_sub _ _).trans
      (add_le_add (kernel_abs_le hε _) (kernel_abs_le hη _))
  have hi (a b : ℝ) : IntervalIntegrable (fun s => Real.exp (-s) * k s) volume a b := by
    have hki : IntervalIntegrable k volume a b := by
      apply (intervalIntegrable_const : IntervalIntegrable
        (fun _ : ℝ => ε⁻¹ + η⁻¹) volume a b).mono_fun'
        hk.aestronglyMeasurable
      exact ae_of_all _ hb
    exact hki.continuousOn_mul (Real.continuous_exp.comp continuous_neg).continuousOn
  have hc : Continuous (fun s : ℝ≥0 =>
      ∫ u in Ioc (0 : ℝ) s, Real.exp (-u) * k u) := by
    have he : (fun s : ℝ≥0 => ∫ u in Ioc (0 : ℝ) s, Real.exp (-u) * k u) =
        (fun s : ℝ≥0 => ∫ u in (0 : ℝ)..s, Real.exp (-u) * k u) := by
      funext s
      exact (intervalIntegral.integral_of_le s.coe_nonneg).symm
    rw [he]
    exact (intervalIntegral.continuous_primitive hi 0).comp NNReal.continuous_coe
  have hr : ContinuousWithinAt (supReflectedFrom 0 f) (Ici t) t :=
    continuousWithinAt_Ioi_iff_Ici.mp ((isCadlag_supReflectedFrom 0 f).isRightContinuous t)
  have hV : ContinuousOn (fun y => supOccupationResolvent θ 1 ε y -
      supOccupationResolvent θ 1 η y) (Ici 0) :=
    (continuousOn_supOccupationResolvent hθ zero_lt_one hε).sub
      (continuousOn_supOccupationResolvent hθ zero_lt_one hη)
  have hcomp := (hV _ (supReflectedFrom_nonneg 0 f t)).comp hr
    (fun s _ => supReflectedFrom_nonneg 0 f s)
  exact hc.continuousAt.continuousWithinAt.add
    ((Real.continuous_exp.comp NNReal.continuous_coe.neg).continuousAt.continuousWithinAt.mul hcomp)

end BGW.StableTrees
