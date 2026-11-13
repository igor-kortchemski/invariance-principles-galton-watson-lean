/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.SupremumLadderTransformBasic
public import BGW.StableTrees.SupremumLadderTransformCumulative

/-!
# The Stieltjes measure of the decreasing boundary weight

The measure is controlled through its tails. It need not be absolutely continuous:
jumps of the running supremum can create atoms.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees

/-- The Stieltjes function of the negative boundary weight, extended constantly to negative time.

Reference: Bertoin, *Lévy Processes*, Chapter VI. -/
noncomputable def supWeightStieltjes (q lam : ℝ) (hq : 0 ≤ q) (hlam : 0 ≤ lam)
    (f : DLoc) : StieltjesFunction ℝ where
  toFun t := -Real.exp (-q * (t.toNNReal : ℝ) - lam * supRunning f t.toNNReal)
  mono' := by
    intro s t hst
    apply neg_le_neg
    apply Real.exp_le_exp.mpr
    have ht := NNReal.coe_le_coe.mpr (Real.toNNReal_mono hst)
    have hs := monotone_supRunning f (Real.toNNReal_mono hst)
    nlinarith [mul_le_mul_of_nonneg_left ht hq, mul_le_mul_of_nonneg_left hs hlam]
  right_continuous' := by
    intro t
    have hS : ContinuousWithinAt (supRunning f) (Ici t.toNNReal) t.toNNReal :=
      continuousWithinAt_Ioi_iff_Ici.mp ((isCadlag_supRunning f).isRightContinuous _)
    have hcomp : ContinuousWithinAt (fun s : ℝ => supRunning f s.toNNReal) (Ici t) t :=
      hS.comp continuous_real_toNNReal.continuousWithinAt (fun s hs => Real.toNNReal_mono hs)
    exact (((continuous_const.mul
      (NNReal.continuous_coe.comp continuous_real_toNNReal)).continuousWithinAt.sub
        (hcomp.const_mul lam)).rexp).neg

private theorem supWeight_tendsto {q lam : ℝ} (hq : 0 < q) (hlam : 0 ≤ lam)
    {f : DLoc} (hf : f.1 0 = 0) :
    Tendsto (supWeightStieltjes q lam hq.le hlam f) atTop (𝓝 0) := by
  have hS (t : ℝ) : 0 ≤ supRunning f t.toNNReal := by
    simpa only [hf] using eval_le_supRunning f (u := 0) (zero_le : 0 ≤ t.toNNReal)
  have hw : Tendsto (fun t : ℝ =>
      Real.exp (-q * (t.toNNReal : ℝ) - lam * supRunning f t.toNNReal)) atTop (𝓝 0) := by
    apply squeeze_zero' (g := fun t : ℝ => Real.exp (-q * t))
      (Eventually.of_forall fun t => (Real.exp_pos _).le)
    · filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
      rw [Real.coe_toNNReal _ ht]
      apply Real.exp_le_exp.mpr
      nlinarith [mul_nonneg hlam (hS t)]
    · have h := Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop hq)
      simpa only [Function.comp_def, id_eq, neg_mul] using h
  simpa only [supWeightStieltjes, neg_zero] using hw.neg

/-- Positive-time tails of the weight measure are exactly the boundary weight.

Reference: Bertoin, *Lévy Processes*, Chapter VI. -/
theorem supWeightStieltjes_measure_Ioi {q lam : ℝ} (hq : 0 < q) (hlam : 0 ≤ lam)
    {f : DLoc} (hf : f.1 0 = 0) {t : ℝ} (ht : 0 ≤ t) :
    (supWeightStieltjes q lam hq.le hlam f).measure (Ioi t) =
      ENNReal.ofReal (Real.exp (-q * t - lam * supRunning f t.toNNReal)) := by
  rw [StieltjesFunction.measure_Ioi _ (supWeight_tendsto hq hlam hf)]
  simp only [supWeightStieltjes, Real.coe_toNNReal _ ht, zero_sub, neg_neg]

/-- Tail domination by the pure time discount; this is not domination of measures.

Reference: Bertoin, *Lévy Processes*, Chapter VI. -/
theorem supWeightStieltjes_measure_Ioi_le {q lam : ℝ} (hq : 0 < q) (hlam : 0 ≤ lam)
    {f : DLoc} (hf : f.1 0 = 0) {t : ℝ} (ht : 0 ≤ t) :
    (supWeightStieltjes q lam hq.le hlam f).measure (Ioi t) ≤
      ENNReal.ofReal (Real.exp (-q * t)) := by
  rw [supWeightStieltjes_measure_Ioi hq hlam hf ht]
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  have hs : 0 ≤ supRunning f t.toNNReal := by
    simpa only [hf] using eval_le_supRunning f (u := 0) (zero_le : 0 ≤ t.toNNReal)
  nlinarith [mul_nonneg hlam hs]

/-- The weighted boundary clock integral is its cumulative integral against the weight measure.

Reference: Bertoin, *Lévy Processes*, Chapter VI. -/
theorem pathStieltjes_lintegral_supWeight {q lam : ℝ} (hq : 0 < q) (hlam : 0 ≤ lam)
    {f : DLoc} (hf : f.1 0 = 0) {m : ℝ≥0 → ℝ}
    (hm : Monotone m ∧ Continuous m) (hm0 : m 0 = 0) :
    (∫⁻ t in Ioi (0 : ℝ),
      ENNReal.ofReal (Real.exp (-q * t - lam * supRunning f t.toNNReal))
        ∂(pathStieltjes m).measure) =
      ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (m s.toNNReal)
        ∂(supWeightStieltjes q lam hq.le hlam f).measure := by
  rw [← pathStieltjes_lintegral_tail hm hm0]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact (supWeightStieltjes_measure_Ioi hq hlam hf ht.le).symm

end BGW.StableTrees
