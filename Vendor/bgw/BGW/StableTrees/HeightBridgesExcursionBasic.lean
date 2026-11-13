/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.KendallAdapter
public import BGW.StableTrees.HeightProcessBasic
public import BGW.StableTrees.ExcursionMarkov
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Small-depth bounds for the excursion approximation

Kendall's identity and the bounded stable density give a linear survival bound uniform in
the time and barrier. It bounds a small infimum depth, and the same bound applies to
the killed stable kernel, uniformly in its starting level, on survival to the observation time.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees

/-- A uniform linear survival bound, with the stable time exponent. -/
theorem exists_sizeTailKernel_le {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r x : ℝ, 0 < r → 0 < x →
      sizeTailKernel θ r x ≤ C * x * r ^ (-1 / θ) := by
  have hθpos : 0 < θ := lt_trans zero_lt_one hθ.1
  obtain ⟨M, hM, hbound⟩ := Scalar.exists_stableDensity_le (α := θ)
  refine ⟨M * θ, mul_nonneg hM hθpos.le, fun r x hr hx => ?_⟩
  have hp : -1 - 1 / θ < -1 := by linarith [one_div_pos.mpr hθpos]
  have hmajor : IntegrableOn (fun s : ℝ => M * x * s ^ (-1 - 1 / θ)) (Ioi r) :=
    (integrableOn_Ioi_rpow_of_lt hp hr).const_mul _
  have hq (s : ℝ) (hs : s ∈ Ioi r) :
      qKernel θ s x ≤ M * x * s ^ (-1 - 1 / θ) := by
    have hspos : 0 < s := hr.trans hs
    calc
      qKernel θ s x ≤ (x / s) * (s ^ (-1 / θ) * M) := by
        apply mul_le_mul_of_nonneg_left _ (div_nonneg hx.le hspos.le)
        exact mul_le_mul_of_nonneg_left ((le_abs_self _).trans (hbound _))
          (Real.rpow_nonneg hspos.le _)
      _ = M * x * s ^ (-1 - 1 / θ) := by
        rw [show -1 - 1 / θ = (-1 : ℝ) + (-1 / θ) by ring,
          Real.rpow_add hspos, Real.rpow_neg_one, div_eq_mul_inv]
        ring
  have hqi : IntegrableOn (fun s => qKernel θ s x) (Ioi r) :=
    hmajor.mono'
      (((measurable_qKernel θ).comp
        (measurable_id.prodMk measurable_const)).aestronglyMeasurable.restrict)
      (by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
        rw [Real.norm_eq_abs, abs_of_nonneg (qKernel_nonneg hθ (hr.trans hs) hx.le)]
        exact hq s hs)
  calc
    sizeTailKernel θ r x ≤ ∫ s in Ioi r, M * x * s ^ (-1 - 1 / θ) :=
      integral_mono_ae hqi hmajor (by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs using hq s hs)
    _ = M * x * (-r ^ ((-1 - 1 / θ) + 1) / ((-1 - 1 / θ) + 1)) := by
      rw [integral_const_mul, integral_Ioi_rpow_of_lt hp hr]
    _ = (M * θ) * x * r ^ (-1 / θ) := by
      rw [show (-1 - 1 / θ) + 1 = -1 / θ by ring]
      field_simp

/-- Uniform small-depth estimate for the running infimum. -/
theorem exists_measure_runningInf_gt_neg_le {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (r : ℝ≥0) (x : ℝ), 0 < r → 0 < x →
      (stableLocalLaw θ : Measure DLoc) {f | -x < runningInfLoc f r} ≤
        ENNReal.ofReal (C * x * (r : ℝ) ^ (-1 / θ)) := by
  obtain ⟨C, hC, hbound⟩ := exists_sizeTailKernel_le hθ
  refine ⟨C, hC, fun r x hr hx => ?_⟩
  let a : ℝ≥0 := ⟨x, hx.le⟩
  have ha : 0 < a := hx
  calc
    (stableLocalLaw θ : Measure DLoc) {f | -x < runningInfLoc f r} ≤
        (stableLocalLaw θ : Measure DLoc) {f | (r : ℝ) < (passageTime a f : ℝ)} := by
      apply measure_mono_ae
      filter_upwards [ae_passageTime_eq_firstPassageBelow hθ] with f hf
      intro h
      by_contra hn
      have hle : passageTime a f ≤ r := by exact_mod_cast (not_lt.mp hn)
      have hpass : firstPassageBelow a f ≤ (r : WithTop ℝ≥0) := by
        rw [hf.1 a, WithTop.coe_le_coe]
        exact hle
      exact (not_lt_of_ge (runningInfLoc_le_of_firstPassageBelow_le f hpass)) h
    _ = passageLaw θ a (Ioi (r : ℝ)) := by
      rw [passageLaw, Measure.map_apply
        (measurable_passageTime a).coe_nnreal_real measurableSet_Ioi]
      rfl
    _ = ENNReal.ofReal (sizeTailKernel θ r x) := by
      exact (sizeTailKernelENN_eq_passageLaw hθ r.2 a ha).symm.trans
        (ofReal_sizeTailKernel hθ r.2 hx).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal (hbound r x hr hx)

/-- The small-depth bound persists under killing, uniformly in the starting height. -/
theorem exists_killedStableKernel_small_depth_le {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (r y : ℝ≥0) (ε : ℝ), 0 < r → 0 < ε →
      killedStableKernel θ y
        {g | 0 < g.1 r ∧ g.1 0 < futureInf g r 0 + ε} ≤
          ENNReal.ofReal (C * ε * (r : ℝ) ^ (-1 / θ)) := by
  obtain ⟨C, hC, hbound⟩ := exists_measure_runningInf_gt_neg_le hθ
  refine ⟨C, hC, fun r y ε hr hε => ?_⟩
  have hA : MeasurableSet {g : DLoc | 0 < g.1 r ∧ g.1 0 < futureInf g r 0 + ε} :=
    (measurableSet_lt measurable_const (DLoc.measurable_eval r)).inter
      (measurableSet_lt (DLoc.measurable_eval 0)
        ((measurable_futureInf_uncurry.comp
          ((measurable_const.prodMk measurable_const).prodMk measurable_id)).add
            measurable_const))
  by_cases hy : y = 0
  · subst y
    rw [killedStableKernel_zero hθ, Measure.dirac_apply' _ hA]
    rw [Set.indicator_of_notMem (show zeroLoc ∉
      {g : DLoc | 0 < g.1 r ∧ g.1 0 < futureInf g r 0 + ε} by
        rintro ⟨h, _⟩
        exact (lt_irrefl (0 : ℝ)) h)]
    exact zero_le
  have hypos : 0 < y := pos_iff_ne_zero.mpr hy
  have hkill : Measurable (killedPath y) :=
    measurable_killedPath_uncurry.comp (measurable_const.prodMk measurable_id)
  rw [killedStableKernel_apply, Measure.map_apply hkill hA]
  refine le_trans (measure_mono_ae ?_) (hbound r ε hr hε)
  filter_upwards [ae_killedPath_spec hθ y hypos, ae_passageTime_eq_firstPassageBelow hθ]
    with f hf hT
  rintro ⟨hpos, hmargin⟩
  have hbefore : (r : WithTop ℝ≥0) < firstPassageBelow y f := by
    by_contra hn
    have hz := hf.2.2.2 r (not_lt.mp hn)
    exact hpos.ne' hz
  have hrt : r < passageTime y f := by
    simpa only [hT.1 y, WithTop.coe_lt_coe] using hbefore
  have hi : futureInf (killedPath y f) r 0 - y ≤ runningInfLoc f r := by
    unfold runningInfLoc
    apply le_ciInf
    intro u
    have hu : (killedPath y f).1 u = (y : ℝ) + f.1 u := by
      have huT : (u : ℝ≥0) ≤ passageTime y f := u.2.trans hrt.le
      simpa only [min_eq_left huT] using killedPath_apply_of_lt_top (hT.1 y) (u : ℝ≥0)
    have hb := futureInf_le_eval (killedPath y f) r 0 u ⟨by simp, u.2⟩
    rw [hu] at hb
    linarith only [hb]
  rw [hf.1] at hmargin
  change -ε < runningInfLoc f r
  linarith only [hi, hmargin]

end BGW.StableTrees
