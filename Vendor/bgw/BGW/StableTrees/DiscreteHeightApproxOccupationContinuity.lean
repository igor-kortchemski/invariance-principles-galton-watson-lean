/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.DiscreteHeightApproxFiniteOccupation
import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import BGW.Skorokhod.StepApprox

/-!
# Dominated convergence for finite-path occupations

Lebesgue integration stays in the original time coordinate. Pointwise J1 continuity
of gaps away from jump times and null boundary levels suffices.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal Classical
open BGW.Skorokhod

namespace BGW.StableTrees.DiscreteHeightApprox

/-- The future-infimum gap of a constantly extended finite path. -/
noncomputable def finiteGap (T t : ℝ≥0) (f : D (T : ℝ) ℝ) (s : ℝ) : ℝ :=
  (extendFinitePath T f).1 s.toNNReal - futureInf (extendFinitePath T f) t s.toNNReal

/-- The finite-path gap is measurable in its real time coordinate. -/
theorem measurable_finiteGap_time (T t : ℝ≥0) (f : D (T : ℝ) ℝ) :
    Measurable (finiteGap T t f) := by
  have hx : Measurable (fun s : ℝ => (extendFinitePath T f).1 s.toNNReal) :=
    Measurable.comp (g := fun p : DLoc × ℝ≥0 => p.1.1 p.2)
      (f := fun s : ℝ => (extendFinitePath T f, s.toNNReal))
      DLoc.measurable_eval₂ (measurable_const.prodMk measurable_real_toNNReal)
  have hi : Measurable (fun s : ℝ => futureInf (extendFinitePath T f) t s.toNNReal) :=
    Measurable.comp
      (g := fun p : (ℝ≥0 × ℝ≥0) × DLoc => futureInf p.2 p.1.1 p.1.2)
      (f := fun s : ℝ => ((t, s.toNNReal), extendFinitePath T f))
      measurable_futureInf_uncurry
      ((measurable_const.prodMk measurable_real_toNNReal).prodMk measurable_const)
  exact hx.sub hi

private def occupationEvent (T t : ℝ≥0) (ε : ℝ) (f : D (T : ℝ) ℝ) : Set ℝ :=
  Icc 0 (t : ℝ) ∩ {s | finiteGap T t f s < ε}

private theorem measurableSet_occupationEvent (T t : ℝ≥0) (ε : ℝ) (f : D (T : ℝ) ℝ) :
    MeasurableSet (occupationEvent T t ε f) :=
  measurableSet_Icc.inter (measurableSet_lt (measurable_finiteGap_time T t f) measurable_const)

private theorem finiteHeightApprox_eq_integral (T t : ℝ≥0) (ε : ℝ) (f : D (T : ℝ) ℝ) :
    finiteHeightApprox T t ε f = ε⁻¹ *
      ∫ s : ℝ, (occupationEvent T t ε f).indicator (fun _ => (1 : ℝ)) s := by
  rw [integral_indicator_const (1 : ℝ) (measurableSet_occupationEvent T t ε f)]
  simp only [smul_eq_mul, mul_one, measureReal_def]
  unfold finiteHeightApprox heightApprox
  congr 3
  ext s
  simp only [occupationEvent, mem_inter_iff, mem_Icc, mem_ofPred_eq, finiteGap,
    sub_lt_iff_lt_add, add_comm ε]
  tauto

/-- Dominated convergence gives occupation continuity whenever the gap is pointwise
continuous almost everywhere in the window and the boundary level has zero measure. -/
theorem continuousAt_finiteHeightApprox_of_ae (T t : ℝ≥0) (ε : ℝ) {f : D (T : ℝ) ℝ}
    (hc : ∀ᵐ s : ℝ, s ∈ Icc 0 (t : ℝ) → ContinuousAt (fun g => finiteGap T t g s) f)
    (hb : volume {s : ℝ | s ∈ Icc 0 (t : ℝ) ∧ finiteGap T t f s = ε} = 0) :
    ContinuousAt (finiteHeightApprox T t ε) f := by
  let F (g : D (T : ℝ) ℝ) := (occupationEvent T t ε g).indicator (fun _ => (1 : ℝ))
  let bound := (Icc 0 (t : ℝ)).indicator (fun _ => (1 : ℝ))
  have hm (g : D (T : ℝ) ℝ) : AEStronglyMeasurable (F g) (volume : Measure ℝ) :=
    (measurable_const.indicator (measurableSet_occupationEvent T t ε g)).aestronglyMeasurable
  have hbound (g : D (T : ℝ) ℝ) (s : ℝ) : ‖F g s‖ ≤ bound s := by
    by_cases hs : s ∈ Icc 0 (t : ℝ)
    · by_cases hg : finiteGap T t g s < ε <;> simp [F, bound, occupationEvent, hs, hg]
    · simp [F, bound, occupationEvent, hs]
  have hint : Integrable bound (volume : Measure ℝ) :=
    (integrableOn_const (s := Icc 0 (t : ℝ))
      (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)).integrable_indicator measurableSet_Icc
  have hn := measure_eq_zero_iff_ae_notMem.mp hb
  have hlim : ∀ᵐ s : ℝ, Tendsto (fun g => F g s) (𝓝 f) (𝓝 (F f s)) := by
    filter_upwards [hc, hn] with s hcs hns
    by_cases hs : s ∈ Icc 0 (t : ℝ)
    · have hne : finiteGap T t f s ≠ ε := fun he => hns ⟨hs, he⟩
      rcases lt_or_gt_of_ne hne with hl | hl
      · have he := (hcs hs).eventually (gt_mem_nhds hl)
        apply tendsto_const_nhds.congr'
        filter_upwards [he] with g hg
        simp [F, occupationEvent, hs, hl, hg]
      · have he := (hcs hs).eventually (lt_mem_nhds hl)
        apply tendsto_const_nhds.congr'
        filter_upwards [he] with g hg
        simp [F, occupationEvent, hs, not_lt.mpr hl.le, not_lt.mpr hg.le]
    · have he : (fun g => F g s) = fun _ => (0 : ℝ) := by
        funext g
        simp [F, occupationEvent, hs]
      have hz : F f s = 0 := by simp [F, occupationEvent, hs]
      rw [he, hz]
      exact tendsto_const_nhds
  have ht := tendsto_integral_filter_of_dominated_convergence bound
    (Eventually.of_forall hm) (Eventually.of_forall fun g => Eventually.of_forall (hbound g))
    hint hlim
  have hmul := ht.const_mul ε⁻¹
  change Tendsto (finiteHeightApprox T t ε) (𝓝 f) (𝓝 (finiteHeightApprox T t ε f))
  simpa only [F, ← finiteHeightApprox_eq_integral] using hmul

/-- A càdlàg path is continuous where its left limit agrees with its value. -/
theorem continuousAt_of_leftLim_eq {T : ℝ} (f : D T ℝ) (s : Icc (0 : ℝ) T)
    (hs : Function.leftLim f s = f s) : ContinuousAt f s := by
  apply continuousAt_iff_continuous_left'_right'.mpr
  constructor
  · change Tendsto (fun u => f u) (𝓝[<] s) (𝓝 (f s))
    simpa only [hs] using (isCadlag f).tendsto_nhdsLT_leftLim s
  · exact (isCadlag f).isRightContinuous s

/-- At almost every real time in the window, the finite-path gap is J1-continuous. -/
theorem ae_continuousAt_finiteGap (T t : ℝ≥0) (ht : t ≤ T) {f : D (T : ℝ) ℝ}
    (htf : t = T ∨ ContinuousAt f ⟨t, t.2, ht⟩) :
    ∀ᵐ s : ℝ, s ∈ Icc 0 (t : ℝ) → ContinuousAt (fun g => finiteGap T t g s) f := by
  let C : Set ℝ := Subtype.val '' {u : Icc (0 : ℝ) (T : ℝ) | Function.leftLim f u ≠ f u}
  have hC : C.Countable := (countable_setOf_jump_ne f).image Subtype.val
  have hn : ∀ᵐ s : ℝ, s ∉ C := measure_eq_zero_iff_ae_notMem.mp (hC.measure_zero volume)
  filter_upwards [hn] with s hs hswin
  let u : Icc (0 : ℝ) (T : ℝ) := ⟨s, hswin.1, hswin.2.trans ht⟩
  have hleft : Function.leftLim f u = f u := by
    by_contra hne
    exact hs ⟨u, hne, rfl⟩
  have hcont := continuousAt_of_leftLim_eq f u hleft
  have hst : s.toNNReal ≤ t := Real.toNNReal_le_iff_le_coe.mpr hswin.2
  have hsf : ContinuousAt f ⟨s.toNNReal, s.toNNReal.2, hst.trans ht⟩ := by
    have he : (⟨s.toNNReal, s.toNNReal.2, hst.trans ht⟩ : Icc (0 : ℝ) (T : ℝ)) = u := by
      apply Subtype.ext
      exact Real.coe_toNNReal s hswin.1
    rw [he]
    exact hcont
  exact continuousAt_extended_gap T hst ht hsf htf

/-- The finite occupation functional is J1-continuous away from null boundary levels. -/
theorem continuousAt_finiteHeightApprox (T t : ℝ≥0) (ht : t ≤ T) (ε : ℝ)
    {f : D (T : ℝ) ℝ} (htf : t = T ∨ ContinuousAt f ⟨t, t.2, ht⟩)
    (hb : volume {s : ℝ | s ∈ Icc 0 (t : ℝ) ∧ finiteGap T t f s = ε} = 0) :
    ContinuousAt (finiteHeightApprox T t ε) f :=
  continuousAt_finiteHeightApprox_of_ae T t ε (ae_continuousAt_finiteGap T t ht htf) hb

end BGW.StableTrees.DiscreteHeightApprox
