/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.ExcursionMeasure
public import BGW.ContinuumTrees.ExcursionCarrier
public import BGW.Skorokhod.DLocShiftAt
public import BGW.StableTrees.StableFirstPassage
public import BGW.StableTrees.StablePassageSubordinator

import BGW.StableTrees.StableStrongMarkov
import Mathlib.Data.NNRat.Encodable

/-!
# Killed stable paths and excursion futures

The killed stable kernel uses strict downward passage of the driving process.
The excursion future is uncentred, and its lifetime is read by the last positive time.

Reference: J. Bertoin, *Lévy Processes*, Cambridge University Press, 1996, Chapter IV.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees

/-! ### Definitions -/

/-- The value of an excursion at time `t`, as a nonnegative real (`(e t).toNNReal`; the path
is nonnegative so nothing is lost). -/
noncomputable def Excursion.valueNN (e : Excursion) (t : ℝ≥0) : ℝ≥0 := (e.path.1 t).toNNReal

/-- Stop a path at an extended time: `⊤` leaves it unchanged, `↑a` is `stopLoc a`. -/
noncomputable def stopLocAt : WithTop ℝ≥0 → DLoc → DLoc
  | ⊤, f => f
  | (a : ℝ≥0), f => stopLoc a f

/-- **The killed path started at `y`**: `s ↦ y + X_{s ∧ T_y}` with `T_y = firstPassageBelow y`
(uncentred, frozen after the first passage below `-y`, where it equals `0` a.s.). -/
noncomputable def killedPath (y : ℝ≥0) (f : DLoc) : DLoc :=
  ⟨fun s => (y : ℝ) + (stopLocAt (firstPassageBelow y f) f).1 s,
    (stopLocAt (firstPassageBelow y f) f).2.continuous_comp (g := fun z : ℝ => (y : ℝ) + z)
      (continuous_const.add continuous_id)⟩

/-- **Uncentred future of an excursion after age `t`**: `s ↦ e(t + s)`. -/
noncomputable def futureFrom (t : ℝ≥0) (e : Excursion) : DLoc :=
  ⟨fun s => e.path.1 t + (DLoc.shift t e.path).1 s,
    (DLoc.shift t e.path).2.continuous_comp (g := fun z : ℝ => e.path.1 t + z)
      (continuous_const.add continuous_id)⟩

/-- **The killed stable kernel** `y ↦ Law_P(killedPath y)`, a kernel `ℝ≥0 → DLoc`, with the
zero path absorbing (`killedStableKernel_zero`). -/
noncomputable def killedStableKernel (θ : ℝ) : Kernel ℝ≥0 DLoc :=
  Kernel.map (Kernel.prod (Kernel.deterministic (id : ℝ≥0 → ℝ≥0) measurable_id)
    (Kernel.const ℝ≥0 (stableLocalLaw θ : Measure DLoc)))
    (fun p : ℝ≥0 × DLoc => killedPath p.1 p.2)

/-- **Last positive time** of a path: `sup {t | g t > 0}` (`⊥ = 0` if none).  Measurable
(`measurable_lastPositiveTime`), unlike weak first hitting of a closed set. -/
noncomputable def lastPositiveTime (g : DLoc) : WithTop ℝ≥0 :=
  ⨆ t : {t : ℝ≥0 // 0 < g.1 t}, ((t.1 : ℝ≥0) : WithTop ℝ≥0)

private theorem measurable_dLoc_of_eval {α : Type*} [MeasurableSpace α] (F : α → DLoc)
    (h : ∀ t : ℝ≥0, Measurable fun x => (F x).1 t) : Measurable F := by
  rw [measurable_iff_comap_le]
  change (⨆ t : ℝ≥0, MeasurableSpace.comap (DLoc.eval t) inferInstance).comap F ≤ _
  rw [MeasurableSpace.comap_iSup, iSup_le_iff]
  intro t
  rw [MeasurableSpace.comap_comp]
  exact (h t).comap_le

private lemma exists_nnrat_right_positive {g : DLoc} {t : ℝ≥0} (ht : 0 < g.1 t) :
    ∃ q : ℚ≥0, t < (q : ℝ≥0) ∧ 0 < g.1 q := by
  have hnhds : g.1 ⁻¹' Ioi 0 ∈ 𝓝[>] t :=
    (g.2.isRightContinuous t) (isOpen_Ioi.mem_nhds ht)
  obtain ⟨u, hu, hsub⟩ :=
    (mem_nhdsGT_iff_exists_mem_Ioc_Ioo_subset (show t < t + 1 by simp)).1 hnhds
  obtain ⟨r, hr, ha, hb⟩ := (NNReal.lt_iff_exists_rat_btwn t u).1 hu.1
  let q : ℚ≥0 := ⟨r, hr⟩
  have heq : (q : ℝ≥0) = Real.toNNReal (r : ℝ) := by
    apply NNReal.eq
    rw [Real.coe_toNNReal _ (Rat.cast_nonneg.2 hr)]
    exact NNRat.cast_mk r hr
  exact ⟨q, heq.symm ▸ ha, hsub ⟨heq.symm ▸ ha, heq.symm ▸ hb⟩⟩

private lemma lastPositiveTime_eq_nnrat (g : DLoc) :
    lastPositiveTime g = ⨆ q : ℚ≥0,
      if 0 < g.1 q then ((q : ℝ≥0) : WithTop ℝ≥0) else 0 := by
  classical
  apply le_antisymm
  · apply iSup_le
    intro t
    obtain ⟨q, htq, hq⟩ := exists_nnrat_right_positive t.2
    exact (WithTop.coe_le_coe.mpr htq.le).trans
      (le_iSup_of_le q (by simp only [ite_eq_left hq]; exact le_rfl))
  · apply iSup_le
    intro q
    split_ifs with hq
    · exact le_iSup_of_le ⟨q, hq⟩ le_rfl
    · exact bot_le

/-- `lastPositiveTime` is measurable: `{L > s} = ⋃_{q ∈ ℚ, q > s} {g q > 0}` by
right-continuity of `g`. -/
theorem measurable_lastPositiveTime : Measurable lastPositiveTime := by
  classical
  have heq : lastPositiveTime = fun g : DLoc => ⨆ q : ℚ≥0,
      if 0 < g.1 q then ((q : ℝ≥0) : WithTop ℝ≥0) else 0 :=
    funext lastPositiveTime_eq_nnrat
  rw [heq]
  exact Measurable.iSup fun q => Measurable.ite
    (measurableSet_lt measurable_const (DLoc.measurable_eval q))
    measurable_const measurable_const

/-- Evaluation of the future: `(futureFrom t e)(s) = e(t + s)`. -/
theorem futureFrom_apply (t : ℝ≥0) (e : Excursion) (s : ℝ≥0) :
    (futureFrom t e).1 s = e.path.1 (t + s) := by
  change e.path.1 t + (e.path.1 (t + s) - e.path.1 t) = _
  ring

/-- `futureFrom t` is measurable. -/
theorem measurable_futureFrom (t : ℝ≥0) : Measurable (futureFrom t) := by
  apply measurable_dLoc_of_eval
  intro s
  simpa only [futureFrom_apply] using measurable_excursion_eval (t + s)

/-- Evaluation of the killed path when the passage time is finite. -/
theorem killedPath_apply_of_lt_top {y : ℝ≥0} {f : DLoc} {τ : ℝ≥0}
    (h : firstPassageBelow y f = (τ : WithTop ℝ≥0)) (s : ℝ≥0) :
    (killedPath y f).1 s = (y : ℝ) + f.1 (min s τ) := by
  simp [killedPath, h, stopLocAt, stopLoc]

/-- Evaluation of the killed path when there is no passage. -/
theorem killedPath_apply_of_eq_top {y : ℝ≥0} {f : DLoc}
    (h : firstPassageBelow y f = ⊤) (s : ℝ≥0) : (killedPath y f).1 s = (y : ℝ) + f.1 s := by
  simp [killedPath, h, stopLocAt]

/-- **Joint measurability** of `(y, f) ↦ killedPath y f` (from
`measurable_firstPassageBelow_uncurry` and `DLoc.measurable_eval₂`). -/
theorem measurable_killedPath_uncurry :
    Measurable (fun p : ℝ≥0 × DLoc => killedPath p.1 p.2) := by
  apply measurable_dLoc_of_eval
  intro s
  have hT := measurable_firstPassageBelow_uncurry
  have htime : Measurable (fun p : ℝ≥0 × DLoc =>
      if firstPassageBelow p.1 p.2 = ⊤ then s
      else min s ((firstPassageBelow p.1 p.2).untopD 0)) :=
    Measurable.ite (measurableSet_eq_fun hT measurable_const) measurable_const
      (measurable_const.min (hT.untopD 0))
  have hm := measurable_fst.coe_nnreal_real.add
    (DLoc.measurable_eval₂.comp (measurable_snd.prodMk htime))
  convert hm using 1
  funext p
  change (killedPath p.1 p.2).1 s = (p.1 : ℝ) + p.2.1
    (if firstPassageBelow p.1 p.2 = ⊤ then s
    else min s ((firstPassageBelow p.1 p.2).untopD 0))
  by_cases htop : firstPassageBelow p.1 p.2 = ⊤
  · simp [killedPath_apply_of_eq_top htop, htop]
  · obtain ⟨τ, hτ⟩ := WithTop.ne_top_iff_exists.mp htop
    rw [killedPath_apply_of_lt_top hτ.symm, ite_eq_right htop, ← hτ,
      WithTop.untopD_coe]

/-- The kernel is the law of the killed path: `K_y = P.map (killedPath y)`. -/
theorem killedStableKernel_apply (θ : ℝ) (y : ℝ≥0) :
    killedStableKernel θ y = (stableLocalLaw θ : Measure DLoc).map (killedPath y) := by
  rw [killedStableKernel, Kernel.map_apply _ measurable_killedPath_uncurry,
    Kernel.prod_apply]
  simp only [Kernel.deterministic_apply, id_eq, Kernel.const_apply]
  rw [Measure.dirac_prod, Measure.map_map measurable_killedPath_uncurry
    measurable_prodMk_left]
  rfl

/-- The killed kernel is a Markov kernel (probability measures). -/
theorem isMarkovKernel_killedStableKernel (θ : ℝ) : IsMarkovKernel (killedStableKernel θ) := by
  exact Kernel.IsMarkovKernel.map _ measurable_killedPath_uncurry

private lemma killedPath_spec_of_creeping {f : DLoc} {y : ℝ≥0}
    (hf0 : f.1 0 = 0) (hfin : firstPassageBelow y f < ⊤)
    (hval : f.1 ((firstPassageBelow y f).untopD 0) = -(y : ℝ)) :
    (killedPath y f).1 0 = (y : ℝ) ∧ (∀ s, 0 ≤ (killedPath y f).1 s) ∧
      ∀ s : ℝ≥0, firstPassageBelow y f ≤ (s : WithTop ℝ≥0) →
        (killedPath y f).1 s = 0 := by
  obtain ⟨τ, hτ⟩ := WithTop.ne_top_iff_exists.mp hfin.ne
  have hT : firstPassageBelow y f = (τ : WithTop ℝ≥0) := hτ.symm
  have hv : f.1 τ = -(y : ℝ) := by
    simpa only [hT, WithTop.untopD_coe] using hval
  refine ⟨?_, ?_, ?_⟩
  · rw [killedPath_apply_of_lt_top hT]
    simp [hf0]
  · intro s
    rw [killedPath_apply_of_lt_top hT]
    by_cases hs : s < τ
    · rw [min_eq_left hs.le]
      have hle : -(y : ℝ) ≤ f.1 s := le_eval_of_lt_strictPassageBelow
        (by change (s : WithTop ℝ≥0) < firstPassageBelow y f; rw [hT]; exact_mod_cast hs)
      linarith
    · rw [min_eq_right (le_of_not_gt hs), hv]
      simp
  · intro s hs
    rw [hT, WithTop.coe_le_coe] at hs
    rw [killedPath_apply_of_lt_top hT, min_eq_right hs, hv]
    simp

/-- **Killed paths are nonnegative and absorbed at zero**: for each fixed positive starting
level `y`, a.s. under `P` the killed path starts at `y`, is `≥ 0`, positive before `T_y`
and is `0` from the passage time on.  (`y` is fixed BEFORE `∀ᵐ`: simultaneous strict
positivity over all levels is false, at passage-jump levels `X_{T_{y-}} = -y`.) -/
theorem ae_killedPath_spec {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (y : ℝ≥0) (hy : 0 < y) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc),
      (killedPath y f).1 0 = (y : ℝ) ∧ (∀ s, 0 ≤ (killedPath y f).1 s) ∧
      (∀ s : ℝ≥0, (s : WithTop ℝ≥0) < firstPassageBelow y f →
        0 < (killedPath y f).1 s) ∧
      ∀ s : ℝ≥0, firstPassageBelow y f ≤ (s : WithTop ℝ≥0) → (killedPath y f).1 s = 0 :=
  by
    filter_upwards [ae_firstPassageBelow_spec hθ,
      ae_firstHitBelow_eq_firstPassageBelow hθ y] with f hf hhit
    obtain ⟨hfin, _, hval⟩ := hf.2 y hy
    obtain ⟨hstart, hnonneg, hzero⟩ := killedPath_spec_of_creeping hf.1 hfin hval
    refine ⟨hstart, hnonneg, ?_, hzero⟩
    intro s hs
    obtain ⟨τ, hτ⟩ := WithTop.ne_top_iff_exists.mp hfin.ne
    have hsτ : s < τ := by simpa only [← hτ, WithTop.coe_lt_coe] using hs
    rw [killedPath_apply_of_lt_top hτ.symm, min_eq_left hsτ.le]
    have hnot : ¬ f.1 s ≤ -(y : ℝ) := by
      intro hle
      have hleHit : firstHitBelow y f ≤ (s : WithTop ℝ≥0) := sInf_le ⟨s, rfl, hle⟩
      rw [hhit] at hleHit
      exact hs.not_ge hleHit
    linarith

/-- **Simultaneous version** (start, nonnegativity, zero after strict passage; NO strict
pre-passage positivity, which fails simultaneously over levels). -/
theorem ae_killedPath_spec_simultaneous {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∀ y : ℝ≥0, 0 < y →
      (killedPath y f).1 0 = (y : ℝ) ∧ (∀ s, 0 ≤ (killedPath y f).1 s) ∧
      ∀ s : ℝ≥0, firstPassageBelow y f ≤ (s : WithTop ℝ≥0) → (killedPath y f).1 s = 0 :=
  by
    filter_upwards [ae_firstPassageBelow_spec hθ] with f hf y hy
    exact killedPath_spec_of_creeping hf.1 (hf.2 y hy).1 (hf.2 y hy).2.2

/-- `T_0 = 0` a.s.: sealed supplier is `ae_passageTime_eq_firstPassageBelow` (second clause
`passageTime 0 f = 0`, with `firstPassageBelow 0 f` its finite reading), itself from
`ae_strictPassage_zero_stableLocalLaw` (regularity, `StableRegularity.lean`). -/
theorem ae_firstPassageBelow_zero {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), firstPassageBelow 0 f = 0 := by
  filter_upwards [ae_passageTime_eq_firstPassageBelow hθ] with f hf
  rw [hf.1 0, hf.2]
  rfl

/-- **Zero is absorbing**: `K_0 = δ_{zeroLoc}` as measures (`T_0 = 0` a.s. by regularity of `(-∞,0)`
at `0`). -/
theorem killedStableKernel_zero {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    killedStableKernel θ 0 = Measure.dirac zeroLoc := by
  rw [killedStableKernel_apply]
  have heq : killedPath 0 =ᵐ[(stableLocalLaw θ : Measure DLoc)] fun _ => zeroLoc := by
    filter_upwards [ae_firstPassageBelow_zero hθ, ae_eval_zero_stableLocalLaw hθ]
      with f hT hf0
    apply Subtype.ext
    funext s
    simpa [zeroLoc, hf0] using killedPath_apply_of_lt_top hT s
  rw [Measure.map_congr heq, Measure.map_const]
  simp

/-! ### Supporting exports -/

/-- `valueNN` is measurable. -/
theorem measurable_excursion_valueNN (t : ℝ≥0) :
    Measurable (fun e : Excursion => e.valueNN t) :=
  (measurable_excursion_eval t).real_toNNReal

/-- `valueNN` is jointly measurable in `(e, t)`. -/
theorem measurable_excursion_valueNN_uncurry :
    Measurable (fun p : Excursion × ℝ≥0 => p.1.valueNN p.2) :=
  measurable_excursion_eval₂.real_toNNReal

/-- Real-value bridge: the carrier requires nonnegativity, so nothing is truncated. -/
theorem Excursion.coe_valueNN (e : Excursion) (t : ℝ≥0) :
    (e.valueNN t : ℝ) = e.path.1 t :=
  Real.coe_toNNReal _ (e.2.2.1 t)

/-- **Strict positivity of the value before death**: for `0 < t`, `N`-a.e. excursion alive
at age `t` has `e(t) > 0` (`ae_excursionMeasure_support`). -/
theorem ae_valueNN_pos {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (t : ℝ≥0) (ht : 0 < t) :
    ∀ᵐ e ∂((excursionMeasure θ).restrict {e : Excursion | t < e.lifetime}),
      0 < e.valueNN t := by
  have hsurv : MeasurableSet {e : Excursion | t < e.lifetime} :=
    measurableSet_lt measurable_const measurable_excursion_lifetime
  apply (ae_restrict_iff' hsurv).2
  filter_upwards [ae_excursionMeasure_support hθ] with e he htζ
  exact Real.toNNReal_pos.mpr (he.1 t ht htζ)

/-- The survival restriction of `N` is finite (`excursionMeasure_lifetime_slab_lt_top`);
σ-finiteness is `sigmaFinite_excursionMeasure`. -/
theorem isFiniteMeasure_excursionMeasure_survival {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (t : ℝ≥0)
    (ht : 0 < t) :
    IsFiniteMeasure ((excursionMeasure θ).restrict {e : Excursion | t < e.lifetime}) := by
  exact ⟨by simpa only [Measure.restrict_apply_univ] using
    excursionMeasure_lifetime_slab_lt_top hθ ht⟩

private lemma lastPositiveTime_eq_of_positive_before {g : DLoc} {τ : ℝ≥0}
    (hpos : ∀ s : ℝ≥0, 0 < s → s < τ → 0 < g.1 s)
    (hzero : ∀ s : ℝ≥0, τ ≤ s → g.1 s = 0) :
    lastPositiveTime g = (τ : WithTop ℝ≥0) := by
  apply le_antisymm
  · apply iSup_le
    intro s
    apply WithTop.coe_le_coe.mpr
    by_contra hn
    have hz := hzero s.1 (le_of_not_ge hn)
    exact (ne_of_gt s.2) hz
  · by_contra hn
    have hL : lastPositiveTime g < (τ : WithTop ℝ≥0) := lt_of_not_ge hn
    obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.mp (hL.trans (WithTop.coe_lt_top τ)).ne
    have haτ : a < τ := by simpa only [← ha, WithTop.coe_lt_coe] using hL
    obtain ⟨s, has, hsτ⟩ := exists_between haτ
    have hs : 0 < g.1 s := hpos s (lt_of_le_of_lt bot_le has) hsτ
    have hle : (s : WithTop ℝ≥0) ≤ lastPositiveTime g := le_iSup_of_le ⟨s, hs⟩ le_rfl
    rw [← ha, WithTop.coe_le_coe] at hle
    exact has.not_ge hle

/-- Remaining lifetime as a functional of the future: for `0 < t`, on `{t < ζ}` N-a.e.,
`lastPositiveTime (futureFrom t e) = ζ - t`. -/
theorem ae_lastPositiveTime_futureFrom {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (t : ℝ≥0) (ht : 0 < t) :
    ∀ᵐ e ∂((excursionMeasure θ).restrict {e : Excursion | t < e.lifetime}),
      lastPositiveTime (futureFrom t e) = ((e.lifetime - t : ℝ≥0) : WithTop ℝ≥0) := by
  have hsurv : MeasurableSet {e : Excursion | t < e.lifetime} :=
    measurableSet_lt measurable_const measurable_excursion_lifetime
  apply (ae_restrict_iff' hsurv).2
  filter_upwards [ae_excursionMeasure_support hθ] with e he htζ
  apply lastPositiveTime_eq_of_positive_before
  · intro s _hs hsζ
    rw [futureFrom_apply]
    exact he.1 (t + s) (lt_of_lt_of_le ht (le_add_of_nonneg_right (bot_le)))
      (by have := (lt_tsub_iff_right).1 hsζ; simpa only [add_comm] using this)
  · intro s hsζ
    rw [futureFrom_apply]
    apply e.2.2.2
    change (e.lifetime : ℝ) ≤ ((t + s : ℝ≥0) : ℝ)
    exact_mod_cast (show e.lifetime ≤ t + s by
      simpa only [add_comm] using (tsub_le_iff_right).1 hsζ)

/-- For each fixed `y > 0`, a.s. the last positive time of the killed path is the strict
passage time `T_y` (strict passage of the driving process, not of the killed path). -/
theorem ae_lastPositiveTime_killedPath {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (y : ℝ≥0) (hy : 0 < y) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc),
      lastPositiveTime (killedPath y f) = firstPassageBelow y f := by
  filter_upwards [ae_killedPath_spec hθ y hy, ae_firstPassageBelow_spec hθ] with f hf hT
  obtain ⟨τ, hτ⟩ := WithTop.ne_top_iff_exists.mp (hT.2 y hy).1.ne
  rw [← hτ]
  apply lastPositiveTime_eq_of_positive_before
  · intro s _hs hsτ
    exact hf.2.2.1 s (by rw [← hτ]; exact_mod_cast hsτ)
  · intro s hsτ
    exact hf.2.2.2 s (by rw [← hτ]; exact_mod_cast hsτ)

private lemma untopA_coe (s : ℝ≥0) : ((s : WithTop ℝ≥0).untopA) = s := by
  rw [WithTop.untopA_eq_untop WithTop.coe_ne_top]
  exact (WithTop.untop_eq_iff _).2 rfl

/-- The whole stopped path is measurable for the stopped sigma-algebra, everywhere,
including paths on which the stopping time is infinite. -/
theorem measurable_stopLocAt_stopped {τ : DLoc → WithTop ℝ≥0}
    (hτ : IsStoppingTime DLoc.filtration τ) :
    Measurable[hτ.measurableSpace] (fun f : DLoc => stopLocAt (τ f) f) := by
  apply @measurable_dLoc_of_eval DLoc hτ.measurableSpace (fun f => stopLocAt (τ f) f)
  intro s
  have hm := (DLoc.measurable_stoppedValue_eval (hτ.min_const s)).mono
    (IsStoppingTime.measurableSpace_mono (hτ.min_const s) hτ (fun _ => min_le_left _ _))
    le_rfl
  convert hm using 1
  funext f
  change (stopLocAt (τ f) f).1 s = f.1 ((min (τ f) (s : WithTop ℝ≥0)).untopA)
  induction h : τ f using WithTop.recTopCoe with
  | top => simp only [stopLocAt, min_top_left, untopA_coe]
  | coe a =>
    simp only [stopLocAt, stopLoc, ← WithTop.coe_min, untopA_coe, min_comm]

/-- The age-`t` prefix selected by a clock `τ`, computed from the path stopped at `τ`. It is
defined on all paths and agrees with the excursion prefix `excursionRestrict t` on the cut
(`selectedAgePrefix_eq_excursionRestrict`). -/
noncomputable def selectedAgePrefix (t : ℝ≥0) (τ : DLoc → WithTop ℝ≥0) (f : DLoc) :
    D (t : ℝ) ℝ :=
  DLoc.restrict t (DLoc.shift ((τ f).untopD 0 - t) (stopLocAt (τ f) f))

/-- The selected prefix is measurable in the stopped sigma-algebra. -/
theorem measurable_selectedAgePrefix (t : ℝ≥0) {τ : DLoc → WithTop ℝ≥0}
    (hτ : IsStoppingTime DLoc.filtration τ) :
    Measurable[hτ.measurableSpace] (selectedAgePrefix t τ) := by
  exact (DLoc.measurable_restrict t).comp
    (DLoc.measurable_shift.comp (((hτ.measurable.untopD 0).sub measurable_const).prodMk
      (measurable_stopLocAt_stopped hτ)))

/-- At an age crossing inside a valid excursion cut, the selected stopped-path prefix is
exactly the excursion prefix. -/
theorem selectedAgePrefix_eq_excursionRestrict {t g d : ℝ≥0}
    {τ : DLoc → WithTop ℝ≥0} {f : DLoc} (hτ : τ f = ((g + t : ℝ≥0) : WithTop ℝ≥0))
    (hv : cutValid g d f) (htd : g + t < d) :
    selectedAgePrefix t τ f = excursionRestrict t (excursionCut g d f) := by
  apply BGW.Skorokhod.ext
  intro s
  let u : ℝ≥0 := ⟨s.1, s.2.1⟩
  have hut : u ≤ t := by exact_mod_cast s.2.2
  have hgu : g + u ≤ g + t := add_le_add le_rfl hut
  change (DLoc.shift ((τ f).untopD 0 - t) (stopLocAt (τ f) f)).1 u =
    (excursionCut g d f).path.1 u
  rw [excursionCut_eval hv]
  simp only [hτ, WithTop.untopD_coe, add_tsub_cancel_right, DLoc.shift, stopLocAt, stopLoc]
  rw [min_eq_left hgu, min_eq_left (le_add_of_nonneg_right (bot_le : (0 : ℝ≥0) ≤ t)),
    min_eq_left (hgu.trans htd.le)]

/-- Strong Markov as a product law with an arbitrary stopped-measurable past observable,
on a past event contained in the finite-stopping event. -/
private theorem map_past_shiftAt_restrict {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    {α : Type*} [MeasurableSpace α] {τ : DLoc → WithTop ℝ≥0}
    (hτ : IsStoppingTime DLoc.filtration τ) {A : Set DLoc}
    (hA : MeasurableSet[hτ.measurableSpace] A) (hAτ : A ⊆ {f | τ f < ⊤})
    {Z : DLoc → α} (hZ : Measurable[hτ.measurableSpace] Z) :
    ((stableLocalLaw θ : Measure DLoc).restrict A).map
        (fun f => (Z f, DLoc.shiftAt τ f)) =
      (((stableLocalLaw θ : Measure DLoc).restrict A).map Z).prod
        (stableLocalLaw θ : Measure DLoc) := by
  have hZ0 := hZ.mono hτ.measurableSpace_le le_rfl
  have hshift := DLoc.measurable_shiftAt hτ
  apply Measure.ext_prod
  intro U V hU hV
  rw [Measure.map_apply (hZ0.prodMk hshift) (hU.prod hV),
    Measure.restrict_apply ((hZ0.prodMk hshift) (hU.prod hV)),
    Measure.prod_prod, Measure.map_apply hZ0 hU, Measure.restrict_apply (hZ0 hU)]
  have heq : ((fun f => (Z f, DLoc.shiftAt τ f)) ⁻¹' (U ×ˢ V)) ∩ A =
      (A ∩ Z ⁻¹' U) ∩ DLoc.shiftAt τ ⁻¹' V := by
    ext f
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_prod]
    tauto
  rw [heq, Set.inter_comm (Z ⁻¹' U) A]
  exact measure_inter_preimage_shiftAt hθ hτ (hA.inter (hZ hU))
    (fun f hf => hAτ hf.1) hV

/-- Nonnegative state-dependent strong Markov integration, with the entire stopped past
allowed as the state variable. -/
theorem lintegral_past_shiftAt {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    {α : Type*} [MeasurableSpace α] {τ : DLoc → WithTop ℝ≥0}
    (hτ : IsStoppingTime DLoc.filtration τ) {A : Set DLoc}
    (hA : MeasurableSet[hτ.measurableSpace] A) (hAτ : A ⊆ {f | τ f < ⊤})
    {Z : DLoc → α} (hZ : Measurable[hτ.measurableSpace] Z)
    {H : α × DLoc → ℝ≥0∞} (hH : Measurable H) :
    (∫⁻ f in A, H (Z f, DLoc.shiftAt τ f) ∂(stableLocalLaw θ : Measure DLoc)) =
      ∫⁻ f in A, ∫⁻ g, H (Z f, g) ∂(stableLocalLaw θ : Measure DLoc)
        ∂(stableLocalLaw θ : Measure DLoc) := by
  have hZ0 := hZ.mono hτ.measurableSpace_le le_rfl
  rw [← lintegral_map hH (hZ0.prodMk (DLoc.measurable_shiftAt hτ)),
    map_past_shiftAt_restrict hθ hτ hA hAτ hZ,
    lintegral_prod _ hH.aemeasurable,
    lintegral_map (Measurable.lintegral_prod_right (f := fun x g => H (x, g)) hH) hZ0]

/-- Translating a strict passage time after a deterministic time before passage. The new
starting level is the old height above the barrier; no probabilistic modification is used. -/
private theorem firstPassageBelow_shift_before {f : DLoc} {x y a d : ℝ≥0}
    (hT : firstPassageBelow x f = (d : WithTop ℝ≥0)) (had : a < d)
    (hy : (y : ℝ) = f.1 a + (x : ℝ)) :
    firstPassageBelow y (DLoc.shift a f) = ((d - a : ℝ≥0) : WithTop ℝ≥0) := by
  apply le_antisymm
  · apply le_of_forall_gt_imp_ge_of_dense
    intro r hr
    induction r using WithTop.recTopCoe with
    | top => exact le_top
    | coe r =>
      have hdr : d - a < r := WithTop.coe_lt_coe.mp hr
      have hdar : d < a + r := by
        rw [← add_tsub_cancel_of_le had.le]
        exact add_lt_add_of_le_of_lt le_rfl hdr
      obtain ⟨u, huar, hu⟩ := exists_eval_lt_of_firstPassageBelow_lt (x := x)
        (by rw [hT]; exact_mod_cast hdar)
      have hdu : d ≤ u := by
        have hle := firstPassageBelow_le_of_eval_lt hu
        simpa only [hT, WithTop.coe_le_coe] using hle
      have hus : u - a < r := by
        rw [tsub_lt_iff_right (had.le.trans hdu)]
        simpa only [add_comm] using huar
      have hshift : (DLoc.shift a f).1 (u - a) < -(y : ℝ) := by
        change f.1 (a + (u - a)) - f.1 a < -(y : ℝ)
        rw [add_tsub_cancel_of_le (had.le.trans hdu), hy]
        linarith
      exact (firstPassageBelow_le_of_eval_lt hshift).trans
        (WithTop.coe_le_coe.mpr hus.le)
  · apply le_iInf
    intro s
    apply le_iInf
    intro hs
    have hval : f.1 (a + s) < -(x : ℝ) := by
      change f.1 (a + s) - f.1 a < -(y : ℝ) at hs
      rw [hy] at hs
      linarith
    have hle := firstPassageBelow_le_of_eval_lt hval
    rw [hT, WithTop.coe_le_coe] at hle
    apply WithTop.coe_le_coe.mpr
    exact tsub_le_iff_right.mpr (by simpa only [add_comm] using hle)

/-- The uncentred future of a valid excursion cut is the killed shifted driving path,
when the right endpoint is the strict passage below its starting infimum. -/
theorem futureFrom_excursionCut_eq_killedPath {t g d x : ℝ≥0} {f : DLoc}
    (hv : cutValid g d f) (hT : firstPassageBelow x f = (d : WithTop ℝ≥0))
    (hg : f.1 g = -(x : ℝ)) (htd : g + t < d) :
    futureFrom t (excursionCut g d f) =
      killedPath ((excursionCut g d f).valueNN t) (DLoc.shift (g + t) f) := by
  have hy : (((excursionCut g d f).valueNN t : ℝ≥0) : ℝ) = f.1 (g + t) + (x : ℝ) := by
    rw [Excursion.coe_valueNN, excursionCut_eval hv, min_eq_left htd.le, hg]
    ring
  have hshift := firstPassageBelow_shift_before hT htd hy
  apply Subtype.ext
  funext s
  rw [futureFrom_apply, excursionCut_eval hv, killedPath_apply_of_lt_top hshift]
  change f.1 (min (g + (t + s)) d) - f.1 g =
    (((excursionCut g d f).valueNN t : ℝ≥0) : ℝ) +
      (f.1 ((g + t) + min s (d - (g + t))) - f.1 (g + t))
  rw [add_min, add_tsub_cancel_of_le htd.le, hy, hg, add_assoc, ← add_assoc g t s]
  ring

end BGW.StableTrees
