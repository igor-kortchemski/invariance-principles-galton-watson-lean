/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.StableExcursionSupportOccupation
import Mathlib.Topology.Bases

/-!
# Excursion support of the reflected stable process

The positive set is exactly the union of the passage-jump intervals, simultaneously on
one full-probability event. Their starts are continuous, their endpoints identify every
excursion candidate, and their complement has zero Lebesgue measure (J. Bertoin, *Lévy Processes*,
Cambridge University Press, 1996, Chapter VII).
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees

/-- **Window minima from plateau inequalities** (no uniqueness needed).  Simultaneously for
every jump level `x`: `X` has left limit `-x` at `T_{x-}`, `T_{x-} > 0`, and over every rational
window `r < T_{x-} < q < T_x` the infimum of `X` is `-x`. -/
theorem ae_jump_window_inf {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∀ x ∈ passageJumpSet f,
      0 < passageTimeMinus x f ∧ Function.leftLim f.1 (passageTimeMinus x f) = -(x : ℝ) ∧
        ∀ r q : ℚ≥0, (r : ℝ≥0) < passageTimeMinus x f → passageTimeMinus x f < (q : ℝ≥0) →
          (q : ℝ≥0) < passageTime x f →
            (⨅ u : Set.Icc (r : ℝ≥0) (q : ℝ≥0), f.1 u) = -(x : ℝ) := by
  filter_upwards [ae_passageTime_eq_firstPassageBelow hθ, ae_creeping_passageTime hθ]
    with f hT hc
  intro x hx
  obtain ⟨hg, hl⟩ := leftLim_at_passageTimeMinus hT.1 hc hx.1
  exact ⟨hg, hl, fun _ _ hrg hgq hqd =>
    iInf_window_passageTimeMinus hT.1 hc hx.1 hrg hgq hqd⟩

/-- **Distinct jump levels give disjoint intervals and distinct starts.** -/
theorem ae_jump_intervals_disjoint {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∀ x ∈ passageJumpSet f, ∀ y ∈ passageJumpSet f,
      x < y → passageTime x f < passageTimeMinus y f := by
  filter_upwards [ae_passageTime_eq_firstPassageBelow hθ, ae_creeping_passageTime hθ]
    with f hT hc
  intro x _hx y _hy hxy
  exact passageTime_lt_passageTimeMinus hT.1 (strictMono_passageTime_of_creeping hT.1 hc) hxy

/-- **Jump levels are countable** (monotone càdlàg `T`). -/
theorem ae_passageJumpSet_countable {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), (passageJumpSet f).Countable := by
  filter_upwards [ae_jump_intervals_disjoint hθ] with f hd
  have hp : (passageJumpSet f).PairwiseDisjoint
      (fun x => Set.Ioo (passageTimeMinus x f) (passageTime x f)) := by
    intro x hx y hy hne
    rcases lt_or_gt_of_ne hne with hxy | hyx
    · exact Set.disjoint_left.mpr fun t ht ht' =>
        (ht.2.trans (hd x hx y hy hxy)).not_gt ht'.1
    · exact Set.disjoint_left.mpr fun t ht ht' =>
        (ht'.2.trans (hd y hy x hx hyx)).not_gt ht.1
  exact hp.countable_of_isOpen (fun _ _ => isOpen_Ioo) (fun _ hx => nonempty_Ioo.mpr hx.2)

/-- **No jump start**: a.s., at every jump level the path is continuous at `T_{x-}`,
takes the value `-x` there, and `R (T_{x-}) = 0`. -/
theorem ae_continuousAt_jumpStart {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∀ x ∈ passageJumpSet f,
      ContinuousAt f.1 (passageTimeMinus x f) ∧ f.1 (passageTimeMinus x f) = -(x : ℝ) ∧
        (reflectedFrom 0 f).1 (passageTimeMinus x f) = 0 := by
  filter_upwards [ae_jump_window_inf hθ, ae_rationalWindowMinima hθ,
    ae_leftLim_le_stableLocalLaw hθ, ae_passageTime_eq_firstPassageBelow hθ,
    ae_localTime_passageTime hθ, ae_eval_zero_stableLocalLaw hθ] with f hw hm hn hT hL h0
  intro x hx
  obtain ⟨hg, hl, _⟩ := hw x hx
  obtain ⟨r, q, hrg, hgq, hqd⟩ := exists_supportWindow hg hx.2
  have hb (u : ℝ≥0) (hu : u ≤ (q : ℝ≥0)) : -(x : ℝ) ≤ f.1 u := by
    apply le_eval_of_lt_strictPassageBelow
    change (u : WithTop ℝ≥0) < firstPassageBelow x f
    rw [hT.1 x]
    exact_mod_cast hu.trans_lt hqd
  have hgen := isGenMinimizer_supportWindow hn hrg hgq hl hb
  have hc := (hm r q (hrg.trans hgq) _ hgen).1
  have hc' := continuousAt_of_supportWindow hrg hgq hc
  have he : f.1 (passageTimeMinus x f) = -(x : ℝ) :=
    hc'.continuousWithinAt.leftLim_eq.symm.trans hl
  refine ⟨hc', he, ?_⟩
  rw [reflectedFrom_zero_apply h0, he]
  have hI := (hL x).2
  change -runningInfLoc f (passageTimeMinus x f) = (x : ℝ) at hI
  linarith

private theorem runningInf_eq_on_passage_interval {f : DLoc}
    (hL : ∀ x : ℝ≥0, localTime f (passageTime x f) = x ∧
      localTime f (passageTimeMinus x f) = x)
    {x t : ℝ≥0} (hgt : passageTimeMinus x f ≤ t) (htd : t ≤ passageTime x f) :
    runningInfLoc f t = -(x : ℝ) := by
  have hlow := runningInfLoc_antitone f htd
  have hupp := runningInfLoc_antitone f hgt
  have hLg := (hL x).2
  have hLd := (hL x).1
  dsimp [localTime] at hLg hLd
  linarith

/-- **Simultaneous excursion-candidate supplier.**  A.s., for every
positive jump label `x` simultaneously, `g = T_{x-} > 0`, `d = T_x`, `L_g = L_d = x` and `(g,d)`
is an `IsExcursionCandidate`; strict interior positivity of `R` comes from uniqueness of the
minimum on rational windows. -/
theorem ae_isExcursionCandidate_of_jump {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∀ x ∈ passageJumpSet f,
      0 < passageTimeMinus x f ∧ localTime f (passageTimeMinus x f) = x ∧
        localTime f (passageTime x f) = x ∧
          IsExcursionCandidate f (passageTimeMinus x f) (passageTime x f) := by
  filter_upwards [ae_continuousAt_jumpStart hθ, ae_jump_window_inf hθ,
    ae_rationalWindowMinima hθ, ae_leftLim_le_stableLocalLaw hθ,
    ae_passageTime_eq_firstPassageBelow hθ, ae_localTime_passageTime hθ,
    ae_eval_zero_stableLocalLaw hθ, ae_creeping_passageTime hθ]
    with f hc hw hm hn hT hL h0 hcreep
  intro x hx
  have hg := (hw x hx).1
  have hstart := hc x hx
  have hend : (reflectedFrom 0 f).1 (passageTime x f) = 0 := by
    rw [reflectedFrom_zero_apply h0, hcreep x]
    have := (hL x).1
    dsimp [localTime] at this
    linarith
  refine ⟨hg, (hL x).2, (hL x).1, hx.2, ?_,
    leftLim_reflectedFrom_eq_zero_of_noNegJumps hn hstart.2.2, hend⟩
  intro t hgt htd
  by_contra hp
  have hz : (reflectedFrom 0 f).1 t = 0 :=
    le_antisymm (le_of_not_gt hp) (reflectedFrom_nonneg 0 f t)
  have hIt := runningInf_eq_on_passage_interval hL hgt.le htd.le
  have htval : f.1 t = -(x : ℝ) := by
    rw [reflectedFrom_zero_apply h0, hIt] at hz
    linarith
  obtain ⟨_r, q, _hrt, htq, hqd⟩ := exists_supportWindow (hg.trans hgt) htd
  obtain ⟨r', _q', hrg, _hgq', _⟩ := exists_supportWindow hg hx.2
  -- Use a window starting before the first contact and ending after the alleged second one.
  have hgq : passageTimeMinus x f < (q : ℝ≥0) := hgt.trans htq
  have hb (u : ℝ≥0) (hu : u ≤ (q : ℝ≥0)) : -(x : ℝ) ≤ f.1 u := by
    apply le_eval_of_lt_strictPassageBelow
    change (u : WithTop ℝ≥0) < firstPassageBelow x f
    rw [hT.1 x]
    exact_mod_cast hu.trans_lt hqd
  have hleft : Function.leftLim f.1 t = -(x : ℝ) := by
    apply le_antisymm ((hn t).trans_eq htval)
    let _ : (𝓝[<] t).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, hg.trans hgt⟩
    apply ge_of_tendsto (f.2.tendsto_nhdsLT_leftLim t)
    filter_upwards [self_mem_nhdsWithin] with u hu
    exact hb u (hu.le.trans htq.le)
  have hgenG := isGenMinimizer_supportWindow hn hrg hgq (hw x hx).2.1 hb
  have hgenT := isGenMinimizer_supportWindow hn (hrg.trans hgt) htq hleft hb
  have heq := (hm r' q (hrg.trans hgq) _ hgenG).2 _ hgenT
  have heq' := congrArg Subtype.val heq
  dsimp [shiftedWindowTime] at heq'
  have : (t : ℝ) = passageTimeMinus x f := by linarith
  exact hgt.ne (NNReal.coe_injective this).symm

/-- **Excursion intervals from jump levels.**  The previous statement with the stronger
`IsExcursionInterval`
(continuous start, `R(T_{x-}) = 0`, via minimum continuity on rational windows). -/
theorem ae_isExcursionInterval_of_jump {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∀ x ∈ passageJumpSet f,
      IsExcursionInterval f (passageTimeMinus x f) (passageTime x f) := by
  filter_upwards [ae_isExcursionCandidate_of_jump hθ, ae_continuousAt_jumpStart hθ] with f hi hc
  intro x hx
  exact isExcursionInterval_of_isExcursionCandidate (hi x hx).2.2.2 (hc x hx).2.2

private theorem candidate_start_pos {f : DLoc} (hn : NoNegJumps f) (h0 : f.1 0 = 0)
    (hI0 : runningInfLoc f 0 = 0) (hr : DLoc.RegularBelowAtZero f)
    {g d : ℝ≥0} (hc : IsExcursionCandidate f g d) : 0 < g := by
  by_contra hng
  have hg : g = 0 := le_antisymm (le_of_not_gt hng) g.2
  subst g
  have hR0 : (reflectedFrom 0 f).1 0 = 0 := by
    rw [reflectedFrom_zero_apply h0, h0, hI0, sub_self]
  have hi := isExcursionInterval_of_isExcursionCandidate hc hR0
  obtain ⟨t, ht, htd, hneg⟩ := hr d hc.1
  have hIt := runningInfLoc_const_of_isExcursionInterval hn h0 hi ht.le htd.le
  have hle := runningInfLoc_le_eval f t ⟨t, le_rfl⟩
  rw [hIt, hI0] at hle
  exact (not_lt_of_ge hle) hneg

/-- **No jump starts, a.s.**: every excursion candidate is an excursion interval (`R g = 0`). -/
theorem ae_isExcursionInterval_of_isExcursionCandidate {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∀ g d : ℝ≥0, IsExcursionCandidate f g d →
      IsExcursionInterval f g d := by
  filter_upwards [ae_rationalWindowMinima hθ, ae_leftLim_le_stableLocalLaw hθ,
    ae_eval_zero_stableLocalLaw hθ, ae_localTime_spec hθ,
    ae_regularBelowAtZero_stableLocalLaw hθ] with f hm hn h0 hL hr
  have hI0 : runningInfLoc f 0 = 0 := neg_eq_zero.mp hL.1
  intro g d hc
  have hg := candidate_start_pos hn h0 hI0 hr hc
  obtain ⟨r, q, hrg, hgq, hqd⟩ := exists_supportWindow hg hc.1
  have hgen := isGenMinimizer_shift_restrict_of_isExcursionCandidate hn h0 hc hrg hgq hqd
  have hcont := continuousAt_of_supportWindow hrg hgq (hm r q (hrg.trans hgq) _ hgen).1
  have hcR : ContinuousAt (reflectedFrom 0 f).1 g := by
    have hI : ContinuousAt (runningInfLoc f) g := (runningInfLoc_continuous hn).continuousAt
    have hmin : ContinuousAt (fun t => min (0 : ℝ) (runningInfLoc f t)) g :=
      (show ContinuousAt (fun _ : ℝ≥0 => (0 : ℝ)) g from continuousAt_const).min hI
    simpa only [reflectedFrom, NNReal.coe_zero, zero_add, Pi.sub_def] using hcont.sub hmin
  have hRg : (reflectedFrom 0 f).1 g = 0 :=
    hcR.continuousWithinAt.leftLim_eq.symm.trans hc.2.2.1
  exact isExcursionInterval_of_isExcursionCandidate hc hRg

/-- **Converse for candidates.**  A.s., every excursion candidate `(g,d)` of the reflected path is
`(T_{x-}, T_x)` for the unique level `x = L_g > 0`, which is a jump level; in particular `0 < g`
(no candidate starts at `0`). -/
theorem ae_exists_jump_of_isExcursionCandidate {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∀ g d : ℝ≥0, IsExcursionCandidate f g d →
      ∃ x ∈ passageJumpSet f, g = passageTimeMinus x f ∧ d = passageTime x f ∧
        x = localTime f g := by
  filter_upwards [ae_isExcursionInterval_of_isExcursionCandidate hθ,
    ae_isExcursionInterval_of_jump hθ, ae_passageTimeMinus_le_le_firstPassageBelow hθ,
    ae_passageTime_eq_firstPassageBelow hθ, ae_leftLim_le_stableLocalLaw hθ,
    ae_eval_zero_stableLocalLaw hθ, ae_localTime_spec hθ,
    ae_regularBelowAtZero_stableLocalLaw hθ] with f hi hj hs hT hn h0 hL hr
  have hI0 : runningInfLoc f 0 = 0 := neg_eq_zero.mp hL.1
  intro g d hc
  have hgi := hi g d hc
  have hg := candidate_start_pos hn h0 hI0 hr hc
  obtain ⟨u, _hu, hug, hneg⟩ := hr g hg
  have hIg : runningInfLoc f g < 0 :=
    (runningInfLoc_le_eval f g ⟨u, hug.le⟩).trans_lt hneg
  let x := localTimeNN f g
  have hxcoe : (x : ℝ) = localTime f g := Real.coe_toNNReal _ (neg_nonneg.mpr hIg.le)
  have hxpos : 0 < x := by
    rw [← NNReal.coe_pos, hxcoe]
    exact neg_pos.mpr hIg
  have hIgId := runningInfLoc_const_of_isExcursionInterval hn h0 hgi hc.1.le le_rfl
  have hxd : localTimeNN f d = x := by
    dsimp [localTimeNN, localTime, x]
    rw [hIgId]
  have hGg : passageTimeMinus x f ≤ g := (hs g).1
  have hdD : d ≤ passageTime x f := by
    have h := (hs d).2
    rw [hxd, hT.1 x] at h
    exact_mod_cast h
  have hxjump : x ∈ passageJumpSet f := ⟨hxpos, hGg.trans_lt (hc.1.trans_le hdD)⟩
  have hxi := hj x hxjump
  have hgG : g = passageTimeMinus x f := by
    apply le_antisymm _ hGg
    by_contra hnot
    have hGg' : passageTimeMinus x f < g := lt_of_not_ge hnot
    exact (ne_of_gt (hxi.2.1 g hGg' (hc.1.trans_le hdD))) hgi.2.2.2.1
  -- A zero at d strictly before T_x would be an interior zero of the full jump interval.
  -- Its strict positivity was proved above on one event for all jump levels.
  have hdD' : d = passageTime x f := by
    apply le_antisymm hdD
    by_contra hnot
    have hdD' : d < passageTime x f := lt_of_not_ge hnot
    exact (ne_of_gt (hxi.2.1 d (hGg.trans_lt hc.1) hdD')) hc.2.2.2
  exact ⟨x, hxjump, hgG, hdD', hxcoe⟩

/-- **Characterization of excursion intervals (iff).** -/
theorem ae_isExcursionInterval_iff {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∀ g d : ℝ≥0, IsExcursionInterval f g d ↔
      ∃ x ∈ passageJumpSet f, g = passageTimeMinus x f ∧ d = passageTime x f := by
  filter_upwards [ae_exists_jump_of_isExcursionCandidate hθ, ae_isExcursionInterval_of_jump hθ]
    with f hc hj
  intro g d
  constructor
  · intro h
    obtain ⟨x, hx, hg, hd, _⟩ := hc g d h.isExcursionCandidate
    exact ⟨x, hx, hg, hd⟩
  · rintro ⟨x, hx, rfl, rfl⟩
    exact hj x hx

/-- **Characterization of excursion candidates (iff).** -/
theorem ae_isExcursionCandidate_iff {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∀ g d : ℝ≥0, IsExcursionCandidate f g d ↔
      ∃ x ∈ passageJumpSet f, g = passageTimeMinus x f ∧ d = passageTime x f := by
  filter_upwards [ae_exists_jump_of_isExcursionCandidate hθ, ae_isExcursionCandidate_of_jump hθ]
    with f hc hj
  intro g d
  constructor
  · intro h
    obtain ⟨x, hx, hg, hd, _⟩ := hc g d h
    exact ⟨x, hx, hg, hd⟩
  · rintro ⟨x, hx, rfl, rfl⟩
    exact (hj x hx).2.2.2

/-- **The reflected process is positive exactly on the union of the excursion intervals**
(a.s., an equality of sets, not merely up to a null set): `{R > 0} = ⋃_{x ∈ jump levels}
(T_{x-}, T_x)`; equivalently `R` vanishes off the union, and the zero set is the Lebesgue-null
complement of `ae_zeroSet_volume_zero`. -/
theorem ae_pos_set_eq_iUnion_jump_intervals {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc),
      {t : ℝ≥0 | 0 < (reflectedFrom 0 f).1 t} =
        ⋃ x ∈ passageJumpSet f, Set.Ioo (passageTimeMinus x f) (passageTime x f) := by
  filter_upwards [ae_isExcursionInterval_of_jump hθ,
    ae_passageTimeMinus_le_le_firstPassageBelow hθ,
    ae_passageTime_eq_firstPassageBelow hθ, ae_creeping_passageTime hθ,
    ae_localTime_passageTime hθ, ae_eval_zero_stableLocalLaw hθ] with f hi hs hT hc hL h0
  ext t
  constructor
  · intro ht
    let x := localTimeNN f t
    have hgt : passageTimeMinus x f ≤ t := (hs t).1
    have htd : t ≤ passageTime x f := by
      have h := (hs t).2
      rw [hT.1 x] at h
      exact_mod_cast h
    have hRd : (reflectedFrom 0 f).1 (passageTime x f) = 0 := by
      rw [reflectedFrom_zero_apply h0, hc x]
      have h := (hL x).1
      dsimp [localTime] at h
      linarith
    have htd' : t < passageTime x f := lt_of_le_of_ne htd (by
      intro heq
      exact (ne_of_gt ht) (heq ▸ hRd))
    have hxpos : 0 < x := by
      by_contra hnot
      have hx : x = 0 := le_antisymm (le_of_not_gt hnot) x.2
      rw [hx, hT.2] at htd'
      exact (not_lt_of_ge t.2) htd'
    have hxjump : x ∈ passageJumpSet f := ⟨hxpos, hgt.trans_lt htd'⟩
    have hgt' : passageTimeMinus x f < t := lt_of_le_of_ne hgt (by
      intro heq
      exact (ne_of_gt ht) (heq ▸ (hi x hxjump).2.2.2.1))
    exact Set.mem_iUnion.mpr ⟨x, Set.mem_iUnion.mpr ⟨hxjump, hgt', htd'⟩⟩
  · intro ht
    obtain ⟨x, hx, hxt⟩ := Set.mem_iUnion₂.mp ht
    exact (hi x hx).2.1 t hxt.1 hxt.2

/-- **Lebesgue-almost every time lies in an excursion interval** (consequence of the two
previous statements). -/
theorem ae_volume_compl_iUnion_jump_intervals {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc),
      (volume : Measure ℝ) (((↑) : ℝ≥0 → ℝ) ''
        (⋃ x ∈ passageJumpSet f, Set.Ioo (passageTimeMinus x f) (passageTime x f))ᶜ) = 0 := by
  filter_upwards [ae_zeroSet_volume_zero hθ, ae_pos_set_eq_iUnion_jump_intervals hθ]
    with f hz hp
  rw [← hp]
  have heq : {t : ℝ≥0 | 0 < (reflectedFrom 0 f).1 t}ᶜ =
      {t : ℝ≥0 | (reflectedFrom 0 f).1 t = 0} := by
    ext t
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_lt]
    exact ⟨fun h => le_antisymm h (reflectedFrom_nonneg 0 f t), fun h => h.le⟩
  rwa [heq]

end BGW.StableTrees
