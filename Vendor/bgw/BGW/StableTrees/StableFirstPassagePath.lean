/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.Skorokhod.DLoc

/-!
# Pathwise first-passage facts for local càdlàg paths

This module contains the deterministic crossing estimates for the strict passage below a level,
the running infimum API, and joint measurability of the level/path passage times.
-/

@[expose] public section

open scoped NNReal ENNReal Topology
open Filter Set MeasureTheory

namespace BGW.StableTrees
open BGW.Skorokhod

/-- Before the strict first passage, the path is not below the barrier. -/
lemma le_eval_of_lt_strictPassageBelow {f : DLoc} {a : ℝ} {s : ℝ≥0}
    (hs : (s : WithTop ℝ≥0) < DLoc.strictPassageBelow a f) :
    a ≤ f.1 s := by
  by_contra h
  have hlt : f.1 s < a := lt_of_not_ge h
  exact (not_lt_of_ge (iInf_le_of_le s (iInf_le _ hlt))) hs

private lemma not_below_of_le_passage {f : DLoc} {a : ℝ} {s : ℝ≥0}
    (hs : (s : WithTop ℝ≥0) < DLoc.strictPassageBelow a f) :
    ¬ f.1 s < a := by
  intro h
  exact (not_lt_of_ge (iInf_le_of_le s (iInf_le _ h))) hs

private lemma exists_time_below_of_passage_lt {f : DLoc} {a : ℝ} {s : ℝ≥0}
    (hs : DLoc.strictPassageBelow a f < (s : WithTop ℝ≥0)) :
    ∃ u : ℝ≥0, f.1 u < a ∧ u < s := by
  simpa only [DLoc.strictPassageBelow, iInf_lt_iff, WithTop.coe_lt_coe, exists_prop]
    using hs

private lemma eval_le_of_passage_eq {f : DLoc} {a : ℝ} {t : ℝ≥0}
    (hT : DLoc.strictPassageBelow a f = (t : WithTop ℝ≥0)) : f.1 t ≤ a := by
  by_contra h
  have ha : a < f.1 t := lt_of_not_ge h
  have he : ∀ᶠ s in 𝓝[Set.Ioi t] t, a < f.1 s :=
    (f.2.isRightContinuous t).eventually (isOpen_Ioi.mem_nhds ha)
  have hSet : {u : ℝ≥0 | a < f.1 u} ∈ 𝓝[Set.Ioi t] t := he
  rw [(nhdsGT_basis t).mem_iff] at hSet
  obtain ⟨b, htb, hb⟩ := hSet
  clear he
  obtain ⟨u, hua, hub⟩ := exists_time_below_of_passage_lt (a := a) (f := f)
    (show DLoc.strictPassageBelow a f < (b : WithTop ℝ≥0) by rw [hT]; exact_mod_cast htb)
  rcases lt_or_ge u t with hut | htu
  · exact (not_lt_of_ge
      (le_eval_of_lt_strictPassageBelow (a := a) (by rw [hT]; exact_mod_cast hut))) hua
  · rcases htu.eq_or_lt with hut | htu
    · subst u
      exact (not_le_of_gt ha) (le_of_lt hua)
    · exact (not_lt_of_ge (le_of_lt (hb ⟨htu, hub⟩))) hua

/-- Passage below a level strictly below the initial value is positive. -/
lemma strictPassageBelow_pos_of_lt_eval_zero {f : DLoc} {a : ℝ} (h0 : a < f.1 0) :
    0 < DLoc.strictPassageBelow a f := by
  rw [pos_iff_ne_zero]
  intro h
  have he := eval_le_of_passage_eq (f := f) (a := a) (t := 0) h
  exact (not_le_of_gt h0) he

private lemma le_leftLim_of_passage_eq {f : DLoc} {a : ℝ} {t : ℝ≥0}
    (hT : DLoc.strictPassageBelow a f = (t : WithTop ℝ≥0))
    (h0 : a ≤ f.1 0) : a ≤ Function.leftLim f.1 t := by
  by_cases ht : t = 0
  · subst t
    rw [leftLim_eq_of_isBot isBot_zero]
    exact h0
  have : (𝓝[Set.Iio t] t).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, pos_iff_ne_zero.mpr ht⟩
  have hle : ∀ᶠ s in 𝓝[Set.Iio t] t, a ≤ f.1 s := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    apply le_eval_of_lt_strictPassageBelow (a := a)
    rw [hT]
    exact_mod_cast hs
  exact ge_of_tendsto (f.2.tendsto_nhdsLT_leftLim t) hle

/-- At a finite strict passage time, the no-negative-jumps property forces creeping. -/
lemma eval_eq_of_strictPassageBelow_eq_coe {f : DLoc} {a : ℝ} {t : ℝ≥0}
    (hf : ∀ s : ℝ≥0, Function.leftLim f.1 s ≤ f.1 s)
    (hT : DLoc.strictPassageBelow a f = (t : WithTop ℝ≥0)) (h0 : a < f.1 0) :
    f.1 t = a := by
  exact le_antisymm (eval_le_of_passage_eq hT) ((le_leftLim_of_passage_eq hT h0.le).trans (hf t))

/-- The running infimum `I_t = inf_{u ≤ t} X_u` of a local path. -/
noncomputable def runningInfLoc (f : DLoc) (t : ℝ≥0) : ℝ := ⨅ u : Set.Iic t, f.1 u

private lemma runningInf_bddBelow (f : DLoc) (t : ℝ≥0) :
    BddBelow (Set.range (fun u : Set.Iic t => f.1 u)) := by
  let T : ℝ≥0 := t + 1
  have hb := (isBounded_range (DLoc.restrict T f)).bddBelow
  apply hb.mono
  rintro y ⟨u, rfl⟩
  have huT : ((u : ℝ≥0) : ℝ) ≤ (T : ℝ) := by
    exact_mod_cast u.2.trans (show t ≤ T by simp [T])
  exact ⟨⟨(u : ℝ), u.1.2, huT⟩, rfl⟩

private lemma runningInf_le_eval (f : DLoc) (t : ℝ≥0) (u : Set.Iic t) :
    runningInfLoc f t ≤ f.1 u := ciInf_le (runningInf_bddBelow f t) u

private lemma le_runningInf (f : DLoc) (t : ℝ≥0) (a : ℝ)
    (h : ∀ u : Set.Iic t, a ≤ f.1 u) : a ≤ runningInfLoc f t := le_ciInf h

/-- The running infimum is antitone. -/
lemma runningInfLoc_antitone (f : DLoc) : Antitone (runningInfLoc f) := by
  intro s t hst
  apply le_runningInf
  intro u
  exact runningInf_le_eval f t ⟨u, u.2.trans hst⟩

/-- A path with no negative jumps has a continuous running infimum. -/
lemma runningInfLoc_continuous {f : DLoc}
    (hf : ∀ t : ℝ≥0, Function.leftLim f.1 t ≤ f.1 t) : Continuous (runningInfLoc f) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  rw [continuousAt_iff_continuous_left'_right']
  constructor
  · apply tendsto_order.2
    constructor
    · intro a ha
      filter_upwards [self_mem_nhdsWithin] with s hs
      exact ha.trans_le (runningInfLoc_antitone f hs.le)
    · intro b hb
      obtain ⟨u, hu⟩ : ∃ u : Set.Iic t, f.1 u < b := by
        exact exists_lt_of_ciInf_lt hb
      by_cases hut : (u : ℝ≥0) < t
      · filter_upwards [Ioo_mem_nhdsLT hut] with s hs
        exact (runningInf_le_eval f s ⟨u, hs.1.le⟩).trans_lt hu
      · have hut_eq : (u : ℝ≥0) = t := le_antisymm u.2 (le_of_not_gt hut)
        have hleft : Function.leftLim f.1 t < b := (hf t).trans_lt
          (hut_eq ▸ hu)
        filter_upwards [(f.2.tendsto_nhdsLT_leftLim t).eventually
          (isOpen_Iio.mem_nhds hleft)] with s hs
        exact (runningInf_le_eval f s ⟨s, by simp⟩).trans_lt hs
  · apply tendsto_order.2
    constructor
    · intro a ha
      obtain ⟨a', haa', ha'⟩ := exists_between ha
      have hat : a' < f.1 t := ha'.trans_le (runningInf_le_eval f t ⟨t, by simp⟩)
      have he : {u : ℝ≥0 | a' < f.1 u} ∈ 𝓝[Set.Ioi t] t :=
        (f.2.isRightContinuous t).eventually (isOpen_Ioi.mem_nhds hat)
      obtain ⟨b, htb, hb⟩ := (nhdsGT_basis t).mem_iff.mp he
      filter_upwards [Ioo_mem_nhdsGT htb] with s hs
      apply haa'.trans_le
      apply le_runningInf
      intro u
      by_cases hut : u ≤ t
      · exact ha'.le.trans (runningInf_le_eval f t ⟨u, hut⟩)
      · exact (hb ⟨lt_of_not_ge hut, lt_of_le_of_lt u.2 hs.2⟩).le
    · intro b hb
      filter_upwards [self_mem_nhdsWithin] with s hs
      exact (runningInfLoc_antitone f hs.le).trans_lt hb

/-- Finite creeping at every positive level makes the running infimum tend to `-∞`. -/
lemma runningInfLoc_tendsto_atBot {f : DLoc}
    (hcreep : ∀ x : ℝ, 0 < x → ∃ t : ℝ≥0,
      DLoc.strictPassageBelow (-x) f = (t : WithTop ℝ≥0) ∧ f.1 t = -x) :
    Tendsto (runningInfLoc f) atTop atBot := by
  apply tendsto_atBot.2
  intro b
  let x : ℝ := |b| + 1
  have hx : 0 < x := by dsimp [x]; positivity
  obtain ⟨t, ht, hval⟩ := hcreep x hx
  filter_upwards [eventually_ge_atTop t] with s hs
  exact (runningInfLoc_antitone f hs).trans ((runningInf_le_eval f t ⟨t, by simp⟩).trans
    (by rw [hval]; dsimp [x]; linarith [neg_abs_le b]))


/-- The first passage time below `-x`, as a process indexed by the level `x ≥ 0`. -/
noncomputable def firstPassageBelow (x : ℝ≥0) (f : DLoc) : WithTop ℝ≥0 :=
  DLoc.strictPassageBelow (-(x : ℝ)) f

/-- Each first passage time is a stopping time of the right-continuous filtration. -/
theorem isStoppingTime_firstPassageBelow (x : ℝ≥0) :
    IsStoppingTime DLoc.filtration (firstPassageBelow x) :=
  DLoc.isStoppingTime_strictPassageBelow _

private lemma passage_mono_level {f : DLoc} {x y : ℝ} (hxy : x ≤ y) :
    DLoc.strictPassageBelow (-x) f ≤ DLoc.strictPassageBelow (-y) f := by
  apply le_iInf
  intro t
  apply le_iInf
  intro ht
  exact iInf_le_of_le t (iInf_le _ (show f.1 t < -x by linarith))

/-- Finiteness at a larger level implies finiteness at a smaller level. -/
lemma strictPassageBelow_ne_top_of_le_neg {f : DLoc} {x y : ℝ} (hxy : x ≤ y)
    (hfin : DLoc.strictPassageBelow (-y) f ≠ ⊤) :
    DLoc.strictPassageBelow (-x) f ≠ ⊤ := by
  exact ne_top_of_le_ne_top hfin (passage_mono_level hxy)

private lemma strictPassageBelow_lt_iff (a : ℝ) (f : DLoc) (t : ℝ≥0) :
    DLoc.strictPassageBelow a f < (t : WithTop ℝ≥0) ↔
      ∃ q : ℚ, 0 ≤ q ∧ (q : ℝ) < t ∧ f.1 (Real.toNNReal q) < a := by
  have hreflect : DLoc.strictPassageBelow a f =
      DLoc.strictPassageAbove (-a)
        (⟨fun u => -f.1 u, f.2.continuous_comp continuous_neg⟩ : DLoc) := by
    simpa only [neg_neg] using DLoc.strictPassageBelow_neg (-a) f
  have hrat := DLoc.strictPassageAbove_lt_iff (-a)
    (⟨fun u => -f.1 u, f.2.continuous_comp continuous_neg⟩ : DLoc) t
  rw [hreflect, hrat]
  constructor
  · rintro ⟨q, hq0, hqt, hval⟩
    exact ⟨q, hq0, hqt, by simpa using neg_lt_neg_iff.mp hval⟩
  · rintro ⟨q, hq0, hqt, hval⟩
    exact ⟨q, hq0, hqt, by simpa using neg_lt_neg_iff.mpr hval⟩

private lemma measurableSet_firstPassage_lt_coe (t : ℝ≥0) :
    MeasurableSet {p : ℝ≥0 × DLoc | firstPassageBelow p.1 p.2 < (t : WithTop ℝ≥0)} := by
  have hset : {p : ℝ≥0 × DLoc | firstPassageBelow p.1 p.2 < (t : WithTop ℝ≥0)} =
      ⋃ q : {q : ℚ // 0 ≤ q ∧ (q : ℝ) < t},
        {p : ℝ≥0 × DLoc | p.2.1 (Real.toNNReal q.1) < -(p.1 : ℝ)} := by
    ext p
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
    change DLoc.strictPassageBelow (-(p.1 : ℝ)) p.2 < (t : WithTop ℝ≥0) ↔ _
    rw [strictPassageBelow_lt_iff]
    constructor
    · rintro ⟨q, hq0, hqt, hval⟩
      exact ⟨⟨q, hq0, hqt⟩, hval⟩
    · rintro ⟨⟨q, hq0, hqt⟩, hval⟩
      exact ⟨q, hq0, hqt, hval⟩
  rw [hset]
  apply MeasurableSet.iUnion
  intro q
  exact measurableSet_lt ((DLoc.measurable_eval _).comp measurable_snd)
    (measurable_coe_nnreal_real.comp measurable_fst).neg

/-- Joint measurability of the first passage times in the level and the path. -/
theorem measurable_firstPassageBelow_uncurry :
    Measurable (fun p : ℝ≥0 × DLoc => firstPassageBelow p.1 p.2) := by
  apply measurable_of_Iio
  intro t
  induction t using WithTop.recTopCoe with
  | top =>
      change MeasurableSet {p : ℝ≥0 × DLoc | firstPassageBelow p.1 p.2 < ⊤}
      have hset : {p : ℝ≥0 × DLoc | firstPassageBelow p.1 p.2 < ⊤} =
          ⋃ n : ℕ, {p : ℝ≥0 × DLoc |
            firstPassageBelow p.1 p.2 < (n : WithTop ℝ≥0)} := by
        ext p
        simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
        constructor
        · intro h
          obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp h.ne
          obtain ⟨n, hn⟩ := exists_nat_gt (r : ℝ)
          refine ⟨n, ?_⟩
          rw [← hr]
          exact_mod_cast hn
        · rintro ⟨n, hn⟩
          exact hn.trans_le le_top
      rw [hset]
      exact MeasurableSet.iUnion fun n => measurableSet_firstPassage_lt_coe n
  | coe t =>
      change MeasurableSet {p : ℝ≥0 × DLoc |
        firstPassageBelow p.1 p.2 < (t : WithTop ℝ≥0)}
      exact measurableSet_firstPassage_lt_coe t

end BGW.StableTrees

