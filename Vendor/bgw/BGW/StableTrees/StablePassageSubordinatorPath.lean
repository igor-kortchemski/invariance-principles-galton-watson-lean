/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.StableFirstPassagePath
public import BGW.Skorokhod.DLocShiftAt

/-!
# Deterministic path facts for passage times

This module develops the order and crossing properties of strict downward passage times
and of the running infimum for an arbitrary local càdlàg path (J. Bertoin, *Lévy Processes*,
Cambridge University Press, 1996, Chapter VII).
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees

/-- Strict downward passage is monotone in its level. -/
theorem firstPassageBelow_mono (f : DLoc) : Monotone (fun x => firstPassageBelow x f) := by
  intro x y hxy
  apply le_iInf
  intro t
  apply le_iInf
  intro ht
  exact iInf_le_of_le t (iInf_le _ (show f.1 t < -(x : ℝ) by
    exact ht.trans_le (neg_le_neg (by exact_mod_cast hxy))))

/-- A strict crossing gives an upper bound for the corresponding passage time. -/
theorem firstPassageBelow_le_of_eval_lt {f : DLoc} {x t : ℝ≥0}
    (h : f.1 t < -(x : ℝ)) : firstPassageBelow x f ≤ (t : WithTop ℝ≥0) := by
  exact iInf_le_of_le t (iInf_le _ h)

/-- If a passage time is strictly below a finite time, a crossing occurs earlier. -/
theorem exists_eval_lt_of_firstPassageBelow_lt {f : DLoc} {x t : ℝ≥0}
    (h : firstPassageBelow x f < (t : WithTop ℝ≥0)) :
    ∃ u : ℝ≥0, u < t ∧ f.1 u < -(x : ℝ) := by
  obtain ⟨u, hu, hut⟩ := (by
    simpa only [firstPassageBelow, DLoc.strictPassageBelow, iInf_lt_iff,
      WithTop.coe_lt_coe, exists_prop] using h :
      ∃ u : ℝ≥0, f.1 u < -(x : ℝ) ∧ u < t)
  exact ⟨u, hut, hu⟩

/-- The running infimum is bounded below on every bounded time interval. -/
theorem bddBelow_runningInf_range (f : DLoc) (t : ℝ≥0) :
    BddBelow (Set.range (fun u : Set.Iic t => f.1 u)) := by
  let T : ℝ≥0 := t + 1
  have hb := (isBounded_range (DLoc.restrict T f)).bddBelow
  apply hb.mono
  rintro y ⟨u, rfl⟩
  have huT : ((u : ℝ≥0) : ℝ) ≤ (T : ℝ) := by
    exact_mod_cast u.2.trans (show t ≤ T by simp [T])
  exact ⟨⟨(u : ℝ), u.1.2, huT⟩, rfl⟩

/-- The running infimum is smaller than every value on its defining interval. -/
theorem runningInfLoc_le_eval (f : DLoc) (t : ℝ≥0) (u : Set.Iic t) :
    runningInfLoc f t ≤ f.1 u := ciInf_le (bddBelow_runningInf_range f t) u

/-- A lower bound of all values on an interval bounds its running infimum. -/
theorem le_runningInfLoc (f : DLoc) (t : ℝ≥0) {a : ℝ}
    (h : ∀ u : Set.Iic t, a ≤ f.1 u) : a ≤ runningInfLoc f t := le_ciInf h

/-- A value strictly below the running infimum produces a crossing time in the interval. -/
theorem exists_eval_lt_of_runningInfLoc_lt {f : DLoc} {t : ℝ≥0} {a : ℝ}
    (h : runningInfLoc f t < a) : ∃ u : ℝ≥0, u ≤ t ∧ f.1 u < a := by
  obtain ⟨u, hu⟩ := (ciInf_lt_iff (bddBelow_runningInf_range f t)).mp h
  exact ⟨u, u.2, hu⟩

/-- At a finite strict passage time, the path is on or below its barrier. -/
theorem eval_le_of_firstPassageBelow_eq_coe {f : DLoc} {x t : ℝ≥0}
    (hT : firstPassageBelow x f = (t : WithTop ℝ≥0)) : f.1 t ≤ -(x : ℝ) := by
  by_contra h
  have ha : -(x : ℝ) < f.1 t := lt_of_not_ge h
  have he : ∀ᶠ s in 𝓝[Set.Ioi t] t, -(x : ℝ) < f.1 s :=
    (f.2.isRightContinuous t).eventually (isOpen_Ioi.mem_nhds ha)
  have hSet : {u : ℝ≥0 | -(x : ℝ) < f.1 u} ∈ 𝓝[Set.Ioi t] t := he
  rw [(nhdsGT_basis t).mem_iff] at hSet
  obtain ⟨b, htb, hb⟩ := hSet
  obtain ⟨u, hut, hu⟩ := exists_eval_lt_of_firstPassageBelow_lt
    (show firstPassageBelow x f < (b : WithTop ℝ≥0) by rw [hT]; exact_mod_cast htb)
  rcases lt_or_ge u t with hut' | htu
  · exact (not_lt_of_ge (le_eval_of_lt_strictPassageBelow
      (a := -(x : ℝ)) (by
        change DLoc.strictPassageBelow (-(x : ℝ)) f = _ at hT
        rw [hT]
        exact_mod_cast hut'))) hu
  · rcases htu.eq_or_lt with hut' | htu'
    · subst u
      exact (not_le_of_gt ha) hu.le
    · exact (not_lt_of_ge (hb ⟨htu', hut⟩).le) hu

/-- A finite passage time up to `t` forces the running infimum at `t` below its level. -/
theorem runningInfLoc_le_of_firstPassageBelow_le (f : DLoc) {x t : ℝ≥0}
    (h : firstPassageBelow x f ≤ (t : WithTop ℝ≥0)) : runningInfLoc f t ≤ -(x : ℝ) := by
  obtain ⟨s, hs⟩ := WithTop.ne_top_iff_exists.mp
    (ne_top_of_le_ne_top WithTop.coe_ne_top h)
  rw [← hs] at h
  have hst : s ≤ t := by exact_mod_cast h
  exact (runningInfLoc_le_eval f t ⟨s, hst⟩).trans
    (eval_le_of_firstPassageBelow_eq_coe hs.symm)

/-- The finite reading of a finite strict passage time coerces back to that time. -/
theorem firstPassageBelow_eq_coe_untopD (f : DLoc)
    (hfin : ∀ x, firstPassageBelow x f < ⊤) (x : ℝ≥0) :
    firstPassageBelow x f = (((firstPassageBelow x f).untopD 0 : ℝ≥0) : WithTop ℝ≥0) := by
  obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.mp (ne_of_lt (hfin x))
  simp only [← ht, WithTop.untopD_coe]

/-- The finite readings of finite strict passage times are nondecreasing. -/
theorem untopD_firstPassageBelow_mono (f : DLoc)
    (hfin : ∀ x, firstPassageBelow x f < ⊤) :
    Monotone (fun x => (firstPassageBelow x f).untopD 0) := by
  intro y z hyz
  have h := firstPassageBelow_mono f hyz
  change firstPassageBelow y f ≤ firstPassageBelow z f at h
  rw [firstPassageBelow_eq_coe_untopD f hfin y,
    firstPassageBelow_eq_coe_untopD f hfin z] at h
  change (firstPassageBelow y f).untopD 0 ≤ (firstPassageBelow z f).untopD 0
  exact_mod_cast h

/-- Finite strict passage times are right-continuous in the level. -/
theorem tendsto_untopD_firstPassageBelow_nhdsGT (f : DLoc)
    (hfin : ∀ x, firstPassageBelow x f < ⊤) (x : ℝ≥0) :
    Tendsto (fun y => (firstPassageBelow y f).untopD 0) (𝓝[>] x)
      (𝓝 ((firstPassageBelow x f).untopD 0)) := by
  let T : ℝ≥0 → ℝ≥0 := fun y => (firstPassageBelow y f).untopD 0
  change Tendsto T (𝓝[>] x) (𝓝 (T x))
  have hmono : Monotone T := untopD_firstPassageBelow_mono f hfin
  apply tendsto_order.2
  constructor
  · intro a ha
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact ha.trans_le (hmono hy.le)
  · intro b hb
    have hpass : firstPassageBelow x f < (b : WithTop ℝ≥0) := by
      rw [firstPassageBelow_eq_coe_untopD f hfin x]
      have hb' : (firstPassageBelow x f).untopD 0 < b := hb
      exact_mod_cast hb'
    obtain ⟨u, hu⟩ := (show ∃ u : ℝ≥0, ∃ _ : f.1 u < -(x : ℝ),
        (u : WithTop ℝ≥0) < (b : WithTop ℝ≥0) by
      simpa only [firstPassageBelow, DLoc.strictPassageBelow, iInf_lt_iff] using hpass)
    obtain ⟨v, hxv, hv⟩ := exists_between (show (x : ℝ) < -f.1 u by linarith [hu.1])
    let y : ℝ≥0 := Real.toNNReal v
    have hy : (y : ℝ) = v := Real.coe_toNNReal v ((by positivity : 0 ≤ (x : ℝ)).trans hxv.le)
    have hxy : x < y := by exact_mod_cast hxv.trans_eq hy.symm
    filter_upwards [Ioo_mem_nhdsGT hxy] with z hz
    have hzy : firstPassageBelow z f ≤ (u : WithTop ℝ≥0) := by
      apply firstPassageBelow_le_of_eval_lt
      have hzy0 : (z : ℝ) < (y : ℝ) := by exact_mod_cast hz.2
      have hzy' : (z : ℝ) < v := hzy0.trans_eq hy
      have hzu : f.1 u < -(z : ℝ) := by linarith [hu.1]
      exact hzu
    rw [firstPassageBelow_eq_coe_untopD f hfin z] at hzy
    have hTu : T z ≤ u := by
      change (firstPassageBelow z f).untopD 0 ≤ u
      exact_mod_cast hzy
    exact hTu.trans_lt (by exact_mod_cast hu.2)

/-- Finite strict passage times form a càdlàg nondecreasing real process. -/
theorem isCadlag_untopD_firstPassageBelow (f : DLoc)
    (hfin : ∀ x, firstPassageBelow x f < ⊤) :
    IsCadlag (fun x : ℝ≥0 => (((firstPassageBelow x f).untopD 0 : ℝ≥0) : ℝ)) := by
  let T : ℝ≥0 → ℝ≥0 := fun y => (firstPassageBelow y f).untopD 0
  have hmono : Monotone T := untopD_firstPassageBelow_mono f hfin
  have hreal : Monotone (fun x : ℝ≥0 => (T x : ℝ)) := fun _ _ h =>
    by exact_mod_cast hmono h
  change IsCadlag (fun x : ℝ≥0 => (T x : ℝ))
  refine ⟨fun x => ?_, fun x => ⟨_, hreal.tendsto_nhdsLT x⟩⟩
  exact NNReal.tendsto_coe.2 (tendsto_untopD_firstPassageBelow_nhdsGT f hfin x)

/-- Strict passage is the inverse of the negative running infimum. -/
theorem firstPassageBelow_eq_sInf_runningInf (x : ℝ≥0) (f : DLoc) :
    firstPassageBelow x f =
      sInf {t : WithTop ℝ≥0 | ∃ u : ℝ≥0, t = u ∧ (x : ℝ) < -runningInfLoc f u} := by
  apply le_antisymm
  · apply le_sInf
    rintro _ ⟨u, rfl, hu⟩
    have hI : runningInfLoc f u < -(x : ℝ) := by linarith
    obtain ⟨v, hvu, hv⟩ := exists_eval_lt_of_runningInfLoc_lt hI
    exact (firstPassageBelow_le_of_eval_lt hv).trans (by exact_mod_cast hvu)
  · apply le_iInf
    intro u
    apply le_iInf
    intro hu
    apply sInf_le
    refine ⟨u, rfl, ?_⟩
    have hI : runningInfLoc f u < -(x : ℝ) :=
      (runningInfLoc_le_eval f u ⟨u, by simp⟩).trans_lt hu
    linarith

/-- Strict-passage/running-infimum sandwich. -/
theorem runningInfLoc_lt_sandwich (x t : ℝ≥0) (f : DLoc) :
    (firstPassageBelow x f < (t : WithTop ℝ≥0) → runningInfLoc f t < -(x : ℝ)) ∧
      (runningInfLoc f t < -(x : ℝ) → firstPassageBelow x f ≤ (t : WithTop ℝ≥0)) := by
  constructor
  · intro h
    obtain ⟨u, hut, hu⟩ := exists_eval_lt_of_firstPassageBelow_lt h
    exact (runningInfLoc_le_eval f t ⟨u, hut.le⟩).trans_lt hu
  · intro h
    obtain ⟨u, hut, hu⟩ := exists_eval_lt_of_runningInfLoc_lt h
    exact (firstPassageBelow_le_of_eval_lt hu).trans (by exact_mod_cast hut)

/-- At a finite creeping passage time, the running infimum is the barrier. -/
theorem runningInfLoc_eq_of_firstPassageBelow_eq_coe {f : DLoc} {x s : ℝ≥0}
    (hs : firstPassageBelow x f = (s : WithTop ℝ≥0)) (hval : f.1 s = -(x : ℝ)) :
    runningInfLoc f s = -(x : ℝ) := by
  apply le_antisymm
  · exact (runningInfLoc_le_eval f s ⟨s, by simp⟩).trans_eq hval
  · apply le_runningInfLoc
    intro u
    rcases u.2.eq_or_lt with hu | hu
    · rw [show (u : ℝ≥0) = s from NNReal.coe_injective hu]
      exact hval.ge
    · apply le_eval_of_lt_strictPassageBelow
      change (u : WithTop ℝ≥0) < firstPassageBelow x f
      rw [hs]
      exact_mod_cast hu

private lemma bddBelow_future_range (f : DLoc) (s t : ℝ≥0) :
    BddBelow (Set.range (fun u : Set.Iic t => f.1 (s + u))) := by
  apply (bddBelow_runningInf_range f (s + t)).mono
  rintro _ ⟨u, rfl⟩
  exact ⟨⟨s + u, add_le_add le_rfl u.2⟩, rfl⟩

/-- Creeping at a passage time gives the additive decomposition at the next level. -/
theorem firstPassageBelow_add_of_creeping {f : DLoc} {s x y : ℝ≥0}
    (hs : firstPassageBelow x f = (s : WithTop ℝ≥0)) (hval : f.1 s = -(x : ℝ)) :
    firstPassageBelow (x + y) f =
      firstPassageBelow x f + firstPassageBelow y (DLoc.shiftAt (firstPassageBelow x) f) := by
  have hshift : DLoc.shiftAt (firstPassageBelow x) f = DLoc.shift s f := by
    unfold DLoc.shiftAt
    rw [hs]
    rfl
  rw [hs, hshift]
  change DLoc.strictPassageBelow (-((x + y : ℝ≥0) : ℝ)) f =
    (s : WithTop ℝ≥0) + DLoc.strictPassageBelow (-(y : ℝ)) (DLoc.shift s f)
  simp only [DLoc.strictPassageBelow]
  change (⨅ t : ℝ≥0, ⨅ (_ : f.1 t < -((x + y : ℝ≥0) : ℝ)), (t : ℝ≥0∞)) =
    (s : ℝ≥0∞) + ⨅ t : ℝ≥0, ⨅ (_ : (DLoc.shift s f).1 t < -(y : ℝ)), (t : ℝ≥0∞)
  rw [ENNReal.add_iInf]
  simp_rw [ENNReal.add_iInf]
  apply le_antisymm
  · apply le_iInf
    intro u
    apply le_iInf
    intro hu
    have heval : f.1 (s + u) < -((x + y : ℝ≥0) : ℝ) := by
      change f.1 (s + u) - f.1 s < -(y : ℝ) at hu
      rw [hval] at hu
      push_cast
      linarith
    exact iInf_le_of_le (s + u) (iInf_le _ heval)
  · apply le_iInf
    intro t
    apply le_iInf
    intro ht
    have hst : s ≤ t := by
      by_contra hst
      have hts : t < s := lt_of_not_ge hst
      have hbefore : -(x : ℝ) ≤ f.1 t := by
        apply le_eval_of_lt_strictPassageBelow
        change (t : WithTop ℝ≥0) < firstPassageBelow x f
        rw [hs]
        exact_mod_cast hts
      have htx : f.1 t < -(x : ℝ) := ht.trans_le (by
        simp only [NNReal.coe_add, neg_add_rev]
        linarith [NNReal.coe_nonneg y])
      exact (not_lt_of_ge hbefore) htx
    let u : ℝ≥0 := t - s
    have ht_eq : s + u = t := add_tsub_cancel_of_le hst
    rw [← ht_eq]
    have hu' : (DLoc.shift s f).1 u < -(y : ℝ) := by
      change f.1 (s + u) - f.1 s < -(y : ℝ)
      rw [hval, ht_eq]
      push_cast at ht ⊢
      linarith
    exact (iInf_le_of_le u (iInf_le _ hu')).trans_eq (WithTop.coe_add s u).symm

/-- The reflected path after a creeping passage time is the reflected centered shift. -/
theorem reflected_shift_of_creeping {f : DLoc} {s x : ℝ≥0}
    (hs : firstPassageBelow x f = (s : WithTop ℝ≥0)) (hval : f.1 s = -(x : ℝ))
    (t : ℝ≥0) :
    f.1 (s + t) - runningInfLoc f (s + t) =
      (DLoc.shift s f).1 t - runningInfLoc (DLoc.shift s f) t := by
  let A : ℝ := ⨅ u : Set.Iic t, f.1 (s + u)
  have hA_le (u : Set.Iic t) : A ≤ f.1 (s + u) := ciInf_le (bddBelow_future_range f s t) u
  have hIp : runningInfLoc f s = -(x : ℝ) :=
    runningInfLoc_eq_of_firstPassageBelow_eq_coe hs hval
  have hdecomp : runningInfLoc f (s + t) = A := by
    apply le_antisymm
    · apply le_ciInf
      intro u
      exact runningInfLoc_le_eval f (s + t) ⟨s + u, add_le_add le_rfl u.2⟩
    · apply le_ciInf
      intro v
      rcases le_or_gt v.1 s with hv | hv
      · have hA0 : A ≤ -(x : ℝ) := (hA_le ⟨0, by simp⟩).trans_eq (by simp [hval])
        have hIv : runningInfLoc f s ≤ f.1 v := runningInfLoc_le_eval f s ⟨v, hv⟩
        exact hA0.trans (hIp.ge.trans hIv)
      · have hsv : s ≤ v.1 := hv.le
        let u : ℝ≥0 := v.1 - s
        have hut : u ≤ t := by
          have hvbound : (v : ℝ≥0) ≤ s + t := v.2
          exact tsub_le_iff_right.mpr (by simpa only [add_comm t s] using hvbound)
        have huv : s + u = v.1 := add_tsub_cancel_of_le hsv
        exact (hA_le ⟨u, hut⟩).trans_eq (by rw [huv])
  have hshift : runningInfLoc (DLoc.shift s f) t = A - f.1 s := by
    apply le_antisymm
    · apply le_of_forall_gt
      intro a ha
      have ha' : A < a + f.1 s := by linarith
      obtain ⟨u, hu⟩ := (ciInf_lt_iff (bddBelow_future_range f s t)).mp ha'
      exact (ciInf_le (bddBelow_runningInf_range (DLoc.shift s f) t) u).trans_lt
        (by change f.1 (s + u) - f.1 s < a; linarith)
    · apply le_ciInf
      intro u
      exact sub_le_sub_right (hA_le u) (f.1 s)
  rw [hdecomp, hshift]
  change f.1 (s + t) - A = f.1 (s + t) - f.1 s - (A - f.1 s)
  ring

/-- Rational times, with the terminal value as a fallback, compute the running infimum. -/
theorem runningInfLoc_eq_iInf_rat (f : DLoc) (t : ℝ≥0) :
    runningInfLoc f t = ⨅ q : ℚ, if 0 ≤ q ∧ (q : ℝ) ≤ (t : ℝ) then
      f.1 (Real.toNNReal q) else f.1 t := by
  let g : ℚ → ℝ := fun q => if 0 ≤ q ∧ (q : ℝ) ≤ (t : ℝ) then
    f.1 (Real.toNNReal q) else f.1 t
  have hbound : BddBelow (Set.range g) := by
    apply (bddBelow_runningInf_range f t).mono
    rintro _ ⟨q, rfl⟩
    by_cases hq : 0 ≤ q ∧ (q : ℝ) ≤ (t : ℝ)
    · have hq0 : 0 ≤ (q : ℝ) := by exact_mod_cast hq.1
      have hqt : Real.toNNReal (q : ℝ) ≤ t := by
        rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hq0]
        exact hq.2
      exact ⟨⟨Real.toNNReal q, hqt⟩, by simp [g, hq]⟩
    · exact ⟨⟨t, by simp⟩, by simp [g, hq]⟩
  change runningInfLoc f t = ⨅ q, g q
  apply le_antisymm
  · apply le_ciInf
    intro q
    by_cases hq : 0 ≤ q ∧ (q : ℝ) ≤ (t : ℝ)
    · have hq0 : 0 ≤ (q : ℝ) := by exact_mod_cast hq.1
      have hqt : Real.toNNReal (q : ℝ) ≤ t := by
        rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hq0]
        exact hq.2
      simpa [g, hq] using runningInfLoc_le_eval f t ⟨Real.toNNReal q, hqt⟩
    · simp only [g, hq]
      exact runningInfLoc_le_eval f t ⟨t, by simp⟩
  · apply le_of_forall_gt
    intro a ha
    obtain ⟨u, hut, hu⟩ := exists_eval_lt_of_runningInfLoc_lt ha
    by_cases hut' : u = t
    · subst u
      have hle : (⨅ q, g q) ≤ g (-1) := ciInf_le hbound (-1)
      have hg : g (-1) = f.1 t := by norm_num [g]
      exact hle.trans_lt (hg.symm.trans_lt hu)
    · have hut'' : u < t := lt_of_le_of_ne hut hut'
      have he : ∀ᶠ v in 𝓝[Set.Ioi u] u, f.1 v < a :=
        (f.2.isRightContinuous u).eventually (isOpen_Iio.mem_nhds hu)
      have hSet : {v : ℝ≥0 | f.1 v < a} ∈ 𝓝[Set.Ioi u] u := he
      rw [(nhdsGT_basis u).mem_iff] at hSet
      obtain ⟨b, hub, hb⟩ := hSet
      obtain ⟨q, huq, hq⟩ := exists_rat_btwn
        (show (u : ℝ) < min (b : ℝ) (t : ℝ) by exact_mod_cast lt_min hub hut'')
      have hq0 : 0 ≤ (q : ℝ) := (by positivity : (0 : ℝ) ≤ u).trans huq.le
      have hqu : u < Real.toNNReal q := by
        rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hq0]
        exact_mod_cast huq
      have hqb : Real.toNNReal q < b := by
        rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hq0]
        exact_mod_cast hq.trans_le (min_le_left _ _)
      have hqt : Real.toNNReal q < t := by
        rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hq0]
        exact_mod_cast hq.trans_le (min_le_right _ _)
      have hqval : f.1 (Real.toNNReal q) < a := hb ⟨hqu, hqb⟩
      have hle : (⨅ q, g q) ≤ g q := ciInf_le hbound q
      apply hle.trans_lt
      have hqt' : (q : ℝ) ≤ (t : ℝ) := by
        have hle : ((Real.toNNReal q : ℝ≥0) : ℝ) ≤ (t : ℝ) := by exact_mod_cast hqt.le
        rwa [Real.coe_toNNReal _ hq0] at hle
      have hqmem : 0 ≤ q ∧ (q : ℝ) ≤ (t : ℝ) := ⟨by exact_mod_cast hq0, hqt'⟩
      simpa [g, hqmem] using hqval

/-- Clamping time at a rational time is strongly progressive. -/
theorem time_progressive (q : ℚ) :
    IsStronglyProgressive DLoc.filtration
      (fun t (_ : DLoc) => min (Real.toNNReal q) t) := by
  apply IsProgressive.isStronglyProgressive
  intro T
  exact (measurable_const.min (measurable_subtype_coe.comp measurable_fst))

/-- The running infimum is strongly progressive for the local filtration. -/
theorem isStronglyProgressive_runningInfLoc :
    IsStronglyProgressive DLoc.filtration (fun t (f : DLoc) => runningInfLoc f t) := by
  apply IsProgressive.isStronglyProgressive
  intro T
  simp_rw [runningInfLoc_eq_iInf_rat]
  apply Measurable.iInf
  intro q
  by_cases hq : 0 ≤ q
  · have hq0 : 0 ≤ (q : ℝ) := by exact_mod_cast hq
    have heq : (fun p : Set.Iic T × DLoc =>
        if 0 ≤ q ∧ (q : ℝ) ≤ (p.1 : ℝ) then p.2.1 (Real.toNNReal q)
        else p.2.1 p.1) = fun p => p.2.1 (min (Real.toNNReal q) p.1) := by
      funext p
      by_cases hqt : (q : ℝ) ≤ (p.1 : ℝ)
      · rw [ite_eq_left ⟨hq, hqt⟩, min_eq_left]
        rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hq0]
        exact hqt
      · rw [ite_eq_right (fun h => hqt h.2), min_eq_right]
        exact le_of_not_ge fun h => hqt (by
          rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hq0] at h
          exact h)
    rw [heq]
    exact ((DLoc.isStronglyProgressive_eval.comp (time_progressive q)
      (fun _ _ => min_le_right _ _)).isProgressive T)
  · have heq : (fun p : Set.Iic T × DLoc =>
        if 0 ≤ q ∧ (q : ℝ) ≤ (p.1 : ℝ) then p.2.1 (Real.toNNReal q)
        else p.2.1 p.1) = fun p => p.2.1 p.1 := by
      funext p
      exact ite_eq_right (fun h => hq h.1)
    rw [heq]
    exact DLoc.isStronglyProgressive_eval.isProgressive T

/-- Joint measurability of the running infimum in time and path. -/
theorem measurable_runningInfLoc_uncurry :
    Measurable (fun p : ℝ≥0 × DLoc => runningInfLoc p.2 p.1) := by
  simp_rw [runningInfLoc_eq_iInf_rat]
  apply Measurable.iInf
  intro q
  have hle : Measurable (fun p : ℝ≥0 × DLoc => (q : ℝ) ≤ (p.1 : ℝ)) :=
    measurable_const.le' (measurable_coe_nnreal_real.comp measurable_fst)
  apply Measurable.ite
  · exact (measurable_const.and hle).setOf
  · exact (DLoc.measurable_eval _).comp measurable_snd
  · exact DLoc.measurable_eval₂.comp (measurable_snd.prodMk measurable_fst)

/-- The running infimum is adapted to the right-continuous local filtration. -/
theorem stronglyAdapted_runningInfLoc :
    StronglyAdapted DLoc.filtration (fun t (f : DLoc) => runningInfLoc f t) := by
  intro t
  apply Measurable.stronglyMeasurable
  have hraw : Measurable[DLoc.rawFiltration t] (fun f : DLoc => runningInfLoc f t) := by
    simp_rw [runningInfLoc_eq_iInf_rat]
    apply Measurable.iInf
    intro q
    by_cases hq : 0 ≤ q ∧ (q : ℝ) ≤ (t : ℝ)
    · have hq0 : 0 ≤ (q : ℝ) := by exact_mod_cast hq.1
      have hqt : Real.toNNReal (q : ℝ) ≤ t := by
        rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hq0]
        exact hq.2
      simp only [hq]
      change Measurable[DLoc.rawFiltration t] (DLoc.eval (Real.toNNReal q))
      rw [measurable_iff_comap_le]
      change MeasurableSpace.comap (DLoc.eval (Real.toNNReal q)) inferInstance ≤
        ⨆ s ≤ t, MeasurableSpace.comap (DLoc.eval s) inferInstance
      exact le_iSup_of_le _ (le_iSup_of_le hqt le_rfl)
    · simp only [hq, ite_false]
      change Measurable[DLoc.rawFiltration t] (DLoc.eval t)
      rw [measurable_iff_comap_le]
      change MeasurableSpace.comap (DLoc.eval t) inferInstance ≤
        ⨆ s ≤ t, MeasurableSpace.comap (DLoc.eval s) inferInstance
      exact le_iSup_of_le t (le_iSup_of_le le_rfl le_rfl)
  exact hraw.mono (DLoc.rawFiltration.le_rightCont t) le_rfl

end BGW.StableTrees
