/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.ReflectedRestart
public import BGW.StableTrees.StablePassageSubordinator

/-!
# Pathwise passage intervals

Order and window-infimum facts for the passage process. These facts precede the use of
uniqueness of the minimum on rational windows in the excursion-support argument (J. Bertoin, *Lévy
Processes*, Cambridge University Press, 1996, Chapter VII).
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees

/-- The set of positive **jump levels** of the passage process: `{x > 0 | T_{x-} < T_x}`. -/
def passageJumpSet (f : DLoc) : Set ℝ≥0 :=
  {x | 0 < x ∧ passageTimeMinus x f < passageTime x f}

/-- The supremum defining the left passage time has its expected finite reading whenever
all passage times are finite. -/
private theorem iSup_passage_eq_coe_passageTimeMinus {f : DLoc}
    (hT : ∀ x, firstPassageBelow x f = (passageTime x f : WithTop ℝ≥0)) (x : ℝ≥0) :
    (⨆ y : Set.Iio x, firstPassageBelow y f) = (passageTimeMinus x f : WithTop ℝ≥0) := by
  have hb : (⨆ y : Set.Iio x, firstPassageBelow y f) ≤ firstPassageBelow x f :=
    iSup_le fun y => firstPassageBelow_mono f y.2.le
  obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.mp
    (ne_top_of_le_ne_top (by rw [hT x]; exact WithTop.coe_ne_top) hb)
  simp only [passageTimeMinus, ← ht, WithTop.untopD_coe]

/-- Passage times at smaller levels are bounded by the left passage time. -/
private theorem passageTime_le_passageTimeMinus {f : DLoc}
    (hT : ∀ x, firstPassageBelow x f = (passageTime x f : WithTop ℝ≥0))
    {x y : ℝ≥0} (hyx : y < x) : passageTime y f ≤ passageTimeMinus x f := by
  have h := le_iSup (fun z : Set.Iio x => firstPassageBelow z f) ⟨y, hyx⟩
  rw [iSup_passage_eq_coe_passageTimeMinus hT x, hT y] at h
  exact_mod_cast h

/-- The left passage time is bounded by the passage time at its level. -/
private theorem passageTimeMinus_le_passageTime {f : DLoc}
    (hT : ∀ x, firstPassageBelow x f = (passageTime x f : WithTop ℝ≥0))
    (x : ℝ≥0) : passageTimeMinus x f ≤ passageTime x f := by
  have h : (⨆ y : Set.Iio x, firstPassageBelow y f) ≤ firstPassageBelow x f :=
    iSup_le fun y => firstPassageBelow_mono f y.2.le
  rw [iSup_passage_eq_coe_passageTimeMinus hT x, hT x] at h
  exact_mod_cast h

/-- Creeping at every level makes the passage process strictly increasing. -/
theorem strictMono_passageTime_of_creeping {f : DLoc}
    (hT : ∀ x, firstPassageBelow x f = (passageTime x f : WithTop ℝ≥0))
    (hcreep : ∀ x, f.1 (passageTime x f) = -(x : ℝ)) :
    StrictMono (fun x => passageTime x f) := by
  have hm : Monotone (fun x => passageTime x f) := by
    intro x y hxy
    have h := firstPassageBelow_mono f hxy
    change firstPassageBelow x f ≤ firstPassageBelow y f at h
    rw [hT x, hT y] at h
    exact_mod_cast h
  intro x y hxy
  apply lt_of_le_of_ne (hm hxy.le)
  intro heq
  have hval := congrArg f.1 heq
  rw [hcreep x, hcreep y] at hval
  have : x = y := NNReal.coe_injective (neg_injective hval)
  exact hxy.ne this

/-- Strict increase separates the passage time at one level from the left passage time
at every larger level. -/
theorem passageTime_lt_passageTimeMinus {f : DLoc}
    (hT : ∀ x, firstPassageBelow x f = (passageTime x f : WithTop ℝ≥0))
    (hm : StrictMono (fun x => passageTime x f)) {x y : ℝ≥0} (hxy : x < y) :
    passageTime x f < passageTimeMinus y f := by
  obtain ⟨z, hxz, hzy⟩ := exists_between hxy
  exact (hm hxz).trans_le (passageTime_le_passageTimeMinus hT hzy)

private theorem tendsto_passageTime_left {f : DLoc}
    (hT : ∀ x, firstPassageBelow x f = (passageTime x f : WithTop ℝ≥0))
    (hm : StrictMono (fun x => passageTime x f)) {x : ℝ≥0} :
    Tendsto (fun y => passageTime y f) (𝓝[<] x) (𝓝[<] (passageTimeMinus x f)) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · apply tendsto_order.2
    constructor
    · intro a ha
      have hex : ∃ y : Set.Iio x, a < passageTime y f := by
        by_contra hn
        have hs : (⨆ y : Set.Iio x, firstPassageBelow y f) ≤ (a : WithTop ℝ≥0) := by
          apply iSup_le
          intro y
          rw [hT y]
          exact_mod_cast (le_of_not_gt (fun hy => hn ⟨y, hy⟩))
        rw [iSup_passage_eq_coe_passageTimeMinus hT x] at hs
        have : passageTimeMinus x f ≤ a := by exact_mod_cast hs
        exact ha.not_ge this
      obtain ⟨y, hy⟩ := hex
      filter_upwards [Ioo_mem_nhdsLT y.2] with z hz
      exact hy.trans_le (hm.monotone hz.1.le)
    · intro b hb
      filter_upwards [self_mem_nhdsWithin] with y hy
      exact (passageTime_le_passageTimeMinus hT hy).trans_lt hb
  · filter_upwards [self_mem_nhdsWithin] with y hy
    exact passageTime_lt_passageTimeMinus hT hm hy

/-- At a positive level the left passage endpoint is positive, and the path approaches
the barrier there from the left. No minimum-uniqueness theorem is used. -/
theorem leftLim_at_passageTimeMinus {f : DLoc}
    (hT : ∀ x, firstPassageBelow x f = (passageTime x f : WithTop ℝ≥0))
    (hcreep : ∀ x, f.1 (passageTime x f) = -(x : ℝ)) {x : ℝ≥0} (hx : 0 < x) :
    0 < passageTimeMinus x f ∧ Function.leftLim f.1 (passageTimeMinus x f) = -(x : ℝ) := by
  have hm := strictMono_passageTime_of_creeping hT hcreep
  have hg : 0 < passageTimeMinus x f :=
    (show 0 ≤ passageTime 0 f from (passageTime 0 f).2).trans_lt
      (passageTime_lt_passageTimeMinus hT hm hx)
  refine ⟨hg, ?_⟩
  let _ : (𝓝[<] x).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, hx⟩
  have hlim := (f.2.tendsto_nhdsLT_leftLim (passageTimeMinus x f)).comp
    (tendsto_passageTime_left hT hm)
  have hval : Tendsto (fun y : ℝ≥0 => f.1 (passageTime y f)) (𝓝[<] x)
      (𝓝 (-(x : ℝ))) := by
    simp_rw [hcreep]
    exact (continuous_subtype_val.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).neg
  exact tendsto_nhds_unique hlim hval

private theorem bddBelow_passage_window (f : DLoc) (r q : ℝ≥0) :
    BddBelow (Set.range (fun u : Set.Icc r q => f.1 u)) := by
  apply (bddBelow_runningInf_range f q).mono
  rintro _ ⟨u, rfl⟩
  exact ⟨⟨u, u.2.2⟩, rfl⟩

/-- A window containing a left passage endpoint, and ending before the right endpoint,
has infimum equal to the passage barrier. -/
theorem iInf_window_passageTimeMinus {f : DLoc}
    (hT : ∀ x, firstPassageBelow x f = (passageTime x f : WithTop ℝ≥0))
    (hcreep : ∀ x, f.1 (passageTime x f) = -(x : ℝ))
    {x r q : ℝ≥0} (hx : 0 < x) (hrg : r < passageTimeMinus x f)
    (hgq : passageTimeMinus x f < q) (hqd : q < passageTime x f) :
    (⨅ u : Set.Icc r q, f.1 u) = -(x : ℝ) := by
  have hg := leftLim_at_passageTimeMinus hT hcreep hx
  have hbefore {u : ℝ≥0} (hu : u < passageTime x f) : -(x : ℝ) ≤ f.1 u := by
    apply le_eval_of_lt_strictPassageBelow
    change (u : WithTop ℝ≥0) < firstPassageBelow x f
    rw [hT x]
    exact_mod_cast hu
  let _ : Nonempty (Set.Icc r q) := ⟨⟨passageTimeMinus x f, hrg.le, hgq.le⟩⟩
  apply le_antisymm
  · rw [← hg.2]
    let _ : (𝓝[<] (passageTimeMinus x f)).NeBot :=
      nhdsLT_neBot_of_exists_lt ⟨0, hg.1⟩
    apply ge_of_tendsto (f.2.tendsto_nhdsLT_leftLim (passageTimeMinus x f))
    filter_upwards [Ioo_mem_nhdsLT hrg] with u hu
    exact ciInf_le (bddBelow_passage_window f r q) ⟨u, hu.1.le, hu.2.le.trans hgq.le⟩
  · exact le_ciInf fun u => hbefore (u.2.2.trans_lt hqd)

/-- Stable paths creep simultaneously at all passage levels, including level zero. -/
theorem ae_creeping_passageTime {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc),
      ∀ x : ℝ≥0, f.1 (passageTime x f) = -(x : ℝ) := by
  filter_upwards [ae_passageTime_eq_firstPassageBelow hθ, ae_firstPassageBelow_spec hθ]
    with f hT hs
  intro x
  by_cases hx : x = 0
  · subst x
    simp [hT.2, hs.1]
  · exact (hs.2 x (pos_iff_ne_zero.mpr hx)).2.2

end BGW.StableTrees
