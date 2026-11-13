/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.ExcursionHeightPositiveAncestors
public import BGW.StableTrees.ExcursionMeasureSupportPath

/-!
# Simultaneous positive heights of host excursion marks

The compact interior support bound keeps a generalized minimum strictly above the root.
The minimum is ancestral to every sufficiently close later horizon.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal Classical
open BGW.Skorokhod

namespace BGW.StableTrees

/-- Compact window infima commute with a valid excursion cut. -/
theorem heightWindowInf_cut {g d : ℝ≥0} {f : DLoc} (hc : cutValid g d f)
    {a b : ℝ≥0} (hab : a ≤ b) (hbd : b ≤ d - g) :
    heightWindowInf (g + a) (g + b) f =
      excursionWindowInf a b (excursionCut g d f) + f.1 g := by
  have hgb : g + b ≤ d := by
    simpa only [add_comm] using (le_tsub_iff_right hc.1.le).mp hbd
  have he (v : ℝ≥0) (hv : v ≤ b) :
      (excursionCut g d f).path.1 v = f.1 (g + v) - f.1 g := by
    rw [excursionCut_eval hc, min_eq_left ((add_le_add le_rfl hv).trans hgb)]
  have hF : DLoc.restrict (b - a) (DLoc.shift (g + a) f) =
      DLoc.restrict (b - a) (DLoc.shift a (excursionCut g d f).path) := by
    apply BGW.Skorokhod.ext
    intro u
    let v : ℝ≥0 := ⟨u, u.2.1⟩
    have huv : a + v ≤ b := by
      calc
        a + v ≤ a + (b - a) := add_le_add le_rfl (show v ≤ b - a from u.2.2)
        _ = b := add_tsub_cancel_of_le hab
    change f.1 ((g + a) + v) - f.1 (g + a) =
      (excursionCut g d f).path.1 (a + v) - (excursionCut g d f).path.1 a
    rw [he (a + v) huv, he a hab, add_assoc]
    ring
  dsimp [heightWindowInf, excursionWindowInf]
  rw [add_tsub_add_eq_tsub_left, hF, he a hab]
  ring

/-- A compact minimum above a previous level forces a positive continuous height. -/
theorem heightLoc_pos_of_window (θ : ℝ) (f : DLoc)
    (hf : ∀ r, Function.leftLim f.1 r ≤ f.1 r)
    (hzero : ∀ t s : ℝ≥0, 0 < s → s < t →
      Function.leftLim f.1 s ≤ futureInf f t s → height θ f s = 0 →
        futureInf f t s = futureInf f t 0)
    (hclock : ∀ q : ℚ, 0 < (q : ℝ) → ∀ s : ℝ≥0, s ≤ (q : ℝ).toNNReal →
      Function.leftLim f.1 s ≤ futureInf f (q : ℝ).toNNReal s →
        0 ≤ height θ f s ∧ height θ f s = height θ f (q : ℝ).toNNReal -
          supLocalTime θ (reversedAt (q : ℝ).toNNReal f) ((q : ℝ).toNNReal - s))
    (hmod : ∀ q : ℚ, heightLoc θ f (q : ℝ).toNNReal = height θ f (q : ℝ).toNNReal)
    {g a t : ℝ≥0} (hga : g < a) (hat : a ≤ t)
    (hmin : f.1 g < heightWindowInf a t f) (hval : f.1 a < f.1 t) :
    0 < heightLoc θ f t := by
  let m := heightWindowInf a t f
  obtain ⟨s, has, hst, hs⟩ := exists_heightWindow_ancestor f hf hat
  have hmt : m < f.1 t := (heightWindowInf_le_eval f le_rfl hat).trans_lt hval
  have hnear : ∀ᶠ v in 𝓝[>] t, m < f.1 v :=
    (f.2.isRightContinuous t).tendsto.eventually (lt_mem_nhds hmt)
  obtain ⟨b, htb, hb⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hnear
  apply heightLoc_pos_of_ancestor_window θ f hzero hclock hmod
    ((zero_le.trans_lt hga).trans_le has) hst htb
  intro r hr
  have hsr : s ≤ r := hst.trans hr.1.le
  have hl : m ≤ futureInf f r s := by
    let : Nonempty (Icc (min s r) r) := ⟨⟨r, min_le_right _ _, le_rfl⟩⟩
    apply le_ciInf
    intro v
    have hsv : s ≤ (v : ℝ≥0) := by simpa only [min_eq_left hsr] using v.2.1
    by_cases hvt : (v : ℝ≥0) ≤ t
    · exact heightWindowInf_le_eval f (has.trans hsv) hvt
    · exact (hb ⟨not_le.mp hvt, v.2.2.trans_lt hr.2⟩).le
  refine ⟨hs.trans hl, ?_⟩
  exact (futureInf_le_eval f r 0 g
    ⟨by simp, (hga.le.trans hat).trans hr.1.le⟩).trans_lt (hmin.trans_le hl)

/-- Every host jump mark has strictly positive continuous height at every interior age. -/
theorem ae_jumpExcursion_height_pos {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∀ x ∈ passageJumpSet f,
      ∀ t : ℝ≥0, 0 < t → t < (jumpExcursion x f).lifetime →
        0 < excursionHeight θ (jumpExcursion x f) t := by
  have hrat (q : ℚ) : ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), 0 < (q : ℝ) →
      ∀ s : ℝ≥0, s ≤ (q : ℝ).toNNReal →
      Function.leftLim f.1 s ≤ futureInf f (q : ℝ).toNNReal s →
        0 ≤ height θ f s ∧ height θ f s = height θ f (q : ℝ).toNNReal -
          supLocalTime θ (reversedAt (q : ℝ).toNNReal f) ((q : ℝ).toNNReal - s) := by
    by_cases hq : 0 < (q : ℝ)
    · filter_upwards [ae_height_ancestor_fixed hθ (Real.toNNReal_pos.mpr hq)] with f hh
      intro _ s hs ha
      exact ⟨(hh s hs ha).2.1, (hh s hs ha).2.2.2⟩
    · exact ae_of_all _ fun _ h => (hq h).elim
  filter_upwards [ae_all_iff.mpr hrat, ae_zero_height_ancestor_inf_all hθ,
    ae_leftLim_le_stableLocalLaw hθ,
    ae_all_iff.mpr (fun q : ℚ => ae_heightLoc_eq_height hθ (q : ℝ).toNNReal),
    ae_jumpExcursion_spec hθ, ae_jumpExcursion_support hθ,
    ae_jumpExcursion_windowInf_pos hθ, ae_heightLoc_jumpExcursion hθ]
    with f hclock hzero hf hmod hcut hsup hwin hloc
  intro x hx t ht htl
  let e := jumpExcursion x f
  let g := passageTimeMinus x f
  let d := passageTime x f
  have hc : cutValid g d f := (hcut x hx).1
  have htd : t < d - g := (hcut x hx).2.1 ▸ htl
  have hpos : 0 < e.path.1 t := (hsup x hx).1 t ht htl
  have hsmall : ∀ᶠ v in 𝓝[>] (0 : ℝ≥0), e.path.1 v < e.path.1 t := by
    have he := (e.path.2.isRightContinuous 0).tendsto
    have he0 : e.path.1 0 = 0 := e.2.1
    rw [he0] at he
    exact he.eventually (gt_mem_nhds hpos)
  have hlt : ∀ᶠ v in 𝓝[>] (0 : ℝ≥0), v < t :=
    (eventually_lt_nhds ht).filter_mono nhdsWithin_le_nhds
  have hgt : ∀ᶠ v in 𝓝[>] (0 : ℝ≥0), 0 < v := self_mem_nhdsWithin
  obtain ⟨a, ⟨ha0, hat⟩, hav⟩ := ((hgt.and hlt).and hsmall).exists
  have hbound : f.1 g < heightWindowInf (g + a) (g + t) f := by
    rw [heightWindowInf_cut hc hat.le htd.le]
    exact lt_add_of_pos_left _ (hwin x hx a t ha0 hat.le htl)
  have hval : f.1 (g + a) < f.1 (g + t) := by
    have hea := excursionCut_eval hc a
    have het := excursionCut_eval hc t
    have hgt : g + t ≤ d := by
      simpa only [add_comm] using (le_tsub_iff_right hc.1.le).mp htd.le
    rw [min_eq_left hgt] at het
    rw [min_eq_left ((add_le_add le_rfl hat.le).trans hgt)] at hea
    change (excursionCut g d f).path.1 a < (excursionCut g d f).path.1 t at hav
    rw [hea, het] at hav
    linarith
  rw [← hloc x hx t htd.le]
  exact heightLoc_pos_of_window θ f hf hzero hclock hmod
    (lt_add_of_pos_right g ha0) (add_le_add le_rfl hat.le) hbound hval

end BGW.StableTrees
