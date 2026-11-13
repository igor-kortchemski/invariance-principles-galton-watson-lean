/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.ExcursionHeightLocality
import BGW.StableTrees.HeightProcessRoot
import BGW.Skorokhod.Vervaat

/-!
# Interior ancestors and positive continuous heights

A compact window minimum supplies an ancestor. A strict gap above the root excludes zero
ancestral height. The reversed clock bounds nearby rational-horizon heights from below.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal Classical
open BGW.Skorokhod

namespace BGW.StableTrees

/-- The infimum of a local path on a compact window. -/
noncomputable def heightWindowInf (a b : ℝ≥0) (f : DLoc) : ℝ :=
  (⨅ s, DLoc.restrict (b - a) (DLoc.shift a f) s) + f.1 a

private theorem height_leftLim_window {f : DLoc} (a b : ℝ≥0)
    (s : Icc (0 : ℝ) (b : ℝ)) (hs : 0 < (s : ℝ)) :
    Function.leftLim (DLoc.restrict b (DLoc.shift a f)) s =
      Function.leftLim f.1 (a + NNReal.mk s s.2.1) - f.1 a := by
  let inc : Icc (0 : ℝ) (b : ℝ) → ℝ≥0 := fun u => a + NNReal.mk u u.2.1
  have hc : Continuous inc := continuous_const.add
    (Continuous.subtype_mk continuous_subtype_val fun u => u.2.1)
  have hm : Tendsto inc (𝓝[<] s) (𝓝[<] (inc s)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨hc.continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with u hu
    exact (add_lt_add_iff_left a).mpr
      (show NNReal.mk u u.2.1 < NNReal.mk s s.2.1 from hu)
  let z : Icc (0 : ℝ) (b : ℝ) := ⟨0, le_rfl, b.2⟩
  let _ : (𝓝[<] s).NeBot := nhdsLT_neBot_of_exists_lt ⟨z, hs⟩
  apply leftLim_eq_of_tendsto
  exact ((f.2.tendsto_nhdsLT_leftLim (inc s)).comp hm).sub_const (f.1 a)

/-- A compact window infimum bounds each value in the window. -/
theorem heightWindowInf_le_eval (f : DLoc) {a b v : ℝ≥0}
    (hav : a ≤ v) (hvb : v ≤ b) : heightWindowInf a b f ≤ f.1 v := by
  let F := DLoc.restrict (b - a) (DLoc.shift a f)
  let u : Icc (0 : ℝ) ((b - a : ℝ≥0) : ℝ) :=
    ⟨((v - a : ℝ≥0) : ℝ), (v - a).2, (tsub_le_tsub_right hvb a)⟩
  have h := ciInf_le (isBounded_range F).bddBelow u
  have he : F u = f.1 v - f.1 a := by
    change f.1 (a + (v - a)) - f.1 a = _
    rw [add_tsub_cancel_of_le hav]
  rw [he] at h
  dsimp [heightWindowInf]
  linarith

/-- A generalized minimum gives an ancestral contact in a compact window. -/
theorem exists_heightWindow_ancestor (f : DLoc)
    (hf : ∀ r, Function.leftLim f.1 r ≤ f.1 r) {a b : ℝ≥0} (hab : a ≤ b) :
    ∃ s : ℝ≥0, a ≤ s ∧ s ≤ b ∧ Function.leftLim f.1 s ≤ heightWindowInf a b f := by
  let F := DLoc.restrict (b - a) (DLoc.shift a f)
  obtain ⟨u, hu⟩ := exists_min_leftLim F (b - a).2
  let s : ℝ≥0 := a + NNReal.mk u u.2.1
  have hsb : s ≤ b := by
    calc
      s ≤ a + (b - a) := add_le_add le_rfl (show NNReal.mk u u.2.1 ≤ b - a from u.2.2)
      _ = b := add_tsub_cancel_of_le hab
  refine ⟨s, le_add_of_nonneg_right zero_le, hsb, ?_⟩
  have heval : F u = f.1 s - f.1 a := rfl
  rcases min_le_iff.mp hu.le with hl | hv
  · by_cases hz : (u : ℝ) = 0
    · have hu0 : u = ⟨0, le_rfl, (b - a).2⟩ := Subtype.ext hz
      rw [hu0, leftLim_eq_of_isBot (show IsBot (⟨0, le_rfl, (b - a).2⟩ :
        Icc (0 : ℝ) ((b - a : ℝ≥0) : ℝ)) from fun v => v.2.1), ← hu0] at hl
      rw [heval] at hl
      have hh := hf s
      dsimp [heightWindowInf]
      linarith
    · have hpos : 0 < (u : ℝ) := lt_of_le_of_ne u.2.1 (Ne.symm hz)
      rw [height_leftLim_window a (b - a) u hpos] at hl
      change Function.leftLim f.1 s - f.1 a ≤ _ at hl
      dsimp [heightWindowInf]
      linarith
  · rw [heval] at hv
    have hh := hf s
    dsimp [heightWindowInf]
    linarith

/-- The rational clock formulas exclude a zero continuous height above a positive ancestor. -/
theorem heightLoc_pos_of_ancestor_window (θ : ℝ) (f : DLoc)
    (hzero : ∀ t s : ℝ≥0, 0 < s → s < t →
      Function.leftLim f.1 s ≤ futureInf f t s → height θ f s = 0 →
        futureInf f t s = futureInf f t 0)
    (hclock : ∀ q : ℚ, 0 < (q : ℝ) → ∀ s : ℝ≥0, s ≤ (q : ℝ).toNNReal →
      Function.leftLim f.1 s ≤ futureInf f (q : ℝ).toNNReal s →
        0 ≤ height θ f s ∧ height θ f s = height θ f (q : ℝ).toNNReal -
          supLocalTime θ (reversedAt (q : ℝ).toNNReal f) ((q : ℝ).toNNReal - s))
    (hmod : ∀ q : ℚ, heightLoc θ f (q : ℝ).toNNReal = height θ f (q : ℝ).toNNReal)
    {s t b : ℝ≥0} (hs : 0 < s) (hst : s ≤ t) (htb : t < b)
    (ha : ∀ r ∈ Ioo t b, Function.leftLim f.1 s ≤ futureInf f r s ∧
      futureInf f r 0 < futureInf f r s) : 0 < heightLoc θ f t := by
  have hbound (r : ℝ≥0) (hr : r ∈ Ioo t b) (hqr : IsRationalTime r) :
      0 ≤ height θ f s ∧ height θ f s ≤ heightLoc θ f r := by
    obtain ⟨q, hq⟩ := hqr
    have hqpos : 0 < (q : ℝ) := by
      rw [hq]
      exact_mod_cast hs.trans_le (hst.trans hr.1.le)
    have hqn : (q : ℝ).toNNReal = r := by rw [hq, Real.toNNReal_coe]
    have hh := hclock q hqpos s (hqn ▸ hst.trans hr.1.le) (hqn ▸ (ha r hr).1)
    have hnn : 0 ≤ supLocalTime θ (reversedAt (q : ℝ).toNNReal f)
        ((q : ℝ).toNNReal - s) := by rw [supLocalTime_eq_toReal]; positivity
    refine ⟨hh.1, ?_⟩
    rw [← hqn, hmod]
    linarith only [hh.2, hnn]
  obtain ⟨q, hqt, hqb⟩ := exists_rat_btwn (show (t : ℝ) < b from htb)
  have hqpos : 0 < (q : ℝ) := (show (0 : ℝ) < t from hs.trans_le hst).trans hqt
  have hqn : ((q : ℝ).toNNReal : ℝ) = q := Real.coe_toNNReal _ hqpos.le
  have hqmem : (q : ℝ).toNNReal ∈ Ioo t b := by
    exact ⟨Real.lt_toNNReal_iff_coe_lt.mpr hqt,
      (Real.toNNReal_lt_iff_lt_coe hqpos.le).mpr hqb⟩
  have hh := hbound _ hqmem ⟨q, hqn.symm⟩
  have hne : height θ f s ≠ 0 := by
    intro hz
    have he := hzero _ s hs (hst.trans_lt hqmem.1) (ha _ hqmem).1 hz
    exact (ne_of_gt (ha _ hqmem).2) he
  have hpos : 0 < height θ f s := lt_of_le_of_ne hh.1 (Ne.symm hne)
  obtain ⟨u, _, hu, hlim⟩ := dense_isRationalTime.exists_seq_strictAnti_tendsto t
  have hnear : ∀ᶠ n in atTop, u n < b := hlim.eventually (gt_mem_nhds htb)
  have hle : height θ f s ≤ heightLoc θ f t := by
    apply ge_of_tendsto ((continuous_heightLoc θ f).continuousAt.tendsto.comp hlim)
    filter_upwards [hnear] with n hn
    exact (hbound _ ⟨(hu n).1, hn⟩ (hu n).2).2
  exact hpos.trans_le hle

end BGW.StableTrees
