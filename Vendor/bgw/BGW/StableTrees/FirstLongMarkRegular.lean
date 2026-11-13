/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.FirstLongMarkBasic
import BGW.StableTrees.StraddlingExcursionPredictable
import Mathlib.Data.NNRat.Encodable

import BGW.Probability.NNReal

/-!
# Regular geometry at all stable excursion levels

Compact interior bounds come from the sealed rational-window minimum theorem. Rational
non-jump levels supply record brackets on both sides; right brackets use right continuity
of the strict passage process.

Reference: J. Bertoin, *Lévy Processes*, Cambridge University Press, 1996, Chapter IV.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod
open BGW.Probability

namespace BGW.StableTrees

variable {θ : ℝ}

private theorem windowInf_le {e : Excursion} {a b t : ℝ≥0} (ht : t ∈ Icc a b) :
    excursionWindowInf a b e ≤ e.path.1 t := by
  let W := DLoc.restrict (b - a) (DLoc.shift a e.path)
  let s : Icc (0 : ℝ) ((b - a : ℝ≥0) : ℝ) :=
    ⟨((t - a : ℝ≥0) : ℝ), (t - a).2, by exact_mod_cast tsub_le_tsub_right ht.2 a⟩
  calc
    excursionWindowInf a b e ≤ W s + e.path.1 a :=
      add_le_add (ciInf_le (isBounded_range W).bddBelow s) le_rfl
    _ = e.path.1 t := by
      change e.path.1 (a + (t - a)) - e.path.1 a + e.path.1 a = _
      rw [add_tsub_cancel_of_le ht.1, sub_add_cancel]

private theorem interior_bound {f : DLoc} {x : ℝ≥0} (_hx : x ∈ passageJumpSet f)
    (hs : (jumpExcursion x f).lifetime = passageTime x f - passageTimeMinus x f)
    (he : ∀ t : ℝ≥0, (jumpExcursion x f).path.1 t =
      (reflectedFrom 0 f).1 (min (passageTimeMinus x f + t) (passageTime x f)))
    (hw : ∀ a b : ℝ≥0, 0 < a → a ≤ b → b < (jumpExcursion x f).lifetime →
      0 < excursionWindowInf a b (jumpExcursion x f))
    (a b : ℝ≥0) (hga : passageTimeMinus x f < a) (hab : a ≤ b)
    (hbd : b < passageTime x f) :
    ∃ c : ℝ, 0 < c ∧ ∀ t : ℝ≥0, a ≤ t → t ≤ b →
      c ≤ (reflectedFrom 0 f).1 t ∧ c ≤ Function.leftLim (reflectedFrom 0 f).1 t := by
  let g := passageTimeMinus x f
  let d := passageTime x f
  obtain ⟨a', hga', ha'a⟩ := exists_between hga
  obtain ⟨b', hbb', hb'd⟩ := exists_between hbd
  have hgab : g ≤ a' := hga'.le
  have ha'b' : a' ≤ b' := ha'a.le.trans (hab.trans hbb'.le)
  have hpos : 0 < a' - g := tsub_pos_iff_lt.mpr hga'
  have hsub : a' - g ≤ b' - g := tsub_le_tsub_right ha'b' g
  have hsubd : b' - g < (jumpExcursion x f).lifetime := by
    rw [hs]
    exact tsub_lt_tsub_right_of_le (hga'.le.trans ha'b') hb'd
  let c := excursionWindowInf (a' - g) (b' - g) (jumpExcursion x f)
  have hc : 0 < c := hw _ _ hpos hsub hsubd
  have hbound (u : ℝ≥0) (hu : u ∈ Icc a' b') : c ≤ (reflectedFrom 0 f).1 u := by
    have hgu : g ≤ u := hgab.trans hu.1
    have hwin := windowInf_le (e := jumpExcursion x f)
      (show u - g ∈ Icc (a' - g) (b' - g) from
        ⟨tsub_le_tsub_right hu.1 g, tsub_le_tsub_right hu.2 g⟩)
    rw [he, add_tsub_cancel_of_le hgu, min_eq_left (hu.2.trans hb'd.le)] at hwin
    exact hwin
  refine ⟨c, hc, fun t hat htb => ⟨hbound t ⟨ha'a.le.trans hat, htb.trans hbb'.le⟩, ?_⟩⟩
  have hat' : a' < t := ha'a.trans_le hat
  have htb' : t < b' := htb.trans_lt hbb'
  let _ : (𝓝[<] t).NeBot := nhdsLT_neBot_of_exists_lt
    ⟨0, (show 0 ≤ a' from bot_le).trans_lt hat'⟩
  apply ge_of_tendsto ((reflectedFrom 0 f).2.tendsto_nhdsLT_leftLim t)
  have hnear : ∀ᶠ u in 𝓝 t, u ∈ Ioo a' b' := Ioo_mem_nhds hat' htb'
  filter_upwards [hnear.filter_mono nhdsWithin_le_nhds] with u hu
  exact hbound u ⟨hu.1.le, hu.2.le⟩

private theorem passage_sup {f : DLoc}
    (hT : ∀ y, firstPassageBelow y f = (passageTime y f : WithTop ℝ≥0)) (x : ℝ≥0) :
    (⨆ y : Iio x, firstPassageBelow y f) = (passageTimeMinus x f : WithTop ℝ≥0) := by
  have hb : (⨆ y : Iio x, firstPassageBelow y f) ≤ firstPassageBelow x f :=
    iSup_le fun y => firstPassageBelow_mono f y.2.le
  obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.mp
    (ne_top_of_le_ne_top (by rw [hT x]; exact WithTop.coe_ne_top) hb)
  simp only [passageTimeMinus, ← ht, WithTop.untopD_coe]

private theorem left_brackets {f : DLoc} {x : ℝ≥0} (hx : x ∈ passageJumpSet f)
    (hT : ∀ y, firstPassageBelow y f = (passageTime y f : WithTop ℝ≥0))
    (hmono : StrictMono (fun y => passageTime y f))
    (hno : ∀ q : ℚ≥0, (q : ℝ≥0) ∉ passageJumpSet f) (η : ℝ≥0) (hη : 0 < η) :
    ∃ x₁ x₂ : ℝ≥0, x₁ < x₂ ∧ x₂ < x ∧
      x₁ ∉ passageJumpSet f ∧ x₂ ∉ passageJumpSet f ∧
      passageTimeMinus x f < passageTime x₁ f + η ∧ passageTime x₂ f < passageTimeMinus x f := by
  have hg : 0 < passageTimeMinus x f :=
    (show 0 ≤ passageTime 0 f from bot_le).trans_lt
      (passageTime_lt_passageTimeMinus hT hmono hx.1)
  have hex : ∃ y : Iio x, passageTimeMinus x f < passageTime y f + η := by
    by_contra hn
    have hle : (⨆ y : Iio x, firstPassageBelow y f) ≤
        ((passageTimeMinus x f - η : ℝ≥0) : WithTop ℝ≥0) := by
      apply iSup_le
      intro y
      rw [hT y]
      have hy : passageTime y f + η ≤ passageTimeMinus x f :=
        le_of_not_gt fun h => hn ⟨y, h⟩
      exact_mod_cast le_tsub_of_add_le_right hy
    rw [passage_sup hT x] at hle
    have hle' : passageTimeMinus x f ≤ passageTimeMinus x f - η := by exact_mod_cast hle
    exact (tsub_lt_self hg hη).not_ge hle'
  obtain ⟨y, hy⟩ := hex
  obtain ⟨q₁, hyq, hqx⟩ := exists_nnrat_btwn y.2
  obtain ⟨q₂, hq₁q₂, hq₂x⟩ := exists_nnrat_btwn hqx
  refine ⟨q₁, q₂, hq₁q₂, hq₂x, hno q₁, hno q₂, ?_,
    passageTime_lt_passageTimeMinus hT hmono hq₂x⟩
  exact hy.trans_le (add_le_add (hmono.monotone hyq.le) le_rfl)

private theorem right_brackets {f : DLoc} {x : ℝ≥0}
    (hmono : StrictMono (fun y => passageTime y f))
    (hr : ContinuousWithinAt (fun y => (passageTime y f : ℝ)) (Ioi x) x)
    (hno : ∀ q : ℚ≥0, (q : ℝ≥0) ∉ passageJumpSet f) (η : ℝ≥0) (hη : 0 < η) :
    ∃ x₁ x₂ : ℝ≥0, x < x₁ ∧ x₁ < x₂ ∧
      x₁ ∉ passageJumpSet f ∧ x₂ ∉ passageJumpSet f ∧
      passageTime x f < passageTime x₁ f ∧ passageTime x₂ f < passageTime x f + η := by
  have hlt : (passageTime x f : ℝ) < (passageTime x f : ℝ) + η := by
    exact lt_add_of_pos_right _ (by exact_mod_cast hη)
  have hevent : ∀ᶠ y in 𝓝[>] x, (passageTime y f : ℝ) < (passageTime x f : ℝ) + η :=
    hr.eventually (eventually_lt_nhds hlt)
  obtain ⟨u, hxu, hu⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hevent
  obtain ⟨q₂, hxq₂, hq₂u⟩ := exists_nnrat_btwn hxu
  obtain ⟨q₁, hxq₁, hq₁q₂⟩ := exists_nnrat_btwn hxq₂
  refine ⟨q₁, q₂, hxq₁, hq₁q₂, hno q₁, hno q₂, hmono hxq₁, ?_⟩
  exact_mod_cast hu ⟨hxq₂, hq₂u⟩

/-- **A.s. supplier of the geometric facts (iii)**: every jump level is a regular excursion
level (interior bounds for values AND left limits, strict record brackets, zero endpoints). -/
theorem ae_isRegularExcursionLevel (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc),
      ∀ x ∈ passageJumpSet f, IsRegularExcursionLevel f x := by
  have hn : ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc),
      ∀ q : ℚ≥0, (q : ℝ≥0) ∉ passageJumpSet f :=
    ae_all_iff.mpr fun q => (ae_passageTimeMinus_eq_passageTime hθ q).mono
      fun f hf hx => hx.2.ne hf
  filter_upwards [ae_jumpExcursion_spec hθ, ae_jumpExcursion_support hθ,
    ae_jumpExcursion_windowInf_pos hθ, ae_passageTime_eq_firstPassageBelow hθ,
    ae_creeping_passageTime hθ, ae_isCadlag_monotone_passage hθ,
    ae_isExcursionInterval_of_jump hθ, ae_leftLim_le_stableLocalLaw hθ, hn]
    with f hs hsup hw hT hcreep hcad hi hneg hno
  intro x hx
  have hm := strictMono_passageTime_of_creeping hT.1 hcreep
  refine ⟨(hs x hx).1, (hsup x hx).2.2.2.1, ?_,
    interior_bound hx (hs x hx).2.1 (hs x hx).2.2 (hw x hx),
    left_brackets hx hT.1 hm hno, right_brackets hm (hcad.1.isRightContinuous x) hno⟩
  have hz : (reflectedFrom 0 f).1 (passageTime x f) = 0 := (hi x hx).2.2.2.2
  apply continuousAt_iff_continuous_left'_right'.mpr
  refine ⟨?_, (reflectedFrom 0 f).2.isRightContinuous _⟩
  change Tendsto (reflectedFrom 0 f).1 (𝓝[<] (passageTime x f))
    (𝓝 ((reflectedFrom 0 f).1 (passageTime x f)))
  rw [hz, ← leftLim_reflectedFrom_eq_zero_of_noNegJumps hneg hz]
  exact (reflectedFrom 0 f).2.tendsto_nhdsLT_leftLim _

end BGW.StableTrees
