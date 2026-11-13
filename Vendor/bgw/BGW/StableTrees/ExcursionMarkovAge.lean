/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.StableExcursionSupport
public import BGW.StableTrees.MarkedExcursionsBasic
import BGW.StableTrees.ExcursionMeasureSupportPath
import Mathlib.Data.NNRat.Encodable

import BGW.Probability.NNReal

/-!
# Pathwise strict age-window clocks

Rational windows with a positive lower bound detect compact intervals inside excursions.
Their first strict age crossings are stopping times on every path, without modification
on a null set.

Reference: J. Bertoin, *Lévy Processes*, Cambridge University Press, 1996, Chapter IV.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open BGW.Skorokhod

open BGW.Probability

namespace BGW.StableTrees

/-- A rational window of the reflected path with a strictly positive uniform lower bound. -/
private def excursionAgeWindow (a b : ℚ≥0) (f : DLoc) : Prop :=
  ∃ m : ℕ, ∀ q : ℚ≥0, a ≤ q → q ≤ b →
    (1 : ℝ) / (m + 1) ≤ (reflectedFrom 0 f).1 q

/-- A positive rational window is measurable at its right endpoint, on every path. -/
private theorem measurableSet_excursionAgeWindow (a b : ℚ≥0) :
    MeasurableSet[DLoc.filtration (b : ℝ≥0)] {f : DLoc | excursionAgeWindow a b f} := by
  let : MeasurableSpace DLoc := DLoc.filtration (b : ℝ≥0)
  change MeasurableSet {f : DLoc | excursionAgeWindow a b f}
  simp only [excursionAgeWindow, Set.ofPred_exists]
  apply MeasurableSet.iUnion
  intro m
  rw [Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro q
  by_cases haq : a ≤ q
  · by_cases hqb : q ≤ b
    · simp only [haq, hqb, forall_const]
      have hqb' : (q : ℝ≥0) ≤ (b : ℝ≥0) := by exact_mod_cast hqb
      have hX : Measurable (fun f : DLoc => f.1 q) :=
        (DLoc.adapted_eval q).mono (DLoc.filtration.mono hqb') le_rfl
      have hI : Measurable (fun f : DLoc => runningInfLoc f q) :=
        (stronglyAdapted_runningInfLoc q).measurable.mono
          (DLoc.filtration.mono hqb') le_rfl
      exact measurableSet_le measurable_const
        (by simpa only [reflectedFrom, NNReal.coe_zero, zero_add, Pi.sub_def] using
          hX.sub ((measurable_const (a := (0 : ℝ))).min hI))
    · simp only [hqb, IsEmpty.forall_iff, implies_true, Set.ofPred_true]
      exact MeasurableSet.univ
  · simp only [haq, IsEmpty.forall_iff, Set.ofPred_true]
    exact MeasurableSet.univ

/-- The first strict age crossing after an extended restart time, detected through rational
windows. The definition is pathwise; a window must have length strictly greater than `t`. -/
private noncomputable def nextExcursionAgeTime (t : ℝ≥0) (σ : DLoc → WithTop ℝ≥0)
    (f : DLoc) : WithTop ℝ≥0 :=
  ⨅ b : ℚ≥0, ⨅ (_ : ∃ a : ℚ≥0,
    σ f ≤ ((a : ℝ≥0) : WithTop ℝ≥0) ∧
      (a : ℝ≥0) + t < (b : ℝ≥0) ∧ excursionAgeWindow a b f),
    ((b : ℝ≥0) : WithTop ℝ≥0)

/-- Strict age-window crossings after a stopping time are stopping times everywhere. -/
private theorem isStoppingTime_nextExcursionAgeTime (t : ℝ≥0) {σ : DLoc → WithTop ℝ≥0}
    (hσ : IsStoppingTime DLoc.filtration σ) :
    IsStoppingTime DLoc.filtration (nextExcursionAgeTime t σ) := by
  apply isStoppingTime_of_measurableSet_lt_of_isRightContinuous
  intro s
  let : MeasurableSpace DLoc := DLoc.filtration s
  change MeasurableSet {f : DLoc | nextExcursionAgeTime t σ f < (s : WithTop ℝ≥0)}
  have heq : {f : DLoc | nextExcursionAgeTime t σ f < (s : WithTop ℝ≥0)} =
      ⋃ b : ℚ≥0, ⋃ (_ : (b : ℝ≥0) < s), ⋃ a : ℚ≥0,
        {f : DLoc | σ f ≤ ((a : ℝ≥0) : WithTop ℝ≥0) ∧
          (a : ℝ≥0) + t < (b : ℝ≥0) ∧ excursionAgeWindow a b f} := by
    ext f
    simp only [nextExcursionAgeTime, iInf_lt_iff, WithTop.coe_lt_coe,
      Set.mem_ofPred_eq, Set.mem_iUnion]
    aesop
  rw [heq]
  apply MeasurableSet.iUnion
  intro b
  apply MeasurableSet.iUnion
  intro hbs
  apply MeasurableSet.iUnion
  intro a
  by_cases hab : (a : ℝ≥0) + t < (b : ℝ≥0)
  · have has : (a : ℝ≥0) ≤ s :=
      (le_add_of_nonneg_right (bot_le : (0 : ℝ≥0) ≤ t)).trans (hab.trans hbs).le
    have hwin := DLoc.filtration.mono hbs.le _ (measurableSet_excursionAgeWindow a b)
    simpa only [hab, true_and, Set.ofPred_and] using
      (DLoc.filtration.mono has _ (hσ (a : ℝ≥0))).inter hwin
  · simp only [hab, false_and, and_false, Set.ofPred_false]
    exact MeasurableSet.empty
/-- First new strict infimum after a stopping time, using only rational observations strictly
after that time. This avoids a weak hitting-time measurability assumption. -/
private noncomputable def excursionAgeRestart (τ : DLoc → WithTop ℝ≥0) (f : DLoc) :
    WithTop ℝ≥0 :=
  ⨅ q : ℚ≥0, ⨅ (_ : ∃ r : ℚ≥0,
    τ f < ((r : ℝ≥0) : WithTop ℝ≥0) ∧ r < q ∧ f.1 q < runningInfLoc f r),
    ((q : ℝ≥0) : WithTop ℝ≥0)

/-- The rational strict-infimum restart is a stopping time everywhere. -/
private theorem isStoppingTime_excursionAgeRestart {τ : DLoc → WithTop ℝ≥0}
    (hτ : IsStoppingTime DLoc.filtration τ) :
    IsStoppingTime DLoc.filtration (excursionAgeRestart τ) := by
  apply isStoppingTime_of_measurableSet_lt_of_isRightContinuous
  intro s
  let : MeasurableSpace DLoc := DLoc.filtration s
  change MeasurableSet {f : DLoc | excursionAgeRestart τ f < (s : WithTop ℝ≥0)}
  have heq : {f : DLoc | excursionAgeRestart τ f < (s : WithTop ℝ≥0)} =
      ⋃ q : ℚ≥0, ⋃ (_ : (q : ℝ≥0) < s), ⋃ r : ℚ≥0, ⋃ (_ : r < q),
        {f : DLoc | τ f < ((r : ℝ≥0) : WithTop ℝ≥0) ∧ f.1 q < runningInfLoc f r} := by
    ext f
    simp only [excursionAgeRestart, iInf_lt_iff, WithTop.coe_lt_coe,
      Set.mem_ofPred_eq, Set.mem_iUnion]
    aesop
  rw [heq]
  apply MeasurableSet.iUnion
  intro q
  apply MeasurableSet.iUnion
  intro hqs
  apply MeasurableSet.iUnion
  intro r
  apply MeasurableSet.iUnion
  intro hrq
  have hrs : (r : ℝ≥0) ≤ s := by
    have hrq' : (r : ℝ≥0) < (q : ℝ≥0) := by exact_mod_cast hrq
    exact (hrq'.trans hqs).le
  have hX : Measurable (fun f : DLoc => f.1 q) :=
    (DLoc.adapted_eval q).mono (DLoc.filtration.mono hqs.le) le_rfl
  have hI : Measurable (fun f : DLoc => runningInfLoc f r) :=
    (stronglyAdapted_runningInfLoc r).measurable.mono
      (DLoc.filtration.mono hrs) le_rfl
  simpa only [Set.ofPred_and] using
    (DLoc.filtration.mono hrs _ (hτ.measurableSet_lt r)).inter (measurableSet_lt hX hI)

/-- The strict-infimum restart never precedes its input clock, on any path. -/
private theorem le_excursionAgeRestart (τ : DLoc → WithTop ℝ≥0) (f : DLoc) :
    τ f ≤ excursionAgeRestart τ f := by
  apply le_iInf
  intro q
  apply le_iInf
  rintro ⟨r, hτr, hrq, _⟩
  exact hτr.le.trans (WithTop.coe_le_coe.mpr (by exact_mod_cast hrq.le))

/-- Every rational age-window crossing occurs at least one age after its input clock. -/
private theorem add_le_nextExcursionAgeTime (t : ℝ≥0) (σ : DLoc → WithTop ℝ≥0) (f : DLoc) :
    σ f + (t : WithTop ℝ≥0) ≤ nextExcursionAgeTime t σ f := by
  apply le_iInf
  intro b
  apply le_iInf
  rintro ⟨a, hσa, hab, _⟩
  calc
    σ f + (t : WithTop ℝ≥0) ≤ ((a : ℝ≥0) : WithTop ℝ≥0) + (t : WithTop ℝ≥0) :=
      add_le_add hσa le_rfl
    _ = (((a : ℝ≥0) + t : ℝ≥0) : WithTop ℝ≥0) := by rw [WithTop.coe_add]
    _ ≤ ((b : ℝ≥0) : WithTop ℝ≥0) := WithTop.coe_le_coe.mpr hab.le

/-- A rational positive window is positive at every real time in the window, including
both endpoints. Right-continuity propagates the rational lower bound. -/
private theorem excursionAgeWindow_pos {a b : ℚ≥0} {f : DLoc} (hw : excursionAgeWindow a b f)
    {u : ℝ≥0} (hau : (a : ℝ≥0) ≤ u) (hub : u ≤ (b : ℝ≥0)) :
    0 < (reflectedFrom 0 f).1 u := by
  obtain ⟨m, hm⟩ := hw
  have hε : (0 : ℝ) < 1 / (m + 1) := by positivity
  rcases hub.eq_or_lt with rfl | hub
  · exact hε.trans_le (hm b (by exact_mod_cast hau) le_rfl)
  · by_contra hn
    have hlt : (reflectedFrom 0 f).1 u < 1 / (m + 1) :=
      (le_of_not_gt hn).trans_lt hε
    have hnhds : (reflectedFrom 0 f).1 ⁻¹' Iio (1 / (m + 1 : ℝ)) ∈ 𝓝[>] u :=
      ((reflectedFrom 0 f).2.isRightContinuous u) (isOpen_Iio.mem_nhds hlt)
    obtain ⟨v, huv, hsub⟩ := (mem_nhdsGT_iff_exists_mem_Ioc_Ioo_subset hub).1 hnhds
    obtain ⟨q, huq, hqv⟩ := exists_nnrat_btwn huv.1
    have haq : a ≤ q := by exact_mod_cast hau.trans huq.le
    have hqb : q ≤ b := by exact_mod_cast (hqv.le.trans huv.2)
    exact (not_lt_of_ge (hm q haq hqb)) (hsub ⟨huq, hqv⟩)

/-- Almost surely every positive rational window lies strictly inside one passage excursion.
In particular it cannot cross an excursion endpoint. -/
private theorem ae_excursionAgeWindow_interval {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∀ a b : ℚ≥0, a ≤ b →
      excursionAgeWindow a b f → ∃ x ∈ passageJumpSet f,
        passageTimeMinus x f < (a : ℝ≥0) ∧ (b : ℝ≥0) < passageTime x f := by
  filter_upwards [ae_pos_set_eq_iUnion_jump_intervals hθ,
    ae_isExcursionInterval_of_jump hθ] with f hpos hi a b hab hw
  have hab' : (a : ℝ≥0) ≤ (b : ℝ≥0) := by exact_mod_cast hab
  have ha : (a : ℝ≥0) ∈ {s : ℝ≥0 | 0 < (reflectedFrom 0 f).1 s} :=
    excursionAgeWindow_pos hw le_rfl hab'
  rw [hpos] at ha
  obtain ⟨x, hx, hax⟩ := Set.mem_iUnion₂.mp ha
  refine ⟨x, hx, hax.1, ?_⟩
  by_contra hn
  have hd := excursionAgeWindow_pos hw hax.2.le (le_of_not_gt hn)
  rw [(hi x hx).2.2.2.2] at hd
  exact lt_irrefl 0 hd

private theorem excursion_windowInf_le_eval {e : Excursion} {a b u : ℝ≥0}
    (hu : u ∈ Icc a b) : excursionWindowInf a b e ≤ e.path.1 u := by
  let W := DLoc.restrict (b - a) (DLoc.shift a e.path)
  let s : Icc (0 : ℝ) ((b - a : ℝ≥0) : ℝ) :=
    ⟨((u - a : ℝ≥0) : ℝ), (u - a).2, by exact_mod_cast tsub_le_tsub_right hu.2 a⟩
  calc
    excursionWindowInf a b e ≤ W s + e.path.1 a := by
      change (⨅ s, W s) + e.path.1 a ≤ _
      exact add_le_add (ciInf_le (isBounded_range W).bddBelow s) le_rfl
    _ = e.path.1 u := by
      change e.path.1 (a + (u - a)) - e.path.1 a + e.path.1 a = _
      rw [add_tsub_cancel_of_le hu.1, sub_add_cancel]

/-- Almost surely every compact rational window strictly inside a passage excursion has a
positive rational lower bound, simultaneously over windows and excursion labels. -/
private theorem ae_excursionAgeWindow_of_interval {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∀ x ∈ passageJumpSet f,
      ∀ a b : ℚ≥0, a ≤ b → passageTimeMinus x f < (a : ℝ≥0) →
        (b : ℝ≥0) < passageTime x f → excursionAgeWindow a b f := by
  filter_upwards [ae_jumpExcursion_windowInf_pos hθ, ae_jumpExcursion_spec hθ]
    with f hwin hspec x hx a b hab hga hbd
  have hab' : (a : ℝ≥0) ≤ (b : ℝ≥0) := by exact_mod_cast hab
  have hp : 0 < excursionWindowInf ((a : ℝ≥0) - passageTimeMinus x f)
      ((b : ℝ≥0) - passageTimeMinus x f) (jumpExcursion x f) := by
    apply hwin x hx _ _ (tsub_pos_of_lt hga) (tsub_le_tsub_right hab' _)
    rw [(hspec x hx).2.1, lt_tsub_iff_right,
      tsub_add_cancel_of_le (hga.le.trans hab')]
    exact hbd
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt hp
  refine ⟨m, fun q haq hqb => ?_⟩
  have haq' : (a : ℝ≥0) ≤ (q : ℝ≥0) := by exact_mod_cast haq
  have hqb' : (q : ℝ≥0) ≤ (b : ℝ≥0) := by exact_mod_cast hqb
  have heval := (hspec x hx).2.2 ((q : ℝ≥0) - passageTimeMinus x f)
  rw [add_tsub_cancel_of_le (hga.le.trans haq'),
    min_eq_left (hqb'.trans hbd.le)] at heval
  rw [← heval]
  exact hm.le.trans (excursion_windowInf_le_eval
    ⟨tsub_le_tsub_right haq' _, tsub_le_tsub_right hqb' _⟩)

private lemma nextExcursionAgeTime_le_of_interval {f : DLoc} {t : ℝ≥0}
    (hwin : ∀ x ∈ passageJumpSet f, ∀ a b : ℚ≥0, a ≤ b →
      passageTimeMinus x f < (a : ℝ≥0) → (b : ℝ≥0) < passageTime x f →
        excursionAgeWindow a b f)
    {σ : DLoc → WithTop ℝ≥0} {x : ℝ≥0} (hx : x ∈ passageJumpSet f)
    (hσx : σ f ≤ (passageTimeMinus x f : WithTop ℝ≥0))
    (htx : passageTimeMinus x f + t < passageTime x f) :
    nextExcursionAgeTime t σ f ≤ ((passageTimeMinus x f + t : ℝ≥0) : WithTop ℝ≥0) := by
  apply le_of_forall_gt_imp_ge_of_dense
  intro r hr
  induction r using WithTop.recTopCoe with
  | top => exact le_top
  | coe r =>
    have hcross : passageTimeMinus x f + t < r := WithTop.coe_lt_coe.mp hr
    obtain ⟨b, hcb, hbr⟩ := exists_nnrat_btwn (lt_min hcross htx)
    have hbr' : (b : ℝ≥0) < r := hbr.trans_le (min_le_left _ _)
    have hbd : (b : ℝ≥0) < passageTime x f := hbr.trans_le (min_le_right _ _)
    obtain ⟨a, hga, hab⟩ := exists_nnrat_btwn (lt_tsub_iff_right.mpr hcb)
    have habt : (a : ℝ≥0) + t < (b : ℝ≥0) := lt_tsub_iff_right.mp hab
    have hab' : a ≤ b := by
      exact_mod_cast (le_add_of_nonneg_right (bot_le : (0 : ℝ≥0) ≤ t)).trans habt.le
    have hσa := hσx.trans (WithTop.coe_le_coe.mpr hga.le)
    exact (iInf_le_of_le b (iInf_le _ ⟨a, hσa, habt, hwin x hx a b hab' hga hbd⟩)).trans
      (WithTop.coe_le_coe.mpr hbr'.le)

private lemma age_window_label {f : DLoc} {t : ℝ≥0} {σ : DLoc → WithTop ℝ≥0}
    (hi : ∀ x ∈ passageJumpSet f,
      IsExcursionInterval f (passageTimeMinus x f) (passageTime x f))
    (hinside : ∀ a b : ℚ≥0, a ≤ b → excursionAgeWindow a b f →
      ∃ x ∈ passageJumpSet f, passageTimeMinus x f < (a : ℝ≥0) ∧
        (b : ℝ≥0) < passageTime x f)
    (hzero : ∀ s : ℝ≥0, σ f = (s : WithTop ℝ≥0) → (reflectedFrom 0 f).1 s = 0)
    {a b : ℚ≥0} (hσa : σ f ≤ ((a : ℝ≥0) : WithTop ℝ≥0))
    (habt : (a : ℝ≥0) + t < (b : ℝ≥0)) (hw : excursionAgeWindow a b f) :
    ∃ x ∈ passageJumpSet f, σ f ≤ (passageTimeMinus x f : WithTop ℝ≥0) ∧
      passageTimeMinus x f + t < (b : ℝ≥0) ∧ (b : ℝ≥0) < passageTime x f := by
  have hab : a ≤ b := by
    exact_mod_cast (le_add_of_nonneg_right (bot_le : (0 : ℝ≥0) ≤ t)).trans habt.le
  obtain ⟨x, hx, hga, hbd⟩ := hinside a b hab hw
  refine ⟨x, hx, ?_, (add_lt_add_of_lt_of_le hga (le_rfl : t ≤ t)).trans habt, hbd⟩
  obtain ⟨s, hs⟩ := WithTop.ne_top_iff_exists.mp
    (ne_top_of_le_ne_top WithTop.coe_ne_top hσa)
  have hsa : s ≤ (a : ℝ≥0) := by
    simpa only [← hs, WithTop.coe_le_coe] using hσa
  rw [← hs, WithTop.coe_le_coe]
  by_contra hn
  have hab' : (a : ℝ≥0) ≤ (b : ℝ≥0) := by exact_mod_cast hab
  have hpos := (hi x hx).2.1 s (lt_of_not_ge hn) (hsa.trans_lt (hab'.trans_lt hbd))
  exact (ne_of_gt hpos) (hzero s hs.symm)

private lemma exists_label_nextExcursionAgeTime {f : DLoc} {t : ℝ≥0} (ht : 0 < t)
    (hi : ∀ x ∈ passageJumpSet f,
      IsExcursionInterval f (passageTimeMinus x f) (passageTime x f))
    (hinside : ∀ a b : ℚ≥0, a ≤ b → excursionAgeWindow a b f →
      ∃ x ∈ passageJumpSet f, passageTimeMinus x f < (a : ℝ≥0) ∧
        (b : ℝ≥0) < passageTime x f)
    (hwin : ∀ x ∈ passageJumpSet f, ∀ a b : ℚ≥0, a ≤ b →
      passageTimeMinus x f < (a : ℝ≥0) → (b : ℝ≥0) < passageTime x f →
        excursionAgeWindow a b f)
    (hdisj : ∀ x ∈ passageJumpSet f, ∀ y ∈ passageJumpSet f, x < y →
      passageTime x f < passageTimeMinus y f)
    {σ : DLoc → WithTop ℝ≥0}
    (hzero : ∀ s : ℝ≥0, σ f = (s : WithTop ℝ≥0) → (reflectedFrom 0 f).1 s = 0)
    (hfin : nextExcursionAgeTime t σ f < ⊤) :
    ∃ x ∈ passageJumpSet f, σ f ≤ (passageTimeMinus x f : WithTop ℝ≥0) ∧
      passageTimeMinus x f + t < passageTime x f ∧
      nextExcursionAgeTime t σ f =
        ((passageTimeMinus x f + t : ℝ≥0) : WithTop ℝ≥0) := by
  have hwitness (r : ℝ≥0) (hr : nextExcursionAgeTime t σ f < (r : WithTop ℝ≥0)) :
      ∃ b : ℚ≥0, (∃ a : ℚ≥0, σ f ≤ ((a : ℝ≥0) : WithTop ℝ≥0) ∧
        (a : ℝ≥0) + t < (b : ℝ≥0) ∧ excursionAgeWindow a b f) ∧ (b : ℝ≥0) < r := by
    simpa only [nextExcursionAgeTime, iInf_lt_iff, WithTop.coe_lt_coe, exists_prop] using hr
  obtain ⟨v, hv⟩ := WithTop.ne_top_iff_exists.mp hfin.ne
  obtain ⟨b, ⟨a, hσa, habt, hw⟩, hb⟩ := hwitness (v + t) (by
    rw [← hv, WithTop.coe_lt_coe]
    exact lt_add_of_pos_right v ht)
  obtain ⟨x, hx, hσx, hxb, hbd⟩ := age_window_label hi hinside hzero hσa habt hw
  have htx : passageTimeMinus x f + t < passageTime x f := hxb.trans hbd
  have hvx : v ≤ passageTimeMinus x f + t := by
    have h := nextExcursionAgeTime_le_of_interval hwin hx hσx htx
    simpa only [← hv, WithTop.coe_le_coe] using h
  have hxv : passageTimeMinus x f + t ≤ v := by
    by_contra hn
    have hvc : v < passageTimeMinus x f + t := lt_of_not_ge hn
    obtain ⟨b', ⟨a', hσa', habt', hw'⟩, hb'⟩ :=
      hwitness (min (passageTimeMinus x f + t) (v + t)) (by
        rw [← hv, WithTop.coe_lt_coe]
        exact lt_min hvc (lt_add_of_pos_right v ht))
    obtain ⟨y, hy, hσy, hyb, hbd'⟩ := age_window_label hi hinside hzero hσa' habt' hw'
    have hty : passageTimeMinus y f + t < passageTime y f := hyb.trans hbd'
    have hyx : passageTimeMinus y f + t < passageTimeMinus x f + t :=
      hyb.trans (hb'.trans_le (min_le_left _ _))
    have hvy : v ≤ passageTimeMinus y f + t := by
      have h := nextExcursionAgeTime_le_of_interval hwin hy hσy hty
      simpa only [← hv, WithTop.coe_le_coe] using h
    rcases lt_trichotomy x y with hxy | rfl | hyx'
    · have hxy' := htx.trans (hdisj x hx y hy hxy)
      exact hyx.not_ge (hxy'.le.trans (le_add_of_nonneg_right (bot_le)))
    · exact (lt_irrefl _ hyx)
    · have hgap := add_lt_add_of_lt_of_le (hty.trans (hdisj y hy x hx hyx')) (le_rfl : t ≤ t)
      exact ((add_le_add hvy (le_rfl : t ≤ t)).trans_lt hgap).not_ge (hxb.trans hb).le
  refine ⟨x, hx, hσx, htx, ?_⟩
  rw [← hv, le_antisymm hvx hxv]

private lemma exists_nnrat_right_below {f : DLoc} {u s : ℝ≥0} {c : ℝ}
    (hus : u < s) (hu : f.1 u < c) :
    ∃ q : ℚ≥0, u < (q : ℝ≥0) ∧ (q : ℝ≥0) < s ∧ f.1 q < c := by
  have hnhds : f.1 ⁻¹' Iio c ∈ 𝓝[>] u :=
    (f.2.isRightContinuous u) (isOpen_Iio.mem_nhds hu)
  obtain ⟨v, huv, hsub⟩ := (mem_nhdsGT_iff_exists_mem_Ioc_Ioo_subset hus).1 hnhds
  obtain ⟨q, huq, hqv⟩ := exists_nnrat_btwn huv.1
  exact ⟨q, huq, hqv.trans_le huv.2, hsub ⟨huq, hqv⟩⟩

private lemma excursionAgeRestart_eq_of_passage {f : DLoc} {τ : DLoc → WithTop ℝ≥0}
    {x a d : ℝ≥0} (hτ : τ f = (a : WithTop ℝ≥0)) (had : a < d)
    (hT : firstPassageBelow x f = (d : WithTop ℝ≥0))
    (hI : ∀ r : ℝ≥0, a ≤ r → r ≤ d → runningInfLoc f r = -(x : ℝ)) :
    excursionAgeRestart τ f = (d : WithTop ℝ≥0) := by
  apply le_antisymm
  · apply le_of_forall_gt_imp_ge_of_dense
    intro s hs
    induction s using WithTop.recTopCoe with
    | top => exact le_top
    | coe s =>
      have hds : d < s := WithTop.coe_lt_coe.mp hs
      obtain ⟨r, har, hrd⟩ := exists_nnrat_btwn had
      obtain ⟨u, hus, hu⟩ := exists_eval_lt_of_firstPassageBelow_lt (x := x)
        (by rw [hT]; exact_mod_cast hds)
      obtain ⟨q, huq, hqs, hq⟩ := exists_nnrat_right_below hus hu
      have hdu : d ≤ u := by
        have hle := firstPassageBelow_le_of_eval_lt hu
        simpa only [hT, WithTop.coe_le_coe] using hle
      have hrq : r < q := by exact_mod_cast hrd.trans_le (hdu.trans huq.le)
      have htest : τ f < ((r : ℝ≥0) : WithTop ℝ≥0) ∧
          r < q ∧ f.1 q < runningInfLoc f r := by
        refine ⟨?_, hrq, ?_⟩
        · rw [hτ, WithTop.coe_lt_coe]
          exact har
        · rw [hI r har.le hrd.le]
          exact hq
      have hle : excursionAgeRestart τ f ≤ ((q : ℝ≥0) : WithTop ℝ≥0) :=
        iInf_le_of_le q (iInf_le _ ⟨r, htest⟩)
      exact hle.trans (WithTop.coe_le_coe.mpr hqs.le)
  · apply le_iInf
    intro q
    apply le_iInf
    rintro ⟨r, hτr, _hrq, hq⟩
    have har : a < (r : ℝ≥0) := by
      simpa only [hτ, WithTop.coe_lt_coe] using hτr
    have hIr : runningInfLoc f r ≤ -(x : ℝ) :=
      (runningInfLoc_antitone f har.le).trans_eq (hI a le_rfl had.le)
    have hle := firstPassageBelow_le_of_eval_lt (hq.trans_le hIr)
    rwa [hT] at hle

/-- Successive restart times for the strict age-window construction. Index zero is the
initial time; index `n + 1` is the end of the excursion selected at stage `n`. -/
private noncomputable def excursionAgeRestarts (t : ℝ≥0) : ℕ → DLoc → WithTop ℝ≥0
  | 0 => fun _ => 0
  | n + 1 => excursionAgeRestart (nextExcursionAgeTime t (excursionAgeRestarts t n))

/-- Successive strict age crossings, defined pathwise after the preceding restart. -/
private noncomputable def excursionAgeCrossings (t : ℝ≥0) (n : ℕ) : DLoc → WithTop ℝ≥0 :=
  nextExcursionAgeTime t (excursionAgeRestarts t n)

/-- Every restart in the age-window construction is a stopping time on all paths. -/
private theorem isStoppingTime_excursionAgeRestarts (t : ℝ≥0) (n : ℕ) :
    IsStoppingTime DLoc.filtration (excursionAgeRestarts t n) := by
  induction n with
  | zero => exact isStoppingTime_const _ 0
  | succ n hn =>
    exact isStoppingTime_excursionAgeRestart (isStoppingTime_nextExcursionAgeTime t hn)

/-- Every crossing in the age-window construction is a stopping time on all paths. -/
private theorem isStoppingTime_excursionAgeCrossings (t : ℝ≥0) (n : ℕ) :
    IsStoppingTime DLoc.filtration (excursionAgeCrossings t n) :=
  isStoppingTime_nextExcursionAgeTime t (isStoppingTime_excursionAgeRestarts t n)

private lemma age_clocks_order (t : ℝ≥0) (n : ℕ) (f : DLoc) :
    excursionAgeRestarts t n f ≤ excursionAgeCrossings t n f ∧
      excursionAgeCrossings t n f ≤ excursionAgeRestarts t (n + 1) f := by
  refine ⟨?_, le_excursionAgeRestart _ f⟩
  exact (le_add_of_nonneg_right (bot_le : (0 : WithTop ℝ≥0) ≤ t)).trans
    (add_le_nextExcursionAgeTime t _ f)

private lemma age_restarts_mono (t : ℝ≥0) (f : DLoc) :
    Monotone (fun n => excursionAgeRestarts t n f) := by
  apply monotone_nat_of_le_succ
  intro n
  exact (age_clocks_order t n f).1.trans (age_clocks_order t n f).2

private lemma age_restarts_lower (t : ℝ≥0) (n : ℕ) (f : DLoc) :
    (((n : ℝ≥0) * t : ℝ≥0) : WithTop ℝ≥0) ≤ excursionAgeRestarts t n f := by
  induction n with
  | zero => simp [excursionAgeRestarts]
  | succ n hn =>
    calc
      ((((n + 1 : ℕ) : ℝ≥0) * t : ℝ≥0) : WithTop ℝ≥0) =
          (((n : ℝ≥0) * t : ℝ≥0) : WithTop ℝ≥0) + (t : WithTop ℝ≥0) := by
        rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul, WithTop.coe_add]
      _ ≤ excursionAgeRestarts t n f + (t : WithTop ℝ≥0) := add_le_add hn le_rfl
      _ ≤ excursionAgeCrossings t n f := add_le_nextExcursionAgeTime t _ f
      _ ≤ excursionAgeRestarts t (n + 1) f := (age_clocks_order t n f).2

/-- **Age-clock supplier** (selected age-crossing times `τ n` and restart times `ρ n`, stopping
times of the right-continuous filtration, exact-once coverage of the excursions surviving to
age `t`; strict crossings exclude lifetime exactly `t`). -/
theorem exists_excursionAge_stoppingTimes {θ : ℝ}
    (hθ : 1 < θ ∧ θ ≤ 2) (t : ℝ≥0) (ht : 0 < t) :
    ∃ τ ρ : ℕ → DLoc → WithTop ℝ≥0,
      (∀ n, IsStoppingTime DLoc.filtration (τ n)) ∧
      (∀ n, IsStoppingTime DLoc.filtration (ρ n)) ∧
      (∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc),
        (∀ x ∈ passageJumpSet f,
          t < (jumpExcursion x f).lifetime →
          ∃! n : ℕ,
            τ n f = ((passageTimeMinus x f + t : ℝ≥0) : WithTop ℝ≥0) ∧
            ρ n f = ((passageTime x f : ℝ≥0) : WithTop ℝ≥0)) ∧
        (∀ n, τ n f < ⊤ →
          ∃ x ∈ passageJumpSet f,
            t < (jumpExcursion x f).lifetime ∧
            τ n f = ((passageTimeMinus x f + t : ℝ≥0) : WithTop ℝ≥0) ∧
            ρ n f = ((passageTime x f : ℝ≥0) : WithTop ℝ≥0)) ∧
        (∀ n, τ n f < ⊤ → τ n f < ρ n f) ∧
        (∀ n, ρ n f ≤ τ (n + 1) f)) := by
  refine ⟨excursionAgeCrossings t, fun n => excursionAgeRestarts t (n + 1),
    isStoppingTime_excursionAgeCrossings t,
    fun n => isStoppingTime_excursionAgeRestarts t (n + 1), ?_⟩
  filter_upwards [ae_isExcursionInterval_of_jump hθ, ae_excursionAgeWindow_interval hθ,
    ae_excursionAgeWindow_of_interval hθ, ae_jump_intervals_disjoint hθ,
    ae_localTime_passageTime hθ, ae_passageTime_eq_firstPassageBelow hθ,
    ae_jumpExcursion_spec hθ, ae_eval_zero_stableLocalLaw hθ]
    with f hi hinside hwin hdisj hL hP he h0
  have hI (x r : ℝ≥0) (hgr : passageTimeMinus x f ≤ r) (hrd : r ≤ passageTime x f) :
      runningInfLoc f r = -(x : ℝ) := by
    have hd := (hL x).1
    have hg := (hL x).2
    dsimp only [localTime] at hd hg
    have hlow := runningInfLoc_antitone f hrd
    have hupp := runningInfLoc_antitone f hgr
    linarith
  have hR0 : (reflectedFrom 0 f).1 0 = 0 := by
    have hL0 := (hL 0).1
    rw [hP.2] at hL0
    dsimp only [localTime] at hL0
    have hI0 : runningInfLoc f 0 = 0 := by simpa using hL0
    rw [reflectedFrom_zero_apply h0, h0, hI0, sub_self]
  have hrestart {n : ℕ} {x : ℝ≥0}
      (hn : excursionAgeCrossings t n f =
        ((passageTimeMinus x f + t : ℝ≥0) : WithTop ℝ≥0))
      (hxd : passageTimeMinus x f + t < passageTime x f) :
      excursionAgeRestarts t (n + 1) f = (passageTime x f : WithTop ℝ≥0) := by
    apply excursionAgeRestart_eq_of_passage hn hxd (hP.1 x)
    intro r har hrd
    exact hI x r ((le_add_of_nonneg_right (bot_le : (0 : ℝ≥0) ≤ t)).trans har) hrd
  have hzeros : ∀ n : ℕ, ∀ s : ℝ≥0,
      excursionAgeRestarts t n f = (s : WithTop ℝ≥0) → (reflectedFrom 0 f).1 s = 0 := by
    intro n
    induction n with
    | zero =>
      intro s hs
      change (0 : WithTop ℝ≥0) = (s : WithTop ℝ≥0) at hs
      have hs0 : s = 0 := by exact_mod_cast hs.symm
      simpa only [hs0] using hR0
    | succ n hn =>
      intro s hs
      have hfin : excursionAgeCrossings t n f < ⊤ :=
        (age_clocks_order t n f).2.trans_lt (by rw [hs]; exact WithTop.coe_lt_top _)
      obtain ⟨x, hx, _hσx, hxd, hnx⟩ :=
        exists_label_nextExcursionAgeTime ht hi hinside hwin hdisj hn hfin
      have hxend := hrestart hnx hxd
      have hsd : s = passageTime x f := by exact_mod_cast hs.symm.trans hxend
      rw [hsd]
      exact (hi x hx).2.2.2.2
  have hclass (n : ℕ) (hfin : excursionAgeCrossings t n f < ⊤) :
      ∃ x ∈ passageJumpSet f,
        excursionAgeRestarts t n f ≤ (passageTimeMinus x f : WithTop ℝ≥0) ∧
        passageTimeMinus x f + t < passageTime x f ∧
        excursionAgeCrossings t n f =
          ((passageTimeMinus x f + t : ℝ≥0) : WithTop ℝ≥0) ∧
        excursionAgeRestarts t (n + 1) f = (passageTime x f : WithTop ℝ≥0) := by
    obtain ⟨x, hx, hσx, hxd, hnx⟩ :=
      exists_label_nextExcursionAgeTime ht hi hinside hwin hdisj (hzeros n) hfin
    exact ⟨x, hx, hσx, hxd, hnx, hrestart hnx hxd⟩
  have hstrict (n : ℕ) (hfin : excursionAgeCrossings t n f < ⊤) :
      excursionAgeCrossings t n f < excursionAgeRestarts t (n + 1) f := by
    obtain ⟨x, _hx, _hσx, hxd, hnx, hρx⟩ := hclass n hfin
    rw [hnx, hρx, WithTop.coe_lt_coe]
    exact hxd
  have huniq (x : ℝ≥0) {n m : ℕ}
      (hn : excursionAgeCrossings t n f =
        ((passageTimeMinus x f + t : ℝ≥0) : WithTop ℝ≥0))
      (hm : excursionAgeCrossings t m f =
        ((passageTimeMinus x f + t : ℝ≥0) : WithTop ℝ≥0)) : n = m := by
    have hnfin : excursionAgeCrossings t n f < ⊤ := by rw [hn]; exact WithTop.coe_lt_top _
    have hmfin : excursionAgeCrossings t m f < ⊤ := by rw [hm]; exact WithTop.coe_lt_top _
    rcases lt_trichotomy n m with hnm | hnm | hmn
    · have hle := (age_restarts_mono t f (Nat.succ_le_of_lt hnm)).trans
        (age_clocks_order t m f).1
      have hlt := (hstrict n hnfin).trans_le hle
      rw [hn, hm] at hlt
      exact (lt_irrefl _ hlt).elim
    · exact hnm
    · have hle := (age_restarts_mono t f (Nat.succ_le_of_lt hmn)).trans
        (age_clocks_order t n f).1
      have hlt := (hstrict m hmfin).trans_le hle
      rw [hn, hm] at hlt
      exact (lt_irrefl _ hlt).elim
  refine ⟨?_, ?_, hstrict, ?_⟩
  · intro x hx htζ
    have hxd : passageTimeMinus x f + t < passageTime x f := by
      rw [← lt_tsub_iff_left, ← (he x hx).2.1]
      exact htζ
    have hex : ∃ n : ℕ, excursionAgeCrossings t n f =
        ((passageTimeMinus x f + t : ℝ≥0) : WithTop ℝ≥0) := by
      by_contra hn
      push Not at hn
      have hbefore : ∀ n : ℕ,
          excursionAgeRestarts t n f ≤ (passageTimeMinus x f : WithTop ℝ≥0) := by
        intro n
        induction n with
        | zero => exact bot_le
        | succ n hprev =>
          have hle := nextExcursionAgeTime_le_of_interval hwin hx hprev hxd
          have hfin : excursionAgeCrossings t n f < ⊤ := hle.trans_lt (WithTop.coe_lt_top _)
          obtain ⟨y, hy, _hσy, hyd, hny, hρy⟩ := hclass n hfin
          have hcross : passageTimeMinus y f + t ≤ passageTimeMinus x f + t := by
            change excursionAgeCrossings t n f ≤ _ at hle
            simpa only [hny, WithTop.coe_le_coe] using hle
          have hyx : y < x := by
            rcases lt_trichotomy y x with hyx | rfl | hxy
            · exact hyx
            · exact (hn n hny).elim
            · have hxy' := hxd.trans (hdisj x hx y hy hxy)
              exact ((not_lt_of_ge hcross)
                (hxy'.trans_le (le_add_of_nonneg_right (bot_le)))).elim
          rw [hρy, WithTop.coe_le_coe]
          exact (hdisj y hy x hx hyx).le
      obtain ⟨n, hnlarge⟩ := exists_nat_gt ((passageTimeMinus x f : ℝ) / (t : ℝ))
      have hnt : passageTimeMinus x f < (n : ℝ≥0) * t := by
        apply NNReal.coe_lt_coe.mp
        simpa only [NNReal.coe_mul, NNReal.coe_natCast] using
          (div_lt_iff₀ (NNReal.coe_pos.mpr ht)).mp hnlarge
      have hbound := (age_restarts_lower t n f).trans (hbefore n)
      exact hnt.not_ge (WithTop.coe_le_coe.mp hbound)
    obtain ⟨n, hn⟩ := hex
    have hnfin : excursionAgeCrossings t n f < ⊤ := by rw [hn]; exact WithTop.coe_lt_top _
    have hρ := hrestart hn hxd
    refine ⟨n, ⟨hn, hρ⟩, ?_⟩
    intro m hm
    exact huniq x hm.1 hn
  · intro n hfin
    obtain ⟨x, hx, _hσx, hxd, hnx, hρx⟩ := hclass n hfin
    refine ⟨x, hx, ?_, hnx, hρx⟩
    rw [(he x hx).2.1, lt_tsub_iff_left]
    exact hxd
  · intro n
    exact (age_clocks_order t (n + 1) f).1

end BGW.StableTrees
