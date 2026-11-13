/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.FirstLongMarkSelection
import Mathlib.Data.NNRat.Encodable

/-!
# Measurability of the first long excursion

Rational label windows detect the first long label. Their countable infimum supplies a
measurable version of the raw infimum selector on the almost-sure selection event.

Reference: J. Bertoin, *Lévy Processes*, Cambridge University Press, 1996, Chapter IV.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod
open BGW.Probability

namespace BGW.StableTrees

variable {θ : ℝ}

/-- On paths with valid excursion tags, a void long-mark window is equivalent to having
all long labels strictly beyond the end of the window. -/
theorem longCount_eq_zero_iff {f : DLoc} (hc : (passageJumpSet f).Countable)
    (hs : ∀ x ∈ passageJumpSet f,
      (jumpExcursion x f).lifetime = passageTime x f - passageTimeMinus x f) (t : ℝ≥0) :
    excursionPointMeasure f (Ioc 0 t ×ˢ {e : Excursion | 1 < e.lifetime}) = 0 ↔
      ∀ x ∈ longLabelSet f, t < x := by
  rw [excursionPointMeasure_apply hc (measurableSet_Ioc.prod
    (measurableSet_lt measurable_const measurable_excursion_lifetime)),
    ENat.toENNReal_eq_zero, Set.encard_eq_zero, eq_empty_iff_forall_notMem]
  constructor
  · intro h x hx
    by_contra hn
    apply h x
    refine ⟨hx.1, ⟨hx.1.1, le_of_not_gt hn⟩, ?_⟩
    change 1 < (jumpExcursion x f).lifetime
    rw [hs x hx.1]
    exact hx.2
  · rintro h x ⟨hx, hxt, he⟩
    have hl : x ∈ longLabelSet f := ⟨hx, by
      change 1 < (jumpExcursion x f).lifetime at he
      rwa [hs x hx] at he⟩
    exact (h x hl).not_ge hxt.2

/-- On the full-measure selection event, initial void probabilities detect the first label. -/
theorem ae_longCount_eq_zero_iff (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∀ t : ℝ≥0,
      excursionPointMeasure f (Ioc 0 t ×ˢ {e : Excursion | 1 < e.lifetime}) = 0 ↔
        t < firstLongLabel f := by
  filter_upwards [ae_passageJumpSet_countable hθ, ae_jumpExcursion_spec hθ,
    ae_exists_longLabel hθ] with f hc hs hex
  obtain ⟨L, hL⟩ := hex
  intro t
  rw [longCount_eq_zero_iff hc (fun x hx => (hs x hx).2.1),
    firstLongLabel_eq_of_isLeast hL]
  exact ⟨fun h => h L hL.1, fun h x hx => h.trans_le (hL.2 hx)⟩

private noncomputable def labelFromCounts (ξ : DLoc → Measure (ℝ≥0 × Excursion))
    (f : DLoc) : ℝ≥0∞ :=
  ⨅ q : ℚ≥0, if ξ f (Ioc 0 (q : ℝ≥0) ×ˢ {e : Excursion | 1 < e.lifetime}) = 0
    then ⊤ else ((q : ℝ≥0) : ℝ≥0∞)

private theorem measurable_labelFromCounts {ξ : DLoc → Measure (ℝ≥0 × Excursion)}
    (hξ : Measurable ξ) : Measurable (labelFromCounts ξ) := by
  classical
  apply Measurable.iInf
  intro q
  apply Measurable.ite
  · exact measurableSet_eq_fun (measurable_count hξ (measurableSet_Ioc.prod
      (measurableSet_lt measurable_const measurable_excursion_lifetime))) measurable_const
  · exact measurable_const
  · exact measurable_const

private theorem labelFromCounts_eq {ξ : DLoc → Measure (ℝ≥0 × Excursion)} {f : DLoc}
    (heq : ξ f = excursionPointMeasure f)
    (hc : ∀ t : ℝ≥0,
      excursionPointMeasure f (Ioc 0 t ×ˢ {e : Excursion | 1 < e.lifetime}) = 0 ↔
        t < firstLongLabel f) :
    labelFromCounts ξ f = (firstLongLabel f : ℝ≥0∞) := by
  classical
  apply le_antisymm
  · by_contra h
    obtain ⟨u, hLu, hu⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp (lt_of_not_ge h)
    have hLu' : (firstLongLabel f : ℝ) < u := by exact_mod_cast hLu
    obtain ⟨q, hLq, hqu⟩ := exists_rat_btwn hLu'
    let q' : ℚ≥0 := ⟨q, by exact_mod_cast ((firstLongLabel f).2.trans hLq.le)⟩
    have hLq' : firstLongLabel f < (q' : ℝ≥0) := by exact_mod_cast hLq
    have hqu' : (q' : ℝ≥0) < u := by exact_mod_cast hqu
    have hn : ξ f (Ioc 0 (q' : ℝ≥0) ×ˢ {e : Excursion | 1 < e.lifetime}) ≠ 0 := by
      rw [heq]
      exact fun hz => (not_lt_of_ge hLq'.le) ((hc q').mp hz)
    have hle : labelFromCounts ξ f ≤ ((q' : ℝ≥0) : ℝ≥0∞) := by
      apply iInf_le_of_le q'
      simp only [hn, ↓reduceIte, le_rfl]
    exact ((show ((q' : ℝ≥0) : ℝ≥0∞) < u by exact_mod_cast hqu').trans hu).not_ge hle
  · apply le_iInf
    intro q
    split_ifs with hz
    · exact le_top
    · have hLq : firstLongLabel f ≤ (q : ℝ≥0) := by
        apply le_of_not_gt
        intro h
        exact hz (heq ▸ (hc q).mpr h)
      exact_mod_cast hLq

/-- The first long label is a.e.-measurable (junk off the a.s. event). -/
theorem aemeasurable_firstLongLabel (hθ : 1 < θ ∧ θ ≤ 2) :
    AEMeasurable firstLongLabel (stableLocalLaw θ : Measure DLoc) := by
  obtain ⟨ξ, hξ, heq⟩ := exists_measurable_modification_excursionPointMeasure hθ
  refine ⟨fun f => (labelFromCounts ξ f).toNNReal,
    (measurable_labelFromCounts hξ).ennreal_toNNReal, ?_⟩
  filter_upwards [heq, ae_longCount_eq_zero_iff hθ] with f hf hc
  simpa only [ENNReal.toNNReal_coe] using
    (congrArg ENNReal.toNNReal (labelFromCounts_eq hf hc)).symm

/-- The first long mark is a.e.-measurable. -/
theorem aemeasurable_firstLongMark (hθ : 1 < θ ∧ θ ≤ 2) :
    AEMeasurable firstLongMark (stableLocalLaw θ : Measure DLoc) := by
  let P : Measure DLoc := stableLocalLaw θ
  have hL : AEMeasurable (fun f : DLoc => firstLongLabel f) P :=
    aemeasurable_firstLongLabel hθ
  have hpair : AEMeasurable
      (fun f : DLoc => ((firstLongLabel f, f) : ℝ≥0 × DLoc)) P :=
    hL.prodMk aemeasurable_id
  have hminus : Measurable (fun p : ℝ≥0 × DLoc => passageTimeMinus p.1 p.2) :=
    measurable_passageTimeMinus_uncurry
  have htime : Measurable (fun p : ℝ≥0 × DLoc => passageTime p.1 p.2) :=
    measurable_passageTime_uncurry
  have htail : Measurable (fun p : ℝ≥0 × DLoc =>
      ((passageTime p.1 p.2, p.2) : ℝ≥0 × DLoc)) :=
    htime.prodMk measurable_snd
  have hm : Measurable (fun p : ℝ≥0 × DLoc =>
      ((passageTimeMinus p.1 p.2, passageTime p.1 p.2, p.2) : ℝ≥0 × ℝ≥0 × DLoc)) :=
    hminus.prodMk htail
  have hcut : Measurable (fun q : ℝ≥0 × ℝ≥0 × DLoc =>
      excursionCut q.1 q.2.1 q.2.2) := measurable_excursionCut
  have hcomp : Measurable (fun p : ℝ≥0 × DLoc =>
      excursionCut (passageTimeMinus p.1 p.2) (passageTime p.1 p.2) p.2) :=
    hcut.comp hm
  have hfinal : AEMeasurable (fun f : DLoc =>
      excursionCut (passageTimeMinus (firstLongLabel f) f)
        (passageTime (firstLongLabel f) f) f) P :=
    hcomp.comp_aemeasurable (f := fun f : DLoc => (firstLongLabel f, f)) hpair
  exact hfinal

end BGW.StableTrees
