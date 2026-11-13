/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.StableExcursionSupportPath
import BGW.StableTrees.StableLocalMarkov
import Mathlib.Data.NNRat.Encodable

/-!
# Minimum uniqueness on rational windows

Window adapters using barrier inequalities, without assuming an excursion candidate (J. Bertoin,
*Lévy Processes*, Cambridge University Press, 1996, Chapter VII).
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees

private theorem leftLim_dloc_restrict_reflected {f : DLoc} {t T : ℝ≥0}
    (ht : 0 < t) (htT : t < T) :
    Function.leftLim (DLoc.restrict T f)
      ⟨t, t.2, (show (t : ℝ) ≤ (T : ℝ) from htT.le)⟩ = Function.leftLim f.1 t := by
  let t' : Set.Icc (0 : ℝ) (T : ℝ) := ⟨t, t.2, htT.le⟩
  let inc : Set.Icc (0 : ℝ) (T : ℝ) → ℝ≥0 := fun u => ⟨u, u.2.1⟩
  have hinc : Continuous inc := Continuous.subtype_mk continuous_subtype_val fun u => u.2.1
  have hleft : Tendsto inc (𝓝[<] t') (𝓝[<] t) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨tendsto_nhdsWithin_of_tendsto_nhds hinc.continuousAt, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with u hu
    exact hu
  let z : Set.Icc (0 : ℝ) (T : ℝ) := ⟨0, le_rfl, T.2⟩
  have hz : z < t' := ht
  let _ : (𝓝[<] t).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, ht⟩
  let _ : (𝓝[<] t').NeBot := nhdsLT_neBot_of_exists_lt ⟨z, hz⟩
  apply leftLim_eq_of_tendsto
  exact (f.2.tendsto_nhdsLT_leftLim t).comp hleft

private lemma leftLim_shift_reflected (f : DLoc) {r g : ℝ≥0} (hrg : r < g) :
    Function.leftLim (DLoc.shift r f).1 (g - r) =
      Function.leftLim f.1 g - f.1 r := by
  let t : ℝ≥0 := g - r
  have hrt : r + t = g := add_tsub_cancel_of_le hrg.le
  have hmap : Tendsto (fun u : ℝ≥0 => r + u) (𝓝[<] t) (𝓝[<] g) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have hc : Continuous (fun u : ℝ≥0 => r + u) := continuous_const.add continuous_id
      have htend : Tendsto (fun u : ℝ≥0 => r + u) (𝓝 t) (𝓝 g) := by
        rw [← hrt]
        exact hc.continuousAt
      exact htend.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with u hu
      change r + u < g
      have hlt : r + u < r + t := (add_lt_add_iff_left r).mpr hu
      simpa only [hrt] using hlt
  have ht : 0 < t := tsub_pos_of_lt hrg
  let _ : (𝓝[<] t).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, ht⟩
  apply leftLim_eq_of_tendsto
  exact ((f.2.tendsto_nhdsLT_leftLim g).comp hmap).sub_const (f.1 r)

/-- The left limit of a centered window at an interior time is the centered left limit. -/
private theorem leftLim_supportWindowTime {f : DLoc} {g r q : ℝ≥0}
    (hrg : r < g) (hgq : g < q) :
    Function.leftLim (DLoc.restrict (q - r) (DLoc.shift r f))
      (shiftedWindowTime r g q hrg.le hgq.le) = Function.leftLim f.1 g - f.1 r := by
  have ht : 0 < g - r := tsub_pos_of_lt hrg
  have htT : g - r < q - r := by
    rw [← NNReal.coe_lt_coe, NNReal.coe_sub hrg.le, NNReal.coe_sub (hrg.le.trans hgq.le)]
    exact sub_lt_sub_right (show (g : ℝ) < q by exact_mod_cast hgq) _
  have htime : shiftedWindowTime r g q hrg.le hgq.le =
      (⟨((g - r : ℝ≥0) : ℝ), (g - r).2,
        (show ((g - r : ℝ≥0) : ℝ) ≤ ((q - r : ℝ≥0) : ℝ) from htT.le)⟩ :
        Set.Icc (0 : ℝ) ((q - r : ℝ≥0) : ℝ)) := by
    apply Subtype.ext
    exact (NNReal.coe_sub hrg.le).symm
  rw [htime, leftLim_dloc_restrict_reflected ht htT, leftLim_shift_reflected f hrg]

/-- Evaluation at the time corresponding to an interior point of a centered window. -/
private theorem eval_supportWindowTime (f : DLoc) {r g q : ℝ≥0} (hrg : r ≤ g) (hgq : g ≤ q) :
    (DLoc.restrict (q - r) (DLoc.shift r f)) (shiftedWindowTime r g q hrg hgq) =
      f.1 g - f.1 r := by
  let gt : ℝ≥0 := ⟨(g : ℝ) - r, sub_nonneg.mpr (by exact_mod_cast hrg)⟩
  have htime : r + gt = g := by
    apply NNReal.coe_injective
    change (r : ℝ) + ((g : ℝ) - r) = g
    ring
  change f.1 (r + gt) - f.1 r = _
  rw [htime]

/-- A left-limit contact with a lower barrier is a generalized window minimizer. -/
theorem isGenMinimizer_supportWindow {f : DLoc} (hf : NoNegJumps f)
    {b : ℝ} {r g q : ℝ≥0} (hrg : r < g) (hgq : g < q)
    (hl : Function.leftLim f.1 g = b) (hb : ∀ u : ℝ≥0, u ≤ q → b ≤ f.1 u) :
    IsGenMinimizer (DLoc.restrict (q - r) (DLoc.shift r f))
      (shiftedWindowTime r g q hrg.le hgq.le) := by
  let _ : Nonempty (Set.Icc (0 : ℝ) ((q - r : ℝ≥0) : ℝ)) :=
    ⟨⟨0, le_rfl, (q - r).2⟩⟩
  let W := DLoc.restrict (q - r) (DLoc.shift r f)
  let s := shiftedWindowTime r g q hrg.le hgq.le
  have hgen : genVal W s = b - f.1 r := by
    dsimp [genVal, W, s]
    rw [leftLim_supportWindowTime hrg hgq, eval_supportWindowTime, hl, min_eq_left]
    exact sub_le_sub_right (hl ▸ hf g) _
  change genVal W s = ⨅ t, W t
  rw [hgen]
  apply le_antisymm
  · apply le_ciInf
    intro t
    change b - f.1 r ≤ f.1 (r + ⟨t, t.2.1⟩) - f.1 r
    apply sub_le_sub_right
    apply hb
    rw [← NNReal.coe_le_coe]
    have ht := t.2.2
    have hqr := NNReal.coe_sub (hrg.le.trans hgq.le)
    change (r : ℝ) + (t : ℝ) ≤ (q : ℝ)
    linarith
  · exact (iInf_le_genVal W s).trans_eq hgen

/-- On every rational window, every generalized minimizer is continuous and any two
such minimizers coincide. -/
def RationalWindowMinima (f : DLoc) : Prop :=
  ∀ r q : ℚ≥0, (r : ℝ≥0) < (q : ℝ≥0) →
    ∀ s : Set.Icc (0 : ℝ) (((q : ℝ≥0) - (r : ℝ≥0) : ℝ≥0) : ℝ),
      IsGenMinimizer (DLoc.restrict ((q : ℝ≥0) - (r : ℝ≥0)) (DLoc.shift r f)) s →
        ContinuousAt (DLoc.restrict ((q : ℝ≥0) - (r : ℝ≥0)) (DLoc.shift r f)) s ∧
          ∀ t, IsGenMinimizer
            (DLoc.restrict ((q : ℝ≥0) - (r : ℝ≥0)) (DLoc.shift r f)) t → t = s

/-- Countable transfer of minimum continuity and uniqueness to all rational windows. -/
theorem ae_rationalWindowMinima {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), RationalWindowMinima f := by
  apply (ae_all_iff).mpr
  intro r
  apply (ae_all_iff).mpr
  intro q
  by_cases hrq : (r : ℝ≥0) < (q : ℝ≥0)
  · let T : ℝ≥0 := (q : ℝ≥0) - (r : ℝ≥0)
    have hT : 0 < T := tsub_pos_of_lt hrq
    have hm : ∀ᵐ w ∂(stableProcessLaw θ (T : ℝ) : Measure (D (T : ℝ) ℝ)),
        ∀ s, IsGenMinimizer w s → ContinuousAt w s ∧
          ∀ t, IsGenMinimizer w t → t = s := by
      filter_upwards [stableProcessLaw_ae_unique_continuous_minimum hθ
        (show (0 : ℝ) < T by exact_mod_cast hT)] with w hw
      obtain ⟨g, _, _, hc, hg, hu⟩ := hw
      intro s hs
      have hsg := hu s hs
      subst s
      exact ⟨hc, hu⟩
    have hr : ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc),
        ∀ s, IsGenMinimizer (DLoc.restrict T f) s →
          ContinuousAt (DLoc.restrict T f) s ∧
            ∀ t, IsGenMinimizer (DLoc.restrict T f) t → t = s := by
      rw [← map_restrict_stableLocalLaw hθ hT] at hm
      exact ae_of_ae_map (DLoc.measurable_restrict T).aemeasurable hm
    have hshift := hr
    rw [← map_shift_stableLocalLaw hθ (r : ℝ≥0)] at hshift
    have hs := ae_of_ae_map (DLoc.measurable_shift_fixed (r : ℝ≥0)).aemeasurable hshift
    exact hs.mono fun _ h _ => h
  · exact Filter.Eventually.of_forall fun _ h => False.elim (hrq h)

/-- Continuity of the window at an interior time identifies the path value with its
left limit, and hence gives continuity of the original local path there. -/
theorem continuousAt_of_supportWindow {f : DLoc} {r g q : ℝ≥0}
    (hrg : r < g) (hgq : g < q)
    (hc : ContinuousAt (DLoc.restrict (q - r) (DLoc.shift r f))
      (shiftedWindowTime r g q hrg.le hgq.le)) : ContinuousAt f.1 g := by
  have he := hc.continuousWithinAt.leftLim_eq
  rw [leftLim_supportWindowTime hrg hgq, eval_supportWindowTime] at he
  have hleft : Function.leftLim f.1 g = f.1 g := sub_left_injective he
  apply continuousAt_iff_continuous_left'_right'.mpr
  refine ⟨?_, f.2.isRightContinuous g⟩
  change Tendsto f.1 (𝓝[<] g) (𝓝 (f.1 g))
  rw [← hleft]
  exact f.2.tendsto_nhdsLT_leftLim g

/-- Every strictly positive interval has rational windows around its positive left endpoint. -/
theorem exists_supportWindow {g d : ℝ≥0} (hg : 0 < g) (hgd : g < d) :
    ∃ r q : ℚ≥0, (r : ℝ≥0) < g ∧ g < (q : ℝ≥0) ∧ (q : ℝ≥0) < d := by
  obtain ⟨r, hr0, hrg⟩ := exists_rat_btwn (show (0 : ℝ) < g by exact_mod_cast hg)
  obtain ⟨q, hgq, hqd⟩ := exists_rat_btwn (show (g : ℝ) < d by exact_mod_cast hgd)
  have hr0' : (0 : ℚ) ≤ r := by exact_mod_cast hr0.le
  have hq0R : (0 : ℝ) ≤ q := (show (0 : ℝ) ≤ g by positivity).trans hgq.le
  have hq0 : (0 : ℚ) ≤ q := by exact_mod_cast hq0R
  refine ⟨⟨r, hr0'⟩, ⟨q, hq0⟩, ?_, ?_, ?_⟩
  · exact_mod_cast hrg
  · exact_mod_cast hgq
  · exact_mod_cast hqd

end BGW.StableTrees
