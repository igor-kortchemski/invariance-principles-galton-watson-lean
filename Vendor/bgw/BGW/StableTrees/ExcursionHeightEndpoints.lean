/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.ExcursionHeightPassageRestart
public import BGW.StableTrees.ExcursionHeightPreStart
import BGW.StableTrees.SupremumFactorizationCompensation
import Mathlib.Topology.Order.IsLUB

/-!
# Simultaneous height zeros at passage endpoints

The fixed-level Markov argument is intersected only at rational levels. Right continuity
of passage and its supremum description on the left give both endpoints at every level.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal Classical
open BGW.Skorokhod

namespace BGW.StableTrees

/-- On finite passages, the passage process tends to its finite left reading from the left. -/
theorem passageTime_tendsto_left (f : DLoc)
    (hfin : ∀ y, firstPassageBelow y f = (passageTime y f : WithTop ℝ≥0))
    (hp : ∀ y, passagePast y f = (passageTimeMinus y f : ℝ≥0∞))
    (hm : Monotone (fun y => passageTime y f)) {x : ℝ≥0} (hx : 0 < x) :
    Tendsto (fun y => passageTime y f) (𝓝[<] x) (𝓝 (passageTimeMinus x f)) := by
  let S := (fun y => passageTime y f) '' Iio x
  have hb : BddAbove S := ⟨passageTime x f, by
    rintro _ ⟨y, hy, rfl⟩
    exact hm hy.le⟩
  have hne : S.Nonempty := ⟨passageTime 0 f, 0, hx, rfl⟩
  have hs : sSup S = passageTimeMinus x f := by
    apply le_antisymm
    · apply csSup_le hne
      rintro _ ⟨y, hy, rfl⟩
      have hh : (firstPassageBelow y f : ℝ≥0∞) ≤ passagePast x f :=
        le_iSup (fun z : Iio x => (firstPassageBelow z f : ℝ≥0∞)) ⟨y, hy⟩
      rw [hfin y, hp x] at hh
      exact ENNReal.coe_le_coe.mp hh
    · have hh : passagePast x f ≤ ((sSup S : ℝ≥0) : ℝ≥0∞) := by
        apply iSup_le
        intro y
        rw [hfin y]
        exact ENNReal.coe_le_coe.mpr (le_csSup hb ⟨y, y.2, rfl⟩)
      rw [hp x] at hh
      exact ENNReal.coe_le_coe.mp hh
  have ht : Tendsto (fun y => passageTime y f) (𝓝[<] x) (𝓝 (sSup S)) :=
    hm.tendsto_nhdsLT x
  rwa [hs] at ht

/-- Height vanishes at both passage readings simultaneously at all levels. -/
theorem ae_heightLoc_passageEndpoints_all {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∀ x : ℝ≥0,
      heightLoc θ f (passageTimeMinus x f) = 0 ∧ heightLoc θ f (passageTime x f) = 0 := by
  have hr : ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∀ q : ℚ,
      heightLoc θ f (passageTime (q : ℝ).toNNReal f) = 0 :=
    ae_all_iff.mpr (fun q => ae_heightLoc_passageTime_fixed hθ (q : ℝ).toNNReal)
  filter_upwards [hr, ae_isCadlag_monotone_passage hθ,
    ae_passagePast_eq_passageTimeMinus hθ, ae_passageTime_eq_firstPassageBelow hθ]
      with f hf hc hp hfin
  have hrat (y : ℝ≥0) (hy : IsRationalTime y) : heightLoc θ f (passageTime y f) = 0 := by
    obtain ⟨q, hq⟩ := hy
    simpa only [hq, Real.toNNReal_coe] using hf q
  intro x
  have hright : heightLoc θ f (passageTime x f) = 0 := by
    obtain ⟨q, _, hq, hqt⟩ := dense_isRationalTime.exists_seq_strictAnti_tendsto x
    have hqwithin : Tendsto q atTop (𝓝[>] x) :=
      tendsto_nhdsWithin_iff.mpr ⟨hqt, Eventually.of_forall fun n => (hq n).1⟩
    have hT := (hc.1.isRightContinuous x).tendsto.comp hqwithin
    have hT' : Tendsto (fun n => passageTime (q n) f) atTop (𝓝 (passageTime x f)) :=
      NNReal.tendsto_coe.mp hT
    have hH := (continuous_heightLoc θ f).continuousAt.tendsto.comp hT'
    have hzero : Tendsto (fun n => heightLoc θ f (passageTime (q n) f)) atTop (𝓝 0) := by
      convert (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0)) using 1
      funext n
      exact hrat _ (hq n).2
    exact tendsto_nhds_unique hH hzero
  refine ⟨?_, hright⟩
  by_cases hx : x = 0
  · subst x
    simp [passageTimeMinus, heightLoc_zero]
  · have hxpos : 0 < x := pos_iff_ne_zero.mpr hx
    obtain ⟨q, _, hq, hqt⟩ := dense_isRationalTime.exists_seq_strictMono_tendsto_of_lt hxpos
    have hqwithin : Tendsto q atTop (𝓝[<] x) :=
      tendsto_nhdsWithin_iff.mpr ⟨hqt, Eventually.of_forall fun n => (hq n).1.2⟩
    have hT := (passageTime_tendsto_left f hfin.1 hp hc.2.1 hxpos).comp hqwithin
    have hH := (continuous_heightLoc θ f).continuousAt.tendsto.comp hT
    have hzero : Tendsto (fun n => heightLoc θ f (passageTime (q n) f)) atTop (𝓝 0) := by
      convert (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0)) using 1
      funext n
      exact hrat _ (hq n).2
    exact tendsto_nhds_unique hH hzero

/-- The host height vanishes at both ends of every excursion interval (K14). -/
theorem ae_heightLoc_passageEndpoints {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∀ x ∈ passageJumpSet f,
      heightLoc θ f (passageTimeMinus x f) = 0 ∧ heightLoc θ f (passageTime x f) = 0 :=
  (ae_heightLoc_passageEndpoints_all hθ).mono fun _ hf x _ => hf x

end BGW.StableTrees
