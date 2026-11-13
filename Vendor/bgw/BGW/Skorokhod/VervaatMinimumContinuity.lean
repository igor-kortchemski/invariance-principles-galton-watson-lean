/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.Skorokhod.Vervaat
import BGW.Skorokhod.RestrictContinuity
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Algebra.Order.Group.MinMax

/-!
# Stability of the first minimum time

The completed lower envelope has a strictly positive gap away from a unique
minimizer. Uniform approximation after a time change preserves this gap.
-/

@[expose] public section

open Set Filter Topology

namespace BGW.Skorokhod

private theorem completedValue_lowerSemicontinuous (f : D 1 ℝ) :
    LowerSemicontinuous (fun t => min (Function.leftLim f t) (f t)) := by
  intro t c hc
  obtain ⟨b, hcb, hbt⟩ := exists_between hc
  have he : ∀ᶠ s in 𝓝 t, b < f s := by
    rw [← nhdsLT_sup_nhdsGE t, eventually_sup]
    constructor
    · exact ((isCadlag f).tendsto_nhdsLT_leftLim t).eventually
        (eventually_gt_nhds (lt_min_iff.mp hbt).1)
    · have hge : ContinuousWithinAt f (Ici t) t := by
        rw [ContinuousWithinAt, ← nhdsGT_sup_nhdsWithin_singleton t, tendsto_sup]
        exact ⟨(isCadlag f).isRightContinuous t,
          by simpa only [nhdsWithin_singleton] using tendsto_pure_nhds f t⟩
      exact hge.eventually (eventually_gt_nhds (lt_min_iff.mp hbt).2)
  filter_upwards [he, eventually_eventually_nhds.mpr he] with s hs hsn
  apply lt_min
  · exact hcb.trans_le (isClosed_Ici.mem_of_mapClusterPt
      ((mapClusterPt_leftLim f s).mono nhdsWithin_le_nhds)
      (hsn.mono fun _ h => h.le))
  · exact hcb.trans hs

private theorem iInf_le_completedValue (f : D 1 ℝ) (t : Icc (0 : ℝ) 1) :
    (⨅ s, f s) ≤ min (Function.leftLim f t) (f t) := by
  refine le_min ?_ (ciInf_le (isBounded_range f).bddBelow t)
  apply isClosed_Ici.mem_of_mapClusterPt (mapClusterPt_leftLim f t)
  exact Eventually.of_forall fun s => ciInf_le (isBounded_range f).bddBelow s

private theorem minimum_gap {f : D 1 ℝ}
    (huniq : ∀ t : Icc (0 : ℝ) 1,
      min (Function.leftLim f t) (f t) = ⨅ s, f s → t = vervaatTime f)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ t : Icc (0 : ℝ) 1, ε ≤ dist t (vervaatTime f) →
      (⨅ s, f s) + δ ≤ min (Function.leftLim f t) (f t) := by
  let K : Set (Icc (0 : ℝ) 1) := {t | ε ≤ dist t (vervaatTime f)}
  have hK : IsCompact K := (isClosed_le continuous_const
    (continuous_id.dist continuous_const)).isCompact
  by_cases hne : K.Nonempty
  · obtain ⟨q, hq, hmin⟩ := LowerSemicontinuousOn.exists_isMinOn hne hK
      ((completedValue_lowerSemicontinuous f).lowerSemicontinuousOn K)
    have hlt : (⨅ s, f s) < min (Function.leftLim f q) (f q) := by
      refine lt_of_le_of_ne (iInf_le_completedValue f q) ?_
      intro heq
      have hqg := huniq q heq.symm
      have hbad : ε ≤ 0 := by simpa [K, hqg] using hq
      exact hε.not_ge hbad
    refine ⟨min (Function.leftLim f q) (f q) - (⨅ s, f s), sub_pos.mpr hlt, ?_⟩
    intro t ht
    have hle : min (Function.leftLim f q) (f q) ≤ min (Function.leftLim f t) (f t) :=
      hmin ht
    linarith
  · refine ⟨1, one_pos, ?_⟩
    intro t ht
    exact (hne ⟨t, ht⟩).elim

/-- Uniform path control after a time change also controls the completed lower envelope. -/
theorem dist_completedValue_timeChange_le (u f : D 1 ℝ) (σ : TimeChange 1) {e : ℝ}
    (he : ∀ t, dist (u (σ t)) (f t) ≤ e) (t : Icc (0 : ℝ) 1) :
    dist (min (Function.leftLim u (σ t)) (u (σ t)))
      (min (Function.leftLim f t) (f t)) ≤ e := by
  have hσ : Tendsto σ (𝓝[<] t) (𝓝[<] σ t) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨σ.continuous.continuousAt.tendsto.mono_left nhdsWithin_le_nhds, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact σ.strictMono hs
  have hl : dist (Function.leftLim u (σ t)) (Function.leftLim f t) ≤ e := by
    rcases eq_or_neBot (𝓝[<] t) with ht | ht
    · have ht' : 𝓝[<] σ t = ⊥ := by
        by_contra hn
        have : (𝓝[<] σ t).NeBot := neBot_iff.mpr hn
        have hi : Tendsto σ.symm (𝓝[<] σ t) (𝓝[<] t) := by
          apply tendsto_nhdsWithin_iff.mpr
          refine ⟨?_, ?_⟩
          · simpa only [OrderIso.symm_apply_apply] using
              (σ.symm.continuous.tendsto (σ t)).mono_left
                (nhdsWithin_le_nhds (s := Iio (σ t)))
          filter_upwards [self_mem_nhdsWithin] with s hs
          change σ.symm s < t
          simpa only [OrderIso.symm_apply_apply] using σ.symm.strictMono hs
        exact hi.neBot.ne ht
      rw [leftLim_eq_of_eq_bot _ ht, leftLim_eq_of_eq_bot _ ht']
      exact he t
    · have : (𝓝[<] t).NeBot := ht
      exact isClosed_Iic.mem_of_tendsto
        ((((isCadlag u).tendsto_nhdsLT_leftLim (σ t)).comp hσ).dist
          ((isCadlag f).tendsto_nhdsLT_leftLim t)) (Eventually.of_forall he)
  rw [Real.dist_eq] at hl ⊢
  exact (abs_min_sub_min_le_max _ _ _ _).trans (max_le hl (by simpa [Real.dist_eq] using he t))

/-- A unique completed minimum makes the first minimizing time J1-continuous. -/
theorem continuousAt_vervaatTime {f : D 1 ℝ}
    (huniq : ∀ t : Icc (0 : ℝ) 1,
      min (Function.leftLim f t) (f t) = ⨅ s, f s → t = vervaatTime f) :
    ContinuousAt vervaatTime f := by
  obtain ⟨σ, hdisp, hpath⟩ :=
    (tendsto_iff_exists_timeChange (u := id) (f := f)).mp tendsto_id
  have hinf : Tendsto (fun u : D 1 ℝ => ⨅ s, u s) (𝓝 f) (𝓝 (⨅ s, f s)) :=
    (lipschitzWith_one_iInf zero_le_one).continuous.continuousAt
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨δ, hδ, hgap⟩ := minimum_gap huniq (half_pos hε)
  have hd := (tendsto_order.mp hdisp).2 (ε / 2) (half_pos hε)
  have hp := (tendsto_order.mp hpath).2 (δ / 3) (by linarith)
  have hm := Metric.tendsto_nhds.mp hinf (δ / 3) (by linarith)
  filter_upwards [hd, hp, hm] with u huD huP huM
  let z := (σ u).symm (vervaatTime u)
  have hpoint (t : Icc (0 : ℝ) 1) : dist (u (σ u t)) (f t) ≤ δ / 3 :=
    (le_ciSup (bddAbove_comp_dist zero_le_one u f (σ u)) t).trans huP.le
  have hcomp := dist_completedValue_timeChange_le u f (σ u) hpoint z
  rw [OrderIso.apply_symm_apply, min_leftLim_vervaatTime, Real.dist_eq] at hcomp
  have hz : dist z (vervaatTime f) < ε / 2 := by
    by_contra! hz
    have hg := hgap z hz
    rw [Real.dist_eq] at huM
    have h1 := (abs_le.mp hcomp).1
    have h2 := (abs_lt.mp huM).2
    linarith
  have hmove : dist (vervaatTime u) z < ε / 2 := by
    have h := (le_ciSup (bddAbove_displacement zero_le_one (σ u)) z).trans_lt huD
    simpa only [Subtype.dist_eq, Real.dist_eq, z, OrderIso.apply_symm_apply] using h
  exact (dist_triangle (vervaatTime u) z (vervaatTime f)).trans_lt (by linarith)

end BGW.Skorokhod
