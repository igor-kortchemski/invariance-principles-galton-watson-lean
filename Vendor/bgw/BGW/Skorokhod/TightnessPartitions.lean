/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.Skorokhod.Basic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Order.Fin.InsertNth

/-!
# Small-oscillation partitions of càdlàg paths

The existence argument uses the supremum of the times reachable by a finite partition.
Left limits make that supremum reachable, and right continuity extends it.
-/

@[expose] public section

open Set Filter Topology

namespace BGW.Skorokhod

variable {T : ℝ} {E : Type*} [MetricSpace E]

private def Reachable (f : D T E) (ε b : ℝ) : Prop :=
  ∃ (r : ℕ) (t : Fin (r + 1) → ℝ), t 0 = 0 ∧ t (Fin.last r) = b ∧ StrictMono t ∧
    ∀ (i : Fin r) (s u : Icc (0 : ℝ) T),
      t i.castSucc ≤ s → (s : ℝ) < t i.succ →
      t i.castSucc ≤ u → (u : ℝ) < t i.succ → dist (f s) (f u) ≤ ε

private theorem reachable_zero (f : D T E) (ε : ℝ) : Reachable f ε 0 := by
  refine ⟨0, fun _ => 0, rfl, rfl, ?_, ?_⟩
  · intro i j hij
    have hi := i.isLt
    have hj := j.isLt
    have hij' : i.val < j.val := hij
    omega
  · intro i
    exact Fin.elim0 i

private theorem reachable_append {f : D T E} {ε a b : ℝ}
    (ha : Reachable f ε a) (hab : a < b)
    (hosc : ∀ s u : Icc (0 : ℝ) T, a ≤ s → (s : ℝ) < b →
      a ≤ u → (u : ℝ) < b → dist (f s) (f u) ≤ ε) : Reachable f ε b := by
  obtain ⟨r, t, ht0, htr, hmono, ht⟩ := ha
  refine ⟨r + 1, Fin.snoc t b, ?_, by simp, ?_, ?_⟩
  · simpa using ht0
  · simpa only [Fin.insertNth_last'] using
      Fin.strictMono_insertNth_last hmono b (htr ▸ hab)
  · intro i
    obtain ⟨i, rfl⟩ | rfl := i.eq_castSucc_or_eq_last
    · simpa only [Fin.snoc_castSucc, Fin.succ_castSucc] using ht i
    · simpa [htr] using hosc

private theorem exists_left_oscillation (f : D T E) {ε : ℝ} (hε : 0 < ε)
    (b : Icc (0 : ℝ) T) :
    ∃ d > 0, ∀ s u : Icc (0 : ℝ) T,
      (b : ℝ) - d < s → s < b → (b : ℝ) - d < u → u < b →
      dist (f s) (f u) ≤ ε := by
  obtain ⟨l, hl⟩ := (isCadlag f).tendsto_nhdsLT b
  obtain ⟨d, hd, hdist⟩ := Metric.tendsto_nhdsWithin_nhds.mp hl (ε / 2) (by positivity)
  refine ⟨d, hd, fun s u hs hsb hu hub => ?_⟩
  have hsb' : (s : ℝ) < (b : ℝ) := hsb
  have hub' : (u : ℝ) < (b : ℝ) := hub
  have hsd : dist s b < d := by
    change |(s : ℝ) - b| < d
    rw [abs_of_neg (sub_neg.mpr hsb')]
    linarith
  have hud : dist u b < d := by
    change |(u : ℝ) - b| < d
    rw [abs_of_neg (sub_neg.mpr hub')]
    linarith
  have hs' := hdist hsb hsd
  have hu' := hdist hub hud
  calc
    dist (f s) (f u) ≤ dist (f s) l + dist (f u) l := dist_triangle_right _ _ _
    _ ≤ ε := by linarith

private theorem exists_right_oscillation (f : D T E) {ε : ℝ} (hε : 0 < ε)
    (b : Icc (0 : ℝ) T) :
    ∃ d > 0, ∀ s u : Icc (0 : ℝ) T,
      b ≤ s → (s : ℝ) < b + d → b ≤ u → (u : ℝ) < b + d →
      dist (f s) (f u) ≤ ε := by
  have hc := continuousWithinAt_Ioi_iff_Ici.mp ((isCadlag f).isRightContinuous b)
  obtain ⟨d, hd, hdist⟩ := Metric.continuousWithinAt_iff.mp hc (ε / 2) (by positivity)
  refine ⟨d, hd, fun s u hs hsb hu hub => ?_⟩
  have hs' : (b : ℝ) ≤ (s : ℝ) := hs
  have hu' : (b : ℝ) ≤ (u : ℝ) := hu
  have hsd : dist s b < d := by
    change |(s : ℝ) - b| < d
    rw [abs_of_nonneg (sub_nonneg.mpr hs')]
    linarith
  have hud : dist u b < d := by
    change |(u : ℝ) - b| < d
    rw [abs_of_nonneg (sub_nonneg.mpr hu')]
    linarith
  have hs' := hdist hs hsd
  have hu' := hdist hu hud
  calc
    dist (f s) (f u) ≤ dist (f s) (f b) + dist (f u) (f b) :=
      dist_triangle_right _ _ _
    _ ≤ ε := by linarith

/-- A càdlàg path admits a finite partition with arbitrarily small oscillation on each
half-open block. The terminal value is deliberately excluded from the last block. -/
theorem exists_partition_dist_le (f : D T E) (hT : 0 ≤ T) {ε : ℝ} (hε : 0 < ε) :
    ∃ (r : ℕ) (t : Fin (r + 1) → ℝ), t 0 = 0 ∧ t (Fin.last r) = T ∧ StrictMono t ∧
      ∀ (i : Fin r) (s u : Icc (0 : ℝ) T),
        t i.castSucc ≤ s → (s : ℝ) < t i.succ →
        t i.castSucc ≤ u → (u : ℝ) < t i.succ → dist (f s) (f u) ≤ ε := by
  change Reachable f ε T
  let S : Set ℝ := {b | Reachable f ε b} ∩ Icc 0 T
  have hzero : 0 ∈ S := ⟨reachable_zero f ε, le_rfl, hT⟩
  have hne : S.Nonempty := ⟨0, hzero⟩
  have hbd : BddAbove S := ⟨T, fun _ hx => hx.2.2⟩
  have hc0 : 0 ≤ sSup S := le_csSup hbd hzero
  have hcT : sSup S ≤ T := csSup_le hne fun _ hx => hx.2.2
  have hreach : Reachable f ε (sSup S) := by
    by_cases hc : sSup S = 0
    · rw [hc]
      exact reachable_zero f ε
    obtain ⟨d, hd, hosc⟩ := exists_left_oscillation f hε ⟨sSup S, hc0, hcT⟩
    obtain ⟨a, ha, hca⟩ := (lt_csSup_iff hbd hne).mp (sub_lt_self (sSup S) hd)
    have hac : a ≤ sSup S := le_csSup hbd ha
    rcases hac.eq_or_lt with hac | hac
    · simpa [hac] using ha.1
    · exact reachable_append ha.1 hac fun s u hs hsc hu huc =>
        hosc s u (hca.trans_le hs) hsc (hca.trans_le hu) huc
  have heq : sSup S = T := by
    by_contra hneT
    have hlt : sSup S < T := lt_of_le_of_ne hcT hneT
    obtain ⟨d, hd, hosc⟩ := exists_right_oscillation f hε ⟨sSup S, hc0, hcT⟩
    obtain ⟨b, hcb, hb⟩ := exists_between (lt_min (lt_add_of_pos_right _ hd) hlt)
    have hreachb : Reachable f ε b := reachable_append hreach hcb
      fun s u hs hsb hu hub => hosc s u hs (hsb.trans (hb.trans_le (min_le_left _ _)))
        hu (hub.trans (hb.trans_le (min_le_left _ _)))
    have hbS : b ∈ S := ⟨hreachb, hc0.trans hcb.le, hb.le.trans (min_le_right _ _)⟩
    exact (not_lt_of_ge (le_csSup hbd hbS)) hcb
  rwa [heq] at hreach

end BGW.Skorokhod
