/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.MarkedExcursionsSupport

/-!
# Passage endpoints after a restart

Deterministic inverse-passage identities used for translating marked excursions.

(J. Bertoin, *Lévy Processes*, Cambridge University Press, 1996, Chapter IV.)
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees

private theorem passage_sup {f : DLoc}
    (hT : ∀ x, firstPassageBelow x f = (passageTime x f : WithTop ℝ≥0)) (x : ℝ≥0) :
    (⨆ y : Set.Iio x, firstPassageBelow y f) = (passageTimeMinus x f : WithTop ℝ≥0) := by
  have hb : (⨆ y : Set.Iio x, firstPassageBelow y f) ≤ firstPassageBelow x f :=
    iSup_le fun y => firstPassageBelow_mono f y.2.le
  obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.mp
    (ne_top_of_le_ne_top (by rw [hT x]; exact WithTop.coe_ne_top) hb)
  simp only [passageTimeMinus, ← ht, WithTop.untopD_coe]

private theorem passageMinus_le_iff {f : DLoc}
    (hT : ∀ x, firstPassageBelow x f = (passageTime x f : WithTop ℝ≥0)) (x b : ℝ≥0) :
    passageTimeMinus x f ≤ b ↔ ∀ y < x, passageTime y f ≤ b := by
  constructor
  · intro h y hy
    have hle := le_iSup (fun z : Set.Iio x => firstPassageBelow z f) ⟨y, hy⟩
    rw [passage_sup hT x, hT y] at hle
    have hle' : passageTime y f ≤ passageTimeMinus x f := by exact_mod_cast hle
    exact hle'.trans h
  · intro h
    have hle : (⨆ y : Set.Iio x, firstPassageBelow y f) ≤ (b : WithTop ℝ≥0) := by
      apply iSup_le
      intro y
      rw [hT y]
      exact_mod_cast h y y.2
    rw [passage_sup hT x] at hle
    exact_mod_cast hle

private theorem passage_restart {f : DLoc}
    (hT : ∀ x, firstPassageBelow x f = (passageTime x f : WithTop ℝ≥0))
    (hc : ∀ x, f.1 (passageTime x f) = -(x : ℝ)) (a : ℝ≥0) :
    (∀ y, firstPassageBelow y (DLoc.shiftAt (firstPassageBelow a) f) =
      (passageTime y (DLoc.shiftAt (firstPassageBelow a) f) : WithTop ℝ≥0)) ∧
    ∀ y, passageTime a f + passageTime y (DLoc.shiftAt (firstPassageBelow a) f) =
      passageTime (a + y) f := by
  let f' := DLoc.shiftAt (firstPassageBelow a) f
  have hadd (y : ℝ≥0) := firstPassageBelow_add_of_creeping (y := y) (hT a) (hc a)
  have hfin (y : ℝ≥0) : firstPassageBelow y f' ≠ ⊤ := by
    intro htop
    have h := hadd y
    rw [htop, WithTop.add_top, hT (a + y)] at h
    exact WithTop.coe_ne_top h
  have hread (y : ℝ≥0) : firstPassageBelow y f' = (passageTime y f' : WithTop ℝ≥0) := by
    obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.mp (hfin y)
    simp only [passageTime, ← ht, WithTop.untopD_coe]
  refine ⟨hread, ?_⟩
  intro y
  have h := hadd y
  rw [hT (a + y), hT a, hread y] at h
  exact_mod_cast h.symm

private theorem passageMinus_restart {f : DLoc}
    (hT : ∀ x, firstPassageBelow x f = (passageTime x f : WithTop ℝ≥0))
    (hc : ∀ x, f.1 (passageTime x f) = -(x : ℝ)) (a : ℝ≥0) {y : ℝ≥0} (hy : 0 < y) :
    passageTime a f + passageTimeMinus y (DLoc.shiftAt (firstPassageBelow a) f) =
      passageTimeMinus (a + y) f := by
  let f' := DLoc.shiftAt (firstPassageBelow a) f
  obtain ⟨hread, hadd⟩ := passage_restart hT hc a
  have hmono : Monotone (fun x => passageTime x f) :=
    (strictMono_passageTime_of_creeping hT hc).monotone
  have hTa : passageTime a f ≤ passageTimeMinus (a + y) f := by
    exact ((passageMinus_le_iff hT (a + y) _).mp le_rfl) a (lt_add_of_pos_right _ hy)
  apply le_antisymm
  · calc
      _ ≤ passageTime a f + (passageTimeMinus (a + y) f - passageTime a f) := by
        apply add_le_add le_rfl
        apply (passageMinus_le_iff hread _ _).mpr
        intro z hz
        apply (le_tsub_iff_left hTa).mpr
        rw [hadd z]
        exact ((passageMinus_le_iff hT (a + y) _).mp le_rfl) (a + z)
          (add_lt_add_right hz a)
      _ = _ := add_tsub_cancel_of_le hTa
  · apply (passageMinus_le_iff hT _ _).mpr
    intro z hz
    by_cases hza : z ≤ a
    · exact (hmono hza).trans le_self_add
    · have haz : a ≤ z := (lt_of_not_ge hza).le
      have hzy : z - a < y := by
        apply (tsub_lt_iff_right haz).mpr
        simpa only [add_comm] using hz
      have hle : passageTime (z - a) f' ≤ passageTimeMinus y f' :=
        ((passageMinus_le_iff hread y _).mp le_rfl) (z - a) hzy
      have heq := hadd (z - a)
      rw [add_tsub_cancel_of_le haz] at heq
      rw [← heq]
      exact add_le_add le_rfl hle

private theorem excursionCut_translate {f : DLoc} {s g d g' d' : ℝ≥0}
    (hg : s + g' = g) (hd : s + d' = d) (hc : cutValid g d f) :
    excursionCut g' d' (DLoc.shift s f) = excursionCut g d f := by
  have hgd : g' < d' := by
    have h := hc.1
    rw [← hg, ← hd] at h
    exact (add_lt_add_iff_left s).mp h
  have hc' : cutValid g' d' (DLoc.shift s f) := by
    refine ⟨hgd, ?_, ?_⟩
    · change f.1 (s + d') - f.1 s = f.1 (s + g') - f.1 s
      rw [hg, hd, hc.2.1]
    · intro t hgt htd
      change f.1 (s + g') - f.1 s ≤ f.1 (s + t) - f.1 s
      rw [hg]
      exact sub_le_sub_right (hc.2.2 _ (hg ▸ add_le_add le_rfl hgt)
        (hd ▸ add_le_add le_rfl htd)) _
  apply Subtype.ext
  apply Prod.ext
  · apply Subtype.ext
    funext t
    change (excursionCut g' d' (DLoc.shift s f)).path.1 t = (excursionCut g d f).path.1 t
    rw [excursionCut_eval hc', excursionCut_eval hc]
    change (f.1 (s + min (g' + t) d') - f.1 s) - (f.1 (s + g') - f.1 s) =
      f.1 (min (g + t) d) - f.1 g
    rw [add_min, ← add_assoc, hg, hd]
    ring
  · apply Subtype.ext
    change (excursionCut g' d' (DLoc.shift s f)).lifetime = (excursionCut g d f).lifetime
    rw [excursionCut_lifetime hc', excursionCut_lifetime hc, ← hg, ← hd,
      add_tsub_add_eq_tsub_left]

private theorem jumpExcursion_restart {f : DLoc}
    (hT : ∀ x, firstPassageBelow x f = (passageTime x f : WithTop ℝ≥0))
    (hc : ∀ x, f.1 (passageTime x f) = -(x : ℝ))
    (hs : ∀ x ∈ passageJumpSet f, cutValid (passageTimeMinus x f) (passageTime x f) f)
    (a : ℝ≥0) {y : ℝ≥0} (hy : 0 < y) (hj : a + y ∈ passageJumpSet f) :
    jumpExcursion y (DLoc.shiftAt (firstPassageBelow a) f) = jumpExcursion (a + y) f := by
  have hg := passageMinus_restart hT hc a hy
  have hd := (passage_restart hT hc a).2 y
  have hshift : DLoc.shiftAt (firstPassageBelow a) f = DLoc.shift (passageTime a f) f := by
    unfold DLoc.shiftAt
    rw [hT a]
    rfl
  unfold jumpExcursion
  rw [hshift] at hg hd ⊢
  exact excursionCut_translate hg hd (hs (a + y) hj)

/-- **Shift identity** (deterministic on a good event, simultaneously in all levels `a`): the
excursion point measure of the post-`T_a` centered path is the translate by `a` of the restriction
of `μ f` to labels `> a` (same cuts, since `T_{(x-a)-}(f') = T_{x-}(f) - T_a`). -/
theorem ae_excursionPointMeasure_shift {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∀ a : ℝ≥0,
      excursionPointMeasure (DLoc.shiftAt (firstPassageBelow a) f) =
        Measure.map (fun p : ℝ≥0 × Excursion => (p.1 - a, p.2))
          ((excursionPointMeasure f).restrict (Ioi a ×ˢ univ))  := by
  filter_upwards [ae_passageTime_eq_firstPassageBelow hθ, ae_creeping_passageTime hθ,
    ae_jumpExcursion_spec hθ, ae_passageJumpSet_countable hθ] with f hT hc hs hcount
  intro a
  classical
  let f' := DLoc.shiftAt (firstPassageBelow a) f
  have hJ (y : ℝ≥0) : y ∈ passageJumpSet f' ↔ 0 < y ∧ a + y ∈ passageJumpSet f := by
    by_cases hy : 0 < y
    · have hgap : passageTimeMinus y f' < passageTime y f' ↔
          passageTimeMinus (a + y) f < passageTime (a + y) f := by
        rw [← passageMinus_restart hT.1 hc a hy, ← (passage_restart hT.1 hc a).2 y]
        exact (add_lt_add_iff_left (passageTime a f)).symm
      change (0 < y ∧ passageTimeMinus y f' < passageTime y f') ↔
        0 < y ∧ 0 < a + y ∧ passageTimeMinus (a + y) f < passageTime (a + y) f
      have hay : 0 < a + y := (show 0 ≤ a from a.2).trans_lt (lt_add_of_pos_right a hy)
      simp only [hy, hay, true_and, hgap]
    · simp only [passageJumpSet, mem_ofPred_eq, hy, false_and]
  have hcount' : (passageJumpSet f').Countable := by
    apply (hcount.preimage (fun x y h => add_left_cancel h)).mono
    intro y hy
    exact ((hJ y).mp hy).2
  have hmark (y : ℝ≥0) (hy : y ∈ passageJumpSet f') :
      jumpExcursion y f' = jumpExcursion (a + y) f :=
    jumpExcursion_restart hT.1 hc (fun x hx => (hs x hx).1) a
      ((hJ y).mp hy).1 ((hJ y).mp hy).2
  have hmap : Measurable (fun p : ℝ≥0 × Excursion => (p.1 - a, p.2)) := by fun_prop
  ext s hsm
  rw [Measure.map_apply hmap hsm, Measure.restrict_apply (hmap hsm),
    excursionPointMeasure_apply hcount' hsm,
    excursionPointMeasure_apply hcount ((hmap hsm).inter
      (measurableSet_Ioi.prod MeasurableSet.univ))]
  let A : Set ℝ≥0 := {y ∈ passageJumpSet f' | (y, jumpExcursion y f') ∈ s}
  let B : Set ℝ≥0 := {x ∈ passageJumpSet f |
    (x, jumpExcursion x f) ∈
      (fun p : ℝ≥0 × Excursion => (p.1 - a, p.2)) ⁻¹' s ∩ (Ioi a ×ˢ univ)}
  have hmemb (x : ℝ≥0) : x ∈ B ↔ x ∈ passageJumpSet f ∧
      (x - a, jumpExcursion x f) ∈ s ∧ a < x := by
    simp only [B, mem_ofPred_eq, mem_inter_iff, mem_preimage, mem_prod, mem_Ioi,
      mem_univ, and_true]
  let e₀ : A → B := fun y => ⟨a + y, (hmemb _).mpr (by
    have hy : (y : ℝ≥0) ∈ passageJumpSet f' ∧ ((y : ℝ≥0), jumpExcursion y f') ∈ s := y.2
    refine ⟨((hJ y).mp hy.1).2, ?_, lt_add_of_pos_right a ((hJ y).mp hy.1).1⟩
    rw [add_tsub_cancel_left, ← hmark y hy.1]
    exact hy.2)⟩
  have hinj : Function.Injective e₀ := by
    intro x y h
    apply Subtype.ext
    exact add_left_cancel (congrArg Subtype.val h)
  have hsurj : Function.Surjective e₀ := by
    intro x
    obtain ⟨hx, hxs, hax⟩ := (hmemb x).mp x.2
    have hy : 0 < (x : ℝ≥0) - a := tsub_pos_of_lt hax
    have heq : a + ((x : ℝ≥0) - a) = x := add_tsub_cancel_of_le hax.le
    have hj : (x : ℝ≥0) - a ∈ passageJumpSet f' :=
      (hJ _).mpr ⟨hy, heq.symm ▸ hx⟩
    have hm : jumpExcursion ((x : ℝ≥0) - a) f' = jumpExcursion x f := by
      rw [hmark _ hj, heq]
    refine ⟨⟨(x : ℝ≥0) - a, hj, ?_⟩, Subtype.ext heq⟩
    simpa only [hm] using hxs
  exact congrArg (fun n : ℕ∞ => (n : ℝ≥0∞))
    (Set.encard_congr (Equiv.ofBijective e₀ ⟨hinj, hsurj⟩))

end BGW.StableTrees
