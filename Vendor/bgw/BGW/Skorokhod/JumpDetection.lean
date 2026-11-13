/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import Mathlib.Topology.Order.Cadlag
public import Mathlib.Topology.Order.LeftRightLim
public import Mathlib.Data.NNRat.Defs
public import Mathlib.Data.Rat.Cast.Lemmas
public import Mathlib.Topology.Instances.ENNReal.Lemmas
public import Mathlib.Analysis.SpecificLimits.Basic

import BGW.Probability.NNReal

/-! # Detection of jumps of càdlàg functions

For a càdlàg `x : ℝ≥0 → ℝ`, `firstJumpAbove q ε x` is the first time after `q` at which `x`
jumps by more than `ε`. There are finitely many jumps larger than `ε` on a bounded interval, the
first such time is attained, and `{σ_{q,ε} < t}` has a description through rational times only.
Every jump time is such a first-passage time for some rational `q ≥ 0` and `ε > 0`. This is the
deterministic input to the enumeration of jumps by stopping times (P. Billingsley, *Convergence
of Probability Measures*, 2nd ed., Wiley, 1999, Section 12; J. Bertoin, *Lévy Processes*,
Cambridge University Press, 1996, Chapter I).
-/

@[expose] public section

open Filter Function Set
open scoped Topology NNReal ENNReal

open BGW.Probability

namespace BGW.Skorokhod

/-- The absolute jump of `x` at `t`. -/
noncomputable def jumpSize (x : ℝ≥0 → ℝ) (t : ℝ≥0) : ℝ := |x t - Function.leftLim x t|

/-- The first time after `q` at which `x` jumps by more than `ε` (`⊤` if there is none). -/
noncomputable def firstJumpAbove (q : ℝ≥0) (ε : ℝ) (x : ℝ≥0 → ℝ) : ℝ≥0∞ :=
  ⨅ t ∈ {t : ℝ≥0 | q < t ∧ ε < jumpSize x t}, (t : ℝ≥0∞)

private lemma tendsto_leftLim_nhdsGT {x : ℝ≥0 → ℝ} (hx : IsCadlag x) (c : ℝ≥0) :
    Tendsto (leftLim x) (𝓝[>] c) (𝓝 (x c)) := by
  apply (closed_nhds_basis (x c)).tendsto_right_iff.2
  rintro s ⟨hs, hsc⟩
  have hmem : {y | x y ∈ s} ∈ 𝓝[>] c := hx.isRightContinuous c hs
  obtain ⟨u, hcu, hu⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hmem
  filter_upwards [Ioo_mem_nhdsGT hcu] with t ht
  have := nhdsLT_neBot_of_exists_lt ⟨c, ht.1⟩
  change leftLim x t ∈ s
  apply hsc.mem_of_tendsto (hx.tendsto_nhdsLT_leftLim t)
  filter_upwards [Ioo_mem_nhdsLT ht.1] with r hr
  exact hu ⟨hr.1, hr.2.trans_le ht.2.le⟩

private lemma tendsto_jumpSize_of_tendsto {x : ℝ≥0 → ℝ} (hx : IsCadlag x)
    {u : ℕ → ℝ≥0} {c : ℝ≥0} (hu : Tendsto u atTop (𝓝 c))
    (hside : (∀ n, c < u n) ∨ (∀ n, u n < c)) :
    Tendsto (fun n ↦ jumpSize x (u n)) atTop (𝓝 0) := by
  have hmem : Tendsto u atTop (𝓝 c) := hu
  have hmain : Tendsto (fun n ↦ x (u n) - leftLim x (u n)) atTop (𝓝 0) := by
    rcases hside with hgt | hlt
    · have hu' : Tendsto u atTop (𝓝[>] c) :=
        tendsto_nhdsWithin_iff.2 ⟨hu, Eventually.of_forall hgt⟩
      have h₁ := (hx.isRightContinuous c).tendsto.comp hu'
      have h₂ := (tendsto_leftLim_nhdsGT hx c).comp hu'
      simpa using h₁.sub h₂
    · have hu' : Tendsto u atTop (𝓝[<] c) :=
        tendsto_nhdsWithin_iff.2 ⟨hu, Eventually.of_forall hlt⟩
      have h₁ := (hx.tendsto_nhdsLT_leftLim c).comp hu'
      have hu'' : Tendsto u atTop (𝓝[≤] c) :=
        tendsto_nhdsWithin_iff.2 ⟨hu, Eventually.of_forall (fun n ↦ (hlt n).le)⟩
      have h₂ := (continuousWithinAt_leftLim_Iic
        (hx.tendsto_nhdsLT_leftLim c)).tendsto.comp hu''
      simpa using h₁.sub h₂
  simpa [jumpSize] using hmain.abs

/-- Finiteness: a càdlàg function has finitely many jumps larger than `ε > 0` on `[0, T]`. -/
theorem finite_setOf_jump_gt_cadlag {x : ℝ≥0 → ℝ} (hx : IsCadlag x) {ε : ℝ} (hε : 0 < ε)
    (T : ℝ≥0) : {t : ℝ≥0 | t ≤ T ∧ ε < jumpSize x t}.Finite := by
  classical
  by_contra hfin
  let S := {t : ℝ≥0 | t ≤ T ∧ ε < jumpSize x t}
  have hinf : S.Infinite := hfin
  let u : ℕ → ℝ≥0 := fun n ↦ hinf.natEmbedding S n
  have huS (n : ℕ) : u n ∈ S := (hinf.natEmbedding S n).property
  have huinj : Injective u := by
    simpa [u, Function.comp_def] using
      Subtype.val_injective.comp (hinf.natEmbedding S).injective
  obtain ⟨c, -, φ, hφ, huc⟩ := isCompact_Icc.tendsto_subseq (x := u)
    (fun n ↦ ⟨bot_le, (huS n).1⟩)
  let v := u ∘ φ
  have hvS (n : ℕ) : v n ∈ S := huS (φ n)
  have hvinj : Injective v := huinj.comp hφ.injective
  by_cases hfreq : ∃ᶠ n in atTop, c < v n
  · obtain ⟨ψ, hψ, hψc⟩ := extraction_of_frequently_atTop hfreq
    let w := v ∘ ψ
    have hw : Tendsto w atTop (𝓝 c) := huc.comp hψ.tendsto_atTop
    have hz := tendsto_jumpSize_of_tendsto hx hw (Or.inl hψc)
    have hev : ∀ᶠ n in atTop, jumpSize x (w n) < ε := (tendsto_order.1 hz).2 ε hε
    obtain ⟨n, hn⟩ := hev.exists
    exact (not_lt_of_ge (hvS (ψ n)).2.le) hn
  · have hle : ∀ᶠ n in atTop, v n ≤ c := by
      filter_upwards [not_frequently.1 hfreq] with n hn
      exact not_lt.1 hn
    have hlt : ∃ᶠ n in atTop, v n < c := by
      by_contra h
      have heq : ∀ᶠ n in atTop, v n = c := by
        filter_upwards [hle, not_frequently.1 h] with n hn hn'
        exact le_antisymm hn (not_lt.1 hn')
      obtain ⟨N, hN⟩ := eventually_atTop.1 heq
      have heq' : v N = v (N + 1) :=
        (hN N le_rfl).trans (hN (N + 1) (Nat.le_add_right N 1)).symm
      have := hvinj heq'
      omega
    obtain ⟨ψ, hψ, hψc⟩ := extraction_of_frequently_atTop hlt
    let w := v ∘ ψ
    have hw : Tendsto w atTop (𝓝 c) := huc.comp hψ.tendsto_atTop
    have hz := tendsto_jumpSize_of_tendsto hx hw (Or.inr hψc)
    have hev : ∀ᶠ n in atTop, jumpSize x (w n) < ε := (tendsto_order.1 hz).2 ε hε
    obtain ⟨n, hn⟩ := hev.exists
    exact (not_lt_of_ge (hvS (ψ n)).2.le) hn

private lemma firstJumpAbove_le_of_mem {x : ℝ≥0 → ℝ} {q t : ℝ≥0} {ε : ℝ}
    (ht : q < t ∧ ε < jumpSize x t) : firstJumpAbove q ε x ≤ (t : ℝ≥0∞) :=
  iInf_le_of_le t (iInf_le_of_le ht le_rfl)

/-- The first jump time is `⊤` iff no jump after `q` is larger than `ε`. -/
theorem firstJumpAbove_eq_top_iff (x : ℝ≥0 → ℝ) (q : ℝ≥0) (ε : ℝ) :
    firstJumpAbove q ε x = ⊤ ↔ ∀ t, q < t → jumpSize x t ≤ ε := by
  constructor
  · intro h t hqt
    by_contra! hj
    have hle := firstJumpAbove_le_of_mem (x := x) (q := q) ⟨hqt, hj⟩
    rw [h] at hle
    simp at hle
  · intro h
    have hS : {t : ℝ≥0 | q < t ∧ ε < jumpSize x t} = ∅ := by
      ext t
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨hqt, hj⟩
      exact (not_lt_of_ge (h t hqt)) hj
    simp [firstJumpAbove, hS]

private lemma exists_min_jump {x : ℝ≥0 → ℝ} (hx : IsCadlag x) {q : ℝ≥0} {ε : ℝ}
    (hε : 0 < ε) (hne : {t : ℝ≥0 | q < t ∧ ε < jumpSize x t}.Nonempty) :
    ∃ r, q < r ∧ ε < jumpSize x r ∧
      ∀ t, q < t → ε < jumpSize x t → r ≤ t := by
  obtain ⟨t₀, ht₀⟩ := hne
  let A := {t : ℝ≥0 | q < t ∧ ε < jumpSize x t} ∩ Iic t₀
  have hAfin : A.Finite := (finite_setOf_jump_gt_cadlag hx hε t₀).subset (by
    intro t ht
    exact ⟨ht.2, ht.1.2⟩)
  obtain ⟨r, hrA, hrmin⟩ := Set.exists_min_image A id hAfin ⟨t₀, ht₀, le_rfl⟩
  have hr_lower (t : ℝ≥0) (ht : q < t ∧ ε < jumpSize x t) : r ≤ t := by
    by_cases htt : t ≤ t₀
    · exact hrmin t ⟨ht, htt⟩
    · exact hrA.2.trans (not_le.1 htt).le
  exact ⟨r, hrA.1.1, hrA.1.2, fun t hqt hj ↦ hr_lower t ⟨hqt, hj⟩⟩

private lemma firstJumpAbove_eq_min {x : ℝ≥0 → ℝ} (hx : IsCadlag x) {q : ℝ≥0} {ε : ℝ}
    (hε : 0 < ε) (hne : {t : ℝ≥0 | q < t ∧ ε < jumpSize x t}.Nonempty) :
    ∃ r : ℝ≥0, firstJumpAbove q ε x = (r : ℝ≥0∞) ∧ q < r ∧ ε < jumpSize x r ∧
      ∀ t, q < t → ε < jumpSize x t → r ≤ t := by
  obtain ⟨r, hqr, hrj, hrmin⟩ := exists_min_jump hx hε hne
  refine ⟨r, ?_, hqr, hrj, hrmin⟩
  apply le_antisymm
  · exact firstJumpAbove_le_of_mem ⟨hqr, hrj⟩
  · apply le_iInf
    intro t
    apply le_iInf
    intro ht
    exact_mod_cast hrmin t ht.1 ht.2

/-- If the first jump above `ε` is finite, it is attained and is minimal. -/
theorem firstJumpAbove_attained {x : ℝ≥0 → ℝ} (hx : IsCadlag x) (q : ℝ≥0) {ε : ℝ}
    (hε : 0 < ε) {s : ℝ≥0} (hs : firstJumpAbove q ε x = s) :
    q < s ∧ ε < jumpSize x s ∧ ∀ t, q < t → ε < jumpSize x t → s ≤ t := by
  have hne : {t : ℝ≥0 | q < t ∧ ε < jumpSize x t}.Nonempty := by
    by_contra h
    have hS : {t : ℝ≥0 | q < t ∧ ε < jumpSize x t} = ∅ := not_nonempty_iff_eq_empty.1 h
    have htop : firstJumpAbove q ε x = ⊤ := by simp [firstJumpAbove, hS]
    rw [hs] at htop
    exact ENNReal.coe_ne_top htop
  obtain ⟨r, hr, hqr, hrj, hrmin⟩ := firstJumpAbove_eq_min hx hε hne
  have hsr : s = r := ENNReal.coe_injective (hs.symm.trans hr)
  subst r
  exact ⟨hqr, hrj, hrmin⟩

private lemma not_tendsto_zero_of_abs_lower {u : ℕ → ℝ} {δ : ℝ}
    (hu : Tendsto u atTop (𝓝 0)) (hδ : 0 < δ) (hl : ∀ n, δ ≤ |u n|) : False := by
  have h0 : Tendsto (fun n ↦ |u n|) atTop (𝓝 0) := by simpa using hu.abs
  have hev : ∀ᶠ n in atTop, |u n| < δ := (tendsto_order.1 h0).2 δ hδ
  obtain ⟨n, hn⟩ := hev.exists
  exact (not_lt_of_ge (hl n)) hn

/-- Countable characterization of `{σ_{q,ε} < t}` for a fixed càdlàg path. -/
theorem firstJumpAbove_lt_iff {x : ℝ≥0 → ℝ} (hx : IsCadlag x) (q : ℚ≥0) {ε : ℚ}
    (hε : 0 < ε) (t : ℝ≥0) :
    firstJumpAbove (q : ℝ≥0) (ε : ℝ) x < (t : ℝ≥0∞) ↔
      ∃ ε' : ℚ, ε < ε' ∧ ∀ n : ℕ, ∃ a b : ℚ≥0,
        q < a ∧ a < b ∧ (b : ℝ≥0) < t ∧ ((b : ℝ) - a < 1 / (n + 1)) ∧
          (ε' : ℝ) ≤ |x (b : ℝ≥0) - x (a : ℝ≥0)| := by
  classical
  constructor
  · intro h
    rw [firstJumpAbove, iInf_lt_iff] at h
    obtain ⟨s, h⟩ := h
    rw [iInf_lt_iff] at h
    obtain ⟨hs, hst⟩ := h
    have hst' : s < t := by exact_mod_cast hst
    obtain ⟨ε', hεε', hε'J⟩ := exists_rat_btwn hs.2
    refine ⟨ε', by exact_mod_cast hεε', fun n ↦ ?_⟩
    let η := (jumpSize x s - (ε' : ℝ)) / 3
    let δ := (1 : ℝ) / (n + 1) / 2
    have hη : 0 < η := by dsimp [η]; positivity
    have hδ : 0 < δ := by dsimp [δ]; positivity
    have hevL : ∀ᶠ r in 𝓝[<] s,
        dist (x r) (leftLim x s) < η ∧ dist r s < δ :=
      (Metric.tendsto_nhds.1 (hx.tendsto_nhdsLT_leftLim s) η hη).and
        (mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds s hδ))
    have hevR : ∀ᶠ r in 𝓝[>] s, dist (x r) (x s) < η ∧ dist r s < δ :=
      (Metric.tendsto_nhds.1 (hx.isRightContinuous s).tendsto η hη).and
        (mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds s hδ))
    obtain ⟨u, hus, hu⟩ := (mem_nhdsLT_iff_exists_Ioo_subset' hs.1).1 hevL
    obtain ⟨v, hsv, hv⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hevR
    obtain ⟨a, hmaxa, has⟩ := exists_nnrat_btwn (max_lt hs.1 hus)
    obtain ⟨b, hsb, hbmin⟩ := exists_nnrat_btwn (lt_min hsv hst')
    have hqua : (q : ℝ≥0) < (a : ℝ≥0) := (le_max_left _ _).trans_lt hmaxa
    have hua : u < (a : ℝ≥0) := (le_max_right _ _).trans_lt hmaxa
    have hab : (a : ℝ≥0) < (b : ℝ≥0) := has.trans hsb
    have hbt : (b : ℝ≥0) < t := hbmin.trans_le (min_le_right _ _)
    have haL := (hu ⟨hua, has⟩).1
    have hbR := (hv ⟨hsb, hbmin.trans_le (min_le_left _ _)⟩).1
    have haT := (hu ⟨hua, has⟩).2
    have hbT := (hv ⟨hsb, hbmin.trans_le (min_le_left _ _)⟩).2
    rw [NNReal.dist_eq, abs_of_neg (sub_neg.2
      (show ((a : ℝ≥0) : ℝ) < (s : ℝ) by exact_mod_cast has))] at haT
    rw [NNReal.dist_eq, abs_of_pos (sub_pos.2
      (show (s : ℝ) < ((b : ℝ≥0) : ℝ) by exact_mod_cast hsb))] at hbT
    have hwidth : ((b : ℝ≥0) : ℝ) - ((a : ℝ≥0) : ℝ) < 1 / (n + 1) := by
      dsimp [δ] at haT hbT
      linarith
    have hjump : (ε' : ℝ) ≤ |x (b : ℝ≥0) - x (a : ℝ≥0)| := by
      rw [Real.dist_eq] at haL hbR
      rw [abs_sub_comm (x (b : ℝ≥0)) (x s)] at hbR
      have h₁ := abs_sub_le (x s) (x (b : ℝ≥0)) (x (a : ℝ≥0))
      have h₂ := abs_sub_le (x s) (x (a : ℝ≥0)) (leftLim x s)
      dsimp [η] at haL hbR
      dsimp [jumpSize] at haL hbR hε'J
      linarith
    exact ⟨a, b, by exact_mod_cast hqua, by exact_mod_cast hab, hbt, hwidth, hjump⟩
  · rintro ⟨ε', hεε', h⟩
    choose a b hqa hab hbt hwidth hdiff using h
    let A : ℕ → ℝ≥0 := fun n ↦ a n
    let B : ℕ → ℝ≥0 := fun n ↦ b n
    have hQA (n : ℕ) : (q : ℝ≥0) < A n := by
      change (q : ℝ≥0) < (a n : ℝ≥0)
      exact_mod_cast hqa n
    have hAB (n : ℕ) : A n < B n := by
      change (a n : ℝ≥0) < (b n : ℝ≥0)
      exact_mod_cast hab n
    have hBT (n : ℕ) : B n < t := hbt n
    have hwidth' (n : ℕ) : ((B n : ℝ) - (A n : ℝ)) < 1 / (n + 1) := by
      exact_mod_cast hwidth n
    have hdiff' (n : ℕ) : (ε' : ℝ) ≤ |x (B n) - x (A n)| := hdiff n
    have hε'0 : (0 : ℝ) < (ε' : ℝ) := by
      have : (0 : ℝ) < (ε : ℝ) := by exact_mod_cast hε
      have : (0 : ℝ) < (ε' : ℝ) := this.trans (by exact_mod_cast hεε')
      exact this
    have hgap : Tendsto (fun n ↦ (B n : ℝ) - (A n : ℝ)) atTop (𝓝 0) := by
      apply squeeze_zero (fun n ↦ sub_nonneg.2 (by exact_mod_cast (hAB n).le))
        (fun n ↦ (hwidth' n).le)
      exact tendsto_one_div_add_atTop_nhds_zero_nat
    obtain ⟨⟨c, d⟩, -, φ, hφ, hlim⟩ :=
      (isCompact_Icc.prod isCompact_Icc).tendsto_subseq
        (x := fun n ↦ (A n, B n)) (fun n ↦
          ⟨⟨bot_le, (hAB n).trans (hBT n) |>.le⟩, ⟨bot_le, (hBT n).le⟩⟩)
    rw [nhds_prod_eq] at hlim
    have hA : Tendsto (A ∘ φ) atTop (𝓝 c) := hlim.fst
    have hB : Tendsto (B ∘ φ) atTop (𝓝 d) := hlim.snd
    have hAR : Tendsto (fun n ↦ ((A (φ n) : ℝ≥0) : ℝ)) atTop (𝓝 (c : ℝ)) := by
      simpa [Function.comp_def] using (NNReal.tendsto_coe.2 hA)
    have hBR : Tendsto (fun n ↦ ((B (φ n) : ℝ≥0) : ℝ)) atTop (𝓝 (d : ℝ)) := by
      simpa [Function.comp_def] using (NNReal.tendsto_coe.2 hB)
    have hgapφ := hgap.comp hφ.tendsto_atTop
    have hcd : d = c := by
      have hz : (d : ℝ) - (c : ℝ) = 0 := tendsto_nhds_unique (hBR.sub hAR) hgapφ
      exact_mod_cast sub_eq_zero.1 hz
    subst d
    have hqc : (q : ℝ≥0) ≤ c := ge_of_tendsto' hA (fun n ↦ (hQA (φ n)).le)
    have hct : c ≤ t := le_of_tendsto' hB (fun n ↦ (hBT (φ n)).le)
    have hqclt : (q : ℝ≥0) < c := by
      apply lt_of_le_of_ne hqc
      intro hEq
      have hcq : c = (q : ℝ≥0) := hEq.symm
      have hA' : Tendsto (A ∘ φ) atTop (𝓝[>] c) :=
        tendsto_nhdsWithin_iff.2 ⟨hA, Eventually.of_forall (fun n ↦ hcq ▸ hQA (φ n))⟩
      have hB' : Tendsto (B ∘ φ) atTop (𝓝[>] c) :=
        tendsto_nhdsWithin_iff.2 ⟨hB, Eventually.of_forall (fun n ↦
          hcq ▸ ((hQA (φ n)).trans (hAB (φ n))))⟩
      have hz := ((hx.isRightContinuous c).tendsto.comp hB').sub
        ((hx.isRightContinuous c).tendsto.comp hA')
      exact not_tendsto_zero_of_abs_lower (by simpa using hz) hε'0 (fun n ↦ hdiff' (φ n))
    have hcltt : c < t := by
      apply lt_of_le_of_ne hct
      intro hEq
      have hct' : c = t := hEq
      have hBc (n : ℕ) : B (φ n) < c := hct'.symm ▸ hBT (φ n)
      have hA' : Tendsto (A ∘ φ) atTop (𝓝[<] c) :=
        tendsto_nhdsWithin_iff.2 ⟨hA, Eventually.of_forall
          (fun n ↦ (hAB (φ n)).trans (hBc n))⟩
      have hB' : Tendsto (B ∘ φ) atTop (𝓝[<] c) :=
        tendsto_nhdsWithin_iff.2 ⟨hB, Eventually.of_forall hBc⟩
      have hz := ((hx.tendsto_nhdsLT_leftLim c).comp hB').sub
        ((hx.tendsto_nhdsLT_leftLim c).comp hA')
      exact not_tendsto_zero_of_abs_lower (by simpa using hz) hε'0 (fun n ↦ hdiff' (φ n))
    have hcjump : (ε' : ℝ) ≤ jumpSize x c := by
      by_cases hleft : ∀ᶠ n in atTop, B (φ n) ≤ c
      · by_cases hleft' : ∀ᶠ n in atTop, B (φ n) < c
        · have hA' : Tendsto (A ∘ φ) atTop (𝓝[<] c) :=
            tendsto_nhdsWithin_iff.2 ⟨hA, hleft'.mono (fun n hn ↦
              (hAB (φ n)).trans hn)⟩
          have hB' : Tendsto (B ∘ φ) atTop (𝓝[<] c) :=
            tendsto_nhdsWithin_iff.2 ⟨hB, hleft'⟩
          have hz := ((hx.tendsto_nhdsLT_leftLim c).comp hB').sub
            ((hx.tendsto_nhdsLT_leftLim c).comp hA')
          exact (not_tendsto_zero_of_abs_lower (by simpa using hz) hε'0
            (fun n ↦ hdiff' (φ n))).elim
        · have hfreq : ∃ᶠ n in atTop, B (φ n) = c := by
            by_contra hn
            apply hleft'
            filter_upwards [hleft, not_frequently.1 hn] with n hle hne
            exact lt_of_le_of_ne hle hne
          obtain ⟨ψ, hψ, hψc⟩ := extraction_of_frequently_atTop hfreq
          have hA' : Tendsto (A ∘ φ ∘ ψ) atTop (𝓝[<] c) :=
            tendsto_nhdsWithin_iff.2 ⟨hA.comp hψ.tendsto_atTop,
              Eventually.of_forall (fun n ↦ (hAB (φ (ψ n))).trans_eq (hψc n))⟩
          have hlim := (tendsto_const_nhds (x := x c)).sub
            ((hx.tendsto_nhdsLT_leftLim c).comp hA')
          have hlim' : Tendsto (fun n ↦ |x (B (φ (ψ n))) - x (A (φ (ψ n)))|) atTop
              (𝓝 (jumpSize x c)) := by
            simpa [jumpSize, Function.comp_def, hψc] using hlim.abs
          exact ge_of_tendsto' hlim' (fun n ↦ hdiff' (φ (ψ n)))
      · rw [not_eventually] at hleft
        have hfreqB : ∃ᶠ n in atTop, c < B (φ n) := by simpa only [not_le] using hleft
        have hAc : ∀ᶠ n in atTop, A (φ n) < c := by
          by_contra hn
          rw [not_eventually] at hn
          have hfreq : ∃ᶠ n in atTop, c ≤ A (φ n) := by simpa only [not_lt] using hn
          obtain ⟨ψ, hψ, hψc⟩ := extraction_of_frequently_atTop hfreq
          have hcont : ContinuousWithinAt x (Ici c) c :=
            continuousWithinAt_Ioi_iff_Ici.1 (hx.isRightContinuous c)
          have hA' : Tendsto (A ∘ φ ∘ ψ) atTop (𝓝[≥] c) :=
            tendsto_nhdsWithin_iff.2 ⟨hA.comp hψ.tendsto_atTop,
              Eventually.of_forall hψc⟩
          have hB' : Tendsto (B ∘ φ ∘ ψ) atTop (𝓝[≥] c) :=
            tendsto_nhdsWithin_iff.2 ⟨hB.comp hψ.tendsto_atTop,
              Eventually.of_forall (fun n ↦ (hψc n).trans (hAB (φ (ψ n))).le)⟩
          have hz := (hcont.tendsto.comp hB').sub (hcont.tendsto.comp hA')
          exact not_tendsto_zero_of_abs_lower (by simpa using hz) hε'0
            (fun n ↦ hdiff' (φ (ψ n)))
        obtain ⟨ψ, hψ, hψAB⟩ := extraction_of_frequently_atTop
          (hfreqB.and_eventually hAc)
        have hψA (n : ℕ) : A (φ (ψ n)) < c := (hψAB n).2
        have hψB (n : ℕ) : c < B (φ (ψ n)) := (hψAB n).1
        have hA' : Tendsto (A ∘ φ ∘ ψ) atTop (𝓝[<] c) :=
          tendsto_nhdsWithin_iff.2 ⟨hA.comp hψ.tendsto_atTop,
            Eventually.of_forall hψA⟩
        have hB' : Tendsto (B ∘ φ ∘ ψ) atTop (𝓝[>] c) :=
          tendsto_nhdsWithin_iff.2 ⟨hB.comp hψ.tendsto_atTop,
            Eventually.of_forall hψB⟩
        have hlim := ((hx.isRightContinuous c).tendsto.comp hB').sub
          ((hx.tendsto_nhdsLT_leftLim c).comp hA')
        have hlim' : Tendsto (fun n ↦ |x (B (φ (ψ n))) - x (A (φ (ψ n)))|) atTop
            (𝓝 (jumpSize x c)) := by
          simpa [jumpSize, Function.comp_def] using hlim.abs
        exact ge_of_tendsto' hlim' (fun n ↦ hdiff' (φ (ψ n)))
    apply lt_of_le_of_lt (firstJumpAbove_le_of_mem (x := x) (q := (q : ℝ≥0))
      ⟨hqclt, lt_of_lt_of_le (by exact_mod_cast hεε') hcjump⟩)
    exact_mod_cast hcltt

/-- Every jump time `s > 0` is `σ_{q,ε}` for rational `q ≥ 0`, `ε > 0`. -/
theorem exists_rat_firstJumpAbove_eq {x : ℝ≥0 → ℝ} (hx : IsCadlag x) {s : ℝ≥0} (hs : 0 < s)
    (hj : x s ≠ Function.leftLim x s) :
    ∃ (q : ℚ≥0) (ε : ℚ), 0 < ε ∧ firstJumpAbove (q : ℝ≥0) (ε : ℝ) x = (s : ℝ≥0∞) := by
  classical
  have hJ : 0 < jumpSize x s := abs_pos.2 (sub_ne_zero.2 hj)
  obtain ⟨ε, hε0, hεJ⟩ := exists_rat_btwn hJ
  have hε0' : 0 < ε := by exact_mod_cast hε0
  let A := {r : ℝ≥0 | r < s ∧ (ε : ℝ) < jumpSize x r}
  have hAfin : A.Finite := (finite_setOf_jump_gt_cadlag hx hε0 s).subset (by
    intro r hr
    exact ⟨hr.1.le, hr.2⟩)
  have hub : ∃ u : ℝ≥0, u < s ∧ ∀ r ∈ A, r ≤ u := by
    by_cases hA : A.Nonempty
    · obtain ⟨u, huA, hu⟩ := Set.exists_max_image A id hAfin hA
      exact ⟨u, huA.1, hu⟩
    · exact ⟨0, hs, fun r hr ↦ (hA ⟨r, hr⟩).elim⟩
  obtain ⟨u, hus, hu⟩ := hub
  obtain ⟨q, huq, hqs⟩ := exists_nnrat_btwn hus
  have hmin (r : ℝ≥0) (hqr : (q : ℝ≥0) < r) (hrj : (ε : ℝ) < jumpSize x r) : s ≤ r := by
    by_contra! hrs
    have hrA : r ∈ A := ⟨hrs, hrj⟩
    exact (not_lt_of_ge ((hu r hrA).trans huq.le)) hqr
  refine ⟨q, ε, hε0', le_antisymm (firstJumpAbove_le_of_mem ⟨hqs, hεJ⟩) ?_⟩
  apply le_iInf
  intro r
  apply le_iInf
  intro hr
  exact_mod_cast hmin r hr.1 hr.2

end BGW.Skorokhod
