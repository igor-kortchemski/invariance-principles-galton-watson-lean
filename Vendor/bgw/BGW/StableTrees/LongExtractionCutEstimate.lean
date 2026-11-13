/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.LongExtractionStoppedCut

/-!
# Quantitative continuity estimate for moving stopped cuts

An interior clock preserves every jump. At the two ends only continuity-window estimates enter.
-/

@[expose] public section

open Set Filter Topology
open scoped NNReal
open BGW.Skorokhod

namespace BGW.StableTrees

/-- A uniform J1 approximation and continuity windows control moving translated stopped cuts.
Reference: Billingsley (1999), Chapter 3. -/
theorem dist_translatedStoppedCut_le {M : ℝ} (T : ℝ≥0) (u f : D M ℝ)
    (g d a b : Icc (0 : ℝ) M) (hgd : g < d) (hab : a ≤ b)
    (σ : TimeChange M) {δ e : ℝ} (hδ : 0 < δ)
    (hsmall : 4 * δ < min ((g : ℝ) + T) d - g)
    (hd : ∀ t, |(σ t : ℝ) - t| ≤ δ / 8)
    (hp : ∀ t, dist (u (σ t)) (f t) ≤ e)
    (ha : |(a : ℝ) - g| ≤ δ / 8) (hb : |(b : ℝ) - d| ≤ δ / 8)
    (hg : ∀ s : Icc (0 : ℝ) M, |(s : ℝ) - g| < 5 * δ → dist (f s) (f g) ≤ e)
    (hq : ∀ s : Icc (0 : ℝ) M, |(s : ℝ) - min ((g : ℝ) + T) d| < 5 * δ →
      dist (f s) (f ⟨min ((g : ℝ) + T) d,
        le_min (add_nonneg g.2.1 T.2) d.2.1, (min_le_right _ _).trans d.2.2⟩) ≤ e) :
    dist (translatedStoppedCut T u a b hab) (translatedStoppedCut T f g d hgd.le) ≤
      max (δ / 4) (5 * e) := by
  let Q : Icc (0 : ℝ) M := ⟨min ((g : ℝ) + T) d,
    le_min (add_nonneg g.2.1 T.2) d.2.1, (min_le_right _ _).trans d.2.2⟩
  let r : ℝ := (Q : ℝ) - g - δ
  have hlr : δ < r := by dsimp only [r, Q]; linarith only [hsmall, hδ]
  have hrT : r < T := by
    have hQ : (Q : ℝ) ≤ (g : ℝ) + T := min_le_left _ _
    dsimp only [r]
    linarith only [hQ, hδ]
  let inc : Icc δ r → Icc (0 : ℝ) M := fun t => ⟨(g : ℝ) + t,
    by linarith only [g.2.1, t.2.1, hδ], by
      have hQ : (Q : ℝ) ≤ M := Q.2.2
      have ht := t.2.2
      dsimp only [r] at ht
      linarith only [ht, hQ, hδ]⟩
  let h : Icc δ r → ℝ := fun t => (σ (inc t) : ℝ) - a
  have hc : Continuous h := (continuous_subtype_val.comp
    (σ.continuous.comp (Continuous.subtype_mk
      (continuous_const.add continuous_subtype_val) _))).sub continuous_const
  have hm : StrictMono h := by
    intro s t hst
    have hst' : inc s < inc t := by
      change (g : ℝ) + (s : ℝ) < (g : ℝ) + t
      have hstR : (s : ℝ) < t := hst
      linarith only [hstR]
    have hσst : (σ (inc s) : ℝ) < σ (inc t) := σ.strictMono hst'
    exact sub_lt_sub_right hσst (a : ℝ)
  have hmove (t : Icc δ r) : |h t - t| ≤ δ / 4 := by
    have heq : h t - t = ((σ (inc t) : ℝ) - inc t) + ((g : ℝ) - a) := by
      dsimp only [h, inc]
      ring
    rw [heq]
    have hsum := (abs_add_le ((σ (inc t) : ℝ) - inc t) ((g : ℝ) - a)).trans
      (add_le_add (hd _) (by simpa only [abs_sub_comm] using ha))
    linarith only [hsum]
  have hlo : 0 < h ⟨δ, le_rfl, hlr.le⟩ := by
    have hh := (abs_le.mp (hmove ⟨δ, le_rfl, hlr.le⟩)).1
    linarith only [hh, hδ]
  have hhi : h ⟨r, hlr.le, le_rfl⟩ < T := by
    have hh := (abs_le.mp (hmove ⟨r, hlr.le, le_rfl⟩)).2
    have hQ : (Q : ℝ) ≤ (g : ℝ) + T := min_le_left _ _
    dsimp only [r] at hh
    linarith only [hh, hQ, hδ]
  obtain ⟨τ, hmid, hhead, htail, hτ⟩ :=
    exists_extraction_middle_timeChange hδ hlr hrT h hc hm hlo hhi hmove
  have he : 0 ≤ e := dist_nonneg.trans (hp g)
  have habs := abs_le.mp ha
  have hbbs := abs_le.mp hb
  let z₀ := σ.symm a
  have hz₀ : |(z₀ : ℝ) - g| < 5 * δ := by
    have hσ := hd z₀
    rw [show σ z₀ = a from σ.apply_symm_apply a] at hσ
    have hh := abs_le.mp hσ
    rw [abs_lt]
    constructor <;> linarith only [hh.1, hh.2, habs.1, habs.2, hδ]
  have hbase : dist (u a) (f g) ≤ 2 * e := by
    have hu : dist (u a) (f z₀) ≤ e := by
      simpa only [z₀, OrderIso.apply_symm_apply] using hp z₀
    exact (dist_triangle _ _ _).trans
      ((add_le_add hu (hg z₀ hz₀)).trans_eq (show e + e = 2 * e by ring))
  have hpath (t : Icc (0 : ℝ) (T : ℝ)) :
      dist (translatedStoppedCut T u a b hab (τ t))
        (translatedStoppedCut T f g d hgd.le t) ≤ 5 * e := by
    let y : Icc (0 : ℝ) M := ⟨min ((a : ℝ) + τ t) b,
      le_min (add_nonneg a.2.1 (τ t).2.1) b.2.1, (min_le_right _ _).trans b.2.2⟩
    let k : Icc (0 : ℝ) M := ⟨min ((g : ℝ) + t) d,
      le_min (add_nonneg g.2.1 t.2.1) d.2.1, (min_le_right _ _).trans d.2.2⟩
    let z := σ.symm y
    have hzmove := abs_le.mp (hd z)
    rw [show σ z = y from σ.apply_symm_apply y] at hzmove
    have hyu : dist (u y) (f z) ≤ e := by
      simpa only [z, OrderIso.apply_symm_apply] using hp z
    have hcompare : dist (f z) (f k) ≤ 2 * e := by
      by_cases ht : (t : ℝ) ≤ δ
      · have hyp : (y : ℝ) ≤ (σ (inc ⟨δ, le_rfl, hlr.le⟩) : ℝ) := by
          have hh := hhead t ht
          change (τ t : ℝ) ≤ (σ (inc ⟨δ, le_rfl, hlr.le⟩) : ℝ) - a at hh
          exact (min_le_left _ _).trans (by linarith only [hh])
        have hym : (a : ℝ) ≤ y := le_min (le_add_of_nonneg_right (τ t).2.1) hab
        have hh := abs_le.mp (hd (inc ⟨δ, le_rfl, hlr.le⟩))
        have hznear : |(z : ℝ) - g| < 5 * δ := by
          change -(δ / 8) ≤ (σ (inc ⟨δ, le_rfl, hlr.le⟩) : ℝ) - ((g : ℝ) + δ) ∧
            (σ (inc ⟨δ, le_rfl, hlr.le⟩) : ℝ) - ((g : ℝ) + δ) ≤ δ / 8 at hh
          rw [abs_lt]
          constructor <;> linarith only [hyp, hym, hh.2, hzmove.1, hzmove.2, habs.1, hδ]
        have hknear : |(k : ℝ) - g| < 5 * δ := by
          have hklo : (g : ℝ) ≤ k := le_min (le_add_of_nonneg_right t.2.1) hgd.le
          have hkhi : (k : ℝ) ≤ (g : ℝ) + δ := (min_le_left _ _).trans (add_le_add le_rfl ht)
          rw [abs_lt]
          constructor <;> linarith only [hklo, hkhi, hδ]
        exact (dist_triangle _ (f g) _).trans
          ((add_le_add (hg z hznear) (by simpa only [dist_comm] using hg k hknear)).trans_eq
            (show e + e = 2 * e by ring))
      by_cases ht' : r ≤ (t : ℝ)
      · have hylow : (Q : ℝ) - δ - δ / 8 ≤ y := by
          have hh := htail t ht'
          change (σ (inc ⟨r, hlr.le, le_rfl⟩) : ℝ) - a ≤ (τ t : ℝ) at hh
          have hhσ := (abs_le.mp (hd (inc ⟨r, hlr.le, le_rfl⟩))).1
          change -(δ / 8) ≤ (σ (inc ⟨r, hlr.le, le_rfl⟩) : ℝ) - ((g : ℝ) + r) at hhσ
          have hQd : (Q : ℝ) ≤ d := min_le_right _ _
          change _ ≤ min _ _
          apply le_min
          · dsimp only [r] at hhσ
            linarith only [hh, hhσ]
          · linarith only [hbbs.1, hQd, hδ]
        have hyhi : (y : ℝ) ≤ (Q : ℝ) + δ / 8 := by
          have hym : (y : ℝ) ≤ min ((a : ℝ) + T) b :=
            min_le_min (add_le_add le_rfl (τ t).2.2) le_rfl
          have hupper : min ((a : ℝ) + T) b ≤ min ((g : ℝ) + T + δ / 8) ((d : ℝ) + δ / 8) :=
            min_le_min (by linarith only [habs.2]) (by linarith only [hbbs.2])
          exact hym.trans (hupper.trans_eq (min_add_add_right _ _ _))
        have hznear : |(z : ℝ) - Q| < 5 * δ := by
          rw [abs_lt]
          constructor <;> linarith only [hylow, hyhi, hzmove.1, hzmove.2, hδ]
        have hknear : |(k : ℝ) - Q| < 5 * δ := by
          have hklo : (Q : ℝ) - δ ≤ k := by
            change _ ≤ min _ _
            apply le_min
            · dsimp only [r] at ht'
              linarith only [ht']
            · exact (sub_le_self _ hδ.le).trans (min_le_right _ _)
          have hkhi : (k : ℝ) ≤ Q := min_le_min (add_le_add le_rfl t.2.2) le_rfl
          rw [abs_lt]
          constructor <;> linarith only [hklo, hkhi, hδ]
        exact (dist_triangle _ (f Q) _).trans
          ((add_le_add (hq z hznear) (by simpa only [dist_comm] using hq k hknear)).trans_eq
            (show e + e = 2 * e by ring))
      · have htl : δ ≤ (t : ℝ) := le_of_not_ge ht
        have htr : (t : ℝ) ≤ r := le_of_not_ge ht'
        have hτt := hmid t htl htr
        let s : Icc (0 : ℝ) M := inc ⟨t, htl, htr⟩
        have hsource : (σ s : ℝ) < b := by
          have hs := (abs_le.mp (hd s)).2
          change (σ s : ℝ) - ((g : ℝ) + t) ≤ δ / 8 at hs
          have hQd : (Q : ℝ) ≤ d := min_le_right _ _
          dsimp only [r] at htr
          linarith only [hs, hQd, htr, hbbs.1, hδ]
        have hy : y = σ s := by
          apply Subtype.ext
          change min ((a : ℝ) + τ t) b = _
          change (τ t : ℝ) = (σ s : ℝ) - a at hτt
          rw [show (a : ℝ) + τ t = (σ s : ℝ) by linarith only [hτt], min_eq_left hsource.le]
        have hk : k = s := by
          apply Subtype.ext
          change min ((g : ℝ) + t) d = (g : ℝ) + t
          apply min_eq_left
          have hQd : (Q : ℝ) ≤ d := min_le_right _ _
          dsimp only [r] at htr
          linarith only [htr, hQd, hδ]
        have hz : z = s := by
          dsimp only [z]
          rw [hy, OrderIso.symm_apply_apply]
        rw [hz, hk, dist_self]
        positivity
    rw [translatedStoppedCut_apply, translatedStoppedCut_apply]
    change dist (u y - u a) (f k - f g) ≤ _
    exact (dist_sub_sub_le _ _ _ _).trans
      ((add_le_add ((dist_triangle _ _ _).trans (add_le_add hyu hcompare)) hbase).trans_eq
        (show (e + 2 * e) + 2 * e = 5 * e by ring))
  rw [dist_comm, dist_eq_j1Dist]
  apply (j1Dist_le_timeChange_cost T.2 _ _ τ).trans
  have hclock : (⨆ t, |(τ t : ℝ) - t|) ≤ δ / 4 := by
    refine csSup_le (s := Set.range (fun t : Icc (0 : ℝ) (T : ℝ) =>
      |(τ t : ℝ) - t|)) ?_ ?_
    · exact ⟨_, ⟨⟨0, le_rfl, T.2⟩, rfl⟩⟩
    · rintro _ ⟨t, rfl⟩
      exact hτ t
  have hpaths : (⨆ t, dist ((translatedStoppedCut T f g d hgd.le) t)
      ((translatedStoppedCut T u a b hab) (τ t))) ≤ 5 * e := by
    refine csSup_le (s := Set.range (fun t : Icc (0 : ℝ) (T : ℝ) =>
      dist ((translatedStoppedCut T f g d hgd.le) t)
        ((translatedStoppedCut T u a b hab) (τ t)))) ?_ ?_
    · exact ⟨_, ⟨⟨0, le_rfl, T.2⟩, rfl⟩⟩
    · rintro _ ⟨t, rfl⟩
      exact (dist_comm _ _).trans_le (hpath t)
  exact max_le_max hclock hpaths

end BGW.StableTrees
