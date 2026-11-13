/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.LongExtractionCutEstimate
public import BGW.StableTrees.LongExtractionClocks
public import BGW.StableTrees.LongExtractionCutTerminal

/-!
# Joint continuity of moving translated stopped cuts

J1 clocks are preserved in the interior. Continuity at the initial and observed terminal source
times controls the affine clock corrections.
-/

@[expose] public section

open Set Filter Topology
open scoped NNReal
open BGW.Skorokhod

namespace BGW.StableTrees

/-- Moving cuts converge when the limit is continuous at the initial and observed terminal times.
Reference: Billingsley (1999), Chapter 3. -/
private theorem tendsto_translatedStoppedCut_of_continuousAt_source {M : ℝ} (T : ℝ≥0)
    {u : ℕ → D M ℝ} {f : D M ℝ} (hu : Tendsto u atTop (𝓝 f))
    (a b : ℕ → Icc (0 : ℝ) M) (hab : ∀ n, a n ≤ b n)
    {g d : Icc (0 : ℝ) M} (hgd : g < d)
    (ha : Tendsto (fun n => (a n : ℝ)) atTop (𝓝 (g : ℝ)))
    (hb : Tendsto (fun n => (b n : ℝ)) atTop (𝓝 (d : ℝ)))
    (hg : ContinuousAt f g)
    (hq : ContinuousAt f ⟨min ((g : ℝ) + T) d,
      le_min (add_nonneg g.2.1 T.2) d.2.1, (min_le_right _ _).trans d.2.2⟩) :
    Tendsto (fun n => translatedStoppedCut T (u n) (a n) (b n) (hab n)) atTop
      (𝓝 (translatedStoppedCut T f g d hgd.le)) := by
  by_cases hT : T = 0
  · subst T
    have hz (p : D M ℝ) (x y : Icc (0 : ℝ) M) (hxy : x ≤ y) :
        translatedStoppedCut 0 p x y hxy = ⟨fun _ => 0, IsCadlag.const⟩ := by
      ext t
      have ht : (t : ℝ) = 0 := le_antisymm t.2.2 t.2.1
      rw [translatedStoppedCut_apply]
      simp only [ht, add_zero, min_eq_left (show (x : ℝ) ≤ (y : ℝ) from hxy),
        sub_self, BGW.Skorokhod.coe_mk]
    simp_rw [hz]
    exact tendsto_const_nhds
  have hTpos : (0 : ℝ) < T := by exact_mod_cast pos_iff_ne_zero.mpr hT
  obtain ⟨σ, hσ, he⟩ := tendsto_iff_exists_timeChange.mp hu
  have hM : 0 ≤ M := g.2.1.trans g.2.2
  let Q : Icc (0 : ℝ) M := ⟨min ((g : ℝ) + T) d,
    le_min (add_nonneg g.2.1 T.2) d.2.1, (min_le_right _ _).trans d.2.2⟩
  have hspan : 0 < (Q : ℝ) - g := sub_pos.mpr
    (lt_min (lt_add_of_pos_right _ hTpos) hgd)
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  let e := ε / 10
  have hepos : 0 < e := by dsimp only [e]; positivity
  obtain ⟨ηg, hηg, hgη⟩ := Metric.continuousAt_iff.mp hg e hepos
  obtain ⟨ηq, hηq, hqη⟩ := Metric.continuousAt_iff.mp hq e hepos
  let δ := min (ε / 2) (min (ηg / 10) (min (ηq / 10) (((Q : ℝ) - g) / 8)))
  have hδ : 0 < δ := lt_min (by positivity)
    (lt_min (by positivity) (lt_min (by positivity) (by positivity)))
  have hδε : δ ≤ ε / 2 := min_le_left _ _
  have hδg : δ ≤ ηg / 10 := (min_le_right _ _).trans (min_le_left _ _)
  have hδq : δ ≤ ηq / 10 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδs : δ ≤ ((Q : ℝ) - g) / 8 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hsmall : 4 * δ < (Q : ℝ) - g := by linarith only [hδs, hspan]
  have htime : ∀ᶠ n in atTop, ∀ t, |(σ n t : ℝ) - t| ≤ δ / 8 := by
    filter_upwards [hσ.eventually (gt_mem_nhds (by positivity : 0 < δ / 8))] with n hn t
    have hbound : BddAbove (Set.range fun t => |(σ n t : ℝ) - t|) := by
      refine ⟨M, ?_⟩
      rintro _ ⟨s, rfl⟩
      exact TimeChange.abs_sub_le (σ n) hM s
    exact (le_ciSup hbound t).trans hn.le
  have hag := ha.eventually (Metric.ball_mem_nhds (g : ℝ) (by positivity : 0 < δ / 8))
  have hbd := hb.eventually (Metric.ball_mem_nhds (d : ℝ) (by positivity : 0 < δ / 8))
  have hnearG (s : Icc (0 : ℝ) M) (hs : |(s : ℝ) - g| < 5 * δ) :
      dist (f s) (f g) ≤ e := by
    apply (hgη ?_).le
    rw [Subtype.dist_eq, Real.dist_eq]
    linarith only [hs, hδg, hηg]
  have hnearQ (s : Icc (0 : ℝ) M) (hs : |(s : ℝ) - Q| < 5 * δ) :
      dist (f s) (f Q) ≤ e := by
    apply (hqη ?_).le
    rw [Subtype.dist_eq, Real.dist_eq]
    linarith only [hs, hδq, hηq]
  apply Filter.eventually_atTop.mp
  filter_upwards [htime, hag, hbd, eventually_extraction_error_lt he hepos]
    with n hnσ hna hnb hne
  have hna' : |(a n : ℝ) - g| ≤ δ / 8 := by
    exact (show dist (a n : ℝ) g < δ / 8 from hna).le
  have hnb' : |(b n : ℝ) - d| ≤ δ / 8 := by
    exact (show dist (b n : ℝ) d < δ / 8 from hnb).le
  have h := dist_translatedStoppedCut_le T (u n) f g d (a n) (b n) hgd (hab n) (σ n)
    hδ hsmall (hnσ) (fun t => (hne t).le) hna' hnb' hnearG hnearQ
  apply h.trans_lt
  apply max_lt
  · linarith only [hδε, hε]
  · dsimp only [e]
    linarith only [hε]

/-- Joint J1 continuity of translated stopped cuts with moving endpoints, at continuous cutoffs.
Reference: Billingsley (1999), Chapter 3. -/
theorem tendsto_translatedStoppedCut {M : ℝ} (T : ℝ≥0)
    {u : ℕ → D M ℝ} {f : D M ℝ} (hu : Tendsto u atTop (𝓝 f))
    (a b : ℕ → Icc (0 : ℝ) M) (hab : ∀ n, a n ≤ b n)
    {g d : Icc (0 : ℝ) M} (hgd : g < d)
    (ha : Tendsto (fun n => (a n : ℝ)) atTop (𝓝 (g : ℝ)))
    (hb : Tendsto (fun n => (b n : ℝ)) atTop (𝓝 (d : ℝ)))
    (hg : ContinuousAt f g) (hd : ContinuousAt f d)
    (hc : ContinuousAt (translatedStoppedCut T f g d hgd.le) ⟨T, T.2, le_rfl⟩) :
    Tendsto (fun n => translatedStoppedCut T (u n) (a n) (b n) (hab n)) atTop
      (𝓝 (translatedStoppedCut T f g d hgd.le)) := by
  apply tendsto_translatedStoppedCut_of_continuousAt_source T hu a b hab hgd ha hb hg
  let Q : Icc (0 : ℝ) M := ⟨min ((g : ℝ) + T) d,
    le_min (add_nonneg g.2.1 T.2) d.2.1, (min_le_right _ _).trans d.2.2⟩
  change ContinuousAt f Q
  by_cases hdT : (d : ℝ) ≤ (g : ℝ) + T
  · have hQ : Q = d := Subtype.ext (min_eq_right hdT)
    simpa only [hQ] using hd
  have hQT : (Q : ℝ) = (g : ℝ) + T := min_eq_left (le_of_not_ge hdT)
  have hQd : Q < d := by change (Q : ℝ) < d; rw [hQT]; exact lt_of_not_ge hdT
  by_cases hT : T = 0
  · have hQ : Q = g := Subtype.ext (by simpa only [hT, NNReal.coe_zero, add_zero] using hQT)
    simpa only [hQ] using hg
  exact continuousAt_source_of_translatedStoppedCut (pos_iff_ne_zero.mpr hT)
    f g d Q hgd.le hQT hQd hc

end BGW.StableTrees
