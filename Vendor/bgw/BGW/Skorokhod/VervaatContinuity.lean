/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.Skorokhod.VervaatRotate
import BGW.Skorokhod.VervaatMinimumContinuity
import BGW.Skorokhod.VervaatAligned
import BGW.Skorokhod.VervaatWindowApproximation
import BGW.Skorokhod.RestrictContinuity

/-!
# Continuity of the càdlàg Vervaat map

A positive minimizing time and continuity there give continuity at the terminal
endpoint. Positivity of the minimizing time is essential for this conclusion.
Local correction of J1 time changes near a unique continuous minimum proves
continuity of the transformation without disturbing the other jumps.

References: W. Vervaat, *A relation between Brownian bridge and Brownian excursion*, Ann.
Probab. 7 (1979); T. Duquesne, *A limit theorem for the contour process of conditioned
Galton–Watson trees*, Ann. Probab. 31 (2003), §4; items C33–C34 of `CLASSICAL_THEORY_INPUTS.md`.
-/

@[expose] public section

open Set Filter Topology

namespace BGW.Skorokhod

/-- Continuity at the minimizing time makes the transformed initial value zero. -/
theorem vervaatD_zero_of_continuousAt {f : D 1 ℝ}
    (hg : ContinuousAt f (vervaatTime f)) :
    vervaatD f ⟨0, le_rfl, zero_le_one⟩ = 0 := by
  have hl := hg.continuousWithinAt (s := Iic (vervaatTime f)) |>.leftLim_eq
  have hmin := min_leftLim_vervaatTime f
  rw [hl, min_self] at hmin
  change (if (vervaatTime f : ℝ) + 0 ≤ 1 then _ else _) = 0
  rw [ite_eq_left (by simpa using (vervaatTime f).2.2)]
  rw [add_zero, projIcc_of_mem zero_le_one (vervaatTime f).2]
  exact sub_eq_zero.mpr hmin

/-- Continuity at the original terminal endpoint makes the transformed wrap point continuous. -/
theorem continuousAt_vervaatD_wrap {f : D 1 ℝ}
    (h1 : ContinuousAt f ⟨1, zero_le_one, le_rfl⟩) :
    ContinuousAt (vervaatD f)
      (projIcc 0 1 zero_le_one (1 - (vervaatTime f : ℝ))) := by
  let c := projIcc 0 1 zero_le_one (1 - (vervaatTime f : ℝ))
  have hc : (c : ℝ) = 1 - (vervaatTime f : ℝ) := by
    rw [show c = projIcc 0 1 zero_le_one (1 - (vervaatTime f : ℝ)) from rfl,
      projIcc_of_mem zero_le_one
        (show 1 - (vervaatTime f : ℝ) ∈ Icc (0 : ℝ) 1 by
          constructor <;> linarith [(vervaatTime f).2.1, (vervaatTime f).2.2])]
  let a : Icc (0 : ℝ) 1 → Icc (0 : ℝ) 1 :=
    fun t => projIcc 0 1 zero_le_one ((vervaatTime f : ℝ) + t)
  have ha : Continuous a := continuous_projIcc.comp
    (continuous_const.add continuous_subtype_val)
  have hac : a c = ⟨1, zero_le_one, le_rfl⟩ := by
    dsimp [a]
    rw [show (vervaatTime f : ℝ) + c = 1 by linarith, projIcc_right]
  have hcont : ContinuousAt (fun t => f (a t) - ⨅ s, f s) c :=
    ((hac ▸ h1).comp ha.continuousAt).sub_const _
  have hval : vervaatD f c = f (a c) - ⨅ s, f s :=
    ite_eq_left (by change (vervaatTime f : ℝ) + c ≤ 1; linarith)
  change Tendsto (vervaatD f) (𝓝 c) (𝓝 (vervaatD f c))
  rw [← nhdsLE_sup_nhdsGT c, tendsto_sup]
  refine ⟨?_, (isCadlag (vervaatD f)).isRightContinuous c⟩
  rw [hval]
  apply (tendsto_congr' (show (vervaatD f : Icc (0 : ℝ) 1 → ℝ) =ᶠ[𝓝[≤] c]
    (fun t => f (a t) - ⨅ s, f s) from ?_)).2
  · exact hcont.tendsto.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with t ht
    have ht' : (t : ℝ) ≤ c := ht
    exact ite_eq_left (by linarith)

/-- If the first infimum time is positive and `f` is continuous there, then `V f` is continuous
at `1` with value `f 1 - f 0` (C33.3, with the corrected premise `0 < g` of roadmap §8.3: for
`f t = t` on `[0,1)` and `f 1 = 2` one has `g = 0` and `V f = f`, discontinuous at `1`). -/
theorem vervaatD_one_of_continuousAt {f : D 1 ℝ} (hg0 : 0 < (vervaatTime f : ℝ))
    (hg : ContinuousAt f (vervaatTime f)) :
    vervaatD f ⟨1, zero_le_one, le_rfl⟩ = f ⟨1, zero_le_one, le_rfl⟩ - f ⟨0, le_rfl, zero_le_one⟩ ∧
      ContinuousAt (vervaatD f) ⟨1, zero_le_one, le_rfl⟩ := by
  have hmin : f (vervaatTime f) = ⨅ s, f s := by
    have hl := hg.continuousWithinAt (s := Iic (vervaatTime f)) |>.leftLim_eq
    simpa only [hl, min_self] using min_leftLim_vervaatTime f
  have hnot : ¬ (vervaatTime f : ℝ) + 1 ≤ 1 := by linarith
  have hproj : projIcc 0 1 zero_le_one ((vervaatTime f : ℝ) + 1 - 1) =
      vervaatTime f := by simp
  constructor
  · change (if (vervaatTime f : ℝ) + 1 ≤ 1 then _ else _) = _
    rw [ite_eq_right hnot, hproj, hmin]
    ring
  · let b : Icc (0 : ℝ) 1 → Icc (0 : ℝ) 1 :=
      fun t => projIcc 0 1 zero_le_one ((vervaatTime f : ℝ) + t - 1)
    have hb : Continuous b := continuous_projIcc.comp
      ((continuous_const.add continuous_subtype_val).sub continuous_const)
    have hb1 : b ⟨1, zero_le_one, le_rfl⟩ = vervaatTime f := hproj
    have hc : ContinuousAt (fun t => f (b t) + f ⟨1, zero_le_one, le_rfl⟩ -
        (⨅ s, f s) - f ⟨0, le_rfl, zero_le_one⟩) ⟨1, zero_le_one, le_rfl⟩ := by
      have hcomp : ContinuousAt (fun t => f (b t)) ⟨1, zero_le_one, le_rfl⟩ :=
        (hb1 ▸ hg).comp hb.continuousAt
      exact ((hcomp.add_const _).sub_const _).sub_const _
    apply hc.congr_of_eventuallyEq
    have he : ∀ᶠ t : Icc (0 : ℝ) 1 in 𝓝 ⟨1, zero_le_one, le_rfl⟩,
        1 < (vervaatTime f : ℝ) + t :=
      (continuous_const.add continuous_subtype_val).continuousAt.eventually
        (eventually_gt_nhds (by simpa using hg0 : 1 < (vervaatTime f : ℝ) + 1))
    filter_upwards [he] with t ht
    exact ite_eq_right ht.not_ge

/-- Continuity of the càdlàg Vervaat map (C34): at a path vanishing at `0`, continuous at `1`,
whose infimum is attained (as a value or left limit) only at an interior time `g` where the path
is continuous. Moreover `V f` vanishes at `0` and is continuous at `1 - g`. -/
theorem continuousAt_vervaatD {f : D 1 ℝ} (h0 : f ⟨0, le_rfl, zero_le_one⟩ = 0)
    (h1 : ContinuousAt f ⟨1, zero_le_one, le_rfl⟩)
    (huniq : ∀ t : Set.Icc (0 : ℝ) 1,
      min (Function.leftLim f t) (f t) = ⨅ s, f s → t = vervaatTime f)
    (hint : 0 < (vervaatTime f : ℝ) ∧ (vervaatTime f : ℝ) < 1)
    (hg : ContinuousAt f (vervaatTime f)) :
    ContinuousAt vervaatD f ∧ vervaatD f ⟨0, le_rfl, zero_le_one⟩ = 0 ∧
      ContinuousAt (vervaatD f) (Set.projIcc 0 1 zero_le_one (1 - (vervaatTime f : ℝ))) := by
  have hstart : vervaatD f ⟨0, le_rfl, zero_le_one⟩ = f ⟨0, le_rfl, zero_le_one⟩ := by
    rw [vervaatD_zero_of_continuousAt hg, h0]
  refine ⟨?_, hstart.trans h0, continuousAt_vervaatD_wrap h1⟩
  obtain ⟨σ, hdisp, hpath⟩ :=
    (tendsto_iff_exists_timeChange (u := id) (f := f)).mp tendsto_id
  have htime : Tendsto (fun u : D 1 ℝ => vervaatTime u) (𝓝 f) (𝓝 (vervaatTime f)) :=
    continuousAt_vervaatTime huniq
  have hinf : Tendsto (fun u : D 1 ℝ => ⨅ s, u s) (𝓝 f) (𝓝 (⨅ s, f s)) :=
    (lipschitzWith_one_iInf zero_le_one).continuous.continuousAt
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let e := ε / 20
  have he : 0 < e := by dsimp [e]; positivity
  obtain ⟨r, hr, hfr⟩ := Metric.continuousAt_iff.mp hg e he
  have hsmall : 0 < min (r / 4) (min ((vervaatTime f : ℝ) / 2)
      (min ((1 - (vervaatTime f : ℝ)) / 2) (ε / 100))) := by
    apply lt_min (by positivity)
    apply lt_min (by linarith [hint.1])
    exact lt_min (by linarith [hint.2]) (by positivity)
  obtain ⟨η, hη, hηbounds⟩ := exists_between hsmall
  obtain ⟨hηr, hηg, hη1, hηε⟩ : η < r / 4 ∧ η < (vervaatTime f : ℝ) / 2 ∧
      η < (1 - (vervaatTime f : ℝ)) / 2 ∧ η < ε / 100 := by
    simpa only [lt_min_iff] using hηbounds
  have hd := (tendsto_order.mp hdisp).2 (η / 4) (by positivity)
  have hp := (tendsto_order.mp hpath).2 e he
  have ht := Metric.tendsto_nhds.mp htime (η / 4) (by positivity)
  have hm := Metric.tendsto_nhds.mp hinf e he
  filter_upwards [hd, hp, ht, hm] with u huD huP huT huM
  have hD (t : Icc (0 : ℝ) 1) : |(σ u t : ℝ) - t| ≤ η / 4 :=
    (le_ciSup (bddAbove_displacement zero_le_one (σ u)) t).trans huD.le
  have hP (t : Icc (0 : ℝ) 1) : dist (u (σ u t)) (f t) ≤ e :=
    (le_ciSup (bddAbove_comp_dist zero_le_one u f (σ u)) t).trans huP.le
  have hnear : dist ((σ u).symm (vervaatTime u)) (vervaatTime f) < η := by
    let z := (σ u).symm (vervaatTime u)
    have hz : dist (vervaatTime u) z ≤ η / 4 := by
      simpa only [Subtype.dist_eq, Real.dist_eq, z, OrderIso.apply_symm_apply] using hD z
    rw [dist_comm] at hz
    exact (dist_triangle z (vervaatTime u) (vervaatTime f)).trans_lt (by linarith)
  have hwindow (s : Icc (0 : ℝ) 1) (hs : dist s (vervaatTime f) < 2 * η) :
      dist (f s) (f (vervaatTime f)) ≤ e :=
    (hfr (by linarith)).le
  obtain ⟨ρ, hρg, hρD, hρP⟩ := exists_aligned_timeChange u f (σ u)
    (vervaatTime f) (vervaatTime u) hη (by linarith) (by linarith)
    hnear hD hP hwindow
  obtain ⟨μ, hμD, hμP⟩ := exists_vervaat_timeChange_bound u f ρ hρg hρD hρP
    (huM.le.trans (by linarith : e ≤ 3 * e))
  have hμD' : (⨆ t, |(μ t : ℝ) - t|) < ε := by
    have hle := ciSup_le hμD
    have hT : |(vervaatTime u : ℝ) - vervaatTime f| < η / 4 := by
      simpa only [Subtype.dist_eq, Real.dist_eq] using huT
    exact hle.trans_lt (by linarith)
  have hμP' : (⨆ t, dist (vervaatD f t) (vervaatD u (μ t))) < ε := by
    have hle : (⨆ t, dist (vervaatD f t) (vervaatD u (μ t))) ≤ 4 * (3 * e) :=
      ciSup_le fun t => by simpa only [dist_comm] using hμP t
    exact hle.trans_lt (by dsimp [e]; linarith)
  calc
    dist (vervaatD u) (vervaatD f) = j1Dist (vervaatD f) (vervaatD u) := by
      rw [dist_comm, dist_eq_j1Dist]
    _ ≤ max (⨆ t, |(μ t : ℝ) - t|) (⨆ t, dist (vervaatD f t) (vervaatD u (μ t))) :=
      j1Dist_le_timeChange_cost zero_le_one _ _ μ
    _ < ε := max_lt hμD' hμP'

end BGW.Skorokhod
