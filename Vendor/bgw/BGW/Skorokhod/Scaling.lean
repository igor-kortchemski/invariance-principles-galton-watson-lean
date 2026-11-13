/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.Skorokhod.RestrictContinuity
import BGW.Skorokhod.ScalingTimeChange
import BGW.Skorokhod.ScalingMultiplication

/-!
# Time and space scaling of càdlàg paths

Positive linear time scaling followed by clipping at the terminal time preserves càdlàg paths.
-/

@[expose] public section

open Set Filter Topology

namespace BGW.Skorokhod

variable {T : ℝ} {E : Type*}

/-- Time–space scaling restricted to `[0,a]`: `t ↦ k * g (min (s * t) T)` for a spatial factor
`k` (coordinatewise for `E = Fin d → ℝ`) and a time factor `s > 0` (C6.4). -/
def timeSpaceScale [NormedRing E] (a : ℝ) (hT : 0 ≤ T) (p : D T E × E × Set.Ioi (0 : ℝ)) :
    D a E where
  toFun t := p.2.1 * p.1 ⟨min (p.2.2 * t) T,
    le_min (mul_nonneg (le_of_lt p.2.2.2) t.2.1) hT, min_le_right _ _⟩
  isCadlag' := by
    let s : ℝ := p.2.2
    have hs : 0 < s := p.2.2.2
    let κ : Icc (0 : ℝ) a → Icc (0 : ℝ) T := fun t =>
      ⟨min (s * t) T, le_min (mul_nonneg hs.le t.2.1) hT, min_le_right _ _⟩
    have hκ : Continuous κ := Continuous.subtype_mk
      ((continuous_const.mul continuous_subtype_val).min continuous_const) _
    have hcad : IsCadlag (p.1 ∘ κ) := by
      constructor
      · intro t
        by_cases ht : s * (t : ℝ) < T
        · apply (isCadlag p.1).isRightContinuous (κ t) |>.comp
            hκ.continuousAt.continuousWithinAt
          intro u hu
          change (t : ℝ) < u at hu
          change min (s * (t : ℝ)) T < min (s * (u : ℝ)) T
          rw [min_eq_left ht.le]
          exact lt_min (mul_lt_mul_of_pos_left hu hs) ht
        · have heq (u : Icc (0 : ℝ) a) (hu : u ∈ Ioi t) : κ u = κ t := by
            apply Subtype.ext
            have htu : (t : ℝ) < u := hu
            change min (s * (u : ℝ)) T = min (s * (t : ℝ)) T
            rw [min_eq_right (le_of_not_gt ht),
              min_eq_right ((le_of_not_gt ht).trans
                (mul_le_mul_of_nonneg_left htu.le hs.le))]
          exact tendsto_nhdsWithin_congr
            (fun u hu => congrArg p.1 (heq u hu).symm) tendsto_const_nhds
      · intro t
        by_cases ht : s * (t : ℝ) ≤ T
        · obtain ⟨l, hl⟩ := (isCadlag p.1).tendsto_nhdsLT (κ t)
          refine ⟨l, hl.comp (tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩)⟩
          · exact tendsto_nhdsWithin_of_tendsto_nhds hκ.continuousAt
          · filter_upwards [self_mem_nhdsWithin] with u hu
            have hut : (u : ℝ) < t := hu
            change min (s * (u : ℝ)) T < min (s * (t : ℝ)) T
            rw [min_eq_left ht, min_eq_left
              ((mul_lt_mul_of_pos_left hut hs).le.trans ht)]
            exact mul_lt_mul_of_pos_left hut hs
        · have ht' : T < s * (t : ℝ) := lt_of_not_ge ht
          have hmem : ∀ᶠ u : Icc (0 : ℝ) a in 𝓝[<] t, T < s * (u : ℝ) :=
            (tendsto_nhdsWithin_of_tendsto_nhds
              ((continuous_const.mul continuous_subtype_val).continuousAt)).eventually
                (Ioi_mem_nhds ht')
          let top : Icc (0 : ℝ) T := ⟨T, hT, le_rfl⟩
          have heq : (p.1 ∘ κ) =ᶠ[𝓝[<] t] fun _ => p.1 top := by
            filter_upwards [hmem] with u hu
            apply congrArg p.1
            exact Subtype.ext (min_eq_right hu.le)
          exact ⟨p.1 top, (tendsto_congr' heq).2 tendsto_const_nhds⟩
    exact hcad.continuous_comp (continuous_const.mul continuous_id)


private theorem tendsto_timeScale_one [NormedRing E] {a : ℝ} (ha : 0 < a) (haT : a < T)
    {f : D T E} (hf : ContinuousAt f ⟨a, ha.le, haT.le⟩)
    {ι : Type*} {l : Filter ι} {u : ι → D T E} {s : ι → Ioi (0 : ℝ)}
    (hu : Tendsto u l (𝓝 f)) (hs : Tendsto (fun i => (s i : ℝ)) l (𝓝 1)) :
    Tendsto (fun i => timeSpaceScale a (ha.le.trans haT.le) (u i, 1, s i)) l
      (𝓝 (restrict haT.le f)) := by
  have : Nonempty (Icc (0 : ℝ) T) := ⟨⟨0, le_rfl, ha.le.trans haT.le⟩⟩
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨η, hη, hηrest⟩ :=
    (Metric.continuousAt_iff.mp (continuousAt_restrict ha.le haT.le hf)) ε hε
  have hγ := eventually_exists_timeChange_scale ha haT hs (show 0 < η / 4 by positivity)
  have hu' := Metric.tendsto_nhds.mp hu (η / 2) (by positivity)
  filter_upwards [hγ, hu'] with i hi hui
  obtain ⟨γ, hhead, hdisp⟩ := hi
  have hdist : dist (reparam (u i) γ) (u i) ≤ η / 4 :=
    (dist_reparam_le (ha.le.trans haT.le) (u i) γ).trans (ciSup_le hdisp)
  have hw : dist (reparam (u i) γ) f < η :=
    (dist_triangle _ _ _).trans_lt (by linarith)
  have heq : timeSpaceScale a (ha.le.trans haT.le) (u i, 1, s i) =
      restrict haT.le (reparam (u i) γ) := by
    apply ext
    intro t
    let tT : Icc (0 : ℝ) T := ⟨t, t.2.1, t.2.2.trans haT.le⟩
    have hh : (γ tT : ℝ) = (s i : ℝ) * t := hhead tT t.2.2
    have hb : (s i : ℝ) * t ≤ T := by rw [← hh]; exact (γ tT).2.2
    change 1 * u i _ = u i (γ tT)
    rw [one_mul]
    apply congrArg (u i)
    exact Subtype.ext (by simpa only [min_eq_left hb] using hh.symm)
  simpa only [heq] using hηrest hw

/-- Time–space scaling is continuous at `(f, 1, 1)` when `f` is continuous at `a < T`
(C6.4, the core of the source's Lemma 5.7). -/
theorem continuousAt_timeSpaceScale [NormedRing E] {a : ℝ} (ha : 0 < a) (haT : a < T)
    {f : D T E} (hf : ContinuousAt f ⟨a, ha.le, haT.le⟩) :
    ContinuousAt (timeSpaceScale a (ha.le.trans haT.le)) (f, 1, ⟨1, Set.mem_Ioi.mpr one_pos⟩) := by
  let p₀ : D T E × E × Ioi (0 : ℝ) := (f, 1, ⟨1, one_pos⟩)
  have hu : Tendsto (fun p : D T E × E × Ioi (0 : ℝ) => p.1) (𝓝 p₀) (𝓝 f) :=
    continuous_fst.continuousAt
  have hs : Tendsto (fun p : D T E × E × Ioi (0 : ℝ) => (p.2.2 : ℝ))
      (𝓝 p₀) (𝓝 1) :=
    continuous_subtype_val.continuousAt.comp continuous_snd.snd.continuousAt
  have hk : Tendsto (fun p : D T E × E × Ioi (0 : ℝ) => p.2.1)
      (𝓝 p₀) (𝓝 1) := continuous_snd.fst.continuousAt
  have hv := tendsto_timeScale_one ha haT hf hu hs
  have hm := tendsto_mulPath_one ha.le hv hk
  have heq : (fun p : D T E × E × Ioi (0 : ℝ) =>
      mulPath p.2.1 (timeSpaceScale a (ha.le.trans haT.le) (p.1, 1, p.2.2))) =
      timeSpaceScale a (ha.le.trans haT.le) := by
    funext p
    apply ext
    intro t
    simp [mulPath, timeSpaceScale]
  rw [heq] at hm
  have hbase : timeSpaceScale a (ha.le.trans haT.le) p₀ = restrict haT.le f := by
    apply ext
    intro t
    change 1 * f _ = f _
    rw [one_mul]
    apply congrArg f
    apply Subtype.ext
    simp only [p₀, one_mul, min_eq_left (t.2.2.trans haT.le)]
  change Tendsto _ (𝓝 p₀) (𝓝 (timeSpaceScale a (ha.le.trans haT.le) p₀))
  rw [hbase]
  exact hm

end BGW.Skorokhod
