/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.Skorokhod.Continuous

/-!
# Evaluation, restriction and stopping on Skorokhod space

This module proves continuity properties of evaluation and prepares the restriction and stopping
operations on compact intervals.
-/

@[expose] public section

open Set Filter Topology

namespace BGW.Skorokhod

variable {T : ℝ} {E : Type*}

/-- Evaluation at time `0` is 1-Lipschitz (C6.1). -/
theorem lipschitzWith_one_eval_zero [MetricSpace E] (hT : 0 ≤ T) :
    LipschitzWith 1 (fun f : D T E => f ⟨0, le_rfl, hT⟩) := by
  apply LipschitzWith.mk_one
  intro f g
  rw [dist_eq_j1Dist]
  change dist (f ⟨0, le_rfl, hT⟩) (g ⟨0, le_rfl, hT⟩) ≤
    ⨅ σ : TimeChange T, max (⨆ t, |((σ t : ℝ)) - t|)
      (⨆ t, dist (f t) (g (σ t)))
  apply le_ciInf
  intro σ
  let t₀ : Set.Icc (0 : ℝ) T := ⟨0, le_rfl, hT⟩
  have hpoint : dist (f t₀) (g t₀) ≤ ⨆ t, dist (f t) (g (σ t)) := by
    simpa [t₀, TimeChange.apply_zero σ hT] using
      (le_ciSup_of_le (bddAbove_range_dist f g σ) t₀ le_rfl)
  exact hpoint.trans (le_max_of_le_right le_rfl)

/-- Evaluation at the terminal time `T` is 1-Lipschitz (C6.1). -/
theorem lipschitzWith_one_eval_right [MetricSpace E] (hT : 0 ≤ T) :
    LipschitzWith 1 (fun f : D T E => f ⟨T, hT, le_rfl⟩) := by
  apply LipschitzWith.mk_one
  intro f g
  rw [dist_eq_j1Dist]
  change dist (f ⟨T, hT, le_rfl⟩) (g ⟨T, hT, le_rfl⟩) ≤
    ⨅ σ : TimeChange T, max (⨆ t, |((σ t : ℝ)) - t|)
      (⨆ t, dist (f t) (g (σ t)))
  apply le_ciInf
  intro σ
  let tT : Set.Icc (0 : ℝ) T := ⟨T, hT, le_rfl⟩
  have hpoint : dist (f tT) (g tT) ≤ ⨆ t, dist (f t) (g (σ t)) := by
    simpa [tT, TimeChange.apply_top σ hT] using
      (le_ciSup_of_le (bddAbove_range_dist f g σ) tT le_rfl)
  exact hpoint.trans (le_max_of_le_right le_rfl)

/-- Evaluation at `t` is continuous at every path continuous at `t` (C6.1). -/
theorem continuousAt_eval [MetricSpace E] {f : D T E} {t : Set.Icc (0 : ℝ) T}
    (hf : ContinuousAt f t) : ContinuousAt (fun g : D T E => g t) f := by
  change Tendsto (fun g : D T E => g t) (𝓝 f) (𝓝 (f t))
  have hT : 0 ≤ T := le_trans t.property.1 t.property.2
  obtain ⟨σ, hdisp, hpath⟩ :=
    (tendsto_iff_exists_timeChange (u := id) (f := f)).mp tendsto_id
  refine Metric.tendsto_nhds.mpr fun ε hε => ?_
  obtain ⟨δ, hδ, hfδ⟩ := (Metric.continuousAt_iff.mp hf) (ε / 2) (half_pos hε)
  let δ' := min δ (ε / 2)
  have hδ' : 0 < δ' := lt_min hδ (half_pos hε)
  have hdisp' : ∀ᶠ g : D T E in 𝓝 f,
      (⨆ r : Set.Icc (0 : ℝ) T, |((σ g r : ℝ)) - r|) < δ' := by
    have h := Metric.tendsto_nhds.mp hdisp δ' hδ'
    have hnonneg (g : D T E) : 0 ≤
        ⨆ r : Set.Icc (0 : ℝ) T, |((σ g r : ℝ)) - r| := displacement_nonneg (σ g) hT
    filter_upwards [h] with g hg
    simpa [Real.dist_eq, abs_of_nonneg (hnonneg g)] using hg
  have hpath' : ∀ᶠ g : D T E in 𝓝 f,
      (⨆ r : Set.Icc (0 : ℝ) T, dist (g (σ g r)) (f r)) < ε / 2 := by
    have h := Metric.tendsto_nhds.mp hpath (ε / 2) (half_pos hε)
    have hnonneg (g : D T E) : 0 ≤
        ⨆ r : Set.Icc (0 : ℝ) T, dist (g (σ g r)) (f r) :=
      le_ciSup_of_le (bddAbove_comp_dist hT g f (σ g)) ⟨0, by simp [hT]⟩ dist_nonneg
    filter_upwards [h] with g hg
    simpa [Real.dist_eq, abs_of_nonneg (hnonneg g)] using hg
  filter_upwards [hdisp', hpath'] with g hgdisp hgpath
  have hdispInv : (⨆ r : Set.Icc (0 : ℝ) T, |((σ g).symm r : ℝ) - r|) < δ' := by
    simpa only [TimeChange.iSup_abs_sub_symm] using hgdisp
  let s : Set.Icc (0 : ℝ) T := (σ g).symm t
  have hfirst : dist (g t) (f s) ≤ ⨆ r : Set.Icc (0 : ℝ) T, dist (g (σ g r)) (f r) := by
    have hh : dist (g (σ g s)) (f s) ≤
        ⨆ r : Set.Icc (0 : ℝ) T, dist (g (σ g r)) (f r) :=
      le_ciSup (bddAbove_comp_dist hT g f (σ g)) s
    simpa [s] using hh
  have hs : dist s t < δ := by
    have hbound : |((σ g).symm t : ℝ) - t| ≤
        ⨆ r : Set.Icc (0 : ℝ) T, |((σ g).symm r : ℝ) - r| :=
      le_ciSup (bddAbove_displacement hT (σ g).symm) t
    have hs' : dist s t = |((σ g).symm t : ℝ) - t| := by
      simp [s, Subtype.dist_eq, Real.dist_eq]
    rw [hs']
    exact lt_of_le_of_lt hbound (lt_of_lt_of_le hdispInv (min_le_left _ _))
  have hsecond : dist (f s) (f t) < ε / 2 := hfδ hs
  calc
    dist (g t) (f t) ≤ dist (g t) (f s) + dist (f s) (f t) := dist_triangle _ _ _
    _ < ε := by linarith [hfirst, hgpath, hsecond]

/-- Restriction of a path on `[0,T]` to `[0,a]` (C6.2). -/
def restrict [TopologicalSpace E] {a : ℝ} (haT : a ≤ T) (f : D T E) : D a E where
  toFun t := f ⟨t, t.2.1, t.2.2.trans haT⟩
  isCadlag' := by
    let inc : Set.Icc (0 : ℝ) a → Set.Icc (0 : ℝ) T := fun t =>
      ⟨t, t.2.1, t.2.2.trans haT⟩
    have hinc : Continuous inc :=
      Continuous.subtype_mk continuous_subtype_val fun t => ⟨t.property.1, t.property.2.trans haT⟩
    change IsCadlag (f ∘ inc)
    constructor
    · intro x
      have hmap : MapsTo inc (Set.Ioi x) (Set.Ioi (inc x)) := by
        intro y hy
        change (y : ℝ) > (x : ℝ) at hy ⊢
        exact hy
      exact (isCadlag f).isRightContinuous (inc x) |>.comp
        (hinc.continuousAt.continuousWithinAt) hmap
    · intro x
      obtain ⟨l, hl⟩ := (isCadlag f).tendsto_nhdsLT (inc x)
      have hmem : ∀ᶠ y in 𝓝[Set.Iio x] x, inc y ∈ Set.Iio (inc x) := by
        filter_upwards [self_mem_nhdsWithin] with y hy
        change (y : ℝ) < (x : ℝ) at hy ⊢
        exact hy
      have hincLeft : Tendsto inc (𝓝[Set.Iio x] x) (𝓝[Set.Iio (inc x)] (inc x)) :=
        tendsto_nhdsWithin_iff.mpr
          ⟨tendsto_nhdsWithin_of_tendsto_nhds hinc.continuousAt, hmem⟩
      exact ⟨l, hl.comp hincLeft⟩

/-- Constant extension of a path on `[0,a]` to `[0,T]`: `t ↦ g (min t a)` (C6.2). -/
def extendConst [TopologicalSpace E] {a : ℝ} (ha : 0 ≤ a) (haT : a ≤ T) (g : D a E) : D T E where
  toFun t := g ⟨min (t : ℝ) a, le_min t.2.1 ha, min_le_right _ _⟩
  isCadlag' := by
    let κ : Set.Icc (0 : ℝ) T → Set.Icc (0 : ℝ) a := fun t =>
      ⟨min (t : ℝ) a, le_min t.2.1 ha, min_le_right _ _⟩
    have hκ : Continuous κ := Continuous.subtype_mk
      (continuous_subtype_val.min continuous_const) fun t => ⟨le_min t.property.1 ha, min_le_right _ _⟩
    change IsCadlag (g ∘ κ)
    constructor
    · intro t
      by_cases ht : (t : ℝ) < a
      · have hmap : MapsTo κ (Set.Ioi t) (Set.Ioi (κ t)) := by
          intro s hs
          change (s : ℝ) > (t : ℝ) at hs
          change min (s : ℝ) a > min (t : ℝ) a
          rw [min_eq_left (le_of_lt ht)]
          exact lt_min_iff.mpr ⟨hs, ht⟩
        exact (isCadlag g).isRightContinuous (κ t) |>.comp
          (hκ.continuousAt.continuousWithinAt) hmap
      · have heq (s : Set.Icc (0 : ℝ) T) (hs : s ∈ Set.Ioi t) : κ s = κ t := by
          apply Subtype.ext
          change min (s : ℝ) a = min (t : ℝ) a
          have hta : a ≤ (t : ℝ) := le_of_not_gt ht
          change (t : ℝ) < (s : ℝ) at hs
          rw [min_eq_right hta, min_eq_right (le_trans hta hs.le)]
        exact tendsto_nhdsWithin_congr
          (fun s hs => congrArg g (heq s hs).symm) tendsto_const_nhds
    · intro t
      by_cases ht : (t : ℝ) ≤ a
      · obtain ⟨l, hl⟩ := (isCadlag g).tendsto_nhdsLT (κ t)
        have hmem : ∀ᶠ s in 𝓝[Set.Iio t] t, κ s ∈ Set.Iio (κ t) := by
          filter_upwards [self_mem_nhdsWithin] with s hs
          change (s : ℝ) < (t : ℝ) at hs
          change min (s : ℝ) a < min (t : ℝ) a
          have hsa : (s : ℝ) < a := lt_of_lt_of_le hs ht
          rw [min_eq_left hsa.le, min_eq_left ht]
          exact hs
        have hκleft : Tendsto κ (𝓝[Set.Iio t] t) (𝓝[Set.Iio (κ t)] (κ t)) :=
          tendsto_nhdsWithin_iff.mpr
            ⟨tendsto_nhdsWithin_of_tendsto_nhds hκ.continuousAt, hmem⟩
        exact ⟨l, hl.comp hκleft⟩
      · have hta : a < (t : ℝ) := lt_of_not_ge ht
        let a' : Set.Icc (0 : ℝ) a := ⟨a, ha, le_rfl⟩
        let aT : Set.Icc (0 : ℝ) T := ⟨a, ha, haT⟩
        have hta' : aT < t := by change a < (t : ℝ); exact hta
        have hmem : (Set.Iio t ∩ Set.Ioi aT) ∈ 𝓝[Set.Iio t] t :=
          inter_mem_nhdsWithin (Set.Iio t) (Ioi_mem_nhds hta')
        have heq : (fun s : Set.Icc (0 : ℝ) T => g (κ s)) =ᶠ[𝓝[Set.Iio t] t]
            fun _ => g a' := by
          filter_upwards [hmem] with s hs
          have hsa' : aT < s := hs.2
          have hsa : a < (s : ℝ) := hsa'
          have hκs : κ s = a' := by
            apply Subtype.ext
            change min (s : ℝ) a = a
            exact min_eq_right hsa.le
          simp [hκs]
        have hconst : Tendsto (fun _ : Set.Icc (0 : ℝ) T => g a')
            (𝓝[Set.Iio t] t) (𝓝 (g a')) := tendsto_const_nhds
        exact ⟨g a', (tendsto_congr' heq).2 hconst⟩

private noncomputable def extendTimeChange {T a : ℝ} (_ha : 0 ≤ a) (haT : a ≤ T)
    (σ : TimeChange a) : TimeChange T := by
  let τ : Set.Icc (0 : ℝ) T → Set.Icc (0 : ℝ) T := fun t =>
    if ht : (t : ℝ) ≤ a then
      ⟨(σ ⟨t, t.property.1, ht⟩ : ℝ), (σ ⟨t, t.property.1, ht⟩).property.1,
        (σ ⟨t, t.property.1, ht⟩).property.2.trans haT⟩
    else t
  let inv : Set.Icc (0 : ℝ) T → Set.Icc (0 : ℝ) T := fun t =>
    if ht : (t : ℝ) ≤ a then
      ⟨(σ.symm ⟨t, t.property.1, ht⟩ : ℝ), (σ.symm ⟨t, t.property.1, ht⟩).property.1,
        (σ.symm ⟨t, t.property.1, ht⟩).property.2.trans haT⟩
    else t
  have hstrict : StrictMono τ := by
    intro x y hxy
    change (τ x : ℝ) < (τ y : ℝ)
    by_cases hx : (x : ℝ) ≤ a <;> by_cases hy : (y : ℝ) ≤ a
    · let x' : Set.Icc (0 : ℝ) a := ⟨x, x.property.1, hx⟩
      let y' : Set.Icc (0 : ℝ) a := ⟨y, y.property.1, hy⟩
      have hxy' : x' < y' := hxy
      simpa [τ, hx, hy, x', y'] using σ.strictMono hxy'
    · have hσx : (τ x : ℝ) ≤ a := by
        simpa [τ, hx] using (σ ⟨x, x.property.1, hx⟩).property.2
      have hy' : a < (y : ℝ) := lt_of_not_ge hy
      have hτy : (τ y : ℝ) = y := by simp [τ, hy]
      rw [hτy]
      exact lt_of_le_of_lt hσx hy'
    · have hx' : a < (x : ℝ) := lt_of_not_ge hx
      have hxyR : (x : ℝ) < (y : ℝ) := hxy
      exact False.elim ((not_lt_of_ge (le_trans hxyR.le hy)) hx')
    · simpa [τ, hx, hy] using hxy
  have hright : Function.RightInverse inv τ := by
    intro y
    apply Subtype.ext
    by_cases hy : (y : ℝ) ≤ a
    · let y' : Set.Icc (0 : ℝ) a := ⟨y, y.property.1, hy⟩
      have hsym : (σ.symm y' : ℝ) ≤ a := (σ.symm y').property.2
      let z : Set.Icc (0 : ℝ) a :=
        ⟨σ.symm y', (σ.symm y').property.1, (σ.symm y').property.2⟩
      have hz : z = σ.symm y' := by apply Subtype.ext; rfl
      calc
        (τ (inv y) : ℝ) = (σ (σ.symm y') : ℝ) := by
          simp [τ, inv, hy, y', hsym, z, hz]
        _ = y := by
          have hσ : σ (σ.symm y') = y' := σ.apply_symm_apply y'
          exact congrArg (fun q : Set.Icc (0 : ℝ) a => (q : ℝ)) hσ
    · simp [τ, inv, hy]
  refine {
    toFun := τ
    invFun := inv
    left_inv := ?_
    right_inv := hright
    map_rel_iff' := ?_ }
  · intro x
    apply hstrict.injective
    exact hright (τ x)
  · intro x y
    change τ x ≤ τ y ↔ x ≤ y
    constructor
    · intro hxy
      by_contra h
      exact (not_lt_of_ge hxy) (hstrict (lt_of_not_ge h))
    · intro hxy
      exact hstrict.monotone hxy

private theorem extendTimeChange_apply {T a : ℝ} (ha : 0 ≤ a) (haT : a ≤ T)
    (σ : TimeChange a) (t : Set.Icc (0 : ℝ) T) :
    (extendTimeChange ha haT σ t : ℝ) =
      if ht : (t : ℝ) ≤ a then (σ ⟨t, t.property.1, ht⟩ : ℝ) else t := by
  by_cases ht : (t : ℝ) ≤ a <;> simp [extendTimeChange, ht]

/-- Constant extension is 1-Lipschitz (C6.2). -/
theorem lipschitzWith_one_extendConst [MetricSpace E] {a : ℝ} (ha : 0 ≤ a) (haT : a ≤ T) :
    LipschitzWith 1 (extendConst (E := E) (T := T) ha haT) := by
  apply LipschitzWith.mk_one
  intro g h
  rw [dist_eq_j1Dist]
  change j1Dist (extendConst ha haT g) (extendConst ha haT h) ≤
    ⨅ σ : TimeChange a,
      max (⨆ t, |((σ t : ℝ)) - t|) (⨆ t, dist (g t) (h (σ t)))
  apply le_ciInf
  intro σ
  let τ : TimeChange T := extendTimeChange ha haT σ
  have htime : (⨆ t : Set.Icc (0 : ℝ) T, |((τ t : ℝ)) - t|) ≤
      ⨆ s : Set.Icc (0 : ℝ) a, |((σ s : ℝ)) - s| := by
    refine csSup_le ⟨_, ⟨⟨0, by simp [ha.trans haT]⟩, rfl⟩⟩ ?_
    rintro x ⟨t, rfl⟩
    change |(τ t : ℝ) - t| ≤ _
    by_cases ht : (t : ℝ) ≤ a
    · let s : Set.Icc (0 : ℝ) a := ⟨t, t.property.1, ht⟩
      have hτ : (τ t : ℝ) = σ s := by
        rw [extendTimeChange_apply]
        simp [s, ht]
      rw [hτ]
      exact le_ciSup (bddAbove_displacement ha σ) s
    · have hτ : (τ t : ℝ) = t := by
        rw [extendTimeChange_apply]
        simp [ht]
      rw [hτ]
      simpa using (displacement_nonneg σ ha)
  have hpath : (⨆ t : Set.Icc (0 : ℝ) T,
      dist ((extendConst ha haT g) t) ((extendConst ha haT h) (τ t))) ≤
      ⨆ s : Set.Icc (0 : ℝ) a, dist (g s) (h (σ s)) := by
    refine csSup_le ⟨_, ⟨⟨0, by simp [ha.trans haT]⟩, rfl⟩⟩ ?_
    rintro x ⟨t, rfl⟩
    change dist ((extendConst ha haT g) t) ((extendConst ha haT h) (τ t)) ≤ _
    by_cases ht : (t : ℝ) ≤ a
    · let s : Set.Icc (0 : ℝ) a := ⟨t, t.property.1, ht⟩
      have hτ : (τ t : ℝ) = σ s := by
        rw [extendTimeChange_apply]
        simp [s, ht]
      have hσa : (σ s : ℝ) ≤ a := (σ s).property.2
      simpa [extendConst, s, min_eq_left ht, hτ, min_eq_left hσa] using
        (le_ciSup (bddAbove_range_dist g h σ) s)
    · have hta : a < (t : ℝ) := lt_of_not_ge ht
      let a' : Set.Icc (0 : ℝ) a := ⟨a, ha, le_rfl⟩
      have hτ : (τ t : ℝ) = t := by
        rw [extendTimeChange_apply]
        simp [ht]
      have hσa : σ a' = a' := TimeChange.apply_top σ ha
      have hpoint : dist (g a') (h a') ≤
          ⨆ s : Set.Icc (0 : ℝ) a, dist (g s) (h (σ s)) := by
        simpa [hσa] using le_ciSup (bddAbove_range_dist g h σ) a'
      simpa [extendConst, a', hτ, min_eq_right hta.le] using hpoint
  have hcost := j1Dist_le_timeChange_cost (ha.trans haT)
    (extendConst ha haT g) (extendConst ha haT h) τ
  exact hcost.trans (max_le_max htime hpath)

private theorem clamp_eq_min_clamp {T a t : ℝ} (hT : 0 ≤ T) (ht0 : 0 ≤ t)
    (htT : t ≤ T) : max 0 (min t a) = min t (max 0 (min a T)) := by
  by_cases ha0 : a < 0
  · have haT : a ≤ T := le_trans ha0.le hT
    calc
      max 0 (min t a) = 0 := by
        rw [min_eq_right (le_trans ha0.le ht0), max_eq_left ha0.le]
      _ = min t (max 0 (min a T)) := by
        rw [min_eq_left haT, max_eq_left ha0.le, min_eq_right ht0]
  · have h0a : 0 ≤ a := le_of_not_gt ha0
    by_cases haT : a ≤ T
    · have hmin : 0 ≤ min t a := le_min ht0 h0a
      simp [max_eq_right hmin, max_eq_right h0a, min_eq_left haT]
    · have hTa : T < a := lt_of_not_ge haT
      have hta : t < a := lt_of_le_of_lt htT hTa
      calc
        max 0 (min t a) = t := by rw [min_eq_left hta.le, max_eq_right ht0]
        _ = min t (max 0 (min a T)) := by
          rw [min_eq_right hTa.le, max_eq_right hT, min_eq_left htT]

/-- The path stopped at time `a`: `t ↦ f (max 0 (min t a))`; total in `a` (C6.2). -/
def stop [TopologicalSpace E] (a : ℝ) (f : D T E) : D T E where
  toFun t := f ⟨max 0 (min (t : ℝ) a), le_max_left _ _,
    max_le (t.2.1.trans t.2.2) ((min_le_left _ _).trans t.2.2)⟩
  isCadlag' := by
    by_cases hT : 0 ≤ T
    · let b : ℝ := max 0 (min a T)
      have hb : 0 ≤ b := le_max_left _ _
      have hbT : b ≤ T := by
        dsimp [b]
        exact max_le hT (min_le_right _ _)
      let g : D T E := extendConst hb hbT (restrict hbT f)
      have heq : (fun t : Set.Icc (0 : ℝ) T =>
          f ⟨max 0 (min (t : ℝ) a), le_max_left _ _,
            max_le (t.2.1.trans t.2.2) ((min_le_left _ _).trans t.2.2)⟩) = g := by
        funext t
        apply congrArg f
        apply Subtype.ext
        change max 0 (min (t : ℝ) a) = min (t : ℝ) b
        exact clamp_eq_min_clamp hT t.property.1 t.property.2
      simpa only [heq] using isCadlag g
    · have hempty : IsEmpty (Set.Icc (0 : ℝ) T) :=
        ⟨fun t => (not_le_of_gt (lt_of_not_ge hT)) (le_trans t.property.1 t.property.2)⟩
      constructor
      · intro t
        exact isEmptyElim t
      · intro t
        exact isEmptyElim t

/-- For `0 ≤ a ≤ T`, stopping is extension after restriction (C6.2). -/
theorem stop_eq_extendConst_restrict [TopologicalSpace E] {a : ℝ} (ha : 0 ≤ a) (haT : a ≤ T)
    (f : D T E) : stop a f = extendConst ha haT (restrict haT f) := by
  apply DFunLike.ext
  intro t
  apply congrArg f
  apply Subtype.ext
  change max 0 (min (t : ℝ) a) = min (t : ℝ) a
  have hmin : 0 ≤ min (t : ℝ) a := le_min t.property.1 ha
  rw [max_eq_right hmin]

/-- Stopped-path approximation (C7). -/
theorem dist_stop_le [MetricSpace E] {a : ℝ} (ha : 0 ≤ a) (haT : a ≤ T) (f : D T E) :
    dist (stop a f) f ≤ ⨆ s : {s : Set.Icc (0 : ℝ) T // a ≤ (s : ℝ)},
      dist (f s) (f ⟨a, ha, haT⟩) := by
  have hT : 0 ≤ T := le_trans ha haT
  let a' : Set.Icc (0 : ℝ) T := ⟨a, ha, haT⟩
  let c : D T E := ⟨fun _ => f a', IsCadlag.const⟩
  have hbdd : BddAbove (Set.range fun s : {s : Set.Icc (0 : ℝ) T // a ≤ (s : ℝ)} =>
      dist (f s) (f a')) := by
    obtain ⟨C, hC⟩ := bddAbove_range_dist f c (OrderIso.refl _)
    refine ⟨C, ?_⟩
    rintro x ⟨s, rfl⟩
    exact hC ⟨s, rfl⟩
  have htime : (⨆ t : Set.Icc (0 : ℝ) T, |((OrderIso.refl _ t : Set.Icc (0 : ℝ) T) : ℝ) - t|) = 0 := by
    simp
  let osc := ⨆ s : {s : Set.Icc (0 : ℝ) T // a ≤ (s : ℝ)}, dist (f s) (f a')
  have hpoint (t : Set.Icc (0 : ℝ) T) : dist ((stop a f) t) (f t) ≤ osc := by
    by_cases hta : a ≤ (t : ℝ)
    · have hstop : (stop a f) t = f a' := by
        apply congrArg f
        apply Subtype.ext
        change max 0 (min (t : ℝ) a) = a
        rw [min_eq_right hta, max_eq_right ha]
      rw [hstop]
      simpa [osc, dist_comm] using le_ciSup hbdd ⟨t, hta⟩
    · have hta : (t : ℝ) < a := lt_of_not_ge hta
      have hstop : (stop a f) t = f t := by
        apply congrArg f
        apply Subtype.ext
        change max 0 (min (t : ℝ) a) = t
        rw [min_eq_left hta.le, max_eq_right t.property.1]
      rw [hstop]
      calc
        dist (f t) (f t) = 0 := dist_self _
        _ ≤ osc := by simpa [osc] using le_ciSup hbdd ⟨a', le_rfl⟩
  have hpath : (⨆ t : Set.Icc (0 : ℝ) T,
      dist ((stop a f) t) (f ((OrderIso.refl _ : TimeChange T) t))) ≤
      ⨆ s : {s : Set.Icc (0 : ℝ) T // a ≤ (s : ℝ)}, dist (f s) (f a') := by
    refine csSup_le ⟨_, ⟨a', rfl⟩⟩ ?_
    rintro x ⟨t, rfl⟩
    simpa [osc, OrderIso.refl] using hpoint t
  rw [dist_eq_j1Dist]
  calc
    j1Dist (stop a f) f ≤ max 0 (⨆ t : Set.Icc (0 : ℝ) T,
        dist ((stop a f) t) (f ((OrderIso.refl _ : TimeChange T) t)) ) := by
      simpa [htime] using j1Dist_le_timeChange_cost hT (stop a f) f (OrderIso.refl _)
    _ ≤ ⨆ s : {s : Set.Icc (0 : ℝ) T // a ≤ (s : ℝ)}, dist (f s) (f a') := by
      apply max_le
      · simpa [osc] using le_ciSup hbdd ⟨a', le_rfl⟩
      · exact hpath

/-- A path continuous at the terminal time is the J1 limit of its stopped paths (C7). -/
theorem tendsto_stop_nhdsLT [MetricSpace E] (hT : 0 < T) {f : D T E}
    (hf : ContinuousAt f ⟨T, hT.le, le_rfl⟩) :
    Tendsto (fun a => stop a f) (𝓝[<] T) (𝓝 f) := by
  refine Metric.tendsto_nhds.mpr fun ε hε => ?_
  obtain ⟨δ, hδ, hfδ⟩ := (Metric.continuousAt_iff.mp hf) (ε / 4) (by positivity)
  let η := min δ (T / 2)
  have hη : 0 < η := lt_min hδ (by positivity)
  have hinterval : Set.Ioo (T - η) T ∈ 𝓝[<] T := Ioo_mem_nhdsLT (by linarith)
  filter_upwards [hinterval] with a ha
  have haT : a ≤ T := ha.2.le
  have ha0 : 0 ≤ a := by
    have hηT : η ≤ T / 2 := min_le_right _ _
    linarith [ha.1]
  let a' : Set.Icc (0 : ℝ) T := ⟨a, ha0, haT⟩
  let tT : Set.Icc (0 : ℝ) T := ⟨T, hT.le, le_rfl⟩
  have hgapA : T - a < η := by linarith [ha.1]
  have hdistA : dist a' tT < δ := by
    have heq : dist a' tT = T - a := by
      simp [a', tT, Subtype.dist_eq, Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr haT)]
    rw [heq]
    exact lt_of_lt_of_le hgapA (min_le_left _ _)
  have haClose : dist (f a') (f tT) < ε / 4 := hfδ hdistA
  have hosc : (⨆ s : {s : Set.Icc (0 : ℝ) T // a ≤ (s : ℝ)},
      dist (f s) (f a')) ≤ ε / 2 := by
    refine csSup_le ⟨_, ⟨⟨tT, haT⟩, rfl⟩⟩ ?_
    rintro x ⟨s, rfl⟩
    have hsT : (s.1 : ℝ) ≤ T := s.1.property.2
    have hgapS : T - (s.1 : ℝ) ≤ T - a := by linarith [s.property]
    have hdistS : dist s.1 tT < δ := by
      have heq : dist s.1 tT = T - (s.1 : ℝ) := by
        simp [tT, Subtype.dist_eq, Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hsT)]
      rw [heq]
      exact lt_of_le_of_lt hgapS (lt_of_lt_of_le hgapA (min_le_left _ _))
    have hsClose : dist (f s.1) (f tT) < ε / 4 := hfδ hdistS
    have haClose' : dist (f tT) (f a') < ε / 4 := by simpa [dist_comm] using haClose
    calc
      dist (f s.1) (f a') ≤ dist (f s.1) (f tT) + dist (f tT) (f a') := dist_triangle _ _ _
      _ ≤ ε / 4 + ε / 4 := add_le_add hsClose.le haClose'.le
      _ = ε / 2 := by ring
  have hdist : dist (stop a f) f < ε := by
    exact (dist_stop_le ha0 haT f).trans_lt (lt_of_le_of_lt hosc (by linarith))
  exact hdist

private theorem bddBelow_range_path {T : ℝ} (hT : 0 ≤ T) (f : D T ℝ) :
    BddBelow (Set.range f) := by
  let t₀ : Set.Icc (0 : ℝ) T := ⟨0, le_rfl, hT⟩
  have hbound : ∃ C, ∀ x y : Set.Icc (0 : ℝ) T, dist (f x) (f y) ≤ C := by
    rw [← Metric.isBounded_range_iff]
    exact isBounded_range f
  obtain ⟨C, hC⟩ := hbound
  refine ⟨f t₀ - C, ?_⟩
  rintro x ⟨t, rfl⟩
  have hdist : |f t - f t₀| ≤ C := by simpa [Real.dist_eq] using hC t t₀
  linarith [(abs_le.mp hdist).1]

private theorem abs_iInf_sub_le_iSup_dist {T : ℝ} (hT : 0 ≤ T)
    (f g : D T ℝ) (σ : TimeChange T) :
    |(⨅ t, f t) - (⨅ t, g t)| ≤ ⨆ t, dist (f t) (g (σ t)) := by
  let t₀ : Set.Icc (0 : ℝ) T := ⟨0, le_rfl, hT⟩
  have hf : BddBelow (Set.range f) := bddBelow_range_path hT f
  have hg : BddBelow (Set.range g) := bddBelow_range_path hT g
  have hgσ : BddBelow (Set.range fun t : Set.Icc (0 : ℝ) T => g (σ t)) := by
    obtain ⟨b, hb⟩ := hg
    refine ⟨b, ?_⟩
    rintro x ⟨t, rfl⟩
    exact hb ⟨σ t, rfl⟩
  have hcomp : (⨅ t : Set.Icc (0 : ℝ) T, g (σ t)) = ⨅ t, g t := by
    exact Equiv.iInf_comp σ.toEquiv
  have hdistBdd := bddAbove_range_dist f g σ
  let d := ⨆ t : Set.Icc (0 : ℝ) T, dist (f t) (g (σ t))
  have hd (t : Set.Icc (0 : ℝ) T) : dist (f t) (g (σ t)) ≤ d := by
    exact le_ciSup hdistBdd t
  have hlow₁ : (⨅ t : Set.Icc (0 : ℝ) T, g (σ t)) - d ≤ ⨅ t, f t := by
    refine le_csInf ⟨f t₀, ⟨t₀, rfl⟩⟩ ?_
    rintro x ⟨t, rfl⟩
    have hgt : (⨅ s : Set.Icc (0 : ℝ) T, g (σ s)) ≤ g (σ t) := ciInf_le hgσ t
    have habs : |f t - g (σ t)| ≤ d := by simpa [Real.dist_eq] using hd t
    calc
      (⨅ s : Set.Icc (0 : ℝ) T, g (σ s)) - d ≤ g (σ t) - d := sub_le_sub_right hgt d
      _ ≤ f t := by linarith [(abs_le.mp habs).1]
  have hlow₂ : (⨅ t : Set.Icc (0 : ℝ) T, f t) - d ≤ ⨅ t, g (σ t) := by
    refine le_csInf ⟨g (σ t₀), ⟨t₀, rfl⟩⟩ ?_
    rintro x ⟨t, rfl⟩
    have hft : (⨅ s : Set.Icc (0 : ℝ) T, f s) ≤ f t := ciInf_le hf t
    have habs : |f t - g (σ t)| ≤ d := by simpa [Real.dist_eq] using hd t
    calc
      (⨅ s : Set.Icc (0 : ℝ) T, f s) - d ≤ f t - d := sub_le_sub_right hft d
      _ ≤ g (σ t) := by linarith [(abs_le.mp habs).2]
  rw [hcomp] at hlow₂
  have h1 : (⨅ t : Set.Icc (0 : ℝ) T, g t) - (⨅ t, f t) ≤ d := by linarith
  have h2 : (⨅ t : Set.Icc (0 : ℝ) T, f t) - (⨅ t, g t) ≤ d := by linarith
  rw [abs_le]
  exact ⟨by linarith, h2⟩

/-- The infimum of a real path is 1-Lipschitz for J1 (C6.3). -/
theorem lipschitzWith_one_iInf (hT : 0 ≤ T) :
    LipschitzWith 1 (fun f : D T ℝ => ⨅ t, f t) := by
  apply LipschitzWith.mk_one
  intro f g
  rw [dist_eq_j1Dist]
  change |(⨅ t, f t) - (⨅ t, g t)| ≤ j1Dist f g
  rw [j1Dist]
  refine le_csInf ⟨_, ⟨OrderIso.refl _, rfl⟩⟩ ?_
  rintro x ⟨σ, rfl⟩
  have h := abs_iInf_sub_le_iSup_dist hT f g σ
  exact h.trans (le_max_right _ _)

private theorem bddAbove_range_real {T : ℝ} (hT : 0 ≤ T) (f : D T ℝ) :
    BddAbove (Set.range f) := by
  let t₀ : Set.Icc (0 : ℝ) T := ⟨0, le_rfl, hT⟩
  have hbound : ∃ C, ∀ x y : Set.Icc (0 : ℝ) T, dist (f x) (f y) ≤ C := by
    rw [← Metric.isBounded_range_iff]
    exact isBounded_range f
  obtain ⟨C, hC⟩ := hbound
  refine ⟨f t₀ + C, ?_⟩
  rintro x ⟨t, rfl⟩
  have hdist : |f t - f t₀| ≤ C := by simpa [Real.dist_eq] using hC t t₀
  linarith [(abs_le.mp hdist).2]

private theorem abs_iSup_sub_le_iSup_dist {T : ℝ} (hT : 0 ≤ T)
    (f g : D T ℝ) (σ : TimeChange T) :
    |(⨆ t, f t) - (⨆ t, g t)| ≤ ⨆ t, dist (f t) (g (σ t)) := by
  let t₀ : Set.Icc (0 : ℝ) T := ⟨0, le_rfl, hT⟩
  have hfbdd := bddAbove_range_real hT f
  have hgbdd := bddAbove_range_real hT g
  have hgσbdd : BddAbove (Set.range fun t : Set.Icc (0 : ℝ) T => g (σ t)) := by
    obtain ⟨b, hb⟩ := hgbdd
    refine ⟨b, ?_⟩
    rintro x ⟨t, rfl⟩
    exact hb ⟨σ t, rfl⟩
  have hcomp : (⨆ t : Set.Icc (0 : ℝ) T, g (σ t)) = ⨆ t, g t := by
    exact Equiv.iSup_comp σ.toEquiv
  have hdistBdd := bddAbove_range_dist f g σ
  let d := ⨆ t : Set.Icc (0 : ℝ) T, dist (f t) (g (σ t))
  have hd (t : Set.Icc (0 : ℝ) T) : dist (f t) (g (σ t)) ≤ d :=
    le_ciSup hdistBdd t
  have hupper₁ : (⨆ t : Set.Icc (0 : ℝ) T, g (σ t)) ≤ (⨆ t, f t) + d := by
    refine csSup_le ⟨_, ⟨t₀, rfl⟩⟩ ?_
    rintro x ⟨t, rfl⟩
    have hft : f t ≤ ⨆ s : Set.Icc (0 : ℝ) T, f s := le_ciSup hfbdd t
    have habs : |f t - g (σ t)| ≤ d := by simpa [Real.dist_eq] using hd t
    linarith [(abs_le.mp habs).1]
  have hupper₂ : (⨆ t : Set.Icc (0 : ℝ) T, f t) ≤ (⨆ t, g (σ t)) + d := by
    refine csSup_le ⟨_, ⟨t₀, rfl⟩⟩ ?_
    rintro x ⟨t, rfl⟩
    have hgt : g (σ t) ≤ ⨆ s : Set.Icc (0 : ℝ) T, g (σ s) := le_ciSup hgσbdd t
    have habs : |f t - g (σ t)| ≤ d := by simpa [Real.dist_eq] using hd t
    linarith [(abs_le.mp habs).2]
  rw [hcomp] at hupper₁ hupper₂
  have h1 : (⨆ t : Set.Icc (0 : ℝ) T, g t) - (⨆ t, f t) ≤ d := by linarith
  have h2 : (⨆ t : Set.Icc (0 : ℝ) T, f t) - (⨆ t, g t) ≤ d := by linarith
  rw [abs_le]
  exact ⟨by linarith, h2⟩

/-- The supremum of a real path is 1-Lipschitz for J1 (C6.3). -/
theorem lipschitzWith_one_iSup (hT : 0 ≤ T) :
    LipschitzWith 1 (fun f : D T ℝ => ⨆ t, f t) := by
  apply LipschitzWith.mk_one
  intro f g
  rw [dist_eq_j1Dist]
  change |(⨆ t, f t) - (⨆ t, g t)| ≤ j1Dist f g
  rw [j1Dist]
  refine le_csInf ⟨_, ⟨OrderIso.refl _, rfl⟩⟩ ?_
  rintro x ⟨σ, rfl⟩
  have h := abs_iSup_sub_le_iSup_dist hT f g σ
  exact h.trans (le_max_right _ _)

end BGW.Skorokhod
