/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.Skorokhod.ContinuousEmbedding
public import BGW.Skorokhod.TimeChange

/-!
# Pairing a càdlàg path with a continuous path

The pair of a càdlàg real path and a continuous real path is a càdlàg path with values in
`ℝ × ℝ`. The pairing map is jointly continuous for the Skorokhod `J1` topology and the uniform
topology on continuous paths. The same time changes control both coordinates; in the continuous
coordinate one also uses uniform convergence and uniform continuity of the limiting path.

Reference: P. Billingsley, *Convergence of Probability Measures*, 2nd ed., Wiley, 1999, Section 12.
-/

@[expose] public section

open Filter Topology

namespace BGW.Skorokhod

variable {T : ℝ}

/-- The pair path `(f, g)` of a càdlàg path and a continuous path. -/
def prodCont (f : D T ℝ) (g : C(Set.Icc (0 : ℝ) T, ℝ)) : D T (ℝ × ℝ) :=
  ⟨fun t => (f t, g t), (isCadlag f).continuous_comp₂ g.continuous.isCadlag continuous_id⟩

variable {T : ℝ} {E F : Type*} [MetricSpace E] [MetricSpace F]

/-- The pair path `(f, g)` of a càdlàg path with values in `E` and a continuous path with
values in `F`. -/
def prodWithCont (f : D T E) (g : C(Set.Icc (0 : ℝ) T, F)) : D T (E × F) :=
  ⟨fun t => (f t, g t), (isCadlag f).continuous_comp₂ g.continuous.isCadlag continuous_id⟩

@[simp]
theorem prodWithCont_apply (f : D T E) (g : C(Set.Icc (0 : ℝ) T, F)) (t : Set.Icc (0 : ℝ) T) :
    prodWithCont f g t = (f t, g t) := rfl

private theorem tendsto_prodWithCont_aux {ι : Type*} {l : Filter ι} {u : ι → D T E} {f : D T E}
    {v : ι → C(Set.Icc (0 : ℝ) T, F)} {g : C(Set.Icc (0 : ℝ) T, F)}
    (hu : Tendsto u l (𝓝 f)) (hv : Tendsto v l (𝓝 g)) :
    Tendsto (fun i => prodWithCont (u i) (v i)) l (𝓝 (prodWithCont f g)) := by
  obtain ⟨σ, hdisp, hpath⟩ := tendsto_iff_exists_timeChange.mp hu
  have hvg : Tendsto (fun i => dist (v i) g) l (𝓝 0) :=
    tendsto_iff_dist_tendsto_zero.mp hv
  have hsecond : Tendsto (fun i => ⨆ t, dist (v i (σ i t)) (g t)) l (𝓝 0) := by
    by_cases hT : 0 ≤ T
    · have hUC : UniformContinuous g :=
        CompactSpace.uniformContinuous_of_continuous g.continuous
      refine Metric.tendsto_nhds.mpr fun ε hε => ?_
      obtain ⟨δ, hδ, hδg⟩ := Metric.uniformContinuous_iff.mp hUC (ε / 4) (by linarith)
      let δ' := min δ (ε / 2)
      have hδ' : 0 < δ' := lt_min hδ (half_pos hε)
      have hdisp' : ∀ᶠ i in l,
          (⨆ t : Set.Icc (0 : ℝ) T, |((σ i t : ℝ)) - t|) < δ' := by
        have h := Metric.tendsto_nhds.mp hdisp δ' hδ'
        filter_upwards [h] with i hi
        simpa [Real.dist_eq, abs_of_nonneg (displacement_nonneg (σ i) hT)] using hi
      have hvg' : ∀ᶠ i in l, dist (v i) g < ε / 4 := by
        filter_upwards [Metric.tendsto_nhds.mp hvg (ε / 4) (by linarith)] with i hi
        simpa [Real.dist_eq] using hi
      filter_upwards [hdisp', hvg'] with i hiδ hiv
      have hpoint (t : Set.Icc (0 : ℝ) T) : dist (v i (σ i t)) (g t) < ε / 2 := by
        have htime : dist (σ i t) t < δ := by
          have hle : |((σ i t : ℝ)) - t| ≤
              ⨆ s : Set.Icc (0 : ℝ) T, |((σ i s : ℝ)) - s| :=
            le_ciSup (bddAbove_displacement hT (σ i)) t
          rw [Subtype.dist_eq, Real.dist_eq]
          exact lt_of_le_of_lt hle (lt_of_lt_of_le hiδ (min_le_left _ _))
        calc
          dist (v i (σ i t)) (g t) ≤ dist (v i (σ i t)) (g (σ i t)) +
              dist (g (σ i t)) (g t) := dist_triangle _ _ _
          _ < ε / 4 + ε / 4 := add_lt_add
            ((ContinuousMap.dist_apply_le_dist _).trans_lt hiv) (hδg htime)
          _ = ε / 2 := by ring
      have hb : BddAbove (Set.range fun t : Set.Icc (0 : ℝ) T =>
          dist (v i (σ i t)) (g t)) := by
        simpa only [ofContinuous, coe_mk] using
          bddAbove_comp_dist hT (ofContinuous (v i)) (ofContinuous g) (σ i)
      have hnonneg : 0 ≤ ⨆ t : Set.Icc (0 : ℝ) T, dist (v i (σ i t)) (g t) :=
        le_ciSup_of_le hb ⟨0, by simp [hT]⟩ dist_nonneg
      rw [Real.dist_eq, sub_zero, abs_of_nonneg hnonneg]
      have hsup : (⨆ t : Set.Icc (0 : ℝ) T, dist (v i (σ i t)) (g t)) ≤ ε / 2 := by
        have hne : (Set.range fun t : Set.Icc (0 : ℝ) T =>
            dist (v i (σ i t)) (g t)).Nonempty := ⟨_, ⟨⟨0, by simp [hT]⟩, rfl⟩⟩
        apply csSup_le hne
        rintro _ ⟨t, rfl⟩
        exact (hpoint t).le
      exact lt_of_le_of_lt hsup (half_lt_self hε)
    · have hempty : IsEmpty (Set.Icc (0 : ℝ) T) :=
        ⟨fun t => (not_le_of_gt (lt_of_not_ge hT)) (le_trans t.property.1 t.property.2)⟩
      have hzero (i : ι) : (⨆ t : Set.Icc (0 : ℝ) T, dist (v i (σ i t)) (g t)) = 0 := by
        rw [@iSup_of_empty' ℝ _ _ hempty]
        simp
      simp_rw [hzero]
      exact tendsto_const_nhds
  apply tendsto_iff_exists_timeChange.mpr
  refine ⟨σ, hdisp, ?_⟩
  by_cases hT : 0 ≤ T
  · have hmax : Tendsto (fun i => max
        (⨆ t : Set.Icc (0 : ℝ) T, dist (u i (σ i t)) (f t))
        (⨆ t : Set.Icc (0 : ℝ) T, dist (v i (σ i t)) (g t))) l (𝓝 0) := by
      simpa using hpath.max hsecond
    apply squeeze_zero (fun i => ?_) (fun i => ?_) hmax
    · have hb := bddAbove_comp_dist hT (prodWithCont (u i) (v i)) (prodWithCont f g) (σ i)
      exact le_ciSup_of_le hb ⟨0, by simp [hT]⟩ dist_nonneg
    · have hne : (Set.range fun t : Set.Icc (0 : ℝ) T =>
          dist (prodWithCont (u i) (v i) (σ i t)) (prodWithCont f g t)).Nonempty :=
        ⟨_, ⟨⟨0, by simp [hT]⟩, rfl⟩⟩
      apply csSup_le hne
      rintro _ ⟨t, rfl⟩
      change max (dist (u i (σ i t)) (f t)) (dist (v i (σ i t)) (g t)) ≤ _
      apply max_le
      · have hb := bddAbove_comp_dist hT (u i) f (σ i)
        exact (le_ciSup hb t).trans (le_max_left _ _)
      · have hb : BddAbove (Set.range fun t : Set.Icc (0 : ℝ) T =>
            dist (v i (σ i t)) (g t)) := by
          simpa only [ofContinuous, coe_mk] using
            bddAbove_comp_dist hT (ofContinuous (v i)) (ofContinuous g) (σ i)
        exact (le_ciSup hb t).trans (le_max_right _ _)
  · have hempty : IsEmpty (Set.Icc (0 : ℝ) T) :=
      ⟨fun t => (not_le_of_gt (lt_of_not_ge hT)) (le_trans t.property.1 t.property.2)⟩
    have hzero (i : ι) :
        (⨆ t : Set.Icc (0 : ℝ) T,
          dist (prodWithCont (u i) (v i) (σ i t)) (prodWithCont f g t)) = 0 := by
      rw [@iSup_of_empty' ℝ _ _ hempty]
      simp
    simp_rw [hzero]
    exact tendsto_const_nhds

/-- `prodWithCont` is jointly continuous on `D_T(E) × C([0,T], F)` (Skorokhod `J1` topology
and uniform topology). -/
theorem continuous_prodWithCont :
    Continuous (fun p : D T E × C(Set.Icc (0 : ℝ) T, F) => prodWithCont p.1 p.2) := by
  rw [continuous_iff_continuousAt]
  intro p
  exact tendsto_prodWithCont_aux continuousAt_fst continuousAt_snd

/-- `prodCont` is jointly continuous on `D_T(ℝ) × C([0,T],ℝ)`. -/
theorem continuous_prodCont :
    Continuous (fun p : D T ℝ × C(Set.Icc (0 : ℝ) T, ℝ) => prodCont p.1 p.2) := by
  simpa only [prodCont, prodWithCont] using
    (continuous_prodWithCont (T := T) (E := ℝ) (F := ℝ))

universe u_1

/-- Sequential form of `continuous_prodCont`. -/
theorem tendsto_prodCont {ι : Type u_1} {l : Filter ι} {u : ι → D T ℝ} {f : D T ℝ}
    {v : ι → C(Set.Icc (0 : ℝ) T, ℝ)} {g : C(Set.Icc (0 : ℝ) T, ℝ)}
    (hu : Tendsto u l (𝓝 f)) (hv : Tendsto v l (𝓝 g)) :
    Tendsto (fun i => prodCont (u i) (v i)) l (𝓝 (prodCont f g)) := by
  have h := ((continuous_prodWithCont (T := T) (E := ℝ) (F := ℝ)).tendsto (f, g)).comp
    (hu.prodMk_nhds hv)
  simpa only [Function.comp_def, prodCont, prodWithCont] using h

end BGW.Skorokhod
