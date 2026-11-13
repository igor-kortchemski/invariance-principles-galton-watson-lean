/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.DiscreteHeightApproxWindow
public import BGW.StableTrees.HeightProcess

/-!
# Finite-path occupation observables

Constant extension past the terminal endpoint lets the finite-horizon occupation
functional use the sealed local-path height approximation.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees.DiscreteHeightApprox

/-- Extend a compact path constantly beyond its terminal endpoint. -/
def extendFinitePath (T : ℝ≥0) (f : D (T : ℝ) ℝ) : DLoc := by
  let κ : ℝ≥0 → Set.Icc (0 : ℝ) (T : ℝ) := fun u =>
    ⟨min (u : ℝ) T, le_min u.2 T.2, min_le_right _ _⟩
  have hκ : Continuous κ := Continuous.subtype_mk
    (continuous_subtype_val.min continuous_const) fun u => ⟨le_min u.2 T.2, min_le_right _ _⟩
  refine ⟨fun u => f (κ u), ?_⟩
  constructor
  · intro t
    by_cases ht : (t : ℝ) < T
    · have hmap : MapsTo κ (Set.Ioi t) (Set.Ioi (κ t)) := by
        intro u hu
        change (t : ℝ) < (u : ℝ) at hu
        change (κ t : ℝ) < (κ u : ℝ)
        simp only [κ, min_eq_left ht.le]
        exact (lt_min_iff.mpr ⟨hu, ht⟩)
      exact f.2.isRightContinuous (κ t) |>.comp
        hκ.continuousAt.continuousWithinAt hmap
    · have htT : T ≤ (t : ℝ) := le_of_not_gt ht
      have hconst : ∀ u ∈ Set.Ioi t, κ u = κ t := by
        intro u hu
        change (t : ℝ) < (u : ℝ) at hu
        apply Subtype.ext
        simp [κ, min_eq_right htT, min_eq_right (htT.trans hu.le)]
      exact tendsto_nhdsWithin_congr (fun u hu => congrArg f (hconst u hu).symm)
        tendsto_const_nhds
  · intro t
    by_cases ht : (t : ℝ) ≤ T
    · have hmap : MapsTo κ (Set.Iio t) (Set.Iio (κ t)) := by
        intro u hu
        change (u : ℝ) < (t : ℝ) at hu
        have huT : (u : ℝ) ≤ T := hu.le.trans ht
        change (κ u : ℝ) < (κ t : ℝ)
        simp only [κ, min_eq_left huT, min_eq_left ht]
        exact hu
      obtain ⟨l, hl⟩ := f.2.tendsto_nhdsLT (κ t)
      have hκleft : Tendsto κ (𝓝[Set.Iio t] t) (𝓝[Set.Iio (κ t)] (κ t)) := by
        apply tendsto_nhdsWithin_iff.mpr
        refine ⟨tendsto_nhdsWithin_of_tendsto_nhds hκ.continuousAt, ?_⟩
        filter_upwards [self_mem_nhdsWithin] with u hu
        exact hmap hu
      exact ⟨l, hl.comp hκleft⟩
    · have htT : T < t := by exact_mod_cast (lt_of_not_ge ht)
      have hev : ∀ᶠ u in 𝓝[Set.Iio t] t, T < u :=
        (eventually_gt_nhds htT).filter_mono nhdsWithin_le_nhds
      have hconst : ∀ u : ℝ≥0, T < u → κ u = κ t := by
        intro u hu
        apply Subtype.ext
        have hu' : (T : ℝ) ≤ (u : ℝ) := by exact_mod_cast hu.le
        simp [κ, min_eq_right hu', min_eq_right (show (T : ℝ) ≤ (t : ℝ) from htT.le)]
      have hfg : (fun u : ℝ≥0 => f (κ u)) =ᶠ[𝓝[Set.Iio t] t]
          fun _ => f (κ t) := by
        filter_upwards [hev] with u hu
        exact congrArg f (hconst u hu)
      exact ⟨f (κ t), (tendsto_congr' hfg).2 tendsto_const_nhds⟩


/-- Constant extension agrees with the finite path before its terminal endpoint. -/
theorem extendFinitePath_apply (T : ℝ≥0) (f : D (T : ℝ) ℝ) (u : ℝ≥0) (hu : u ≤ T) :
    (extendFinitePath T f).1 u = f ⟨u, u.2, hu⟩ := by
  change f ⟨min (u : ℝ) T, le_min u.2 T.2, min_le_right _ _⟩ = _
  congr 1
  exact Subtype.ext (min_eq_left hu)

/-- Constant extension is measurable for the evaluation sigma-algebra. -/
theorem measurable_extendFinitePath (T : ℝ≥0) : Measurable (extendFinitePath T) := by
  rw [measurable_iff_comap_le]
  change (⨆ t : ℝ≥0, MeasurableSpace.comap (DLoc.eval t) inferInstance).comap
    (extendFinitePath T) ≤ _
  rw [MeasurableSpace.comap_iSup, iSup_le_iff]
  intro t
  rw [MeasurableSpace.comap_comp]
  exact (measurable_eval ⟨min (t : ℝ) T, le_min t.2 T.2, min_le_right _ _⟩).comap_le

/-- The future infimum of a constant extension is the finite window infimum. -/
theorem futureInf_extendFinitePath (T : ℝ≥0) (f : D (T : ℝ) ℝ) {s t : ℝ≥0}
    (hst : s ≤ t) (ht : t ≤ T) :
    futureInf (extendFinitePath T f) t s = windowInf f s.2 hst ht := by
  let e : Icc (s : ℝ) (t : ℝ) ≃ Icc s t :=
    { toFun := fun u => ⟨⟨u, s.2.trans u.2.1⟩, u.2.1, u.2.2⟩
      invFun := fun u => ⟨u.1, u.2.1, u.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [futureInf, min_eq_left hst]
  have he := Equiv.iInf_comp (g := fun u : Icc s t => (extendFinitePath T f).1 u) e
  rw [← he]
  apply iInf_congr
  intro u
  exact extendFinitePath_apply T f _ (u.2.2.trans ht)

/-- The sealed occupation approximation applied to the constant extension of a finite path. -/
noncomputable def finiteHeightApprox (T t : ℝ≥0) (ε : ℝ) (f : D (T : ℝ) ℝ) : ℝ :=
  heightApprox ε (extendFinitePath T f) t

/-- Finite-path occupation observables are measurable. -/
theorem measurable_finiteHeightApprox (T t : ℝ≥0) (ε : ℝ) :
    Measurable (finiteHeightApprox T t ε) := by
  exact Measurable.comp
    (g := fun p : ℝ × ℝ≥0 × DLoc => heightApprox p.1 p.2.2 p.2.1)
    (f := fun f : D (T : ℝ) ℝ => (ε, t, extendFinitePath T f))
    measurable_heightApprox_uncurry
    (measurable_const.prodMk (measurable_const.prodMk (measurable_extendFinitePath T)))

/-- The finite-path gap is continuous at a path continuous at the two window endpoints. -/
theorem continuousAt_extended_gap (T : ℝ≥0) {s t : ℝ≥0} (hst : s ≤ t) (ht : t ≤ T)
    {f : D (T : ℝ) ℝ} (hsf : ContinuousAt f ⟨s, s.2, hst.trans ht⟩)
    (htf : t = T ∨ ContinuousAt f ⟨t, t.2, ht⟩) :
    ContinuousAt (fun g : D (T : ℝ) ℝ => (extendFinitePath T g).1 s -
      futureInf (extendFinitePath T g) t s) f := by
  have ht' : (t : ℝ) = T ∨ ContinuousAt f ⟨t, s.2.trans hst, ht⟩ := by
    rcases htf with he | he
    · exact Or.inl (congrArg (fun u : ℝ≥0 => (u : ℝ)) he)
    · exact Or.inr he
  have hi := continuousAt_windowInf s.2 hst ht hsf ht'
  have he : ContinuousAt (fun g : D (T : ℝ) ℝ =>
      g ⟨s, s.2, hst.trans ht⟩ - windowInf g s.2 hst ht) f :=
    (continuousAt_eval hsf).sub hi
  simpa only [Pi.sub_apply, extendFinitePath_apply T _ s (hst.trans ht),
    futureInf_extendFinitePath T _ hst ht] using he

/-- Prefix agreement determines the future infimum at all earlier times. -/
theorem futureInf_eq_of_prefix {f g : DLoc} {t s : ℝ≥0}
    (he : ∀ u ≤ t, f.1 u = g.1 u) : futureInf f t s = futureInf g t s := by
  apply iInf_congr
  intro u
  exact he u u.2.2

/-- Prefix agreement determines the fixed-time occupation approximation. -/
theorem heightApprox_eq_of_prefix {f g : DLoc} {t : ℝ≥0}
    (he : ∀ u ≤ t, f.1 u = g.1 u) (ε : ℝ) : heightApprox ε f t = heightApprox ε g t := by
  unfold heightApprox
  congr 3
  ext s
  simp only [mem_ofPred_eq]
  by_cases hs : 0 ≤ s ∧ s ≤ (t : ℝ)
  · have hst : s.toNNReal ≤ t := Real.toNNReal_le_iff_le_coe.mpr hs.2
    rw [he _ hst, futureInf_eq_of_prefix he]
  · tauto

/-- Extending a restriction preserves all occupations before that restriction endpoint. -/
theorem finiteHeightApprox_restrict (T t : ℝ≥0) (ht : t ≤ T) (ε : ℝ) (f : DLoc) :
    finiteHeightApprox T t ε (DLoc.restrict T f) = heightApprox ε f t := by
  apply heightApprox_eq_of_prefix
  intro u hu
  rw [extendFinitePath_apply T _ u (hu.trans ht)]
  rfl

end BGW.StableTrees.DiscreteHeightApprox
