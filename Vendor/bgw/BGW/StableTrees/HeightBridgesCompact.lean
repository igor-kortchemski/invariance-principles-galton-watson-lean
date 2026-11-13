/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.HeightBridgesUniversalBasic
public import BGW.StableTrees.HeightBridgesExtraction
import Mathlib.MeasureTheory.Function.FactorsThrough

/-!
# Compact prefix representatives for height approximations

Constant extension supplies literal representatives on the compact prefix space.
The definitions agree with the original observables on every local path.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod
open BGW.Probability

namespace BGW.StableTrees

/-- Constant extension of a compact prefix to a local càdlàg path. -/
def horizonExtension (T : ℝ≥0) (f : D (T : ℝ) ℝ) : DLoc := by
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

/-- Constant extension of a compact prefix is measurable. -/
theorem measurable_horizonExtension (T : ℝ≥0) :
    Measurable (horizonExtension T) := by
  rw [measurable_iff_comap_le]
  change (⨆ t : ℝ≥0, MeasurableSpace.comap (DLoc.eval t) inferInstance).comap
    (horizonExtension T) ≤ _
  rw [MeasurableSpace.comap_iSup, iSup_le_iff]
  intro u
  rw [MeasurableSpace.comap_comp]
  exact (BGW.Skorokhod.measurable_eval
    ⟨min (u : ℝ) T, le_min u.2 T.2, min_le_right _ _⟩).comap_le

/-- Restricting the constant extension recovers the compact prefix. -/
theorem restrict_horizonExtension (T : ℝ≥0) (f : D (T : ℝ) ℝ) :
    DLoc.restrict T (horizonExtension T f) = f := by
  apply BGW.Skorokhod.ext
  intro u
  change f ⟨min (u : ℝ) T, le_min u.2.1 T.2, min_le_right _ _⟩ = f u
  congr 1
  exact Subtype.ext (min_eq_left u.2.2)

/-- Compact-prefix representative of the height approximation. -/
noncomputable def horizonHeightApprox (ε : ℝ) (T : ℝ≥0) (f : D (T : ℝ) ℝ) : ℝ :=
  heightApprox ε (horizonExtension T f) T

/-- Compact-prefix representative of H02's chosen height. -/
noncomputable def horizonHeight (θ : ℝ) (T : ℝ≥0) (f : D (T : ℝ) ℝ) : ℝ :=
  height θ (horizonExtension T f) T

/-- The compact approximation is measurable. -/
theorem measurable_horizonHeightApprox (ε : ℝ) (T : ℝ≥0) :
    Measurable (horizonHeightApprox ε T) :=
  measurable_heightApprox_uncurry.comp
    (measurable_const.prodMk (measurable_const.prodMk (measurable_horizonExtension T)))

/-- The compact height representative is measurable. -/
theorem measurable_horizonHeight (θ : ℝ) (T : ℝ≥0) : Measurable (horizonHeight θ T) :=
  by
    unfold horizonHeight
    exact Measurable.comp (g := fun p : ℝ≥0 × DLoc => height θ p.2 p.1)
      (f := fun f : D (T : ℝ) ℝ => (T, horizonExtension T f))
      (measurable_height_uncurry θ)
      (measurable_const.prodMk (measurable_horizonExtension T))

/-- Restricting a local path preserves its compact approximation. -/
theorem horizonHeightApprox_restrict (ε : ℝ) (T : ℝ≥0) (f : DLoc) :
    horizonHeightApprox ε T (DLoc.restrict T f) = heightApprox ε f T := by
  exact heightApprox_eq_of_restrict_eq ε T _ f (restrict_horizonExtension T _) T le_rfl

/-- Restricting a local path preserves its compact H02 height. -/
theorem horizonHeight_restrict (θ : ℝ) (T : ℝ≥0) (f : DLoc) :
    horizonHeight θ T (DLoc.restrict T f) = height θ f T := by
  exact (measurable_height_prefix θ T).factorsThrough (restrict_horizonExtension T _)

/-- H02 convergence on the compact stable prefix law. -/
theorem horizonHeightApprox_tendstoInMeasure {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (T : ℝ≥0) :
    TendstoInMeasure ((stableLocalLaw θ : Measure DLoc).map (DLoc.restrict T))
      (fun ε => horizonHeightApprox ε T) (𝓝[>] (0 : ℝ)) (horizonHeight θ T) := by
  apply (tendstoInMeasure_map_iff (DLoc.measurable_restrict T)
    (fun ε => measurable_horizonHeightApprox ε T) (measurable_horizonHeight θ T)).mpr
  simpa only [horizonHeightApprox_restrict, horizonHeight_restrict] using
    heightApprox_tendstoInMeasure hθ T

end BGW.StableTrees

