/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.Skorokhod.Basic
public import Mathlib.Topology.ContinuousMap.Compact

/-!
# Continuous paths in Skorokhod space

Continuous paths are càdlàg, and convergence to a continuous limit in the J1 topology implies
uniform convergence.
-/

@[expose] public section

open Set Filter Topology

namespace BGW.Skorokhod

variable {T : ℝ} {E : Type*}

/-- The displacement of a time change on a compact interval is bounded. -/
theorem bddAbove_displacement {T : ℝ} (hT : 0 ≤ T) (σ : TimeChange T) :
    BddAbove (Set.range fun t : Set.Icc (0 : ℝ) T => |((σ t : ℝ)) - t|) := by
  refine ⟨T, ?_⟩
  rintro x ⟨t, rfl⟩
  exact TimeChange.abs_sub_le σ hT t

/-- The supremum displacement of a time change is nonnegative. -/
theorem displacement_nonneg {T : ℝ} (σ : TimeChange T) (hT : 0 ≤ T) :
    0 ≤ ⨆ t : Set.Icc (0 : ℝ) T, |((σ t : ℝ)) - t| := by
  exact le_ciSup_of_le (bddAbove_displacement hT σ) ⟨0, by simp [hT]⟩ (abs_nonneg _)

/-- Distances between two càdlàg paths, with one composed with a time change, are bounded above. -/
theorem bddAbove_comp_dist [PseudoMetricSpace E] {T : ℝ} (hT : 0 ≤ T)
    (f g : D T E) (σ : TimeChange T) :
    BddAbove (Set.range fun t : Set.Icc (0 : ℝ) T => dist (f (σ t)) (g t)) := by
  have hf : ∃ C, ∀ x y : Set.Icc (0 : ℝ) T, dist (f x) (f y) ≤ C := by
    rw [← Metric.isBounded_range_iff]
    exact isBounded_range f
  have hg : ∃ C, ∀ x y : Set.Icc (0 : ℝ) T, dist (g x) (g y) ≤ C := by
    rw [← Metric.isBounded_range_iff]
    exact isBounded_range g
  obtain ⟨Cf, hCf⟩ := hf
  obtain ⟨Cg, hCg⟩ := hg
  let t₀ : Set.Icc (0 : ℝ) T := ⟨0, by simp [hT]⟩
  refine ⟨Cf + dist (f t₀) (g t₀) + Cg, ?_⟩
  rintro x ⟨t, rfl⟩
  calc
    dist (f (σ t)) (g t) ≤ dist (f (σ t)) (f t₀) + dist (f t₀) (g t₀) +
        dist (g t₀) (g t) := dist_triangle4 _ _ _ _
    _ ≤ Cf + dist (f t₀) (g t₀) + Cg := by
      exact add_le_add (add_le_add (hCf _ _) le_rfl) (hCg _ _)

/-- A continuous path, seen as a càdlàg path (C5). -/
def ofContinuous [TopologicalSpace E] (f : C(Set.Icc (0 : ℝ) T, E)) : D T E :=
  ⟨f, f.continuous.isCadlag⟩

/-- On continuous paths the J1 distance is at most the uniform distance (C5.1). -/
theorem lipschitzWith_one_ofContinuous [MetricSpace E] :
    LipschitzWith 1 (ofContinuous (T := T) (E := E)) := by
  apply LipschitzWith.mk_one
  intro f g
  calc
    dist (ofContinuous f) (ofContinuous g) ≤ ⨆ t, dist (f t) (g t) := by
      simpa only [ofContinuous, coe_mk] using dist_le_iSup_dist (ofContinuous f) (ofContinuous g)
    _ = dist f g := ContinuousMap.dist_eq_iSup.symm

/-- The J1 distance is at most the cost of any chosen time change. -/
theorem j1Dist_le_timeChange_cost [PseudoMetricSpace E] (hT : 0 ≤ T) (f g : D T E)
    (σ : TimeChange T) :
    j1Dist f g ≤ max (⨆ t, |((σ t : ℝ)) - t|) (⨆ t, dist (f t) (g (σ t))) := by
  change (⨅ τ : TimeChange T,
      max (⨆ t, |((τ t : ℝ)) - t|) (⨆ t, dist (f t) (g (τ t)))) ≤ _
  have hcostNonneg (τ : TimeChange T) : 0 ≤
      max (⨆ t : Set.Icc (0 : ℝ) T, |((τ t : ℝ)) - t|)
        (⨆ t : Set.Icc (0 : ℝ) T, dist (f t) (g (τ t))) := by
    apply le_max_of_le_left
    exact displacement_nonneg τ hT
  have hbelow : BddBelow (Set.range fun τ : TimeChange T =>
      max (⨆ t, |((τ t : ℝ)) - t|) (⨆ t, dist (f t) (g (τ t)))) := by
    refine ⟨0, ?_⟩
    rintro x ⟨τ, rfl⟩
    exact hcostNonneg τ
  exact ciInf_le hbelow σ

/-- J1 convergence to a continuous path is uniform convergence (C5.2). -/
theorem tendsto_iSup_dist_of_tendsto_ofContinuous [MetricSpace E] {ι : Type*} {l : Filter ι}
    {u : ι → D T E} {f : C(Set.Icc (0 : ℝ) T, E)}
    (h : Tendsto u l (𝓝 (ofContinuous f))) :
    Tendsto (fun i => ⨆ t, dist (u i t) (f t)) l (𝓝 0) := by
  by_cases hT : 0 ≤ T
  · obtain ⟨σ, hdisp, hpath⟩ := (tendsto_iff_exists_timeChange.mp h)
    have hUC : UniformContinuous f :=
      CompactSpace.uniformContinuous_of_continuous f.continuous
    refine Metric.tendsto_nhds.mpr fun ε hε => ?_
    obtain ⟨δ, hδ, hδf⟩ := Metric.uniformContinuous_iff.mp hUC (ε / 2) (half_pos hε)
    let δ' := min δ (ε / 2)
    have hδ' : 0 < δ' := lt_min hδ (half_pos hε)
    have hdisp' : ∀ᶠ i in l, (⨆ t : Set.Icc (0 : ℝ) T, |((σ i t : ℝ)) - t|) < δ' := by
      have h := Metric.tendsto_nhds.mp hdisp δ' hδ'
      have hnonneg (i : ι) : 0 ≤
          ⨆ t : Set.Icc (0 : ℝ) T, |((σ i t : ℝ)) - t| := displacement_nonneg (σ i) hT
      filter_upwards [h] with i hi
      simpa [Real.dist_eq, abs_of_nonneg (hnonneg i)] using hi
    have hpath' : ∀ᶠ i in l, (⨆ t : Set.Icc (0 : ℝ) T,
        dist (u i (σ i t)) (f t)) < ε / 2 := by
      have h := Metric.tendsto_nhds.mp hpath (ε / 2) (half_pos hε)
      have hnonneg (i : ι) : 0 ≤ ⨆ t : Set.Icc (0 : ℝ) T,
          dist (u i (σ i t)) (f t) :=
        le_ciSup_of_le (bddAbove_comp_dist hT (u i) (ofContinuous f) (σ i))
          ⟨0, by simp [hT]⟩ dist_nonneg
      filter_upwards [h] with i hi
      simpa [Real.dist_eq, abs_of_nonneg (hnonneg i), ofContinuous] using hi
    filter_upwards [hdisp', hpath'] with i hiδ hiε
    have hdispInv : (⨆ t : Set.Icc (0 : ℝ) T, |((σ i).symm t : ℝ) - t|) < δ' := by
      simpa only [TimeChange.iSup_abs_sub_symm] using hiδ
    have hbound (t : Set.Icc (0 : ℝ) T) :
        dist (u i t) (f t) ≤
          (⨆ s : Set.Icc (0 : ℝ) T, dist (u i (σ i s)) (f s)) + ε / 2 := by
      let s : Set.Icc (0 : ℝ) T := (σ i).symm t
      have hfirst : dist (u i t) (f s) ≤
          ⨆ r : Set.Icc (0 : ℝ) T, dist (u i (σ i r)) (f r) := by
        have hh : dist (u i (σ i s)) (f s) ≤
            ⨆ r : Set.Icc (0 : ℝ) T, dist (u i (σ i r)) (f r) := by
          simpa [ofContinuous] using
            (le_ciSup (bddAbove_comp_dist hT (u i) (ofContinuous f) (σ i)) s)
        simpa [s] using hh
      have htime : dist s t < δ := by
        have hs : |((σ i).symm t : ℝ) - t| ≤
            ⨆ r : Set.Icc (0 : ℝ) T, |((σ i).symm r : ℝ) - r| :=
          le_ciSup (bddAbove_displacement hT (σ i).symm) t
        have hs' : dist s t = |((σ i).symm t : ℝ) - t| := by
          simp [s, Subtype.dist_eq, Real.dist_eq]
        rw [hs']
        exact lt_of_le_of_lt hs (lt_of_lt_of_le hdispInv (min_le_left _ _))
      have hsecond : dist (f s) (f t) < ε / 2 := hδf htime
      exact (dist_triangle _ _ _).trans (add_le_add hfirst hsecond.le)
    have hsup : (⨆ t : Set.Icc (0 : ℝ) T, dist (u i t) (f t)) ≤
        (⨆ s : Set.Icc (0 : ℝ) T, dist (u i (σ i s)) (f s)) + ε / 2 :=
      csSup_le ⟨_, ⟨⟨0, by simp [hT]⟩, rfl⟩⟩ fun x hx => by
        obtain ⟨t, rfl⟩ := hx
        exact hbound t
    have hnonneg : 0 ≤ ⨆ t : Set.Icc (0 : ℝ) T, dist (u i t) (f t) :=
      le_ciSup_of_le (bddAbove_range_dist (u i) (ofContinuous f) (OrderIso.refl _))
        ⟨0, by simp [hT]⟩ dist_nonneg
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hnonneg]
    exact lt_of_le_of_lt hsup (by linarith)
  · have hempty : IsEmpty (Set.Icc (0 : ℝ) T) :=
      ⟨fun t => (not_le_of_gt (lt_of_not_ge hT)) (le_trans t.property.1 t.property.2)⟩
    have hzero (i : ι) : (⨆ t : Set.Icc (0 : ℝ) T, dist (u i t) (f t)) = 0 := by
      rw [@iSup_of_empty' ℝ _ _ hempty]
      simp
    simp_rw [hzero]
    exact tendsto_const_nhds

end BGW.Skorokhod
