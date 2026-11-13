/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.Skorokhod.Basic
public import BGW.Skorokhod.CompleteMetricTimeChange

/-!
# Billingsley's distance with logarithmic time-change cost

The extended cost is finite at the identity, so its infimum has a genuine real value.
-/

@[expose] public section

open Set Filter
open scoped Topology ENNReal

namespace BGW.Skorokhod

variable {T : ℝ} {E : Type*}

/-- Billingsley's distance `d°(f,g) = inf_σ max (‖σ‖°, sup_t dist (f t) (g (σ t)))` (C3). -/
noncomputable def j1CompleteDist [PseudoMetricSpace E] (f g : D T E) : ℝ :=
  (⨅ σ : TimeChange T, max (TimeChange.logSlope σ) (⨆ t, edist (f t) (g (σ t)))).toReal

/-- Extended cost of matching two paths with a given time change. -/
noncomputable def completeCost [PseudoMetricSpace E] (f g : D T E)
    (σ : TimeChange T) : ℝ≥0∞ :=
  max (TimeChange.logSlope σ) (⨆ t, edist (f t) (g (σ t)))

/-- The path part of a time-change cost is finite. -/
theorem iSup_edist_ne_top [PseudoMetricSpace E] (f g : D T E) (σ : TimeChange T) :
    (⨆ t, edist (f t) (g (σ t))) ≠ ∞ := by
  obtain ⟨C, hC⟩ := bddAbove_range_dist f g σ
  apply ne_top_of_le_ne_top ENNReal.ofReal_ne_top
  refine iSup_le fun t => ?_
  rw [edist_dist]
  exact ENNReal.ofReal_le_ofReal (hC ⟨t, rfl⟩)

/-- Matching a path with itself using the identity costs zero. -/
@[simp] theorem completeCost_refl [PseudoMetricSpace E] (f : D T E) :
    completeCost f f (OrderIso.refl _) = 0 := by
  simp [completeCost]

/-- The infimum of matching costs is finite, because the identity is admissible. -/
theorem iInf_completeCost_ne_top [PseudoMetricSpace E] (f g : D T E) :
    (⨅ σ, completeCost f g σ) ≠ ∞ := by
  apply ne_top_of_le_ne_top _ (iInf_le _ (OrderIso.refl _))
  simp only [completeCost, TimeChange.logSlope_refl, max_eq_right zero_le]
  exact iSup_edist_ne_top f g (OrderIso.refl _)

/-- Billingsley's distance is nonnegative. -/
theorem j1CompleteDist_nonneg [PseudoMetricSpace E] (f g : D T E) :
    0 ≤ j1CompleteDist f g := ENNReal.toReal_nonneg

/-- Any radius strictly above the distance admits a matching with smaller cost. -/
theorem exists_completeCost_lt [PseudoMetricSpace E] (f g : D T E) {r : ℝ}
    (hr : j1CompleteDist f g < r) :
    ∃ σ : TimeChange T, completeCost f g σ < ENNReal.ofReal r := by
  apply iInf_lt_iff.mp
  exact (ENNReal.lt_ofReal_iff_toReal_lt (iInf_completeCost_ne_top f g)).mpr hr

/-- Inverting a time change exchanges the two paths without changing the cost. -/
theorem completeCost_symm [PseudoMetricSpace E] (f g : D T E) (σ : TimeChange T) :
    completeCost g f σ.symm = completeCost f g σ := by
  unfold completeCost
  rw [TimeChange.logSlope_symm]
  congr 1
  calc
    (⨆ t, edist (g t) (f (σ.symm t))) =
        ⨆ t, edist (g (σ t)) (f (σ.symm (σ t))) :=
      (Equiv.iSup_comp σ.toEquiv).symm
    _ = ⨆ t, edist (f t) (g (σ t)) := by simp [edist_comm]

/-- Composing time changes gives the triangle bound for matching costs. -/
theorem completeCost_trans_le [PseudoMetricSpace E] (f g h : D T E)
    (σ τ : TimeChange T) :
    completeCost f h (σ.trans τ) ≤ completeCost f g σ + completeCost g h τ := by
  apply max_le
  · exact (TimeChange.logSlope_trans_le σ τ).trans
      (add_le_add (le_max_left _ _) (le_max_left _ _))
  · refine iSup_le fun t => (edist_triangle (f t) (g (σ t)) (h (τ (σ t)))).trans ?_
    exact add_le_add ((le_iSup (fun s => edist (f s) (g (σ s))) t).trans
      (le_max_right _ _)) ((le_iSup (fun s => edist (g s) (h (τ s))) (σ t)).trans
        (le_max_right _ _))

/-- Billingsley's distance vanishes on the diagonal. -/
@[simp] theorem j1CompleteDist_self [PseudoMetricSpace E] (f : D T E) :
    j1CompleteDist f f = 0 := by
  have hz : (⨅ σ, completeCost f f σ) = 0 := le_antisymm
    ((iInf_le _ (OrderIso.refl _)).trans (le_of_eq (completeCost_refl f))) zero_le
  change (⨅ σ, completeCost f f σ).toReal = 0
  simp [hz]

/-- Billingsley's distance is symmetric. -/
theorem j1CompleteDist_comm [PseudoMetricSpace E] (f g : D T E) :
    j1CompleteDist f g = j1CompleteDist g f := by
  have hle : ∀ a b : D T E, (⨅ σ, completeCost a b σ) ≤ ⨅ σ, completeCost b a σ := by
    intro a b
    refine le_iInf fun σ => ?_
    exact (iInf_le _ σ.symm).trans (le_of_eq (completeCost_symm b a σ))
  exact congrArg ENNReal.toReal (le_antisymm (hle f g) (hle g f))

/-- Billingsley's distance satisfies the triangle inequality. -/
theorem j1CompleteDist_triangle [PseudoMetricSpace E] (f g h : D T E) :
    j1CompleteDist f h ≤ j1CompleteDist f g + j1CompleteDist g h := by
  have htri : (⨅ σ, completeCost f h σ) ≤
      (⨅ σ, completeCost f g σ) + ⨅ τ, completeCost g h τ := by
    apply ENNReal.le_iInf_add_iInf
    intro σ τ
    exact (iInf_le _ (σ.trans τ)).trans (completeCost_trans_le f g h σ τ)
  change (⨅ σ, completeCost f h σ).toReal ≤
    (⨅ σ, completeCost f g σ).toReal + (⨅ σ, completeCost g h σ).toReal
  rw [← ENNReal.toReal_add (iInf_completeCost_ne_top f g) (iInf_completeCost_ne_top g h)]
  exact ENNReal.toReal_mono (ENNReal.add_ne_top.mpr
    ⟨iInf_completeCost_ne_top f g, iInf_completeCost_ne_top g h⟩) htri

/-- A matching of cost at most a nonnegative radius bounds the distance. -/
theorem j1CompleteDist_le_of_completeCost_le [PseudoMetricSpace E] (f g : D T E)
    (σ : TimeChange T) {r : ℝ} (hr : 0 ≤ r)
    (hc : completeCost f g σ ≤ ENNReal.ofReal r) : j1CompleteDist f g ≤ r := by
  exact ENNReal.toReal_le_of_le_ofReal hr ((iInf_le _ σ).trans hc)

end BGW.Skorokhod
