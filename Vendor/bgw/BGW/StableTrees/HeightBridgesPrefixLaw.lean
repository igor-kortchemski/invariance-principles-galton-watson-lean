/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.HeightProcess
public import BGW.StableTrees.StableLocalMarkov
import Mathlib.Probability.Independence.Basic

/-!
# Independent reversed prefix and fresh increments

Reversal preserves the compact prefix law, and deterministic-time independence separates
that prefix from the future increment path.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees

/-- The compact prefix is measurable for the right-continuous past filtration. -/
theorem measurable_restrict_height_filtration (t : ℝ≥0) :
    Measurable[DLoc.filtration t] (DLoc.restrict t) := by
  rw [measurable_iff_comap_le]
  change MeasurableSpace.comap (DLoc.restrict t)
      (inferInstance : MeasurableSpace (D (t : ℝ) ℝ)) ≤ DLoc.filtration t
  rw [BGW.Skorokhod.measurableSpace_eq_iSup_comap_eval (T := (t : ℝ)) (E := ℝ)
    (S := Set.univ) dense_univ t.2 (by simp)]
  simp only [MeasurableSpace.comap_iSup, iSup_le_iff, MeasurableSpace.comap_comp,
    Function.comp_def]
  intro u _hu
  let s : ℝ≥0 := ⟨u, u.2.1⟩
  have hst : s ≤ t := by exact_mod_cast u.2.2
  exact ((DLoc.adapted_eval s).mono (DLoc.filtration.mono hst) le_rfl).comap_le

/-- Reversed prefix and fresh increments have the independent stable product law. -/
theorem map_reversed_prefix_shift_stableLocalLaw {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    {t : ℝ≥0} (ht : 0 < t) :
    (stableLocalLaw θ : Measure DLoc).map
      (fun f => (DLoc.restrict t (reversedAt t f), DLoc.shift t f)) =
      ((stableLocalLaw θ : Measure DLoc).map (DLoc.restrict t)).prod
        (stableLocalLaw θ : Measure DLoc) := by
  have hR : Measurable[DLoc.filtration t]
      (fun f => DLoc.restrict t (reversedAt t f)) := by
    have he : (fun f => DLoc.restrict t (reversedAt t f)) =
        reverseIncrements t.2 ∘ DLoc.restrict t := funext (restrict_reversedAt t)
    rw [he]
    exact (measurable_reverseIncrements t.2).comp (measurable_restrict_height_filtration t)
  have hind : IndepFun (fun f => DLoc.restrict t (reversedAt t f)) (DLoc.shift t)
      (stableLocalLaw θ : Measure DLoc) :=
    indep_of_indep_of_le_left (indep_filtration_shift_stableLocalLaw hθ t) hR.comap_le
  have hRfull : Measurable (fun f => DLoc.restrict t (reversedAt t f)) :=
    hR.mono (DLoc.filtration.le t) le_rfl
  have he := hind.map_prod_eq_prod_map_map hRfull.aemeasurable
    (DLoc.measurable_shift_fixed t).aemeasurable
  rw [map_restrict_reversedAt_stableLocalLaw hθ ht, map_shift_stableLocalLaw hθ t] at he
  exact he

end BGW.StableTrees
