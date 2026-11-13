/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.SupremumLocalTimeIdent
public import BGW.StableTrees.StableStrongMarkov
public import Mathlib.Probability.Independence.Basic

/-!
# Whole-path restart law at inverse local time

The everywhere stopping representative of inverse local time is finite almost surely.
Strong Markov therefore gives the original law and independence of the entire shifted path.

Reference: J. Bertoin, *Lévy Processes*, Cambridge University Press, 1996, Chapter VI.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees

/-- The stopping representative and raw ladder time give the same centered shift almost surely. -/
theorem ae_shiftAt_supHitting_eq {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (z : ℝ≥0) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc),
      DLoc.shiftAt (supHitting θ z) f =
        DLoc.shiftAt (fun g => (supLadderTime θ z g : ℝ≥0∞)) f := by
  filter_upwards [ae_supLadder_geometry hθ] with f hf
  simp only [DLoc.shiftAt, hf.2.1 z]

/-- `A_z < ⊤` almost surely (for the stopping representative), so restart is a.s. defined. -/
theorem ae_supHitting_lt_top {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (z : ℝ≥0) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), supHitting θ z f < ⊤ := by
  filter_upwards [ae_supLadder_geometry hθ] with f hf
  rw [hf.2.1 z]
  exact ENNReal.coe_lt_top

/-- Independence of stopped events from measurable events of the restarted whole path. -/
theorem measure_inter_preimage_shiftAt_supHitting {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (z : ℝ≥0)
    {A : Set DLoc} (hA : MeasurableSet[(isStoppingTime_supHitting θ z).measurableSpace] A)
    (hAτ : A ⊆ {f | supHitting θ z f < ⊤}) {B : Set DLoc} (hB : MeasurableSet B) :
    (stableLocalLaw θ : Measure DLoc) (A ∩ DLoc.shiftAt (supHitting θ z) ⁻¹' B) =
      (stableLocalLaw θ : Measure DLoc) A * (stableLocalLaw θ : Measure DLoc) B := by
  exact measure_inter_preimage_shiftAt hθ (isStoppingTime_supHitting θ z) hA hAτ hB

/-- The post-inverse-local-time whole path has the original stable law. -/
theorem map_shiftAt_supHitting {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (z : ℝ≥0) :
    (stableLocalLaw θ : Measure DLoc).map (DLoc.shiftAt (supHitting θ z)) =
      (stableLocalLaw θ : Measure DLoc) := by
  have hfin := ae_supHitting_lt_top hθ z
  have hr : (stableLocalLaw θ : Measure DLoc).restrict {f | supHitting θ z f < ⊤} =
      (stableLocalLaw θ : Measure DLoc) := Measure.restrict_eq_self_of_ae_mem hfin
  have hm := map_shiftAt_restrict_stableLocalLaw hθ (isStoppingTime_supHitting θ z)
  have hmass : (stableLocalLaw θ : Measure DLoc) {f | supHitting θ z f < ⊤} = 1 :=
    (mem_ae_iff_prob_eq_one ((isStoppingTime_supHitting θ z).measurable'
      measurableSet_Iio)).mp hfin
  rw [hr, hmass, one_smul] at hm
  exact hm

/-- The restarted whole path is independent of the stopped sigma algebra. -/
theorem indep_shiftAt_supHitting {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (z : ℝ≥0) :
    Indep (isStoppingTime_supHitting θ z).measurableSpace
      (MeasurableSpace.comap (DLoc.shiftAt (supHitting θ z)) (inferInstance : MeasurableSpace DLoc))
      (stableLocalLaw θ : Measure DLoc) := by
  let P : Measure DLoc := stableLocalLaw θ
  let τ := supHitting θ z
  have hfin := ae_supHitting_lt_top hθ z
  have hτ := isStoppingTime_supHitting θ z
  intro A B hA hB
  change MeasurableSet[hτ.measurableSpace] A at hA
  apply Filter.Eventually.of_forall
  intro a
  change P (A ∩ B) = P A * P B
  obtain ⟨B, hB, rfl⟩ := hB
  have hAS : A ∩ {f | τ f < ⊤} =ᵐ[P] A := by
    filter_upwards [hfin] with f hf
    exact propext (and_iff_left hf)
  have hi : (A ∩ {f | τ f < ⊤}) ∩ DLoc.shiftAt τ ⁻¹' B =ᵐ[P]
      A ∩ DLoc.shiftAt τ ⁻¹' B := by
    filter_upwards [hAS] with f hf
    simp only [mem_inter_iff] at *
    rw [hf]
  have hm := measure_inter_preimage_shiftAt_supHitting hθ z
    (hA.inter (DLoc.measurableSet_lt_top_stopped hτ)) inter_subset_right hB
  rw [measure_congr hi, measure_congr hAS] at hm
  have hlaw : P (DLoc.shiftAt τ ⁻¹' B) = P B := by
    rw [← Measure.map_apply (DLoc.measurable_shiftAt hτ) hB]
    exact congrArg (fun μ : Measure DLoc => μ B) (map_shiftAt_supHitting hθ z)
  rw [hlaw]
  exact hm

end BGW.StableTrees
