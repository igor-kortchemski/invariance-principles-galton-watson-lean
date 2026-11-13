/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.SupremumAuxLocalTimeRecurrence
import Mathlib.MeasureTheory.Constructions.BorelSpace.WithTop

/-!
# Almost-everywhere measurability of the auxiliary ladder

A countable rational crossing inverse is measurable on every path. Monotonicity identifies
it with the raw inverse almost surely. This proves fixed-level a.e. measurability only,
without any all-path inverse or stopping-time identification.

## References

* J. Bertoin, *Lévy Processes*, Cambridge University Press, 1996, Chapter IV.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees

open scoped Classical in
private noncomputable def auxRatInverse (θ : ℝ) (z : ℝ≥0) (f : DLoc) : WithTop ℝ≥0 :=
  ⨅ q : {q : ℚ // 0 ≤ q},
    if (z : ℝ) < supAuxLocalTime θ f (q.1 : ℝ).toNNReal then
      ((q.1 : ℝ).toNNReal : WithTop ℝ≥0) else ⊤

private theorem measurable_auxRatInverse (θ : ℝ) (z : ℝ≥0) :
    Measurable (auxRatInverse θ z) := by
  classical
  apply Measurable.iInf
  intro q
  exact measurable_const.ite
    (measurableSet_lt measurable_const (measurable_supAuxLocalTime_eval θ _)) measurable_const

private theorem supAuxInverse_eq_auxRatInverse (θ : ℝ) (f : DLoc)
    (hm : Monotone (supAuxLocalTime θ f)) (z : ℝ≥0) :
    supAuxInverse θ f z = auxRatInverse θ z f := by
  classical
  apply le_antisymm
  · change supAuxInverse θ f z ≤ ⨅ q : {q : ℚ // 0 ≤ q}, _
    apply le_iInf
    intro q
    split_ifs with hq
    · exact sInf_le ⟨(q.1 : ℝ).toNNReal, rfl, hq⟩
    · exact le_top
  · apply le_sInf
    rintro _ ⟨u, rfl, hu⟩
    apply le_of_forall_gt
    intro b hub
    obtain ⟨v, huv, hvb⟩ := exists_between hub
    have hvtop : v ≠ ⊤ := ne_top_of_lt hvb
    lift v to ℝ≥0 using hvtop
    have huvR : (u : ℝ) < (v : ℝ) := by exact_mod_cast huv
    obtain ⟨q, huq, hqv⟩ := exists_rat_btwn huvR
    have hqR : (0 : ℝ) ≤ q := u.coe_nonneg.trans huq.le
    have hq0 : (0 : ℚ) ≤ q := by exact_mod_cast hqR
    have huqN : u ≤ (q : ℝ).toNNReal := by
      apply NNReal.coe_le_coe.mp
      rw [Real.coe_toNNReal _ hqR]
      exact huq.le
    have hqvN : (q : ℝ).toNNReal < v := by
      apply NNReal.coe_lt_coe.mp
      rw [Real.coe_toNNReal _ hqR]
      exact hqv
    have hcross : (z : ℝ) < supAuxLocalTime θ f (q : ℝ).toNNReal :=
      hu.trans_le (hm huqN)
    have hle : auxRatInverse θ z f ≤ ((q : ℝ).toNNReal : WithTop ℝ≥0) := by
      unfold auxRatInverse
      exact iInf_le_of_le ⟨q, hq0⟩ (by rw [ite_eq_left hcross])
    exact hle.trans_lt ((show ((q : ℝ).toNNReal : WithTop ℝ≥0) < (v : WithTop ℝ≥0) by
      exact_mod_cast hqvN).trans hvb)

/-- The inverse at each fixed level is a.e.-measurable (everywhere measurability of the
totalized inverse is not claimed here). -/
theorem aemeasurable_supAuxLadder {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (z : ℝ≥0) :
    AEMeasurable (supAuxLadderTime θ z) (stableLocalLaw θ : Measure DLoc) ∧
      AEMeasurable (supAuxLadderHeight θ z) (stableLocalLaw θ : Measure DLoc) := by
  have he : (fun f => (auxRatInverse θ z f).untopD 0) =ᵐ[(stableLocalLaw θ : Measure DLoc)]
      supAuxLadderTime θ z := by
    filter_upwards [ae_supAuxLocalTime_continuous hθ] with f hf
    change (auxRatInverse θ z f).untopD 0 = (supAuxInverse θ f z).untopD 0
    exact congrArg (fun t : WithTop ℝ≥0 => t.untopD 0)
      (supAuxInverse_eq_auxRatInverse θ f hf.2.1 z).symm
  have hA : AEMeasurable (supAuxLadderTime θ z) (stableLocalLaw θ : Measure DLoc) :=
    ((measurable_auxRatInverse θ z).untopD 0).aemeasurable.congr he
  refine ⟨hA, ?_⟩
  change AEMeasurable (fun f : DLoc => supRunning f (supAuxLadderTime θ z f))
    (stableLocalLaw θ : Measure DLoc)
  have hH := measurable_supRunning_uncurry.comp_aemeasurable (hA.prodMk aemeasurable_id)
  dsimp only [Function.comp_def] at hH
  exact hH

end BGW.StableTrees
