/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.SupremumAuxLocalTimeRecurrence
public import BGW.StableTrees.SupremumAuxLocalTimeSupport
import BGW.StableTrees.StablePassageSubordinatorPath

/-!
# Simultaneous auxiliary ladder geometry

A continuous clock is encoded as a negative continuous path, allowing reuse of the generic
strict-passage geometry from the infimum development.
The proof uses no identification of the public local time.

## References

* J. Bertoin, *Lévy Processes*, Cambridge University Press, 1996, Chapter IV.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees

/-- **Inverse geometry, simultaneously for all levels `z`**: `A^*` is finite and agrees with
`supAuxInverse`, `A^*_0 = 0`, monotone, right continuous, unbounded; `B^*` monotone;
`L^aux(A^*_z) = z`; and `R_{A^*_z} = 0` (`A^*_z ∈ {S = X}`, so `B^*_z = X_{A^*_z}`). -/
theorem ae_supAuxLadder_spec {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc),
      (∀ z : ℝ≥0, supAuxInverse θ f z = (supAuxLadderTime θ z f : WithTop ℝ≥0)) ∧
        supAuxLadderTime θ 0 f = 0 ∧ Monotone (fun z => supAuxLadderTime θ z f) ∧
        (∀ z, ContinuousWithinAt (fun z => supAuxLadderTime θ z f) (Ici z) z) ∧
        Tendsto (fun z => supAuxLadderTime θ z f) atTop atTop ∧
        Monotone (fun z => supAuxLadderHeight θ z f) ∧
        (∀ z : ℝ≥0, supAuxLocalTime θ f (supAuxLadderTime θ z f) = z) ∧
        (∀ z : ℝ≥0, supAuxLadderTime θ z f ∈ supContact f) ∧
        ∀ z : ℝ≥0, supAuxLadderHeight θ z f = f.1 (supAuxLadderTime θ z f) := by
  filter_upwards [ae_supAuxLocalTime_spec hθ, ae_supAuxLocalTime_pos hθ,
    ae_leftLim_le_stableLocalLaw hθ] with f hm hp hf
  let g : DLoc := ⟨fun t => -supAuxLocalTime θ f t, hm.2.2.1.neg.isCadlag⟩
  let A : ℝ≥0 → ℝ≥0 := fun z => supAuxLadderTime θ z f
  have he (z : ℝ≥0) : supAuxInverse θ f z = firstPassageBelow z g := by
    apply le_antisymm
    · apply le_iInf
      intro u
      apply le_iInf
      intro hu
      apply sInf_le
      refine ⟨u, rfl, ?_⟩
      change -supAuxLocalTime θ f u < -(z : ℝ) at hu
      linarith
    · apply le_sInf
      rintro _ ⟨u, rfl, hu⟩
      apply firstPassageBelow_le_of_eval_lt
      change -supAuxLocalTime θ f u < -(z : ℝ)
      linarith
  have hfin (z : ℝ≥0) : firstPassageBelow z g < ⊤ := by
    obtain ⟨u, hu⟩ := (hm.2.2.2.eventually (eventually_gt_atTop (z : ℝ))).exists
    exact (firstPassageBelow_le_of_eval_lt (show g.1 u < -(z : ℝ) by
      change -supAuxLocalTime θ f u < -(z : ℝ)
      linarith)).trans_lt (WithTop.coe_lt_top u)
  have hAc (z : ℝ≥0) : A z = (firstPassageBelow z g).untopD 0 := by
    change (supAuxInverse θ f z).untopD 0 = _
    rw [he]
  have hAf : A = fun z => (firstPassageBelow z g).untopD 0 := funext hAc
  have hco (z : ℝ≥0) : supAuxInverse θ f z = (A z : WithTop ℝ≥0) := by
    rw [he, hAc]
    exact firstPassageBelow_eq_coe_untopD g hfin z
  have hAmono : Monotone A := by
    rw [hAf]
    exact untopD_firstPassageBelow_mono g hfin
  have hA0 : A 0 = 0 := by
    apply le_antisymm _ (zero_le : (0 : ℝ≥0) ≤ A 0)
    apply le_of_forall_gt
    intro b hb
    have hh : supAuxInverse θ f 0 ≤ ((b / 2 : ℝ≥0) : WithTop ℝ≥0) :=
      sInf_le ⟨b / 2, rfl, hp (b / 2) (half_pos hb)⟩
    rw [hco] at hh
    have hhalf : A 0 ≤ b / 2 := by exact_mod_cast hh
    exact hhalf.trans_lt (half_lt_self hb)
  have hval (z : ℝ≥0) : supAuxLocalTime θ f (A z) = z := by
    by_cases hz : z = 0
    · simp only [hz, hA0, hm.1, NNReal.coe_zero]
    · have hz0 : 0 < (z : ℝ) := by exact_mod_cast pos_iff_ne_zero.mpr hz
      have hg : ∀ u, Function.leftLim g.1 u ≤ g.1 u := by
        intro u
        exact ((hm.2.2.1.neg.continuousAt).continuousWithinAt.leftLim_eq).le
      have hpass : DLoc.strictPassageBelow (-(z : ℝ)) g = (A z : WithTop ℝ≥0) :=
        (he z).symm.trans (hco z)
      have hh := eval_eq_of_strictPassageBelow_eq_coe hg hpass (show -(z : ℝ) < g.1 0 by
        change -(z : ℝ) < -supAuxLocalTime θ f 0
        rw [hm.1]
        linarith)
      change -supAuxLocalTime θ f (A z) = -(z : ℝ) at hh
      exact neg_injective hh
  have hright (z : ℝ≥0) : ContinuousWithinAt A (Ici z) z := by
    rw [ContinuousWithinAt, ← nhdsGT_sup_nhdsWithin_singleton z, tendsto_sup]
    constructor
    · rw [hAf]
      exact tendsto_untopD_firstPassageBelow_nhdsGT g hfin z
    · simpa only [nhdsWithin_singleton] using tendsto_pure_nhds A z
  have hAtop : Tendsto A atTop atTop := by
    apply tendsto_atTop.mpr
    intro t
    let z := (supAuxLocalTime θ f t + 1).toNNReal
    have hmt0 : 0 ≤ supAuxLocalTime θ f t := by
      simpa only [hm.1] using hm.2.1 (zero_le : (0 : ℝ≥0) ≤ t)
    have hz : (z : ℝ) = supAuxLocalTime θ f t + 1 :=
      Real.coe_toNNReal _ (by positivity)
    have htA : t ≤ A z := by
      by_contra h
      have hh := hm.2.1 (lt_of_not_ge h).le
      rw [hval, hz] at hh
      linarith
    filter_upwards [eventually_ge_atTop z] with y hy
    exact htA.trans (hAmono hy)
  have hcontact (z : ℝ≥0) : A z ∈ supContact f := by
    by_contra hn
    have hR : 0 < supReflected f (A z) :=
      lt_of_le_of_ne (supReflected_nonneg f _) (Ne.symm hn)
    have hU := lowerSemicontinuous_supReflected hf (A z) 0 hR
    obtain ⟨b, hAb, hb⟩ := (nhdsGT_basis (A z)).mem_iff.mp
      (mem_nhdsWithin_of_mem_nhds hU)
    obtain ⟨v, hAv, hvb⟩ := exists_between hAb
    have hv : supAuxLocalTime θ f v = supAuxLocalTime θ f (A z) := by
      apply supAuxLocalTime_eq_of_gap hθ hf hAv.le
      intro u hu
      rcases hu.1.eq_or_lt with heq | hlt
      · simpa only [← heq] using hR
      · exact hb ⟨hlt, hu.2.trans_lt hvb⟩
    have hpass : firstPassageBelow z g < (v : WithTop ℝ≥0) := by
      rw [← he, hco]
      exact_mod_cast hAv
    obtain ⟨u, huv, hu⟩ := exists_eval_lt_of_firstPassageBelow_lt hpass
    have hmu := hm.2.1 huv.le
    rw [hv, hval] at hmu
    change -supAuxLocalTime θ f u < -(z : ℝ) at hu
    linarith
  refine ⟨hco, hA0, hAmono, hright, hAtop, ?_, hval, hcontact, ?_⟩
  · exact (monotone_supRunning f).comp hAmono
  · intro z
    exact (mem_supContact_iff.mp (hcontact z)).symm

end BGW.StableTrees
