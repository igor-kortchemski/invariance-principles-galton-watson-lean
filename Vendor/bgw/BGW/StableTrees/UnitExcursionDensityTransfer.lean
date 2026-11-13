/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.UnitExcursionDensityCandidate
import BGW.StableTrees.ExcursionMarkov
import BGW.Skorokhod.MeasurableJumps

/-!
# Transferring absence of fixed jumps through prefix densities

Restriction preserves the left limit at each positive prefix time.
Absolute continuity of the weighted excursion measure transfers the fixed-time property.

## References

* L. Chaumont, *Excursion normalisée, méandre et pont pour les processus de Lévy stables*,
  Bull. Sci. Math. 121 (1997), 377–403.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod
namespace BGW.StableTrees

/-- Restricting an excursion preserves its left limit at positive prefix times. -/
theorem leftLim_excursionRestrict (a t : ℝ≥0) (ht : 0 < t) (hta : t ≤ a) (e : Excursion) :
    Function.leftLim (excursionRestrict a e) ⟨t, t.2, hta⟩ = Function.leftLim e.path.1 t := by
  let s : Icc (0 : ℝ) a := ⟨t, t.2, hta⟩
  let inc : Icc (0 : ℝ) a → ℝ≥0 := fun u => ⟨u, u.2.1⟩
  let _ : NeBot (𝓝[<] s) := nhdsLT_neBot_of_exists_lt
    ⟨⟨0, le_rfl, a.2⟩, ht⟩
  apply leftLim_eq_of_tendsto
  have hc : Continuous inc := continuous_subtype_val.subtype_mk fun u => u.2.1
  have hi : Tendsto inc (𝓝[<] s) (𝓝[<] t) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨hc.continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with u hu
    exact hu
  exact (e.path.2.tendsto_nhdsLT_leftLim t).comp hi

/-- A prefix density transfers absence of fixed jumps from the excursion measure. -/
theorem noFixedJumpUnit_of_prefix_density {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    (b t : ℝ≥0) (ht : 0 < t) (htb : t ≤ b)
    (hd : unitPrefix θ b = (ENNReal.ofReal (Scalar.stableDensity θ 0))⁻¹ •
      (prefixDensityMeasure θ b).map (excursionRestrict b)) : NoFixedJumpUnit θ t := by
  let s : Icc (0 : ℝ) b := ⟨t, t.2, htb⟩
  have hB : MeasurableSet {x : D (b : ℝ) ℝ | Function.leftLim x s = x s} :=
    measurableSet_eq_fun (measurable_leftLim_eval s) (measurable_eval s)
  have hN : ∀ᵐ e ∂excursionTail θ b,
      Function.leftLim (excursionRestrict b e) s = excursionRestrict b e s := by
    have hj := ae_restrict_of_ae (s := {e : Excursion | (b : ℝ) < (e.lifetime : ℝ)})
      (N_noFixedJump hθ t ht)
    filter_upwards [hj] with e he
    rw [leftLim_excursionRestrict b t ht htb e]
    exact he
  have hW : ∀ᵐ e ∂prefixDensityMeasure θ b,
      Function.leftLim (excursionRestrict b e) s = excursionRestrict b e s :=
    (withDensity_absolutelyContinuous _ _).ae_le hN
  have hP : ∀ᵐ (x : D (b : ℝ) ℝ) ∂unitPrefix θ b, Function.leftLim x s = x s := by
    rw [hd]
    apply Measure.ae_smul_measure
    exact (ae_map_iff (measurable_excursionRestrict b).aemeasurable hB).mpr hW
  change ∀ᵐ (x : D (b : ℝ) ℝ) ∂((unitExcursionLaw θ : Measure Excursion).map
    (excursionRestrict b)), Function.leftLim x s = x s at hP
  have hE := ae_of_ae_map (measurable_excursionRestrict b).aemeasurable hP
  filter_upwards [hE] with e he
  change Function.leftLim (excursionRestrict b e) ⟨t, t.2, htb⟩ = e.path.1 t at he
  rw [leftLim_excursionRestrict b t ht htb e] at he
  exact he

end BGW.StableTrees
