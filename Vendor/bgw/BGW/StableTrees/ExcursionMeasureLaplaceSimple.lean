/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.ExcursionMeasureLaplacePartition

/-! Laplace functionals of simple tests supported in a finite-rate box.

See Bertoin, *Lévy Processes*, Chapter IV.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal BigOperators
open BGW.Skorokhod

namespace BGW.StableTrees

/-- The excursion Laplace functional for a simple test supported in a bounded slab box. -/
theorem excursion_laplace_simple {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    {ξ : DLoc → Measure (ℝ≥0 × Excursion)} (hξ : Measurable ξ)
    (hae : ξ =ᵐ[(stableLocalLaw θ : Measure DLoc)] excursionPointMeasure)
    (T ε : ℝ≥0) (hε : 0 < ε) (g : SimpleFunc (ℝ≥0 × Excursion) ℝ≥0∞)
    (hgs : Function.support g ⊆ Ioc 0 T ×ˢ {e : Excursion | ε < e.lifetime}) :
    (∫⁻ f, expNeg (∫⁻ p, g p ∂ξ f) ∂(stableLocalLaw θ : Measure DLoc)) =
      expNeg (∫⁻ p, 1 - expNeg (g p) ∂(lebNN.prod (excursionMeasure θ))) := by
  classical
  let I := ↥g.range
  let B : I → Set (ℝ≥0 × Excursion) := fun r => if r.val = 0 then ∅ else g ⁻¹' {r.val}
  have hB (r : I) : MeasurableSet (B r) := by
    dsimp [B]
    split_ifs
    · exact MeasurableSet.empty
    · exact g.measurableSet_fiber _
  have hpre (r : I) : B r ⊆ g ⁻¹' {r.val} := by
    dsimp [B]
    split_ifs <;> simp
  have hsub (r : I) : B r ⊆ Ioc 0 T ×ˢ {e : Excursion | ε < e.lifetime} := by
    intro p hp
    have hr : r.val ≠ 0 := by intro hz; simp [B, hz] at hp
    apply hgs
    change g p ≠ 0
    rw [show g p = r.val from hpre r hp]
    exact hr
  have hd : Pairwise (Function.onFun Disjoint B) := by
    intro r s hrs
    apply Set.disjoint_left.mpr
    intro p hpr hps
    have heq : r.val = s.val := (hpre r hpr).symm.trans (hpre s hps)
    exact hrs (Subtype.ext heq)
  have hrepr (a : ℝ≥0∞ → ℝ≥0∞) (ha : a 0 = 0) (p : ℝ≥0 × Excursion) :
      a (g p) = ∑ r : I, (B r).indicator (fun _ => a r.val) p := by
    let r₀ : I := ⟨g p, g.mem_range_self p⟩
    rw [Finset.sum_eq_single r₀]
    · by_cases hz : g p = 0
      · simp [B, r₀, hz, ha]
      · simp [B, r₀, hz]
    · intro r _ hne
      have hp : p ∉ B r := by
        intro hp
        apply hne
        apply Subtype.ext
        exact (hpre r hp).symm
      exact indicator_of_notMem hp _
    · simp
  have hint (ν : Measure (ℝ≥0 × Excursion)) (a : ℝ≥0∞ → ℝ≥0∞) (ha : a 0 = 0) :
      (∫⁻ p, a (g p) ∂ν) = ∑ r : I, a r.val * ν (B r) := by
    simp_rw [hrepr a ha]
    rw [lintegral_finsetSum]
    · apply Finset.sum_congr rfl
      intro r _
      exact lintegral_indicator_const (hB r) _
    · exact fun r _ => measurable_const.indicator (hB r)
  have hidentity (f : DLoc) : (∫⁻ p, g p ∂ξ f) = ∑ r : I, r.val * ξ f (B r) :=
    hint (ξ f) id rfl
  have htransform : (∫⁻ p, 1 - expNeg (g p) ∂(lebNN.prod (excursionMeasure θ))) =
      ∑ r : I, (1 - expNeg r.val) * (lebNN.prod (excursionMeasure θ)) (B r) :=
    hint _ (fun x => 1 - expNeg x) (by simp)
  simp_rw [hidentity, htransform]
  exact excursion_laplace_partition hθ hξ hae T ε hε B hB hsub hd Subtype.val

end BGW.StableTrees
