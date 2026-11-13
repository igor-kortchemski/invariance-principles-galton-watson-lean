/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.StableExcursionSupport
public import BGW.ContinuumTrees.ExcursionCarrier
public import BGW.Probability.PoissonCharacterizationBasic
import Mathlib.MeasureTheory.Measure.Count

/-!
# Marked excursions at passage jumps

The marked measure associates each positive passage jump with its excursion cut.
This module establishes its deterministic counting representation and excursion support.

(J. Bertoin, *Lévy Processes*, Cambridge University Press, 1996, Chapter IV.)
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees

/-- The excursion attached to the jump level `x`: the excursion cut `excursionCut` of `f` on
`(T_{x-}, T_x)`. -/
noncomputable def jumpExcursion (x : ℝ≥0) (f : DLoc) : Excursion :=
  excursionCut (passageTimeMinus x f) (passageTime x f) f

open scoped Classical in
/-- **The marked excursion point measure** on `ℝ≥0 × Excursion`:
`∑_{x ∈ J f} δ_{(x, jumpExcursion x f)}` (zero measure when `J f` is not countable). -/
noncomputable def excursionPointMeasure (f : DLoc) : Measure (ℝ≥0 × Excursion) :=
  if (passageJumpSet f).Countable then
    Measure.sum (fun x : passageJumpSet f => Measure.dirac ((x : ℝ≥0), jumpExcursion x f))
  else 0

/-- **Counting-measure form** (deterministic): when `J f` is countable, the mass of a measurable
set is the number of jump levels whose marked point lies in it. -/
theorem excursionPointMeasure_apply {f : DLoc} (hf : (passageJumpSet f).Countable)
    {s : Set (ℝ≥0 × Excursion)} (hs : MeasurableSet s) :
    excursionPointMeasure f s =
      ((({x ∈ passageJumpSet f | ((x : ℝ≥0), jumpExcursion x f) ∈ s}).encard : ℕ∞) : ℝ≥0∞) := by
  classical
  rw [excursionPointMeasure, ite_eq_left hf, Measure.sum_apply _ hs,
    ← ENNReal.tsum_set_one]
  simp only [Measure.dirac_apply' _ hs]
  rw [tsum_subtype (passageJumpSet f)
    (fun x => s.indicator 1 (x, jumpExcursion x f)),
    tsum_subtype {x ∈ passageJumpSet f | (x, jumpExcursion x f) ∈ s} (fun _ => 1)]
  apply tsum_congr
  intro x
  by_cases hx : x ∈ passageJumpSet f <;>
    by_cases hsx : (x, jumpExcursion x f) ∈ s <;> simp [hx, hsx]

/-- **Counting measure** (the `counting` field of `IsTimeSimpleLevy`): a.s. the point measure is
the sum of unit Dirac masses at the points of a countable set, namely the marked points. -/
theorem ae_excursionPointMeasure_counting {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∃ S : Set (ℝ≥0 × Excursion), S.Countable ∧
      excursionPointMeasure f = Measure.sum (fun p : S => Measure.dirac (p : ℝ≥0 × Excursion)) := by
  filter_upwards [ae_passageJumpSet_countable hθ] with f hf
  classical
  let := hf.to_subtype
  let p : passageJumpSet f → ℝ≥0 × Excursion := fun x => (x, jumpExcursion x f)
  have hp : Function.Injective p := fun x y h => Subtype.ext (congrArg Prod.fst h)
  refine ⟨Set.range p, Set.countable_range p, ?_⟩
  rw [excursionPointMeasure, ite_eq_left hf]
  exact (Measure.sum_comp_equiv (Equiv.ofInjective p hp)
    (fun q : Set.range p => Measure.dirac (q : ℝ≥0 × Excursion)))

/-- **No mass at label `0`** (jump levels are positive). -/
theorem excursionPointMeasure_atZero (f : DLoc) :
    excursionPointMeasure f ({0} ×ˢ univ) = 0 := by
  classical
  by_cases hf : (passageJumpSet f).Countable
  · rw [excursionPointMeasure_apply hf
      ((measurableSet_singleton (0 : ℝ≥0)).prod MeasurableSet.univ)]
    have hempty : {x ∈ passageJumpSet f | (x, jumpExcursion x f) ∈ {0} ×ˢ univ} = ∅ := by
      ext x
      simp only [mem_ofPred_eq, mem_prod, mem_singleton_iff, mem_univ, and_true,
        mem_empty_iff_false, iff_false]
      rintro ⟨hx, rfl⟩
      exact (lt_irrefl 0) hx.1
    rw [hempty]
    simp
  · simp [excursionPointMeasure, hf]

open scoped Classical in
/-- **Atoms**: a.s., the label-`x` slice of a measurable mark set `A` has mass one iff `x` is a jump
level whose excursion lies in `A`, and zero otherwise. -/
theorem ae_excursionPointMeasure_singleton_prod {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∀ (x : ℝ≥0) (A : Set Excursion),
      MeasurableSet A →
        excursionPointMeasure f ({x} ×ˢ A) =
          if x ∈ passageJumpSet f ∧ jumpExcursion x f ∈ A then 1 else 0 := by
  filter_upwards [ae_passageJumpSet_countable hθ] with f hf
  classical
  intro x A hA
  rw [excursionPointMeasure_apply hf ((measurableSet_singleton x).prod hA)]
  have heq : {y ∈ passageJumpSet f | (y, jumpExcursion y f) ∈ {x} ×ˢ A} =
      if x ∈ passageJumpSet f ∧ jumpExcursion x f ∈ A then {x} else ∅ := by
    ext y
    split_ifs with h
    · simp only [mem_ofPred_eq, mem_prod, mem_singleton_iff]
      exact ⟨fun hy => hy.2.1, fun hy => by subst y; exact ⟨h.1, rfl, h.2⟩⟩
    · simp only [mem_ofPred_eq, mem_prod, mem_singleton_iff, mem_empty_iff_false, iff_false]
      rintro ⟨hy, rfl, hA⟩
      exact h ⟨hy, hA⟩
  rw [heq]
  split_ifs <;> simp

/-- **Time-simplicity** (the `timeSimple` field of `IsTimeSimpleLevy`): a.s. at most one excursion
per label (the labels are distinct points `x`, each carrying a single cut). -/
theorem ae_excursionPointMeasure_timeSimple {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∀ s : ℝ≥0,
      excursionPointMeasure f ({s} ×ˢ univ) ≤ 1 := by
  filter_upwards [ae_excursionPointMeasure_singleton_prod hθ] with f hf
  intro s
  rw [hf s univ MeasurableSet.univ]
  split_ifs <;> simp

end BGW.StableTrees
