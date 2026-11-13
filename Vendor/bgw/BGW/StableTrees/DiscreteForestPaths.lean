/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.DiscreteForestSequence
public import BGW.StableTrees.WalkPathTightness
public import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
import Mathlib.Topology.Algebra.Order.Floor

/-!
# Walk and interpolated-height path laws of the discrete forest

Heights are interpolated linearly; the walk retains the floor-step convention.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal Classical

namespace BGW.StableTrees.DiscreteForest

open BGW.Skorokhod BGW.Probability.RealWalk

/-- Linear interpolation of the integer-time heights (not of the walk). -/
noncomputable def forestHeightLin (ω : ℕ → ℕ) (t : ℝ) : ℝ :=
  (1 - (t - ⌊t⌋₊)) * (forestHeight ω ⌊t⌋₊ : ℝ) + (t - ⌊t⌋₊) * (forestHeight ω (⌊t⌋₊ + 1) : ℝ)

private theorem forestHeightLin_cell (ω : ℕ → ℕ) (n : ℕ) {t : ℝ}
    (ht : t ∈ Icc (n : ℝ) (n + 1)) :
    forestHeightLin ω t =
      (1 - (t - n)) * (forestHeight ω n : ℝ) + (t - n) * (forestHeight ω (n + 1) : ℝ) := by
  by_cases he : t = n + 1
  · subst t
    have hf : ⌊(n : ℝ) + 1⌋₊ = n + 1 := by
      rw [← Nat.cast_add_one, Nat.floor_natCast]
    simp [forestHeightLin, hf]
  · have hf : ⌊t⌋₊ = n := (Nat.floor_eq_iff (le_trans (Nat.cast_nonneg n) ht.1)).2
      ⟨ht.1, lt_of_le_of_ne ht.2 he⟩
    simp only [forestHeightLin, hf]

private theorem continuousOn_heightLin_cell (ω : ℕ → ℕ) (n : ℕ) :
    ContinuousOn (forestHeightLin ω) (Icc (n : ℝ) (n + 1)) := by
  apply ContinuousOn.congr (f := fun t : ℝ =>
    (1 - (t - n)) * (forestHeight ω n : ℝ) + (t - n) * (forestHeight ω (n + 1) : ℝ))
      (by fun_prop)
  intro t ht
  exact forestHeightLin_cell ω n ht

private theorem continuousOn_heightLin_Iic (ω : ℕ → ℕ) (n : ℕ) :
    ContinuousOn (forestHeightLin ω) (Iic (n : ℝ)) := by
  induction n with
  | zero =>
    apply ContinuousOn.congr (f := fun t : ℝ =>
      (1 - t) * (forestHeight ω 0 : ℝ) + t * (forestHeight ω 1 : ℝ)) (by fun_prop)
    intro t ht
    have ht0 : t ≤ 0 := by simpa using ht
    have hf : ⌊t⌋₊ = 0 := Nat.floor_eq_zero.mpr (by linarith)
    simp [forestHeightLin, hf]
  | succ n ih =>
    have hu : Iic (n : ℝ) ∪ Icc (n : ℝ) (n + 1) = Iic ((n + 1 : ℕ) : ℝ) := by
      ext t
      simp only [mem_union, mem_Iic, mem_Icc, Nat.cast_add, Nat.cast_one]
      constructor
      · rintro (h | h) <;> linarith [h]
      · intro h
        rcases le_total t (n : ℝ) with hn | hn
        · exact Or.inl hn
        · exact Or.inr ⟨hn, h⟩
    rw [← hu]
    exact ih.union_of_isClosed (continuousOn_heightLin_cell ω n) isClosed_Iic isClosed_Icc

/-- The interpolated height is continuous. -/
theorem continuous_forestHeightLin (ω : ℕ → ℕ) : Continuous (forestHeightLin ω) := by
  rw [continuous_iff_continuousAt]
  intro t
  have ht : t < ((⌊t⌋₊ + 1 : ℕ) : ℝ) := by
    simpa only [Nat.cast_add, Nat.cast_one] using Nat.lt_floor_add_one t
  exact (continuousOn_heightLin_Iic ω (⌊t⌋₊ + 1)).continuousAt (Iic_mem_nhds ht)

/-- The normalised interpolated height path `t ↦ (B n / n) * forestHeightLin ω (n t)` on
`[0,T]`. -/
noncomputable def forestHeightPath (B : ℕ → ℝ) (n : ℕ) (T : ℝ≥0) (ω : ℕ → ℕ) :
    C(Set.Icc (0 : ℝ) (T : ℝ), ℝ) :=
  ⟨fun t => (B n / n) * forestHeightLin ω ((n : ℝ) * (t : ℝ)),
    (continuous_const.mul ((continuous_forestHeightLin ω).comp
      (continuous_const.mul continuous_subtype_val)))⟩

/-- The rescaled floor-step walk `t ↦ W_{⌊n t⌋} / B n` as an element of `D T ℝ`. -/
noncomputable def forestWalkPath (B : ℕ → ℝ) (n : ℕ) (T : ℝ≥0) (ω : ℕ → ℕ) : D (T : ℝ) ℝ :=
  realStepPath (T : ℝ) n (B n) (fun i => ((ω i : ℤ) - 1 : ℝ))

/-- The pair `(walk, height)` path of the forest, with uniform topology on heights. -/
noncomputable def forestPairPath (B : ℕ → ℝ) (n : ℕ) (T : ℝ≥0) (ω : ℕ → ℕ) :
    D (T : ℝ) ℝ × C(Set.Icc (0 : ℝ) (T : ℝ), ℝ) :=
  (forestWalkPath B n T ω, forestHeightPath B n T ω)

/-- Each integer-time walk coordinate is measurable. -/
theorem measurable_walk (k : ℕ) : Measurable (fun ω => walk ω k) := by
  unfold walk
  fun_prop

/-- Each integer-time record count is measurable. -/
theorem measurable_forestHeight (k : ℕ) : Measurable (fun ω => forestHeight ω k) := by
  simp only [forestHeight, Finset.card_eq_sum_ones, Finset.sum_filter]
  apply Finset.measurable_sum
  intro j _
  apply Measurable.ite _ measurable_const measurable_const
  have hm (j l : ℕ) := measurableSet_le (measurable_walk j) (measurable_walk l)
  simp only [ofPred_forall]
  exact MeasurableSet.iInter fun l => MeasurableSet.iInter fun _ =>
    MeasurableSet.iInter fun _ => hm j l

/-- (K01) Measurability of the pair path. -/
theorem measurable_forestPairPath (B : ℕ → ℝ) (n : ℕ) (T : ℝ≥0) :
    Measurable (forestPairPath B n T) := by
  apply Measurable.prodMk
  · exact (measurable_realStepPath _ _ _).comp (by fun_prop)
  · apply ContinuousMap.measurable_iff_eval.mpr
    intro t
    change Measurable (fun ω => (B n / n) * forestHeightLin ω ((n : ℝ) * (t : ℝ)))
    unfold forestHeightLin
    have hc : Measurable (fun a : ℕ => (a : ℝ)) := measurable_of_countable _
    exact (measurable_const.mul (hc.comp (measurable_forestHeight _))).add
      (measurable_const.mul (hc.comp (measurable_forestHeight _))) |>.const_mul _

/-- The law of the pair path under the iid offspring sequence. -/
noncomputable def forestPairLaw (μ : PMF ℕ) (B : ℕ → ℝ) (n : ℕ) (T : ℝ≥0) :
    ProbabilityMeasure (D (T : ℝ) ℝ × C(Set.Icc (0 : ℝ) (T : ℝ), ℝ)) :=
  (offspringSeqLaw μ).map (forestPairPath B n T)

/-- The first marginal of the forest pair law is the step-path law of the offspring walk. -/
theorem forestPairLaw_fst (μ : PMF ℕ) (B : ℕ → ℝ) (n : ℕ) (T : ℝ≥0) :
    ((forestPairLaw μ B n T).toMeasure).map Prod.fst =
      ((stepPathLaw (realOffspringStepLaw μ) (T : ℝ) B n :
        ProbabilityMeasure (D (T : ℝ) ℝ)) : Measure (D (T : ℝ) ℝ)) := by
  change (Measure.map (forestPairPath B n T) (offspringSeqLaw μ).toMeasure).map Prod.fst =
    Measure.map (realStepPath (T : ℝ) n (B n)) (iidLaw (realOffspringStepLaw μ)).toMeasure
  rw [Measure.map_map measurable_fst (measurable_forestPairPath B n T),
    ← map_offspringSeqLaw_realIncrements, Measure.map_map (measurable_realStepPath _ _ _)
      (by fun_prop)]
  rfl

end BGW.StableTrees.DiscreteForest
