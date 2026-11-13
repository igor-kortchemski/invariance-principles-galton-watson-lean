/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.WalkPathTightness
public import BGW.StableTrees.RealAttractionBounds
import BGW.Skorokhod.Separable
import BGW.Skorokhod.CompleteMetricCompleteness
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric

/-!
# Compactness of stable-attracted walk laws

Prokhorov compactness supplies convergent subsequences of the tight step-path laws
(Billingsley, *Convergence of Probability Measures*, 2nd ed., 1999, Theorem 5.1).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace BGW.StableTrees

open BGW.Skorokhod BGW.Probability.RealWalk

/-- Every sequence of indices has a subsequence along which the step-path laws converge weakly
in `ProbabilityMeasure (D T ℝ)`. -/
theorem IsRealStableAttracted.exists_subseq_stepPathLaw {ν : ProbabilityMeasure ℝ} {θ : ℝ}
    {B : ℕ → ℝ} (h : IsRealStableAttracted ν θ B) {T : ℝ} (hT : 0 < T) (q : ℕ → ℕ) :
    ∃ (P : ProbabilityMeasure (D T ℝ)) (r : ℕ → ℕ), StrictMono r ∧
      Tendsto (fun j => stepPathLaw ν T B (q (r j))) atTop (𝓝 P) := by
  have htight : IsTightMeasureSet
      {((μ : ProbabilityMeasure (D T ℝ)) : Measure (D T ℝ)) |
        μ ∈ Set.range (stepPathLaw ν T B)} := by
    convert h.isTightMeasureSet_stepPathLaw hT using 1
    ext μ
    simp
  have hc := isCompact_closure_of_isTightMeasureSet htight
  obtain ⟨P, _, r, hr, hlim⟩ := hc.tendsto_subseq
    (fun n => subset_closure (Set.mem_range_self (q n)))
  exact ⟨P, r, hr, hlim⟩

/-- Normalizer floor ratio for every `t > 0`. -/
theorem IsRealStableAttracted.tendsto_norming_floor_ratio {ν : ProbabilityMeasure ℝ} {θ : ℝ}
    {B : ℕ → ℝ} (h : IsRealStableAttracted ν θ B) {t : ℝ} (ht : 0 < t) :
    Tendsto (fun n : ℕ => B ⌊(n : ℝ) * t⌋₊ / B n) atTop (𝓝 (t ^ (1 / θ))) := by
  apply h.tendsto_norming_ratio (m := fun n => ⌊(n : ℝ) * t⌋₊)
    (q := id) ht tendsto_id
  change Tendsto (fun n : ℕ => (⌊(n : ℝ) * t⌋₊ : ℝ) / (n : ℝ)) atTop (𝓝 t)
  simpa only [mul_comm, Function.comp_def] using
    (tendsto_nat_floor_mul_div_atTop (R := ℝ) (a := t) ht.le).comp
      tendsto_natCast_atTop_atTop

end BGW.StableTrees
