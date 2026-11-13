/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module
public import BGW.Probability.PoissonCharacterizationExpectation

/-! Integer-valued counts and the probability of a collision in a fine grid. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal BigOperators

namespace BGW.Probability

variable {Ω M : Type*} [MeasurableSpace Ω] [MeasurableSpace M]
variable {P : Measure Ω} [IsProbabilityMeasure P] {ξ : Ω → Measure (ℝ≥0 × M)} {A : Set M}

/-- A finite count of a sum of unit point masses is a natural number. -/
private lemma exists_nat_eq_count {μ : Measure (ℝ≥0 × M)} {S : Set (ℝ≥0 × M)}
    (hμ : μ = Measure.sum (fun p : S => Measure.dirac (p : ℝ≥0 × M)))
    {B : Set (ℝ≥0 × M)} (hB : MeasurableSet B) (hfin : μ B ≠ ⊤) :
    ∃ n : ℕ, μ B = n := by
  classical
  let T : Set S := {p | (p : ℝ≥0 × M) ∈ B}
  have he : μ B = (T.encard : ℝ≥0∞) := by
    rw [hμ, Measure.sum_apply _ hB]
    calc
      _ = ∑' p : S, T.indicator (fun _ => (1 : ℝ≥0∞)) p := by
        apply tsum_congr
        intro p
        simp [Measure.dirac_apply' _ hB, Set.indicator, T]
      _ = ∑' _p : T, (1 : ℝ≥0∞) := (tsum_subtype T (fun _ => (1 : ℝ≥0∞))).symm
      _ = _ := ENNReal.tsum_set_one T
  have hT : T.encard ≠ ⊤ := ENat.toENNReal_ne_top.1 (he ▸ hfin)
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 hT
  exact ⟨n, by simp only [he, ← hn, ENat.toENNReal_coe]⟩

omit [IsProbabilityMeasure P] in
/-- Reading a finite counting-measure value in `ℕ` preserves its value. -/
lemma ae_natCount_cast (hξ : IsTimeSimpleLevy P ξ) {B : Set (ℝ≥0 × M)}
    (hB : MeasurableSet B) (hfin : ∀ᵐ ω ∂P, ξ ω B < ⊤) :
    ∀ᵐ ω ∂P, (natCount (ξ ω) B : ℝ≥0∞) = ξ ω B := by
  filter_upwards [hξ.counting, hfin] with ω hω hf
  obtain ⟨S, _, hμ⟩ := hω
  obtain ⟨n, hn⟩ := exists_nat_eq_count hμ hB hf.ne
  simp [natCount, hn]

end BGW.Probability
