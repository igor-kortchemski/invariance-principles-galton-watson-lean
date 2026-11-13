/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module
public import BGW.Probability.PoissonCharacterizationJointTransform

/-! Finite-partition generating functions for disjoint finite-rate boxes. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal BigOperators

namespace BGW.Probability

variable {Ω M : Type*} [MeasurableSpace Ω] [MeasurableSpace M]
variable {P : Measure Ω} [IsProbabilityMeasure P] {ξ : Ω → Measure (ℝ≥0 × M)}

/-- The complex generating function of disjoint finite-rate boxes, on the closed unit polydisk. -/
lemma integral_complex_pgf_boxes (hξ : IsTimeSimpleLevy P ξ) {k : ℕ} (A : Fin k → Set M)
    (hA : ∀ i, IsFiniteRate P ξ (A i)) (s t : Fin k → ℝ≥0) (hst : ∀ i, s i ≤ t i)
    (hd : Pairwise (Function.onFun Disjoint fun i => Ioc (s i) (t i) ×ˢ A i))
    (z : Fin k → ℂ) (hz : ∀ i, ‖z i‖ ≤ 1) :
    (∫ ω, ∏ i, z i ^ natCount (ξ ω) (Ioc (s i) (t i) ×ˢ A i) ∂P) =
      Complex.exp (∑ i, ((((t i - s i : ℝ≥0) : ℝ) * (markRate P ξ (A i)).toReal : ℝ) : ℂ) *
        (z i - 1)) := by
  let C : Set M := ⋃ i, A i
  let T : ℝ≥0 := Finset.univ.sup t
  let B : Fin k → Set (ℝ≥0 × M) := fun i => Ioc (s i) (t i) ×ˢ A i
  have hC : IsFiniteRate P ξ C := isFiniteRate_iUnion A hA
  have hB (i : Fin k) : MeasurableSet (B i) := measurable_box (hA i).1
  have hsub (i : Fin k) : B i ⊆ Ioc 0 T ×ˢ C := by
    intro p hp
    exact ⟨⟨(zero_le : (0 : ℝ≥0) ≤ s i).trans_lt hp.1.1,
      hp.1.2.trans (Finset.le_sup (f := t) (Finset.mem_univ i))⟩, mem_iUnion.2 ⟨i, hp.2⟩⟩
  have he := integral_complex_pgf_subsets hξ hC T B hB hsub hd z hz
  have hmean (i : Fin k) : (∫ ω, (natCount (ξ ω) (B i) : ℝ) ∂P) =
      ((t i - s i : ℝ≥0) : ℝ) * (markRate P ξ (A i)).toReal := by
    rw [integral_natCount_subset hξ hC (hB i) (hsub i),
      lintegral_count_window hξ (hA i) (hst i)]
    rw [ENNReal.toReal_mul, ENNReal.coe_toReal]
  simpa only [hmean] using he

/-- **Finite-mark partition pgf.** For finitely many boxes `(s i, t i] × A i`, pairwise disjoint
as subsets of `ℝ≥0 × M` and with finite-rate `A i`, and `z i ∈ [0,1]`:
`E ∏ z_i^{N_i} = exp(∑ (t_i - s_i) λ_{A_i} (z_i - 1))`. -/
theorem pgf_finite_partition (hξ : IsTimeSimpleLevy P ξ) {k : ℕ} (A : Fin k → Set M)
    (hA : ∀ i, IsFiniteRate P ξ (A i)) (s t : Fin k → ℝ≥0) (hst : ∀ i, s i ≤ t i)
    (hdisj : Pairwise (Function.onFun Disjoint fun i => Ioc (s i) (t i) ×ˢ A i))
    (z : Fin k → ℝ) (hz0 : ∀ i, 0 ≤ z i) (hz1 : ∀ i, z i ≤ 1) :
    ∫ ω, ∏ i, z i ^ natCount (ξ ω) (Ioc (s i) (t i) ×ˢ A i) ∂P =
      Real.exp (∑ i, ((t i - s i : ℝ≥0) : ℝ) * (markRate P ξ (A i)).toReal * (z i - 1)) := by
  have hz (i : Fin k) : ‖(z i : ℂ)‖ ≤ 1 := by
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hz0 i)] using hz1 i
  have he := integral_complex_pgf_boxes hξ A hA s t hst hdisj (fun i => (z i : ℂ)) hz
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal]
  convert he using 1 <;> simp

end BGW.Probability
