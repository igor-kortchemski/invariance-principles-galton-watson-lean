/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module
public import BGW.Probability.PoissonCharacterizationPGF
public import Mathlib.Probability.Distributions.Poisson.Basic

/-! Identification of the joint count law by its complex generating function. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology WithLp
open scoped NNReal ENNReal BigOperators

namespace BGW.Probability

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- A complex generating function on the unit polydisk identifies a product Poisson law. -/
lemma map_eq_pi_poisson_of_complex_pgf {k : ℕ} (N : Fin k → Ω → ℕ)
    (hN : ∀ i, Measurable (N i)) (r : Fin k → ℝ≥0)
    (hpgf : ∀ z : Fin k → ℂ, (∀ i, ‖z i‖ ≤ 1) →
      (∫ ω, ∏ i, z i ^ N i ω ∂P) =
        Complex.exp (∑ i, ((r i : ℝ) : ℂ) * (z i - 1))) :
    P.map (fun ω i => N i ω) = Measure.pi (fun i => poissonMeasure (r i)) := by
  let g : (Fin k → ℕ) → (Fin k → ℝ) := fun x i => (x i : ℝ)
  let X : Ω → (Fin k → ℝ) := fun ω i => (N i ω : ℝ)
  have hg : MeasurableEmbedding g := by
    refine ⟨?_, by fun_prop, ?_⟩
    · intro x y hxy
      funext i
      exact Nat.cast_injective (congrFun hxy i)
    · intro s _
      exact ((Set.to_countable s).image g).measurableSet
  have hX : Measurable X := by fun_prop
  have hreal : P.map X = Measure.pi (fun i => (poissonMeasure (r i)).map (Nat.cast : ℕ → ℝ)) := by
    apply (charFun_eq_pi_iff (μ := fun i => (poissonMeasure (r i)).map (Nat.cast : ℕ → ℝ))).1
    intro v
    rw [charFun_apply, integral_map (by fun_prop) (by fun_prop),
      integral_map hX.aemeasurable (by fun_prop)]
    have hz (i : Fin k) : ‖Complex.exp ((v i : ℂ) * Complex.I)‖ ≤ 1 := by
      simp [Complex.norm_exp]
    have he := hpgf (fun i => Complex.exp ((v i : ℂ) * Complex.I)) hz
    simp only [charFun_map_cast_poissonMeasure]
    rw [← Complex.exp_sum]
    convert he using 1
    apply integral_congr_ae
    exact Eventually.of_forall fun ω => by
      simp only [PiLp.inner_apply, Real.inner_apply, X,
        Complex.ofReal_sum, Finset.sum_mul, Complex.exp_sum]
      apply Finset.prod_congr rfl
      intro i _
      rw [← Complex.exp_nat_mul]
      congr 1
      push_cast
      ring
  apply hg.map_injective
  rw [Measure.map_map hg.measurable (by fun_prop), Measure.pi_map_pi
    (f := fun _ => (Nat.cast : ℕ → ℝ))
    (fun _ => Measurable.of_discrete.aemeasurable)]
  exact hreal

variable {M : Type*} [MeasurableSpace M] {ξ : Ω → Measure (ℝ≥0 × M)}

/-- **Independent Poisson counts** on finitely many disjoint finite-rate boxes. -/
theorem counts_poisson_independent (hξ : IsTimeSimpleLevy P ξ) {k : ℕ} (A : Fin k → Set M)
    (hA : ∀ i, IsFiniteRate P ξ (A i)) (s t : Fin k → ℝ≥0) (hst : ∀ i, s i ≤ t i)
    (hdisj : Pairwise (Function.onFun Disjoint fun i => Ioc (s i) (t i) ×ˢ A i)) :
    P.map (fun ω i => natCount (ξ ω) (Ioc (s i) (t i) ×ˢ A i)) =
      Measure.pi (fun i => poissonMeasure ((t i - s i) * (markRate P ξ (A i)).toNNReal)) := by
  apply map_eq_pi_poisson_of_complex_pgf
    (fun i ω => natCount (ξ ω) (Ioc (s i) (t i) ×ˢ A i))
    (fun i => measurable_natCount hξ.measurable (measurable_box (hA i).1))
  intro z hz
  convert integral_complex_pgf_boxes hξ A hA s t hst hdisj z hz using 1
  simp [ENNReal.coe_toNNReal_eq_toReal]

end BGW.Probability
