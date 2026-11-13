/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import Mathlib.Probability.Martingale.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut

/-!
# Finite-grid identities for the stopped energy calculation

The algebraic identity uses right endpoint values of the correction and retains the
sum of squared finite-variation increments. This remainder must be removed by continuity
in a subsequent mesh limit; no continuity of the martingale is needed here.

## References

* J. Bertoin, *Lévy Processes*, Cambridge University Press, 1996, Chapter IV.
-/

@[expose] public section

open MeasureTheory

namespace BGW.StableTrees

/-- Summation by parts for `D = C + w`, retaining the square-increment remainder of `C`. -/
theorem stopped_energy_grid_identity (D C : ℕ → ℝ) (hD : D 0 = 0) (hC : C 0 = 0)
    (N : ℕ) :
    D N ^ 2 =
      2 * (∑ k ∈ Finset.range N, C k * (D (k + 1) - D k)) +
      2 * (∑ k ∈ Finset.range N, (D (k + 1) - C (k + 1)) * (C (k + 1) - C k)) +
      (∑ k ∈ Finset.range N, (C (k + 1) - C k) ^ 2) + (D N - C N) ^ 2 := by
  induction N with
  | zero => simp [hD, hC]
  | succ N ih =>
    simp only [Finset.sum_range_succ]
    nlinarith only [ih]

/-- An adapted multiplier is orthogonal to a future martingale increment whenever their
product is integrable. In applications the multiplier is bounded on the stopped interval. -/
theorem integral_mul_martingale_increment_eq_zero {Ω ι : Type*} [MeasurableSpace Ω]
    [Preorder ι] {μ : Measure Ω} [IsFiniteMeasure μ] {ℱ : Filtration ι ‹MeasurableSpace Ω›}
    {D : ι → Ω → ℝ} (hD : Martingale D ℱ μ) {s t : ι} (hst : s ≤ t)
    {X : Ω → ℝ} (hX : StronglyMeasurable[ℱ s] X)
    (hi : Integrable (fun ω => X ω * (D t ω - D s ω)) μ) :
    ∫ ω, X ω * (D t ω - D s ω) ∂μ = 0 := by
  have hinc := condExp_sub (hD.integrable t) (hD.integrable s) (ℱ s)
  have hi' : Integrable (X * (D t - D s)) μ := hi
  have hp := condExp_mul_of_stronglyMeasurable_left hX hi'
    ((hD.integrable t).sub (hD.integrable s))
  have hz : μ[fun ω => X ω * (D t ω - D s ω) | ℱ s] =ᵐ[μ] 0 := by
    filter_upwards [hp, hinc, hD.2 s t hst] with ω hp hi he
    change μ[X * (D t - D s) | ℱ s] ω = 0
    simp only [Pi.mul_apply, Pi.sub_apply] at hp hi
    rw [hp, hi, he,
      condExp_of_stronglyMeasurable (ℱ.le s) (hD.stronglyMeasurable s) (hD.integrable s)]
    simp
  rw [← integral_condExp (ℱ.le s)]
  exact integral_eq_zero_of_ae hz

end BGW.StableTrees
