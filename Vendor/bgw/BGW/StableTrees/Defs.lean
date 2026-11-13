/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import Mathlib.Probability.ProbabilityMassFunction.Basic
public import Mathlib.MeasureTheory.Group.Convolution
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Topology.ContinuousMap.Bounded.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Scalar walks and normalized stable attraction

The walk has offspring increments `K - 1`. Its stable-domain hypothesis states
scalar weak convergence to a probability law with Laplace transform
`exp (λ ^ α)`, for `1 < α ≤ 2`. It assumes neither a local limit estimate nor
regular variation of the normalizing sequence.

Extracted from the scalar definitions in `PoissonDeclumping/Statements/Defs.lean`
and `PoissonDeclumping/Setup/Walk.lean` in
`igor-kortchemski/rare-subtree-patterns`, commit
`fc5ef722392b1af41e8b9d5fc45d5a521b7823dd` (Apache-2.0).
-/

@[expose] public section

open MeasureTheory Filter
open scoped Topology ENNReal

namespace BGW.StableTrees

/-- The offspring mean is one, including finiteness of the mean. -/
def IsCritical (μ : PMF ℕ) : Prop := ∑' j : ℕ, (j : ℝ≥0∞) * μ j = 1

/-- The law of one increment `X = K - 1`. -/
noncomputable def stepLaw (μ : PMF ℕ) : Measure ℤ :=
  μ.toMeasure.map (fun k : ℕ => (k : ℤ) - 1)

/-- The law of the sum of `n` independent increments; the empty sum is zero. -/
noncomputable def walkLaw (μ : PMF ℕ) : ℕ → Measure ℤ
  | 0 => Measure.dirac 0
  | m + 1 => (walkLaw μ m).conv (stepLaw μ)

/-- Ratio slow variation at infinity. Positivity and measurability are not part
of this predicate; applications retain the needed hypotheses explicitly. -/
def SlowlyVarying (ℓ : ℝ → ℝ) : Prop :=
  ∀ a : ℝ, 0 < a → Tendsto (fun x : ℝ => ℓ (a * x) / ℓ x) atTop (𝓝 1)

/-- Normalized scalar attraction to a spectrally positive stable law with
Laplace exponent `λ ^ α`. The limit law is an existence hypothesis here.
The normalizer is nondecreasing and positive for `n ≥ 1`. -/
structure StableDomain (μ : PMF ℕ) (α : ℝ) (a : ℕ → ℝ) : Prop where
  critical : IsCritical μ
  nondegenerate : μ 1 ≠ 1
  alpha_mem : 1 < α ∧ α ≤ 2
  monotone : Monotone a
  pos : ∀ n : ℕ, 1 ≤ n → 0 < a n
  converges : ∃ ν : Measure ℝ, IsProbabilityMeasure ν ∧
    (∀ lam : ℝ, 0 < lam → ∫ y, Real.exp (-lam * y) ∂ν = Real.exp (lam ^ α)) ∧
    ∀ f : BoundedContinuousFunction ℝ ℝ,
      Tendsto (fun n : ℕ => ∫ x, f x ∂((walkLaw μ n).map (fun z : ℤ => (z : ℝ) / a n)))
        atTop (𝓝 (∫ x, f x ∂ν))

/-- Stable attraction for some index and normalizing sequence. -/
def InStableDomain (μ : PMF ℕ) : Prop := ∃ (α : ℝ) (a : ℕ → ℝ), StableDomain μ α a

/-- A walk point probability, extended to zero at negative integer times. -/
noncomputable def walkProb (μ : PMF ℕ) (m : ℤ) (i : ℤ) : ℝ :=
  if 0 ≤ m then (walkLaw μ m.toNat).real {i} else 0

end BGW.StableTrees
