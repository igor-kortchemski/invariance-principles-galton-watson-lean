/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.DiscreteForestBasic
import Mathlib.Probability.Independence.InfinitePi

/-!
# Laws of shifted offspring sequences

Coordinate shifts preserve the iid offspring law, and the real increments have
the canonical iid real-walk law. Stopping times of the coordinate filtration and
their pre-stopped events are also defined here.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal Classical

namespace BGW.StableTrees.DiscreteForest

open BGW.Probability.RealWalk

/-- The iid sequence law is shift invariant. -/
theorem map_shiftSeq_offspringSeqLaw (μ : PMF ℕ) (m : ℕ) :
    ((offspringSeqLaw μ).toMeasure).map (shiftSeq m) = (offspringSeqLaw μ).toMeasure := by
  exact Measure.map_infinitePi_infinitePi_of_inj (P := fun _ : ℕ => μ.toMeasure)
    (fun _ _ h => Nat.add_left_cancel h)

/-- The walk `(ω i - 1)_i` of `offspringSeqLaw μ` is the iid real walk with step law
`realOffspringStepLaw μ`. -/
theorem map_offspringSeqLaw_realIncrements (μ : PMF ℕ) :
    ((offspringSeqLaw μ : ProbabilityMeasure (ℕ → ℕ)) : Measure (ℕ → ℕ)).map
        (fun ω i => ((ω i : ℤ) - 1 : ℝ)) =
      ((iidLaw (realOffspringStepLaw μ) : ProbabilityMeasure (ℕ → ℝ)) : Measure (ℕ → ℝ)) := by
  change (Measure.infinitePi (fun _ : ℕ => μ.toMeasure)).map _ = _
  rw [Measure.infinitePi_map_pi (f := fun _ : ℕ => fun k : ℕ => ((k : ℤ) - 1 : ℝ))
    (fun _ : ℕ => μ.toMeasure) (fun _ => by fun_prop)]
  congr 1
  funext i
  change μ.toMeasure.map (fun k : ℕ => ((k : ℤ) - 1 : ℝ)) =
    (stepLaw μ).map (fun z : ℤ => (z : ℝ))
  rw [stepLaw, Measure.map_map (by fun_prop) (by fun_prop)]
  simp only [Function.comp_def, Int.cast_sub, Int.cast_one]

/-- `E` is determined, on `{N = n}`, by the first `n` coordinates, and so is `{N = n}`:
the pre-`N` events of an `ℕ∞`-valued stopping time `N` of the coordinate filtration. -/
def PreStopped (N : (ℕ → ℕ) → ℕ∞) (E : Set (ℕ → ℕ)) : Prop :=
  ∀ (n : ℕ) (ω ω' : ℕ → ℕ), N ω = n → (∀ i < n, ω i = ω' i) → N ω' = n ∧ (ω ∈ E ↔ ω' ∈ E)

/-- A stopping time of the coordinate filtration with values in `ℕ∞`. -/
def IsSeqStoppingTime (N : (ℕ → ℕ) → ℕ∞) : Prop := PreStopped N Set.univ

end BGW.StableTrees.DiscreteForest
