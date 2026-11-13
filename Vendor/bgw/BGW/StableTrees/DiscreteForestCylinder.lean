/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.DiscreteForestSequence
public import BGW.StableTrees.Scalar.ForestWalkBridge

/-!
# Finite offspring cylinders and degree words

Degree words, their weights, walk values, surviving prefixes and pending stacks.
Finite restrictions of the infinite offspring product have the usual finite
product law. Degree lists retain their order from time zero.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal Classical

namespace BGW.StableTrees.DiscreteForest

/-- The discrete sigma-algebra on degree words, local to this module. -/
local instance cylinderListMeasurable : MeasurableSpace (List ℕ) := ⊤
/-- Single degree words are measurable in the local discrete sigma-algebra. -/
local instance cylinderListSingleton : MeasurableSingletonClass (List ℕ) := ⟨fun _ => trivial⟩

/-- The first `m` offspring numbers of `ω`. -/
def seqPrefix (m : ℕ) (ω : ℕ → ℕ) : List ℕ := (List.range m).map ω

/-- The walk value `W_m(a) = ∑ (a_i - 1)` of a degree word. -/
def prefixWalk (a : List ℕ) : ℤ := (a.map (fun d => (d : ℤ) - 1)).sum

/-- Product of offspring probabilities along a degree list. -/
noncomputable def degreeWeight (μ : PMF ℕ) (a : List ℕ) : ℝ := ((a.map μ).prod).toReal

/-- A prefix of degrees is surviving if all its partial walk values are `≥ 0`. -/
def IsSurvivingPrefix (a : List ℕ) : Prop :=
  ∀ i ≤ a.length, 0 ≤ ((a.take i).map (fun d => (d : ℤ) - 1)).sum

/-- The number of pending subtrees after exploring `a`: `j = W_m + 1`. -/
def prefixStack (a : List ℕ) : ℕ := (((a.map (fun d => (d : ℤ) - 1)).sum) + 1).toNat

/-- Finite restrictions of the offspring sequence have the finite product law. -/
theorem map_offspringSeqLaw_initial (μ : PMF ℕ) (n : ℕ) :
    (offspringSeqLaw μ).toMeasure.map (fun ω (i : Fin n) => ω i) =
      Measure.pi (fun _ : Fin n => μ.toMeasure) := by
  rw [show Measure.pi (fun _ : Fin n => μ.toMeasure) =
    Measure.infinitePi (fun _ : Fin n => μ.toMeasure) from
      (Measure.infinitePi_eq_pi (fun _ : Fin n => μ.toMeasure)).symm]
  exact Measure.map_infinitePi_infinitePi_of_inj Fin.val_injective

/-- A finite restriction written as a list of its coordinates. -/
theorem seqPrefix_eq_ofFn (m : ℕ) (ω : ℕ → ℕ) :
    seqPrefix m ω = List.ofFn (fun i : Fin m => ω i) := by
  apply List.ext_getElem
  · simp [seqPrefix]
  · intro i hi hi'
    simp [seqPrefix]

/-- Prefix lists are measurable. -/
theorem measurable_seqPrefix (m : ℕ) : Measurable (seqPrefix m) := by
  change Measurable (fun ω => seqPrefix m ω)
  simp_rw [seqPrefix_eq_ofFn]
  exact (measurable_of_countable (fun a : Fin m → ℕ => List.ofFn a)).comp (by fun_prop)

/-- The increment word of a finite restriction is the existing count-vector encoding. -/
theorem stepWord_initial (m : ℕ) (ω : ℕ → ℕ) :
    BGW.stepWord (fun i : Fin m => ω i) =
      (seqPrefix m ω).map (fun d : ℕ => (d : ℤ) - 1) := by
  rw [seqPrefix_eq_ofFn, List.map_ofFn]
  rfl

/-- The sum of the initial increment word is the infinite walk at the same time. -/
theorem sum_seqPrefix (m : ℕ) (ω : ℕ → ℕ) :
    ((seqPrefix m ω).map (fun d : ℕ => (d : ℤ) - 1)).sum = walk ω m := by
  rw [seqPrefix_eq_ofFn, List.map_ofFn, List.sum_ofFn]
  exact Fin.sum_univ_eq_sum_range (fun i : ℕ => (ω i : ℤ) - 1) m

/-- Taking an initial part of a degree prefix just gives the shorter degree prefix. -/
theorem take_seqPrefix (m i : ℕ) (ω : ℕ → ℕ) (hi : i ≤ m) :
    (seqPrefix m ω).take i = seqPrefix i ω := by
  simp [seqPrefix, ← List.map_take, List.take_range, min_eq_left hi]

/-- Bridge-prefix density: `walkProb μ (n-m) (-1-W_m) / walkProb μ n (-1)`. -/
noncomputable def bridgePrefixDensity (μ : PMF ℕ) (n m : ℕ) (w : ℤ) : ℝ :=
  walkProb μ ((n - m : ℕ) : ℤ) (-1 - w) / walkProb μ n (-1)

end BGW.StableTrees.DiscreteForest
