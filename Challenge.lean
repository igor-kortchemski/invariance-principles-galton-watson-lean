/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.List.Count
public import Mathlib.Data.List.OfFn
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.W.Basic
public import Mathlib.MeasureTheory.Function.Floor
public import Mathlib.MeasureTheory.Group.Convolution
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
public import Mathlib.Probability.ConditionalProbability
public import Mathlib.Probability.ProbabilityMassFunction.Basic
public import Mathlib.Probability.ProductMeasure
public import Mathlib.Topology.ContinuousMap.Bounded.Basic
public import Lean.Meta.Tactic.AuxLemma

/-!
# Discrete asymptotics for Galton–Watson trees conditioned on leaves

Statement interface for arXiv:1110.2163v4 by Igor Kortchemski,
Stochastic Processes and their Applications 122 (2012), 3126–3172.
The seven compared declarations cover Theorem 1.10(i–iii) with corrected
norming, Theorem 3.1(i–ii) (Introduction (I)), corrected Theorem 8.1(I),
and Theorem 7.1(ii). Functional convergence results are outside this interface.

Conventions: offspring laws are probability mass functions on the naturals;
the stable law has Laplace transform `exp(λ^θ)`, `1 < θ ≤ 2`. Trees are
rooted and ordered. `bienaymeLaw` prunes an independent offspring field;
`finiteTreeEvent` embeds finite plane trees in that carrier.
The arithmetic filters retain admissible sizes, including lattice cases.

All definitions have their actual values. Only the seven selected theorem
proofs are deliberate `sorry` placeholders. `Solution.lean` imports the proved
development, never this file. The defining helpers below retain their proofs.
See the README and FORMALIZATION_REPORT.md for corrections and proof routes.
-/

@[expose] public section

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Asymptotics Set
open scoped ENNReal NNReal Topology

namespace BGW.LocallyFinite


/-- A vertex address, with positive child indices and `[]` for the root. -/
abbrev Address := List ℕ


/-- A field assigning a finite offspring count to each address. -/
abbrev Offspring := Address → ℕ


/-- Invalid children have zero offspring; the condition propagates to descendants. -/
def Canonical (f : Offspring) : Prop :=
  ∀ (u : Address) (j : ℕ), ¬(1 ≤ j ∧ j ≤ f u) → f (u ++ [j]) = 0


/-- Canonical offspring fields describe possibly infinite, locally finite plane trees. -/
abbrev Tree := {f : Offspring // Canonical f}


/-- The number of children of the root. -/
def degree (T : Tree) : ℕ := T.val []


/-- Re-root at child `j`. An absent child is represented by `leaf`; use `Present`
to test whether that child actually exists. -/
def child (T : Tree) (j : ℕ) : Tree :=
  ⟨fun u => T.val (j :: u), fun u k hk => T.property (j :: u) k hk⟩


/-- Membership of an address, including leaves and the root. -/
def Present (T : Tree) : Address → Prop
  | [] => True
  | j :: u => 1 ≤ j ∧ j ≤ degree T ∧ Present (child T j) u

end BGW.LocallyFinite

namespace BGW.LocallyFinite


-- Keep the auxiliary matcher name used in its original, separate source module.
set_option bootstrap.genMatcherCode false in
/-- Keep the offspring count at an address only if every step of the address is a valid child
of the retained counts above it. -/
def pruneRaw (f : Offspring) : Address → ℕ
  | [] => f []
  | j :: u => if 1 ≤ j ∧ j ≤ f [] then pruneRaw (fun v => f (j :: v)) u else 0


theorem canonical_pruneRaw (f : Offspring) : Canonical (pruneRaw f) := by
  intro u j
  induction u generalizing f with
  | nil =>
    simp only [List.nil_append, pruneRaw]
    intro hj
    rw [ite_eq_right hj]
  | cons i u ih =>
    by_cases hi : 1 ≤ i ∧ i ≤ f []
    · simpa only [List.cons_append, pruneRaw, ite_eq_left hi] using ih (fun v => f (i :: v))
    · simp only [List.cons_append, pruneRaw, hi, ↓reduceIte]
      intro _
      trivial

/-- The tree obtained from an offspring field by discarding the counts at absent addresses. -/
def prune (f : Offspring) : Tree := ⟨pruneRaw f, canonical_pruneRaw f⟩

end BGW.LocallyFinite

namespace BGW.LocallyFinite


/-- Independent potential offspring counts, one for each address.

The probability hypothesis is not used by the formula, but it fixes the domain of the definition:
`Measure.infinitePi` is the zero measure unless every component is a probability measure, so
without it the definition would expose that default value instead of an offspring law. -/
@[nolint unusedArguments]
noncomputable def offspringFieldLaw (μ : Measure ℕ) [IsProbabilityMeasure μ] :
    Measure Offspring :=
  Measure.infinitePi (fun _ : Address => μ)


/-- The Bienaymé–Galton–Watson law with offspring law `μ`. -/
noncomputable def bienaymeLaw (μ : Measure ℕ) [IsProbabilityMeasure μ] : Measure Tree :=
  (offspringFieldLaw μ).map prune

end BGW.LocallyFinite

namespace BGW


/-- Finite rooted ordered trees, with no vertex labels. -/
def PlaneTree : Type := WType (fun n : ℕ => Fin n)

end BGW

namespace BGW.PlaneTree


/-- A tree is determined by the ordered list of subtrees attached to its root. -/
def equivChildren : PlaneTree ≃ List PlaneTree :=
  (WType.equivSigma (fun n : ℕ => Fin n)).trans List.equivSigmaTuple.symm


/-- The ordered subtrees attached to the root. -/
def children (t : PlaneTree) : List PlaneTree := equivChildren t


/-- Bottom-up recursion: `fold g` applies `g` to the values already computed at the
children of the root, in child order. -/
def fold {β : Type*} (g : List β → β) : PlaneTree → β :=
  WType.elim β fun ⟨_, f⟩ => g (List.ofFn f)


/-- The number of children of the root. -/
def rootDegree (t : PlaneTree) : ℕ := t.children.length

end BGW.PlaneTree

namespace BGW.PlaneTree

open Classical

/-- Offspring count at a positive-index address; invalid addresses have count zero. -/
def offspringAt : PlaneTree → List ℕ → ℕ
  | t, [] => t.rootDegree
  | _, 0 :: _ => 0
  | t, (i + 1) :: u => ((t.children[i]?).map (fun s => offspringAt s u)).getD 0

open Classical

theorem canonical_offspringAt (t : PlaneTree) : LocallyFinite.Canonical t.offspringAt := by
  intro u j
  induction u generalizing t with
  | nil =>
    cases j with
    | zero =>
      intro _
      rfl
    | succ j =>
      intro hj
      have hn : ¬j < t.children.length := by
        intro hlt
        exact hj ⟨Nat.succ_le_succ (Nat.zero_le j), hlt⟩
      change ((t.children[j]?).map (fun s => s.rootDegree)).getD 0 = 0
      rw [List.getElem?_eq_none (Nat.le_of_not_gt hn)]
      rfl
  | cons i u ih =>
    cases i with
    | zero =>
      intro _
      rfl
    | succ i =>
      cases h : t.children[i]? with
      | none =>
        intro _
        change ((t.children[i]?).map (fun s => s.offspringAt (u ++ [j]))).getD 0 = 0
        rw [h]
        rfl
      | some s =>
        intro hj
        have heq : t.offspringAt ((i + 1) :: u) = s.offspringAt u := by
          change ((t.children[i]?).map (fun s => s.offspringAt u)).getD 0 = s.offspringAt u
          rw [h]
          rfl
        rw [heq] at hj
        change ((t.children[i]?).map (fun s => s.offspringAt (u ++ [j]))).getD 0 = 0
        rw [h]
        exact ih s hj

/-- View a finite plane tree as a canonical, possibly-infinite-tree value. -/
def toLocallyFinite (t : PlaneTree) : LocallyFinite.Tree :=
  ⟨t.offspringAt, t.canonical_offspringAt⟩

end BGW.PlaneTree

namespace BGW.PlaneTree


/-- Outdegrees in root-first depth-first order, counting every vertex occurrence. -/
def degrees : PlaneTree → List ℕ := fold fun ds => ds.length :: ds.flatten

end BGW.PlaneTree

namespace BGW.PlaneTree


/-- Number of vertices whose outdegree is `k`, counting every DFS occurrence. -/
def degreeCount (t : PlaneTree) (k : ℕ) : ℕ := t.degrees.count k

end BGW.PlaneTree

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
    (∀ lam : ℝ, 0 < lam →
      @MeasureTheory.integral ℝ ℝ _ (@NormedField.toNormedSpace ℝ Real.normedField) _ ν
        (fun y => Real.exp (-lam * y)) = Real.exp (lam ^ α)) ∧
    ∀ f : BoundedContinuousFunction ℝ ℝ,
      Tendsto (fun n : ℕ =>
        @MeasureTheory.integral ℝ ℝ _ (@NormedField.toNormedSpace ℝ Real.normedField) _
          ((walkLaw μ n).map (fun z : ℤ => (z : ℝ) / a n)) (fun x => f x))
        atTop (𝓝 (@MeasureTheory.integral ℝ ℝ _
          (@NormedField.toNormedSpace ℝ Real.normedField) _ ν (fun x => f x)))

end BGW.StableTrees

namespace BGW.StableTrees.Scalar

open Complex

/-- The characteristic function `θ ↦ exp((-iθ)^α)` of the limit law (principal power). -/
noncomputable def stableCF (α θ : ℝ) : ℂ := cexp ((-(θ * I)) ^ (α : ℂ))

end BGW.StableTrees.Scalar

namespace BGW.StableTrees.Scalar

open Complex

/-- The density `d_α` of the limit law `Y_α`, defined by Fourier inversion of its
characteristic function `exp((-iθ)^α)`. -/
noncomputable def stableDensity (α x : ℝ) : ℝ :=
  (1 / (2 * Real.pi)) * (∫ θ : ℝ, stableCF α θ * cexp (-(θ * x * I))).re

end BGW.StableTrees.Scalar

namespace BGWLeaves.StableAnalysis

open BGW BGW.StableTrees BGW.LocallyFinite

-- Keep the auxiliary matcher name used in its original, separate source module.
set_option bootstrap.genMatcherCode false in
/-- `n`-fold convolution power of a step law on `ℤ`; the empty sum is `δ₀`.
For `ν = stepLaw μ` this is `walkLaw μ` (`intWalk_stepLaw`). -/
noncomputable def intWalk (ν : Measure ℤ) : ℕ → Measure ℤ
  | 0 => Measure.dirac 0
  | m + 1 => (intWalk ν m).conv ν


/-- `P[W_n = k]` for the walk with step law `ν`. -/
noncomputable def intWalkProb (ν : Measure ℤ) (n : ℕ) (k : ℤ) : ℝ := (intWalk ν n).real {k}


/-- Mean and variance of a law on `ℤ`. -/
noncomputable def mean (ν : Measure ℤ) : ℝ := ∫ z, (z : ℝ) ∂ν


noncomputable def variance (ν : Measure ℤ) : ℝ := ∫ z, ((z : ℝ) - mean ν) ^ 2 ∂ν


/-- Definition 1.8: the law is lattice if its support lies in `b + dℤ` for some `d ≥ 2`.
On the countable space `ℤ`, "support contained in" is "almost surely in". -/
def IsLatticeLaw (ν : Measure ℤ) : Prop :=
  ∃ (b : ℤ) (d : ℕ), 2 ≤ d ∧ ∀ᵐ z ∂ν, (d : ℤ) ∣ z - b


/-- Aperiodicity of an offspring law: the support generates `ℤ` as an additive group. -/
def Aperiodic (μ : PMF ℕ) : Prop :=
  AddSubgroup.closure (((↑) : ℕ → ℤ) '' {j : ℕ | μ j ≠ 0}) = ⊤


/-- Right tail quantile `inf {x ≥ 0 : P[W₁ > x] ≤ 1/n}` of a step law. -/
noncomputable def tailQuantile (ν : Measure ℤ) (n : ℕ) : ℝ :=
  sInf {x : ℝ | 0 ≤ x ∧ ν.real {z : ℤ | x < (z : ℝ)} ≤ 1 / n}


/-- Truncated second moment `K(x) = E[W₁² 1_{|W₁| ≤ x}]`. -/
noncomputable def truncSecondMoment (ν : Measure ℤ) (x : ℝ) : ℝ :=
  ∫ z in {z : ℤ | |(z : ℝ)| ≤ x}, (z : ℝ) ^ 2 ∂ν


/-- `sup {z ≥ 0 : K(z)/z² ≥ 1/n}` (`sSup ∅ = 0` as in the printed convention;
at `z = 0` Lean's `K 0 / 0 = 0 < 1/n`, so `0` is not in the set for `n ≥ 1`). -/
noncomputable def gaussQuantile (ν : Measure ℤ) (n : ℕ) : ℝ :=
  sSup {z : ℝ | 0 ≤ z ∧ 1 / (n : ℝ) ≤ truncSecondMoment ν z / z ^ 2}

-- Match the auxiliary proof names from the original, separate source module.
-- This clears only Lean's elaboration cache, without changing declarations.
run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.modifyState env fun _ => {}

open Classical

/-- The **corrected** norming `a_n` of Theorem 1.10, for Laplace exponent `u ^ θ`:
`σ √(n/2)` if the variance is finite; `(-Γ(1-θ))^{1/θ} · inf{x : P[W₁>x] ≤ 1/n}` if the variance
is infinite and `θ < 2`; `√(n K(z_n) / 2)` (note the factor `1/2`) if the variance is
infinite and `θ = 2`. -/
noncomputable def norming (ν : Measure ℤ) (θ : ℝ) (n : ℕ) : ℝ :=
  if Integrable (fun z : ℤ => (z : ℝ) ^ 2) ν then Real.sqrt (variance ν) * Real.sqrt (n / 2)
  else if θ < 2 then (-Real.Gamma (1 - θ)) ^ (1 / θ) * tailQuantile ν n
  else Real.sqrt (n * truncSecondMoment ν (gaussQuantile ν n) / 2)


/-- Weak convergence of `(W_n - n m) / a_n` to the law `X_1` with Laplace transform
`exp(λ^θ)`; `a_n > 0` **eventually** (the explicit quantile norming vanishes at small `n`).  This is the **definition** of the domain of
attraction with centering `n m`, normalized to the spectrally positive law of 1.10.
For `ν = stepLaw μ` and `m = 0` it is `StableDomain μ θ a` without monotonicity. -/
structure IsStableAttracted (ν : Measure ℤ) (θ m : ℝ) (a : ℕ → ℝ) : Prop where
  alpha_mem : 1 < θ ∧ θ ≤ 2
  pos : ∃ N : ℕ, ∀ n : ℕ, N ≤ n → 0 < a n
  converges : ∃ X : Measure ℝ, IsProbabilityMeasure X ∧
    (∀ lam : ℝ, 0 < lam → ∫ y, Real.exp (-lam * y) ∂X = Real.exp (lam ^ θ)) ∧
    ∀ f : BoundedContinuousFunction ℝ ℝ,
      Tendsto (fun n : ℕ => ∫ x, f x ∂((intWalk ν n).map (fun z : ℤ => ((z : ℝ) - n * m) / a n)))
        atTop (𝓝 (∫ x, f x ∂X))

end BGWLeaves.StableAnalysis

namespace BGWLeaves

open BGW BGW.StableTrees BGW.LocallyFinite
open BGWLeaves.StableAnalysis

/-- The event of `LocallyFinite.Tree` that the tree is finite, equal to `t.toLocallyFinite` for a
finite plane tree `t` with `Q t`. -/
def finiteTreeEvent (Q : PlaneTree → Prop) : Set LocallyFinite.Tree :=
  {T | ∃ t : PlaneTree, t.toLocallyFinite = T ∧ Q t}

end BGWLeaves

namespace BGWLeaves

open BGW BGW.StableTrees BGW.LocallyFinite
open BGWLeaves.StableAnalysis

/-- The integers whose gcd is the arithmetic factor: the offspring numbers `k ∈ supp μ ∩ A`
and the shifted offspring numbers `k - 1` for `k ∈ supp μ ∖ A`. -/
def arithSet (μ : PMF ℕ) (A : Set ℕ) : Set ℤ :=
  {s | ∃ k : ℕ, μ k ≠ 0 ∧ ((k ∈ A ∧ s = (k : ℤ)) ∨ (k ∉ A ∧ s = (k : ℤ) - 1))}


/-- The largest positive integer dividing every element of `arithSet μ A` (the gcd). It is
positive and finite as soon as `arithSet` contains a nonzero integer, which holds for a critical
`μ` with `μ 1 ≠ 1` (see `arithFactor_isGreatest`). -/
noncomputable def arithFactor (μ : PMF ℕ) (A : Set ℕ) : ℕ :=
  sSup {e : ℕ | 1 ≤ e ∧ ∀ s ∈ arithSet μ A, (e : ℤ) ∣ s}


/-- `ζ_A(τ)`: the number of vertices `u` of `τ` whose offspring number lies in `A`, as an
extended natural number (infinite trees may have `ζ_A = ∞`). -/
noncomputable def zetaA (A : Set ℕ) (T : Tree) : ℕ∞ :=
  {u : Address | Present T u ∧ T.val u ∈ A}.encard

end BGWLeaves

namespace BGWLeaves

open BGW BGW.StableTrees BGW.LocallyFinite
open BGWLeaves.StableAnalysis

/-- `{λ(τ) = m}` (Theorem 3.1, Corollary 3.3): the tree is finite and has exactly `m` leaves
(vertices of outdegree `0`; `λ(τ) = t.degreeCount 0`).  Infinite trees never belong to it. -/
def leafCountEvent (m : ℕ) : Set LocallyFinite.Tree :=
  finiteTreeEvent fun t => t.degreeCount 0 = m


/-- `P_μ[λ(τ) = m]` (the `Prmu{lt = m}` of Theorem 3.1): the probability that a `GW_μ` tree has
exactly `m` leaves. -/
noncomputable def leafProb (μ : PMF ℕ) (m : ℕ) : ℝ :=
  (bienaymeLaw μ.toMeasure).real (leafCountEvent m)


/-- The slowly varying function `h` of Theorem 3.1 (`B_n = h(n) n^{1/θ}`, introduced before
Lemma 1.11 of the paper): `h(x) = B_{⌊x⌋} / x^{1/θ}` with `B_n = norming (stepLaw μ) θ n` (the
corrected norming).  That it is slowly varying is `hSlow_slowlyVarying`. -/
noncomputable def hSlow (μ : PMF ℕ) (θ : ℝ) : ℝ → ℝ :=
  fun x => norming (stepLaw μ) θ ⌊x⌋₊ / x ^ (1 / θ)


/-- The pair `(d, b)` of Theorem 3.1 (line 864): `d ≥ 1` is the **largest** integer such that
`supp μ ∖ {0} ⊂ b + dℤ` for some `b ∈ ℕ`, and then `b` is the **least** natural number with
`supp μ ∖ {0} ⊂ b + dℤ`.  It is a property, not a definition by choice: the pair exists exactly when
`supp μ ∖ {0}` has at least two points (otherwise there is no largest `d`), see
`exists_isSuppSpan`, and it is then unique (`isSuppSpan_unique`).  Equivalently: `IsSuppSpan μ d b`
holds iff `d` is the gcd of the differences of the points of `supp μ ∖ {0}` and `b` is the residue of
any of them modulo `d`. -/
def IsSuppSpan (μ : PMF ℕ) (d b : ℕ) : Prop :=
  1 ≤ d ∧
  (∀ k : ℕ, μ k ≠ 0 → k ≠ 0 → (d : ℤ) ∣ (k : ℤ) - b) ∧
  (∀ d' : ℕ, 1 ≤ d' → (∃ b' : ℕ, ∀ k : ℕ, μ k ≠ 0 → k ≠ 0 → (d' : ℤ) ∣ (k : ℤ) - b') → d' ≤ d) ∧
  (∀ b' : ℕ, (∀ k : ℕ, μ k ≠ 0 → k ≠ 0 → (d : ℤ) ∣ (k : ℤ) - b') → b ≤ b')

end BGWLeaves

namespace BGWLeaves

open BGW BGW.StableTrees BGW.LocallyFinite
open BGWLeaves.StableAnalysis

/-- `P_μ[ζ_A = n]`, so that the statements of `BGWLeaves.GeneralAInf` stay readable. -/
noncomputable abbrev zetaAProb (μ : PMF ℕ) (A : Set ℕ) (n : ℕ) : ℝ :=
  (bienaymeLaw μ.toMeasure).real {T | zetaA A T = (n : ℕ∞)}

end BGWLeaves

namespace BGWLeaves

open BGW BGW.StableTrees BGW.LocallyFinite
open BGWLeaves.StableAnalysis

/-- `Δ(τ) = max{k_u ; u ∈ τ}`, the maximum number of children (`PlaneTree.degrees` lists all
outdegrees). -/
def maxDegree (t : PlaneTree) : ℕ := t.degrees.foldr max 0

end BGWLeaves

namespace BGWLeaves

open BGW BGW.StableTrees BGW.LocallyFinite
open BGWLeaves.StableAnalysis

-- Spell the development's supremum instance path; this is the same supremum.
local notation "radiusSupSet" =>
  @ConditionallyCompletePartialOrderSup.toSupSet ℝ≥0∞
    (@ConditionallyCompletePartialOrder.toConditionallyCompletePartialOrderSup ℝ≥0∞
      (@ConditionallyCompleteLattice.toConditionallyCompletePartialOrder ℝ≥0∞
        (@ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice ℝ≥0∞
          (@ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder ℝ≥0∞
            (@CompleteLinearOrder.toConditionallyCompleteLinearOrderBot ℝ≥0∞ ENNReal.instCompleteLinearOrder)))))

/-- The radius of convergence `R ∈ [0, ∞]` of `∑ μ(i) z^i`: the supremum of the `r ≥ 0` for which
`∑ μ(i) r^i` converges (the definition; no Cauchy-Hadamard is used). -/
noncomputable def genFunRadius (μ : PMF ℕ) : ℝ≥0∞ :=
  @iSup ℝ≥0∞ ℝ≥0 radiusSupSet fun r =>
    @iSup ℝ≥0∞ (Summable fun n : ℕ => (μ n).toReal * (r : ℝ) ^ n) radiusSupSet
      fun _ => (r : ℝ≥0∞)


/-- **Hypothesis `𝓗`** of Section 7: `ν` is critical, aperiodic, of finite variance, with `R > 1`, and
if `R < ∞` then `ν(n)^{1/n} → 1/R`, while if `R = ∞` there is `N` with `(ν(k)^{1/k})_{k ≥ N}` decreasing.
Spelled out (as `(H_θ)` in `BGWLeaves.LeafConcentration` and `BGWLeaves.LeafMass`): `IsCritical`, `μ 1 ≠ 1` (part (i) of `(H_θ)`: "`μ(1) < 1`"),
`Aperiodic`, finite variance (`MemLp (fun j => j) 2`, the form of `HthetaTail`), then the two clauses on `R`.
"Decreasing" is read as non-increasing (`AntitoneOn`); this is the weaker reading, which includes laws with bounded
support (`ν(k) = 0` eventually), and it makes the theorem stronger.  `finiteVariance` is redundant under
`radius_gt_one` (printed), and `nondegenerate` is not part of the printed `𝓗` but of `(H_θ)(i)`. -/
structure HypH (μ : PMF ℕ) : Prop where
  critical : IsCritical μ
  nondegenerate : μ 1 ≠ 1
  aperiodic : Aperiodic μ
  finiteVariance : MemLp (fun j : ℕ => (j : ℝ)) 2 μ.toMeasure
  radius_gt_one : 1 < genFunRadius μ
  root_limit : genFunRadius μ < ⊤ →
    Tendsto (fun n : ℕ => (μ n).toReal ^ (1 / (n : ℝ))) atTop (𝓝 ((genFunRadius μ).toReal)⁻¹)
  root_antitone : genFunRadius μ = ⊤ →
    ∃ N : ℕ, AntitoneOn (fun k : ℕ => (μ k).toReal ^ (1 / (k : ℝ))) (Set.Ici N)


/-- `μ([x, ∞))` for a real threshold `x` (`{k : ℕ | x ≤ k}`); this is the paper's `μ([x,∞))`,
e.g. `μ([(1 - ε) D(n), ∞))`. -/
noncomputable def offTail (μ : PMF ℕ) (x : ℝ) : ℝ := (μ.toMeasure {k : ℕ | x ≤ (k : ℝ)}).toReal


/-- `D(n) = max {k ≥ 1 ; μ([k,∞)) ≥ 1/n}` (`sSup` in `ℕ`).  The set is nonempty and bounded for
`n ≥ 1/(1 - μ₀)` (see `bigD_spec`); for smaller `n` the value is the junk `0`. -/
noncomputable def bigD (μ : PMF ℕ) (n : ℕ) : ℕ :=
  sSup {k : ℕ | 1 ≤ k ∧ 1 / (n : ℝ) ≤ offTail μ k}

end BGWLeaves

namespace BGWLeaves.StableAnalysis

open BGW BGW.StableTrees BGW.LocallyFinite
variable (ν : Measure ℤ) [IsProbabilityMeasure ν] {θ : ℝ}

/-- 1.10(i): `(W_n - n E W₁) / a_n → X₁`, with `a_n = norming ν θ n`. -/
theorem locallimit_i (hstep : ν {z | z < -1} = 0) (hint : Integrable (fun z : ℤ => (z : ℝ)) ν)
    (hDA : ∃ b, IsStableAttracted ν θ (mean ν) b) :
    IsStableAttracted ν θ (mean ν) (norming ν θ) := by
  sorry


/-- 1.10(ii): `a_n` is nondecreasing and `a_n = n^{1/θ} L(n)` with `L` slowly varying. -/
theorem locallimit_ii (hstep : ν {z | z < -1} = 0) (hint : Integrable (fun z : ℤ => (z : ℝ)) ν)
    (hDA : ∃ b, IsStableAttracted ν θ (mean ν) b) :
    Monotone (norming ν θ) ∧
      SlowlyVarying (fun x : ℝ => norming ν θ ⌊x⌋₊ / x ^ (1 / θ)) := by
  sorry

end BGWLeaves.StableAnalysis

namespace BGWLeaves.StableAnalysis

open BGW BGW.StableTrees BGW.LocallyFinite
variable (ν : Measure ℤ) [IsProbabilityMeasure ν] {θ : ℝ}

/-- 1.10(iii) with the corrected norming. -/
theorem locallimit_iii (hstep : ν {z | z < -1} = 0) (hint : Integrable (fun z : ℤ => (z : ℝ)) ν)
    (hnl : ¬ IsLatticeLaw ν) (hDA : ∃ b, IsStableAttracted ν θ (mean ν) b) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ k : ℤ,
      |norming ν θ n * intWalkProb ν n k -
          Scalar.stableDensity θ (((k : ℝ) - n * mean ν) / norming ν θ n)| ≤ ε := by
  sorry

end BGWLeaves.StableAnalysis

namespace BGWLeaves

open BGW BGW.StableTrees BGW.LocallyFinite
open BGWLeaves.StableAnalysis

/-- **Theorem 3.1(i)** as printed (line 868), under `(H_θ)`: for the pair
`(d, b)` of `IsSuppSpan` (`d` the largest integer and `b` the least natural number with
`supp μ ∖ {0} ⊂ b + dℤ`), there is `N` such that for every `n ≥ N`, `P_μ[λ = n+1] > 0` iff
`gcd(b-1,d) ∣ n`.  Assembled from `ltn_i_arith` and `int_gcd_eq_arithFactor`; the hypotheses `hDA`,
`hap` (those of `(H_θ)`) are not used. -/
theorem thm_ltn_i {μ : PMF ℕ} {θ : ℝ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hDA : ∃ a, StableDomain μ θ a) (hap : Aperiodic μ) {d b : ℕ} (hdb : IsSuppSpan μ d b) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → (0 < leafProb μ (n + 1) ↔ Int.gcd ((b : ℤ) - 1) (d : ℤ) ∣ n) := by
  sorry


/-- **Theorem 3.1(ii)** as printed (line 870), under `(H_θ)`:
`P_μ[λ = n+1] ∼ μ₀^{1/θ} p₁(0) gcd(b-1,d) / (h(n) n^{1/θ+1})` as `n → ∞` in the multiples of
`gcd(b-1,d)`, for the pair `(d, b)` of `IsSuppSpan`, with `h = hSlow μ θ` (the slowly varying
function with `B_n = h(n) n^{1/θ}`, `hSlow_slowlyVarying`) and `p₁ = Scalar.stableDensity θ`.
Equivalent to `ltn_ii_tendsto` (via `int_gcd_eq_arithFactor`, `p₁(0) > 0` and
`h(n) n^{1/θ+1} = n B_n`). -/
theorem thm_ltn_ii {μ : PMF ℕ} {θ : ℝ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hap : Aperiodic μ) (hDA : ∃ a, StableDomain μ θ a) {d b : ℕ} (hdb : IsSuppSpan μ d b) :
    (fun n : ℕ => leafProb μ (n + 1)) ~[atTop ⊓ 𝓟 {n : ℕ | Int.gcd ((b : ℤ) - 1) (d : ℤ) ∣ n}]
      (fun n : ℕ => (μ 0).toReal ^ (1 / θ) * Scalar.stableDensity θ 0 *
        (Int.gcd ((b : ℤ) - 1) (d : ℤ) : ℝ) / (hSlow μ θ n * (n : ℝ) ^ (1 / θ + 1))) := by
  sorry

end BGWLeaves

namespace BGWLeaves

open BGW BGW.StableTrees BGW.LocallyFinite
open BGWLeaves.StableAnalysis

/-- **Theorem 8.1(I), CORRECTED, general form.**  This is the corrected statement of
Theorem 8.1(I) (`thm:general`, lines 2494-2503): it REPLACES the printed constant
`μ(A)^{1/θ} p₁(0) gcd(b-1,d) / (h(n) n^{1/θ+1})` (false in general, correction 5 of `FORMALIZATION_REPORT.md`;
also false for infinite variance) by
`n B_n P_μ[ζ_A = n] → μ(A)^{1/θ} p₁(0) e` along `n = e j + 1`, with `e = arithFactor μ A =
gcd((supp μ ∩ A) ∪ {k - 1 : k ∈ supp μ ∖ A})` and `B_n = norming (stepLaw μ) θ n` the corrected norming
(`h(n) n^{1/θ} = B_n`, see `thm81_printed_form`); and `P_μ[ζ_A = n] = 0` for `n ≢ 1 (mod e)` (this half
holds for every critical `μ`, `MarkedLaw.zetaA_eq_zero_of_not_dvd`).

**The corrected statement formalized here REPLACES the printed `gcd(b-1,d)/(h(n) n^{1/θ+1})` of Theorem 8.1(I)**
(the printed factor is false in general; the printed claim is not proved).

**This statement is STRONGER than the printed theorem**:
(a) NO finiteness hypothesis on `A` (printed: "`A` finite or `ℕ∖A` finite" when `σ² = ∞`); (b) NO aperiodicity
(`(H_θ)(iii)`, which the finite-variance theorem also does not use); (c) all variances at once (finite variance is
the case `θ = 2`, `B_n = σ√(n/2)`).  The A-time-walk proof uses only `hc, hne, hDA`.  The three statements
`thm81_infiniteVariance_A_finite`, `thm81_infiniteVariance_A_cofinite` and `thm81_corrected` carry the printed
hypotheses (`hap` unused) and are the COVERED statements of the printed Theorem 8.1(I); they are proved from this one.

Hypotheses.  `hc, hne, hDA` are `(H_θ)(i),(ii)` (`StableDomain` includes the two); `hA` is `μ(A) > 0`
(printed: `A ≠ ∅`; for `μ(A) = 0` see `zetaA_eq_zero_of_measure_zero`); `p₁(0) = 1/|Γ(-1/θ)|`. -/
theorem thm81_corrected_general {μ : PMF ℕ} {θ : ℝ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hDA : ∃ a, StableDomain μ θ a) {A : Set ℕ} (hA : μ.toMeasure A ≠ 0) :
    (∀ n : ℕ, ¬ ((arithFactor μ A : ℤ) ∣ (n : ℤ) - 1) →
        bienaymeLaw μ.toMeasure {T | zetaA A T = n} = 0) ∧
    Tendsto (fun j : ℕ =>
        ((arithFactor μ A * j + 1 : ℕ) : ℝ) * norming (stepLaw μ) θ (arithFactor μ A * j + 1) *
          zetaAProb μ A (arithFactor μ A * j + 1))
      atTop
      (𝓝 ((μ.toMeasure A).toReal ^ (1 / θ) * Scalar.stableDensity θ 0 * (arithFactor μ A : ℝ))) := by
  sorry

end BGWLeaves

namespace BGWLeaves

open BGW BGW.StableTrees BGW.LocallyFinite
open BGWLeaves.StableAnalysis

/-- **Theorem 7.1(ii)** (`thm:max`), finite variance and `𝓗`, AT THE PRINTED STRENGTH (no `hnl`): for every `ε > 0`
and `δ > 0` there is `N` such that for all `n ≥ N` with `P_μ[λ(τ) = n] > 0`,
`P[(1-ε) D(n) ≤ Δ(τ_n) ≤ (1+ε) D(n)] ≥ 1 - δ` (this is the printed "`→ 1`" along the `n` for which `τ_n` is
defined; `τ_n ∼ P_μ[· | λ = n]`).  The printed hypotheses: `(H_θ)` with `σ² < ∞`, and `𝓗`; the Lean hypothesis is
`HypH μ` (= `(H_2)` + `𝓗`, `HypH.hthetaTail`, plus `μ 1 ≠ 1` from `(H_θ)(i)`).

`hnl` is deliberately NOT a hypothesis (it would silently drop the lattice laws of bounded support, a
specialisation of the printed claim).  Proof, a case split on the support (`tendsto_bigD_atTop_iff`):
* unbounded support: `HypH` implies `hnl` (`HypH.not_isLatticeLaw_etaLaw_of_unbounded`), and the two principles
  `maxDegree_lower_principle` (`p_n = (1-ε) D(n) - 1`, `MM_lower_limit`) and `maxDegree_upper_principle`
  (`q_n = (1+ε) D(n) - 1`, `MM_upper_limit`) give `P[Δ < (1-ε)D] → 0` and `P[Δ > (1+ε)D] → 0`;
* bounded support: `thm_max_ii_of_bounded`.
This is proved here from those statements. -/
theorem thm_max_ii {μ : PMF ℕ} (h : HypH μ) {ε : ℝ} (hε : 0 < ε) {δ : ℝ} (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → leafProb μ n ≠ 0 →
      1 - δ ≤ ((bienaymeLaw μ.toMeasure)[|leafCountEvent n]).real
        (finiteTreeEvent fun t =>
          (1 - ε) * (bigD μ n : ℝ) ≤ (maxDegree t : ℝ) ∧ (maxDegree t : ℝ) ≤ (1 + ε) * (bigD μ n : ℝ)) := by
  sorry

end BGWLeaves
