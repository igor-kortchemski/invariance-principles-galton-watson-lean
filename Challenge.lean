/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import Mathlib

/-!
# Invariance principles for Galton–Watson trees conditioned on the number of leaves

arXiv:1110.2163v4: corrected 1.10(i–iii), 3.1(i–ii), 7.1(ii), corrected 8.1(I),
Introduction (II) including lattice laws, and 8.1(II). The functional limits are
JOINT on D(J1) × C(uniform) × C(uniform): the excursion and height are coupled,
and the two height coordinates coincide. The mathematical objects are concrete.
Two construction holes supply evaluation and metric-space instances, constrained
by `coe_mk` and `dist_eq_j1Dist`; they cannot change evaluation or the J1 topology.
Auxiliary theorem targets carry construction proofs in Solution. Solution never
imports Challenge. See README.md for corrections, hypotheses and proof routes.
-/

@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 10000
set_option linter.auxLemma false
set_option linter.unusedVariables false
open MeasureTheory ProbabilityTheory Filter Set Topology Asymptotics Complex
open scoped ENNReal NNReal Topology Classical

-- These spellings preserve the development's instance paths, without changing values.
local infix:50 " ≤ᵣ " => @LE.le ℝ (@Preorder.toLE ℝ Real.instPreorder)
local infix:50 " <ᵣ " => @LT.lt ℝ (@Preorder.toLT ℝ (@PartialOrder.toPreorder ℝ Real.partialOrder))
macro "twoReal[" h:term "]" : term =>
  `(@OfNat.ofNat ℝ (nat_lit 2) (@instOfNatAtLeastTwo ℝ (nat_lit 2) Real.instNatCast $h))
local notation "zeroRField" => @OfNat.ofNat ℝ (nat_lit 0) (@Zero.toOfNat0 ℝ
  Real.instField.toSemifield.toDivisionSemiring.toGroupWithZero.toMonoidWithZero.toMulZeroOneClass.toMulZeroClass.toZero)
local notation "zeroRSemiring" => @OfNat.ofNat ℝ (nat_lit 0) (@Zero.toOfNat0 ℝ
  (@MulZeroClass.toZero ℝ (@instMulZeroClassOfSemiring ℝ Real.semiring)))
local notation "invRField" => @Inv.inv ℝ Real.instField.toSemifield.toDivisionSemiring.toGroupWithZero.toDivisionMonoid.toDivInvOneMonoid.toInvOneClass.toInv
local notation "mulRSemiring" => @HMul.hMul ℝ ℝ ℝ (@instHMul ℝ (@MulZeroClass.toMul ℝ (@instMulZeroClassOfSemiring ℝ Real.semiring)))
local notation "coeNNSemiring" => @Subtype.val ℝ (fun x => @LE.le ℝ (@Preorder.toLE ℝ (@PartialOrder.toPreorder ℝ Real.partialOrder)) zeroRSemiring x)
syntax "forallRealAE[" term "]" ident " in " term ", " term : term
macro_rules
  | `(forallRealAE[$h] $s:ident in $m, $p) =>
    `(@Filter.Eventually ℝ (fun $s : ℝ => $p)
      (@MeasureTheory.ae ℝ (@MeasureTheory.Measure ℝ (@MeasureTheory.MeasureSpace.toMeasurableSpace ℝ Real.measureSpace))
        (@MeasureTheory.Measure.instFunLike ℝ (@MeasureTheory.MeasureSpace.toMeasurableSpace ℝ Real.measureSpace)) $h $m))

namespace BGW.LocallyFinite
end BGW.LocallyFinite
namespace BGW.Skorokhod
end BGW.Skorokhod
namespace BGW.Probability.RealWalk
end BGW.Probability.RealWalk
namespace BGW.StableTrees
end BGW.StableTrees
namespace BGWLeaves.StableAnalysis
end BGWLeaves.StableAnalysis
open BGW BGW.LocallyFinite BGW.Skorokhod BGW.StableTrees
open BGW.Probability.RealWalk BGWLeaves.StableAnalysis BGWLeaves
local notation "unitHorizons" => (fun n => @HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (@Nat.cast Real Real.instNatCast n) (@OfNat.ofNat Real (nat_lit 1) (@One.toOfNat1 Real Real.instOne)))
/-! ## Scalar attraction and norming -/
set_option bootstrap.genMatcherCode false in
/-- `n`-fold convolution power of a step law on `ℤ`; the empty sum is `δ₀`. For `ν = stepLaw μ` this is `walkLaw μ`
(`intWalk_stepLaw`). -/
noncomputable def BGWLeaves.StableAnalysis.intWalk (ν : Measure ℤ) : ℕ → Measure ℤ
  | 0 => Measure.dirac 0
  | m + 1 => (BGWLeaves.StableAnalysis.intWalk ν m).conv ν
namespace BGWLeaves.StableAnalysis
/-- Centered scalar attraction to a law with Laplace transform `exp(λ^θ)`. The normalizer is eventually positive;
neither monotonicity nor centering by a moment is required here. -/
structure IsStableAttracted (ν : Measure ℤ) (θ m : ℝ) (a : ℕ → ℝ) : Prop where
  alpha_mem : 1 < θ ∧ θ ≤ 2
  pos : ∃ N : ℕ, ∀ n : ℕ, N ≤ n → 0 < a n
  converges : ∃ X : Measure ℝ, IsProbabilityMeasure X ∧
    (∀ lam : ℝ, 0 < lam → ∫ y, Real.exp (-lam * y) ∂X = Real.exp (lam ^ θ)) ∧
    ∀ f : BoundedContinuousFunction ℝ ℝ,
      Tendsto (fun n : ℕ => ∫ x, f x ∂((intWalk ν n).map (fun z : ℤ => ((z : ℝ) - n * m) / a n)))
        atTop (𝓝 (∫ x, f x ∂X))
end BGWLeaves.StableAnalysis
/-- Mean and variance of a law on `ℤ`. -/
noncomputable def BGWLeaves.StableAnalysis.mean (ν : Measure ℤ) : ℝ := ∫ (z : ℤ), (↑z : ℝ) ∂ν
/-- The centered second moment of the integer step law. -/
noncomputable def BGWLeaves.StableAnalysis.variance (ν : Measure ℤ) : ℝ := ∫ (z : ℤ), ((↑z : ℝ) - mean ν) ^ (2 : ℕ) ∂ν
theorem BGWLeaves.StableAnalysis.norming._proof_1 : ((1 : ℕ) + (1 : ℕ)).AtLeastTwo := by sorry
/-- Right tail quantile `inf {x ≥ 0 : P[W₁ > x] ≤ 1/n}` of a step law. -/
noncomputable def BGWLeaves.StableAnalysis.tailQuantile (ν : Measure ℤ) (n : ℕ) : ℝ :=
  sInf {x : ℝ | (0 : ℝ) ≤ x ∧ ν.real {z : ℤ | x < (↑z : ℝ)} ≤ (1 : ℝ) / (↑n : ℝ)}
/-- Truncated second moment `K(x) = E[W₁² 1_{|W₁| ≤ x}]`. -/
noncomputable def BGWLeaves.StableAnalysis.truncSecondMoment (ν : Measure ℤ) (x : ℝ) : ℝ :=
  ∫ (z : ℤ) in {z : ℤ | |(↑z : ℝ)| ≤ x}, (↑z : ℝ) ^ (2 : ℕ) ∂ν
/-- `sup {z ≥ 0 : K(z)/z² ≥ 1/n}` (`sSup ∅ = 0` as in the printed convention; at `z = 0` Lean's `K 0 / 0 = 0 < 1/n`, so
`0` is not in the set for `n ≥ 1`). -/
noncomputable def BGWLeaves.StableAnalysis.gaussQuantile (ν : Measure ℤ) (n : ℕ) : ℝ :=
  sSup {z : ℝ | (0 : ℝ) ≤ z ∧ (1 : ℝ) / (↑n : ℝ) ≤ truncSecondMoment ν z / z ^ (2 : ℕ)}
/-- The **corrected** norming `a_n` of Theorem 1.10, for Laplace exponent `u ^ θ`: `σ √(n/2)` if the variance is finite;
`(-Γ(1-θ))^{1/θ} · inf{x : P[W₁>x] ≤ 1/n}` if the variance is infinite and `θ < 2`; `√(n K(z_n) / 2)` (note the factor
`1/2`) if the variance is infinite and `θ = 2`. -/
noncomputable def BGWLeaves.StableAnalysis.norming (ν : Measure ℤ) (θ : ℝ) (n : ℕ) : ℝ :=
  if Integrable (fun (z : ℤ) => (↑z : ℝ) ^ (2 : ℕ)) ν then √(BGWLeaves.StableAnalysis.variance ν) * √((↑n : ℝ) / twoReal[BGWLeaves.StableAnalysis.norming._proof_1])
  else
    if θ < twoReal[BGWLeaves.StableAnalysis.norming._proof_1] then (-Real.Gamma ((1 : ℝ) - θ)) ^ ((1 : ℝ) / θ) * tailQuantile ν n
    else √((↑n : ℝ) * truncSecondMoment ν (gaussQuantile ν n) / twoReal[BGWLeaves.StableAnalysis.norming._proof_1])
namespace BGWLeaves.StableAnalysis
variable (ν : Measure ℤ) [IsProbabilityMeasure ν] {θ : ℝ}
/-- Theorem 1.10(i): scalar stable convergence with the corrected explicit normalizer. -/
theorem locallimit_i (hstep : ν {z | z < -1} = 0) (hint : Integrable (fun z : ℤ => (z : ℝ)) ν)
    (hDA : ∃ b, IsStableAttracted ν θ (mean ν) b) :
    IsStableAttracted ν θ (mean ν) (norming ν θ) := by sorry
end BGWLeaves.StableAnalysis
/-- Ratio slow variation at infinity. Positivity and measurability are not part of this predicate; applications retain
the needed hypotheses explicitly. -/
noncomputable def BGW.StableTrees.SlowlyVarying (ℓ : ℝ → ℝ) : Prop :=
  ∀ (a : ℝ), (0 : ℝ) < a → Tendsto (fun (x : ℝ) => ℓ (a * x) / ℓ x) atTop (𝓝 (1 : ℝ))
namespace BGWLeaves.StableAnalysis
variable (ν : Measure ℤ) [IsProbabilityMeasure ν] {θ : ℝ}
/-- Theorem 1.10(ii): monotonicity and regular variation of that normalizer. -/
theorem locallimit_ii (hstep : ν {z | z < -1} = 0) (hint : Integrable (fun z : ℤ => (z : ℝ)) ν)
    (hDA : ∃ b, IsStableAttracted ν θ (mean ν) b) :
    Monotone (norming ν θ) ∧
      SlowlyVarying (fun x : ℝ => norming ν θ ⌊x⌋₊ / x ^ (1 / θ)) := by sorry
end BGWLeaves.StableAnalysis
/-- Definition 1.8: the law is lattice if its support lies in `b + dℤ` for some `d ≥ 2`. On the countable space `ℤ`,
"support contained in" is "almost surely in". -/
noncomputable def BGWLeaves.StableAnalysis.IsLatticeLaw (ν : Measure ℤ) : Prop :=
  ∃ (b : ℤ) (d : ℕ), (2 : ℕ) ≤ d ∧ ∀ᵐ (z : ℤ) ∂ν, (↑d : ℤ) ∣ z - b
/-- `P[W_n = k]` for the walk with step law `ν`. -/
noncomputable def BGWLeaves.StableAnalysis.intWalkProb (ν : Measure ℤ) (n : ℕ) (k : ℤ) : ℝ := (intWalk ν n).real {k}
theorem BGW.StableTrees.Scalar.stableDensity._proof_1 : ((1 : ℕ) + (1 : ℕ)).AtLeastTwo := by sorry
/-- The characteristic function `θ ↦ exp((-iθ)^α)` of the limit law (principal power). -/
noncomputable def BGW.StableTrees.Scalar.stableCF (α : ℝ) (θ : ℝ) : ℂ := cexp ((-((↑θ : ℂ) * I)) ^ (↑α : ℂ))
/-- The density `d_α` of the limit law `Y_α`, defined by Fourier inversion of its characteristic function
`exp((-iθ)^α)`. -/
noncomputable def BGW.StableTrees.Scalar.stableDensity (α : ℝ) (x : ℝ) : ℝ :=
  (1 : ℝ) / (twoReal[BGW.StableTrees.Scalar.stableDensity._proof_1] * Real.pi) * (∫ (θ : ℝ), Scalar.stableCF α θ * cexp (-((↑θ : ℂ) * (↑x : ℂ) * I))).re
namespace BGWLeaves.StableAnalysis
variable (ν : Measure ℤ) [IsProbabilityMeasure ν] {θ : ℝ}
/-- Theorem 1.10(iii): the uniform local limit estimate for non-lattice step laws. -/
theorem locallimit_iii (hstep : ν {z | z < -1} = 0) (hint : Integrable (fun z : ℤ => (z : ℝ)) ν)
    (hnl : ¬ IsLatticeLaw ν) (hDA : ∃ b, IsStableAttracted ν θ (mean ν) b) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ k : ℤ,
      |norming ν θ n * intWalkProb ν n k -
          Scalar.stableDensity θ (((k : ℝ) - n * mean ν) / norming ν θ n)| ≤ ε := by sorry
end BGWLeaves.StableAnalysis
/-- The offspring mean is one, including finiteness of the mean. -/
noncomputable def BGW.StableTrees.IsCritical (μ : PMF ℕ) : Prop := ∑' j : ℕ, (j : ℝ≥0∞) * μ j = 1
/-- The law of one increment `X = K - 1`. -/
noncomputable def BGW.StableTrees.stepLaw (μ : PMF ℕ) : Measure ℤ := Measure.map (fun (k : ℕ) => (↑k : ℤ) - (1 : ℤ)) μ.toMeasure
/-- The law of the sum of `n` independent increments; the empty sum is zero. -/
noncomputable def BGW.StableTrees.walkLaw (μ : PMF ℕ) : ℕ → Measure ℤ
  | 0 => Measure.dirac 0
  | m + 1 => (BGW.StableTrees.walkLaw μ m).conv (stepLaw μ)
namespace BGW.StableTrees
/-- Normalized scalar attraction to a spectrally positive stable law with Laplace exponent `λ ^ α`. The limit law is an
existence hypothesis here. The normalizer is nondecreasing and positive for `n ≥ 1`. -/
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
/-- Aperiodicity of an offspring law: the support generates `ℤ` as an additive group. -/
noncomputable def BGWLeaves.StableAnalysis.Aperiodic (μ : PMF ℕ) : Prop := AddSubgroup.closure (((↑) : ℕ → ℤ) '' {j : ℕ | μ j ≠ 0}) = ⊤
/-- Maximal positive span `d` and least natural residue `b` for `supp μ ∖ {0} ⊆ b+dℤ`. A singleton support has no
maximal span; when a span exists, `d` is the gcd of support differences. -/
noncomputable def BGWLeaves.IsSuppSpan (μ : PMF ℕ) (d : ℕ) (b : ℕ) : Prop :=
  (1 : ℕ) ≤ d ∧
    (∀ (k : ℕ), (μ : ℕ → ℝ≥0∞) k ≠ (0 : ℝ≥0∞) → k ≠ (0 : ℕ) → (↑d : ℤ) ∣ (↑k : ℤ) - (↑b : ℤ)) ∧
      (∀ (d' : ℕ),
          (1 : ℕ) ≤ d' →
            (∃ (b' : ℕ), ∀ (k : ℕ), (μ : ℕ → ℝ≥0∞) k ≠ (0 : ℝ≥0∞) → k ≠ (0 : ℕ) → (↑d' : ℤ) ∣ (↑k : ℤ) - (↑b' : ℤ)) →
              d' ≤ d) ∧
        ∀ (b' : ℕ), (∀ (k : ℕ), (μ : ℕ → ℝ≥0∞) k ≠ (0 : ℝ≥0∞) → k ≠ (0 : ℕ) → (↑d : ℤ) ∣ (↑k : ℤ) - (↑b' : ℤ)) → b ≤ b'
/-! ## Ordered trees and discrete asymptotics -/
/-- A vertex address, with positive child indices and `[]` for the root. -/
noncomputable abbrev BGW.LocallyFinite.Address : Type := List ℕ
/-- A field assigning a finite offspring count to each address. -/
noncomputable abbrev BGW.LocallyFinite.Offspring : Type := Address → ℕ
/-- Invalid children have zero offspring; the condition propagates to descendants. -/
noncomputable def BGW.LocallyFinite.Canonical (f : Offspring) : Prop :=
  ∀ (u : Address) (j : ℕ), ¬((1 : ℕ) ≤ j ∧ j ≤ f u) → f (u ++ [j]) = (0 : ℕ)
/-- Canonical offspring fields describe possibly infinite, locally finite plane trees. -/
noncomputable abbrev BGW.LocallyFinite.Tree : Type := { f : Offspring // Canonical f }
set_option bootstrap.genMatcherCode false in
/-- Keep the offspring count at an address only if every step of the address is a valid child of the retained counts
above it. -/
noncomputable def BGW.LocallyFinite.pruneRaw (f : Offspring) : Address → ℕ
  | [] => f []
  | j :: u => if 1 ≤ j ∧ j ≤ f [] then BGW.LocallyFinite.pruneRaw (fun v => f (j :: v)) u else 0
theorem BGW.LocallyFinite.canonical_pruneRaw : ∀ (f : Offspring), Canonical (pruneRaw f) := by sorry
/-- The tree obtained from an offspring field by discarding the counts at absent addresses. -/
noncomputable def BGW.LocallyFinite.prune (f : Offspring) : LocallyFinite.Tree :=
  (⟨pruneRaw f, canonical_pruneRaw f⟩ : { f : Offspring // Canonical f })
/-- Independent μ-distributed potential offspring at every address; μ is a probability measure. -/
noncomputable def BGW.LocallyFinite.offspringFieldLaw (μ : Measure ℕ) [arg_inst_0 : IsProbabilityMeasure μ] : Measure Offspring :=
  Measure.infinitePi fun (x : Address) => μ
/-- The Bienaymé–Galton–Watson law with offspring law `μ`. -/
noncomputable def BGW.LocallyFinite.bienaymeLaw (μ : Measure ℕ) [arg_inst_0 : IsProbabilityMeasure μ] : Measure LocallyFinite.Tree :=
  Measure.map prune (offspringFieldLaw μ)
/-- Finite rooted ordered trees, with no vertex labels. -/
noncomputable def BGW.PlaneTree : Type := WType fun (n : ℕ) => Fin n
/-- A tree is determined by the ordered list of subtrees attached to its root. -/
noncomputable def BGW.PlaneTree.equivChildren : PlaneTree ≃ List PlaneTree :=
  (WType.equivSigma fun (n : ℕ) => Fin n).trans List.equivSigmaTuple.symm
/-- The ordered subtrees attached to the root. -/
noncomputable def BGW.PlaneTree.children (t : PlaneTree) : List PlaneTree := (PlaneTree.equivChildren : PlaneTree → List PlaneTree) t
/-- The number of children of the root. -/
noncomputable def BGW.PlaneTree.rootDegree (t : PlaneTree) : ℕ := t.children.length
/-- Offspring count at a positive-index address; invalid addresses have count zero. -/
noncomputable def BGW.PlaneTree.offspringAt : PlaneTree → List ℕ → ℕ
  | t, [] => t.rootDegree
  | _, 0 :: _ => 0
  | t, (i + 1) :: u => ((t.children[i]?).map (fun s => BGW.PlaneTree.offspringAt s u)).getD 0
theorem BGW.PlaneTree.canonical_offspringAt : ∀ (t : PlaneTree), Canonical t.offspringAt := by sorry
/-- View a finite plane tree as a canonical, possibly-infinite-tree value. -/
noncomputable def BGW.PlaneTree.toLocallyFinite (t : PlaneTree) : LocallyFinite.Tree :=
  (⟨t.offspringAt, PlaneTree.canonical_offspringAt t⟩ : { f : Offspring // Canonical f })
/-- The event of `LocallyFinite.Tree` that the tree is finite, equal to `t.toLocallyFinite` for a finite plane tree `t`
with `Q t`. -/
noncomputable def BGWLeaves.finiteTreeEvent (Q : PlaneTree → Prop) : Set LocallyFinite.Tree :=
  {T : LocallyFinite.Tree | ∃ (t : PlaneTree), t.toLocallyFinite = T ∧ Q t}
/-- Bottom-up recursion: `fold g` applies `g` to the values already computed at the children of the root, in child
order. -/
noncomputable def BGW.PlaneTree.fold {β : Type*} (g : List β → β) : PlaneTree → β := WType.elim β fun ⟨_, f⟩ => g (List.ofFn f)
/-- Outdegrees in root-first depth-first order, counting every vertex occurrence. -/
noncomputable def BGW.PlaneTree.degrees : PlaneTree → List ℕ := PlaneTree.fold fun (ds : List (List ℕ)) => ds.length :: ds.flatten
/-- Number of vertices whose outdegree is `k`, counting every DFS occurrence. -/
noncomputable def BGW.PlaneTree.degreeCount (t : PlaneTree) (k : ℕ) : ℕ := List.count k t.degrees
/-- `{λ(τ) = m}` (Theorem 3.1, Corollary 3.3): the tree is finite and has exactly `m` leaves (vertices of outdegree `0`;
`λ(τ) = t.degreeCount 0`). Infinite trees never belong to it. -/
noncomputable def BGWLeaves.leafCountEvent (m : ℕ) : Set LocallyFinite.Tree :=
  BGWLeaves.finiteTreeEvent fun (t : PlaneTree) => t.degreeCount (0 : ℕ) = m
/-- `P_μ[λ(τ) = m]` (the `Prmu{lt = m}` of Theorem 3.1): the probability that a `GW_μ` tree has exactly `m` leaves. -/
noncomputable def BGWLeaves.leafProb (μ : PMF ℕ) (m : ℕ) : ℝ := (bienaymeLaw μ.toMeasure).real (BGWLeaves.leafCountEvent m)
/-- Theorem 3.1(i): eventual admissible leaf counts, including lattice laws. -/
theorem BGWLeaves.thm_ltn_i {μ : PMF ℕ} {θ : ℝ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hDA : ∃ a, StableDomain μ θ a) (hap : Aperiodic μ) {d b : ℕ} (hdb : IsSuppSpan μ d b) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → (0 < leafProb μ (n + 1) ↔ Int.gcd ((b : ℤ) - 1) (d : ℤ) ∣ n) := by sorry
/-- The slowly varying function `h` of Theorem 3.1 (`B_n = h(n) n^{1/θ}`, introduced before Lemma 1.11 of the paper):
`h(x) = B_{⌊x⌋} / x^{1/θ}` with `B_n = norming (stepLaw μ) θ n` (the corrected norming). That it is slowly varying is
`hSlow_slowlyVarying`. -/
noncomputable def BGWLeaves.hSlow (μ : PMF ℕ) (θ : ℝ) (arg_a_0 : ℝ) : ℝ := norming (stepLaw μ) θ ⌊arg_a_0⌋₊ / arg_a_0 ^ ((1 : ℝ) / θ)
/-- Theorem 3.1(ii), Introduction (I): leaf-count probability asymptotics on the admissible progression. -/
theorem BGWLeaves.thm_ltn_ii {μ : PMF ℕ} {θ : ℝ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hap : Aperiodic μ) (hDA : ∃ a, StableDomain μ θ a) {d b : ℕ} (hdb : IsSuppSpan μ d b) :
    (fun n : ℕ => leafProb μ (n + 1)) ~[atTop ⊓ 𝓟 {n : ℕ | Int.gcd ((b : ℤ) - 1) (d : ℤ) ∣ n}]
      (fun n : ℕ => (μ 0).toReal ^ (1 / θ) * Scalar.stableDensity θ 0 *
        (Int.gcd ((b : ℤ) - 1) (d : ℤ) : ℝ) / (hSlow μ θ n * (n : ℝ) ^ (1 / θ + 1))) := by sorry
/-- The integers whose gcd is the arithmetic factor: the offspring numbers `k ∈ supp μ ∩ A` and the shifted offspring
numbers `k - 1` for `k ∈ supp μ ∖ A`. -/
noncomputable def BGWLeaves.arithSet (μ : PMF ℕ) (A : Set ℕ) : Set ℤ :=
  {s : ℤ | ∃ (k : ℕ), (μ : ℕ → ℝ≥0∞) k ≠ (0 : ℝ≥0∞) ∧ (k ∈ A ∧ s = (↑k : ℤ) ∨ k ∉ A ∧ s = (↑k : ℤ) - (1 : ℤ))}
/-- The largest positive integer dividing every element of `arithSet μ A` (the gcd). It is positive and finite as soon
as `arithSet` contains a nonzero integer, which holds for a critical `μ` with `μ 1 ≠ 1` (see `arithFactor_isGreatest`). -/
noncomputable def BGWLeaves.arithFactor (μ : PMF ℕ) (A : Set ℕ) : ℕ := sSup {e : ℕ | (1 : ℕ) ≤ e ∧ ∀ s ∈ BGWLeaves.arithSet μ A, (↑e : ℤ) ∣ s}
/-- The number of children of the root. -/
noncomputable def BGW.LocallyFinite.degree (T : LocallyFinite.Tree) : ℕ := (↑T : Offspring) []
theorem BGW.LocallyFinite.child._proof_1 : ∀ (T : LocallyFinite.Tree) (j : Nat) (u : Address) (k : Nat), Not (And (@LE.le Nat instLENat (@OfNat.ofNat Nat (nat_lit 1)
  (instOfNatNat (nat_lit 1))) k) (@LE.le Nat instLENat k (@Subtype.val Offspring (fun f => Canonical f) T (@List.cons Nat j u)))) →
  @Eq Nat (@Subtype.val Offspring (fun f => Canonical f) T (@HAppend.hAppend Address (List Nat) Address (@instHAppendOfAppend
  Address (@List.instAppend Nat)) (@List.cons Nat j u) (@List.cons Nat k (@List.nil Nat)))) (@OfNat.ofNat Nat (nat_lit 0)
  (instOfNatNat (nat_lit 0))) := by sorry
/-- Re-root at child `j`. An absent child is represented by `leaf`; use `Present` to test whether that child actually
exists. -/
noncomputable def BGW.LocallyFinite.child (T : LocallyFinite.Tree) (j : ℕ) : LocallyFinite.Tree :=
  (⟨fun (u : Address) => (↑T : Offspring) (j :: u), child._proof_1 T j⟩ : { f : Offspring // Canonical f })
/-- Membership of an address, including leaves and the root. -/
noncomputable def BGW.LocallyFinite.Present (T : BGW.LocallyFinite.Tree) : Address → Prop
  | [] => True
  | j :: u => 1 ≤ j ∧ j ≤ degree T ∧ BGW.LocallyFinite.Present (child T j) u
/-- `ζ_A(τ)`: the number of vertices `u` of `τ` whose offspring number lies in `A`, as an extended natural number
(infinite trees may have `ζ_A = ∞`). -/
noncomputable def BGWLeaves.zetaA (A : Set ℕ) (T : LocallyFinite.Tree) : ℕ∞ := {u : Address | Present T u ∧ (↑T : Offspring) u ∈ A}.encard
/-- `P_μ[ζ_A = n]`, so that the statements of `BGWLeaves.GeneralAInf` stay readable. -/
noncomputable abbrev BGWLeaves.zetaAProb (μ : PMF ℕ) (A : Set ℕ) (n : ℕ) : ℝ :=
  (bienaymeLaw μ.toMeasure).real {T : LocallyFinite.Tree | BGWLeaves.zetaA A T = (↑n : ℕ∞)}
/-- Corrected Theorem 8.1(I): arbitrary offspring-mark sets of positive mass, with the corrected gcd factor. The printed
false factor is not claimed; see README.md for the correction and strengthening. -/
theorem BGWLeaves.thm81_corrected_general {μ : PMF ℕ} {θ : ℝ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hDA : ∃ a, StableDomain μ θ a) {A : Set ℕ} (hA : μ.toMeasure A ≠ 0) :
    (∀ n : ℕ, ¬ ((arithFactor μ A : ℤ) ∣ (n : ℤ) - 1) →
        bienaymeLaw μ.toMeasure {T | zetaA A T = n} = 0) ∧
    Tendsto (fun j : ℕ =>
        ((arithFactor μ A * j + 1 : ℕ) : ℝ) * norming (stepLaw μ) θ (arithFactor μ A * j + 1) *
          zetaAProb μ A (arithFactor μ A * j + 1))
      atTop
      (𝓝 ((μ.toMeasure A).toReal ^ (1 / θ) * Scalar.stableDensity θ 0 * (arithFactor μ A : ℝ))) := by sorry
namespace BGWLeaves
local notation "radiusSupSet" =>
  @ConditionallyCompletePartialOrderSup.toSupSet ℝ≥0∞
    (@ConditionallyCompletePartialOrder.toConditionallyCompletePartialOrderSup ℝ≥0∞
      (@ConditionallyCompleteLattice.toConditionallyCompletePartialOrder ℝ≥0∞
        (@ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice ℝ≥0∞
          (@ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder ℝ≥0∞
            (@CompleteLinearOrder.toConditionallyCompleteLinearOrderBot ℝ≥0∞ ENNReal.instCompleteLinearOrder)))))

/-- The radius of convergence `R ∈ [0, ∞]` of `∑ μ(i) z^i`: the supremum of the `r ≥ 0` for which `∑ μ(i) r^i` converges
(the definition; no Cauchy-Hadamard is used). -/
noncomputable def genFunRadius (μ : PMF ℕ) : ℝ≥0∞ :=
  @iSup ℝ≥0∞ ℝ≥0 radiusSupSet fun r =>
    @iSup ℝ≥0∞ (Summable fun n : ℕ => (μ n).toReal * (r : ℝ) ^ n) radiusSupSet
      fun _ => (r : ℝ≥0∞)

end BGWLeaves
namespace BGWLeaves
/-- Hypothesis H: critical, nondegenerate, aperiodic, finite variance, radius R>1. For finite R the offspring nth roots
tend to 1/R; for R=∞ they are eventually nonincreasing, including bounded support. -/
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
end BGWLeaves
/-- `μ([x, ∞))` for a real threshold `x` (`{k : ℕ | x ≤ k}`); this is the paper's `μ([x,∞))`, e.g. `μ([(1 - ε) D(n),
∞))`. -/
noncomputable def BGWLeaves.offTail (μ : PMF ℕ) (x : ℝ) : ℝ := ((μ.toMeasure : Set ℕ → ℝ≥0∞) {k : ℕ | x ≤ (↑k : ℝ)}).toReal
/-- `D(n) = max {k ≥ 1 ; μ([k,∞)) ≥ 1/n}` (`sSup` in `ℕ`). The set is nonempty and bounded for `n ≥ 1/(1 - μ₀)` (see
`bigD_spec`); for smaller `n` the value is the junk `0`. -/
noncomputable def BGWLeaves.bigD (μ : PMF ℕ) (n : ℕ) : ℕ := sSup {k : ℕ | (1 : ℕ) ≤ k ∧ (1 : ℝ) / (↑n : ℝ) ≤ BGWLeaves.offTail μ (↑k : ℝ)}
/-- `Δ(τ) = max{k_u ; u ∈ τ}`, the maximum number of children (`PlaneTree.degrees` lists all outdegrees). -/
noncomputable def BGWLeaves.maxDegree (t : PlaneTree) : ℕ := List.foldr max (0 : ℕ) t.degrees
/-- Theorem 7.1(ii): maximum-degree concentration under HypH, along non-null leaf counts. Both bounded and unbounded
offspring support are included. -/
theorem BGWLeaves.thm_max_ii {μ : PMF ℕ} (h : HypH μ) {ε : ℝ} (hε : 0 < ε) {δ : ℝ} (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → leafProb μ n ≠ 0 →
      1 - δ ≤ ((bienaymeLaw μ.toMeasure)[|leafCountEvent n]).real
        (finiteTreeEvent fun t =>
          (1 - ε) * (bigD μ n : ℝ) ≤ (maxDegree t : ℝ) ∧ (maxDegree t : ℝ) ≤ (1 + ε) * (bigD μ n : ℝ)) := by sorry
theorem BGW.Probability.RealWalk.iidLaw._proof_1 : ∀ (ν : ProbabilityMeasure ℝ), IsProbabilityMeasure (Measure.infinitePi fun (x : ℕ) => (↑ν : Measure ℝ)) := by sorry
/-- The canonical real iid law `ν ^ ⊗ ℕ` on sequences. -/
noncomputable def BGW.Probability.RealWalk.iidLaw (ν : ProbabilityMeasure ℝ) : ProbabilityMeasure (ℕ → ℝ) :=
  (⟨Measure.infinitePi fun (x : ℕ) => (↑ν : Measure ℝ), iidLaw._proof_1 ν⟩ :
    { μ : Measure (ℕ → ℝ) // IsProbabilityMeasure μ })
/-- The partial sum `ω 0 + ⋯ + ω (m-1)`. -/
noncomputable def BGW.Probability.RealWalk.partialSum (ω : ℕ → ℝ) (m : ℕ) : ℝ := ∑ i ∈ Finset.range m, ω i
/-- The law of the sum of `m` iid steps. -/
noncomputable def BGW.Probability.RealWalk.sumLaw (ν : ProbabilityMeasure ℝ) (m : ℕ) : ProbabilityMeasure ℝ :=
  (iidLaw ν).map fun (ω : ℕ → ℝ) => partialSum ω m
/-- The law of the sum of `m` iid steps divided by `B m`. -/
noncomputable def BGW.Probability.RealWalk.scaledSumLaw (ν : ProbabilityMeasure ℝ) (B : ℕ → ℝ) (m : ℕ) : ProbabilityMeasure ℝ :=
  (sumLaw ν m).map fun (x : ℝ) => x / B m
theorem BGW.StableTrees.stableLaw._proof_2 : ((1 : ℕ) + (1 : ℕ)).AtLeastTwo := by sorry
theorem BGW.StableTrees.stableLaw._proof_1 : ∀ (θ : Real), And (@LT.lt Real Real.instLT (@OfNat.ofNat Real (nat_lit 1) (@One.toOfNat1 Real Real.instOne)) θ) (@LE.le Real
  Real.instLE θ (@OfNat.ofNat Real (nat_lit 2) (@instOfNatAtLeastTwo Real (nat_lit 2) Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat
  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (@Nat.instNeZeroSucc (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat
  (nat_lit 0)))))))) → @IsProbabilityMeasure Real Real.measurableSpace (@Measure.withDensity Real (@MeasureSpace.toMeasurableSpace
  Real Real.measureSpace) (@volume Real Real.measureSpace) fun x => ENNReal.ofReal (Scalar.stableDensity θ x)) := by sorry
theorem BGW.StableTrees.stableLaw._proof_3 : IsProbabilityMeasure (Measure.dirac (0 : ℝ)) := by sorry
/-- The spectrally positive θ-stable law, normalized by `E[exp(-λ X)] = exp(λ^θ)`, for `1 < θ ≤ 2`; the Dirac mass at
`0` outside this range (a junk value). -/
noncomputable def BGW.StableTrees.stableLaw (θ : ℝ) : ProbabilityMeasure ℝ :=
  if hθ : (1 : ℝ) < θ ∧ θ ≤ twoReal[BGW.StableTrees.stableLaw._proof_2] then
    (⟨volume.withDensity fun (x : ℝ) => ENNReal.ofReal (Scalar.stableDensity θ x), stableLaw._proof_1 θ hθ⟩ :
      { μ : Measure ℝ // IsProbabilityMeasure μ })
  else (⟨Measure.dirac (0 : ℝ), stableLaw._proof_3⟩ : { μ : Measure ℝ // IsProbabilityMeasure μ })
namespace BGW.StableTrees
/-- Real scalar attraction (audit correction 1): `B n > 0` only eventually; no monotonicity, no centering, and no moment
assumption. -/
structure IsRealStableAttracted (ν : ProbabilityMeasure ℝ) (θ : ℝ) (B : ℕ → ℝ) : Prop where
  index_mem : 1 < θ ∧ θ ≤ 2
  pos : ∀ᶠ n in atTop, 0 < B n
  converges : Tendsto (fun n => scaledSumLaw ν B n) atTop (𝓝 (stableLaw θ))
end BGW.StableTrees
theorem BGW.StableTrees.castLaw._proof_1 : ∀ (ν : Measure ℤ) [IsProbabilityMeasure ν], IsProbabilityMeasure (Measure.map (fun (z : ℤ) => (↑z : ℝ)) ν) := by sorry
/-- The cast pushforward of an integer step law to `ℝ`. -/
noncomputable def BGW.StableTrees.castLaw (ν : Measure ℤ) [arg_inst_0 : IsProbabilityMeasure ν] : ProbabilityMeasure ℝ :=
  (⟨Measure.map (fun (z : ℤ) => (↑z : ℝ)) ν, castLaw._proof_1 ν⟩ : { μ : Measure ℝ // IsProbabilityMeasure μ })
theorem BGW.StableTrees.Attraction.isProbabilityMeasure_stepLaw : ∀ (μ : PMF ℕ), IsProbabilityMeasure (stepLaw μ) := by sorry
attribute [instance] BGW.StableTrees.Attraction.isProbabilityMeasure_stepLaw
/-- The real offspring step law `K - 1`, as a cast of `stepLaw μ`. -/
noncomputable def BGW.StableTrees.realOffspringStepLaw (μ : PMF ℕ) : ProbabilityMeasure ℝ := castLaw (stepLaw μ)
/-- `P_μ[λ(τ) = n] > 0`: the `n` along which Intro (II) is stated. -/
noncomputable def BGWLeaves.LeafAdmissible (μ : PMF ℕ) (n : ℕ) : Prop :=
  (bienaymeLaw μ.toMeasure : Set LocallyFinite.Tree → ℝ≥0∞) (BGWLeaves.leafCountEvent n) ≠ (0 : ℝ≥0∞)
/-! ## Skorokhod path space and coding maps -/
namespace BGW.Skorokhod
/-- The Skorokhod space `D([0,T], E)` of càdlàg paths on `[0,T]`. On the subtype `Set.Icc 0 T`, `IsCadlag` is
Billingsley's condition: right-continuity at every `t < T` and a left limit at every `t > 0`. -/
structure D (T : ℝ) (E : Type*) [TopologicalSpace E] where
  /-- The underlying path. -/
  toFun : Set.Icc (0 : ℝ) T → E
  /-- The path is càdlàg. -/
  isCadlag' : IsCadlag toFun
end BGW.Skorokhod
local notation "paths[" T "]" => @BGW.Skorokhod.D T ℝ (@UniformSpace.toTopologicalSpace Real (@PseudoMetricSpace.toUniformSpace Real Real.pseudoMetricSpace))
/-- Increasing order isomorphisms of the interval `[0,T]`. -/
noncomputable abbrev BGW.Skorokhod.TimeChange (T : ℝ) : Type := (↑(Icc (0 : ℝ) T) : Type) ≃o (↑(Icc (0 : ℝ) T) : Type)
/-- Evaluation of a càdlàg path as its underlying function; equal functions give equal paths. -/
noncomputable def BGW.Skorokhod.instFunLikeDElemRealIccOfNat.{u_1} : {T : ℝ} → {E : Type u_1} → [inst : TopologicalSpace E] → FunLike (D T E) (↑(Icc (0 : ℝ) T) : Type) E :=
  fun {T} {E} [inst : TopologicalSpace E] => { coe := D.toFun, coe_injective := by sorry }
attribute [instance, instance_reducible] BGW.Skorokhod.instFunLikeDElemRealIccOfNat
/-- Billingsley's Skorokhod J1 distance: `d(f,g) = inf_σ max (sup_t |σ t - t|) (sup_t dist (f t) (g (σ t)))`. -/
noncomputable def BGW.Skorokhod.j1Dist.{u_1} {T : ℝ} {E : Type u_1} [arg_inst_0 : PseudoMetricSpace E] (f : D T E) (g : D T E) : ℝ :=
  ⨅ (σ : TimeChange T),
    max
      (⨆ (t : (↑(Icc (0 : ℝ) T) : Type)),
        |(↑((σ : (↑(Icc (0 : ℝ) T) : Type) → (↑(Icc (0 : ℝ) T) : Type)) t) : ℝ) - (↑t : ℝ)|)
      (⨆ (t : (↑(Icc (0 : ℝ) T) : Type)),
        dist ((f : (↑(Icc (0 : ℝ) T) : Type) → E) t)
          ((g : (↑(Icc (0 : ℝ) T) : Type) → E) ((σ : (↑(Icc (0 : ℝ) T) : Type) → (↑(Icc (0 : ℝ) T) : Type)) t)))
/-- The J1 metric space structure, with distance `j1Dist`. -/
noncomputable def BGW.Skorokhod.instMetricSpace.{u_1} : {T : ℝ} → {E : Type u_1} → [inst : MetricSpace E] → MetricSpace (D T E) :=
  fun {T} {E} [inst : MetricSpace E] => { dist := j1Dist, dist_self := by sorry, dist_comm := by sorry, dist_triangle := by sorry, eq_of_dist_eq_zero := by sorry }
attribute [instance, instance_reducible] BGW.Skorokhod.instMetricSpace
/-- The measurable structure on the Skorokhod space is the Borel structure of J1. -/
noncomputable def BGW.Skorokhod.instMeasurableSpace.{u_1} {T : ℝ} {E : Type u_1} [arg_inst_0 : MetricSpace E] : MeasurableSpace (D T E) :=
  borel (D T E)
attribute [instance, instance_reducible] BGW.Skorokhod.instMeasurableSpace
theorem BGWLeaves.leafTreeLaw._proof_1 : ∀ (μ : PMF ℕ) (n : ℕ),
  BGWLeaves.LeafAdmissible μ n → IsProbabilityMeasure (bienaymeLaw μ.toMeasure)[|BGWLeaves.leafCountEvent n] := by sorry
theorem BGW.LocallyFinite.leaf._proof_1 : ∀ (x : Address) (x : ℕ), ¬((1 : ℕ) ≤ x ∧ x ≤ (0 : ℕ)) → (0 : ℕ) = (0 : ℕ) := by sorry
/-- The tree consisting only of its root, with zero offspring at every address. -/
noncomputable def BGW.LocallyFinite.leaf : LocallyFinite.Tree :=
  (⟨fun (x : Address) => (0 : ℕ), leaf._proof_1⟩ : { f : Offspring // Canonical f })
theorem BGWLeaves.leafTreeLaw._proof_2 : IsProbabilityMeasure (Measure.dirac leaf) := by sorry
/-- `P_μ[· | λ = n]` as a probability measure on trees; the Dirac mass at the one-vertex tree when `P_μ[λ = n] = 0`
(junk; excluded by admissibility in sequence-indexed limits and eventually excluded in the all-size canonical
corollary). -/
noncomputable def BGWLeaves.leafTreeLaw (μ : PMF ℕ) (n : ℕ) : ProbabilityMeasure LocallyFinite.Tree :=
  if h : BGWLeaves.LeafAdmissible μ n then
    (⟨(bienaymeLaw μ.toMeasure)[|BGWLeaves.leafCountEvent n], BGWLeaves.leafTreeLaw._proof_1 μ n h⟩ :
      { μ : Measure LocallyFinite.Tree // IsProbabilityMeasure μ })
  else
    (⟨Measure.dirac leaf, BGWLeaves.leafTreeLaw._proof_2⟩ : { μ : Measure LocallyFinite.Tree // IsProbabilityMeasure μ })
theorem BGW.Skorokhod.isCadlag_stepPath : ∀ {T : ℝ} (n : ℕ) (b : ℝ) (ω : ℕ → ℝ),
  IsCadlag fun (t : (↑(Icc (0 : ℝ) T) : Type)) => partialSum ω ⌊(↑n : ℝ) * (↑t : ℝ)⌋₊ / b := by sorry
/-- The càdlàg floor-step path `t ↦ S_{⌊n t⌋} / b` on `[0,T]` (Node 2). The same formula is used at `T`: if `n T` is an
integer there is a genuine terminal jump. -/
noncomputable def BGW.Skorokhod.realStepPath (T : ℝ) (n : ℕ) (b : ℝ) (ω : ℕ → ℝ) : D T ℝ :=
  { toFun := fun (t : (↑(Icc (0 : ℝ) T) : Type)) => partialSum ω ⌊(↑n : ℝ) * (↑t : ℝ)⌋₊ / b,
    isCadlag' := isCadlag_stepPath n b ω : D T ℝ }
/-- Finiteness refers to the vertices, not to the support of the offspring field. -/
noncomputable def BGW.LocallyFinite.FiniteVertices (T : LocallyFinite.Tree) : Prop := {u : Address | Present T u}.Finite
/-- Integer Łukasiewicz increments; subtraction is not truncated at zero. -/
noncomputable def BGW.PlaneTree.increments (t : PlaneTree) : List ℤ := List.map (fun (d : ℕ) => (↑d : ℤ) - (1 : ℤ)) t.degrees
theorem BGW.PlaneTree.finiteVertices_toLocallyFinite : ∀ (t : PlaneTree), FiniteVertices t.toLocallyFinite := by sorry
theorem BGW.PlaneTree.equivFiniteVertices._proof_2 : (Function.Injective fun (t : PlaneTree) =>
    (⟨t.toLocallyFinite, PlaneTree.finiteVertices_toLocallyFinite t⟩ :
      { T : LocallyFinite.Tree // FiniteVertices T })) ∧
  Function.Surjective fun (t : PlaneTree) =>
    (⟨t.toLocallyFinite, PlaneTree.finiteVertices_toLocallyFinite t⟩ : { T : LocallyFinite.Tree // FiniteVertices T }) := by sorry
/-- The existing finite-tree type is equivalent to the finite part of the canonical carrier. -/
noncomputable def BGW.PlaneTree.equivFiniteVertices : PlaneTree ≃ { T : LocallyFinite.Tree // FiniteVertices T } :=
  Equiv.ofBijective
    (fun (t : PlaneTree) =>
      (⟨t.toLocallyFinite, PlaneTree.finiteVertices_toLocallyFinite t⟩ : { T : LocallyFinite.Tree // FiniteVertices T }))
    PlaneTree.equivFiniteVertices._proof_2
/-- The DFS increments `(d_i - 1)` of a finite tree (empty list for infinite trees). -/
noncomputable def BGW.StableTrees.PathTail.treeIncrements (τ : LocallyFinite.Tree) : List ℤ :=
  if h : FiniteVertices τ then
    ((PlaneTree.equivFiniteVertices.symm : { T : LocallyFinite.Tree // FiniteVertices T } → PlaneTree)
        (⟨τ, h⟩ : { T : LocallyFinite.Tree // FiniteVertices T })).increments
  else []
/-- The increments of a tree as a real sequence, extended by `0` after the end of the tree. -/
noncomputable def BGW.StableTrees.PathTail.treeIncrementSeq (τ : LocallyFinite.Tree) (arg_a_0 : ℕ) : ℝ :=
  (↑((PathTail.treeIncrements τ).getD arg_a_0 (0 : ℤ)) : ℝ)
/-- `t ↦ W_{⌊z t⌋}(τ) / b` on `[0,1]` (Łukasiewicz path, time scale `z`, divisor `b`). -/
noncomputable def BGWLeaves.rescaledLuka (z : ℕ) (b : ℝ) (τ : LocallyFinite.Tree) : D (1 : ℝ) ℝ :=
  realStepPath (1 : ℝ) z b (PathTail.treeIncrementSeq τ)
/-- `ζ(τ)`: the number of vertices of `τ` (`0` for an infinite tree, `Set.ncard` convention). -/
noncomputable def BGWLeaves.treeSize (τ : LocallyFinite.Tree) : ℕ := {u : Address | Present τ u}.ncard
/-- Heights along the complete depth-first contour, including both endpoint visits. -/
noncomputable def BGW.PlaneTree.contour : PlaneTree → List ℕ :=
  PlaneTree.fold fun (cs : List (List ℕ)) =>
    (0 : ℕ) :: (List.map (fun (c : List ℕ) => List.map Nat.succ c ++ [(0 : ℕ)]) cs).flatten
/-- The contour at integer time `m` (original speed), `0` after the end of the contour. -/
noncomputable def BGW.PlaneTree.contourAt (t : PlaneTree) (m : ℕ) : ℕ := t.contour.getD m (0 : ℕ)
/-- Linear interpolation of the contour at integer times (used for `s ≥ 0`). -/
noncomputable def BGW.PlaneTree.contourLin (t : PlaneTree) (s : ℝ) : ℝ :=
  ((1 : ℝ) - (s - (↑⌊s⌋₊ : ℝ))) * (↑(t.contourAt ⌊s⌋₊) : ℝ) + (s - (↑⌊s⌋₊ : ℝ)) * (↑(t.contourAt (⌊s⌋₊ + (1 : ℕ))) : ℝ)
/-- The interpolated contour (original speed, `0` after time `2(z-1)`) of the decoded finite tree; `0` for an infinite
tree. -/
noncomputable def BGW.StableTrees.ExactContour.treeContourLin (τ : LocallyFinite.Tree) (s : ℝ) : ℝ :=
  if h : FiniteVertices τ then
    ((PlaneTree.equivFiniteVertices.symm : { T : LocallyFinite.Tree // FiniteVertices T } → PlaneTree)
          (⟨τ, h⟩ : { T : LocallyFinite.Tree // FiniteVertices T })).contourLin
      s
  else (0 : ℝ)
theorem BGWLeaves.rescaledContour._proof_1 : ((1 : ℕ) + (1 : ℕ)).AtLeastTwo := by sorry
theorem BGWLeaves.rescaledContour._proof_2 : ∀ (z : ℕ) (a : ℝ) (τ : LocallyFinite.Tree),
  Continuous
    ((fun (x : (↑(Icc (0 : ℝ) (1 : ℝ)) : Type)) => a) * fun (t : (↑(Icc (0 : ℝ) (1 : ℝ)) : Type)) =>
      ExactContour.treeContourLin τ (twoReal[BGWLeaves.rescaledContour._proof_1] * (↑z : ℝ) * (↑t : ℝ))) := by sorry
/-- `t ↦ a · C_{2 z t}(τ)` on `[0,1]` (contour function, paper clock: `C = 0` on `[2(ζ-1), 2ζ]`). -/
noncomputable def BGWLeaves.rescaledContour (z : ℕ) (a : ℝ) (τ : LocallyFinite.Tree) : C((↑(Icc (0 : ℝ) (1 : ℝ)) : Type), ℝ) :=
  {
    toFun := fun (t : (↑(Icc (0 : ℝ) (1 : ℝ)) : Type)) =>
      a * ExactContour.treeContourLin τ (twoReal[BGWLeaves.rescaledContour._proof_1] * (↑z : ℝ) * (↑t : ℝ)),
    continuous_toFun := BGWLeaves.rescaledContour._proof_2 z a τ : C((↑(Icc (0 : ℝ) (1 : ℝ)) : Type), ℝ) }
/-- All vertex addresses, listed in root-first depth-first order. -/
noncomputable def BGW.PlaneTree.vertices : PlaneTree → List (List ℕ) :=
  PlaneTree.fold fun (vs : List (List (List ℕ))) =>
    [] :: (List.mapIdx (fun (i : ℕ) (v : List (List ℕ)) => List.map (fun (u : List ℕ) => i :: u) v) vs).flatten
/-- DFS heights extended by `0`: `|v_i|` for `i < size`, and `0` for `i ≥ size`. -/
noncomputable def BGW.PlaneTree.heightSeq (t : PlaneTree) (i : ℕ) : ℕ := (Option.map List.length t.vertices[i]?).getD (0 : ℕ)
/-- Linear interpolation of the heights at integer times (used for `u ≥ 0`). -/
noncomputable def BGW.PlaneTree.heightLin (t : PlaneTree) (u : ℝ) : ℝ :=
  ((1 : ℝ) - (u - (↑⌊u⌋₊ : ℝ))) * (↑(t.heightSeq ⌊u⌋₊) : ℝ) + (u - (↑⌊u⌋₊ : ℝ)) * (↑(t.heightSeq (⌊u⌋₊ + (1 : ℕ))) : ℝ)
/-- Linear interpolation at real time `u` of the DFS heights of a locally finite tree: the `PlaneTree.heightLin` of the
decoded finite tree (heights `|v_i|` for `i < z`, then `0`), and `0` for an infinite tree. -/
noncomputable def BGW.StableTrees.TailPair.treeHeightLin (τ : LocallyFinite.Tree) (u : ℝ) : ℝ :=
  if h : FiniteVertices τ then
    ((PlaneTree.equivFiniteVertices.symm : { T : LocallyFinite.Tree // FiniteVertices T } → PlaneTree)
          (⟨τ, h⟩ : { T : LocallyFinite.Tree // FiniteVertices T })).heightLin
      u
  else (0 : ℝ)
theorem BGWLeaves.rescaledHeight._proof_1 : ∀ (z : ℕ) (a : ℝ) (τ : LocallyFinite.Tree),
  Continuous
    ((fun (x : (↑(Icc (0 : ℝ) (1 : ℝ)) : Type)) => a) * fun (t : (↑(Icc (0 : ℝ) (1 : ℝ)) : Type)) =>
      TailPair.treeHeightLin τ ((↑z : ℝ) * (↑t : ℝ))) := by sorry
/-- `t ↦ a · H_{z t}(τ)` on `[0,1]` (height function, linear interpolation, `H = 0` after `ζ`). -/
noncomputable def BGWLeaves.rescaledHeight (z : ℕ) (a : ℝ) (τ : LocallyFinite.Tree) : C((↑(Icc (0 : ℝ) (1 : ℝ)) : Type), ℝ) :=
  { toFun := fun (t : (↑(Icc (0 : ℝ) (1 : ℝ)) : Type)) => a * TailPair.treeHeightLin τ ((↑z : ℝ) * (↑t : ℝ)),
    continuous_toFun := BGWLeaves.rescaledHeight._proof_1 z a τ : C((↑(Icc (0 : ℝ) (1 : ℝ)) : Type), ℝ) }
/-- The three rescaled codings of Intro (II) at the RANDOM size `ζ = ζ(τ)`: `(W_{⌊ζ t⌋}/B_ζ, (B_ζ/ζ) C_{2ζt}, (B_ζ/ζ)
H_{ζt})_{0 ≤ t ≤ 1}` (lines 256-259). -/
noncomputable def BGWLeaves.codingTriple (B : ℕ → ℝ) (τ : LocallyFinite.Tree) : D (1 : ℝ) ℝ × C((↑(Icc (0 : ℝ) (1 : ℝ)) : Type), ℝ) × C((↑(Icc (0 : ℝ) (1 : ℝ)) : Type), ℝ) :=
  (BGWLeaves.rescaledLuka (BGWLeaves.treeSize τ) (B (BGWLeaves.treeSize τ)) τ,
    BGWLeaves.rescaledContour (BGWLeaves.treeSize τ) (B (BGWLeaves.treeSize τ) / (↑(BGWLeaves.treeSize τ) : ℝ)) τ,
    BGWLeaves.rescaledHeight (BGWLeaves.treeSize τ) (B (BGWLeaves.treeSize τ) / (↑(BGWLeaves.treeSize τ) : ℝ)) τ)
theorem BGW.Skorokhod.instBorelSpace.{u_1} : ∀ {T : ℝ} {E : Type u_1} [inst : MetricSpace E], BorelSpace (D T E) := by sorry
attribute [instance] BGW.Skorokhod.instBorelSpace
/-! ## Stable processes and normalized excursions -/
/-- The local càdlàg carrier: càdlàg real paths on `ℝ≥0` (Mathlib's `IsCadlag`; at `0` the left limit is vacuous). -/
noncomputable def BGW.Skorokhod.DLoc : Type := { f : ℝ≥0 → ℝ // IsCadlag f }
attribute [reducible] BGW.Skorokhod.DLoc
/-- The valid-excursion conditions on a (path, tag) pair: starts at `0`, nonnegative, identically zero at and after the
tag. -/
noncomputable def BGW.StableTrees.IsExcursionTag (p : DLoc × (↑(Ioi (0 : ℝ≥0)) : Type)) : Prop :=
  (↑p.1 : ℝ≥0 → ℝ) (0 : ℝ≥0) = (0 : ℝ) ∧
    (∀ (t : ℝ≥0), (0 : ℝ) ≤ (↑p.1 : ℝ≥0 → ℝ) t) ∧ ∀ (t : ℝ≥0), (↑p.2 : ℝ≥0) ≤ t → (↑p.1 : ℝ≥0 → ℝ) t = (0 : ℝ)
/-- The tagged excursion carrier (Borel subtype of `DLoc × Ioi 0`). -/
noncomputable def BGW.StableTrees.Excursion : Type := { p : DLoc × (↑(Ioi (0 : ℝ≥0)) : Type) // IsExcursionTag p }
attribute [reducible] BGW.StableTrees.Excursion
/-- Evaluation at time `t`. -/
noncomputable def BGW.Skorokhod.DLoc.eval (t : ℝ≥0) (f : DLoc) : ℝ := (↑f : ℝ≥0 → ℝ) t
/-- The evaluation σ-algebra: the supremum of the pullbacks of the Borel σ-algebra of `ℝ` under all evaluations. -/
noncomputable def BGW.Skorokhod.DLoc.instMeasurableSpace : MeasurableSpace DLoc :=
  @iSup (MeasurableSpace DLoc) NNReal (@ConditionallyCompletePartialOrderSup.toSupSet (MeasurableSpace DLoc)
    (@ConditionallyCompletePartialOrder.toConditionallyCompletePartialOrderSup (MeasurableSpace DLoc)
    (@ConditionallyCompleteLattice.toConditionallyCompletePartialOrder (MeasurableSpace DLoc)
    (@CompleteLattice.toConditionallyCompleteLattice (MeasurableSpace DLoc) (@MeasurableSpace.instCompleteLattice DLoc))))) fun t =>
    @MeasurableSpace.comap DLoc Real (DLoc.eval t) (@inferInstance (MeasurableSpace Real) Real.measurableSpace)
attribute [instance, instance_reducible] BGW.Skorokhod.DLoc.instMeasurableSpace
/-- The subspace sigma-algebra on excursion tags, inherited from local paths and positive lifetimes. -/
noncomputable def BGW.StableTrees.instMeasurableSpaceExcursion : MeasurableSpace Excursion :=
  (inferInstance : MeasurableSpace {p : DLoc × Set.Ioi (0 : ℝ≥0) // IsExcursionTag p})
attribute [instance, instance_reducible] BGW.StableTrees.instMeasurableSpaceExcursion
theorem BGW.StableTrees.zeroLoc._proof_1 : IsCadlag fun (x : ℝ≥0) => (0 : ℝ) := by sorry
/-- The constant zero local path. -/
noncomputable def BGW.StableTrees.zeroLoc : DLoc := (⟨fun (x : ℝ≥0) => (0 : ℝ), zeroLoc._proof_1⟩ : { f : ℝ≥0 → ℝ // IsCadlag f })
theorem BGW.StableTrees.junkExcursion._proof_2 : (1 : ℝ≥0) ∈ Ioi (0 : ℝ≥0) := by sorry
theorem BGW.StableTrees.junkExcursion._proof_1 : IsExcursionTag (zeroLoc, (⟨(1 : ℝ≥0), mem_Ioi.mpr (@one_pos NNReal NNReal.instZero NNReal.instOne NNReal.instPartialOrder
  (@FloorSemiring.instZeroLEOneClass NNReal NNReal.instSemiring NNReal.instPartialOrder NNReal.instFloorSemiring)
  (@NeZero.charZero_one NNReal (@AddCommMonoidWithOne.toAddMonoidWithOne NNReal (@NonAssocSemiring.toAddCommMonoidWithOne NNReal
  (@Semiring.toNonAssocSemiring NNReal NNReal.instSemiring))) (@FloorSemiring.instCharZero NNReal NNReal.instSemiring
  NNReal.instPartialOrder NNReal.instFloorSemiring)))⟩ : { x : ℝ≥0 // x ∈ Ioi (0 : ℝ≥0) })) := by sorry
/-- The junk excursion: zero path with tag one. -/
noncomputable def BGW.StableTrees.junkExcursion : Excursion :=
  (⟨(zeroLoc, (⟨(1 : ℝ≥0), junkExcursion._proof_2⟩ : { x : ℝ≥0 // x ∈ Ioi (0 : ℝ≥0) })), junkExcursion._proof_1⟩ :
    { p : DLoc × (↑(Ioi (0 : ℝ≥0)) : Type) // IsExcursionTag p })
theorem BGW.StableTrees.toProbOrJunk._proof_1 : IsProbabilityMeasure (Measure.dirac junkExcursion) := by sorry
/-- Probability-measure packaging with a junk `dirac junkExcursion` branch. -/
noncomputable def BGW.StableTrees.toProbOrJunk (μ : Measure Excursion) : ProbabilityMeasure Excursion :=
  if h : IsProbabilityMeasure μ then (⟨μ, h⟩ : { μ : Measure Excursion // IsProbabilityMeasure μ })
  else (⟨Measure.dirac junkExcursion, toProbOrJunk._proof_1⟩ : { μ : Measure Excursion // IsProbabilityMeasure μ })
theorem BGW.StableTrees.unitExcursionMeasure._proof_1 : @IsScalarTower ENNReal ENNReal ENNReal (@Algebra.toSMul ENNReal ENNReal ENNReal.instCommSemiring (@CommSemiring.toSemiring ENNReal
  ENNReal.instCommSemiring) (@Algebra.id ENNReal ENNReal.instCommSemiring)) (@instSMulOfMul ENNReal (@Distrib.toMul ENNReal
  (@instDistribOfSemiring ENNReal (@CommSemiring.toSemiring ENNReal ENNReal.instCommSemiring)))) (@Algebra.toSMul ENNReal ENNReal
  ENNReal.instCommSemiring (@CommSemiring.toSemiring ENNReal ENNReal.instCommSemiring) (@Algebra.id ENNReal
  ENNReal.instCommSemiring)) := by sorry
theorem BGW.StableTrees.isCadlag_scaleLoc : ∀ (θ : ℝ) (c : (↑(Ioi (0 : ℝ)) : Type)) (f : DLoc),
  IsCadlag fun (t : ℝ≥0) => (↑c : ℝ) ^ ((1 : ℝ) / θ) * (↑f : ℝ≥0 → ℝ) (t / (↑c : ℝ).toNNReal) := by sorry
/-- Scaling of the underlying path: `t ↦ c^(1/θ) * f (t / c)`. -/
noncomputable def BGW.StableTrees.scaleLoc (θ : ℝ) (c : (↑(Ioi (0 : ℝ)) : Type)) (f : DLoc) : DLoc :=
  (⟨fun (t : ℝ≥0) => (↑c : ℝ) ^ ((1 : ℝ) / θ) * (↑f : ℝ≥0 → ℝ) (t / (↑c : ℝ).toNNReal), isCadlag_scaleLoc θ c f⟩ :
    { f : ℝ≥0 → ℝ // IsCadlag f })
/-- The path coordinate. -/
noncomputable def BGW.StableTrees.Excursion.path (e : Excursion) : DLoc := (↑e : DLoc × (↑(Ioi (0 : ℝ≥0)) : Type)).1
/-- The tagged lifetime. -/
noncomputable def BGW.StableTrees.Excursion.lifetime (e : Excursion) : ℝ≥0 := (↑(↑e : DLoc × (↑(Ioi (0 : ℝ≥0)) : Type)).2 : ℝ≥0)
theorem BGW.StableTrees.excursionScale._proof_1 : ∀ (c : Set.Ioi (0 : ℝ)) (e : Excursion), zeroRSemiring <ᵣ mulRSemiring (coeNNSemiring (Real.toNNReal c.val)) (coeNNSemiring e.lifetime) := by sorry
theorem BGW.StableTrees.Excursion.lifetime_pos : ∀ (e : Excursion), (0 : ℝ≥0) < e.lifetime := by sorry
theorem BGW.StableTrees.isExcursionTag_scale : ∀ (θ : ℝ) (c : (↑(Ioi (0 : ℝ)) : Type)) (e : Excursion),
  IsExcursionTag
    (scaleLoc θ c e.path,
      (⟨(↑c : ℝ).toNNReal * e.lifetime, mul_pos (Real.toNNReal_pos.mpr c.property) (Excursion.lifetime_pos e)⟩ :
        { x : ℝ≥0 // x ∈ Ioi (0 : ℝ≥0) })) := by sorry
/-- **Excursion scaling `S_c`**: path `c^(1/θ) e(t/c)`, tag `c * ζ`; the lifetime multiplies by `c`. -/
noncomputable def BGW.StableTrees.excursionScale (θ : ℝ) (c : (↑(Ioi (0 : ℝ)) : Type)) (e : Excursion) : Excursion :=
  (⟨(scaleLoc θ c e.path,
        (⟨(↑c : ℝ).toNNReal * e.lifetime, excursionScale._proof_1 c e⟩ : { x : ℝ≥0 // x ∈ Ioi (0 : ℝ≥0) })),
      isExcursionTag_scale θ c e⟩ :
    { p : DLoc × (↑(Ioi (0 : ℝ≥0)) : Type) // IsExcursionTag p })
theorem BGW.StableTrees.normalizeExc._proof_1 : ∀ (e : Excursion), zeroRField <ᵣ invRField (↑e.lifetime : ℝ) := by sorry
/-- **Normalization**: rescale to lifetime one, `S_{1/ζ} e`. -/
noncomputable def BGW.StableTrees.normalizeExc (θ : ℝ) (e : Excursion) : Excursion :=
  excursionScale θ (⟨(↑e.lifetime : ℝ)⁻¹, normalizeExc._proof_1 e⟩ : { x : ℝ // x ∈ Ioi (0 : ℝ) }) e
/-- `inf {t | f t < x}` (strict passage downward). -/
noncomputable def BGW.Skorokhod.DLoc.strictPassageBelow (x : ℝ) (f : DLoc) : WithTop ℝ≥0 :=
  ⨅ (t : ℝ≥0), ⨅ (_ : (↑f : ℝ≥0 → ℝ) t < x), (↑t : WithTop ℝ≥0)
/-- The first passage time below `-x`, as a process indexed by the level `x ≥ 0`. -/
noncomputable def BGW.StableTrees.firstPassageBelow (x : ℝ≥0) (f : DLoc) : WithTop ℝ≥0 := DLoc.strictPassageBelow (-(↑x : ℝ)) f
/-- The `ℝ≥0`-valued left limit `T_{x-} = sup_{y<x} T_y` of the passage process, with `T_{0-} = 0`; junk `0` where some
`T_y = ⊤` (null set). -/
noncomputable def BGW.StableTrees.passageTimeMinus (x : ℝ≥0) (f : DLoc) : ℝ≥0 :=
  WithTop.untopD (0 : ℝ≥0) (⨆ (y : (↑(Iio x) : Type)), firstPassageBelow (↑y : ℝ≥0) f)
/-- The `ℝ≥0`-valued passage time (junk value `0` on `{T_x = ⊤}`, a null set). -/
noncomputable def BGW.StableTrees.passageTime (x : ℝ≥0) (f : DLoc) : ℝ≥0 := WithTop.untopD (0 : ℝ≥0) (firstPassageBelow x f)
/-- The set of positive **jump levels** of the passage process: `{x > 0 | T_{x-} < T_x}`. -/
noncomputable def BGW.StableTrees.passageJumpSet (f : DLoc) : Set ℝ≥0 := {x : ℝ≥0 | (0 : ℝ≥0) < x ∧ passageTimeMinus x f < passageTime x f}
/-- Cut-validity: `g<d`, `f d=f g`, and `f≥f g` on `[g,d]`; the base is the post-jump value `f g`. -/
noncomputable def BGW.StableTrees.cutValid (g : ℝ≥0) (d : ℝ≥0) (f : DLoc) : Prop :=
  g < d ∧ (↑f : ℝ≥0 → ℝ) d = (↑f : ℝ≥0 → ℝ) g ∧ ∀ (t : ℝ≥0), g ≤ t → t ≤ d → (↑f : ℝ≥0 → ℝ) g ≤ (↑f : ℝ≥0 → ℝ) t
theorem BGW.StableTrees.isCadlag_stopLoc : ∀ (a : ℝ≥0) (f : DLoc), IsCadlag fun (t : ℝ≥0) => (↑f : ℝ≥0 → ℝ) (min t a) := by sorry
/-- Stopping a local path at a deterministic time: `t ↦ f (min t a)`. -/
noncomputable def BGW.StableTrees.stopLoc (a : ℝ≥0) (f : DLoc) : DLoc :=
  (⟨fun (t : ℝ≥0) => (↑f : ℝ≥0 → ℝ) (min t a), isCadlag_stopLoc a f⟩ : { f : ℝ≥0 → ℝ // IsCadlag f })
theorem BGW.Skorokhod.DLoc.shift._proof_2 : ∀ (s : ℝ≥0) (f : DLoc), IsCadlag fun (u : ℝ≥0) => (↑f : ℝ≥0 → ℝ) (s + u) - (↑f : ℝ≥0 → ℝ) s := by sorry
/-- Centered shift: `u ↦ f (s + u) - f s`. -/
noncomputable def BGW.Skorokhod.DLoc.shift (s : ℝ≥0) (f : DLoc) : DLoc :=
  (⟨fun (u : ℝ≥0) => (↑f : ℝ≥0 → ℝ) (s + u) - (↑f : ℝ≥0 → ℝ) s, DLoc.shift._proof_2 s f⟩ : { f : ℝ≥0 → ℝ // IsCadlag f })
/-- The path of the cut of `f` between times `g` and `d`: `t ↦ f (min (g+t) d) - f g` (for `g ≤ d`). -/
noncomputable def BGW.StableTrees.cutPath (g : ℝ≥0) (d : ℝ≥0) (f : DLoc) : DLoc := stopLoc (d - g) (DLoc.shift g f)
theorem BGW.StableTrees.excursionCut._proof_1 : ∀ (g d : NNReal) (f : DLoc), cutValid g d f → @LT.lt NNReal (@Preorder.toLT NNReal (@PartialOrder.toPreorder NNReal
  NNReal.instPartialOrder)) (@OfNat.ofNat NNReal (nat_lit 0) (@Zero.toOfNat0 NNReal (@AddZero.toZero NNReal (@AddZeroClass.toAddZero
  NNReal (@AddMonoid.toAddZeroClass NNReal (@AddCommMonoid.toAddMonoid NNReal (@Semiring.toAddCommMonoid NNReal
  NNReal.instSemiring))))))) (@HSub.hSub NNReal NNReal NNReal (@instHSub NNReal NNReal.instSub) d g) := by sorry
theorem BGW.StableTrees.isExcursionTag_cutPath : ∀ {g d : ℝ≥0} {f : DLoc} (h : cutValid g d f),
  IsExcursionTag (cutPath g d f, (⟨d - g, tsub_pos_of_lt h.left⟩ : { x : ℝ≥0 // x ∈ Ioi (0 : ℝ≥0) })) := by sorry
/-- Cut `f` on `[g,d]` to path `f(min(g+t,d))-f g` and lifetime `d-g` when valid; junk otherwise. The cut is based at
the post-jump value, so it starts without a jump out of the infimum. -/
noncomputable def BGW.StableTrees.excursionCut (g : ℝ≥0) (d : ℝ≥0) (f : DLoc) : Excursion :=
  if h : cutValid g d f then
    (⟨(cutPath g d f, (⟨d - g, excursionCut._proof_1 g d f h⟩ : { x : ℝ≥0 // x ∈ Ioi (0 : ℝ≥0) })),
        isExcursionTag_cutPath h⟩ :
      { p : DLoc × (↑(Ioi (0 : ℝ≥0)) : Type) // IsExcursionTag p })
  else junkExcursion
/-- The excursion attached to the jump level `x`: the excursion cut `excursionCut` of `f` on `(T_{x-}, T_x)`. -/
noncomputable def BGW.StableTrees.jumpExcursion (x : ℝ≥0) (f : DLoc) : Excursion := excursionCut (passageTimeMinus x f) (passageTime x f) f
/-- **The marked excursion point measure** on `ℝ≥0 × Excursion`: `∑_{x ∈ J f} δ_{(x, jumpExcursion x f)}` (zero measure
when `J f` is not countable). -/
noncomputable def BGW.StableTrees.excursionPointMeasure (f : DLoc) : Measure (ℝ≥0 × Excursion) :=
  if (passageJumpSet f).Countable then
    Measure.sum fun (x : (↑(passageJumpSet f) : Type)) => Measure.dirac ((↑x : ℝ≥0), jumpExcursion (↑x : ℝ≥0) f)
  else (0 : Measure (ℝ≥0 × Excursion))
theorem BGW.StableTrees.stableLocalLaw._proof_2 : ((1 : ℕ) + (1 : ℕ)).AtLeastTwo := by sorry
theorem BGW.Skorokhod.restrict._proof_2 : ∀ {T a : ℝ}, a ≤ T → ∀ (t : (↑(Icc (0 : ℝ) a) : Type)), (0 : ℝ) ≤ᵣ (↑t : ℝ) ∧ (↑t : ℝ) ≤ᵣ T := by sorry
theorem BGW.Skorokhod.restrict._proof_1.{u_1} : ∀ {T : ℝ} {E : Type u_1} [inst : TopologicalSpace E] {a : ℝ} (haT : a ≤ T) (f : D T E),
  IsCadlag fun (t : (↑(Icc (0 : ℝ) a) : Type)) =>
    (f : (↑(Icc (0 : ℝ) T) : Type) → E)
      (⟨(↑t : ℝ), (⟨t.property.left, LE.le.trans t.property.right haT⟩ : (0 : ℝ) ≤ᵣ (↑t : ℝ) ∧ (↑t : ℝ) ≤ᵣ T)⟩ :
        { x : ℝ // x ∈ Icc (0 : ℝ) T }) := by sorry
/-- Restriction of a path on `[0,T]` to `[0,a]` (C6.2). -/
noncomputable def BGW.Skorokhod.restrict.{u_1} {T : ℝ} {E : Type u_1} [arg_inst_0 : TopologicalSpace E] {a : ℝ} (haT : a ≤ T) (f : D T E) : D a E :=
  {
    toFun := fun (t : (↑(Icc (0 : ℝ) a) : Type)) =>
      (f : (↑(Icc (0 : ℝ) T) : Type) → E) (⟨(↑t : ℝ), restrict._proof_2 haT t⟩ : { x : ℝ // x ∈ Icc (0 : ℝ) T }),
    isCadlag' := restrict._proof_1 haT f : D a E }
theorem BGW.Skorokhod.CompatiblePaths._proof_1 : ∀ (b : ℕ → ℝ), StrictMono b → ∀ (n : ℕ), b n ≤ᵣ b n.succ := by sorry
/-- Compatible horizon families with adjacent restrictions agreeing. -/
noncomputable def BGW.Skorokhod.CompatiblePaths (b : ℕ → ℝ) (hb : StrictMono b) : Type :=
  { p : (n : ℕ) → D (b n) ℝ // ∀ (n : ℕ), Skorokhod.restrict (CompatiblePaths._proof_1 b hb n) (p (n + (1 : ℕ))) = p n }
attribute [reducible] BGW.Skorokhod.CompatiblePaths
theorem BGW.Skorokhod.strictMono_succHorizon : StrictMono fun (n : ℕ) => (↑n : ℝ) + (1 : ℝ) := by sorry
/-- The compatible-family subtype carries its subspace measurable structure. -/
noncomputable def BGW.Skorokhod.instMeasurableSpaceCompatiblePaths (b : ℕ → ℝ) (hb : StrictMono b) : MeasurableSpace (CompatiblePaths b hb) :=
  (inferInstance : MeasurableSpace (Subtype _))
attribute [instance, instance_reducible] BGW.Skorokhod.instMeasurableSpaceCompatiblePaths
/-- The coordinate map of the compatible-family subtype. -/
noncomputable def BGW.Skorokhod.CompatiblePaths.coord {b : ℕ → ℝ} {hb : StrictMono b} (n : ℕ) (p : CompatiblePaths b hb) : D (b n) ℝ :=
  (↑p : (n : ℕ) → D (b n) ℝ) n
theorem BGW.StableTrees.stableProcessLaw._proof_1 : ((1 : ℕ) + (1 : ℕ)).AtLeastTwo := by sorry
/-- The stable law at time `t > 0`, image of `stableLaw θ` under `x ↦ t^{1/θ} x` (C15.4). -/
noncomputable def BGW.StableTrees.stableLawAt (θ : ℝ) (t : ℝ) : ProbabilityMeasure ℝ := (stableLaw θ).map fun (x : ℝ) => t ^ ((1 : ℝ) / θ) * x
namespace BGW.StableTrees
/-- `P` is a law of a spectrally positive θ-stable Lévy process on `[0,T]`, expressed through its finite-dimensional
increments and its initial value. -/
structure IsStableLevyLaw (θ T : ℝ) (P : ProbabilityMeasure (D T ℝ)) : Prop where
  /-- The path starts at zero almost surely whenever the horizon is nonnegative. -/
  start : ∀ h : 0 ≤ T, ∀ᵐ f : D T ℝ ∂(P : Measure (D T ℝ)), f ⟨0, le_rfl, h⟩ = 0
  /-- Increments along increasing times starting at zero have independent stable laws. -/
  increments : ∀ (k : ℕ) (t : Fin (k + 1) → Set.Icc (0 : ℝ) T),
    StrictMono t → (t 0 : ℝ) = 0 →
    Measure.map (fun f : D T ℝ => fun i : Fin k => f (t i.succ) - f (t i.castSucc))
      (P : Measure (D T ℝ)) =
      Measure.pi (fun i : Fin k =>
        (stableLawAt θ ((t i.succ : ℝ) - t i.castSucc) : Measure ℝ))
end BGW.StableTrees
theorem BGW.StableTrees.stableProcessLaw._proof_2 : ∀ (θ T : ℝ), ((1 : ℝ) < θ ∧ θ ≤ twoReal[BGW.StableTrees.stableProcessLaw._proof_1]) ∧ (0 : ℝ) < T → ∃ (P : ProbabilityMeasure (D T ℝ)), IsStableLevyLaw θ T P := by sorry
theorem BGW.Skorokhod.ofContinuous._proof_1.{u_1} : ∀ {T : ℝ} {E : Type u_1} [inst : TopologicalSpace E] (f : C((↑(Icc (0 : ℝ) T) : Type), E)),
  IsCadlag (⇑f : (↑(Icc (0 : ℝ) T) : Type) → E) := by sorry
/-- A continuous path, seen as a càdlàg path (C5). -/
noncomputable def BGW.Skorokhod.ofContinuous.{u_1} {T : ℝ} {E : Type u_1} [arg_inst_0 : TopologicalSpace E] (f : C((↑(Icc (0 : ℝ) T) : Type), E)) : D T E :=
  { toFun := (⇑f : (↑(Icc (0 : ℝ) T) : Type) → E), isCadlag' := ofContinuous._proof_1 f : D T E }
theorem BGW.StableTrees.stableProcessLaw._proof_3 : ∀ (T : ℝ), IsProbabilityMeasure (Measure.dirac (ofContinuous (ContinuousMap.const (↑(Icc (0 : ℝ) T) : Type) (0 : ℝ)))) := by sorry
/-- The law of the spectrally positive `θ`-stable Lévy process on `[0,T]`; chosen after existence is proved. Junk value
(Dirac at the zero path) unless `1 < θ ≤ 2` and `0 < T`. -/
noncomputable def BGW.StableTrees.stableProcessLaw (θ : ℝ) (T : ℝ) : ProbabilityMeasure (D T ℝ) :=
  if h : ((1 : ℝ) < θ ∧ θ ≤ twoReal[BGW.StableTrees.stableProcessLaw._proof_1]) ∧ (0 : ℝ) < T then Classical.choose (stableProcessLaw._proof_2 θ T h)
  else
    (⟨Measure.dirac (ofContinuous (ContinuousMap.const (↑(Icc (0 : ℝ) T) : Type) (0 : ℝ))), stableProcessLaw._proof_3 T⟩ :
      { μ : Measure (D T ℝ) // IsProbabilityMeasure μ })
theorem BGW.StableTrees.stableLocalLaw._proof_3 : ∀ (θ : ℝ),
  (1 : ℝ) < θ ∧ θ ≤ twoReal[BGW.StableTrees.stableLocalLaw._proof_2] →
    ∃ (x : ProbabilityMeasure (CompatiblePaths (fun (n : ℕ) => (↑n : ℝ) + (1 : ℝ)) strictMono_succHorizon)),
      ∀ (n : ℕ),
        Measure.map (CompatiblePaths.coord n)
            (↑x : Measure (CompatiblePaths (fun (n : ℕ) => (↑n : ℝ) + (1 : ℝ)) strictMono_succHorizon)) =
          (↑(stableProcessLaw θ ((↑n : ℝ) + (1 : ℝ))) : Measure (D ((↑n : ℝ) + (1 : ℝ)) ℝ)) := by sorry
theorem BGW.Skorokhod.DLoc.toCompatible._proof_3 : ∀ (n : ℕ), (↑n : ℝ) + (1 : ℝ) ≤ᵣ (↑n.succ : ℝ) + (1 : ℝ) := by sorry
theorem BGW.Skorokhod.DLoc.restrict._proof_2 : ∀ (T : ℝ≥0) (t : (↑(Icc (0 : ℝ) (↑T : ℝ)) : Type)), (0 : ℝ) ≤ᵣ (↑t : ℝ) := by sorry
theorem BGW.Skorokhod.DLoc.restrict._proof_1 : ∀ (T : ℝ≥0) (f : DLoc),
  IsCadlag fun (t : (↑(Icc (0 : ℝ) (↑T : ℝ)) : Type)) =>
    (↑f : ℝ≥0 → ℝ) (⟨(↑t : ℝ), t.property.left⟩ : { r : ℝ // (0 : ℝ) ≤ r }) := by sorry
/-- Restriction to `[0, T]`, as an element of the compact path space. -/
noncomputable def BGW.Skorokhod.DLoc.restrict (T : ℝ≥0) (f : DLoc) : D (↑T : ℝ) ℝ :=
  {
    toFun := fun (t : (↑(Icc (0 : ℝ) (↑T : ℝ)) : Type)) =>
      (↑f : ℝ≥0 → ℝ) (⟨(↑t : ℝ), DLoc.restrict._proof_2 T t⟩ : { r : ℝ // (0 : ℝ) ≤ r }),
    isCadlag' := DLoc.restrict._proof_1 T f : D (↑T : ℝ) ℝ }
theorem BGW.Skorokhod.DLoc.toCompatible._proof_1 : ∀ (n : ℕ), (0 : ℝ) ≤ (↑n : ℝ) + (1 : ℝ) := by sorry
theorem BGW.Skorokhod.DLoc.toCompatible._proof_2 : ∀ (f : DLoc) (n : Nat), @Eq (paths[(unitHorizons n)]) (@Skorokhod.restrict (unitHorizons (Nat.succ n)) Real
  (@UniformSpace.toTopologicalSpace Real (@PseudoMetricSpace.toUniformSpace Real Real.pseudoMetricSpace)) (unitHorizons n)
  (CompatiblePaths._proof_1 unitHorizons strictMono_succHorizon n) ((fun n => DLoc.restrict (@Subtype.mk Real (fun r => @LE.le Real
  Real.instLE (@OfNat.ofNat Real (nat_lit 0) (@Zero.toOfNat0 Real Real.instZero)) r) (@HAdd.hAdd Real Real Real (@instHAdd Real
  Real.instAdd) (@Nat.cast Real Real.instNatCast n) (@OfNat.ofNat Real (nat_lit 1) (@One.toOfNat1 Real Real.instOne)))
  (DLoc.toCompatible._proof_1 n)) f) (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n (@OfNat.ofNat Nat (nat_lit 1)
  (instOfNatNat (nat_lit 1)))))) ((fun n => DLoc.restrict (@Subtype.mk Real (fun r => @LE.le Real Real.instLE (@OfNat.ofNat Real
  (nat_lit 0) (@Zero.toOfNat0 Real Real.instZero)) r) (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (@Nat.cast Real
  Real.instNatCast n) (@OfNat.ofNat Real (nat_lit 1) (@One.toOfNat1 Real Real.instOne))) (DLoc.toCompatible._proof_1 n)) f) n) := by sorry
/-- The compatible integer-horizon family of a local path (horizons `n + 1`). -/
noncomputable def BGW.Skorokhod.DLoc.toCompatible : DLoc → CompatiblePaths (fun (n : ℕ) => (↑n : ℝ) + (1 : ℝ)) strictMono_succHorizon :=
  fun f => @Subtype.mk ((n : Nat) → paths[(unitHorizons n)]) (fun p => ∀ (n : Nat), @Eq (paths[(unitHorizons n)]) (@Skorokhod.restrict
    (unitHorizons (Nat.succ n)) Real (@UniformSpace.toTopologicalSpace Real (@PseudoMetricSpace.toUniformSpace Real
    Real.pseudoMetricSpace)) (unitHorizons n) (DLoc.toCompatible._proof_3 n) (p (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n
    (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))) (p n)) (fun n => DLoc.restrict (@Subtype.mk Real (fun r => @LE.le
    Real Real.instLE (@OfNat.ofNat Real (nat_lit 0) (@Zero.toOfNat0 Real Real.instZero)) r) (@HAdd.hAdd Real Real Real (@instHAdd Real
    Real.instAdd) (@Nat.cast Real Real.instNatCast n) (@OfNat.ofNat Real (nat_lit 1) (@One.toOfNat1 Real Real.instOne)))
    (DLoc.toCompatible._proof_1 n)) f) (DLoc.toCompatible._proof_2 f)
theorem BGW.Skorokhod.DLoc.glue._proof_3 : ∀ (t : ℝ≥0), (0 : ℝ) ≤ᵣ (↑t : ℝ) ∧ (↑t : ℝ) ≤ᵣ (↑⌈(↑t : ℝ)⌉₊ : ℝ) + (1 : ℝ) := by sorry
theorem BGW.Skorokhod.DLoc.glue._proof_1 : ∀ (t : ℝ≥0), (↑t : ℝ) ≤ᵣ (fun (n : ℕ) => (↑n : ℝ) + (1 : ℝ)) ⌈(↑t : ℝ)⌉₊ := by sorry
theorem BGW.Skorokhod.DLoc.glue._proof_2 : ∀ (p : CompatiblePaths (fun (n : ℕ) => (↑n : ℝ) + (1 : ℝ)) strictMono_succHorizon),
  IsCadlag fun (t : ℝ≥0) =>
    ((↑p : (n : ℕ) → D ((fun (n : ℕ) => (↑n : ℝ) + (1 : ℝ)) n) ℝ) ⌈(↑t : ℝ)⌉₊ :
        (↑(Icc (0 : ℝ) ((fun (n : ℕ) => (↑n : ℝ) + (1 : ℝ)) ⌈(↑t : ℝ)⌉₊)) : Type) → ℝ)
      (⟨(↑t : ℝ),
          (⟨t.property, DLoc.glue._proof_1 t⟩ :
            (0 : ℝ) ≤ᵣ (↑t : ℝ) ∧ (↑t : ℝ) ≤ᵣ (fun (n : ℕ) => (↑n : ℝ) + (1 : ℝ)) ⌈(↑t : ℝ)⌉₊)⟩ :
        { x : ℝ // x ∈ Icc (0 : ℝ) ((fun (n : ℕ) => (↑n : ℝ) + (1 : ℝ)) ⌈(↑t : ℝ)⌉₊) }) := by sorry
/-- Gluing: a compatible integer-horizon family determines a local càdlàg path. -/
noncomputable def BGW.Skorokhod.DLoc.glue : CompatiblePaths (fun (n : ℕ) => (↑n : ℝ) + (1 : ℝ)) strictMono_succHorizon → DLoc :=
  fun p => @Subtype.mk (NNReal → Real) (fun f => @IsCadlag NNReal Real NNReal.instTopologicalSpace (@PartialOrder.toPreorder NNReal
    NNReal.instPartialOrder) (@UniformSpace.toTopologicalSpace Real (@PseudoMetricSpace.toUniformSpace Real Real.pseudoMetricSpace))
    f) (fun t => @DFunLike.coe (paths[(unitHorizons (@Nat.ceil Real Real.semiring Real.partialOrder (@FloorRing.toFloorSemiring Real
    Real.instRing Real.linearOrder Real.instFloorRing) (NNReal.toReal t)))]) (@Elem Real (@Icc Real Real.instPreorder (@OfNat.ofNat
    Real (nat_lit 0) (@Zero.toOfNat0 Real Real.instZero)) (unitHorizons (@Nat.ceil Real Real.semiring Real.partialOrder
    (@FloorRing.toFloorSemiring Real Real.instRing Real.linearOrder Real.instFloorRing) (NNReal.toReal t))))) (fun x => Real)
    (@instFunLikeDElemRealIccOfNat (unitHorizons (@Nat.ceil Real Real.semiring Real.partialOrder (@FloorRing.toFloorSemiring Real
    Real.instRing Real.linearOrder Real.instFloorRing) (NNReal.toReal t))) Real (@UniformSpace.toTopologicalSpace Real
    (@PseudoMetricSpace.toUniformSpace Real Real.pseudoMetricSpace))) (@Subtype.val ((n : Nat) → paths[(unitHorizons n)]) (fun p => ∀
    (n : Nat), @Eq (paths[(unitHorizons n)]) (@Skorokhod.restrict (unitHorizons (Nat.succ n)) Real (@UniformSpace.toTopologicalSpace
    Real (@PseudoMetricSpace.toUniformSpace Real Real.pseudoMetricSpace)) (unitHorizons n) (DLoc.toCompatible._proof_3 n) (p
    (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))) (p n)) p
    (@Nat.ceil Real Real.semiring Real.partialOrder (@FloorRing.toFloorSemiring Real Real.instRing Real.linearOrder
    Real.instFloorRing) (NNReal.toReal t))) (@Subtype.mk Real (fun x => @Membership.mem Real (Set Real) (@Set.instMembership Real)
    (@Icc Real Real.instPreorder (@OfNat.ofNat Real (nat_lit 0) (@Zero.toOfNat0 Real Real.instZero)) (unitHorizons (@Nat.ceil Real
    Real.semiring Real.partialOrder (@FloorRing.toFloorSemiring Real Real.instRing Real.linearOrder Real.instFloorRing) (NNReal.toReal
    t)))) x) (NNReal.toReal t) (DLoc.glue._proof_3 t))) (DLoc.glue._proof_2 p)
theorem BGW.Skorokhod.DLoc.glue_toCompatible : ∀ (f : DLoc), DLoc.glue f.toCompatible = f := by sorry
theorem BGW.Skorokhod.DLoc.toCompatible_glue : ∀ (p : CompatiblePaths (fun (n : ℕ) => (↑n : ℝ) + (1 : ℝ)) strictMono_succHorizon), (DLoc.glue p).toCompatible = p := by sorry
theorem BGW.Skorokhod.DLoc.measurableEquivCompatible._proof_1 : Measurable
  (⇑{ toFun := DLoc.toCompatible, invFun := DLoc.glue, left_inv := DLoc.glue_toCompatible,
        right_inv := DLoc.toCompatible_glue :
        DLoc ≃ CompatiblePaths (fun (n : ℕ) => (↑n : ℝ) + (1 : ℝ)) strictMono_succHorizon } :
    DLoc → CompatiblePaths (fun (n : ℕ) => (↑n : ℝ) + (1 : ℝ)) strictMono_succHorizon) := by sorry
theorem BGW.Skorokhod.DLoc.measurableEquivCompatible._proof_2 : Measurable
  (⇑{ toFun := DLoc.toCompatible, invFun := DLoc.glue, left_inv := DLoc.glue_toCompatible,
          right_inv := DLoc.toCompatible_glue :
          DLoc ≃ CompatiblePaths (fun (n : ℕ) => (↑n : ℝ) + (1 : ℝ)) strictMono_succHorizon }.symm :
    CompatiblePaths (fun (n : ℕ) => (↑n : ℝ) + (1 : ℝ)) strictMono_succHorizon → DLoc) := by sorry
/-- `DLoc` is measurably equivalent to the compatible families of restrictions to `[0, n + 1]`, so laws constructed in
`PathLawFamily` transfer to `DLoc`. -/
noncomputable def BGW.Skorokhod.DLoc.measurableEquivCompatible : DLoc ≃ᵐ CompatiblePaths (fun (n : ℕ) => (↑n : ℝ) + (1 : ℝ)) strictMono_succHorizon :=
  let __Equiv : DLoc ≃ CompatiblePaths (fun (n : ℕ) => (↑n : ℝ) + (1 : ℝ)) strictMono_succHorizon :=
    { toFun := DLoc.toCompatible, invFun := DLoc.glue, left_inv := DLoc.glue_toCompatible,
      right_inv := DLoc.toCompatible_glue :
      DLoc ≃ CompatiblePaths (fun (n : ℕ) => (↑n : ℝ) + (1 : ℝ)) strictMono_succHorizon };
  { toEquiv := __Equiv, measurable_toFun := DLoc.measurableEquivCompatible._proof_1,
    measurable_invFun := DLoc.measurableEquivCompatible._proof_2 :
    DLoc ≃ᵐ CompatiblePaths (fun (n : ℕ) => (↑n : ℝ) + (1 : ℝ)) strictMono_succHorizon }
theorem BGW.Skorokhod.DLoc.zero._proof_1 : IsCadlag fun (x : ℝ≥0) => (0 : ℝ) := by sorry
/-- The zero local path. -/
noncomputable def BGW.Skorokhod.DLoc.zero : DLoc := (⟨fun (x : ℝ≥0) => (0 : ℝ), DLoc.zero._proof_1⟩ : { f : ℝ≥0 → ℝ // IsCadlag f })
theorem BGW.StableTrees.stableLocalLaw._proof_4 : IsProbabilityMeasure (Measure.dirac DLoc.zero) := by sorry
/-- For `1<θ≤2`, the unique local càdlàg path law with integer-horizon marginals `stableProcessLaw θ (n+1)`. It is
transported from compatible paths; outside that index range it is the zero-path Dirac law. -/
noncomputable def BGW.StableTrees.stableLocalLaw (θ : ℝ) : ProbabilityMeasure DLoc :=
  if hθ : (1 : ℝ) < θ ∧ θ ≤ twoReal[BGW.StableTrees.stableLocalLaw._proof_2] then
    (Classical.choose (stableLocalLaw._proof_3 θ hθ)).map
      (⇑DLoc.measurableEquivCompatible.symm :
        CompatiblePaths (fun (n : ℕ) => (↑n : ℝ) + (1 : ℝ)) strictMono_succHorizon → DLoc)
  else (⟨Measure.dirac DLoc.zero, stableLocalLaw._proof_4⟩ : { μ : Measure DLoc // IsProbabilityMeasure μ })
/-- **The excursion measure** `N A = ∫⁻ f, μ f ((0,1] × A) ∂P`, `P = stableLocalLaw θ`, as the `Measure.join` of the law
of `f ↦ ((μ f) ↾ (0,1] × univ).map Prod.snd`. -/
noncomputable def BGW.StableTrees.excursionMeasure (θ : ℝ) : Measure Excursion :=
  (Measure.map
      (fun (f : DLoc) => Measure.map Prod.snd ((excursionPointMeasure f).restrict (Ioc (0 : ℝ≥0) (1 : ℝ≥0) ×ˢ univ)))
      (↑(stableLocalLaw θ) : Measure DLoc)).join
/-- The tail `N ↾ {ζ > a}` of the excursion measure. -/
noncomputable def BGW.StableTrees.excursionTail (θ : ℝ) (a : ℝ) : Measure Excursion :=
  (excursionMeasure θ).restrict {e : Excursion | a < (↑e.lifetime : ℝ)}
/-- Explicit normalized unit measure: `Γ(1-1/θ) • (normalizeExc θ)_* (N ↾ {ζ > 1})`. The coefficient is `N(ζ > 1)⁻¹`;
this is a normalized restriction, not a conditioning on `{ζ = 1}`. -/
noncomputable def BGW.StableTrees.unitExcursionMeasure : ℝ → Measure Excursion :=
  fun θ => @HSMul.hSMul ENNReal (@Measure Excursion instMeasurableSpaceExcursion) (@Measure Excursion instMeasurableSpaceExcursion)
    (@instHSMul ENNReal (@Measure Excursion instMeasurableSpaceExcursion) (@Measure.instSMul Excursion ENNReal
    instMeasurableSpaceExcursion (@instSMulOfMul ENNReal (@Distrib.toMul ENNReal (@instDistribOfSemiring ENNReal
    (@CommSemiring.toSemiring ENNReal ENNReal.instCommSemiring)))) unitExcursionMeasure._proof_1)) (ENNReal.ofReal (Real.Gamma
    (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@OfNat.ofNat Real (nat_lit 1) (@One.toOfNat1 Real Real.instOne))
    (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real (nat_lit 1)
    (@One.toOfNat1 Real Real.instOne)) θ)))) (@Measure.map Excursion Excursion instMeasurableSpaceExcursion
    instMeasurableSpaceExcursion (normalizeExc θ) (excursionTail θ (@OfNat.ofNat Real (nat_lit 1) (@One.toOfNat1 Real Real.instOne))))
/-- **Unit excursion law**; agrees with `unitExcursionMeasure` for `1 < θ ≤ 2`. Outside that range it is only a
totalized probability measure. -/
noncomputable def BGW.StableTrees.unitExcursionLaw (θ : ℝ) : ProbabilityMeasure Excursion := toProbOrJunk (unitExcursionMeasure θ)
/-- Restriction of an excursion to the horizon `[0, T]`, as a path in the sealed compact space. -/
noncomputable def BGW.StableTrees.excursionRestrict (T : ℝ≥0) (e : Excursion) : D (↑T : ℝ) ℝ := DLoc.restrict T e.path
theorem BGW.StableTrees.heightRestrict._proof_1 : ∀ (T : ℝ≥0) (t : (↑(Icc (0 : ℝ) (↑T : ℝ)) : Type)), (0 : ℝ) ≤ᵣ (↑t : ℝ) := by sorry
theorem BGW.StableTrees.heightRestrict._proof_2 : ∀ (T : ℝ≥0) (x : { x : ℝ // x ∈ Icc (0 : ℝ) (↑T : ℝ) }), (0 : ℝ) ≤ᵣ (↑x : ℝ) := by sorry
theorem BGW.StableTrees.heightRestrict._proof_3 : ∀ (T : ℝ≥0),
  Continuous fun (x : { x : ℝ // x ∈ Icc (0 : ℝ) (↑T : ℝ) }) =>
    (⟨(↑x : ℝ), heightRestrict._proof_2 T x⟩ : { r : ℝ // (0 : ℝ) ≤ r }) := by sorry
/-- Restriction of a continuous function on `ℝ≥0` to `[0,T]`. -/
noncomputable def BGW.StableTrees.heightRestrict (T : ℝ≥0) (g : C(ℝ≥0, ℝ)) : C((↑(Icc (0 : ℝ) (↑T : ℝ)) : Type), ℝ) :=
  g.comp
    {
      toFun := fun (t : (↑(Icc (0 : ℝ) (↑T : ℝ)) : Type)) =>
        (⟨(↑t : ℝ), heightRestrict._proof_1 T t⟩ : { r : ℝ // (0 : ℝ) ≤ r }),
      continuous_toFun := heightRestrict._proof_3 T : C((↑(Icc (0 : ℝ) (↑T : ℝ)) : Type), ℝ≥0) }
/-- The interval infimum `I^s_t = inf_{[s ∧ t, t]} X`. -/
noncomputable def BGW.StableTrees.futureInf (f : DLoc) (t : ℝ≥0) (s : ℝ≥0) : ℝ := ⨅ (u : (↑(Icc (min s t) t) : Type)), (↑f : ℝ≥0 → ℝ) (↑u : ℝ≥0)
/-- Minimal-exploration occupation approximation `ε⁻¹ Leb{s ≤ t | X_s < I^s_t + ε}`. -/
noncomputable def BGW.StableTrees.heightApprox (ε : ℝ) (f : DLoc) (t : ℝ≥0) : ℝ :=
  ε⁻¹ *
    ((volume : Set ℝ → ℝ≥0∞)
        {s : ℝ | (0 : ℝ) ≤ s ∧ s ≤ (↑t : ℝ) ∧ (↑f : ℝ≥0 → ℝ) s.toNNReal < futureInf f t s.toNNReal + ε}).toReal
/-- Running supremum `S_t = sup_{u ≤ t} X_u`. -/
noncomputable def BGW.StableTrees.supRunning (f : DLoc) (t : ℝ≥0) : ℝ := ⨆ (u : (↑(Iic t) : Type)), (↑f : ℝ≥0 → ℝ) (↑u : ℝ≥0)
/-- The reflected-at-supremum process `S_t - X_t`. -/
noncomputable def BGW.StableTrees.supReflected (f : DLoc) (t : ℝ≥0) : ℝ := supRunning f t - (↑f : ℝ≥0 → ℝ) t
/-- Occupation approximation `ε⁻¹ · Leb{s ≤ t | S_s - X_s < ε}`. -/
noncomputable def BGW.StableTrees.supOccupation (ε : ℝ) (f : DLoc) (t : ℝ≥0) : ℝ :=
  ε⁻¹ * ((volume : Set ℝ → ℝ≥0∞) {s : ℝ | (0 : ℝ) ≤ s ∧ s ≤ (↑t : ℝ) ∧ supReflected f s.toNNReal < ε}).toReal
theorem BGW.StableTrees.supEps._proof_1 : ((1 : ℕ) + (1 : ℕ)).AtLeastTwo := by sorry
/-- A deterministic sequence is a *simultaneous occupation sequence*: positive, strictly decreasing to `0`, and almost
surely the approximations converge at every time at once. -/
noncomputable def BGW.StableTrees.IsSupOccupationSeq (θ : ℝ) (ε : ℕ → ℝ) : Prop :=
  (∀ (k : ℕ), (0 : ℝ) < ε k) ∧
    StrictAnti ε ∧
      Tendsto ε atTop (𝓝 (0 : ℝ)) ∧
        ∀ᵐ (f : DLoc) ∂(↑(stableLocalLaw θ) : Measure DLoc),
          ∀ (t : ℝ≥0), ∃ (ℓ : ℝ), Tendsto (fun (k : ℕ) => supOccupation (ε k) f t) atTop (𝓝 ℓ)
theorem BGW.StableTrees.exists_isSupOccupationSeq : ∀ {θ : ℝ}, (1 : ℝ) < θ ∧ θ ≤ (2 : ℝ) → ∃ (ε : ℕ → ℝ), IsSupOccupationSeq θ ε := by sorry
/-- The chosen sequence `ε_k ↓ 0`. -/
noncomputable def BGW.StableTrees.supEps (θ : ℝ) : ℕ → ℝ :=
  if h : (1 : ℝ) < θ ∧ θ ≤ twoReal[BGW.StableTrees.supEps._proof_1] then Classical.choose (exists_isSupOccupationSeq h)
  else fun (k : ℕ) => (1 : ℝ) / ((↑k : ℝ) + (1 : ℝ))
/-- The supremum local time `L^S = M`, the limsup of the occupation approximations along `supEps θ` (real-valued, junk
`0` where the occupations are unbounded). -/
noncomputable def BGW.StableTrees.supLocalTime (θ : ℝ) (f : DLoc) (t : ℝ≥0) : ℝ := limsup (fun (k : ℕ) => supOccupation (supEps θ k) f t) atTop
/-- The time-reversed process at `t`: `u ↦ X_t - X_{(t - u ∧ t)-}` (constant after `t`). -/
noncomputable def BGW.StableTrees.reversedPath (t : ℝ≥0) (f : DLoc) (arg_a_0 : ℝ≥0) : ℝ :=
  (↑f : ℝ≥0 → ℝ) t - Function.leftLim (↑f : ℝ≥0 → ℝ) (t - min arg_a_0 t)
/-- The reversed process at `t` as a `DLoc` element (junk `DLoc.zero` never occurs). -/
noncomputable def BGW.StableTrees.reversedAt (t : ℝ≥0) (f : DLoc) : DLoc :=
  if h : IsCadlag (reversedPath t f) then (⟨reversedPath t f, h⟩ : { f : ℝ≥0 → ℝ // IsCadlag f }) else DLoc.zero
/-- **The height** `H_t = M_t(reversed process at t)`: the H01 supremum local time of the time-reversed process. -/
noncomputable def BGW.StableTrees.height (θ : ℝ) (f : DLoc) (t : ℝ≥0) : ℝ := supLocalTime θ (reversedAt t f) t
theorem BGW.StableTrees.IsUniversalHeightSeq._proof_1 : @OuterMeasureClass (@Measure Real (@MeasureSpace.toMeasurableSpace Real Real.measureSpace)) Real (@Measure.instFunLike Real
  (@MeasureSpace.toMeasurableSpace Real Real.measureSpace)) := by sorry
/-! ## Height and the joint limiting law -/
/-- A positive strictly decreasing cutoff sequence tending to zero, with almost-sure rational-time and a.e.-age
occupation-height limits under the stable, excursion and normalized excursion laws specified below. -/
noncomputable def BGW.StableTrees.IsUniversalHeightSeq (θ : ℝ) (ε : ℕ → ℝ) : Prop :=
  (∀ (k : ℕ), (0 : ℝ) < ε k) ∧
    StrictAnti ε ∧
      Tendsto ε atTop (𝓝 (0 : ℝ)) ∧
        (∀ (q : ℚ),
            (0 : ℚ) ≤ q →
              ∀ᵐ (f : DLoc) ∂(↑(stableLocalLaw θ) : Measure DLoc),
                Tendsto (fun (k : ℕ) => heightApprox (ε k) f (↑q : ℝ).toNNReal) atTop
                  (𝓝 (height θ f (↑q : ℝ).toNNReal))) ∧
          (∀ (q : ℚ),
              (0 : ℚ) < q →
                ∀ᵐ (e : Excursion) ∂(excursionMeasure θ).restrict {e : Excursion | (↑q : ℝ).toNNReal < e.lifetime},
                  ∃ (L : ℝ), Tendsto (fun (k : ℕ) => heightApprox (ε k) e.path (↑q : ℝ).toNNReal) atTop (𝓝 L)) ∧
            (∀ (q : ℚ),
                (0 : ℚ) < q →
                  q < (1 : ℚ) →
                    ∀ᵐ (e : Excursion) ∂(↑(unitExcursionLaw θ) : Measure Excursion),
                      ∃ (L : ℝ), Tendsto (fun (k : ℕ) => heightApprox (ε k) e.path (↑q : ℝ).toNNReal) atTop (𝓝 L)) ∧
              (∀ (S : ℝ≥0),
                  forallRealAE[BGW.StableTrees.IsUniversalHeightSeq._proof_1] s in volume.restrict (Ioo (0 : ℝ) (↑S : ℝ)),
                    ∀ᵐ (f : DLoc) ∂(↑(stableLocalLaw θ) : Measure DLoc),
                      Tendsto (fun (k : ℕ) => heightApprox (ε k) f s.toNNReal) atTop (𝓝 (height θ f s.toNNReal))) ∧
                (∀ (S : ℝ≥0),
                    forallRealAE[BGW.StableTrees.IsUniversalHeightSeq._proof_1] s in volume.restrict (Ioo (0 : ℝ) (↑S : ℝ)),
                      ∀ᵐ (e : Excursion) ∂(excursionMeasure θ).restrict {e : Excursion | s.toNNReal < e.lifetime},
                        ∃ (L : ℝ), Tendsto (fun (k : ℕ) => heightApprox (ε k) e.path s.toNNReal) atTop (𝓝 L)) ∧
                  forallRealAE[BGW.StableTrees.IsUniversalHeightSeq._proof_1] s in volume.restrict (Ioo (0 : ℝ) (1 : ℝ)),
                    ∀ᵐ (e : Excursion) ∂(↑(unitExcursionLaw θ) : Measure Excursion),
                      ∃ (L : ℝ), Tendsto (fun (k : ℕ) => heightApprox (ε k) e.path s.toNNReal) atTop (𝓝 L)
/-- The chosen universal sequence (junk `1/(k+1)` only if none exists). -/
noncomputable def BGW.StableTrees.heightEps (θ : ℝ) : ℕ → ℝ :=
  if h : ∃ (ε : ℕ → ℝ), IsUniversalHeightSeq θ ε then Classical.choose h
  else fun (k : ℕ) => (1 : ℝ) / ((↑k : ℝ) + (1 : ℝ))
/-- **The height read along the universal sequence** (a real limsup; junk where it diverges). -/
noncomputable def BGW.StableTrees.heightUniv (θ : ℝ) (f : DLoc) (t : ℝ≥0) : ℝ := limsup (fun (k : ℕ) => heightApprox (heightEps θ k) f t) atTop
theorem BGW.StableTrees.IsExcursionHeightVersion._proof_1 : @OuterMeasureClass (@Measure Real (@MeasureSpace.toMeasurableSpace Real Real.measureSpace)) Real (@Measure.instFunLike Real
  (@MeasureSpace.toMeasurableSpace Real Real.measureSpace)) := by sorry
/-- `g` is an **a.e.-age height version** of the excursion `e`: it vanishes at time `0` and at and after the lifetime,
and agrees with `heightUniv θ e.path` at Lebesgue-almost every age of `(0, ζ(e))`. -/
noncomputable def BGW.StableTrees.IsExcursionHeightVersion (θ : ℝ) (e : Excursion) (g : C(ℝ≥0, ℝ)) : Prop :=
  (g : ℝ≥0 → ℝ) (0 : ℝ≥0) = (0 : ℝ) ∧
    (∀ (t : ℝ≥0), e.lifetime ≤ t → (g : ℝ≥0 → ℝ) t = (0 : ℝ)) ∧
      forallRealAE[BGW.StableTrees.IsExcursionHeightVersion._proof_1] s in volume.restrict (Ioo (0 : ℝ) (↑e.lifetime : ℝ)), (g : ℝ≥0 → ℝ) s.toNNReal = heightUniv θ e.path s.toNNReal
/-- **The excursion height**: the a.e.-age height version of `e` when one exists (it is then unique), the zero function
otherwise. -/
noncomputable def BGW.StableTrees.excursionHeight (θ : ℝ) (e : Excursion) : C(ℝ≥0, ℝ) :=
  if h : ∃ (g : C(ℝ≥0, ℝ)), IsExcursionHeightVersion θ e g then Classical.choose h else (0 : C(ℝ≥0, ℝ))
/-- **The excursion/height pair on `[0,T]`**: the restricted path and the restricted height of the same excursion. -/
noncomputable def BGW.StableTrees.excursionPair (θ : ℝ) (T : ℝ≥0) (e : Excursion) : D (↑T : ℝ) ℝ × C((↑(Icc (0 : ℝ) (↑T : ℝ)) : Type), ℝ) :=
  (excursionRestrict T e, heightRestrict T (excursionHeight θ e))
/-- **The normalized excursion/height law** on `D 1 ℝ × C([0,1], ℝ)`: the image of the unit excursion law under the pair
map (path and height of the same excursion). -/
noncomputable def BGW.StableTrees.excLaw (θ : ℝ) : ProbabilityMeasure (D (1 : ℝ) ℝ × C((↑(Icc (0 : ℝ) (1 : ℝ)) : Type), ℝ)) :=
  (unitExcursionLaw θ).map (excursionPair θ (1 : ℝ≥0))
/-- The limit `(X^exc, H^exc, H^exc)` of Intro (II): the joint law `excLaw θ` of `(X, H)` under `N(· | ζ = 1)` (BGW),
with the height duplicated (a joint law, not a product of marginals). -/
noncomputable def BGWLeaves.excTripleLaw (θ : ℝ) : ProbabilityMeasure (D (1 : ℝ) ℝ × C((↑(Icc (0 : ℝ) (1 : ℝ)) : Type), ℝ) × C((↑(Icc (0 : ℝ) (1 : ℝ)) : Type), ℝ)) :=
  (excLaw θ).map fun (p : D (1 : ℝ) ℝ × C((↑(Icc (0 : ℝ) (1 : ℝ)) : Type), ℝ)) => (p.1, p.2, p.2)
/-! ## Principal functional limits -/
/-- Introduction (II): JOINT walk, contour and height convergence under leaf conditioning. No extra non-lattice
assumption; any admissible norming, along every admissible sequence tending to infinity. -/
theorem BGWLeaves.intro_II_general {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hap : Aperiodic μ) (hB : IsRealStableAttracted (realOffspringStepLaw μ) θ B) {q : ℕ → ℕ}
    (hqtop : Tendsto q atTop atTop) (hq : ∀ k, LeafAdmissible μ (q k)) :
    Tendsto (fun k => (leafTreeLaw μ (q k)).map (codingTriple B)) atTop (𝓝 (excTripleLaw θ)) := by sorry
/-- `P_μ[ζ_A(τ) = n] > 0` (finite trees). -/
noncomputable def BGWLeaves.ZetaAAdmissible (μ : PMF ℕ) (A : Set ℕ) (n : ℕ) : Prop :=
  (bienaymeLaw μ.toMeasure : Set LocallyFinite.Tree → ℝ≥0∞)
      {T : LocallyFinite.Tree | FiniteVertices T ∧ BGWLeaves.zetaA A T = (↑n : ℕ∞)} ≠
    (0 : ℝ≥0∞)
theorem BGWLeaves.zetaATreeLaw._proof_1 : ∀ (μ : PMF ℕ) (A : Set ℕ) (n : ℕ),
  BGWLeaves.ZetaAAdmissible μ A n →
    IsProbabilityMeasure
      (bienaymeLaw μ.toMeasure)[|{T : LocallyFinite.Tree | FiniteVertices T ∧ BGWLeaves.zetaA A T = (↑n : ℕ∞)}] := by sorry
theorem BGWLeaves.zetaATreeLaw._proof_2 : IsProbabilityMeasure (Measure.dirac leaf) := by sorry
/-- `P_μ[· | ζ_A = n]` as a probability measure (junk Dirac mass at the one-vertex tree if null). -/
noncomputable def BGWLeaves.zetaATreeLaw (μ : PMF ℕ) (A : Set ℕ) (n : ℕ) : ProbabilityMeasure LocallyFinite.Tree :=
  if h : BGWLeaves.ZetaAAdmissible μ A n then
    (⟨(bienaymeLaw μ.toMeasure)[|{T : LocallyFinite.Tree | FiniteVertices T ∧ BGWLeaves.zetaA A T = (↑n : ℕ∞)}],
        BGWLeaves.zetaATreeLaw._proof_1 μ A n h⟩ :
      { μ : Measure LocallyFinite.Tree // IsProbabilityMeasure μ })
  else
    (⟨Measure.dirac leaf, BGWLeaves.zetaATreeLaw._proof_2⟩ : { μ : Measure LocallyFinite.Tree // IsProbabilityMeasure μ })
/-- Theorem 8.1(II): the same JOINT limit under offspring-mark conditioning. Finite-or-cofinite marks in infinite
variance, any admissible norming and admissible diverging sequence. -/
theorem BGWLeaves.thm_general_II {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ} {A : Set ℕ} (hA : A.Nonempty)
    (hc : IsCritical μ) (hne : μ 1 ≠ 1) (hap : Aperiodic μ)
    (hB : IsRealStableAttracted (realOffspringStepLaw μ) θ B)
    (hAfin : ¬ Integrable (fun z : ℤ => (z : ℝ) ^ 2) (stepLaw μ) → A.Finite ∨ Aᶜ.Finite)
    {q : ℕ → ℕ} (hqtop : Tendsto q atTop atTop) (hq : ∀ k, ZetaAAdmissible μ A (q k)) :
    Tendsto (fun k => (zetaATreeLaw μ A (q k)).map (codingTriple B)) atTop
      (𝓝 (excTripleLaw θ)) := by sorry
/-- Coercing a path constructor to a function recovers its underlying path. -/
theorem BGW.Skorokhod.coe_mk {T : ℝ} {E : Type*} [TopologicalSpace E] (p : Set.Icc (0 : ℝ) T → E)
    (hp : IsCadlag p) : ((⟨p, hp⟩ : D T E) : Set.Icc (0 : ℝ) T → E) = p := by sorry
/-- The J1 metric has distance exactly `j1Dist`. -/
theorem BGW.Skorokhod.dist_eq_j1Dist {T : ℝ} {E : Type*} [MetricSpace E] (f g : D T E) : dist f g = j1Dist f g := by sorry
