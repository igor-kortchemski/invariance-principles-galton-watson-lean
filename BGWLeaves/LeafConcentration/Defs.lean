module

public import BGWLeaves.Passage.Defs
public import BGWLeaves.ForestLaw.Defs
public import BGWLeaves.StableAnalysis.Defs
public import Mathlib.Probability.Independence.Basic

/-!
# Leaf concentration (M4a): definitions and proved bridges

Source: arXiv:1110.2163v4, `largetrees_final.tex`, Section 2: Definition 2.1 (`def:Lambda`),
Lemma 2.2 (`lem:phi`), the notation `oe_ε(n)` of Definition and Remark 2.3-2.4 (`rem:oe`),
Lemma 2.5 (`lem:GdesDev`), Corollary 2.6 (`cor:GD2mieux`) and Lemma 2.7 (`lem:GdesDev2`).

This file contains every definition of milestone M4a and the proved bridges between the tree
counter `Λ_τ` of Definition 2.1 and the walk counter `Λ` of Section 1.3.  It contains no proof
holes.  The statements still to be proved are in `BGWLeaves.LeafConcentration`; their proofs are
supplied by the provider modules `BGWLeaves.LeafConcentration.*` (imported through
`BGWLeaves.LeafConcentration.Proof`).

Conventions.
* Offspring law `μ : PMF ℕ` (as in the M3 interface); the law of one Galton-Watson tree is
  `LocallyFinite.bienaymeLaw μ.toMeasure` on `LocallyFinite.Tree`, the law of a forest of `j`
  independent trees is `Measure.pi (fun _ : Fin j => bienaymeLaw μ.toMeasure)`, and the walk with
  steps `ω i - 1` is `Measure.infinitePi (fun _ : ℕ => μ.toMeasure)` (as in M2b).
* Finite trees are `PlaneTree`; an event `Q` of finite trees is lifted to `LocallyFinite.Tree` by
  `finiteTreeEvent Q`.  Infinite trees never belong to it.
* Conditioning is `ProbabilityTheory.cond` (`μ[|s]`): the conditional law of a null event is the
  zero measure.
* Probabilities are real numbers (`Measure.real`; all measures are probability measures).
-/

@[expose] public section

namespace BGWLeaves

open MeasureTheory ProbabilityTheory Filter Asymptotics BGW
open BGW.StableTrees BGW.LocallyFinite BGWLeaves.StableAnalysis
open scoped ENNReal Topology

/-! ## 2.3 The notation `oe_ε(n)` -/

/-- `x_n = oe_ε(n)`: there are `C, c > 0` with `x_n ≤ C exp(-c n^ε)` for all `n`
(the paper's definition; `n = 0` is harmless since `0 ^ ε = 0` for `ε > 0`). -/
def IsOe (ε : ℝ) (x : ℕ → ℝ) : Prop :=
  ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ n : ℕ, x n ≤ C * Real.exp (-c * (n : ℝ) ^ ε)

/-- `x_j(n) = oe_ε(n)` **uniformly in `1 ≤ j ≤ n`**: one pair `(C, c)` serves all `j` and `n`. -/
def IsOeUniform (ε : ℝ) (x : ℕ → ℕ → ℝ) : Prop :=
  ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
    ∀ n j : ℕ, 1 ≤ j → j ≤ n → x j n ≤ C * Real.exp (-c * (n : ℝ) ^ ε)

/-! ## 2.1 Definition 2.1 (`def:Lambda`) -/

/-- `k_j(τ)`: the number of children of the `j`-th vertex of `τ` in lexicographic order
(= root-first depth-first order, children from left to right); the junk value `0` for `j ≥ ζ(τ)`. -/
def childCountAt (t : PlaneTree) (j : ℕ) : ℕ := t.degrees.getD j 0

/-- Definition 2.1: `Λ_τ(s) = ∑_{j=0}^{⌊s⌋} 1{k_j = 0}` for `0 ≤ s < ζ(τ)` and `Λ_τ(ζ(τ)) = λ(τ)`
(`ζ(τ) = t.size`, `λ(τ) = t.degreeCount 0`). It is the number of leaves among the first `⌊s⌋ + 1`
vertices. Values for `s < 0` and `s > ζ(τ)` are not part of the definition (junk, not used). -/
noncomputable def Lambda (t : PlaneTree) (s : ℝ) : ℕ :=
  if (t.size : ℝ) ≤ s then t.degreeCount 0
  else ∑ j ∈ Finset.range (⌊s⌋₊ + 1), if childCountAt t j = 0 then 1 else 0

/-- `Λ(k) = Card {0 ≤ i ≤ k - 1 : W_{i+1} - W_i = -1}` of Section 1.3 for the walk with steps
`W_{i+1} - W_i = ω i - 1`: the number of the first `k` steps equal to `-1`. -/
def walkLeafCount (ω : ℕ → ℕ) (k : ℕ) : ℕ :=
  ((Finset.range k).filter fun i => (ω i : ℤ) - 1 = -1).card

/-- `walkLeafCount` is the count of zero offspring numbers among the first `k` steps, in the form
used by M2b (`firstHit_leaves_law`). -/
theorem walkLeafCount_eq_card_fin (ω : ℕ → ℕ) (k : ℕ) :
    walkLeafCount ω k = (Finset.univ.filter fun i : Fin k => ω i = 0).card := by
  unfold walkLeafCount
  rw [Finset.card_filter, Finset.card_filter,
    Finset.sum_range (fun i => if (ω i : ℤ) - 1 = -1 then 1 else 0)]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : ω i = 0 <;> simp [h]

/-- Helper: the number of zeros in a list of offspring numbers. -/
theorem count_zero_eq_sum (l : List ℕ) :
    l.count 0 = ∑ i ∈ Finset.range l.length, if l.getD i 0 = 0 then 1 else 0 := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.length_cons, Finset.sum_range_succ', List.count_cons, ih]
    simp

/-- Helper: `Λ(k)` of a walk starting with the word of `t` is the vertex-indexed sum of Definition 2.1. -/
theorem walkLeafCount_eq_sum (t : PlaneTree) (ω : ℕ → ℕ) (hω : ω ∈ stoppedWordEvent 1 t.increments) {k : ℕ}
    (hk : k ≤ t.size) :
    walkLeafCount ω k = ∑ j ∈ Finset.range k, if childCountAt t j = 0 then 1 else 0 := by
  unfold walkLeafCount
  rw [Finset.card_filter]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i < t.size := lt_of_lt_of_le (Finset.mem_range.1 hi) hk
  have h2 := hω.2 i (by simpa [PlaneTree.length_increments] using hi')
  have hlen : i < t.degrees.length := by simpa using hi'
  have : (t.increments)[i]'(by simpa [PlaneTree.length_increments] using hi') = (t.degrees[i] : ℤ) - 1 := by
    simp [PlaneTree.increments]
  rw [this] at h2
  have h3 : ω i = t.degrees[i] := by omega
  unfold childCountAt
  have h4 : t.degrees.getD i 0 = ω i := by
    rw [h3, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlen]; rfl
  rw [h4]
  by_cases h : ω i = 0 <;> simp [h]

/-- The two cases of the one-step translation: strictly inside `Λ_t(s) = Λ(⌊s⌋ + 1)`, at the end
`Λ_t(ζ) = Λ(ζ) = λ(t)`. -/
theorem Lambda_translation (t : PlaneTree) (ω : ℕ → ℕ)
    (hω : ω ∈ stoppedWordEvent 1 t.increments) :
    (∀ s : ℝ, 0 ≤ s → s < t.size → Lambda t s = walkLeafCount ω (⌊s⌋₊ + 1)) ∧
      Lambda t t.size = walkLeafCount ω t.size ∧ walkLeafCount ω t.size = t.degreeCount 0 := by
  have hdeg : t.degreeCount 0 = ∑ j ∈ Finset.range t.size, if childCountAt t j = 0 then 1 else 0 := by
    unfold PlaneTree.degreeCount childCountAt
    rw [count_zero_eq_sum, PlaneTree.length_degrees]
  have hend : walkLeafCount ω t.size = t.degreeCount 0 := by
    rw [walkLeafCount_eq_sum t ω hω le_rfl, hdeg]
  refine ⟨fun s hs hlt => ?_, ?_, hend⟩
  · have hf : ⌊s⌋₊ < t.size := (Nat.floor_lt hs).2 hlt
    rw [walkLeafCount_eq_sum t ω hω (by omega)]
    simp [Lambda, hlt]
  · simp [Lambda, hend]

/-- **One-step translation of the counters.** If the walk `ω` starts with the Łukasiewicz word of
the tree `t` (`ω ∈ stoppedWordEvent 1 t.increments`: it first hits `-1` at time `ζ(t)`, with the
steps of `t`), then for `0 ≤ s < ζ(t)`: `Λ_t(s) = Λ(⌊s⌋ + 1)`; the tree counter at `s` counts vertices
`0,…,⌊s⌋`, the walk counter `Λ(k)` counts the increments with indices `0,…,k-1`. At `s = ζ(t)`,
`Λ_t(ζ) = λ(t) = Λ(ζ)`. -/
theorem Lambda_eq_walkLeafCount (t : PlaneTree) (ω : ℕ → ℕ)
    (hω : ω ∈ stoppedWordEvent 1 t.increments) {s : ℝ} (hs : 0 ≤ s) :
    Lambda t s = walkLeafCount ω (min (⌊s⌋₊ + 1) t.size) := by
  obtain ⟨h1, h2, -⟩ := Lambda_translation t ω hω
  by_cases hlt : s < t.size
  · rw [h1 s hs hlt]
    have : ⌊s⌋₊ < t.size := (Nat.floor_lt hs).2 hlt
    rw [min_eq_left (by omega)]
  · have : t.size ≤ ⌊s⌋₊ := Nat.le_floor (not_lt.1 hlt)
    rw [min_eq_right (by omega), ← h2]
    have e1 : Lambda t s = t.degreeCount 0 := by simp [Lambda, not_lt.1 hlt]
    have e2 : Lambda t t.size = t.degreeCount 0 := by simp [Lambda]
    rw [e1, e2]

/-! ## 2.2 The rate function of Lemma 2.2 (`lem:phi`) -/

/-- `φ*(x) = x ln (x / p) + (1 - x) ln ((1 - x) / (1 - p))` for `0 ≤ x ≤ 1` (the paper's `p = μ₀`).
Lean's `0 * log 0 = 0` gives the convention `0 ln 0 = 0` at the endpoints; outside `[0,1]` the
value is junk: the thresholds outside `[0,1]` are trivial events in Lemma 2.2(i). -/
noncomputable def phiStar (p x : ℝ) : ℝ := x * Real.log (x / p) + (1 - x) * Real.log ((1 - x) / (1 - p))

/-! ## Events of finite trees, sup of the leaf-fraction deviation -/

/-- The event of `LocallyFinite.Tree` that the tree is finite, equal to `t.toLocallyFinite` for a
finite plane tree `t` with `Q t`. -/
def finiteTreeEvent (Q : PlaneTree → Prop) : Set LocallyFinite.Tree :=
  {T | ∃ t : PlaneTree, t.toLocallyFinite = T ∧ Q t}

/-- `sup_{η ≤ t ≤ 1} |f t|` in `[0, ∞]` (a supremum in `ℝ≥0∞`: no boundedness side condition, and
the comparison `c ≤ sup` is the printed one, not `∃ t, c ≤ |f t|`). -/
noncomputable def supDev (η : ℝ) (f : ℝ → ℝ) : ℝ≥0∞ :=
  ⨆ t ∈ Set.Icc η 1, ENNReal.ofReal |f t|

/-- `c < sup_{η ≤ t ≤ 1} |f t|` (`c ≥ 0`) iff `c < |f t|` for some `t ∈ [η, 1]` (the strict
comparison, used for the `>` of Lemma 2.5(i)). -/
theorem lt_supDev_iff {η c : ℝ} (hc : 0 ≤ c) (f : ℝ → ℝ) :
    ENNReal.ofReal c < supDev η f ↔ ∃ t ∈ Set.Icc η 1, c < |f t| := by
  unfold supDev
  simp only [lt_iSup_iff]
  constructor
  · rintro ⟨t, ht, h⟩
    exact ⟨t, ht, (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hc).1 h⟩
  · rintro ⟨t, ht, h⟩
    exact ⟨t, ht, (ENNReal.ofReal_lt_ofReal_iff (lt_of_le_of_lt hc h)).2 h⟩

/-- `(1/(n t)) ∑_{j=0}^{⌊nt⌋} 1{X_j = -1} - p` of Lemma 2.5(i), with the vertex indexing of
Definition 2.1: the sum runs over the first `⌊nt⌋ + 1` steps `ω 0, …, ω ⌊nt⌋`, so it is
`Λ(⌊nt⌋ + 1)` (see `Lambda_eq_walkLeafCount`). -/
noncomputable def walkLeafDev (p : ℝ) (ω : ℕ → ℕ) (n : ℕ) (t : ℝ) : ℝ :=
  (walkLeafCount ω (⌊(n : ℝ) * t⌋₊ + 1) : ℝ) / ((n : ℝ) * t) - p

/-- `Λ_τ(L t) / (L t) - p` of Lemma 2.5(ii) (`L = n`) and Corollary 2.6 (`L = ζ(τ)`). -/
noncomputable def treeLeafDev (p : ℝ) (τ : PlaneTree) (L t : ℝ) : ℝ :=
  (Lambda τ (L * t) : ℝ) / (L * t) - p

end BGWLeaves
