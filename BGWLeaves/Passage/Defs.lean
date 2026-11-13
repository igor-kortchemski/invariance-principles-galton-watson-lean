module

public import BGWLeaves.ForestLaw.Defs
public import Mathlib.Probability.ProductMeasure

/-!
# Stopped walk words and forests: definitions

Source: arXiv:1110.2163v4, `largetrees_final.tex`, Definition 1.3, Proposition 1.4 (`prop:RW`),
`eq:kemperman` and the Introduction's formula `eq:f` (lines 291, 471–542).

* `IsFirstHit j ω p`: `p` is the first time at which the walk `W_n = ∑_{i<n} (ω i - 1)` hits `-j`.
* `stoppedWordEvent j x`: the walk first hits `-j` at time `x.length` and its steps up to then
  are the word `x`.
* `forestCodeEvent j x`: the Łukasiewicz word (concatenated depth-first increments) of the forest of
  `j` finite trees is `x`.
* `forestSizeEvent j p`: a forest of `j` finite trees with `p` vertices in total.
* `treeSizeLeavesEvent p n`: a single finite tree with `p` vertices and `n` leaves.
-/

@[expose] public section

namespace BGWLeaves

open MeasureTheory ProbabilityTheory BGW
open scoped ENNReal

/-- `p` is the first time at which the walk `W_n = ∑_{i<n} (ω i - 1)` hits `-j`. -/
def IsFirstHit (j : ℕ) (ω : ℕ → ℕ) (p : ℕ) : Prop :=
  (∑ i ∈ Finset.range p, ((ω i : ℤ) - 1)) = -(j : ℤ) ∧
    ∀ q < p, -(j : ℤ) < ∑ i ∈ Finset.range q, ((ω i : ℤ) - 1)

/-- The walk with steps `ω i - 1` hits `-j` for the first time at time `x.length`, and its steps
up to that time are the word `x`. -/
def stoppedWordEvent (j : ℕ) (x : List ℤ) : Set (ℕ → ℕ) :=
  {ω | IsFirstHit j ω x.length ∧ ∀ (i : ℕ) (hi : i < x.length), (ω i : ℤ) - 1 = x[i]}

/-- The Łukasiewicz word (increments) of the forest of `j` finite trees is `x`. -/
def forestCodeEvent (j : ℕ) (x : List ℤ) : Set (Fin j → LocallyFinite.Tree) :=
  {F | ∃ ts : Fin j → PlaneTree, PlaneForest.increments (List.ofFn ts) = x ∧
    F = fun i => (ts i).toLocallyFinite}

/-- A forest of `j` finite trees with `p` vertices in total. -/
def forestSizeEvent (j p : ℕ) : Set (Fin j → LocallyFinite.Tree) :=
  {F | ∃ ts : Fin j → PlaneTree, (∑ i, (ts i).size = p) ∧ F = fun i => (ts i).toLocallyFinite}

/-- A single finite tree with `p` vertices and `n` leaves. -/
def treeSizeLeavesEvent (p n : ℕ) : Set LocallyFinite.Tree :=
  {T | ∃ t : PlaneTree, t.size = p ∧ t.degreeCount 0 = n ∧ T = t.toLocallyFinite}

end BGWLeaves
