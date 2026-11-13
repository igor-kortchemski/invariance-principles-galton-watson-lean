module

public import BGWLeaves.MarkedForest.Defs
public import BGW.LocallyFinite.Law
public import BGW.LocallyFinite.ForestWalkLaw
public import Mathlib.Probability.ConditionalProbability

/-!
# The forest law and the jump law of `W'`: definitions

Source: arXiv:1110.2163v4, Definitions 1.1–1.2 (forests of independent
Galton–Watson trees) and Proposition 1.6 (`prop:K`).

* `eta μ` is the law of `K - 1` given `K > 0` for `K ∼ μ`, that is the jump law
  `η(r) = μ(r+1)/(1-μ(0))` of the random walk `W'` (a probability measure when `μ {0} ≠ 1`).
* `forestEvent j p n` is the event that a forest of `j` independent locally finite trees consists
  of finite trees with `p` vertices and `n` leaves in total.
-/

@[expose] public section

namespace BGWLeaves

open MeasureTheory ProbabilityTheory BGW
open scoped ENNReal

/-- Law of `K - 1` given `K > 0`, `K ∼ μ`: the jump law `η(r) = μ(r+1)/(1-μ(0))` of `W'`. -/
noncomputable def eta (μ : Measure ℕ) : Measure ℕ :=
  (μ[|Set.Ici 1]).map (fun k => k - 1)

/-- A forest of `j` finite trees with `p` vertices and `n` leaves in total, as an event for the
product of `j` independent locally finite Galton–Watson trees. -/
def forestEvent (j p n : ℕ) : Set (Fin j → LocallyFinite.Tree) :=
  {F | ∃ ts : Fin j → PlaneTree, (∑ i, (ts i).size = p) ∧ (∑ i, (ts i).degreeCount 0 = n) ∧
    F = fun i => (ts i).toLocallyFinite}

end BGWLeaves
