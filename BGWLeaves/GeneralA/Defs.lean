module

public import BGWLeaves.StableAnalysis.Defs

/-!
# Theorem 8.1(I) for a general set `A` (corrected, finite variance): definitions

Source: arXiv:1110.2163v4, Section 8, Theorem 8.1(I), `largetrees_final.tex` lines 2495-2515.

The printed constant `gcd(b-1,d)` of Theorem 8.1(I) is false in general
(`MANUSCRIPT_RECOMMENDATIONS.md` R1).  The statement formalized in `BGWLeaves.GeneralA` is the
**corrected** one, with the arithmetic factor `arithFactor μ A` below, in the finite-variance case
only; the printed claim is not counted as proved, and the infinite-variance cases stay open.
-/

@[expose] public section

namespace BGWLeaves

open BGW.StableTrees BGW.LocallyFinite

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
