module

public import BGWLeaves.GeneralA.Defs
public import BGWLeaves.GeneralA.MarkedSeries
public import BGWLeaves.GeneralA.MarkedSpan
public import BGWLeaves.LeafMass.Defs
public import BGWLeaves.StableAnalysis
public import BGWLeaves.StableAnalysis.StableDomainTail

/-!
# Theorem 8.1(I), corrected, all variances: definitions

Source: arXiv:1110.2163v4, Section 8, Theorem 8.1(I) (`thm:general`, lines 2494-2515 of the LaTeX source)
and the non-functional pieces of Theorem 8.1(II) (`eq:gen`, `eq:gen2`, lines 2512-2540).

This file contains the definitions for `BGWLeaves.GeneralAInf`, all of them abbreviations of expressions of
`BGWLeaves.GeneralA` (the finite-variance case) and of `BGWLeaves.StableAnalysis`.  The main statements are
in `BGWLeaves.GeneralAInf`; their proofs are in the modules `BGWLeaves.GeneralAInf.*` (imported through
`BGWLeaves.GeneralAInf.Proof`).

Conventions as in `BGWLeaves.GeneralA`: `B_n = norming (stepLaw μ) θ n` is the corrected norming
(corrections 1 and 2 of `FORMALIZATION_REPORT.md`), `p₁ = Scalar.stableDensity θ`, and `P_μ[ζ_A = n]` is the
real-valued mass of `{T | zetaA A T = n}` under `bienaymeLaw μ.toMeasure` (infinite trees are null in the
critical case).  No conditional measure is used.
-/

@[expose] public section

namespace BGWLeaves

open MeasureTheory
open scoped ENNReal
open BGW BGW.StableTrees BGW.LocallyFinite BGWLeaves.StableAnalysis
open BGWLeaves.GeneralA.MarkedWalk BGWLeaves.GeneralA.Regroup BGWLeaves.GeneralA.MarkedTime

/-- The step law `ν = ν^A` of the A-time walk of the finite-variance proof:
`ν = α * ∑ₖ β^{*k}` with `α = markedStep` (the part of `K - 1` carried by `K ∈ A`, mass `μ(A)`) and
`β = unmarkedStep` (the part carried by `K ∉ A`).  It is the law of one marked step followed by a
geometric number of unmarked steps.  `MarkedSeries.zetaA_blockLaw` states
`P[ζ_A = n] = (1/n) P[W^ν_n = -1]`. -/
noncomputable abbrev blockStep (μ : PMF ℕ) (A : Set ℕ) : Measure ℤ :=
  blockLaw (markedStep (fun k => μ k) A) (unmarkedStep (fun k => μ k) A)

/-- The paper's `ρ` (line 2519, shifted: `ρ(i) = μ(i+1)/μ(A)` for `i + 1 ∈ A`): the law of `K - 1` given
`K ∈ A`.  (The normalization of the zero measure only occurs multiplied by `μ(A)^n = 0`.) -/
noncomputable abbrev insideMarkLaw (μ : PMF ℕ) (A : Set ℕ) : Measure ℤ :=
  normalized (markedStep (fun k => μ k) A)

/-- The paper's `μ'` (line 2519): the law of `K - 1` given `K ∉ A`. -/
noncomputable abbrev outsideMarkLaw (μ : PMF ℕ) (A : Set ℕ) : Measure ℤ :=
  normalized (unmarkedStep (fun k => μ k) A)

/-- The function `q₁(x) = x p₁(-x)` of the paper (line 1904, used in `eq:gen`). -/
noncomputable def q₁ (θ x : ℝ) : ℝ := x * Scalar.stableDensity θ (-x)

/-- `P_μ[ζ_A = n]`, so that the statements of `BGWLeaves.GeneralAInf` stay readable. -/
noncomputable abbrev zetaAProb (μ : PMF ℕ) (A : Set ℕ) (n : ℕ) : ℝ :=
  (bienaymeLaw μ.toMeasure).real {T | zetaA A T = (n : ℕ∞)}

end BGWLeaves
