module

public import BGWLeaves.GeneralA.Defs
import BGWLeaves.GeneralA.Proof

/-!
# Theorem 8.1(I), corrected statement for finite variance

Source: arXiv:1110.2163v4, Section 8, Theorem 8.1(I).  **The statement formalized here is the
corrected one**: it replaces the printed constant `gcd(b-1,d)` (false in general, see correction 5 of
`FORMALIZATION_REPORT.md`) by `arithFactor μ A`, and it covers the finite-variance case (`θ = 2`) only.
The printed claim is not proved.  The infinite-variance cases are in `BGWLeaves.GeneralAInf`.
-/

@[expose] public section

namespace BGWLeaves

open MeasureTheory Filter
open scoped Topology ENNReal
open BGW.StableTrees BGW.LocallyFinite BGWLeaves.StableAnalysis

/-- Sanity (non-vacuity): the largest positive common divisor exists. -/
theorem arithFactor_isGreatest {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1) (A : Set ℕ) :
    IsGreatest {e : ℕ | 1 ≤ e ∧ ∀ s ∈ arithSet μ A, (e : ℤ) ∣ s} (arithFactor μ A) := by
  exact BGWLeaves.GeneralA.Arithmetic.arithFactor_isGreatest hc hne A

/-- **Theorem 8.1(I), finite variance, CORRECTED.**  The statement formalized here is the
corrected one, replacing the printed constant `gcd(b-1,d)` of Theorem 8.1(I) (false in general,
correction 5 of `FORMALIZATION_REPORT.md`) by `e = arithFactor μ A`: for `μ` critical, aperiodic, of finite
variance `σ²`, and `A` with `m = μ(A) > 0`, `P(ζ_A = n) = 0` unless `n ≡ 1 (mod e)`, and
`n^{3/2} P(ζ_A = n) → e √(2m) / (2σ√π)` along `n = e j + 1`, `j → ∞`. -/
theorem thm81_finiteVariance_corrected {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hap : Aperiodic μ) (hvar : Integrable (fun z : ℤ => (z : ℝ) ^ 2) (stepLaw μ))
    {A : Set ℕ} (hA : μ.toMeasure A ≠ 0) :
    (∀ n : ℕ, ¬ ((arithFactor μ A : ℤ) ∣ (n : ℤ) - 1) →
        bienaymeLaw μ.toMeasure {T | zetaA A T = n} = 0) ∧
    Tendsto (fun j : ℕ =>
        ((arithFactor μ A * j + 1 : ℕ) : ℝ) ^ ((3 : ℝ) / 2) *
          (bienaymeLaw μ.toMeasure).real {T | zetaA A T = ((arithFactor μ A * j + 1 : ℕ) : ℕ∞)})
      atTop
      (𝓝 ((arithFactor μ A : ℝ) * Real.sqrt (2 * (μ.toMeasure A).toReal) /
        (2 * Real.sqrt (BGWLeaves.StableAnalysis.variance (stepLaw μ)) * Real.sqrt Real.pi))) := by
  exact BGWLeaves.GeneralA.Asymptotic.thm81_finiteVariance_corrected hc hne hap hvar hA

end BGWLeaves
