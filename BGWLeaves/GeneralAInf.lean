module

public import BGWLeaves.GeneralAInf.Defs
import BGWLeaves.GeneralAInf.Proof

/-!
# Theorem 8.1(I), corrected statement for all variances

Source: arXiv:1110.2163v4, Section 8, Theorem 8.1(I) (`thm:general`, lines 2494-2515) and the
non-functional part of Theorem 8.1(II) (`eq:gen`, `eq:gen2`, lines 2512-2540), for all variances (finite and infinite).
Line numbers refer to the LaTeX source of arXiv:1110.2163v4.

**The statement formalized here is the CORRECTED one.**  It replaces the printed constant
`gcd(b-1,d)/(h(n) n^{1/θ+1})` of Theorem 8.1(I) (false in general, correction 5 of `FORMALIZATION_REPORT.md`) by
`n B_n P_μ[ζ_A = n] → μ(A)^{1/θ} p₁(0) e` with `e = arithFactor μ A` and `B_n = norming (stepLaw μ) θ n` (the corrected
norming, corrections 1 and 2).  The printed claim is not proved.  The finite-variance case is
`BGWLeaves.thm81_finiteVariance_corrected` (`BGWLeaves.GeneralA`), linked by `thm81_corrected_general_finiteVariance_iff`.

Scope and strength.  The main statement `thm81_corrected_general` is STRONGER than the printed theorem: it drops the finite or
cofinite hypothesis on `A` (printed for `σ² = ∞`) and aperiodicity, and treats all variances at once.  The three statements
`thm81_infiniteVariance_A_finite`, `thm81_infiniteVariance_A_cofinite` and `thm81_corrected` carry the printed hypotheses
(`hap` is carried and unused) and are the statements that cover the printed Theorem 8.1(I); each is proved in this file
from `thm81_corrected_general`.  No cited external theorem is needed (Lévy's continuity theorem is in Mathlib), so there is
no `CitedXxx` definition and the result is unconditional.  The joint walk/contour/height limit (Theorem 8.1(II) proper) is
functional and is in `BGWLeaves.GeneralAFunctional` (comment at the end of this file).

The proofs are in the modules `BGWLeaves.GeneralAInf.*` (imported through `BGWLeaves.GeneralAInf.Proof`).  Definitions are
in `BGWLeaves.GeneralAInf.Defs`.  The declarations `thm81_infiniteVariance_A_finite`, `thm81_infiniteVariance_A_cofinite`
and `thm81_corrected` are proved here from `thm81_corrected_general`.

Layout.
* the A-time step law `ν = blockStep μ A` (module `BlockStable`): `blockStep_firstMoment`, `blockStep_charFun_identity`,
  `blockStep_isStableAttracted` (the only new analytic ingredient), `monotone_norming_floor`, `norming_floor_ratio`.
* the local limit for `ν` (module `BlockLocal`): `thm81_corrected_general`, `eq_gen_corrected`.
* consequences and calibrations (module `Asymptotic`): `thm81_corrected_general_finiteVariance_iff`, `thm81_printed_form`,
  `thm81_pos_iff`, `zetaA_eq_zero_of_measure_zero`, `arithFactor_univ_eq_latticeSpan`, `zetaA_univ_eq_sizeEvent`,
  `zetaA_zero_eq_leafCount`.
* forests and the discrete content of 8.1(II) (module `Forest`): `zetaA_forest_blockLaw`, `marked_forest_factorization`,
  `zetaA_forest_eq_zero_of_not_dvd`, and the paper-route statements `insideMark_LLN`, `eq_gen2_concentration`
  (not needed by the proof of any other statement of this file).
-/

@[expose] public section

namespace BGWLeaves

open MeasureTheory Filter Asymptotics
open scoped Topology ENNReal
open BGW BGW.StableTrees BGW.LocallyFinite BGWLeaves.StableAnalysis
open BGWLeaves.GeneralA BGWLeaves.GeneralA.MarkedWalk BGWLeaves.GeneralA.Regroup
  BGWLeaves.GeneralA.MarkedTime BGWLeaves.GeneralA.MarkedLaw

/-! ## 1. Theorem 8.1(I), the helpers of the infinite-variance regime

The proof of `thm81_corrected_general` is the finite-variance proof of `BGWLeaves.GeneralA`
with ONE change: the A-time step law `ν` is no longer in the domain of attraction of the Gaussian
because of finite variance, but because of the characteristic-function identity
`φ_ν = φ_α / (1 - φ_β) = φ_α / (1 - φ_W + φ_α)` (`blockStep_charFun_identity`), which gives
`1 - φ_ν = (1 - φ_W)/(φ_α + 1 - φ_W)` and `φ_α(t) → μ(A)` as `t → 0`; the A-count never has to be
controlled (no law of large numbers, no finite/cofinite hypothesis, no aperiodicity). -/

/-- **Helper 1** (first moment of the A-time step law; the first-moment half of
`MarkedTime.blockLaw_moments` without the second-moment hypothesis).  `ν` is integrable with mean `0`. -/
theorem blockStep_firstMoment {μ : PMF ℕ} (hc : IsCritical μ) {A : Set ℕ}
    (hA : μ.toMeasure A ≠ 0) :
    IsProbabilityMeasure (blockStep μ A) ∧ Integrable (fun z : ℤ => (z : ℝ)) (blockStep μ A) ∧
      mean (blockStep μ A) = 0 := by
  exact BGWLeaves.GeneralAInf.BlockStable.blockStep_firstMoment hc hA

/-- **Helper 2** (the characteristic-function identity).  With `φ_ν`, `φ_α`, `φ_β` the
characteristic functions of `blockStep μ A`, `markedStep` and `unmarkedStep` (as real laws):
`φ_ν(t) (1 - φ_W(t) + φ_α(t)) = φ_α(t)` where `φ_W = φ_α + φ_β` is that of `stepLaw μ`
(`MarkedTime.stepLaw_decomposition`).  For `μ(A) > 0` the geometric series `∑ φ_β^k` converges since
`|φ_β| ≤ 1 - μ(A) < 1`. -/
theorem blockStep_charFun_identity {μ : PMF ℕ} {A : Set ℕ} (hA : μ.toMeasure A ≠ 0) (t : ℝ) :
    charFun ((blockStep μ A).map (fun z : ℤ => (z : ℝ))) t *
        (1 - charFun ((stepLaw μ).map (fun z : ℤ => (z : ℝ))) t +
          charFun ((markedStep (fun k => μ k) A).map (fun z : ℤ => (z : ℝ))) t) =
      charFun ((markedStep (fun k => μ k) A).map (fun z : ℤ => (z : ℝ))) t := by
  exact BGWLeaves.GeneralAInf.BlockStable.blockStep_charFun_identity hA t

/-- **Helper 3** (the new analytic ingredient).  If `μ` is in the domain of attraction of the
index-`θ` law with norming `B_n = norming (stepLaw μ) θ n`, then the A-time step law `ν` is in the
domain of attraction of the SAME stable law, with norming `b_n = B_{⌊n / μ(A)⌋}`.  Proof: `φ_ν(t/b_n)^n →
exp(-ψ(t))` by `blockStep_charFun_identity` (the proof of `isStableAttracted_of_finiteVariance`
in `CanonicalAttraction.lean`: Lévy continuity `ProbabilityMeasure.tendsto_iff_tendsto_charFun` plus the
limit of `k (1 - φ_W(t/B_k))`, taken along `k = ⌊n/μ(A)⌋`).  Valid for every `A` with `μ(A) > 0`, finite
or infinite variance, finite/cofinite or not.  NOTE: `ν` can have steps `< -1` (when `0 ∉ A`), so the
Laplace-transform results of `BGWLeaves.StableAnalysis` (`isStableAttracted_of_centered_one_step_limit`, which need
`ν{z < -1} = 0`) do not apply; the characteristic-function route is needed. -/
theorem blockStep_isStableAttracted {μ : PMF ℕ} {θ : ℝ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hDA : ∃ a, StableDomain μ θ a) {A : Set ℕ} (hA : μ.toMeasure A ≠ 0) :
    IsStableAttracted (blockStep μ A) θ 0
      (fun n : ℕ => norming (stepLaw μ) θ ⌊(n : ℝ) / (μ.toMeasure A).toReal⌋₊) := by
  exact BGWLeaves.GeneralAInf.BlockStable.blockStep_isStableAttracted hc hne hDA hA

/-- **Helper 4** (monotonicity of the time-changed norming; from `locallimit_i/ii`,
`mean_stepLaw`, `stableDomain_isStableAttracted`). -/
theorem monotone_norming_floor {μ : PMF ℕ} {θ : ℝ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hDA : ∃ a, StableDomain μ θ a) {A : Set ℕ} (hA : μ.toMeasure A ≠ 0) :
    Monotone (fun n : ℕ => norming (stepLaw μ) θ ⌊(n : ℝ) / (μ.toMeasure A).toReal⌋₊) := by
  exact BGWLeaves.GeneralAInf.BlockStable.monotone_norming_floor hc hne hDA hA

/-- **Helper 5** (regular variation of `B_n` of index `1/θ`; from `locallimit_ii`:
`B_⌊x⌋ / x^{1/θ}` is slowly varying):  `B_n / B_{⌊n/m⌋} → m^{1/θ}` with `m = μ(A) ∈ (0,1]`.
At `m = 1` this is `B_n / B_n = 1`. -/
theorem norming_floor_ratio {μ : PMF ℕ} {θ : ℝ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hDA : ∃ a, StableDomain μ θ a) {A : Set ℕ} (hA : μ.toMeasure A ≠ 0) :
    Tendsto (fun n : ℕ => norming (stepLaw μ) θ n /
        norming (stepLaw μ) θ ⌊(n : ℝ) / (μ.toMeasure A).toReal⌋₊) atTop
      (𝓝 ((μ.toMeasure A).toReal ^ (1 / θ))) := by
  exact BGWLeaves.GeneralAInf.BlockStable.norming_floor_ratio hc hne hDA hA

/-! ## 2. Theorem 8.1(I), corrected -/

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
  exact BGWLeaves.GeneralAInf.BlockLocal.thm81_corrected_general hc hne hDA hA

set_option linter.unusedVariables false in
/-- **Theorem 8.1(I), CORRECTED, infinite variance, exactly the printed hypotheses (`A` finite).**
Printed: "`(H_θ)`, `σ² = ∞`, `A` finite" (aperiodic `hap`, `θ ∈ (1,2]`, `index 2` included: `θ = 2`
with `σ² = ∞` is allowed, then `B_n = √(n K(z_n)/2)`).  The corrected conclusion is that of
`thm81_corrected_general`; it REPLACES the printed `gcd(b-1,d)/(h(n) n^{1/θ+1})`.  `hap` is not used (stated only to carry
the printed `(H_θ)(iii)`).  This is one of the covered statements of the printed Theorem 8.1(I). -/
theorem thm81_infiniteVariance_A_finite {μ : PMF ℕ} {θ : ℝ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hap : Aperiodic μ) (hDA : ∃ a, StableDomain μ θ a)
    (hinf : ¬ Integrable (fun z : ℤ => (z : ℝ) ^ 2) (stepLaw μ))
    {A : Set ℕ} (hAfin : A.Finite) (hA : μ.toMeasure A ≠ 0) :
    (∀ n : ℕ, ¬ ((arithFactor μ A : ℤ) ∣ (n : ℤ) - 1) →
        bienaymeLaw μ.toMeasure {T | zetaA A T = n} = 0) ∧
    Tendsto (fun j : ℕ =>
        ((arithFactor μ A * j + 1 : ℕ) : ℝ) * norming (stepLaw μ) θ (arithFactor μ A * j + 1) *
          zetaAProb μ A (arithFactor μ A * j + 1))
      atTop
      (𝓝 ((μ.toMeasure A).toReal ^ (1 / θ) * Scalar.stableDensity θ 0 * (arithFactor μ A : ℝ))) :=
  thm81_corrected_general hc hne hDA hA

set_option linter.unusedVariables false in
/-- **Theorem 8.1(I), CORRECTED, infinite variance, exactly the printed hypotheses (`ℕ ∖ A` finite,
i.e. `A` cofinite).**  Same corrected conclusion (it REPLACES the printed `gcd(b-1,d)` factor); `hap` unused.  This is one
of the covered statements of the printed Theorem 8.1(I). -/
theorem thm81_infiniteVariance_A_cofinite {μ : PMF ℕ} {θ : ℝ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hap : Aperiodic μ) (hDA : ∃ a, StableDomain μ θ a)
    (hinf : ¬ Integrable (fun z : ℤ => (z : ℝ) ^ 2) (stepLaw μ))
    {A : Set ℕ} (hAcof : Aᶜ.Finite) (hA : μ.toMeasure A ≠ 0) :
    (∀ n : ℕ, ¬ ((arithFactor μ A : ℤ) ∣ (n : ℤ) - 1) →
        bienaymeLaw μ.toMeasure {T | zetaA A T = n} = 0) ∧
    Tendsto (fun j : ℕ =>
        ((arithFactor μ A * j + 1 : ℕ) : ℝ) * norming (stepLaw μ) θ (arithFactor μ A * j + 1) *
          zetaAProb μ A (arithFactor μ A * j + 1))
      atTop
      (𝓝 ((μ.toMeasure A).toReal ^ (1 / θ) * Scalar.stableDensity θ 0 * (arithFactor μ A : ℝ))) :=
  thm81_corrected_general hc hne hDA hA

set_option linter.unusedVariables false in
/-- **Theorem 8.1(I), CORRECTED, whole printed theorem, all variances** (`(H_θ)` with `hap`, and the
printed side condition "if `μ` has infinite variance, `A` is finite or `ℕ ∖ A` is finite" as the
implication `hfc`).  The conclusion is the CORRECTED one and REPLACES the printed
`gcd(b-1,d)/(h(n) n^{1/θ+1})` of Theorem 8.1(I) (correction 5 of `FORMALIZATION_REPORT.md`).  Finite
variance (`θ = 2`) is `thm81_finiteVariance_corrected` (restated with `B_n = σ√(n/2)`, `p₁(0) = 1/√(4π)`).  The hypothesis `hA : μ(A) ≠ 0` is
strictly stronger than the printed "`A` non-empty": `A ≠ ∅` with `μ(A) = 0` is the VACUOUS case (`ζ_A = 0` almost surely,
`P[ζ_A = n] = 0` for `n ≥ 1`, no attainable `n`), see `zetaA_eq_zero_of_measure_zero`.  `hc, hne` are implied by `hDA`
(`StableDomain`) and are kept to match the finite-variance statement; `hap` is unused.  This is one of the covered statements of
the printed Theorem 8.1(I). -/
theorem thm81_corrected {μ : PMF ℕ} {θ : ℝ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hap : Aperiodic μ) (hDA : ∃ a, StableDomain μ θ a)
    {A : Set ℕ} (hA : μ.toMeasure A ≠ 0)
    (hfc : ¬ Integrable (fun z : ℤ => (z : ℝ) ^ 2) (stepLaw μ) → A.Finite ∨ Aᶜ.Finite) :
    (∀ n : ℕ, ¬ ((arithFactor μ A : ℤ) ∣ (n : ℤ) - 1) →
        bienaymeLaw μ.toMeasure {T | zetaA A T = n} = 0) ∧
    Tendsto (fun j : ℕ =>
        ((arithFactor μ A * j + 1 : ℕ) : ℝ) * norming (stepLaw μ) θ (arithFactor μ A * j + 1) *
          zetaAProb μ A (arithFactor μ A * j + 1))
      atTop
      (𝓝 ((μ.toMeasure A).toReal ^ (1 / θ) * Scalar.stableDensity θ 0 * (arithFactor μ A : ℝ))) :=
  thm81_corrected_general hc hne hDA hA

/-- **Consistency with the finite-variance theorem**: for finite variance
`σ²`, `θ = 2` (`BGW.alpha_eq_two_of_finiteVariance`), `B_n = σ√(n/2)`
(`norming_of_integrable_sq`), `p₁(0) = 1/√(4π)` (`stableDensity_two`), and
`n B_n P → √m e/√(4π)` is `n^{3/2} P → e √(2m)/(2σ√π)`, i.e. `thm81_corrected_general` at finite
variance is equivalent to `BGWLeaves.thm81_finiteVariance_corrected`. -/
theorem thm81_corrected_general_finiteVariance_iff {μ : PMF ℕ} {θ : ℝ} (hc : IsCritical μ)
    (hne : μ 1 ≠ 1) (hDA : ∃ a, StableDomain μ θ a)
    (hvar : Integrable (fun z : ℤ => (z : ℝ) ^ 2) (stepLaw μ)) {A : Set ℕ}
    (hA : μ.toMeasure A ≠ 0) :
    θ = 2 ∧
      (Tendsto (fun j : ℕ =>
          ((arithFactor μ A * j + 1 : ℕ) : ℝ) * norming (stepLaw μ) θ (arithFactor μ A * j + 1) *
            zetaAProb μ A (arithFactor μ A * j + 1))
        atTop
        (𝓝 ((μ.toMeasure A).toReal ^ (1 / θ) * Scalar.stableDensity θ 0 * (arithFactor μ A : ℝ))) ↔
      Tendsto (fun j : ℕ =>
          ((arithFactor μ A * j + 1 : ℕ) : ℝ) ^ ((3 : ℝ) / 2) *
            zetaAProb μ A (arithFactor μ A * j + 1)) atTop
        (𝓝 ((arithFactor μ A : ℝ) * Real.sqrt (2 * (μ.toMeasure A).toReal) /
          (2 * Real.sqrt (variance (stepLaw μ)) * Real.sqrt Real.pi)))) := by
  exact BGWLeaves.GeneralAInf.Asymptotic.thm81_corrected_general_finiteVariance_iff hc hne hDA hvar hA

set_option linter.unusedVariables false in
/-- **Theorem 8.1(I) in the printed `~` form** (`P ∼ μ(A)^{1/θ} p₁(0) e / (h(n) n^{1/θ+1})`), with the
corrected constant `e` and `h = hSlow μ θ` (so that `h(n) n^{1/θ+1} = n B_n`), along the lattice
`n ≡ 1 (mod e)` of attainable values.  Together with `thm81_pos_iff` this is the printed
"for those `n` such that `P > 0`" (positivity of `P` implies `e ∣ n - 1`, and conversely for large
`n`).  Proof: from `thm81_corrected_general` (sequence form to filter form, `p₁(0) > 0`,
`hSlow μ θ n * n^{1/θ+1} = n * norming (stepLaw μ) θ n`). -/
theorem thm81_printed_form {μ : PMF ℕ} {θ : ℝ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hap : Aperiodic μ) (hDA : ∃ a, StableDomain μ θ a) {A : Set ℕ} (hA : μ.toMeasure A ≠ 0)
    (hfc : ¬ Integrable (fun z : ℤ => (z : ℝ) ^ 2) (stepLaw μ) → A.Finite ∨ Aᶜ.Finite) :
    (fun n : ℕ => zetaAProb μ A n)
      ~[atTop ⊓ 𝓟 {n : ℕ | (arithFactor μ A : ℤ) ∣ (n : ℤ) - 1}]
      (fun n : ℕ => (μ.toMeasure A).toReal ^ (1 / θ) * Scalar.stableDensity θ 0 *
        (arithFactor μ A : ℝ) / (hSlow μ θ n * (n : ℝ) ^ (1 / θ + 1))) := by
  exact BGWLeaves.GeneralAInf.Asymptotic.thm81_printed_form hc hne hap hDA hA hfc

/-- **Attainable values** (printed "for those `n` such that `P_μ[ζ_A = n] > 0`", the lattice half of
8.1(I)): for large `n`, `P_μ[ζ_A = n] > 0` iff `e ∣ n - 1`.  ("Only if" is the exact vanishing for every
`n`; "if" follows from the limit being positive.)  Proof: from `thm81_corrected_general`. -/
theorem thm81_pos_iff {μ : PMF ℕ} {θ : ℝ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hDA : ∃ a, StableDomain μ θ a) {A : Set ℕ} (hA : μ.toMeasure A ≠ 0) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (bienaymeLaw μ.toMeasure {T | zetaA A T = (n : ℕ∞)} ≠ 0 ↔
        (arithFactor μ A : ℤ) ∣ (n : ℤ) - 1) := by
  exact BGWLeaves.GeneralAInf.Asymptotic.thm81_pos_iff hc hne hDA hA

/-! ## 3. Degenerate sets, and consistency with the other theorems of the paper -/

/-- Edge case `A ≠ ∅` but `μ(A) = 0` (the printed hypothesis "non-empty" does not exclude it): `ζ_A = 0`
almost surely, so `P[ζ_A = n] = 0` for every `n ≥ 1` and the printed statement is vacuous (there is no
`n` with positive probability; the printed constant would be `0^{1/θ} = 0`). -/
theorem zetaA_eq_zero_of_measure_zero {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1) {A : Set ℕ}
    (hA : μ.toMeasure A = 0) {n : ℕ} (hn : 1 ≤ n) :
    bienaymeLaw μ.toMeasure {T | zetaA A T = (n : ℕ∞)} = 0 := by
  exact BGWLeaves.GeneralAInf.Asymptotic.zetaA_eq_zero_of_measure_zero hc hne hA hn

/-- Calibration `A = ℕ` (`ζ_A = ` total progeny, `μ(A) = 1`): `arithFactor μ ℕ = gcd supp μ`
is the lattice span `d` of Remark 1.12 (`1` for aperiodic `μ`). -/
theorem arithFactor_univ_eq_latticeSpan {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1) :
    arithFactor μ Set.univ = Scalar.latticeSpan μ := by
  exact BGWLeaves.GeneralAInf.Asymptotic.arithFactor_univ_eq_latticeSpan hc hne

/-- Calibration `A = ℕ`: `ζ_ℕ(T)` is the size of `T`; the events `{ζ_ℕ = n}` and `{ζ = n}` agree up to the
null set of infinite trees (so `thm81_corrected_general` at `A = ℕ` is Lemma 1.11 / Remark 1.12,
`sizeProb_lattice_asymp`). -/
theorem zetaA_univ_eq_sizeEvent {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1) (n : ℕ) :
    {T : LocallyFinite.Tree | zetaA Set.univ T = (n : ℕ∞)} =ᵐ[bienaymeLaw μ.toMeasure]
      sizeEvent n := by
  exact BGWLeaves.GeneralAInf.Asymptotic.zetaA_univ_eq_sizeEvent hc hne n

/-- Calibration `A = {0}` (`ζ_A = ` number of leaves, up to the null set of infinite trees):
with it the corrected 8.1(I) is Theorem 3.1(ii) (`ltn_ii_tendsto`), `arithFactor μ {0}` being its `g`. -/
theorem zetaA_zero_eq_leafCount {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1) (n : ℕ) :
    bienaymeLaw μ.toMeasure {T | zetaA {0} T = (n : ℕ∞)} =
      bienaymeLaw μ.toMeasure (leafCountEvent n) := by
  exact BGWLeaves.GeneralAInf.Asymptotic.zetaA_zero_eq_leafCount hc hne n

/-! ## 4. The non-functional part of Theorem 8.1(II) (`eq:gen`, `eq:gen2`, factorization, LLN)

Theorem 8.1(II) itself (the joint walk / contour / height limit under `ζ_A = n`) is functional and is
stated in `BGWLeaves.GeneralAFunctional`.  What follows is the discrete content that the printed text
sketches. -/

/-- **A-time-walk identity for forests** (the forest version of `zetaA_blockLaw`, with
the same proof: `natCast_mul_forestAWeight` for `j` trees + `blockLaw_walk`): for `j, n ≥ 1`,
`P_j[ζ_A(F) = n] = (j/n) P[W^ν_n = -j]` where `P_j` is the law of `j` independent `GW_μ` trees. -/
theorem zetaA_forest_blockLaw {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1) (A : Set ℕ)
    {j : ℕ} (hj : 1 ≤ j) {n : ℕ} (hn : 1 ≤ n) :
    (Measure.pi fun _ : Fin j => bienaymeLaw μ.toMeasure)
        {F | ∑ i, zetaA A (F i) = (n : ℕ∞)} =
      (j : ℝ≥0∞) * (n : ℝ≥0∞)⁻¹ * intWalk (blockStep μ A) n {-(j : ℤ)} := by
  exact BGWLeaves.GeneralAInf.Forest.zetaA_forest_blockLaw hc hne A hj hn

/-- **The generalized marked-forest factorization** (the displayed formula after `μ'` on line 2523, the
extension of Proposition 1.6, `prop:K`): for `p ≥ 1`,
`P_j[ζ(F) = p, ζ_A(F) = n] = (j/p) P[S_p = n] P[W'_{p-n} = -U_n - j]`, where `S_p` is the sum of `p`
independent Bernoulli(`μ(A)`) (so `P[S_p = n] = C(p,n) μ(A)^n (1-μ(A))^{p-n}`), `U_n` the `n`-step walk
with law `ρ = insideMarkLaw` and `W'` the walk with law `μ' = outsideMarkLaw`, independent;
`P[W'_{p-n} = -U_n - j] = (ρ^{*n} * μ'^{*(p-n)}){-j}`.  The event is `forestAEvent A j p n`
(finite forests of `j` trees, total size `p`, `n` vertices with out-degree in `A`).  Valid for every `A`
(the two degenerate cases `μ(A) ∈ {0,1}` included: the normalization of a zero measure is multiplied by `0`).
Proof: `pi_bienaymeLaw_forestAEvent`, `natCast_mul_forestAWeight`, `markedWalk_binomial`, `mass_smul_normalized`. -/
theorem marked_forest_factorization {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1) (A : Set ℕ)
    {j p n : ℕ} (hj : 1 ≤ j) (hp : 1 ≤ p) :
    (Measure.pi fun _ : Fin j => bienaymeLaw μ.toMeasure) (forestAEvent A j p n) =
      (j : ℝ≥0∞) * (p : ℝ≥0∞)⁻¹ *
        ((p.choose n : ℝ≥0∞) * (μ.toMeasure A) ^ n * (1 - μ.toMeasure A) ^ (p - n)) *
        ((intWalk (insideMarkLaw μ A) n).conv (intWalk (outsideMarkLaw μ A) (p - n)))
          {-(j : ℤ)} := by
  exact BGWLeaves.GeneralAInf.Forest.marked_forest_factorization hc hne A hj hp

/-- **`eq:gen2`, the concentration step** (the integral over `x ∈ n/μ(A) ± εn` of line 2531, i.e. the
exponentially small remainder `oe(n)`; printed `oe_{1/2}(n)`; we state the cruder `e^{-cn}` bound with
a factor `j`): for `0 < ε`, `j ≥ 1`, `n ≥ 1`, the probability that the forest has `ζ_A(F) = n` and total size
outside `n/μ(A) ± εn` is `≤ C j e^{-c n}`.  Chernoff for `P[S_p = n]` (`BGWLeaves.LeafConcentration.Chernoff`)
and `P[ρ^{*n} * μ'^{*(p-n)} {-j}] ≤ 1`.  **Not needed by the A-time-walk proof of
`thm81_corrected_general` or of `eq_gen_corrected` (it is the paper's route only).** -/
theorem eq_gen2_concentration {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1) {A : Set ℕ}
    (hA : μ.toMeasure A ≠ 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ j n : ℕ, 1 ≤ j → 1 ≤ n →
      (Measure.pi fun _ : Fin j => bienaymeLaw μ.toMeasure)
          (⋃ p ∈ {p : ℕ | ε * n < |(p : ℝ) - n / (μ.toMeasure A).toReal|}, forestAEvent A j p n) ≤
        ENNReal.ofReal (C * j * Real.exp (-c * n)) := by
  exact BGWLeaves.GeneralAInf.Forest.eq_gen2_concentration hc hne hA hε

/-- **The law of large numbers for the inside-mark sum** (line 2535: "`P[|U_n - n E U_1| > εn] < ε` for
`n` large"), for the law `ρ = insideMarkLaw μ A` (integrable, because `μ(A) ρ ≤ stepLaw μ`): the walk
`U_n` satisfies the weak law.  Proof: Mathlib's `ProbabilityTheory.strong_law_ae`, via the identification
of `intWalk` with the law of an i.i.d. sum.  **Paper's route only: the A-time-walk proof does
not use it.** -/
theorem insideMark_LLN {μ : PMF ℕ} (hc : IsCritical μ) {A : Set ℕ} (hA : μ.toMeasure A ≠ 0)
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => (intWalk (insideMarkLaw μ A) n).real
        {z : ℤ | ε * n < |(z : ℝ) - n * mean (insideMarkLaw μ A)|}) atTop (𝓝 0) := by
  exact BGWLeaves.GeneralAInf.Forest.insideMark_LLN hc hA hε

/-- **`eq:gen`, CORRECTED** (line 2512-2514; uniform local limit for forests with `j ≤ αB_n` trees).
Printed: `sup_{1 ≤ j ≤ αB_n} |n P_j[ζ_A(F) = n] - q₁(j / B_{n/μ(A)})| → 0`.  The printed display has no
lattice indicator and no factor `e`, so it fails for `e ≥ 2` (the same defect as correction 5 of
`FORMALIZATION_REPORT.md`); the corrected form:
`P_j[ζ_A(F) = n] = 0` unless `e ∣ n - j` and
`sup_{1 ≤ j ≤ αB_n} |n P_j[ζ_A(F) = n] - e 1{e ∣ n-j} q₁(j / B_{⌊n/μ(A)⌋})| → 0`.
(For `e = 1` and `A = {0}` it is the printed display.)  Uniform in `j` by the uniform lattice local limit
for `ν`: `n P_j = j P[W^ν_n = -j]`.  Proof: `zetaA_forest_blockLaw`,
`llt_lattice_abstract`, `blockStep_isStableAttracted`, `norming_floor_ratio`.
Same strengthened hypotheses as `thm81_corrected_general`. -/
theorem eq_gen_corrected {μ : PMF ℕ} {θ : ℝ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hDA : ∃ a, StableDomain μ θ a) {A : Set ℕ} (hA : μ.toMeasure A ≠ 0) {α : ℝ} (hα : 0 < α)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ j : ℕ, 1 ≤ j → (j : ℝ) ≤ α * norming (stepLaw μ) θ n →
      |(n : ℝ) * (Measure.pi fun _ : Fin j => bienaymeLaw μ.toMeasure).real
            {F | ∑ i, zetaA A (F i) = (n : ℕ∞)} -
          (if (arithFactor μ A : ℤ) ∣ (n : ℤ) - j then
            (arithFactor μ A : ℝ) *
              q₁ θ (j / norming (stepLaw μ) θ ⌊(n : ℝ) / (μ.toMeasure A).toReal⌋₊)
           else 0)| ≤ ε := by
  exact BGWLeaves.GeneralAInf.BlockLocal.eq_gen_corrected hc hne hDA hA hα hε

/-- The exact vanishing for forests: `P_j[ζ_A(F) = n] = 0` unless `e ∣ n - j` (all `n ≥ 0`, `j ≥ 1`, every
critical `μ`; the corrected lattice of `eq:gen`).  For `n ≥ 1` it follows from `zetaA_forest_blockLaw`
and `MarkedSpan.blockLaw_span`.  **The case `n = 0` is not covered by `zetaA_forest_blockLaw` (which needs
`n ≥ 1`):** if `0 ∈ A` then every finite forest of `j ≥ 1` trees has at least `j` leaves, all
vertices of out-degree `0 ∈ A`, so `ζ_A(F) ≥ j ≥ 1` and `{ζ_A(F) = 0}` is null (infinite forests are null in the
critical case); if `0 ∉ A` then `0 ∈ supp μ ∖ A` (critical, `μ 1 ≠ 1`, so `μ 0 > 0`) gives `-1 ∈ arithSet μ A`, hence
`e = 1` and the hypothesis `¬ (1 ∣ -j)` is false. -/
theorem zetaA_forest_eq_zero_of_not_dvd {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1) (A : Set ℕ)
    {j n : ℕ} (hj : 1 ≤ j) (hn : ¬ ((arithFactor μ A : ℤ) ∣ (n : ℤ) - j)) :
    (Measure.pi fun _ : Fin j => bienaymeLaw μ.toMeasure)
        {F | ∑ i, zetaA A (F i) = (n : ℕ∞)} = 0 := by
  exact BGWLeaves.GeneralAInf.Forest.zetaA_forest_eq_zero_of_not_dvd hc hne A hj hn

/-! ## 5. Theorem 8.1(II), functional part

`Theorem 8.1(II)`: for `n` with `P_μ[ζ_A(τ) = n] > 0`, the rescaled triple `(W, C, H)` of `τ_n ~ P_μ[· | ζ_A = n]`
(random time scale `ζ(τ_n)`, spatial scale `B_{ζ(τ_n)}`) converges in distribution to `(𝕏, ℍ, ℍ)`.  Not stated
here: it is a functional limit theorem, stated and proved in `BGWLeaves.GeneralAFunctional` on top of the
Section 4-6 path laws. -/

end BGWLeaves
