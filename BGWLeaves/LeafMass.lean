module

public import BGWLeaves.LeafMass.Defs
import BGWLeaves.LeafMass.Proof

/-!
# Exact leaf counts (M4b): the results still to be proved

Source: arXiv:1110.2163v4, `largetrees_final.tex`, Section 3: Theorem 3.1 (`thm:ltn`, lines
864-882), the remark after it (line 880), Corollary 3.3 (`cor:Lambda`, lines 890-896), Section 3.1
(the law of `Y = (K - 1 | K > 0)`, `eq:Y`, `eq:ll`, lines 904-932) and Section 3.2 (the lattice case
and the periodic remark, lines 1074-1096).  Remark 3.2 (line 885, "in the finite variance case
Theorem 3.1 is a consequence of results contained in [Minami]") is bibliographic: it has no
declaration, and its claim is covered by `thm_ltn_finiteVariance`.  Lemma 3.4 (`lem:hhp`) and
Theorem 3.5 (`thm:strongLL`) are proved in M3 (`BGWLeaves.StableAnalysis`) and not restated.

Each declaration here is a statement approved for freezing; its proof is to be supplied in the
provider modules `BGWLeaves.LeafMass.*` (imported through `BGWLeaves.LeafMass.Proof`).  Definitions
and proved bridges are in `BGWLeaves.LeafMass.Defs`.  Four declarations (`thm_ltn_i`,
`thm_ltn_finiteVariance`, `cor_Lambda`, `rem_periodic_ltn_i`) are proved assemblies of other
statements of this file and need no provider declaration.

Layout.
* Printed forms (stated with `gcd(b-1,d)` for the pair `(d, b)` of `IsSuppSpan`): `thm_ltn_i`,
  `thm_ltn_ii`, `thm_ltn_finiteVariance`, `cor_Lambda`.
* Arithmetic forms (stated with `arithFactor μ {0}` of `BGWLeaves.GeneralA.Defs`; the proof targets and
  the working interface for later milestones): `ltn_i_arith`, `leafProb_eq_zero_of_not_dvd`,
  `ltn_ii_tendsto`, `thm_ltn_finiteVariance_arith`, `cor_Lambda_arith`, `cor_Lambda_isOe`.
* Bridges between the two: `int_gcd_eq_arithFactor`, `exists_isSuppSpan`.
* Interfaces on the law `Y` (`etaLaw μ`): `etaLaw_isStableAttracted`, `etaLaw_norming`,
  `llt_etaLaw_nonlattice`, `llt_etaLaw_lattice`.
* Remark-level coverage entries: `suppNonLattice_iff`, `example_047`, `example_28_40_52`,
  `example_3_6`, `exists_examples`, `rem_periodic_ltn_i`, `rem_periodic_ltn_ii`.

Proof-dependency rule: the finite-variance forms are derived from `ltn_ii_tendsto`, independently of
Theorem 8.1(I) (M10); the case `A = {0}` of the frozen corrected 8.1(I) may later be derived from
M4b, never the reverse.
-/

@[expose] public section

namespace BGWLeaves

open MeasureTheory ProbabilityTheory Filter Asymptotics BGW
open BGW.StableTrees BGW.LocallyFinite BGWLeaves.StableAnalysis
open scoped ENNReal Topology

/-! ## Arithmetic bridges between `gcd(b-1,d)` and `arithFactor μ {0}` -/

/-- Non-vacuity of the pair `(d, b)` of Theorem 3.1 (line 864): under `(H_θ)(i),(iii)` (critical,
`μ 1 ≠ 1`, aperiodic) the pair exists, because `supp μ ∖ {0}` has at least two points (a single
point `{k}` would force `μ = (1-1/k)δ₀ + (1/k)δ_k`, whose support generates `kℤ`, so `k = 1`, excluded
by `μ 1 ≠ 1`).  It can fail for a periodic `μ` (`supp μ = {0, 2}`). -/
theorem exists_isSuppSpan {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1) (hap : Aperiodic μ) :
    ∃ d b : ℕ, IsSuppSpan μ d b := by
  exact BGWLeaves.LeafMass.Arithmetic.exists_isSuppSpan hc hne hap

/-- **The bridge `gcd(b-1, d) = arithFactor μ {0}`** between the printed constant of Theorem 3.1
(line 866) and the object `arithFactor` of `BGWLeaves.GeneralA.Defs` (Theorem 8.1(I)): for the pair
`(d, b)` of `IsSuppSpan`, the printed `gcd(b-1,d)` is the largest positive integer dividing all the
`k - 1`, `k ∈ supp μ ∖ {0}` (the set `arithSet μ {0}` is `{0}` together with these `k - 1`; the
element `0` changes no gcd).  In particular, for `A = {0}` the corrected constant of Theorem 8.1(I)
is exactly the printed constant of Theorem 3.1. -/
theorem int_gcd_eq_arithFactor {μ : PMF ℕ} {d b : ℕ} (h : IsSuppSpan μ d b) :
    Int.gcd ((b : ℤ) - 1) (d : ℤ) = arithFactor μ {0} := by
  exact BGWLeaves.LeafMass.Arithmetic.int_gcd_eq_arithFactor h

/-- The remark after Theorem 3.1 (line 880): `supp μ ∖ {0}` is non-lattice (not contained in
`b' + d'ℤ` for any `d' ≥ 2`) iff `d = 1` (and then automatically `b = 0`), for the pair `(d, b)` of
`IsSuppSpan`.  This is also the identification "`Y` non-lattice iff `b = 0` and `d = 1`" of
Section 3.1 (line 906) at the level of `supp μ ∖ {0}`. -/
theorem suppNonLattice_iff {μ : PMF ℕ} {d b : ℕ} (h : IsSuppSpan μ d b) :
    (¬ ∃ (b' : ℤ) (d' : ℕ), 2 ≤ d' ∧ ∀ k : ℕ, μ k ≠ 0 → k ≠ 0 → (d' : ℤ) ∣ (k : ℤ) - b') ↔
      d = 1 ∧ b = 0 := by
  exact BGWLeaves.LeafMass.Remarks.suppNonLattice_iff h

/-- The example of line 882 (the remark after Theorem 3.1): a `μ` with `supp μ = {0, 4, 7}` is
aperiodic, but `supp μ ∖ {0}` is lattice: `d = 3`, `b = 1`, `gcd(b - 1, d) = 3`.  (Non-vacuity of the
hypothesis: `exists_examples`, third component.) -/
theorem example_047 {μ : PMF ℕ} (hsupp : ∀ k, μ k ≠ 0 ↔ k = 0 ∨ k = 4 ∨ k = 7) :
    Aperiodic μ ∧ IsSuppSpan μ 3 1 ∧ Int.gcd ((1 : ℤ) - 1) 3 = 3 := by
  exact BGWLeaves.LeafMass.Remarks.example_047 hsupp

/-! ## Theorem 3.1 (`thm:ltn`), part (i) -/

/-- **Theorem 3.1(i), exact "only if" half** (line 1081, valid for every `n`), arithmetic form: if
`arithFactor μ {0} ∤ n` then `P_μ[λ = n+1] = 0`.  Only criticality and `μ 1 ≠ 1` are used. -/
theorem leafProb_eq_zero_of_not_dvd {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1) {n : ℕ}
    (hn : ¬ arithFactor μ {0} ∣ n) : leafProb μ (n + 1) = 0 := by
  exact BGWLeaves.LeafMass.Arithmetic.leafProb_eq_zero_of_not_dvd hc hne hn

/-- **Theorem 3.1(i)**, arithmetic form (with `g = arithFactor μ {0}`): there is `N` such that for
every `n ≥ N`, `P_μ[λ = n+1] > 0` iff `g ∣ n`.  Only criticality and `μ 1 ≠ 1` are used (the argument
is the additive monoid generated by `supp Y`, Section 3.2, lines 1081-1083; no analysis).  It is
stronger than the printed statement: aperiodicity and the domain of attraction are not needed, and
`g` is always defined (also when `supp μ ∖ {0}` is a single point). -/
theorem ltn_i_arith {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → (0 < leafProb μ (n + 1) ↔ arithFactor μ {0} ∣ n) := by
  exact BGWLeaves.LeafMass.Arithmetic.ltn_i_arith hc hne

set_option linter.unusedVariables false in
/-- **Theorem 3.1(i)** as printed (`largetrees_final.tex`, line 868), under `(H_θ)`: for the pair
`(d, b)` of `IsSuppSpan` (`d` the largest integer and `b` the least natural number with
`supp μ ∖ {0} ⊂ b + dℤ`), there is `N` such that for every `n ≥ N`, `P_μ[λ = n+1] > 0` iff
`gcd(b-1,d) ∣ n`.  Assembled from `ltn_i_arith` and `int_gcd_eq_arithFactor`; the hypotheses `hDA`,
`hap` (those of `(H_θ)`) are not used. -/
theorem thm_ltn_i {μ : PMF ℕ} {θ : ℝ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hDA : ∃ a, StableDomain μ θ a) (hap : Aperiodic μ) {d b : ℕ} (hdb : IsSuppSpan μ d b) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → (0 < leafProb μ (n + 1) ↔ Int.gcd ((b : ℤ) - 1) (d : ℤ) ∣ n) := by
  obtain ⟨N, hN⟩ := ltn_i_arith hc hne
  exact ⟨N, fun n hn => by rw [int_gcd_eq_arithFactor hdb]; exact hN n hn⟩

/-! ## Theorem 3.1 (`thm:ltn`), part (ii) -/

/-- **Theorem 3.1(ii), the limit form** (the proof target): under `(H_θ)`, along `n → ∞` in the
multiples of `g = arithFactor μ {0}` (the filter `atTop ⊓ 𝓟 {n | g ∣ n}`),
`n B_n P_μ[λ = n+1] → μ₀^{1/θ} p₁(0) g`, with `B_n = norming (stepLaw μ) θ n = h(n) n^{1/θ}` the
corrected norming (`MANUSCRIPT_RECOMMENDATIONS.md` R2, R4) and `p₁ = Scalar.stableDensity θ`. -/
theorem ltn_ii_tendsto {μ : PMF ℕ} {θ : ℝ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hap : Aperiodic μ) (hDA : ∃ a, StableDomain μ θ a) :
    Tendsto (fun n : ℕ => (n : ℝ) * norming (stepLaw μ) θ n * leafProb μ (n + 1))
      (atTop ⊓ 𝓟 {n : ℕ | arithFactor μ {0} ∣ n})
      (𝓝 ((μ 0).toReal ^ (1 / θ) * Scalar.stableDensity θ 0 * (arithFactor μ {0} : ℝ))) := by
  exact BGWLeaves.LeafMass.LeafLocalLimit.ltn_ii_tendsto hc hne hap hDA

/-- **Theorem 3.1(ii)** as printed (`largetrees_final.tex`, line 870), under `(H_θ)`:
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
  exact BGWLeaves.LeafMass.LeafLocalLimit.thm_ltn_ii hc hne hap hDA hdb

/-- **Theorem 3.1, finite-variance form** (line 873: "in particular, when the second moment of `μ`
is finite"), arithmetic form: if `W₁` has finite variance `σ² = variance (stepLaw μ)`, then along the
multiples of `g = arithFactor μ {0}`, `P_μ[λ = n+1] ∼ √(μ₀/(2πσ²)) g n^{-3/2}`.  It is the
specialization of `ltn_ii_tendsto` at `θ = 2` (`B_n = σ√(n/2)`, `p₁(0) = 1/√(4π)`), and must be
proved from it, independently of Theorem 8.1(I) (M10); it is also the case `A = {0}` of the frozen
corrected `BGWLeaves.thm81_finiteVariance_corrected`. -/
theorem thm_ltn_finiteVariance_arith {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hap : Aperiodic μ) (hfin : Integrable (fun z : ℤ => (z : ℝ) ^ 2) (stepLaw μ)) :
    (fun n : ℕ => leafProb μ (n + 1)) ~[atTop ⊓ 𝓟 {n : ℕ | arithFactor μ {0} ∣ n}]
      (fun n : ℕ => Real.sqrt ((μ 0).toReal / (2 * Real.pi * variance (stepLaw μ))) *
        (arithFactor μ {0} : ℝ) * (n : ℝ) ^ (-(3 : ℝ) / 2)) := by
  exact BGWLeaves.LeafMass.LeafLocalLimit.thm_ltn_finiteVariance_arith hc hne hap hfin

/-- **Theorem 3.1, finite-variance form** as printed (`largetrees_final.tex`, line 873), with
`gcd(b-1,d)` for the pair `(d, b)` of `IsSuppSpan`: `P_μ[λ = n+1] ∼ √(μ₀/(2πσ²)) gcd(b-1,d) n^{-3/2}`
along the multiples of `gcd(b-1,d)`.  Assembled from `thm_ltn_finiteVariance_arith` and
`int_gcd_eq_arithFactor`.  This is also the claim that Remark 3.2 attributes to [Minami]. -/
theorem thm_ltn_finiteVariance {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hap : Aperiodic μ) (hfin : Integrable (fun z : ℤ => (z : ℝ) ^ 2) (stepLaw μ))
    {d b : ℕ} (hdb : IsSuppSpan μ d b) :
    (fun n : ℕ => leafProb μ (n + 1)) ~[atTop ⊓ 𝓟 {n : ℕ | Int.gcd ((b : ℤ) - 1) (d : ℤ) ∣ n}]
      (fun n : ℕ => Real.sqrt ((μ 0).toReal / (2 * Real.pi * variance (stepLaw μ))) *
        (Int.gcd ((b : ℤ) - 1) (d : ℤ) : ℝ) * (n : ℝ) ^ (-(3 : ℝ) / 2)) := by
  have := thm_ltn_finiteVariance_arith hc hne hap hfin
  rwa [int_gcd_eq_arithFactor hdb]

/-! ## Corollary 3.3 (`cor:Lambda`) -/

/-- **Corollary 3.3** (`largetrees_final.tex`, lines 890-896), arithmetic form.  Fix `δ > 0`,
`η ∈ (0,1)`: `P_μ[ sup_{η ≤ t ≤ 1} |Λ_τ(ζ t)/(ζ t) - μ₀| ≥ δ n^{-1/4} | λ = n ] = oe_{1/2}(n)` as
`n - 1` tends to infinity in the multiples of `g = arithFactor μ {0}` (`IsOeOn` on
`{n | 1 ≤ n ∧ g ∣ n - 1}`).  The denominator is `ζ t` (the random size `t.size`), the threshold
`δ n^{-1/4}` has the fixed `n`, and the conditioning is on the number of leaves (`leafCountEvent n`;
`ProbabilityTheory.cond`, the conditional law of a null event is `0`).  The paper's proof: `{λ = n} ⊂
{ζ ≥ n}`, Corollary 2.6 (`cor_GD2mieux`) and `P[λ = n] ≥ n^{-A}` from Theorem 3.1(ii). -/
theorem cor_Lambda_arith {μ : PMF ℕ} {θ : ℝ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hap : Aperiodic μ) (hDA : ∃ a, StableDomain μ θ a) {η δ : ℝ}
    (hη0 : 0 < η) (hη1 : η < 1) (hδ : 0 < δ) :
    IsOeOn {n : ℕ | 1 ≤ n ∧ arithFactor μ {0} ∣ n - 1} (1 / 2) fun n : ℕ =>
      (((bienaymeLaw μ.toMeasure)[|leafCountEvent n]).real
        (finiteTreeEvent fun t =>
          ENNReal.ofReal (δ / (n : ℝ) ^ (1 / 4 : ℝ)) ≤
            supDev η (treeLeafDev (μ 0).toReal t (t.size : ℝ)))) := by
  exact BGWLeaves.LeafMass.CorLambda.cor_Lambda_arith hc hne hap hDA hη0 hη1 hδ

/-- **Corollary 3.3** as printed (`largetrees_final.tex`, lines 890-896), with `gcd(b-1,d)` for the
pair `(d, b)` of `IsSuppSpan`.  Assembled from `cor_Lambda_arith` and `int_gcd_eq_arithFactor`. -/
theorem cor_Lambda {μ : PMF ℕ} {θ : ℝ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hap : Aperiodic μ) (hDA : ∃ a, StableDomain μ θ a) {d b : ℕ} (hdb : IsSuppSpan μ d b)
    {η δ : ℝ} (hη0 : 0 < η) (hη1 : η < 1) (hδ : 0 < δ) :
    IsOeOn {n : ℕ | 1 ≤ n ∧ Int.gcd ((b : ℤ) - 1) (d : ℤ) ∣ n - 1} (1 / 2) fun n : ℕ =>
      (((bienaymeLaw μ.toMeasure)[|leafCountEvent n]).real
        (finiteTreeEvent fun t =>
          ENNReal.ofReal (δ / (n : ℝ) ^ (1 / 4 : ℝ)) ≤
            supDev η (treeLeafDev (μ 0).toReal t (t.size : ℝ)))) := by
  have := cor_Lambda_arith hc hne hap hDA hη0 hη1 hδ
  rwa [int_gcd_eq_arithFactor hdb]

/-- Corollary 3.3 for **all** `n` (not a printed statement; a convenience for the users of the
corollary, with Lean's conditioning convention that the conditional law of a null event is `0`): for
`n ≥ 1` with `g ∤ n - 1` the event `{λ = n}` is null (`leafProb_eq_zero_of_not_dvd`) and `{λ = 0}` is
empty, so `cor_Lambda_arith` upgrades from the set `{n | 1 ≤ n ∧ g ∣ n - 1}` to `IsOe (1/2)` on all
`n`. -/
theorem cor_Lambda_isOe {μ : PMF ℕ} {θ : ℝ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hap : Aperiodic μ) (hDA : ∃ a, StableDomain μ θ a) {η δ : ℝ}
    (hη0 : 0 < η) (hη1 : η < 1) (hδ : 0 < δ) :
    IsOe (1 / 2) fun n : ℕ =>
      (((bienaymeLaw μ.toMeasure)[|leafCountEvent n]).real
        (finiteTreeEvent fun t =>
          ENNReal.ofReal (δ / (n : ℝ) ^ (1 / 4 : ℝ)) ≤
            supDev η (treeLeafDev (μ 0).toReal t (t.size : ℝ)))) := by
  exact BGWLeaves.LeafMass.CorLambda.cor_Lambda_isOe hc hne hap hDA hη0 hη1 hδ

/-! ## Section 3.1: the law of `Y = (K - 1 | K > 0)` (`eq:Y`, `eq:ll`) -/

/- Already proved in M3 and not restated: `mean_etaLaw` (`E[Y] = μ₀/(1-μ₀)`), `integrable_sq_etaLaw`,
`variance_etaLaw`, `finiteVariance_norming_ratio_eta`, `lem_hhp` (Lemma 3.4: `B'_n/B_n → (1-μ₀)^{-1/θ}`
when `σ² = ∞`), `strongLLT` (Theorem 3.5). -/

/-- "`Y` is in the domain of attraction of a stable law of index `θ`" (`largetrees_final.tex`,
Section 3.1, line 910): `Y` (`etaLaw μ`, the law of `K - 1` given `K ≥ 1`) lies in the domain of
attraction of the stable law of the same index `θ` and the same normalized limit `X₁`: there is a
norming `b` with `IsStableAttracted (etaLaw μ) θ (mean (etaLaw μ)) b`.  Hypotheses: `μ` critical,
`μ 1 ≠ 1`, in the domain of attraction of index `θ`; no aperiodicity.

**Hypothesis `hS`** (non-degeneracy of `Y`: `supp μ ∖ {0}` contains two distinct points
`1 ≤ k₁ < k₂`, equivalently `∃ d b, IsSuppSpan μ d b`): the paper's claim tacitly uses it.  Without it
the statement is false, e.g. for `μ = ½δ₀ + ½δ₂`, where `Y ≡ 1` is degenerate and is not attracted to a
non-degenerate stable law.  `hS` follows from aperiodicity under `(H_θ)` (`exists_isSuppSpan`) and is
kept off `Aperiodic` so that the periodic remark can reuse it.  The paper's argument: Ibragimov-Linnik
Theorem 2.6.1 when `σ² = ∞` (the tail of `Y` is the tail of `K - 1` divided by `1 - μ₀`), and finite
second moment of `Y` when `σ² < ∞`. -/
theorem etaLaw_isStableAttracted {μ : PMF ℕ} {θ : ℝ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hS : ∃ k₁ k₂ : ℕ, 1 ≤ k₁ ∧ k₁ < k₂ ∧ μ k₁ ≠ 0 ∧ μ k₂ ≠ 0)
    (hDA : ∃ a, StableDomain μ θ a) :
    ∃ b : ℕ → ℝ, IsStableAttracted (etaLaw μ) θ (mean (etaLaw μ)) b := by
  exact BGWLeaves.LeafMass.YLaw.etaLaw_isStableAttracted hc hne hS hDA

/-- The norming of Theorem 1.10 for `W'` (the sum of `n` copies of `Y`; `largetrees_final.tex`,
Section 3.1, lines 913-920): `B'_n = norming (etaLaw μ) θ n` is a valid norming for the domain of
attraction of `Y`, it is nondecreasing, and `B'_n = h'(n) n^{1/θ}` with `h'` slowly varying.
Hypothesis `hS` (non-degeneracy of `Y`: two distinct support points `1 ≤ k₁ < k₂` of `μ`) is the one
of `etaLaw_isStableAttracted`: the paper's claim tacitly uses it, and it is false for
`μ = ½δ₀ + ½δ₂` (`Y ≡ 1`). -/
theorem etaLaw_norming {μ : PMF ℕ} {θ : ℝ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hS : ∃ k₁ k₂ : ℕ, 1 ≤ k₁ ∧ k₁ < k₂ ∧ μ k₁ ≠ 0 ∧ μ k₂ ≠ 0)
    (hDA : ∃ a, StableDomain μ θ a) :
    IsStableAttracted (etaLaw μ) θ (mean (etaLaw μ)) (norming (etaLaw μ) θ) ∧
      Monotone (norming (etaLaw μ) θ) ∧
      SlowlyVarying (fun x : ℝ => norming (etaLaw μ) θ ⌊x⌋₊ / x ^ (1 / θ)) := by
  exact BGWLeaves.LeafMass.YLaw.etaLaw_norming hc hne hS hDA

/-- **`eq:ll`** (`largetrees_final.tex`, line 915): the centered uniform local limit theorem for `W'`
(the sum of `n` copies of `Y`) when `Y` is non-lattice (`¬ IsLatticeLaw (etaLaw μ)`, i.e. `b = 0`,
`d = 1`): for every `ε > 0`, for all large `n` and all `k ∈ ℤ`,
`|B'_n P[W'_n = k] - p₁((k - n E[Y]) / B'_n)| ≤ ε`, with `E[Y] = μ₀/(1-μ₀)` written explicitly and
`B'_n = norming (etaLaw μ) θ n`.  This is Theorem 1.10(iii) (`locallimit_iii`) for `ν = etaLaw μ`.
Hypothesis `hS` (non-degeneracy of `Y`: two distinct support points `1 ≤ k₁ < k₂` of `μ`) is the one
of `etaLaw_isStableAttracted`: the paper's claim tacitly uses it, and it is false for
`μ = ½δ₀ + ½δ₂` (`Y ≡ 1`). -/
theorem llt_etaLaw_nonlattice {μ : PMF ℕ} {θ : ℝ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hS : ∃ k₁ k₂ : ℕ, 1 ≤ k₁ ∧ k₁ < k₂ ∧ μ k₁ ≠ 0 ∧ μ k₂ ≠ 0)
    (hDA : ∃ a, StableDomain μ θ a) (hnl : ¬ IsLatticeLaw (etaLaw μ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ k : ℤ,
      |norming (etaLaw μ) θ n * intWalkProb (etaLaw μ) n k -
          Scalar.stableDensity θ
            (((k : ℝ) - n * ((μ 0).toReal / (1 - (μ 0).toReal))) / norming (etaLaw μ) θ n)| ≤ ε := by
  exact BGWLeaves.LeafMass.YLaw.llt_etaLaw_nonlattice hc hne hS hDA hnl hε

/-- **The lattice local limit theorem for `W'`** (Section 3.2, line 1085: "the Local Limit Theorem
for lattice random variables, see [IL, Theorem 4.2.1]"; the manuscript omits the argument), for the
pair `(d, b)` of `IsSuppSpan`: for every `ε > 0`, for all large `n` and all `k ∈ ℤ`,
`|B'_n P[W'_n = k] - d p₁((k - n c)/B'_n) 1{d ∣ k - n (b-1)}| ≤ ε`, with `c = μ₀/(1-μ₀) = E[Y]` and
`B'_n = norming (etaLaw μ) θ n`.  The mass of a lattice point is `d` times the density; for `d = 1` it
is `llt_etaLaw_nonlattice`.  Proved here, not in the manuscript. -/
theorem llt_etaLaw_lattice {μ : PMF ℕ} {θ : ℝ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hDA : ∃ a, StableDomain μ θ a) {d b : ℕ} (hdb : IsSuppSpan μ d b) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ k : ℤ,
      |norming (etaLaw μ) θ n * intWalkProb (etaLaw μ) n k -
          (if (d : ℤ) ∣ k - n * ((b : ℤ) - 1) then
            (d : ℝ) * Scalar.stableDensity θ
              (((k : ℝ) - n * ((μ 0).toReal / (1 - (μ 0).toReal))) / norming (etaLaw μ) θ n)
          else 0)| ≤ ε := by
  exact BGWLeaves.LeafMass.YLaw.llt_etaLaw_lattice hc hne hDA hdb hε

/-! ## Section 3.2: the periodic remark (lines 1088-1096), a remark, not the standing hypothesis -/

set_option linter.unusedVariables false in
/-- **Remark (periodic case), Theorem 3.1(i)** (`largetrees_final.tex`, lines 1088-1092: "Theorem 3.1
remains valid in this case"): this is `ltn_i_arith`, whose proof does not use aperiodicity (the
printed `gcd(b-1,d)` is replaced by `arithFactor μ {0}`, which is defined also when `supp μ ∖ {0}`
is a single point and no pair `(d, b)` exists).  `hper` is not used. -/
theorem rem_periodic_ltn_i {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1) (hper : ¬ Aperiodic μ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → (0 < leafProb μ (n + 1) ↔ arithFactor μ {0} ∣ n) :=
  ltn_i_arith hc hne

/-- **Remark (periodic case), Theorem 3.1(ii)** (`largetrees_final.tex`, lines 1088-1092: "the same
reasoning as above shows that Theorem 3.1 remains valid"; a sketch in the source): the periodic
extension of `ltn_ii_tendsto` to a periodic `μ` (`hper : ¬ Aperiodic μ`).  The hypotheses `hper` and
`hap` of `ltn_ii_tendsto` cover complementary cases, so this statement is the periodic extension of
the aperiodic one, not a strengthening of it.  The constant is the same, `μ₀^{1/θ} p₁(0) g` with
`g = arithFactor μ {0}`: the lattice factor `d` of the `Y`-walk is shared out among the allowable
summands, while it appears in the size law only for `n ≡ 1 mod d`.  Checked numerically.  The
single-positive-support subcase `μ = {0, k}` (`Y` degenerate, no `IsSuppSpan`) needs separate
treatment: the non-degeneracy hypothesis `hS` of the `Y`-law interfaces cannot be assumed for the
periodic mass asymptotic, and the local limit theorem for `Y` does not apply there. -/
theorem rem_periodic_ltn_ii {μ : PMF ℕ} {θ : ℝ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hper : ¬ Aperiodic μ) (hDA : ∃ a, StableDomain μ θ a) :
    Tendsto (fun n : ℕ => (n : ℝ) * norming (stepLaw μ) θ n * leafProb μ (n + 1))
      (atTop ⊓ 𝓟 {n : ℕ | arithFactor μ {0} ∣ n})
      (𝓝 ((μ 0).toReal ^ (1 / θ) * Scalar.stableDensity θ 0 * (arithFactor μ {0} : ℝ))) := by
  exact BGWLeaves.LeafMass.Remarks.rem_periodic_ltn_ii hc hne hper hDA

/-- The first example of the periodic remark (`largetrees_final.tex`, line 1094: `supp μ =
{0, 28, 40, 52}`): `μ` is periodic (span `4`), `supp μ ∖ {0} = {28, 40, 52}` has `d = 12`, `b = 4`,
`gcd(b-1, d) = 3 = arithFactor μ {0}`, and `P[λ = n] = 0` for infinitely many `n` (every `n ≢ 1 mod 3`).
Non-vacuity: `exists_examples` (`μ k = 1/120` for `k = 28, 40, 52`). -/
theorem example_28_40_52 {μ : PMF ℕ} (hc : IsCritical μ)
    (hsupp : ∀ k, μ k ≠ 0 ↔ k = 0 ∨ k = 28 ∨ k = 40 ∨ k = 52) :
    ¬ Aperiodic μ ∧ IsSuppSpan μ 12 4 ∧ arithFactor μ {0} = 3 ∧
      {n : ℕ | leafProb μ n = 0}.Infinite := by
  exact BGWLeaves.LeafMass.Remarks.example_28_40_52 hc hsupp

/-- The second example of the periodic remark (`largetrees_final.tex`, line 1095: `supp μ = {0, 3, 6}`):
`μ` is periodic (span `3`), `d = 3`, `b = 0`, `gcd(b-1,d) = 1 = arithFactor μ {0}`, and the set of `n`
with `P[λ = n] = 0` is exactly `{0, 2, 4}` (the monoid generated by `supp Y = {2, 5}` is
`{0, 2, 4, 5, 6, ...}`), a finite set.  Non-vacuity: `exists_examples` (`μ 3 = 1/6`, `μ 6 = 1/12`). -/
theorem example_3_6 {μ : PMF ℕ} (hc : IsCritical μ)
    (hsupp : ∀ k, μ k ≠ 0 ↔ k = 0 ∨ k = 3 ∨ k = 6) :
    ¬ Aperiodic μ ∧ IsSuppSpan μ 3 0 ∧ arithFactor μ {0} = 1 ∧
      {n : ℕ | leafProb μ n = 0} = {0, 2, 4} := by
  exact BGWLeaves.LeafMass.Remarks.example_3_6 hc hsupp

/-- Non-vacuity of the examples (`example_047`, `example_28_40_52`, `example_3_6`): critical laws with
the supports `{0, 28, 40, 52}`, `{0, 3, 6}` and `{0, 4, 7}` exist. -/
theorem exists_examples :
    (∃ μ : PMF ℕ, IsCritical μ ∧ ∀ k, μ k ≠ 0 ↔ k = 0 ∨ k = 28 ∨ k = 40 ∨ k = 52) ∧
    (∃ μ : PMF ℕ, IsCritical μ ∧ ∀ k, μ k ≠ 0 ↔ k = 0 ∨ k = 3 ∨ k = 6) ∧
    (∃ μ : PMF ℕ, IsCritical μ ∧ ∀ k, μ k ≠ 0 ↔ k = 0 ∨ k = 4 ∨ k = 7) := by
  exact BGWLeaves.LeafMass.Remarks.exists_examples

end BGWLeaves
