module

public import BGWLeaves.StableAnalysis.Defs
import BGWLeaves.StableAnalysis.Proof

/-!
# Scalar stable analysis (M3): the results still to be proved

Source: arXiv:1110.2163v4, `largetrees_final.tex`.  Each declaration here is a statement approved
for freezing; its proof is to be supplied in the provider modules `BGWLeaves.StableAnalysis.*`
(imported through `BGWLeaves.StableAnalysis.Proof`).  Definitions and proved bridges are in
`BGWLeaves.StableAnalysis.Defs`; proved results depending on these statements are in
`BGWLeaves.StableAnalysis.Consequences`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal

namespace BGWLeaves.StableAnalysis

open BGW.StableTrees
open BGW.LocallyFinite (bienaymeLaw sizeEvent FiniteVertices Present)

/-! ## 1. Proposition 1.7 (`prop:slow`), slowly varying functions -/

section SlowVariation

variable {L : ℝ → ℝ}

/-- 1.7(i), first half. -/
theorem slow_rpow_mul_tendsto_atTop (hmeas : Measurable L) (hnn : ∀ x, 0 < x → 0 ≤ L x)
    (hL : SlowlyVarying L) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun x : ℝ => x ^ ε * L x) atTop atTop := by
  exact BGWLeaves.StableAnalysis.SlowVariation.slow_rpow_mul_tendsto_atTop hmeas hnn hL hε

/-- 1.7(i), second half. -/
theorem slow_rpow_neg_mul_tendsto_zero (hmeas : Measurable L) (hnn : ∀ x, 0 < x → 0 ≤ L x)
    (hL : SlowlyVarying L) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun x : ℝ => x ^ (-ε) * L x) atTop (𝓝 0) := by
  exact BGWLeaves.StableAnalysis.SlowVariation.slow_rpow_neg_mul_tendsto_zero hmeas hnn hL hε

/-- 1.7(ii) (Potter bounds): one `C > 1` for all large integers `n` and all real `x ≥ 1`. -/
theorem slow_potter_nat (hmeas : Measurable L) (hnn : ∀ x, 0 < x → 0 ≤ L x)
    (hL : SlowlyVarying L) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 1 < C ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ x : ℝ, 1 ≤ x →
      1 / C * x ^ (-ε) ≤ L (n * x) / L n ∧ L (n * x) / L n ≤ C * x ^ ε := by
  exact BGWLeaves.StableAnalysis.SlowVariation.slow_potter_nat hmeas hnn hL hε

/-- Bingham's representation theorem, in the well-posed eventual form (the printed text has
`∫₁ˣ` for all `x ≥ 0`, which needs `ε/u` integrable near `0` and at finite points). -/
theorem slow_representation (hmeas : Measurable L) (hnn : ∀ x, 0 < x → 0 ≤ L x) :
    SlowlyVarying L ↔
      ∃ (c e : ℝ → ℝ) (cinf X : ℝ), 0 < cinf ∧ 1 ≤ X ∧ Measurable c ∧ Measurable e ∧
        Tendsto c atTop (𝓝 cinf) ∧ Tendsto e atTop (𝓝 0) ∧ (∀ x, X ≤ x → |e x| ≤ 1) ∧
        ∀ x, X ≤ x → L x = c x * Real.exp (∫ u in X..x, e u / u) := by
  exact BGWLeaves.StableAnalysis.SlowRepresentation.slow_representation hmeas hnn

end SlowVariation

/-! ## 4. Theorem 1.10 (`thm:locallimit`), with the corrected norming

Hypotheses of the paper: `W` has i.i.d. integer steps with law `ν`, `ν {z < -1} = 0`,
finite mean (automatic for `θ > 1`), `ν` in the domain of attraction of the index-`θ` law
(= `IsStableAttracted ν θ (mean ν) b` for some `b`), and `ν` non-lattice for (iii). -/

section LocalLimit

variable (ν : Measure ℤ) [IsProbabilityMeasure ν] {θ : ℝ}

/-- 1.10(i): `(W_n - n E W₁) / a_n → X₁`, with `a_n = norming ν θ n`. -/
theorem locallimit_i (hstep : ν {z | z < -1} = 0) (hint : Integrable (fun z : ℤ => (z : ℝ)) ν)
    (hDA : ∃ b, IsStableAttracted ν θ (mean ν) b) :
    IsStableAttracted ν θ (mean ν) (norming ν θ) := by
  exact BGWLeaves.StableAnalysis.Norming.locallimit_i ν hstep hint hDA

/-- 1.10(ii): `a_n` is nondecreasing and `a_n = n^{1/θ} L(n)` with `L` slowly varying. -/
theorem locallimit_ii (hstep : ν {z | z < -1} = 0) (hint : Integrable (fun z : ℤ => (z : ℝ)) ν)
    (hDA : ∃ b, IsStableAttracted ν θ (mean ν) b) :
    Monotone (norming ν θ) ∧
      SlowlyVarying (fun x : ℝ => norming ν θ ⌊x⌋₊ / x ^ (1 / θ)) := by
  exact BGWLeaves.StableAnalysis.Norming.locallimit_ii ν hstep hint hDA

/-- 1.10(iii), **abstract-norming form**: any monotone norming `a` for which the weak
limit holds gives the local limit theorem uniformly over all `k ∈ ℤ`. -/
theorem llt_abstract (hint : Integrable (fun z : ℤ => (z : ℝ)) ν) (hnl : ¬ IsLatticeLaw ν)
    {a : ℕ → ℝ} (hmono : Monotone a) (h : IsStableAttracted ν θ (mean ν) a) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ k : ℤ,
      |a n * intWalkProb ν n k - Scalar.stableDensity θ (((k : ℝ) - n * mean ν) / a n)| ≤ ε := by
  exact BGWLeaves.StableAnalysis.LocalLimit.llt_abstract ν hint hnl hmono h hε

/-- The identification of the norming with the printed tail/truncated-moment quantity is a
statement about any norming `b` in a domain of attraction: `a_n / b_n → 1`. -/
theorem norming_isEquivalent (hstep : ν {z | z < -1} = 0)
    (hint : Integrable (fun z : ℤ => (z : ℝ)) ν) {b : ℕ → ℝ}
    (hb : IsStableAttracted ν θ (mean ν) b) :
    Tendsto (fun n => norming ν θ n / b n) atTop (𝓝 1) := by
  exact BGWLeaves.StableAnalysis.Norming.norming_isEquivalent ν hstep hint hb

end LocalLimit

/-- **Lemma 1.11, second half**: `P[ζ ≥ n] ∼ θ p₁(0) / B_n`.  Needs a *sharp* Karamata
tail sum `∑_{q ≥ n} 1/(q a_q) ∼ θ / a_n` (BGW has only the bound `karamata_tail_tsum`). -/
theorem sizeTail_asymp {μ : PMF ℕ} {α : ℝ} {a : ℕ → ℝ} (h : StableDomain μ α a)
    (hap : Aperiodic μ) :
    Tendsto (fun n : ℕ => a n * (bienaymeLaw μ.toMeasure).real (sizeGeEvent n)) atTop
      (𝓝 (α * Scalar.stableDensity α 0)) := by
  exact BGWLeaves.StableAnalysis.SizeTail.sizeTail_asymp h hap

/-- `E[Y] = μ₀/(1-μ₀)` (line 903). -/
theorem mean_etaLaw {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1) :
    mean (etaLaw μ) = (μ 0).toReal / (1 - (μ 0).toReal) := by
  exact BGWLeaves.StableAnalysis.EtaLaw.mean_etaLaw hc hne

/-- Finite variance of `μ` gives finite variance of `Y` (line 903). -/
theorem integrable_sq_etaLaw {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (h : Integrable (fun z : ℤ => (z : ℝ) ^ 2) (stepLaw μ)) :
    Integrable (fun z : ℤ => (z : ℝ) ^ 2) (etaLaw μ) := by
  exact BGWLeaves.StableAnalysis.EtaLaw.integrable_sq_etaLaw hc hne h

/-- `σ'^2 = σ²/(1-μ₀) - μ₀/(1-μ₀)²`, the variance of `Y`. -/
theorem variance_etaLaw {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (h : Integrable (fun z : ℤ => (z : ℝ) ^ 2) (stepLaw μ)) :
    variance (etaLaw μ) =
      variance (stepLaw μ) / (1 - (μ 0).toReal) - (μ 0).toReal / (1 - (μ 0).toReal) ^ 2 := by
  exact BGWLeaves.StableAnalysis.EtaLaw.variance_etaLaw hc hne h

/-- **Finite-variance ratio** (the statement that replaces the printed `c^{1/θ}` in the
finite-variance branch of 5.13 / 6.11):
`B'_n / B_{⌊n/μ₀⌋} → √μ₀ σ'/σ`. -/
theorem finiteVariance_norming_ratio_eta {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (h : Integrable (fun z : ℤ => (z : ℝ) ^ 2) (stepLaw μ)) :
    Tendsto (fun n : ℕ => norming (etaLaw μ) 2 n / norming (stepLaw μ) 2 ⌊n / (μ 0).toReal⌋₊)
      atTop (𝓝 (Real.sqrt (μ 0).toReal * Real.sqrt (variance (etaLaw μ)) /
        Real.sqrt (variance (stepLaw μ)))) := by
  exact BGWLeaves.StableAnalysis.EtaLaw.finiteVariance_norming_ratio_eta hc hne h

/-! ## 7. Lemma 3.4 (`lem:hhp`), infinite variance -/

/-- **Lemma 3.4**: if `σ² = ∞`, `B'_n / B_n → (1-μ₀)^{-1/θ}`, for the corrected normings
(`norming` of the law of `Y` and of the law of `K - 1`). -/
theorem lem_hhp {μ : PMF ℕ} {θ : ℝ} (hc : IsCritical μ) (hne : μ 1 ≠ 1) (hap : Aperiodic μ)
    (hDA : ∃ b, StableDomain μ θ b)
    (hinf : ¬ Integrable (fun z : ℤ => (z : ℝ) ^ 2) (stepLaw μ)) :
    Tendsto (fun n : ℕ => norming (etaLaw μ) θ n / norming (stepLaw μ) θ n) atTop
      (𝓝 ((1 - (μ 0).toReal) ^ (-(1 / θ)))) := by
  exact BGWLeaves.StableAnalysis.LemHhp.lem_hhp hc hne hap hDA hinf

/-- Bridge: the Fourier-defined `d_2` of `BGW` is the Gaussian density. -/
theorem stableDensity_two (x : ℝ) : Scalar.stableDensity 2 x = gaussDensity x := by
  exact BGWLeaves.StableAnalysis.StrongLLT.stableDensity_two x

/-- **Theorem 3.5.**  `ρ` non-lattice with finite second moment, mean `m`, variance `σ̃²`,
`ã_n = σ̃ √(n/2)`.  The weight `1 ∨ (x - mn)²/n` is **inside** the supremum, and the
supremum is over **all** `x ∈ ℤ` (with `N` independent of `x`). -/
theorem strongLLT (ρ : Measure ℤ) [IsProbabilityMeasure ρ] (hnl : ¬ IsLatticeLaw ρ)
    (hL2 : Integrable (fun z : ℤ => (z : ℝ) ^ 2) ρ) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ x : ℤ,
      max 1 (((x : ℝ) - n * mean ρ) ^ 2 / n) *
        |Real.sqrt (variance ρ) * Real.sqrt (n / 2) * intWalkProb ρ n x -
          gaussDensity (((x : ℝ) - n * mean ρ) / (Real.sqrt (variance ρ) * Real.sqrt (n / 2)))|
        ≤ ε := by
  exact BGWLeaves.StableAnalysis.StrongLLT.strongLLT ρ hnl hL2 hε

/-- **Remark after Theorem 1.10** (needed in the proof of 6.11, `h'(n) → ∞`): for `σ² = ∞`,
`θ = 2`, `h(n) = a_n/√n` tends to `∞`, and `h` can be taken increasing: indeed
`a_n²/n = K(z_n)/2` is nondecreasing since `K` and `z_n` are. The paper's "`L` increasing" is
stated here for the integer sequence `h(n)`. -/
theorem locallimit_remark (ν : Measure ℤ) [IsProbabilityMeasure ν] (hstep : ν {z | z < -1} = 0)
    (hint : Integrable (fun z : ℤ => (z : ℝ)) ν) (hDA : ∃ b, IsStableAttracted ν 2 (mean ν) b)
    (hinf : ¬ Integrable (fun z : ℤ => (z : ℝ) ^ 2) ν) :
    Tendsto (fun n : ℕ => norming ν 2 n / Real.sqrt n) atTop atTop ∧
      Monotone (fun n : ℕ => norming ν 2 n / Real.sqrt n) := by
  exact BGWLeaves.StableAnalysis.QuantileAnalysis.locallimit_remark ν hstep hint hDA hinf

/-- **Bridge, tail branch**: `μ[j,∞) = j^{-θ}L(j)` gives a normalized domain of attraction.
Direct half of the Gnedenko-Kolmogorov / Feller XVII.5 theory plus the construction of the norming. -/
theorem exists_stableDomain_of_tail {μ : PMF ℕ} {θ : ℝ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hθ : 1 < θ ∧ θ ≤ 2) {L : ℝ → ℝ} (hmeas : Measurable L) (hnn : ∀ x, 0 < x → 0 ≤ L x)
    (hL : SlowlyVarying L)
    (htail : ∀ j : ℕ, 1 ≤ j → (μ.toMeasure (Set.Ici j)).toReal = (j : ℝ) ^ (-θ) * L j) :
    ∃ a : ℕ → ℝ, StableDomain μ θ a := by
  exact BGWLeaves.StableAnalysis.StableDomainTail.exists_stableDomain_of_tail hc hne hθ hmeas hnn hL htail

end BGWLeaves.StableAnalysis
