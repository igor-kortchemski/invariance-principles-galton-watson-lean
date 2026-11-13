module

public import BGWLeaves.Conditioning.Defs
public import BGWLeaves.LeafMass
public import BGWLeaves.LeafConcentration
public import BGWLeaves.Passage
public import BGWLeaves.ForestLaw
public import BGWLeaves.StableAnalysis

/-!
# Local estimates for forests and marked walks: definitions and bridges

Source: arXiv:1110.2163v4 (line numbers refer to its LaTeX source), Section 5 (conditioning on exactly
`n` leaves):
Lemma 5.4 (`lem:technical`, lines 1412-1470), Corollary 5.5 (`cor:tejhnique`, with `eq:amontrer`), Lemma
5.11 (`lem:technical2`), Lemma 5.12 (`lem:g`, with `eq:e`), Lemma 5.13 (`lem:techniqueutile`, with
`eq:psi` .. `eq:lemtechnique4`), and Section 6, Lemma 6.11 (`lem:technic3`).

This file contains the definitions for the local estimates and the bridges.  The shared definitions of
`BGWLeaves.Conditioning.Defs` (`forestLaw`, `forestLeafCountEvent`,
`forestLeafGeEvent`, `forestSizeGeEvent`, `forestSizeWindow`, `leafCutoff`, `psi`, `psiStar`, `chi`) are
used as they are: they are `ℝ≥0∞`-valued, and the real-valued forms used here are their
`.toReal` (`toReal_psi`, `toReal_psiStar`).  The main statements are in
`BGWLeaves.LocalEstimates`; their proofs are in the modules
`BGWLeaves.LocalEstimates.*` (imported through `BGWLeaves.LocalEstimates.Proof`), which use
`BGWLeaves.Conditioning` (Lemma 4.3 with `U ≡ 1`, `M = 1`) and `BGWLeaves.Vervaat`
(Lemma 6.2(i), `lem_CVf2_i`).

Conventions.
* `B_n = norming (stepLaw μ) θ n` (the CORRECTED norming, corrections 1 and 2 of `FORMALIZATION_REPORT.md`),
  `B'_n = norming (etaLaw μ) θ n`,
  `B_u = B_{⌊u⌋}` for real `u ≥ 1` as printed (`normB`, `normBp`), `p₁ = Scalar.stableDensity θ`.
* `(H_θ)` is spelled out as `IsCritical μ`, `μ 1 ≠ 1`, `Aperiodic μ`, `∃ b, StableDomain μ θ b`.  Section 5
  also assumes (line 1269) that `supp μ ∖ {0}` is non-lattice: `¬ IsLatticeLaw (etaLaw μ)` (named `hnl`;
  `nonLattice_etaLaw_iff` links it with the printed phrase).
* Uniform convergence `sup_{1 ≤ j ≤ αB_n} |f_n(j)| → 0` is written `ε`-`N`.
* All probabilities are real masses of events (`Measure.real`); conditioning on a null event is never used.
-/

@[expose] public section

namespace BGWLeaves

open MeasureTheory ProbabilityTheory Filter Asymptotics BGW
open BGW.StableTrees BGW.LocallyFinite BGWLeaves.StableAnalysis
open scoped ENNReal Topology

/-! ## 0. Definitions -/

/--  `{λ(f) = m, a ≤ ζ(f) ≤ b}`: a finite forest of `j` trees with `m` leaves and `p ∈ [a, b]`
vertices (`eq:psi`). -/
def forestLeafWindowEvent (j m : ℕ) (a b : ℝ) : Set (Fin j → LocallyFinite.Tree) :=
  {F | ∃ p : ℕ, F ∈ forestEvent j p m ∧ a ≤ (p : ℝ) ∧ (p : ℝ) ≤ b}

/--  `P_{μ,j}[ζ(f) ≥ n]` (the left side of Lemma 5.11). -/
noncomputable def sizeTailProb (μ : PMF ℕ) (n j : ℕ) : ℝ := (forestLaw μ j).real (forestSizeGeEvent j n)

/--  `B_u = B_{⌊u⌋}` (line 1363: "we put `B_u = B_{⌊u⌋}` for `u ≥ 1`"), with the corrected `B_n`. -/
noncomputable def normB (μ : PMF ℕ) (θ u : ℝ) : ℝ := norming (stepLaw μ) θ ⌊u⌋₊

/--  `B'_u = B'_{⌊u⌋}`, `B'_n = norming (etaLaw μ) θ n` the norming of the walk `W'` (sum of copies of `Y`). -/
noncomputable def normBp (μ : PMF ℕ) (θ u : ℝ) : ℝ := norming (etaLaw μ) θ ⌊u⌋₊

/--  `p_s(x) = s^{-1/θ} p₁(x s^{-1/θ})`: the density of `X_s`, defined through the scaling
property `eq:scaling` (`p_{λ s}(x) = λ^{-1/θ} p_s(x λ^{-1/θ})` at `s = 1`).  No process is constructed. -/
noncomputable def pDens (θ s x : ℝ) : ℝ := s ^ (-(1 / θ)) * Scalar.stableDensity θ (x * s ^ (-(1 / θ)))

/--  `q_s(x) = (x/s) p_s(-x)` (Proposition 5.3, line 1397). -/
noncomputable def qKernel (θ s x : ℝ) : ℝ := x / s * pDens θ s (-x)

/--  `∫_a^∞ q_s(x) ds` (`a = 1` in Lemmas 5.4, 5.11; `a = 1 - a'` in Corollary 5.5). -/
noncomputable def sizeTailKernel (θ a x : ℝ) : ℝ := ∫ s in Set.Ioi a, qKernel θ s x

/--  `P[S_p = n]` for `S_p` a sum of `p` independent Bernoulli(`m`) variables (`m = μ₀`): the
binomial point mass `C(p,n) m^n (1-m)^{p-n}` (the form used by `prop_K`).  It is `0` for `n > p`. -/
noncomputable def binomProb (m : ℝ) (p n : ℕ) : ℝ := (p.choose n : ℝ) * m ^ n * (1 - m) ^ (p - n)

/--  `c = μ₀/(1-μ₀) = E[Y]`. -/
noncomputable def cC (μ : PMF ℕ) : ℝ := (μ 0).toReal / (1 - (μ 0).toReal)

/--  `r_n(u) = ⌊n/μ₀ + u√n⌋` (line 1832; `Nat.floor`, so a negative argument gives `0`; irrelevant for
`|u| ≤ ε√n`, `ε < 1/μ₀`). -/
noncomputable def rN (μ : PMF ℕ) (n : ℕ) (u : ℝ) : ℕ := ⌊(n : ℝ) / (μ 0).toReal + u * Real.sqrt n⌋₊

/--  `a_n(u) = √n P[S_{r_n(u)} = n]` (line 1833). -/
noncomputable def aN (μ : PMF ℕ) (n : ℕ) (u : ℝ) : ℝ :=
  Real.sqrt n * binomProb (μ 0).toReal (rN μ n u) n

/--  `b_n(u, j) = B'_n P[W'_{r_n(u)-n} = n - j]` (line 1833), **with `j ∈ ℤ`** (the printed range is
`1 ≤ j ≤ n`; the signed range is needed for Lemma 6.11).  `P[W'_q = k] = intWalkProb (etaLaw μ) q k`; for
`n ≤ r_n(u)` the index `r_n(u) - n` is the printed one; `Nat` subtraction is `0` below, where `a_n(u) = 0`. -/
noncomputable def bN (μ : PMF ℕ) (θ : ℝ) (n : ℕ) (u : ℝ) (j : ℤ) : ℝ :=
  norming (etaLaw μ) θ n * intWalkProb (etaLaw μ) (rN μ n u - n) ((n : ℤ) - j)

open Classical in
/--  The `u`-dependent shift of `G₀` (printed `\frac{\sqrt2 c^{3/2} u}{\sigma'} 1_{\{\sigma^2<\infty\}}`),
`σ' = √(variance (etaLaw μ))`, `0` if `σ² = ∞` (`σ²` finite iff `stepLaw μ` is square integrable). -/
noncomputable def finVarShift (μ : PMF ℕ) (u : ℝ) : ℝ :=
  if Integrable (fun z : ℤ => (z : ℝ) ^ 2) (stepLaw μ) then
    Real.sqrt 2 * cC μ ^ (3 / 2 : ℝ) * u / Real.sqrt (variance (etaLaw μ))
  else 0

/--  `G₀(u,x) = c^{1/θ} p₁(-c^{1/θ} x - (√2 c^{3/2} u/σ') 1_{σ²<∞})` (line 1850). -/
noncomputable def G0 (μ : PMF ℕ) (θ u x : ℝ) : ℝ :=
  cC μ ^ (1 / θ) * Scalar.stableDensity θ (-(cC μ ^ (1 / θ) * x) - finVarShift μ u)

/--  `q_n(u) = r_n(u) - n` (line 1865). -/
noncomputable def qN (μ : PMF ℕ) (n : ℕ) (u : ℝ) : ℕ := rN μ n u - n

/--  `Q_n(u,j) = c^{1/θ} p₁((n - j - c q_n(u)) / B'_{q_n(u)})` (line 1866), `j ∈ ℤ`. -/
noncomputable def Qn (μ : PMF ℕ) (θ : ℝ) (n : ℕ) (u : ℝ) (j : ℤ) : ℝ :=
  cC μ ^ (1 / θ) * Scalar.stableDensity θ
    (((n : ℝ) - j - cC μ * qN μ n u) / norming (etaLaw μ) θ (qN μ n u))

/--  `K_n(u,j) = |(n - j - c q_n(u))/B'_{q_n(u)} + c^{1/θ} j/B'_n + (√2 c^{3/2}u/σ') 1_{σ²<∞}|`
(line 1870). -/
noncomputable def Kn (μ : PMF ℕ) (θ : ℝ) (n : ℕ) (u : ℝ) (j : ℤ) : ℝ :=
  |((n : ℝ) - j - cC μ * qN μ n u) / norming (etaLaw μ) θ (qN μ n u) +
      cC μ ^ (1 / θ) * ((j : ℝ) / norming (etaLaw μ) θ n) + finVarShift μ u|

/--  `sup_{j ∈ S} f j` for `f ≥ 0` and `S` finite, as the real `iSup` (it is `0` for `S = ∅`, and the
family is bounded: it vanishes off `S` and `S` is finite).  Used only in `eq:lemtechnique2`, where the
supremum must stay inside the integral. -/
noncomputable def supJ (S : Finset ℕ) (f : ℕ → ℝ) : ℝ := ⨆ j ∈ S, f j

/--  `r_n`, "the greatest positive integer such that `⌈μ₀ r_n - r_n^{3/4}⌉ = n`" (line 1783; the
threshold inversion of Lemma 5.4(i)); `0` (junk) if there is none or no greatest one, which does not
happen for large `n` (`thresholdInv_spec`). -/
noncomputable def thresholdInv (m : ℝ) (n : ℕ) : ℕ :=
  sSup {r : ℕ | 1 ≤ r ∧ ⌈m * r - (r : ℝ) ^ (3 / 4 : ℝ)⌉ = (n : ℤ)}

/-! ## 1. Proved elementary bridges -/

theorem normB_natCast (μ : PMF ℕ) (θ : ℝ) (n : ℕ) : normB μ θ (n : ℝ) = norming (stepLaw μ) θ n := by
  simp [normB]

theorem normBp_natCast (μ : PMF ℕ) (θ : ℝ) (n : ℕ) : normBp μ θ (n : ℝ) = norming (etaLaw μ) θ n := by
  simp [normBp]

/-- `q_1(x) = x p₁(-x)` (line 1700: "Recall that `q_1(x) = x p_1(-x)`"). -/
theorem qKernel_one (θ x : ℝ) : qKernel θ 1 x = x * Scalar.stableDensity θ (-x) := by
  simp [qKernel, pDens]

/-- `a ↦ ∫_a^∞ q_s(x) ds` and the printed formula for `x ≥ 0` (proved below as `sizeTailKernel_eq_integral`). -/
theorem sizeTailKernel_def (θ a x : ℝ) : sizeTailKernel θ a x = ∫ s in Set.Ioi a, qKernel θ s x := rfl

end BGWLeaves
