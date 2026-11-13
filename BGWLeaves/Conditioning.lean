module

public import BGWLeaves.Conditioning.Defs
import BGWLeaves.Conditioning.Proof

/-!
# Conditioning on the number of leaves

Source: arXiv:1110.2163v4 (line numbers refer to its LaTeX source): Lemma 4.3 (`lemma:passage`, line 1149),
Proposition 4.4 (`prop:passage`, line 1200), Proposition 5.2 (`prop:abscon`, line 1384), Lemma 5.6
(`lem:CVf`, line 1473) and Lemma 6.10 (`lem:absolueC2`, line 2185), together with the claim of the proof
of 4.4(ii) (lines 1219-1220: `leafTail_asymp`, a non-numbered helper).

The proofs are in the modules `BGWLeaves.Conditioning.*` (imported through `BGWLeaves.Conditioning.Proof`).
Definitions and bridges are in `BGWLeaves.Conditioning.Defs`.  Declarations `isBoundedTest_finiteTreeLiftR`,
`lemma_passage_isOeUniform` and `lem_absolueC2` are proved here from other statements of this file.

Layout.
* Basics (module `Basics`): `measurable_finiteTreeLift(R)`, `psi_one`, `psiStar_one`,
  `forestLaw_infinite_null`, `sizeGeEvent_ne_zero`, `leafGeEvent_ne_zero`, `leafCutoff_surjective`.
* Lemma 4.3 (module `PassageProof`): `passage_est_lambda_small`, `passage_est_size_dev`, `lemma_passage`,
  `lemma_passage_isOeUniform`, `lemma_passage_tree`.  The common bound `M` of the family `U_j` in
  `lemma_passage_isOeUniform` is part of the statement ("uniform in `j`").
* Proposition 4.4 (modules `PassageProof`, `LeafTail`): `integral_cond_sizeGe`, `sizeGe_poly_lower`,
  `sizeWindow_small`, `leafTail_asymp`, `norming_leafCutoff_ratio`, `leafGe_sizeGe_ratio`, `prop_passage_i`,
  `prop_passage_ii`.
* Proposition 5.2 (module `AbsCont`): `treeLeafTime_ne_top_iff`, `abscon_pending_nonneg`,
  `tree_markov_leafCount`, `tree_markov_leafGe`, the unconditioned core `abscon_core` and the printed
  conditional form `prop_abscon`.
* Lemma 5.6 (module `Clock`): `clock_unconditioned_oe`, `clock_leafConditioned_oe`, `lem_CVf_i`,
  `lem_CVf_ii`.
* Lemma 6.10 (module `StrongMarkov`): `walkLeafTime_ne_top_ae`, `walkLeafTime_add`,
  `strongMarkov_leafTime`, the unconditioned core `absolueC2_core`, `lem_absolueC2_k` and the printed form
  `lem_absolueC2`.
-/

@[expose] public section

namespace BGWLeaves

open MeasureTheory ProbabilityTheory Filter Asymptotics BGW
open BGW.StableTrees BGW.LocallyFinite BGWLeaves.StableAnalysis
open scoped ENNReal Topology

/-! ## 0. Measurability of lifted functionals, bridges to the one-tree objects -/

/-- `finiteTreeLiftR g` is a measurable test (and a bounded nonnegative one with bound `M` if
`0 ≤ g ≤ M`: `isBoundedTest_finiteTreeLiftR`).  Proof: as `measurable_finiteTreeLift`. -/
theorem measurable_finiteTreeLiftR (g : PlaneTree → ℝ) : Measurable (finiteTreeLiftR g) := by
  exact BGWLeaves.Conditioning.Basics.measurable_finiteTreeLiftR g

theorem isBoundedTest_finiteTreeLiftR {M : ℝ} {g : PlaneTree → ℝ} (hg : ∀ t, 0 ≤ g t ∧ g t ≤ M)
    (hM : 0 ≤ M) : IsBoundedTest M (finiteTreeLiftR g) := by
  refine ⟨measurable_finiteTreeLiftR g, fun T => ?_⟩
  by_cases h : ∃ t : PlaneTree, t.toLocallyFinite = T
  · simp only [finiteTreeLiftR, h, ↓reduceDIte]
    exact hg _
  · simp only [finiteTreeLiftR, h, ↓reduceDIte]
    exact ⟨le_rfl, hM⟩

/-- Every lifted functional of finite plane trees is a measurable test function (the finite trees are a
countable union of points of the Polish space `LocallyFinite.Tree`). -/
theorem measurable_finiteTreeLift (g : PlaneTree → ℝ≥0∞) : Measurable (finiteTreeLift g) := by
  exact BGWLeaves.Conditioning.Basics.measurable_finiteTreeLift g

/-- Bridge to the one-tree objects (`j = 1`): `ψ_p(1) = P_μ[λ = p]` (`leafProb`).  Proof:
`MeasurableEquiv.funUnique` and `forestEvent 1 p m = {F | F 0 ∈ finite tree with p vertices, m leaves}`. -/
theorem psi_one (μ : PMF ℕ) (p : ℕ) :
    psi μ p 1 = bienaymeLaw μ.toMeasure (leafCountEvent p) := by
  exact BGWLeaves.Conditioning.Basics.psi_one μ p

/-- `ψ*_p(1) = P_μ[λ ≥ p]`. -/
theorem psiStar_one (μ : PMF ℕ) (p : ℕ) :
    psiStar μ p 1 = bienaymeLaw μ.toMeasure (leafGeEvent p) := by
  exact BGWLeaves.Conditioning.Basics.psiStar_one μ p

/-- The infinite forests are null for critical `μ` with `μ 1 ≠ 1` (from
`BGW.LocallyFinite.ae_finiteVertices_bienaymeLaw`). -/
theorem forestLaw_infinite_null {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1) (j : ℕ) :
    forestLaw μ j {F | ∃ i, ¬ FiniteVertices (F i)} = 0 := by
  exact BGWLeaves.Conditioning.Basics.forestLaw_infinite_null hc hne j

/-! ## 1. Lemma 4.3 (`lemma:passage`, line 1149) -/

/-- The deviation estimate on the other side: for a forest of total size `p ≥ n`, `λ < μ₀ p - p^{3/4}` has
joint probability `oe_{1/2}(n)`, uniformly in `1 ≤ j ≤ n`.  It is the sum over `p ≥ n` of Lemma 2.7(i) at
`δ = 1` (`lem_GdesDev2_i`, `IsOe.tail`; `{λ < μ₀ p - p^{3/4}} ⊂ {|λ/p - μ₀| > p^{-1/4}}`).  Step 1 of the
printed proof ("`(eq:lempassage)`", line 1161). -/
theorem passage_est_lambda_small {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ n j : ℕ, 1 ≤ j → j ≤ n →
      (forestLaw μ j).real {F | ∃ p m : ℕ, F ∈ forestEvent j p m ∧ n ≤ p ∧
        (m : ℝ) < (μ 0).toReal * p - (p : ℝ) ^ (3 / 4 : ℝ)} ≤ C * Real.exp (-c * (n : ℝ) ^ (1 / 2 : ℝ)) := by
  exact BGWLeaves.Conditioning.PassageProof.passage_est_lambda_small hc hne

/-- The deviation estimate in the other variable: for forests with `λ = m ≥ μ₀ n - n^{3/4}` and
`ζ = p < n`, `|p - m/μ₀| > p^{3/4}` has probability `oe_{1/2}(n)` uniformly in `1 ≤ j ≤ n`.  It is the sum
over `m ≥ μ₀ n - n^{3/4}` of Lemma 2.7(ii) (`lem_GdesDev2_ii`; for `j > m` the forest has probability `0`,
each tree having a leaf).  The first display of the printed bound for `D_n` (line 1169). -/
theorem passage_est_size_dev {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ n j : ℕ, 1 ≤ j → j ≤ n →
      (forestLaw μ j).real {F | ∃ p m : ℕ, F ∈ forestEvent j p m ∧ p < n ∧
        (μ 0).toReal * n - (n : ℝ) ^ (3 / 4 : ℝ) ≤ m ∧
        (p : ℝ) ^ (3 / 4 : ℝ) < |(p : ℝ) - m / (μ 0).toReal|} ≤
          C * Real.exp (-c * (n : ℝ) ^ (1 / 2 : ℝ)) := by
  exact BGWLeaves.Conditioning.PassageProof.passage_est_size_dev hc hne

/-- **Lemma 4.3 (`lemma:passage`)**, uniform in the test.  Fix `1 ≤ j ≤ n` and a bounded nonnegative
measurable `U` on `𝕋^j` (bound `M`, the paper's `‖U‖`).  Then
`|E_{μ,j}[U 1_{ζ ≥ n}] - E_{μ,j}[U 1_{λ ≥ μ₀ n - n^{3/4}}]| ≤ M (P_{μ,j}[n - (μ₀⁻¹+1) n^{3/4} ≤ ζ ≤ n] + oe_{1/2}(n))`
with ONE pair `(C, c)` for all `n`, all `1 ≤ j ≤ n` and all tests `U` (stronger than the printed statement,
where `oe` may depend on `U`; this is what the printed proof gives, every error term being `‖U‖` times an
`oe_{1/2}(n)` of Lemma 2.7).  The cutoff is `⌈μ₀ n - n^{3/4}⌉` (`mem_forestLeafGeEvent_real_iff`: the real
threshold of the paper).  Hypotheses: criticality and `μ 1 ≠ 1` only (the printed `(H_θ)` is not used: Lemma 2.7
needs `0 < μ₀ < 1`, criticality makes infinite forests null).  Proof: from `passage_est_*`. -/
theorem lemma_passage {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ n j : ℕ, 1 ≤ j → j ≤ n →
      ∀ (M : ℝ) (U : (Fin j → LocallyFinite.Tree) → ℝ), IsBoundedTest M U →
        |(∫ F in forestSizeGeEvent j n, U F ∂forestLaw μ j) -
            ∫ F in forestLeafGeEvent j (leafCutoff μ n), U F ∂forestLaw μ j| ≤
          M * ((forestLaw μ j).real (forestSizeWindow (μ 0).toReal j n) +
            C * Real.exp (-c * (n : ℝ) ^ (1 / 2 : ℝ))) := by
  exact BGWLeaves.Conditioning.PassageProof.lemma_passage hc hne

/-- Lemma 4.3 in the printed form "`oe_{1/2}(n)` uniform in `j`", for a family of tests `U_j` on `𝕋^j`
bounded by the common `M > 0` (the bound `M` is the same for all `j`: it is part of the statement, this is the only meaning of "uniform in `j`"): the excess of the left side over `M P[window]` is `oe_{1/2}(n)` in the sense of
`IsOeUniform` (`x j n` for `1 ≤ j ≤ n`).  Proved from `lemma_passage`. -/
theorem lemma_passage_isOeUniform {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1) {M : ℝ}
    (hM : 0 < M) (U : ∀ j : ℕ, (Fin j → LocallyFinite.Tree) → ℝ) (hU : ∀ j, IsBoundedTest M (U j)) :
    IsOeUniform (1 / 2) fun j n : ℕ =>
      |(∫ F in forestSizeGeEvent j n, U j F ∂forestLaw μ j) -
          ∫ F in forestLeafGeEvent j (leafCutoff μ n), U j F ∂forestLaw μ j| -
        M * (forestLaw μ j).real (forestSizeWindow (μ 0).toReal j n) := by
  obtain ⟨C, c, hC, hc0, h⟩ := lemma_passage hc hne
  refine ⟨M * C, c, mul_pos hM hC, hc0, fun n j hj hjn => ?_⟩
  have := h n j hj hjn M (U j) (hU j)
  have h2 : M * (C * Real.exp (-c * (n : ℝ) ^ (1 / 2 : ℝ))) =
      M * C * Real.exp (-c * (n : ℝ) ^ (1 / 2 : ℝ)) := by ring
  linarith

/-- Lemma 4.3 for one tree (`j = 1`), on the tree space `LocallyFinite.Tree` itself: tests `U : Tree → ℝ`.
This is the form used by Proposition 4.4.  Proof: from `lemma_passage` (`j = 1`) and the bridges
`psi_one`-type: `Measure.pi` over `Fin 1` is the image of `bienaymeLaw` under `MeasurableEquiv.funUnique`,
and `forestSizeGeEvent 1 n`, `forestLeafGeEvent 1 m`, `forestSizeWindow μ₀ 1 n` correspond to `sizeGeEvent n`,
`leafGeEvent m`, `sizeWindow μ₀ n`. -/
theorem lemma_passage_tree {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ n : ℕ, 1 ≤ n →
      ∀ (M : ℝ) (U : LocallyFinite.Tree → ℝ), IsBoundedTest M U →
        |(∫ τ in sizeGeEvent n, U τ ∂bienaymeLaw μ.toMeasure) -
            ∫ τ in leafGeEvent (leafCutoff μ n), U τ ∂bienaymeLaw μ.toMeasure| ≤
          M * ((bienaymeLaw μ.toMeasure).real (sizeWindow (μ 0).toReal n) +
            C * Real.exp (-c * (n : ℝ) ^ (1 / 2 : ℝ))) := by
  exact BGWLeaves.Conditioning.PassageProof.lemma_passage_tree hc hne

/-! ## 2. Proposition 4.4 (`prop:passage`, line 1200) -/

/-- `P_μ[ζ ≥ n] > 0` for every `n` (critical, `μ 1 ≠ 1`: there is a tree with at least `n` vertices).
Proof: a spine of `μ`-positive degrees (or `sizeProb_pos_iff` under `(H_θ)`). -/
theorem sizeGeEvent_ne_zero {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1) (n : ℕ) :
    bienaymeLaw μ.toMeasure (sizeGeEvent n) ≠ 0 := by
  exact BGWLeaves.Conditioning.Basics.sizeGeEvent_ne_zero hc hne n

/-- `P_μ[λ ≥ n] > 0` for every `n` (critical, `μ 1 ≠ 1`: there are finite trees with arbitrarily many
leaves; a spine of an offspring `k ≥ 2` with `μ 0`).  The positivity of the denominator `ψ*_n(1)` of
`prop_abscon`. -/
theorem leafGeEvent_ne_zero {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1) (n : ℕ) :
    bienaymeLaw μ.toMeasure (leafGeEvent n) ≠ 0 := by
  exact BGWLeaves.Conditioning.Basics.leafGeEvent_ne_zero hc hne n

/-- The averaging formula of the first line of the proof of 4.4(i):
`E_μ[U | ζ ≥ n] = P_μ[ζ ≥ n]⁻¹ ∑_{k ≥ n} P_μ[ζ = k] E_μ[U | ζ = k]` (`E[U | ζ = k] := 0` if `P[ζ = k] = 0`;
infinite trees are null).  Proof: `ae_finiteVertices_bienaymeLaw`, `tsum`/`measure_iUnion`, `cond`. -/
theorem integral_cond_sizeGe {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1) {M : ℝ}
    {U : LocallyFinite.Tree → ℝ} (hU : IsBoundedTest M U) (n : ℕ) :
    ∫ τ, U τ ∂((bienaymeLaw μ.toMeasure)[|sizeGeEvent n]) =
      ((bienaymeLaw μ.toMeasure).real (sizeGeEvent n))⁻¹ *
        ∑' k : ℕ, (bienaymeLaw μ.toMeasure).real (sizeEvent (n + k)) *
          ∫ τ, U τ ∂((bienaymeLaw μ.toMeasure)[|sizeEvent (n + k)]) := by
  exact BGWLeaves.Conditioning.PassageProof.integral_cond_sizeGe hc hne hU n

/-- Polynomial lower bound for the size tail, the constant `c₃` of the proof of 4.4(ii) (line 1218): for
`η > 0`, `P_μ[ζ ≥ n] ≥ c₃ n^{-1/θ-η}` for large `n`.  Proof: from `lem_locallimit` (`B_n P[ζ ≥ n] → θ p₁(0) > 0`)
and Proposition 1.7(i) (`B_n ≤ n^{1/θ+η}` eventually, `slow_rpow_neg_mul_tendsto_zero`, `locallimit_ii`). -/
theorem sizeGe_poly_lower {μ : PMF ℕ} {θ : ℝ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hap : Aperiodic μ) (hDA : ∃ a, StableDomain μ θ a) {η : ℝ} (hη : 0 < η) :
    ∃ c₃ : ℝ, 0 < c₃ ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      c₃ * (n : ℝ) ^ (-(1 / θ) - η) ≤ (bienaymeLaw μ.toMeasure).real (sizeGeEvent n) := by
  exact BGWLeaves.Conditioning.LeafTail.sizeGe_poly_lower hc hne hap hDA hη

/-- The first term of the printed bound of 4.4(ii) tends to `0` ("by Lemma 1.11", line 1219): for
`0 < η < 1/4`, `n^{1/θ+η} P_μ[n - (μ₀⁻¹+1) n^{3/4} ≤ ζ ≤ n] → 0`.  Proof: the window has `O(n^{3/4})` sizes
`p`, each with `P[ζ = p] ≤ C/(p B_p) ≤ C' n^{-1-1/θ+ε}` (`lem_locallimit`, Potter lower bound for `B_p`,
`slow_potter_nat`), so the product is `O(n^{η + ε - 1/4}) → 0` as `η < 1/4` (here is where `η < 1/4` is used). -/
theorem sizeWindow_small {μ : PMF ℕ} {θ : ℝ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hap : Aperiodic μ) (hDA : ∃ a, StableDomain μ θ a) {η : ℝ} (hη0 : 0 < η) (hη1 : η < 1 / 4) :
    Tendsto (fun n : ℕ => (n : ℝ) ^ (1 / θ + η) *
      (bienaymeLaw μ.toMeasure).real (sizeWindow (μ 0).toReal n)) atTop (𝓝 0) := by
  exact BGWLeaves.Conditioning.LeafTail.sizeWindow_small hc hne hap hDA hη0 hη1

/-- **Tail of the leaf count** (line 1219-1220, "from Theorem 3.1(ii) it is easy to get"):
`B_m P_μ[λ ≥ m] → θ μ₀^{1/θ} p₁(0)`, i.e. `P_μ[λ ≥ m] ∼ θ μ₀^{1/θ} p₁(0) / (m^{1/θ} h(m))` with the corrected
`B_m = norming (stepLaw μ) θ m`.  Proof: sum `ltn_ii_tendsto` (`m B_m P[λ = m+1] → μ₀^{1/θ} p₁(0) g` along
`g ∣ m`, `g = arithFactor μ {0}`, zero off the lattice, `leafProb_eq_zero_of_not_dvd`) over `m' ≥ m`; the
lattice factor `g` cancels against the density `1/g` of the lattice; needs the sharp Karamata tail sum
`∑_{q ≥ m} 1/(q B_q) ∼ θ/B_m` (as in `sizeTail_asymp`).  NOT a numbered result of the paper; a claim inside
the proof of 4.4(ii) that is stated once here (no cited input). -/
theorem leafTail_asymp {μ : PMF ℕ} {θ : ℝ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hap : Aperiodic μ) (hDA : ∃ a, StableDomain μ θ a) :
    Tendsto (fun m : ℕ => norming (stepLaw μ) θ m *
      (bienaymeLaw μ.toMeasure).real (leafGeEvent m)) atTop
      (𝓝 (θ * (μ 0).toReal ^ (1 / θ) * Scalar.stableDensity θ 0)) := by
  exact BGWLeaves.Conditioning.LeafTail.leafTail_asymp hc hne hap hDA

/-- Regular variation of `B` at the leaf cutoff: `B_{⌈μ₀ n - n^{3/4}⌉} / B_n → μ₀^{1/θ}`.  Proof: from
`locallimit_ii` (`B` monotone, `B_n = n^{1/θ} h(n)` with `h` slowly varying): sandwich `B_{(μ₀ - ε) n} ≤ B_{cutoff} ≤ B_{μ₀ n}`. -/
theorem norming_leafCutoff_ratio {μ : PMF ℕ} {θ : ℝ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hDA : ∃ a, StableDomain μ θ a) :
    Tendsto (fun n : ℕ => norming (stepLaw μ) θ (leafCutoff μ n) / norming (stepLaw μ) θ n)
      atTop (𝓝 ((μ 0).toReal ^ (1 / θ))) := by
  exact BGWLeaves.Conditioning.LeafTail.norming_leafCutoff_ratio hc hne hDA

/-- The ratio `P_μ[λ ≥ ⌈μ₀ n - n^{3/4}⌉] / P_μ[ζ ≥ n] → 1` ("by combining ... with Lemma 1.11", line 1220).
Proof: assembly of `leafTail_asymp`, `norming_leafCutoff_ratio` and `lem_locallimit` (second half). -/
theorem leafGe_sizeGe_ratio {μ : PMF ℕ} {θ : ℝ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hap : Aperiodic μ) (hDA : ∃ a, StableDomain μ θ a) :
    Tendsto (fun n : ℕ => (bienaymeLaw μ.toMeasure).real (leafGeEvent (leafCutoff μ n)) /
      (bienaymeLaw μ.toMeasure).real (sizeGeEvent n)) atTop (𝓝 1) := by
  exact BGWLeaves.Conditioning.LeafTail.leafGe_sizeGe_ratio hc hne hap hDA

/-- **Proposition 4.4(i)** (`prop:passage`).  Let `U` be a bounded nonnegative measurable function on the tree
space.  If `E_μ[U | ζ = n]` converges as `n → ∞`, then `E_μ[U | ζ ≥ n]` converges to the same limit
(`E[U | ζ = n] := 0` when `P[ζ = n] = 0`: only finitely many `n` under `(H_θ)`, `sizeEvent_ne_zero_eventually`).
Hypotheses: `(H_θ)` as in the paper's section.  Proof: Cesàro-type average, `integral_cond_sizeGe`,
`sizeGeEvent_ne_zero`, `sizeEvent_ne_zero_eventually`. -/
theorem prop_passage_i {μ : PMF ℕ} {θ : ℝ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hap : Aperiodic μ) (hDA : ∃ a, StableDomain μ θ a) {M : ℝ} {U : LocallyFinite.Tree → ℝ}
    (hU : IsBoundedTest M U) {L : ℝ}
    (h : Tendsto (fun n : ℕ => ∫ τ, U τ ∂((bienaymeLaw μ.toMeasure)[|sizeEvent n])) atTop (𝓝 L)) :
    Tendsto (fun n : ℕ => ∫ τ, U τ ∂((bienaymeLaw μ.toMeasure)[|sizeGeEvent n])) atTop (𝓝 L) := by
  exact BGWLeaves.Conditioning.PassageProof.prop_passage_i hc hne hap hDA hU h

/-- **Proposition 4.4(ii)** (`prop:passage`).  Let `(U_n)` be uniformly bounded (one `M`) nonnegative measurable
functions on the tree space.  If `E_μ[U_n | ζ ≥ n]` converges, then `E_μ[U_n | λ ≥ ⌈μ₀ n - n^{3/4}⌉]` converges
to the same limit.  The cutoff is the CEILING `leafCutoff μ n = ⌈μ₀ n - n^{3/4}⌉₊` (equivalent to the real
threshold `λ ≥ μ₀ n - n^{3/4}` of Lemma 4.3 by `mem_leafGeEvent_real_iff`), so that it takes all positive
integer values as `n` varies (`leafCutoff_surjective`).  Hypotheses: `(H_θ)` as in the paper's section.
Proof: assembly of `lemma_passage_tree`, `sizeGe_poly_lower` (with `η ∈ (0, 1/4)`, say `η = 1/8`),
`sizeWindow_small`, `leafGe_sizeGe_ratio`: the printed three-term bound. -/
theorem prop_passage_ii {μ : PMF ℕ} {θ : ℝ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hap : Aperiodic μ) (hDA : ∃ a, StableDomain μ θ a) {M : ℝ} {U : ℕ → LocallyFinite.Tree → ℝ}
    (hU : ∀ n, IsBoundedTest M (U n)) {L : ℝ}
    (h : Tendsto (fun n : ℕ => ∫ τ, U n τ ∂((bienaymeLaw μ.toMeasure)[|sizeGeEvent n])) atTop (𝓝 L)) :
    Tendsto (fun n : ℕ => ∫ τ, U n τ
      ∂((bienaymeLaw μ.toMeasure)[|leafGeEvent (leafCutoff μ n)])) atTop (𝓝 L) := by
  exact BGWLeaves.Conditioning.LeafTail.prop_passage_ii hc hne hap hDA hU h

/-- (Not a numbered result; used in the proof of Theorem 4.5: "`⌈μ₀ n - n^{3/4}⌉` takes all
positive integer values when `n` varies".)  For `0 < μ₀ < 1` the map `n ↦ ⌈μ₀ n - n^{3/4}⌉₊` hits every `m ≥ 1`
(the real function `x ↦ μ₀ x - x^{3/4}` is negative at `1` and grows by less than `μ₀ < 1` per step). -/
theorem leafCutoff_surjective {μ : PMF ℕ} (h0 : 0 < (μ 0).toReal) (h1 : (μ 0).toReal < 1) :
    ∀ m : ℕ, 1 ≤ m → ∃ n : ℕ, leafCutoff μ n = m := by
  exact BGWLeaves.Conditioning.Basics.leafCutoff_surjective h0 h1

/-! ## 5.2 Proposition `prop:abscon` -/

/-- `T_k(τ) < ∞` iff `k ≤ λ(τ)`; then `T_k(τ) < ζ(τ)`.  Proof: `List.count` of a prefix. -/
theorem treeLeafTime_ne_top_iff (t : PlaneTree) (k : ℕ) :
    treeLeafTime t k ≠ ⊤ ↔ k ≤ t.degreeCount 0 := by
  exact BGWLeaves.Conditioning.AbsCont.treeLeafTime_ne_top_iff t k

/-- For `1 ≤ k ≤ λ(τ)` the Łukasiewicz path at the `k`-th leaf is `≥ 0`, and it is `0` iff the tree ends
at that leaf (`ζ(τ) = T_k + 1`, i.e. `λ(τ) = k`); so on `{λ(τ) > k}` there is at least one pending tree.
Proof: `lukasiewicz` is `≥ 0` before the end, and `= -1` at the end: `W_{T_k+1} = W_{T_k} - 1`. -/
theorem abscon_pending_nonneg (t : PlaneTree) {k : ℕ} (hk : 1 ≤ k) (hkl : k ≤ t.degreeCount 0) :
    0 ≤ treeStopPos t k ∧ (treeStopPos t k = 0 ↔ k = t.degreeCount 0) := by
  exact BGWLeaves.Conditioning.AbsCont.abscon_pending_nonneg t hk hkl

/-- **Markov property of the tree at the `k`-th leaf, count `λ = k + m`** (the content of the printed proof
of 5.2: Proposition 1.4 and the strong Markov property of the walk at the `k`-th negative jump).  For
`k ≥ 1`, a nonnegative `F` of the prefix `W^{(k)}(τ)` and a weight `g` of the number `j` of pending trees:
`E_μ[F(W^{(k)}) g(j) 1{λ = k + m}] = E_μ[F(W^{(k)}) g(j) ψ_m(j) 1{λ ≥ k}]`: the pending forest is a fresh
forest of `j` GW trees (`= forestLaw μ j`) and `λ(τ) = k + λ(forest)`.  Proof: combinatorial
decomposition of the degree list into prefix + forest code (module `AbsCont`). -/
theorem tree_markov_leafCount {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1) {k : ℕ} (hk : 1 ≤ k)
    (m : ℕ) (F : List ℤ → ℝ≥0∞) (g : ℕ → ℝ≥0∞) :
    ∫⁻ τ in leafCountEvent (k + m), finiteTreeLift
        (fun t => F (treeStopPath t k) * g (pendingTrees t k)) τ ∂bienaymeLaw μ.toMeasure =
      ∫⁻ τ in leafGeEvent k, finiteTreeLift
        (fun t => F (treeStopPath t k) * (g (pendingTrees t k) * psi μ m (pendingTrees t k))) τ
          ∂bienaymeLaw μ.toMeasure := by
  exact BGWLeaves.Conditioning.AbsCont.tree_markov_leafCount hc hne hk m F g

/-- **Markov property at the `k`-th leaf, count `λ ≥ k + m`** (same content, tail version):
`E_μ[F(W^{(k)}) g(j) 1{λ ≥ k + m}] = E_μ[F(W^{(k)}) g(j) ψ*_m(j) 1{λ ≥ k}]`. -/
theorem tree_markov_leafGe {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1) {k : ℕ} (hk : 1 ≤ k)
    (m : ℕ) (F : List ℤ → ℝ≥0∞) (g : ℕ → ℝ≥0∞) :
    ∫⁻ τ in leafGeEvent (k + m), finiteTreeLift
        (fun t => F (treeStopPath t k) * g (pendingTrees t k)) τ ∂bienaymeLaw μ.toMeasure =
      ∫⁻ τ in leafGeEvent k, finiteTreeLift
        (fun t => F (treeStopPath t k) * (g (pendingTrees t k) * psiStar μ m (pendingTrees t k))) τ
          ∂bienaymeLaw μ.toMeasure := by
  exact BGWLeaves.Conditioning.AbsCont.tree_markov_leafGe hc hne hk m F g

/-- **Proposition 5.2, unconditioned (multiplied) form.**  For `1 ≤ k < n` and every nonnegative `f` of the
prefix `W^{(k)}(τ) = (W_0, …, W_{T_k})`,
`E_μ[f(W^{(k)}) 1{λ = n}] = E_μ[f(W^{(k)}) (ψ_{n-k}(j)/ψ*_{n-k}(j)) 1{λ ≥ n}]`, `j = W_{T_k}(τ)` the number of
pending trees.  No division by a probability of `λ`: this is the form that holds without any positivity
assumption.  Proof: from `tree_markov_leafCount` and `tree_markov_leafGe` (with `g = ψ_m/ψ*_m`, and
`ψ ≤ ψ*`, `ψ* ≠ ⊤`, `ψ_m(j)/ψ*_m(j) · ψ*_m(j) = ψ_m(j)`: if `ψ*_m(j) = 0` then `ψ_m(j) = 0`). -/
theorem abscon_core {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1) {n k : ℕ} (hk1 : 1 ≤ k)
    (hkn : k < n) (f : List ℤ → ℝ≥0∞) :
    ∫⁻ τ in leafCountEvent n, finiteTreeLift (fun t => f (treeStopPath t k)) τ
        ∂bienaymeLaw μ.toMeasure =
      ∫⁻ τ in leafGeEvent n, finiteTreeLift
        (fun t => f (treeStopPath t k) *
          (psi μ (n - k) (pendingTrees t k) / psiStar μ (n - k) (pendingTrees t k))) τ
          ∂bienaymeLaw μ.toMeasure := by
  exact BGWLeaves.Conditioning.AbsCont.abscon_core hc hne hk1 hkn f

/-- **Proposition 5.2 (`prop:abscon`).**  Let `1 ≤ k ≤ n - 1` (`k < n` in `ℕ`), `W^{(k)}(τ) = (W_0(τ), …,
W_{T_k(τ)}(τ))`, `ψ_p(j) = P_{μ,j}(λ = p)` and `ψ*_p(j) = P_{μ,j}(λ ≥ p)`.  For every nonnegative `f` on
finite paths (the printed `f` is bounded; here all `f : List ℤ → ℝ≥0∞`, i.e. the lower-bounded/unbounded
case is included),
`E_μ[f(W^{(k)}) | λ = n] = E_μ[ f(W^{(k)}) · (ψ_{n-k}(W_{T_k})/ψ_n(1)) / (ψ*_{n-k}(W_{T_k})/ψ*_n(1)) | λ ≥ n ]`.
The value `j = W_{T_k(τ)}(τ)` is the NUMBER OF PENDING TREES (`pendingTrees`), `ψ_n(1)` is the one-tree mass
`P_μ[λ = n]` (`psi_one`).  Conventions: the conditional laws are `ProbabilityTheory.cond` (zero measure for a
null event), the `ℝ≥0∞` division convention `0 / 0 = 0`; with these the statement holds WITHOUT any
positivity hypothesis (if `ψ_n(1) = 0`, both sides are `0`), while the printed statement
implicitly assumes `P[λ = n] > 0`.  Proof: assembly of `abscon_core`, `psi_one`, `psiStar_one`,
`sizeGeEvent_ne_zero`-type positivity of `ψ*_n(1)`. -/
theorem prop_abscon {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1) {n k : ℕ} (hk1 : 1 ≤ k)
    (hkn : k < n) (f : List ℤ → ℝ≥0∞) :
    ∫⁻ τ, finiteTreeLift (fun t => f (treeStopPath t k)) τ
        ∂((bienaymeLaw μ.toMeasure)[|leafCountEvent n]) =
      ∫⁻ τ, finiteTreeLift
        (fun t => f (treeStopPath t k) *
          ((psi μ (n - k) (pendingTrees t k) / psi μ n 1) /
            (psiStar μ (n - k) (pendingTrees t k) / psiStar μ n 1))) τ
        ∂((bienaymeLaw μ.toMeasure)[|leafGeEvent n]) := by
  exact BGWLeaves.Conditioning.AbsCont.prop_abscon hc hne hk1 hkn f

/-! ## 5.6 Lemma `lem:CVf` -/

/-- Unconditioned stretched-exponential bound for the clock in the window `ζ ≥ n` (the real content of
Lemma 5.6(i)): `P_μ[ζ ≥ n, ∃ b ∈ (a-α, a+α), |T_{μ₀ b n}/n - b| > n^{-1/4}] = oe_{1/2}(n)`.  Proof: for
`b < a + α < 1` the time `T_{μ₀ b n}` is `< n ≤ ζ` and `Λ_τ(s) = Λ(⌊s⌋+1)` for the walk
(`Lambda_eq_walkLeafCount`, `tree_law_eq_walk_law`), so `lem_GdesDev_walk` (Lemma 2.5(i), for the first `n`
steps, `η = a/4`, `δ = μ₀/4`) gives `|Λ(s)/s - μ₀| ≤ δ n^{-1/4}` on `[ηn, n]` outside an `oe_{1/2}(n)` event, and
inversion of `Λ` into `T` (deterministic: `|T - bn| ≤ (1 + δ n^{3/4})/μ₀ ≤ n^{3/4}` for large `n`, since
`T ≥ a n/2 ≥ η n` because `α < a/2`) gives the claim; `α < (1-a)/2` keeps `T ≤ n`.  NOTE: the printed
justification cites Corollaries 2.6 and 3.3; Corollary 2.6 controls `Λ_τ` only on `[η ζ, ζ]` and is not
sufficient when `ζ ≫ n`; one needs Lemma 2.5(i) on the first `n` steps, as here. -/
theorem clock_unconditioned_oe {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1) {a α : ℝ}
    (ha : a ∈ Set.Ioo (0 : ℝ) 1) (hα : α < min (a / 2) ((1 - a) / 2)) :
    IsOe (1 / 2) fun n : ℕ =>
      (bienaymeLaw μ.toMeasure).real
        (finiteTreeEvent fun t => n ≤ t.size ∧
          ∃ b ∈ Set.Ioo (a - α) (a + α),
            ClockDev n b (treeLeafTime t ⌊(μ 0).toReal * b * n⌋₊)) := by
  exact BGWLeaves.Conditioning.Clock.clock_unconditioned_oe hc hne ha hα

/-- Stretched-exponential bound for the clock under `λ = n` (the real content of Lemma 5.6(ii)):
`P_μ[∃ b ∈ (a-α, a+α), |T_{b n}/n - b/μ₀| > n^{-1/4} | λ = n] = oe_{1/2}(n)` as `n - 1` tends to infinity in
the multiples of `g = arithFactor μ {0}` (`IsOeOn`).  Proof: from Corollary 3.3 (`cor_Lambda_arith`:
`sup_{η ≤ t ≤ 1} |Λ_τ(ζ t)/(ζ t) - μ₀| < δ n^{-1/4}` outside an `oe_{1/2}(n)` event under `λ = n`) and the same
deterministic inversion; under `λ = n` one has `ζ ≈ n/μ₀`, `T_{b n} ≈ b n/μ₀ ∈ [η ζ, ζ]` since `a/2 < b < (1+a)/2`.
(Here Corollary 2.6/3.3 are the right tools, as printed.) -/
theorem clock_leafConditioned_oe {μ : PMF ℕ} {θ : ℝ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hap : Aperiodic μ) (hDA : ∃ a, StableDomain μ θ a) {a α : ℝ}
    (ha : a ∈ Set.Ioo (0 : ℝ) 1) (hα : α < min (a / 2) ((1 - a) / 2)) :
    IsOeOn {n : ℕ | 1 ≤ n ∧ arithFactor μ {0} ∣ n - 1} (1 / 2) fun n : ℕ =>
      (((bienaymeLaw μ.toMeasure)[|leafCountEvent n]).real
        (finiteTreeEvent fun t =>
          ∃ b ∈ Set.Ioo (a - α) (a + α),
            ClockDev n (b / (μ 0).toReal) (treeLeafTime t ⌊b * n⌋₊))) := by
  exact BGWLeaves.Conditioning.Clock.clock_leafConditioned_oe hc hne hap hDA ha hα

/-- **Lemma 5.6(i)** (`lem:CVf`).  Fix `a ∈ (0,1)` and `α < min(a/2, (1-a)/2)`.  Then
`P_μ[ sup_{b ∈ (a-α, a+α)} |T_{μ₀ b n}(τ)/n - b| > n^{-1/4} | ζ ≥ n ] → 0` as `n → ∞`; here `T_u = T_{⌊u⌋}`
(`treeLeafTime`, `⊤` counts as a deviation) and the supremum over `b` is written `∃ b ∈ (a-α, a+α), … > n^{-1/4}`
(strict, as printed).  `α ≤ 0` gives an empty interval, hence the trivially true statement `0 → 0`, as printed.
Hypotheses `(H_θ)` of the paper's section (needed for the polynomial lower bound of `P[ζ ≥ n]`).  Proof: from
`clock_unconditioned_oe` and `sizeGe_poly_lower` (an `oe_{1/2}(n)` is `o(n^{-1/θ-η})`). -/
theorem lem_CVf_i {μ : PMF ℕ} {θ : ℝ} (hc : IsCritical μ) (hne : μ 1 ≠ 1) (hap : Aperiodic μ)
    (hDA : ∃ a, StableDomain μ θ a) {a α : ℝ} (ha : a ∈ Set.Ioo (0 : ℝ) 1)
    (hα : α < min (a / 2) ((1 - a) / 2)) :
    Tendsto (fun n : ℕ =>
      (((bienaymeLaw μ.toMeasure)[|sizeGeEvent n]).real
        (finiteTreeEvent fun t =>
          ∃ b ∈ Set.Ioo (a - α) (a + α),
            ClockDev n b (treeLeafTime t ⌊(μ 0).toReal * b * n⌋₊)))) atTop (𝓝 0) := by
  exact BGWLeaves.Conditioning.Clock.lem_CVf_i hc hne hap hDA ha hα

/-- **Lemma 5.6(ii)** (`lem:CVf`).  Same `a, α`:
`P_μ[ sup_{b ∈ (a-α, a+α)} |T_{b n}(τ)/n - b/μ₀| > n^{-1/4} | λ = n ] → 0`.  The printed section assumes that
`supp μ ∖ {0}` is non-lattice (so `P[λ = n] > 0` for large `n`); it is NOT needed here: for the `n` with
`P[λ = n] = 0` (all `n ≥ 1` with `g ∤ n - 1`, `leafProb_eq_zero_of_not_dvd`) the conditional law is the zero
measure and the term is `0`, so the limit statement is true for all `(H_θ)` laws (for lattice laws it only
says something along the multiples of `g`, as it must).  Proof: from `clock_leafConditioned_oe`. -/
theorem lem_CVf_ii {μ : PMF ℕ} {θ : ℝ} (hc : IsCritical μ) (hne : μ 1 ≠ 1) (hap : Aperiodic μ)
    (hDA : ∃ a, StableDomain μ θ a) {a α : ℝ} (ha : a ∈ Set.Ioo (0 : ℝ) 1)
    (hα : α < min (a / 2) ((1 - a) / 2)) :
    Tendsto (fun n : ℕ =>
      (((bienaymeLaw μ.toMeasure)[|leafCountEvent n]).real
        (finiteTreeEvent fun t =>
          ∃ b ∈ Set.Ioo (a - α) (a + α),
            ClockDev n (b / (μ 0).toReal) (treeLeafTime t ⌊b * n⌋₊)))) atTop (𝓝 0) := by
  exact BGWLeaves.Conditioning.Clock.lem_CVf_ii hc hne hap hDA ha hα

/-! ## 6.10 Lemma `lem:absolueC2` -/

/-- `T_k < ∞` for all `k` almost surely when `μ 0 > 0` (infinitely many steps `-1`, Borel-Cantelli /
`infinitePi` independence). -/
theorem walkLeafTime_ne_top_ae {μ : PMF ℕ} (h0 : μ 0 ≠ 0) :
    ∀ᵐ ω ∂iidWalk μ, ∀ k : ℕ, walkLeafTime ω k ≠ ⊤ := by
  exact BGWLeaves.Conditioning.StrongMarkov.walkLeafTime_ne_top_ae h0

/-- Additivity of the leaf clock and of the position: for `k ≤ n` and `T_k(ω) < ∞`,
`T_n(ω) = T_k(ω) + T_{n-k}(θ_{T_k} ω)` and, if `T_n(ω) < ∞`, `W_{T_n}(ω) = W_{T_k}(ω) + W_{T_{n-k}}(θ_{T_k} ω)`
(both sides `⊤` simultaneously).  Proof: deterministic bookkeeping with `walkLeafCount`. -/
theorem walkLeafTime_add (ω : ℕ → ℕ) {k n : ℕ} (hkn : k ≤ n) (hk : walkLeafTime ω k ≠ ⊤) :
    walkLeafTime ω n = walkLeafTime ω k + walkLeafTime (shiftSeq (walkLeafTime ω k).toNat ω) (n - k) ∧
      (walkLeafTime ω n ≠ ⊤ →
        walkStopPos ω n = walkStopPos ω k +
          walkStopPos (shiftSeq (walkLeafTime ω k).toNat ω) (n - k)) := by
  exact BGWLeaves.Conditioning.StrongMarkov.walkLeafTime_add ω hkn hk

/-- **Strong Markov property of the walk at the `k`-th leaf time `T_k`** (the content of the one-line proof of
Lemma 6.10 and, with Proposition 1.4, of Proposition 5.2).  For `μ 0 > 0`, any nonnegative `F` of the stopped
path and any measurable nonnegative `G` of the future `θ_{T_k} ω`:
`E[F(W^{(k)}) G(θ_{T_k} ω)] = E[F(W^{(k)})] · E[G]`.  (`T_k < ∞` a.s.: the null set where `T_k = ⊤` carries the
junk shift `θ_0` but contributes `0`.)  Proof: decompose on `{T_k = m}` (depends on `ω 0, …, ω (m-1)`), use
independence of the first `m` coordinates from the tail `θ_m ω` (`Measure.infinitePi`, `Fin m → ℕ` product),
and that `θ_m ω` has law `iidWalk μ` (shift invariance). -/
theorem strongMarkov_leafTime {μ : PMF ℕ} (h0 : μ 0 ≠ 0) (k : ℕ) (F : List ℤ → ℝ≥0∞)
    (G : (ℕ → ℕ) → ℝ≥0∞) (hG : Measurable G) :
    ∫⁻ ω, F (walkStopPath ω k) * G (shiftSeq (walkLeafTime ω k).toNat ω) ∂iidWalk μ =
      (∫⁻ ω, F (walkStopPath ω k) ∂iidWalk μ) * ∫⁻ ω, G ω ∂iidWalk μ := by
  exact BGWLeaves.Conditioning.StrongMarkov.strongMarkov_leafTime h0 k F G hG

/-- **Lemma 6.10, unconditioned (multiplied) form**: for every `k < n` (`k = 0`
allowed) and every nonnegative `f` of finite paths,
`E[f(W^{(k)}) 1{W_{T_n} = -1}] = E[f(W^{(k)}) χ_{n-k}(W_{T_k})]`.  No division and no positivity
assumption; it is the form from which `lem_absolueC2_k` follows by the `ℝ≥0∞` division convention
(`χ_n(0) ≤ 1 < ⊤`).  Proof: from `strongMarkov_leafTime` and `walkLeafTime_add`. -/
theorem absolueC2_core {μ : PMF ℕ} (h0 : μ 0 ≠ 0) {n k : ℕ} (hkn : k < n) (f : List ℤ → ℝ≥0∞) :
    ∫⁻ ω in walkStopEvent n (-1), f (walkStopPath ω k) ∂iidWalk μ =
      ∫⁻ ω, f (walkStopPath ω k) * chi μ (n - k) (walkStopPos ω k) ∂iidWalk μ := by
  exact BGWLeaves.Conditioning.StrongMarkov.absolueC2_core h0 hkn f

/-- **Lemma 6.10 (`lem:absolueC2`), the engine**: for every `k < n` (`k = 0` allowed, `W^{(0)} = (W_0)`) and
every nonnegative `f` of finite paths,
`E[f(W^{(k)}) | W_{T_n} = -1] = E[ f(W^{(k)}) χ_{n-k}(W_{T_k}) / χ_n(0) ]`, `W^{(k)} = (W_0, …, W_{T_k})`,
`χ_m(j) = P_j[W_{T_m} = -1]`.  Conventions: `cond` (zero measure if `χ_n(0) = 0`), `ℝ≥0∞` division (`0 / 0 = 0`);
the statement holds with no positivity hypothesis (if `χ_n(0) = 0` then `χ_{n-k}(W_{T_k}) = 0` a.s. by the
strong Markov property, so both sides are `0`).  Needs only `μ 0 > 0`.  Proof: from
`strongMarkov_leafTime` (with `G = 1{T_{n-k} < ∞, W_{T_{n-k}} = -1 - x}` at `x = W_{T_k}`, via
`walkLeafTime_add`; a sum over the countably many values `x ∈ ℤ`). -/
theorem lem_absolueC2_k {μ : PMF ℕ} (h0 : μ 0 ≠ 0) {n k : ℕ} (hkn : k < n) (f : List ℤ → ℝ≥0∞) :
    ∫⁻ ω, f (walkStopPath ω k) ∂((iidWalk μ)[|walkStopEvent n (-1)]) =
      ∫⁻ ω, f (walkStopPath ω k) * (chi μ (n - k) (walkStopPos ω k) / chi μ n 0) ∂iidWalk μ := by
  exact BGWLeaves.Conditioning.StrongMarkov.lem_absolueC2_k h0 hkn f

/-- **Lemma 6.10 (`lem:absolueC2`)** as printed: `a ∈ (0,1)`, `n ≥ 1`, `W^{(an)} = (W_0, …, W_{T_{⌊an⌋}})`,
`E[f(W^{(an)}) | W_{T_n} = -1] = E[f(W^{(an)}) χ_{n-⌊an⌋}(W_{T_{an}}) / χ_n(0)]` for every nonnegative `f` on
`⋃_{i ≥ 1} ℤ^i` (here all `f : List ℤ → ℝ≥0∞`).  Derived from `lem_absolueC2_k` with `k = ⌊a n⌋₊ < n`
(`a < 1`, `n ≥ 1`); note `n - ⌊a n⌋₊ ≥ 1`, so `χ_{n-⌊an⌋}` is the printed `χ_k`, `k ≥ 1`.  The standing
hypothesis `μ 0 > 0` is part of `(H_θ)` (critical, `μ 1 ≠ 1`). -/
theorem lem_absolueC2 {μ : PMF ℕ} (h0 : μ 0 ≠ 0) {a : ℝ} (ha : a ∈ Set.Ioo (0 : ℝ) 1) {n : ℕ}
    (hn : 1 ≤ n) (f : List ℤ → ℝ≥0∞) :
    ∫⁻ ω, f (walkStopPath ω ⌊a * n⌋₊) ∂((iidWalk μ)[|walkStopEvent n (-1)]) =
      ∫⁻ ω, f (walkStopPath ω ⌊a * n⌋₊) *
        (chi μ (n - ⌊a * n⌋₊) (walkStopPos ω ⌊a * n⌋₊) / chi μ n 0) ∂iidWalk μ := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hk : ⌊a * n⌋₊ < n := by
    refine (Nat.floor_lt (by nlinarith [ha.1])).2 ?_
    nlinarith [ha.2]
  exact lem_absolueC2_k h0 hk f

end BGWLeaves
