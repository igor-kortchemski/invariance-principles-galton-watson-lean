module

public import BGWLeaves.LocalEstimates.Defs
import BGWLeaves.LocalEstimates.Proof

/-!
# Local estimates for forests and marked walks

Source: arXiv:1110.2163v4 (line numbers refer to its LaTeX source): Lemma 5.4 (`lem:technical`), Corollary 5.5
(`cor:tejhnique`, with `eq:amontrer`), Lemma 5.11 (`lem:technical2`), Lemma 5.12 (`lem:g`, `eq:e`),
Lemma 5.13 (`lem:techniqueutile`, with `eq:psi`, `eq:retenir`, `eq:cvdd`, `eq:cvmoche`,
`eq:lemtechnique0`, `eq:lemtechnique1`, `eq:lemtechnique2`) and Lemma 6.11 (`lem:technic3`).

The proofs are in the modules `BGWLeaves.LocalEstimates.*` (imported through `BGWLeaves.LocalEstimates.Proof`).
Definitions and bridges are in `BGWLeaves.LocalEstimates.Defs` (and the shared ones in
`BGWLeaves.Conditioning.Defs`).  The declarations `eq_e`, `lem_techniqueutile`, `lem_technical`,
`chi_zero_asymp`, `normB_pos_eventually` and `G0_eq_G0fv` are proved here from other statements of
this file.

Lemma 4.3 is used as `BGWLeaves.lemma_passage` with `U ≡ 1`, `M = 1` (in the proof of `lem_g`); the
concentration of the mark times is `BGWLeaves.lem_CVf2_i` (in the proof of `chi_window`); `psi`, `psiStar`,
`chi`, `forestLaw`, `forestLeafGeEvent`, `forestSizeGeEvent` are those of
`BGWLeaves.Conditioning.Defs` (`ℝ≥0∞`-valued, hence the `.toReal` below); `chi_window` has the extra
hypothesis `ε < 1/μ₀`.

Layout.
* Norming ratios and arithmetic of `Y` (module `NormRatios`): `mu0_ne_one`, `nonLattice_etaLaw_iff`,
  `hS_of_nonLattice`, `normB_ratio_tendsto`, `normBp_ratio_tendsto`, `normBp_div_normB_infVar`,
  `normBp_div_normB_finVar`.
* Lemma 5.11 (module `SizeTailKernel`): `sizeTailProb_eq_tsum`, `tailSum_bound`, `sizeTail_riemann`,
  `lem_technical2`; the kernel `sizeTailKernel`: `sizeTailKernel_eq_integral`, `sizeTailKernel_scaling`,
  `sizeTailKernel_lipschitz`, `qKernel_one_lipschitzOn`, `qKernel_scaling`.
* Lemma 5.12, Lemma 5.4(i), Corollary 5.5 (module `LeafWindow`): `forestSize_window_small`, `lem_g`,
  `eq_e`, `thresholdInv_spec`, `lem_technical_i`, `mn_ratio_tendsto`, `eq_amontrer`, `cor_tejhnique_i`,
  `cor_tejhnique_ii`.
* Lemma 5.13 and Lemma 5.4(ii) (module `Technique`): `aN_tendsto`, `aN_majorant`, `aTilde_eq`, `eq_psi`,
  `eq_retenir`, `bN_bounded`, `bN_sub_Qn`, `Kn_tendsto_*`, `eq_cvmoche`, `bN_tendsto_signed`,
  `lem_techniqueutile`, `eq_lemtechnique0/1/2`, `eq_cvdd`, `lem_technical_ii`, `lem_technical`.
* Lemma 6.11 (module `Chi`): `chi_eq_tsum`, `chi_window`, `chi_retenir`, `chi_Bprime_infVar`,
  `chi_Bprime_finVar_corrected`, `lem_technic3`, `chi_zero_asymp`.
-/

@[expose] public section

namespace BGWLeaves

open MeasureTheory ProbabilityTheory Filter Asymptotics BGW
open BGW.StableTrees BGW.LocallyFinite BGWLeaves.StableAnalysis
open scoped ENNReal Topology

set_option linter.unusedSectionVars false

/-! ## 2. Arithmetic and analytic helpers -/

/-- Helper: `μ₀ < 1` for a critical law with `μ 1 ≠ 1` (the proof is inline in `lem_GdesDev_tree`). -/
theorem mu0_ne_one {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1) : μ 0 ≠ 1 := by
  exact BGWLeaves.LocalEstimates.NormRatios.mu0_ne_one hc hne

/-- The printed standing assumption of Section 5 ("`supp μ ∖ {0}` is non-lattice", line 1269) is
`¬ IsLatticeLaw (etaLaw μ)`: `etaLaw μ` is the law of `Y = K - 1` given `K ≥ 1`, whose support is
`{k - 1 : k ∈ supp μ ∖ {0}}`; a shift by `1` does not change latticeness (`b' = b + 1`). -/
theorem nonLattice_etaLaw_iff {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1) :
    ¬ IsLatticeLaw (etaLaw μ) ↔
      ¬ ∃ (b' : ℤ) (d' : ℕ), 2 ≤ d' ∧ ∀ k : ℕ, μ k ≠ 0 → k ≠ 0 → (d' : ℤ) ∣ (k : ℤ) - b' := by
  exact BGWLeaves.LocalEstimates.NormRatios.nonLattice_etaLaw_iff hc hne

/-- `hS` of the `Y`-law statements (`etaLaw_norming`, `llt_etaLaw_nonlattice`) follows from `Y` being
non-lattice (a point mass is lattice: `δ_a` is carried by `a + 2ℤ`). -/
theorem hS_of_nonLattice {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hnl : ¬ IsLatticeLaw (etaLaw μ)) :
    ∃ k₁ k₂ : ℕ, 1 ≤ k₁ ∧ k₁ < k₂ ∧ μ k₁ ≠ 0 ∧ μ k₂ ≠ 0 := by
  exact BGWLeaves.LocalEstimates.NormRatios.hS_of_nonLattice hc hne hnl

section Htheta

variable {μ : PMF ℕ} {θ : ℝ} (hc : IsCritical μ) (hne : μ 1 ≠ 1) (hap : Aperiodic μ)
  (hDA : ∃ b, StableDomain μ θ b)
include hc hne hap hDA

/-- `B_n > 0` for large `n` (from `locallimit_i`, as in `hSlow_slowlyVarying`). -/
theorem normB_pos_eventually : ∀ᶠ n : ℕ in atTop, 0 < norming (stepLaw μ) θ n := by
  obtain ⟨b, hb⟩ := hDA
  have := isProbabilityMeasure_stepLaw μ
  obtain ⟨N, hN⟩ := (locallimit_i (stepLaw μ) (stepLaw_lt_neg_one μ) (integrable_stepLaw hc)
    ⟨b, by rw [mean_stepLaw hc]; exact stableDomain_isStableAttracted hb⟩).pos
  exact eventually_atTop.2 ⟨N, hN⟩

/-- **Regular variation of `B`** (the form in which the paper uses it: "`B_{r_n}/B_{n/μ₀} → 1`",
lines 1795, 1743-1744; "`B'_n ∼ c^{1/θ} B'_{q_n(u)}`", line 1866): if `u_n / n → l > 0` then
`B_{u_n}/B_n → l^{1/θ}`.  From `B_n = h(n) n^{1/θ}`, `h` slowly varying (`locallimit_ii`), `B` monotone: for `δ > 0` eventually
`(l-δ)n ≤ u_n ≤ (l+δ)n`, so `B_{(l-δ)n} ≤ B_{u_n} ≤ B_{(l+δ)n}` and the pointwise limits `(l ± δ)^{1/θ}` squeeze
(no uniform convergence theorem is needed because of the monotonicity). -/
theorem normB_ratio_tendsto {u : ℕ → ℝ} {l : ℝ} (hl : 0 < l)
    (hu : Tendsto (fun n : ℕ => u n / n) atTop (𝓝 l)) :
    Tendsto (fun n : ℕ => normB μ θ (u n) / normB μ θ n) atTop (𝓝 (l ^ (1 / θ))) := by
  exact BGWLeaves.LocalEstimates.NormRatios.normB_ratio_tendsto hc hne hap hDA hl hu

/-- The same for `B'_n` (`etaLaw_norming`: `B'_n = h'(n) n^{1/θ}`, `h'` slowly varying, `B'` monotone). -/
theorem normBp_ratio_tendsto {u : ℕ → ℝ} {l : ℝ} (hl : 0 < l)
    (hu : Tendsto (fun n : ℕ => u n / n) atTop (𝓝 l)) :
    Tendsto (fun n : ℕ => normBp μ θ (u n) / normBp μ θ n) atTop (𝓝 (l ^ (1 / θ))) := by
  exact BGWLeaves.LocalEstimates.NormRatios.normBp_ratio_tendsto hc hne hap hDA hl hu

/-- The ratio between the two normings, by regime (Lemma 3.4 for `σ² = ∞`, the corrected
finite-variance ratio otherwise), **in the form used in 5.13 and 6.11**:
`B'_n / B_{⌊n/μ₀⌋} → c^{1/θ}` if `σ² = ∞` (from `lem_hhp` and `normB_ratio_tendsto`: `B'_n/B_n → (1-μ₀)^{-1/θ}`,
`B_n/B_{n/μ₀} → μ₀^{1/θ}`), and `→ √μ₀ σ'/σ` if `σ² < ∞` (`finiteVariance_norming_ratio_eta`; this is
**not** `c^{1/θ}`, correction 4 of `FORMALIZATION_REPORT.md`). -/
theorem normBp_div_normB_infVar
    (hinf : ¬ Integrable (fun z : ℤ => (z : ℝ) ^ 2) (stepLaw μ)) :
    Tendsto (fun n : ℕ => norming (etaLaw μ) θ n / normB μ θ ((n : ℝ) / (μ 0).toReal)) atTop
      (𝓝 (cC μ ^ (1 / θ))) := by
  exact BGWLeaves.LocalEstimates.NormRatios.normBp_div_normB_infVar hc hne hap hDA hinf

theorem normBp_div_normB_finVar
    (hfin : Integrable (fun z : ℤ => (z : ℝ) ^ 2) (stepLaw μ)) :
    Tendsto (fun n : ℕ => norming (etaLaw μ) θ n / normB μ θ ((n : ℝ) / (μ 0).toReal)) atTop
      (𝓝 (Real.sqrt (μ 0).toReal * Real.sqrt (variance (etaLaw μ)) /
        Real.sqrt (variance (stepLaw μ)))) := by
  exact BGWLeaves.LocalEstimates.NormRatios.normBp_div_normB_finVar hc hne hap hDA hfin

/-! ## 3. Lemma 5.11 (`lem:technical2`): the uniform size-tail kernel

The paper cites Le Gall (`LGIto`, finite variance) and `Kautre` Lemma 3.2(ii) (general index).  It can be
derived here from the uniform local limit theorem (`llt_abstract` / `llt_stepLaw`), the unmarked
Kemperman formula and regular variation, so it is proved, not taken as a cited input:
`P_j[ζ ≥ n] = ∑_{p ≥ n} (j/p) P[W_p = -j]`; replace `P[W_p = -j]` by `p₁(-j/B_p)/B_p` with error `≤ ε` uniform
in `p ≥ N`, `j ∈ ℤ`; the error sum is `≤ ε j ∑_{p≥n} 1/(p B_p) ≤ ε C α` (sharp Karamata tail sum, as in the proof
of `sizeTail_asymp`); the main term is a Riemann sum of `s ↦ q_s(j/B_n)` (Potter bounds for the tail). -/

/-- Kemperman at the level of the tail: `P_j[ζ ≥ n] = ∑_{p ≥ n} (j/p) P[W_p = -j]` for `j ≥ 1`, `n ≥ 1`
(critical: infinite forests are null).  From `firstHit_law`, `kemperman_unmarked`, `intWalkProb_stepLaw`
and `ae_finiteVertices_bienaymeLaw`. -/
theorem sizeTailProb_eq_tsum {n j : ℕ} (hn : 1 ≤ n) (hj : 1 ≤ j) :
    sizeTailProb μ n j =
      ∑' p : ℕ, if n ≤ p then ((j : ℝ) / p) * intWalkProb (stepLaw μ) p (-(j : ℤ)) else 0 := by
  exact BGWLeaves.LocalEstimates.SizeTailKernel.sizeTailProb_eq_tsum hc hne hap hDA hn hj

/-- The tail sum bound `∑_{p ≥ n} 1/(p B_p) ≤ C/B_n` (BGW `karamata_tail_tsum`; sharp form `∼ θ/B_n`). -/
theorem tailSum_bound :
    ∃ C : ℝ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∑' p : ℕ, (if n ≤ p then 1 / ((p : ℝ) * norming (stepLaw μ) θ p) else 0) ≤
        C / norming (stepLaw μ) θ n := by
  exact BGWLeaves.LocalEstimates.SizeTailKernel.tailSum_bound hc hne hap hDA

/-- The Riemann-sum step of 5.11: uniformly for `1 ≤ j ≤ α B_n`,
`∑_{p ≥ n} (j/p) (1/B_p) p₁(-j/B_p)` is within `ε` of `∫_1^∞ q_s(j/B_n) ds`
(`s ↦ n (j/⌊ns⌋)(1/B_{⌊ns⌋}) p₁(-j/B_{⌊ns⌋})` converges to `q_s(j/B_n)` since `B_{⌊ns⌋}/B_n → s^{1/θ}`
locally uniformly, dominated by `C s^{-1-1/θ+ε'}` by Potter; `p₁` is bounded and Lipschitz). -/
theorem sizeTail_riemann {α : ℝ} (hα : 0 < α) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ j : ℕ, 1 ≤ j → (j : ℝ) ≤ α * norming (stepLaw μ) θ n →
      |(∑' p : ℕ, if n ≤ p then ((j : ℝ) / p) * (1 / norming (stepLaw μ) θ p) *
          Scalar.stableDensity θ (-((j : ℝ) / norming (stepLaw μ) θ p)) else 0) -
        sizeTailKernel θ 1 ((j : ℝ) / norming (stepLaw μ) θ n)| ≤ ε := by
  exact BGWLeaves.LocalEstimates.SizeTailKernel.sizeTail_riemann hc hne hap hDA hα hε

/-- **Lemma 5.11 (`lem:technical2`)**, line 1750: `lim_n sup_{1 ≤ j ≤ αB_n} |P_j[ζ(f) ≥ n] - ∫_1^∞ q_s(j/B_n) ds| = 0`
(`α > 0` fixed; the argument of `q_s` is `j/B_n`, **not** `j/B_{n/μ₀}`).  Hypotheses: `(H_θ)`.  Derived
from the local limit theorem; the paper cites Le Gall and `Kautre`. -/
theorem lem_technical2 {α : ℝ} (hα : 0 < α) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ j : ℕ, 1 ≤ j → (j : ℝ) ≤ α * normB μ θ n →
      |sizeTailProb μ n j - sizeTailKernel θ 1 ((j : ℝ) / normB μ θ n)| ≤ ε := by
  exact BGWLeaves.LocalEstimates.SizeTailKernel.lem_technical2 hc hne hap hDA hα hε

/-! ## 4. Lemma 5.12 (`lem:g`) and `eq:e` -/

/-- `P_j[n - γ n^{3/4} ≤ ζ ≤ n] → 0` uniformly in `1 ≤ j ≤ αB_n`, `γ = μ₀^{-1} + 1`: the displayed claim in the
proof of 5.12 (line 1767).  By unmarked Kemperman `P_j[ζ = k] = (j/k) P[W_k = -j]`, the uniform LLT
(`llt_stepLaw`), `B_k ≥ B_n/2` on the window (regular variation) and `|x p₁(-x)| ≤ M`: each of the
`≈ γ n^{3/4}` terms is `≤ (M + 2αε)/k`. -/
theorem forestSize_window_small {α : ℝ} (hα : 0 < α) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ j : ℕ, 1 ≤ j → (j : ℝ) ≤ α * normB μ θ n →
      (forestLaw μ j).real (forestSizeWindow (μ 0).toReal j n) ≤ ε := by
  exact BGWLeaves.LocalEstimates.LeafWindow.forestSize_window_small hc hne hap hDA hα hε

end Htheta


section Htheta2

variable {μ : PMF ℕ} {θ : ℝ} (hc : IsCritical μ) (hne : μ 1 ≠ 1) (hap : Aperiodic μ)
  (hDA : ∃ b, StableDomain μ θ b)
include hc hne hap hDA

/-- **Lemma 5.12 (`lem:g`)**, line 1760: for `α > 0`,
`lim_n sup_{1 ≤ j ≤ αB_n} |P_j[ζ(f) ≥ n] - P_j[λ(f) ≥ μ₀ n - n^{3/4}]| = 0`.  Proof: Lemma 4.3
(`BGWLeaves.lemma_passage` with `U ≡ 1`, `M = 1`, `isBoundedTest_one`; the cutoff is
`leafCutoff μ n = ⌈μ₀ n - n^{3/4}⌉₊`, equivalent to the real threshold by `mem_forestLeafGeEvent_real_iff`
up to the null set of infinite forests) and `forestSize_window_small` (and `oe_{1/2}(n) → 0`). -/
theorem lem_g {α : ℝ} (hα : 0 < α) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ j : ℕ, 1 ≤ j → (j : ℝ) ≤ α * normB μ θ n →
      |sizeTailProb μ n j -
          (forestLaw μ j).real (forestLeafGeEvent j (leafCutoff μ n))| ≤ ε := by
  exact BGWLeaves.LocalEstimates.LeafWindow.lem_g hc hne hap hDA hα hε

/-- **`eq:e`** (line 1775): `lim_n sup_{1 ≤ j ≤ αB_n} |P_j[λ(f) ≥ μ₀ n - n^{3/4}] - ∫_1^∞ q_s(j/B_n) ds| = 0`.
Proved from `lem_technical2` and `lem_g` (triangle inequality). -/
theorem eq_e {α : ℝ} (hα : 0 < α) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ j : ℕ, 1 ≤ j → (j : ℝ) ≤ α * normB μ θ n →
      |(forestLaw μ j).real (forestLeafGeEvent j (leafCutoff μ n)) -
          sizeTailKernel θ 1 ((j : ℝ) / normB μ θ n)| ≤ ε := by
  obtain ⟨N₁, h₁⟩ := lem_technical2 hc hne hap hDA hα (half_pos hε)
  obtain ⟨N₂, h₂⟩ := lem_g hc hne hap hDA hα (half_pos hε)
  refine ⟨max N₁ N₂, fun n hn j hj1 hj2 => ?_⟩
  have a := h₁ n (le_of_max_le_left hn) j hj1 hj2
  have b := h₂ n (le_of_max_le_right hn) j hj1 hj2
  rw [abs_sub_comm] at b
  calc _ ≤ _ := abs_sub_le _ (sizeTailProb μ n j) _
    _ ≤ ε / 2 + ε / 2 := add_le_add b a
    _ = ε := by ring

end Htheta2

/-! ## 5. The kernel `∫_a^∞ q_s` (analytic helpers of Lemma 5.4(i) and Corollary 5.5) -/

/-- The closed form of the proof of Corollary 5.5 (line 1431): for `x ≥ 0`,
`∫_1^∞ q_s(x) ds = x ∫_1^∞ s^{-1-1/θ} p₁(-x s^{-1/θ}) ds = θ ∫_0^x p₁(-u) du`
(substitution `u = x s^{-1/θ}`; integrability of `q_s(x)` on `(1,∞)` from `p₁` bounded). -/
theorem sizeTailKernel_eq_integral {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {x : ℝ} (hx : 0 ≤ x) :
    sizeTailKernel θ 1 x = θ * ∫ u in (0 : ℝ)..x, Scalar.stableDensity θ (-u) := by
  exact BGWLeaves.LocalEstimates.SizeTailKernel.sizeTailKernel_eq_integral hθ hx

/-- The scaling identity of line 1426: for `a > 0`, `∫_a^∞ q_s(x) ds = ∫_1^∞ q_s(x a^{-1/θ}) ds`
(change of variable `s ↦ a s` and `eq:scaling`; with `a = 1 - a'` this is the printed
`∫_{1-a}^∞ q_s(x) ds = ∫_1^∞ q_s(x/(1-a)^{1/θ}) ds`). -/
theorem sizeTailKernel_scaling {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {a : ℝ} (ha : 0 < a) {x : ℝ} (hx : 0 ≤ x) :
    sizeTailKernel θ a x = sizeTailKernel θ 1 (x * a ^ (-(1 / θ))) := by
  exact BGWLeaves.LocalEstimates.SizeTailKernel.sizeTailKernel_scaling hθ ha hx

/-- Lipschitz bound of the kernel (line 1432-1435: `|∫_{a_1}^{a_2} p₁(-u) du| ≤ θ' M |a_2 - a_1|`, `M` a bound
of `p₁`): `|∫_1^∞ (q_s(x) - q_s(y)) ds| ≤ θ M |x - y|` for `x, y ≥ 0`.  Follows from the two statements above. -/
theorem sizeTailKernel_lipschitz {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ x y : ℝ, 0 ≤ x → 0 ≤ y →
      |sizeTailKernel θ 1 x - sizeTailKernel θ 1 y| ≤ L * |x - y| := by
  exact BGWLeaves.LocalEstimates.SizeTailKernel.sizeTailKernel_lipschitz hθ

/-- `q_s`-version: `x ↦ q_1(x) = x p₁(-x)` is Lipschitz on bounded sets (used in Corollary 5.5(ii); `p₁` is
bounded and Lipschitz: BGW `lipschitzWith_stableDensity`). -/
theorem qKernel_one_lipschitzOn {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (A : ℝ) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ x y : ℝ, 0 ≤ x → x ≤ A → 0 ≤ y → y ≤ A →
      |qKernel θ 1 x - qKernel θ 1 y| ≤ L * |x - y| := by
  exact BGWLeaves.LocalEstimates.SizeTailKernel.qKernel_one_lipschitzOn hθ A

/-- `q_s(x) = (1-a)^{-1} q_1(x (1-a)^{-1/θ})` for `s = 1 - a` (the identity behind Corollary 5.5(ii),
from `eq:scaling`): `q_{1-a}(x) = (1-a)^{-1} q_1(x/(1-a)^{1/θ})`. -/
theorem qKernel_scaling {θ : ℝ} {a : ℝ} (ha : 0 < a) (x : ℝ) :
    qKernel θ a x = a⁻¹ * qKernel θ 1 (x * a ^ (-(1 / θ))) := by
  exact BGWLeaves.LocalEstimates.SizeTailKernel.qKernel_scaling ha x

/-! ## 6. Lemma 5.4 (`lem:technical`) -/

section Htheta3

variable {μ : PMF ℕ} {θ : ℝ} (hc : IsCritical μ) (hne : μ 1 ≠ 1) (hap : Aperiodic μ)
  (hDA : ∃ b, StableDomain μ θ b)
include hc hne hap hDA

/-- Threshold inversion (line 1783): for large `n`, `⌈μ₀ r_n - r_n^{3/4}⌉ = n` and `r_n/n → 1/μ₀`
(`r ↦ μ₀ r - r^{3/4}` is eventually increasing with increments in `(0,1)`, tends to `∞`). -/
theorem thresholdInv_spec :
    (∀ᶠ n : ℕ in atTop, 1 ≤ thresholdInv (μ 0).toReal n ∧
      ⌈(μ 0).toReal * thresholdInv (μ 0).toReal n - (thresholdInv (μ 0).toReal n : ℝ) ^ (3 / 4 : ℝ)⌉ =
        (n : ℤ)) ∧
    Tendsto (fun n : ℕ => (thresholdInv (μ 0).toReal n : ℝ) / n) atTop (𝓝 (1 / (μ 0).toReal)) := by
  exact BGWLeaves.LocalEstimates.LeafWindow.thresholdInv_spec hc hne hap hDA

/-- **Lemma 5.4(i) (`lem:technical`, line 1412)**: for every `α > 0`,
`lim_n sup_{1 ≤ j ≤ αB_n} |ψ*_n(j) - ∫_1^∞ q_s(j/B_{n/μ₀}) ds| = 0` (`B_{n/μ₀} = B_{⌊n/μ₀⌋}`).
Hypotheses: `(H_θ)` only (the non-lattice assumption of §5 is not needed for (i)).  Proof: `eq_e` at
`n := r_n` (`ψ*_n(j) = P_j[λ ≥ μ₀ r_n - r_n^{3/4}]` since `λ ∈ ℕ`; `j ≤ αB_n ≤ αB_{r_n}`), then
`sizeTailKernel_lipschitz` with `|B_n/B_{r_n} - B_n/B_{n/μ₀}| → 0` (`normB_ratio_tendsto`). -/
theorem lem_technical_i {α : ℝ} (hα : 0 < α) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ j : ℕ, 1 ≤ j → (j : ℝ) ≤ α * normB μ θ n →
      |(psiStar μ n j).toReal - sizeTailKernel θ 1 ((j : ℝ) / normB μ θ ((n : ℝ) / (μ 0).toReal))| ≤ ε := by
  exact BGWLeaves.LocalEstimates.LeafWindow.lem_technical_i hc hne hap hDA hα hε

end Htheta3

/-! ## 7. Corollary 5.5 (`cor:tejhnique`) and `eq:amontrer` -/

section Htheta4

variable {μ : PMF ℕ} {θ : ℝ} (hc : IsCritical μ) (hne : μ 1 ≠ 1) (hap : Aperiodic μ)
  (hDA : ∃ b, StableDomain μ θ b)
include hc hne hap hDA

/-- The new leaf number `m_n = n - ⌊a μ₀ r_n⌋` satisfies `m_n/n → 1 - a` (from `n/r_n → μ₀`); in
particular `m_n ≥ 1` eventually. -/
theorem mn_ratio_tendsto {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {r : ℕ → ℕ} (hr : ∀ n, 0 < r n)
    (hrn : Tendsto (fun n : ℕ => (n : ℝ) / r n) atTop (𝓝 (μ 0).toReal)) :
    Tendsto (fun n : ℕ => ((n - ⌊a * (μ 0).toReal * r n⌋₊ : ℕ) : ℝ) / n) atTop (𝓝 (1 - a)) := by
  exact BGWLeaves.LocalEstimates.LeafWindow.mn_ratio_tendsto hc hne hap hDA ha0 ha1 hr hrn

/-- **`eq:amontrer`** (line 1425): with `a_1(n,j) = j/((1-a)^{1/θ} B_{n/μ₀})` and
`a_2(n,j) = j/B_{(n - ⌊aμ₀r_n⌋)/μ₀}`, `sup_{1 ≤ j ≤ αB_n} |∫_1^∞ (q_s(a_1) - q_s(a_2)) ds| → 0`
(the integral of the difference is the difference `sizeTailKernel θ 1 a_1 - sizeTailKernel θ 1 a_2`;
Lipschitz bound and `B_n/((1-a)^{1/θ} B_{n/μ₀}) - B_n/B_{(n-⌊aμ₀r_n⌋)/μ₀} → 0`). -/
theorem eq_amontrer {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {r : ℕ → ℕ} (hr : ∀ n, 0 < r n)
    (hrn : Tendsto (fun n : ℕ => (n : ℝ) / r n) atTop (𝓝 (μ 0).toReal))
    {α : ℝ} (hα : 0 < α) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ j : ℕ, 1 ≤ j → (j : ℝ) ≤ α * normB μ θ n →
      |sizeTailKernel θ 1 ((j : ℝ) / ((1 - a) ^ (1 / θ) * normB μ θ ((n : ℝ) / (μ 0).toReal))) -
          sizeTailKernel θ 1 ((j : ℝ) /
            normB μ θ (((n - ⌊a * (μ 0).toReal * r n⌋₊ : ℕ) : ℝ) / (μ 0).toReal))| ≤ ε := by
  exact BGWLeaves.LocalEstimates.LeafWindow.eq_amontrer hc hne hap hDA ha0 ha1 hr hrn hα hε

/-- **Corollary 5.5(i) (`cor:tejhnique`, line 1422)**: if `n/r_n → μ₀` (`r_n` positive integers) and
`a ∈ (0,1)`, then `lim_n sup_{1 ≤ j ≤ αB_n} |ψ*_{n - ⌊aμ₀r_n⌋}(j) - ∫_{1-a}^∞ q_s(j/B_{n/μ₀}) ds| = 0`.
The sup is over `j ≤ αB_n` (not `αB_{n - ⌊aμ₀r_n⌋}`): in the proof apply `lem_technical_i` at `m_n` with
`α' = 2α(1-a)^{-1/θ}` (`B_n ≤ α'/α · B_{m_n}` for large `n`).  The printed range of `a` is only implicit
(`a ∈ (0,1)`; `1 - a` is the lower limit of the integral). -/
theorem cor_tejhnique_i {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {r : ℕ → ℕ} (hr : ∀ n, 0 < r n)
    (hrn : Tendsto (fun n : ℕ => (n : ℝ) / r n) atTop (𝓝 (μ 0).toReal))
    {α : ℝ} (hα : 0 < α) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ j : ℕ, 1 ≤ j → (j : ℝ) ≤ α * normB μ θ n →
      |(psiStar μ (n - ⌊a * (μ 0).toReal * r n⌋₊) j).toReal -
          sizeTailKernel θ (1 - a) ((j : ℝ) / normB μ θ ((n : ℝ) / (μ 0).toReal))| ≤ ε := by
  exact BGWLeaves.LocalEstimates.LeafWindow.cor_tejhnique_i hc hne hap hDA ha0 ha1 hr hrn hα hε

/-- **Corollary 5.5(ii)**: same hypotheses, `lim_n sup_{1 ≤ j ≤ αB_n} |n ψ_{n - ⌊aμ₀r_n⌋}(j) - q_{1-a}(j/B_{n/μ₀})| = 0`
(the prefactor stays `n`, not `m_n`; `q_{1-a}(x) = (1-a)^{-1} q_1(x (1-a)^{-1/θ})`).  Needs the non-lattice
assumption of §5 (it is `lem_technical_ii` at `m_n`).  "Easier and left to the reader" in the paper. -/
theorem cor_tejhnique_ii (hnl : ¬ IsLatticeLaw (etaLaw μ))
    {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {r : ℕ → ℕ} (hr : ∀ n, 0 < r n)
    (hrn : Tendsto (fun n : ℕ => (n : ℝ) / r n) atTop (𝓝 (μ 0).toReal))
    {α : ℝ} (hα : 0 < α) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ j : ℕ, 1 ≤ j → (j : ℝ) ≤ α * normB μ θ n →
      |(n : ℝ) * (psi μ (n - ⌊a * (μ 0).toReal * r n⌋₊) j).toReal -
          qKernel θ (1 - a) ((j : ℝ) / normB μ θ ((n : ℝ) / (μ 0).toReal))| ≤ ε := by
  exact BGWLeaves.LocalEstimates.LeafWindow.cor_tejhnique_ii hc hne hap hDA hnl ha0 ha1 hr hrn hα hε

end Htheta4

/-! ## 8. Lemma 5.13 (`lem:techniqueutile`) and the proof of Lemma 5.4(ii)

Intermediate statements (kept visible, in the order of the proof, lines 1823-1966).  Throughout `0 < ε <
(1-μ₀)/(2μ₀)` (the printed "`0 < ε < 1`" is not enough for the uniform bound of `b_n`). -/

section Mu0

variable {μ : PMF ℕ} (h0 : μ 0 ≠ 0) (h1 : μ 0 ≠ 1)
include h0 h1

/-- **First half of Lemma 5.13**: for fixed `u ∈ ℝ`, `a_n(u) → F₀(u)`, `F₀(u) = √μ₀ F(μ₀^{3/2}u)` (`F0`).
By the strong LLT for the Bernoulli walk (`strongLLT`, `Bernoulli` is non-lattice in the paper's sense,
`E S_1 = μ₀`, `Var S_1 = μ₀(1-μ₀)`, `stableDensity_two`), line 1856. -/
theorem aN_tendsto (u : ℝ) :
    Tendsto (fun n : ℕ => aN μ n u) atTop (𝓝 (F0 (μ 0).toReal u)) := by
  exact BGWLeaves.LocalEstimates.Technique.aN_tendsto h0 h1 u

/-- `a_n(u) ≤ C (1 ∧ u^{-2})` for `|u| ≤ ε√n` and `n ≥ N` (line 1890: "from Theorem 3.5"; the weight
`max 1 ((x - mn)²/n)` inside the supremum is exactly what is needed).  `1 ∧ u^{-2}` is written
`1 / max 1 (u²)` (equal for all `u`; avoids Lean's `0⁻¹ = 0`). -/
theorem aN_majorant {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < (1 - (μ 0).toReal) / (2 * (μ 0).toReal)) :
    ∃ C : ℝ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ u : ℝ, |u| ≤ ε * Real.sqrt n →
      aN μ n u ≤ C / max 1 (u ^ 2) := by
  exact BGWLeaves.LocalEstimates.Technique.aN_majorant h0 h1 hε0 hε1

/-- `a_n(u)` and the index-shifted `ã_n(u) = √n P[S_{r_n(u)-1} = n-1]` of Lemma 6.11 (line 2223) are related by
`C(p-1,n-1) = (n/p) C(p,n)`: `ã_n(u) = n/(μ₀ r_n(u)) · a_n(u)` (`r_n(u) ≥ 1`).  Proof: `Nat.succ_mul_choose_eq`. -/
theorem aTilde_eq {n : ℕ} (hn : 1 ≤ n) (u : ℝ) (hr : 1 ≤ rN μ n u) :
    Real.sqrt n * binomProb (μ 0).toReal (rN μ n u - 1) (n - 1) =
      (n : ℝ) / ((μ 0).toReal * rN μ n u) * aN μ n u := by
  exact BGWLeaves.LocalEstimates.Technique.aTilde_eq h0 h1 hn u hr

/-- **`eq:psi`** (line 1828), with `n` times: `n ψ_n(j) = n P_j[λ = n, n/μ₀ - εn ≤ ζ ≤ n/μ₀ + εn] + oe_{1/2}(n)`,
uniformly in `1 ≤ j ≤ n`.  From `lem_GdesDev2_ii` (`|ζ - n/μ₀| > ζ^{3/4}` is implied by `|ζ - n/μ₀| > εn` for large `n`;
the factor `n` is absorbed into `oe_{1/2}`; small `n` by enlarging `C`). -/
theorem eq_psi {ε : ℝ} (hε : 0 < ε) :
    IsOeUniform (1 / 2) fun j n : ℕ =>
      |(n : ℝ) * (psi μ n j).toReal - (n : ℝ) * (forestLaw μ j).real (forestLeafWindowEvent j n
          ((n : ℝ) / (μ 0).toReal - ε * n) ((n : ℝ) / (μ 0).toReal + ε * n))| := by
  exact BGWLeaves.LocalEstimates.Technique.eq_psi h0 h1 hε

/-- **`eq:retenir`** (line 1843), exact form: for `n, j ≥ 1` with `B'_n > 0`,
`n P_j[λ = n, n/μ₀ - εn ≤ ζ ≤ n/μ₀ + εn] = (j/B'_n) ∫_{u₁}^{u₂} (n/r_n(u)) a_n(u) b_n(u,j) du`, with the exact
limits `u₁ = (⌈n/μ₀ - εn⌉ - n/μ₀)/√n`, `u₂ = (⌊n/μ₀ + εn⌋ + 1 - n/μ₀)/√n` (the printed "`±ε√n + o(1)`").
Proof: `prop_K` for `p ≥ max(1,n)`, `pi_eta_real_eq_intWalkProb` (`Measure.pi (eta μ)` to `intWalkProb (etaLaw μ)`),
the empty events for `p < n`, and `Σ_p f(p) = √n ∫ f(⌊n/μ₀ + u√n⌋) du` on the step function. -/
theorem eq_retenir {θ ε : ℝ} (hε : 0 < ε) {n j : ℕ} (hn : 1 ≤ n) (hj : 1 ≤ j)
    (hB : 0 < norming (etaLaw μ) θ n) :
    (n : ℝ) * (forestLaw μ j).real (forestLeafWindowEvent j n
        ((n : ℝ) / (μ 0).toReal - ε * n) ((n : ℝ) / (μ 0).toReal + ε * n)) =
      ((j : ℝ) / norming (etaLaw μ) θ n) *
        ∫ u in ((⌈(n : ℝ) / (μ 0).toReal - ε * n⌉ - (n : ℝ) / (μ 0).toReal) / Real.sqrt n)..
            ((⌊(n : ℝ) / (μ 0).toReal + ε * n⌋ + 1 - (n : ℝ) / (μ 0).toReal) / Real.sqrt n),
          (n : ℝ) / (rN μ n u : ℝ) * aN μ n u * bN μ θ n u j := by
  exact BGWLeaves.LocalEstimates.Technique.eq_retenir h0 h1 hε hn hj hB

end Mu0

section Htheta5

variable {μ : PMF ℕ} {θ : ℝ} (hc : IsCritical μ) (hne : μ 1 ≠ 1) (hap : Aperiodic μ)
  (hDA : ∃ b, StableDomain μ θ b) (hnl : ¬ IsLatticeLaw (etaLaw μ))
include hc hne hap hDA hnl

/-- `b_n(u,j)` is uniformly bounded (line 1890: "by (eq:ll) the functions `b_n` are uniformly bounded"): for
`|u| ≤ ε√n`, all `j ∈ ℤ`, `n ≥ N`.  `B'_n P[W'_q = k] = (B'_n/B'_q) B'_q P[W'_q=k] ≤ (B'_n/B'_q)(‖p₁‖ + 1)`
with `q = r_n(u) - n ≥ n(1-μ₀)/(2μ₀) - 1`, `B'_n/B'_q` bounded (regular variation).  Needs `ε` small. -/
theorem bN_bounded {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < (1 - (μ 0).toReal) / (2 * (μ 0).toReal)) :
    ∃ C : ℝ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ u : ℝ, |u| ≤ ε * Real.sqrt n → ∀ j : ℤ,
      |bN μ θ n u j| ≤ C := by
  exact BGWLeaves.LocalEstimates.Technique.bN_bounded hc hne hap hDA hnl hε0 hε1

/-- First reduction in the proof of the second half of 5.13 (line 1865): `|b_n(u,j) - Q_n(u,j)| → 0` as
`n → ∞`, for fixed `u`, uniformly in **all** `j ∈ ℤ` (the printed claim is for `0 ≤ j ≤ αB_n`; the uniform LLT
`llt_etaLaw_nonlattice` is uniform in `k ∈ ℤ`, so no range is needed), with `B'_n ∼ c^{1/θ} B'_{q_n(u)}`
(`normBp_ratio_tendsto`, `q_n(u)/n → 1/c`). -/
theorem bN_sub_Qn (u : ℝ) {ε' : ℝ} (hε' : 0 < ε') :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ j : ℤ, |bN μ θ n u j - Qn μ θ n u j| ≤ ε' := by
  exact BGWLeaves.LocalEstimates.Technique.bN_sub_Qn hc hne hap hDA hnl u hε'

/-- `K_n(u,j) → 0` in the finite variance case (`θ = 2`, `B'_n = σ'√(n/2)`; "simple calculations show
`K_n ≤ A/√n`", line 1873). -/
theorem Kn_tendsto_finiteVariance
    (hfin : Integrable (fun z : ℤ => (z : ℝ) ^ 2) (stepLaw μ)) (u : ℝ) {α : ℝ} (hα : 0 < α)
    {ε' : ℝ} (hε' : 0 < ε') :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ j : ℤ, |(j : ℝ)| ≤ α * normB μ θ n → Kn μ θ n u j ≤ ε' := by
  exact BGWLeaves.LocalEstimates.Technique.Kn_tendsto_finiteVariance hc hne hap hDA hnl hfin u hα hε'

/-- `K_n(u,j) → 0` for `σ² = ∞`, `θ < 2` (line 1875: `B'_{q_n(u)} ≥ n^{1/θ-η}`, `1/θ - η > 1/2`, Potter /
`slow_rpow_mul_tendsto_atTop`; `α' = 2α(1-μ₀)^{1/θ}`-type constant from `lem_hhp` for `j ≤ α' B'_n`). -/
theorem Kn_tendsto_infiniteVariance_lt_two (hθ : θ < 2)
    (hinf : ¬ Integrable (fun z : ℤ => (z : ℝ) ^ 2) (stepLaw μ)) (u : ℝ) {α : ℝ} (hα : 0 < α)
    {ε' : ℝ} (hε' : 0 < ε') :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ j : ℤ, |(j : ℝ)| ≤ α * normB μ θ n → Kn μ θ n u j ≤ ε' := by
  exact BGWLeaves.LocalEstimates.Technique.Kn_tendsto_infiniteVariance_lt_two hc hne hap hDA hnl hθ hinf u hα hε'

/-- `K_n(u,j) → 0` for `σ² = ∞`, `θ = 2` (line 1881: `B'_n = h'(n)√n`, `h'` increasing, `h'(n) → ∞`:
`locallimit_remark` applied to `etaLaw μ`, `etaLaw_gauss_hprime_tendsto`). -/
theorem Kn_tendsto_theta_two_infiniteVariance (hθ : θ = 2)
    (hinf : ¬ Integrable (fun z : ℤ => (z : ℝ) ^ 2) (stepLaw μ)) (u : ℝ) {α : ℝ} (hα : 0 < α)
    {ε' : ℝ} (hε' : 0 < ε') :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ j : ℤ, |(j : ℝ)| ≤ α * normB μ θ n → Kn μ θ n u j ≤ ε' := by
  exact BGWLeaves.LocalEstimates.Technique.Kn_tendsto_theta_two_infiniteVariance hc hne hap hDA hnl hθ hinf u hα hε'

/-- **`eq:cvmoche`** (line 1869): `sup_{|j| ≤ αB_n} |Q_n(u,j) - G₀(u, j/B'_n)| → 0`, for fixed `u`.  From the three
`Kn_tendsto_*` statements and `|p₁(x) - p₁(y)| ≤ M' |x - y|` (BGW `abs_stableDensity_sub_le`), since the
difference of the arguments of `p₁` in `Q_n` and `G₀` is exactly the quantity inside `K_n` (the case split on
`σ²` and `θ` is exhaustive: finite variance forces `θ = 2`). -/
theorem eq_cvmoche (u : ℝ) {α : ℝ} (hα : 0 < α) {ε' : ℝ} (hε' : 0 < ε') :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ j : ℤ, |(j : ℝ)| ≤ α * normB μ θ n →
      |Qn μ θ n u j - G0 μ θ u ((j : ℝ) / norming (etaLaw μ) θ n)| ≤ ε' := by
  exact BGWLeaves.LocalEstimates.Technique.eq_cvmoche hc hne hap hDA hnl u hα hε'

/-- **Second half of Lemma 5.13, signed form**: for fixed `u`,
`sup_{|j| ≤ αB_n} |b_n(u,j) - G₀(u, j/B'_n)| → 0`, `j ∈ ℤ` (the printed range is `1 ≤ j ≤ αB_n`; the signed range is
needed by Lemma 6.11 and costs nothing: `bN_sub_Qn` is uniform in `j ∈ ℤ`, `eq_cvmoche` for `|j| ≤ αB_n`). -/
theorem bN_tendsto_signed (u : ℝ) {α : ℝ} (hα : 0 < α) {ε' : ℝ} (hε' : 0 < ε') :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ j : ℤ, |(j : ℝ)| ≤ α * normB μ θ n →
      |bN μ θ n u j - G0 μ θ u ((j : ℝ) / norming (etaLaw μ) θ n)| ≤ ε' := by
  exact BGWLeaves.LocalEstimates.Technique.bN_tendsto_signed hc hne hap hDA hnl u hα hε'

/-- **Lemma 5.13 (`lem:techniqueutile`)**, line 1859, as printed: for fixed `u ∈ ℝ`,
`a_n(u) → F₀(u)` and `sup_{1 ≤ j ≤ αB_n} |b_n(u,j) - G₀(u, j/B'_n)| → 0`.  The first half is `aN_tendsto`, the
second is the restriction of `bN_tendsto_signed` to `1 ≤ j`. -/
theorem lem_techniqueutile (u : ℝ) {α : ℝ} (hα : 0 < α) :
    Tendsto (fun n : ℕ => aN μ n u) atTop (𝓝 (F0 (μ 0).toReal u)) ∧
    ∀ ε' : ℝ, 0 < ε' → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ j : ℕ, 1 ≤ j → (j : ℝ) ≤ α * normB μ θ n →
      |bN μ θ n u (j : ℤ) - G0 μ θ u ((j : ℝ) / norming (etaLaw μ) θ n)| ≤ ε' := by
  have h0 : μ 0 ≠ 0 := hc.apply_zero_ne_zero hne
  have h1 : μ 0 ≠ 1 := mu0_ne_one hc hne
  refine ⟨aN_tendsto h0 h1 u, fun ε' hε' => ?_⟩
  obtain ⟨N, hN⟩ := bN_tendsto_signed hc hne hap hDA hnl u hα hε'
  refine ⟨N, fun n hn j _ hj2 => hN n hn (j : ℤ) ?_⟩
  simpa using hj2

/-- **`eq:lemtechnique2`** (line 1913), the integral of the sup: `∫_{-ε√n}^{ε√n} sup_{1 ≤ j ≤ αB_n}
|a_n(u) b_n(u,j) - F₀(u) G₀(u, j/B'_n)| du → 0`.  Uniform dominated convergence: pointwise in `u` from
`lem_techniqueutile` (+ `bN_bounded`, `F0` bounded), majorant `C(1 ∧ u^{-2})` from `aN_majorant`,
`bN_bounded`, `G0` bounded and `F0` integrable. -/
theorem eq_lemtechnique2 {α : ℝ} (hα : 0 < α) {ε : ℝ} (hε0 : 0 < ε)
    (hε1 : ε < (1 - (μ 0).toReal) / (2 * (μ 0).toReal)) :
    Tendsto (fun n : ℕ => ∫ u in (-(ε * Real.sqrt n))..(ε * Real.sqrt n),
        supJ (Finset.Icc 1 ⌊α * normB μ θ n⌋₊) fun j =>
          |aN μ n u * bN μ θ n u (j : ℤ) -
            F0 (μ 0).toReal u * G0 μ θ u ((j : ℝ) / norming (etaLaw μ) θ n)|)
      atTop (𝓝 0) := by
  exact BGWLeaves.LocalEstimates.Technique.eq_lemtechnique2 hc hne hap hDA hnl hα hε0 hε1

/-- **`eq:lemtechnique1`** (line 1904): `sup_{1 ≤ j ≤ αB_n} |μ₀ ∫_{-ε√n}^{ε√n} a_n(u) b_n(u,j) du -
μ₀ ∫_ℝ F₀(u) G₀(u, j/B'_n) du| → 0` (from `eq_lemtechnique2` and `F0 G0` integrable on `ℝ`). -/
theorem eq_lemtechnique1 {α : ℝ} (hα : 0 < α) {ε : ℝ} (hε0 : 0 < ε)
    (hε1 : ε < (1 - (μ 0).toReal) / (2 * (μ 0).toReal)) {ε' : ℝ} (hε' : 0 < ε') :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ j : ℕ, 1 ≤ j → (j : ℝ) ≤ α * normB μ θ n →
      |(μ 0).toReal * (∫ u in (-(ε * Real.sqrt n))..(ε * Real.sqrt n),
            aN μ n u * bN μ θ n u (j : ℤ)) -
        (μ 0).toReal * ∫ u : ℝ, F0 (μ 0).toReal u * G0 μ θ u ((j : ℝ) / norming (etaLaw μ) θ n)| ≤ ε' := by
  exact BGWLeaves.LocalEstimates.Technique.eq_lemtechnique1 hc hne hap hDA hnl hα hε0 hε1 hε'

/-- **`eq:cvdd`** (line 1894): `sup_{1 ≤ j ≤ αB_n} |(j/B'_n) ∫_{-ε√n}^{ε√n} (n/r_n(u)) a_n(u) b_n(u,j) du -
(j/B'_n) μ₀ ∫_{-ε√n}^{ε√n} a_n(u) b_n(u,j) du| → 0` (dominated convergence: `n/r_n(u) → μ₀` uniformly on
`|u| ≤ ε√n`, majorant `C α' (1 ∧ u^{-2})`; `j ≤ αB_n ≤ α'B'_n`).  The `o(1)` in the printed limits of the integral
in `eq:retenir` (`eq_retenir`) is absorbed: the integrand is `≤ C` on an interval of length `o(1)`. -/
theorem eq_cvdd {α : ℝ} (hα : 0 < α) {ε : ℝ} (hε0 : 0 < ε)
    (hε1 : ε < (1 - (μ 0).toReal) / (2 * (μ 0).toReal)) {ε' : ℝ} (hε' : 0 < ε') :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ j : ℕ, 1 ≤ j → (j : ℝ) ≤ α * normB μ θ n →
      |((j : ℝ) / norming (etaLaw μ) θ n) * (∫ u in (-(ε * Real.sqrt n))..(ε * Real.sqrt n),
            (n : ℝ) / (rN μ n u : ℝ) * aN μ n u * bN μ θ n u (j : ℤ)) -
        ((j : ℝ) / norming (etaLaw μ) θ n) * (μ 0).toReal *
          ∫ u in (-(ε * Real.sqrt n))..(ε * Real.sqrt n), aN μ n u * bN μ θ n u (j : ℤ)| ≤ ε' := by
  exact BGWLeaves.LocalEstimates.Technique.eq_cvdd hc hne hap hDA hnl hα hε0 hε1 hε'

/-- **`eq:lemtechnique0` for `σ² = ∞`**, as printed (line 1900; `eq:lemtechnique3`, `eq:lemtechnique4`):
`sup_{1 ≤ j ≤ αB_n} |μ₀ ∫_{-ε√n}^{ε√n} a_n(u) b_n(u,j) du - c^{1/θ} p₁(-j/B_{n/μ₀})| → 0`.
Here `G₀(u,x) = c^{1/θ} p₁(-c^{1/θ} x)` does not depend on `u`, `μ₀ ∫ F₀ = 1`, and
`B'_n/B_{n/μ₀} → c^{1/θ}` (`normBp_div_normB_infVar`) with `j/B'_n ≤ α'` and Lipschitz `p₁`. -/
theorem eq_lemtechnique0_infVar
    (hinf : ¬ Integrable (fun z : ℤ => (z : ℝ) ^ 2) (stepLaw μ))
    {α : ℝ} (hα : 0 < α) {ε : ℝ} (hε0 : 0 < ε)
    (hε1 : ε < (1 - (μ 0).toReal) / (2 * (μ 0).toReal)) {ε' : ℝ} (hε' : 0 < ε') :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ j : ℕ, 1 ≤ j → (j : ℝ) ≤ α * normB μ θ n →
      |(μ 0).toReal * (∫ u in (-(ε * Real.sqrt n))..(ε * Real.sqrt n),
            aN μ n u * bN μ θ n u (j : ℤ)) -
        cC μ ^ (1 / θ) * Scalar.stableDensity θ (-((j : ℝ) / normB μ θ ((n : ℝ) / (μ 0).toReal)))| ≤ ε' := by
  exact BGWLeaves.LocalEstimates.Technique.eq_lemtechnique0_infVar hc hne hap hDA hnl hinf hα hε0 hε1 hε'

/-- **`eq:lemtechnique0` for `σ² < ∞`, CORRECTED** (replaces the printed `c^{1/2} p₁(-j/B_{n/μ₀})`,
correction 4 of `FORMALIZATION_REPORT.md`): with
`r = √μ₀ σ'/σ` (`σ² = variance (stepLaw μ)`, `σ'² = variance (etaLaw μ)`),
`sup_{1 ≤ j ≤ αB_n} |μ₀ ∫_{-ε√n}^{ε√n} a_n(u) b_n(u,j) du - r p₁(-j/B_{n/μ₀})| → 0`.
The Gaussian convolution is `gaussian_convolution_identity`: `μ₀ ∫ F₀ G₀ = r p₁(r x)` at `x = j/B'_n`,
and `r x = j/B_{n/μ₀} + o(1)` since `B'_n = σ'√(n/2)`.  The printed claim is false in finite variance (`r < √c`,
`r_lt_sqrt_c`); the final limit of 5.4(ii) survives because the prefactor `j/B'_n` then cancels `r`. -/
theorem eq_lemtechnique0_finVar_corrected
    (hfin : Integrable (fun z : ℤ => (z : ℝ) ^ 2) (stepLaw μ))
    {α : ℝ} (hα : 0 < α) {ε : ℝ} (hε0 : 0 < ε)
    (hε1 : ε < (1 - (μ 0).toReal) / (2 * (μ 0).toReal)) {ε' : ℝ} (hε' : 0 < ε') :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ j : ℕ, 1 ≤ j → (j : ℝ) ≤ α * normB μ θ n →
      |(μ 0).toReal * (∫ u in (-(ε * Real.sqrt n))..(ε * Real.sqrt n),
            aN μ n u * bN μ θ n u (j : ℤ)) -
        Real.sqrt (μ 0).toReal * Real.sqrt (variance (etaLaw μ)) / Real.sqrt (variance (stepLaw μ)) *
          Scalar.stableDensity θ (-((j : ℝ) / normB μ θ ((n : ℝ) / (μ 0).toReal)))| ≤ ε' := by
  exact BGWLeaves.LocalEstimates.Technique.eq_lemtechnique0_finVar_corrected hc hne hap hDA hnl hfin hα hε0 hε1 hε'

/-- The finite-variance case is `θ = 2` and `G₀` is `G0fv`: `G0 μ 2 u x = G0fv μ₀ σ' x u`
(`c^{1/2} = √c`, `c^{3/2} = c √c`, `stableDensity_two`).  Connects the printed `G₀` with the Gaussian
identity `gaussian_convolution_identity`. -/
theorem G0_eq_G0fv
    (hfin : Integrable (fun z : ℤ => (z : ℝ) ^ 2) (stepLaw μ)) (hθ : θ = 2) (u x : ℝ) :
    G0 μ θ u x = G0fv (μ 0).toReal (Real.sqrt (variance (etaLaw μ))) x u := by
  have hle : (μ 0).toReal ≤ 1 := by
    have := ENNReal.toReal_mono ENNReal.one_ne_top (PMF.coe_le_one μ 0)
    simpa using this
  have hc0 : 0 ≤ cC μ := div_nonneg ENNReal.toReal_nonneg (sub_nonneg.2 hle)
  subst hθ
  unfold G0 finVarShift G0fv
  simp only [hfin, ite_true]
  rw [stableDensity_two]
  have hs : cC μ ^ (1 / 2 : ℝ) = Real.sqrt (cC μ) := by
    rw [Real.sqrt_eq_rpow]
  have h32 : cC μ ^ (3 / 2 : ℝ) = cC μ * Real.sqrt (cC μ) := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add' hc0 (by norm_num), Real.rpow_one, hs]
  rw [hs, h32]
  unfold cC
  rfl

/-- **Lemma 5.4(ii) (`lem:technical`, line 1412)**: for `α > 0`,
`lim_n sup_{1 ≤ j ≤ αB_n} |n ψ_n(j) - q_1(j/B_{n/μ₀})| = 0` (`q_1(x) = x p₁(-x)`).  Hypotheses: `(H_θ)` and
the non-lattice assumption of §5 (`hnl`); without it the statement is false (lattice case).
Proof: `eq_psi`, `eq_retenir`, `eq_cvdd`, `eq_lemtechnique1`, then `eq_lemtechnique0_infVar` or
`eq_lemtechnique0_finVar_corrected`, and the ratio `B'_n/B_{n/μ₀}` (`normBp_div_normB_infVar` / `_finVar`) which cancels
against the prefactor `j/B'_n ≤ α'`. -/
theorem lem_technical_ii {α : ℝ} (hα : 0 < α) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ j : ℕ, 1 ≤ j → (j : ℝ) ≤ α * normB μ θ n →
      |(n : ℝ) * (psi μ n j).toReal - qKernel θ 1 ((j : ℝ) / normB μ θ ((n : ℝ) / (μ 0).toReal))| ≤ ε := by
  exact BGWLeaves.LocalEstimates.Technique.lem_technical_ii hc hne hap hDA hnl hα hε

/-- **Lemma 5.4 (`lem:technical`) as printed**: both parts, under `(H_θ)` and the non-lattice assumption of §5.
Assembled from `lem_technical_i` (which does not use `hnl`) and `lem_technical_ii`. -/
theorem lem_technical {α : ℝ} (hα : 0 < α) :
    (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ j : ℕ, 1 ≤ j → (j : ℝ) ≤ α * normB μ θ n →
      |(psiStar μ n j).toReal - sizeTailKernel θ 1 ((j : ℝ) / normB μ θ ((n : ℝ) / (μ 0).toReal))| ≤ ε) ∧
    (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ j : ℕ, 1 ≤ j → (j : ℝ) ≤ α * normB μ θ n →
      |(n : ℝ) * (psi μ n j).toReal - qKernel θ 1 ((j : ℝ) / normB μ θ ((n : ℝ) / (μ 0).toReal))| ≤ ε) :=
  ⟨fun _ hε => lem_technical_i hc hne hap hDA hα hε, fun _ hε => lem_technical_ii hc hne hap hDA hnl hα hε⟩

end Htheta5

/-! ## 9. Lemma 6.11 (`lem:technic3`)

`χ_n(j) = P_j[W_{T_n} = -1]` (`chi`, `ℝ≥0∞`-valued; its `.toReal`).  Statement for **signed** `j`, `|j| ≤ αB_n`.  Hypotheses: `(H_θ)` and
`hnl` (the printed proof uses the local limit theorem for `W'`, hence `Y` non-lattice).  The
intermediate statements follow the printed proof (lines 2204-2236). -/

section Chi

variable {μ : PMF ℕ} {θ : ℝ} (hc : IsCritical μ) (hne : μ 1 ≠ 1) (hap : Aperiodic μ)
  (hDA : ∃ b, StableDomain μ θ b) (hnl : ¬ IsLatticeLaw (etaLaw μ))
include hc hne hap hDA hnl

/-- Exact decomposition at the last marked step (line 2208-2216): for `n ≥ 1` and **every** `j ∈ ℤ`,
`χ_n(j) = μ₀ ∑_{q ≥ 0} P[S_{n-1+q} = n-1] P[W'_q = n-1-j]` (the time of the `n`-th mark is `T_n = n + q`; the last step is
the mark; `eq:LambdaUtile` for `p = n-1+q` marks `n-1`, endpoint `-j`).  `pi_leafMarkedBridges` has
`j ≥ 1` natural; this is its signed, infinite-walk form.  The series is a sum of probabilities. -/
theorem chi_eq_tsum {n : ℕ} (hn : 1 ≤ n) (j : ℤ) :
    (chi μ n j).toReal =
      (μ 0).toReal * ∑' q : ℕ, binomProb (μ 0).toReal (n - 1 + q) (n - 1) *
        intWalkProb (etaLaw μ) q ((n : ℤ) - 1 - j) := by
  exact BGWLeaves.LocalEstimates.Chi.chi_eq_tsum hc hne hap hDA hnl hn j


/-- Localization (line 2208): for `ε > 0`, `|χ_n(j) - μ₀ ∑_{|k - n/μ₀| ≤ εn} P[S_{k-1} = n-1] P[W'_{k-n} = n-1-j]| ≤ C e^{-c√n}`,
uniformly in `j ∈ ℤ` (the error is `P[|T_n - n/μ₀| > εn] ≤ P[|T_n/n - 1/μ₀| > n^{-1/4}]` for large `n`, i.e. Lemma 6.2(i),
`BGWLeaves.lem_CVf2_i`).  The hypothesis `hε1 : ε < 1/μ₀` makes the lower
limit of the window positive, so that `toNat` is the identity (for `ε > 1/μ₀` and `n = 1` the window starts at
`k = 0` and a spurious term appears). -/
theorem chi_window {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1 / (μ 0).toReal) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ n : ℕ, 1 ≤ n → ∀ j : ℤ,
      |(chi μ n j).toReal - (μ 0).toReal * ∑ k ∈ Finset.Icc (⌈(n : ℝ) / (μ 0).toReal - ε * n⌉.toNat)
          ⌊(n : ℝ) / (μ 0).toReal + ε * n⌋₊,
        binomProb (μ 0).toReal (k - 1) (n - 1) * intWalkProb (etaLaw μ) (k - n) ((n : ℤ) - 1 - j)| ≤
        C * Real.exp (-c * (n : ℝ) ^ (1 / 2 : ℝ)) := by
  exact BGWLeaves.LocalEstimates.Chi.chi_window hc hne hap hDA hnl hε hε1

/-- `B'_n P_j[W_{T_n} = -1] = μ₀ ∫ ã_n(u) b_n(u, j+1) du + oe_{1/2}(n)` (line 2220), exact form of the
sum-to-integral step (`k = r_n(u)`, `ã_n(u) = √n P[S_{r_n(u)-1} = n-1]`, `b_n(u, j+1)` signed): for `n ≥ 1`
with `B'_n > 0`, `B'_n μ₀ ∑_{k ∈ window} P[S_{k-1} = n-1] P[W'_{k-n} = n-1-j] =
μ₀ ∫_{u₁}^{u₂} ã_n(u) b_n(u, j+1) du` with the exact limits of `eq_retenir`.  `ε < 1/μ₀` makes the lower limit positive (so that `toNat` is the identity). -/
theorem chi_retenir {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1 / (μ 0).toReal) {n : ℕ} (hn : 1 ≤ n) (j : ℤ)
    (hB : 0 < norming (etaLaw μ) θ n) :
    norming (etaLaw μ) θ n * ((μ 0).toReal * ∑ k ∈ Finset.Icc (⌈(n : ℝ) / (μ 0).toReal - ε * n⌉.toNat)
          ⌊(n : ℝ) / (μ 0).toReal + ε * n⌋₊,
        binomProb (μ 0).toReal (k - 1) (n - 1) * intWalkProb (etaLaw μ) (k - n) ((n : ℤ) - 1 - j)) =
      (μ 0).toReal * ∫ u in ((⌈(n : ℝ) / (μ 0).toReal - ε * n⌉ - (n : ℝ) / (μ 0).toReal) / Real.sqrt n)..
            ((⌊(n : ℝ) / (μ 0).toReal + ε * n⌋ + 1 - (n : ℝ) / (μ 0).toReal) / Real.sqrt n),
          Real.sqrt n * binomProb (μ 0).toReal (rN μ n u - 1) (n - 1) * bN μ θ n u (j + 1) := by
  exact BGWLeaves.LocalEstimates.Chi.chi_retenir hc hne hap hDA hnl hε hε1 hn j hB

/-- The printed intermediate for `σ² = ∞` (line 2232: "`sup_{|j| ≤ αB_n} |B'_n P_j[W_{T_n} = -1] - c^{1/θ} p₁(-j/B_{n/μ₀})| → 0`"),
the signed analogue of `eq:lemtechnique0` with `b_n(u, j+1)` (`bN_tendsto_signed` for `|j+1| ≤ 2αB_n`, `aTilde_eq`,
`aN_majorant`, `bN_bounded`, `eq_lemtechnique2`-type domination). -/
theorem chi_Bprime_infVar (hinf : ¬ Integrable (fun z : ℤ => (z : ℝ) ^ 2) (stepLaw μ))
    {α : ℝ} (hα : 0 < α) {ε' : ℝ} (hε' : 0 < ε') :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ j : ℤ, |(j : ℝ)| ≤ α * normB μ θ n →
      |norming (etaLaw μ) θ n * (chi μ n j).toReal -
        cC μ ^ (1 / θ) * Scalar.stableDensity θ (-((j : ℝ) / normB μ θ ((n : ℝ) / (μ 0).toReal)))| ≤ ε' := by
  exact BGWLeaves.LocalEstimates.Chi.chi_Bprime_infVar hc hne hap hDA hnl hinf hα hε'

/-- The same for `σ² < ∞`, **CORRECTED** (the printed intermediate has `c^{1/2}`; it must be `r = √μ₀ σ'/σ`,
correction 4 of `FORMALIZATION_REPORT.md`, lines 2238-2240). -/
theorem chi_Bprime_finVar_corrected (hfin : Integrable (fun z : ℤ => (z : ℝ) ^ 2) (stepLaw μ))
    {α : ℝ} (hα : 0 < α) {ε' : ℝ} (hε' : 0 < ε') :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ j : ℤ, |(j : ℝ)| ≤ α * normB μ θ n →
      |norming (etaLaw μ) θ n * (chi μ n j).toReal -
        Real.sqrt (μ 0).toReal * Real.sqrt (variance (etaLaw μ)) / Real.sqrt (variance (stepLaw μ)) *
          Scalar.stableDensity θ (-((j : ℝ) / normB μ θ ((n : ℝ) / (μ 0).toReal)))| ≤ ε' := by
  exact BGWLeaves.LocalEstimates.Chi.chi_Bprime_finVar_corrected hc hne hap hDA hnl hfin hα hε'

/-- **Lemma 6.11 (`lem:technic3`)**, line 2196: for every `α > 0`,
`lim_n sup_{|j| ≤ αB_n} |B_{⌊n/μ₀⌋} χ_n(j) - p₁(-j/B_{⌊n/μ₀⌋})| = 0`, `j ∈ ℤ` **signed** ("`j` is allowed to take
negative values").  `B_{⌊n/μ₀⌋} = normB μ θ (n/μ₀)`.  Proof: `chi_window`, `chi_retenir`, then
`chi_Bprime_infVar` / `_finVar_corrected` and the norming ratio (`normBp_div_normB_infVar` / `_finVar`),
which turns `B'_n χ_n(j)` into `B_{n/μ₀} χ_n(j)`. -/
theorem lem_technic3 {α : ℝ} (hα : 0 < α) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ j : ℤ, |(j : ℝ)| ≤ α * normB μ θ n →
      |normB μ θ ((n : ℝ) / (μ 0).toReal) * (chi μ n j).toReal -
        Scalar.stableDensity θ (-((j : ℝ) / normB μ θ ((n : ℝ) / (μ 0).toReal)))| ≤ ε := by
  exact BGWLeaves.LocalEstimates.Chi.lem_technic3 hc hne hap hDA hnl hα hε

/-- The remark after 6.11 (line 2200, "`χ_n(0) ∼ p₁(0)/B_{n/μ₀}`"): the denominator asymptotic, from `lem_technic3`
at `j = 0`, `α = 1`, and `p₁(0) > 0`. -/
theorem chi_zero_asymp :
    Tendsto (fun n : ℕ => normB μ θ ((n : ℝ) / (μ 0).toReal) * (chi μ n 0).toReal /
      Scalar.stableDensity θ 0) atTop (𝓝 1) := by
  obtain ⟨b, hb⟩ := hDA
  have hθ := hb.alpha_mem
  have hp : 0 < Scalar.stableDensity θ 0 := Scalar.stableDensity_zero_pos hθ
  have hpos := normB_pos_eventually hc hne hap ⟨b, hb⟩
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 hpos
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := lem_technic3 hc hne hap ⟨b, hb⟩ hnl (α := 1) one_pos (ε := ε / 2 * Scalar.stableDensity θ 0)
    (by positivity)
  refine ⟨max N N₀, fun n hn => ?_⟩
  have hBn : 0 < norming (stepLaw μ) θ n := hN₀ n (le_trans (le_max_right _ _) hn)
  have h := hN n (le_trans (le_max_left _ _) hn) 0 (by
    simp only [Int.cast_zero, abs_zero, one_mul]
    rw [normB_natCast]
    exact hBn.le)
  simp only [Int.cast_zero, zero_div, neg_zero] at h
  set x := normB μ θ ((n : ℝ) / (μ 0).toReal) * (chi μ n 0).toReal with hx
  set p := Scalar.stableDensity θ 0 with hpdef
  have e : x / p - 1 = (x - p) / p := by field_simp
  rw [Real.dist_eq, e, abs_div, abs_of_pos hp, div_lt_iff₀ hp]
  have : ε / 2 * p < ε * p := by nlinarith
  linarith

end Chi

end BGWLeaves
