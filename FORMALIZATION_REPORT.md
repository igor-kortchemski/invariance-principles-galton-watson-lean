# Correspondence record

This record maps the results of the paper to the Lean declarations that prove
them, and lists the corrections, the conventions and the differences of route.
The README gives the overview; [verification/](verification/README.md) gives
the checks.

- **Paper:** I. Kortchemski, *Invariance principles for Galton–Watson trees
  conditioned on the number of leaves*, Stochastic Process. Appl. 122 (2012)
  3126–3172, [doi:10.1016/j.spa.2012.05.013](https://doi.org/10.1016/j.spa.2012.05.013).
  The formalization follows [arXiv:1110.2163v4](https://arxiv.org/abs/1110.2163v4),
  whose numbering of results is the same as the journal's.
- **Scope:** every numbered theorem, proposition, lemma, corollary and remark
  with mathematical content, the claims of the Introduction, and the
  unnumbered claims used by the proofs.
- **Lean:** Lean 4.35.0, Mathlib v4.35.0. The declarations named below are in
  the namespace `BGWLeaves`, those of the files under
  `StableAnalysis` in `BGWLeaves.StableAnalysis`; the files listed are the statement
  files, whose proofs are in the modules of the folder of the same name.
- **Axioms:** every declaration of `BGWLeaves` and of the vendored packages
  depends only on `propext`, `Classical.choice` and `Quot.sound`
  ([scripts/AxiomAudit.lean](scripts/AxiomAudit.lean)).

## Conventions

- **Offspring law.** `μ : PMF ℕ`, critical (`IsCritical μ`), not the Dirac mass
  at 1 (`μ 1 ≠ 1`), aperiodic where the paper assumes it (`Aperiodic μ`), and
  in the domain of attraction of a stable law of index `θ ∈ (1,2]`
  (`StableDomain`, `IsRealStableAttracted`).
- **Norming.** The functional limit theorems are stated for any norming
  sequence `B` of the step law (`IsRealStableAttracted (realOffspringStepLaw μ) θ B`),
  with corollaries for the norming of Theorem 1.10 as corrected below
  (`norming (stepLaw μ) θ`). The laws of `X`, `X^exc` and `H^exc` are those of
  the paper: Laplace exponent `λ^θ`.
- **Conditioned laws.** `leafTreeLaw μ n` is the Galton–Watson law conditioned
  on `λ(τ) = n`, stated along any sequence `q k → ∞` of values with
  `P[λ = q k] > 0` (`LeafAdmissible`); the rescaled Łukasiewicz path, contour
  and height function are `codingTriple B`, valued in Skorokhod space and
  continuous functions; the limit `(X^exc, H^exc, H^exc)` is `excTripleLaw θ`
  ([BGWLeaves/Coding/Defs.lean](BGWLeaves/Coding/Defs.lean)).
- **Non-lattice assumption.** Section 5 of the paper assumes that
  `supp μ ∖ {0}` is non-lattice "to avoid technical issues". The statements of
  Lemma 5.8, Theorem 5.9, Remark 5.10, Theorem 6.1, Theorem 7.1(i) and the GH
  and GHP claims carry it as `hnl : ¬ IsLatticeLaw (etaLaw μ)`. Introduction
  (II) is also proved without it, in the paper's generality
  (`intro_II_general`), and so is Theorem 8.1(II).
- **Trees.** Plane trees, the Bienaymé law, Skorokhod space, the stable
  process, its excursion measure and height process, the Vervaat transform and
  the stable bridge come from the vendored
  [Bienaymé–Galton–Watson trees](Vendor/VENDORED.md) library.

## Result correspondence

| Paper | Lean declarations | File | Status |
| --- | --- | --- | --- |
| Introduction (I) | `thm_ltn_i`, `thm_ltn_ii` | [LeafMass](BGWLeaves/LeafMass.lean) | proved |
| Introduction (II) | `intro_II_general`; `intro_II`, `intro_II_canonical` | [LeafLimitsGeneral](BGWLeaves/LeafLimitsGeneral.lean), [LeafLimits](BGWLeaves/LeafLimits.lean) | proved (general form without `hnl`) |
| Introduction, maximum degree | `thm_max_i`, `thm_max_two_zero`, `thm_max_ii` | [MaxDegreeLimit](BGWLeaves/MaxDegreeLimit.lean), [MaxDegree](BGWLeaves/MaxDegree.lean) | proved |
| Introduction, GHP claim | `intro_GHP_leaf`, `cvG_GHP` | [LeafLimits](BGWLeaves/LeafLimits.lean) | proved, under `hnl`; leaf and vertex measures |
| Introduction, codings | `intro_enc_lukasiewicz_end`, `intro_enc_lukasiewicz_injective` | [Coding](BGWLeaves/Coding.lean) | proved for `W`; the claims for `C`, `H` are not stated |
| Proposition 1.4 | `stoppedWord_atom`, `stoppedWord_none`, `firstHit_law`, `firstHit_leaves_law` | [Passage](BGWLeaves/Passage.lean) | proved |
| Proposition 1.5 | `prop_Hmes` | [Coding](BGWLeaves/Coding.lean) | proved |
| Cyclic lemma, (1.1) | `natCast_mul_forestLeafWeight`; `kemperman_marked`, `kemperman_unmarked`, `eq_f` | [MarkedForest](BGWLeaves/MarkedForest.lean), [Passage](BGWLeaves/Passage.lean) | proved |
| Proposition 1.6 | `prop_K`, `pi_leafMarkedBridges`, `pi_bienaymeLaw_forestEvent` | [ForestLaw](BGWLeaves/ForestLaw.lean) | proved |
| Proposition 1.7 | `slow_rpow_mul_tendsto_atTop`, `slow_rpow_neg_mul_tendsto_zero`, `slow_potter_nat`, `slow_representation` | [StableAnalysis](BGWLeaves/StableAnalysis.lean) | proved |
| Remark 1.9 | `nonLattice_stepLaw` | [StableAnalysis/Defs](BGWLeaves/StableAnalysis/Defs.lean) | proved |
| Theorem 1.10 | `locallimit_i`, `locallimit_ii`, `locallimit_iii`, `llt_abstract` | [StableAnalysis](BGWLeaves/StableAnalysis.lean), [Consequences](BGWLeaves/StableAnalysis/Consequences.lean) | proved, corrected norming |
| Lemma 1.11, Remark 1.12 | `lem_locallimit`, `sizeProb_asymp`, `sizeTail_asymp`, `sizeProb_lattice_asymp` | [StableAnalysis](BGWLeaves/StableAnalysis.lean), [Consequences](BGWLeaves/StableAnalysis/Consequences.lean) | proved |
| Lemma 2.2 | `lem_phi_i`, `lem_phi_ii` | [LeafConcentration](BGWLeaves/LeafConcentration.lean) | proved |
| Remark 2.4 | `IsOe.tail` | [LeafConcentration](BGWLeaves/LeafConcentration.lean) | proved |
| Lemma 2.5, Corollary 2.6, Lemma 2.7 | `lem_GdesDev_walk`, `lem_GdesDev_tree`, `cor_GD2mieux`, `lem_GdesDev2_i`, `lem_GdesDev2_ii` | [LeafConcentration](BGWLeaves/LeafConcentration.lean) | proved |
| Theorem 3.1 | `thm_ltn_i`, `thm_ltn_ii`, `ltn_i_arith`, `thm_ltn_finiteVariance` | [LeafMass](BGWLeaves/LeafMass.lean) | proved, lattice case included |
| Corollary 3.3 | `cor_Lambda`, `cor_Lambda_arith` | [LeafMass](BGWLeaves/LeafMass.lean) | proved |
| Lemma 3.4, Theorem 3.5 | `lem_hhp`, `strongLLT`, `finiteVariance_norming_ratio_eta` | [StableAnalysis](BGWLeaves/StableAnalysis.lean) | proved |
| Remark 3.6 | `rem_periodic_ltn_i`, `rem_periodic_ltn_ii` | [LeafMass](BGWLeaves/LeafMass.lean) | proved |
| Theorem 4.1, Remark 4.2 | `thm_cv1`, `thm_cv1_printed`, `rem_cv1`, `height_exc_endpoints` | [ClassicalLimits](BGWLeaves/ClassicalLimits.lean) | proved |
| Lemma 4.3, Proposition 4.4 | `lemma_passage`, `prop_passage_i`, `prop_passage_ii` | [Conditioning](BGWLeaves/Conditioning.lean) | proved |
| Theorem 4.5, Remark 4.6 | `thm_inv1`, `rem_inv1_finiteVariance` | [LeafLimits](BGWLeaves/LeafLimits.lean) | proved |
| Section 5.1 | `sec51_laplace`, `sec51_scaling`, `sec51_density`, `sec51_exc_endpoints`, `sec51_two_exc` | [ClassicalLimits](BGWLeaves/ClassicalLimits.lean) | proved |
| Theorem 5.1 | `thm_cvW` | [ClassicalLimits](BGWLeaves/ClassicalLimits.lean) | proved, precise form |
| Proposition 5.2 | `prop_abscon` | [Conditioning](BGWLeaves/Conditioning.lean) | proved |
| Proposition 5.3 | `prop_Gamma`, `gammaA_eq_paper` | [ClassicalLimits](BGWLeaves/ClassicalLimits.lean) | proved, precise form |
| Lemma 5.4, Corollary 5.5, Lemma 5.6 | `lem_technical_i`, `lem_technical_ii`, `cor_tejhnique_i`, `cor_tejhnique_ii`, `lem_CVf_i`, `lem_CVf_ii` | [LocalEstimates](BGWLeaves/LocalEstimates.lean), [Conditioning](BGWLeaves/Conditioning.lean) | proved |
| Lemma 5.7 | `lem_CVproba`, `lem_CVproba_pair` | [ClassicalLimits](BGWLeaves/ClassicalLimits.lean) | proved, precise form |
| Lemma 5.8 | `lem_absolue` | [LeafLimits](BGWLeaves/LeafLimits.lean) | proved, under `hnl` |
| Theorem 5.9, Remark 5.10, GH claim | `thm_cvG_i`, `thm_cvG_ii`, `rem_changement`, `cvG_GH` | [LeafLimits](BGWLeaves/LeafLimits.lean) | proved, under `hnl` |
| Lemmas 5.11–5.13 | `lem_technical2`, `lem_g`, `lem_techniqueutile` | [LocalEstimates](BGWLeaves/LocalEstimates.lean) | proved |
| Theorem 6.1 | `thm_cvW3`, `tendsto_bridgeWalkPath` | [LeafLimits](BGWLeaves/LeafLimits.lean) | proved, under `hnl` |
| Lemma 6.2 | `lem_CVf2_i`, `lem_CVf2_ii` | [Vervaat](BGWLeaves/Vervaat.lean), [ClassicalLimits](BGWLeaves/ClassicalLimits.lean) | proved |
| Lemma 6.4, Proposition 6.5 | `lem_cool_i`, `lem_cool_ii`, `prop_vervaatdiscrete` | [Vervaat](BGWLeaves/Vervaat.lean) | proved |
| Definition 6.6, Corollary 6.7 | `def_vervaatC`, `cor_vervaatC` | [ClassicalLimits](BGWLeaves/ClassicalLimits.lean), [LeafLimits](BGWLeaves/LeafLimits.lean) | proved |
| Proposition 6.8 | `prop_timereversal` | [Vervaat](BGWLeaves/Vervaat.lean) | proved |
| Proposition 6.9 | `prop_bridge_i`, `prop_bridge_ii` | [ClassicalLimits](BGWLeaves/ClassicalLimits.lean) | proved |
| Lemmas 6.10, 6.11 | `lem_absolueC2`, `lem_technic3` | [Conditioning](BGWLeaves/Conditioning.lean), [LocalEstimates](BGWLeaves/LocalEstimates.lean) | proved |
| Theorem 7.1 | `thm_max_i`, `thm_max_i_pos`, `thm_max_two_zero`, `thm_max_ii` | [MaxDegreeLimit](BGWLeaves/MaxDegreeLimit.lean), [MaxDegree](BGWLeaves/MaxDegree.lean) | proved; (i) under `hnl` |
| Lemma 7.2 | `lem_MM` | [MaxDegree](BGWLeaves/MaxDegree.lean) | proved |
| Remark 7.3 | `rem_uniformtree_iff`, `rem_uniformtree_tail_upper`, `rem_uniformtree_window` | [Vervaat](BGWLeaves/Vervaat.lean), [MaxDegree](BGWLeaves/MaxDegree.lean) | proved, precise form |
| Theorem 8.1(I) | `thm81_corrected_general`, `thm81_corrected`, `thm81_infiniteVariance_A_finite`, `thm81_infiniteVariance_A_cofinite` | [GeneralAInf](BGWLeaves/GeneralAInf.lean) | proved, corrected |
| Theorem 8.1(II) | `thm_general_II`, `thm_general_II_canonical` | [GeneralAFunctional](BGWLeaves/GeneralAFunctional.lean) | proved; `A` finite or cofinite in infinite variance, as in the paper |

Definitions 1.1–1.3, 1.8, 2.1, 2.3 and 6.3 are Lean definitions (in the vendored
library for trees, in the `Defs` modules here otherwise), with proved
identifications where the encoding differs. Remark 3.2 only cites the
literature; its finite-variance claim is `thm_ltn_finiteVariance`.

## Corrections to the paper

Five errors were found; the statements formalized are the corrected ones, and
the printed claims are not counted as proved. Locations are those of the journal
version.

1. **Theorem 1.10, `σ² = ∞`, `θ < 2` (p. 3134).** The constant
   `Γ(1−θ)^{1/θ}` has a negative base; the correct norming uses
   `(−Γ(1−θ))^{1/θ}` (`norming`; `printedConstant_neg`, `negGamma_eq`).
2. **Theorem 1.10, `σ² = ∞`, `θ = 2` (p. 3134).** The printed norming
   normalizes to the standard Gaussian law while `X₁` has variance 2; the
   correct one has a factor `1/2` under the square root
   (`printedNorming_gauss`).
3. **Proof of Lemma 5.4(ii), choice of `α′` (p. 3157).** The inequality
   `αB_n ≤ α′B′_n` is taken from Lemma 3.4, which assumes `σ² = ∞`, and can
   fail for finite variance; any `α′ > α lim B_n/B′_n` works.
4. **Proofs of Lemmas 5.4(ii) and 6.11, `σ² < ∞` (pp. 3158–3159, 3164).**
   The constant `c^{1/2}` should be `√μ₀ σ′/σ`, the limit of `B′_n/B_{n/μ₀}`;
   the two printed errors cancel and the lemmas hold
   (`finiteVariance_norming_ratio_eta`, `eq_lemtechnique0_finVar_corrected`).
5. **Theorem 8.1(I) (p. 3170).** The factor `gcd(b−1,d)` is wrong when
   `A ≠ {0}`: the correct factor is `e = gcd((supp μ ∩ A) ∪ {k−1 : k ∈ supp μ ∖ A})`
   (`arithFactor`), along `n ≡ 1 mod e`. For `μ = (0.6, 0.2, 0, 0.1, 0, 0.1)`
   and `A = {0,1}` the printed constant is twice the true one.

Smaller points of exposition (index conventions, unstated measurability, the
two forms of the non-lattice condition in Sections 5 and 6) are not listed
here; they do not change any statement.

## Differences of route

- **Proposition 1.6.** The product law of a forest is identified with a
  weighted sum over words, and the marked cyclic lemma replaces Proposition 1.4
  with (1.1) at the level of weights; Proposition 1.4 is proved separately.
- **Theorem 3.1(ii).** Proved through the walk indexed by leaves, whose step
  law is attracted with the norming `B_{⌊m/μ₀⌋}`, instead of the localization
  of the paper with Theorem 3.5 (which is proved and not used there). The
  lattice case, omitted in the paper, is proved.
- **Theorems 5.9, 6.1 and Introduction (II).** The convergence on `[0,1]` is
  obtained from the convergence on `[0,a]`, `a < 1`, and a control of the
  oscillation near the end point, through an approximation theorem of the
  vendored library. The joint law of the three coding paths, which the paper
  states but does not derive from the marginal limits, is proved.
- **Theorem 8.1.** Part (I) is proved by a walk with marks on the vertices with
  degree in `A`, for every variance and every `A` with `μ(A) > 0`. Part (II) is
  proved for every `A`, without the finiteness assumption on `A` in the
  infinite-variance case.

## Not formalized

- The claims of the Introduction that the contour and the height function each
  determine the tree.
- Historical and bibliographic remarks, and the application to dissections
  cited from other papers.
