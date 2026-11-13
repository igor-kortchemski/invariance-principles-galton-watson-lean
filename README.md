# Invariance principles for Galton–Watson trees conditioned on the number of leaves

[![Lean build and axiom audit](https://github.com/igor-kortchemski/invariance-principles-galton-watson-lean/actions/workflows/lean.yml/badge.svg?branch=main)](https://github.com/igor-kortchemski/invariance-principles-galton-watson-lean/actions/workflows/lean.yml?query=branch%3Amain)
[![Comparator and full Palomar preflight](https://github.com/igor-kortchemski/invariance-principles-galton-watson-lean/actions/workflows/palomar-full.yml/badge.svg?branch=main)](https://github.com/igor-kortchemski/invariance-principles-galton-watson-lean/actions/workflows/palomar-full.yml?query=branch%3Amain)
Comparison, kernel replay and exact-commit verification evidence is recorded
in [verification/](verification/README.md).
[Linux Comparator runs](https://github.com/igor-kortchemski/invariance-principles-galton-watson-lean/actions/workflows/comparator.yml)
and [full Palomar preflight runs](https://github.com/igor-kortchemski/invariance-principles-galton-watson-lean/actions/workflows/palomar-full.yml)
identify the exact commits they check.

Lean 4 and Mathlib formalization of *Invariance principles for Galton–Watson
trees conditioned on the number of leaves* by Igor Kortchemski
([arXiv:1110.2163v4](https://arxiv.org/abs/1110.2163v4)), published in
*Stochastic Processes and their Applications* 122 (2012) 3126–3172,
[doi:10.1016/j.spa.2012.05.013](https://doi.org/10.1016/j.spa.2012.05.013).
**Every numbered theorem, proposition, lemma and corollary of the paper is
proved, Theorems 1.10 and 8.1(I) in corrected form, using only the axioms
`propext`, `Classical.choice` and `Quot.sound`, with no proof holes in the development.**
The [Palomar candidate](Challenge.lean) selects nine principal statements:
Theorems 1.10(i–iii), 3.1(i–ii), 7.1(ii), corrected 8.1(I), Introduction (II)
including lattice laws, and Theorem 8.1(II). Supporting construction lemmas
are also compared so that the statement file gives concrete tree laws,
codings, the J1 topology, and the coupled excursion/height law without
repeating their construction proofs. Two typeclass construction holes are
fixed by checked equations: evaluation is the underlying path and the metric
has the explicit J1 distance. The limiting laws are concrete. No Palomar
registration is claimed.
Links: [comparison statements](Challenge.lean) · [functional statements](BGWLeaves/LeafLimits.lean) ·
[correspondence record](FORMALIZATION_REPORT.md) ·
[submission interface](verification/FUNCTIONAL_SUBMISSION.md) ·
[verification](verification/README.md).

## Main results

Let $\mu$ be a critical, aperiodic offspring law in the domain of attraction of
a stable law of index $\theta\in(1,2]$, let $\tau_n$ be a Galton–Watson tree
conditioned to have $n$ leaves, and let $B_n$ be any norming sequence of the
step law ($W_n/B_n\to X_1$, `IsRealStableAttracted`).

| Paper | Lean | Statement |
| --- | --- | --- |
| Theorem 1.10, corrected | [`locallimit_i`, `locallimit_ii`](BGWLeaves/StableAnalysis.lean), [`locallimit_iii`](BGWLeaves/StableAnalysis/Consequences.lean) | explicit stable norming, its slow variation and the uniform scalar local limit theorem |
| Introduction (I), Theorem 3.1 | [`thm_ltn_i`, `thm_ltn_ii`](BGWLeaves/LeafMass.lean) | $\mathbb P_\mu[\lambda(\tau)=n+1]\sim\mu_0^{1/\theta}p_1(0)\gcd(b-1,d)/(h(n)n^{1/\theta+1})$ along multiples of $\gcd(b-1,d)$ |
| Introduction (II) | [`intro_II_general`](BGWLeaves/LeafLimitsGeneral.lean), [`intro_II`](BGWLeaves/LeafLimits.lean) | the rescaled Łukasiewicz path, contour and height of $\tau_n$ converge jointly to $(X^{exc},H^{exc},H^{exc})$ |
| Theorem 4.5 | [`thm_inv1`](BGWLeaves/LeafLimits.lean) | the same under the conditioning $\lambda(\tau)\ge n$ |
| Theorem 5.9 | [`thm_cvG_i`, `thm_cvG_ii`](BGWLeaves/LeafLimits.lean) | contour and height functions of $\tau_n$ |
| Theorem 6.1 | [`thm_cvW3`](BGWLeaves/LeafLimits.lean) | Łukasiewicz path of $\tau_n$ on $[0,1]$ |
| Theorem 7.1 | [`thm_max_i`](BGWLeaves/MaxDegreeLimit.lean), [`thm_max_ii`](BGWLeaves/MaxDegree.lean) | maximum degree: $\mu_0^{1/\theta}\Delta(\tau_n)/B_n\to\bar\Delta(X^{exc})$ for $\theta<2$; concentration around $D(n)$ under (H) |
| Theorem 8.1(I), corrected | [`thm81_corrected_general`](BGWLeaves/GeneralAInf.lean) | $\mathbb P_\mu[\zeta_{\mathcal A}=n]\sim\mu(\mathcal A)^{1/\theta}p_1(0)\,e/(h(n)n^{1/\theta+1})$ for $n\equiv1\bmod e$ |
| Theorem 8.1(II) | [`thm_general_II`](BGWLeaves/GeneralAFunctional.lean) | the joint limit under the conditioning $\zeta_{\mathcal A}(\tau)=n$; $\mathcal A$ finite or cofinite in infinite variance |
| GHP claim, Introduction | [`intro_GHP_leaf`](BGWLeaves/LeafLimits.lean) | $\tau_n$, with distances multiplied by $\mu_0^{1-1/\theta}B_n/n$ and the uniform measure on its leaves, converges to the stable tree |

The norming of Theorem 1.10 is corrected (the constant
$(-\Gamma(1-\theta))^{1/\theta}$ for $\theta<2$, and a factor $1/2$ under the
square root for $\theta=2$, $\sigma^2=\infty$); every statement holds for any
admissible norming, and corollaries give the corrected one. In Theorem 8.1(I)
the factor $\gcd(b-1,d)$ is replaced by $e$, the gcd of the degrees in
$\mathrm{supp}\mu\cap\mathcal A$ and of $k-1$ for the others. Where a
printed display is ill-posed (Theorem 5.1, Proposition 5.3, Lemma 5.7,
Remark 7.3), the Lean statement is a precise version of it. Theorems
5.9, 6.1, 7.1(i) and the steps leading to them carry the paper's Section 5
assumption that $\mathrm{supp}\mu\setminus\{0\}$ is non-lattice (`hnl`);
Introduction (II) and Theorem 8.1(II) are also proved without it. The full
correspondence, the proof-route differences and what is not formalized are in
the [correspondence record](FORMALIZATION_REPORT.md).

## Where to start

- [Challenge.lean](Challenge.lean): the nine principal statements, their
  construction lemmas and concrete mathematical definitions, importing only
  Mathlib and Lean core; the theorem proofs are deliberate placeholders
  supplied by [Solution.lean](Solution.lean), as are the two characterized
  typeclass instances.
- [BGWLeaves/LeafLimits.lean](BGWLeaves/LeafLimits.lean): the invariance
  principles (Theorems 4.5, 5.9, 6.1, Introduction (II)).
- [BGWLeaves/LeafMass.lean](BGWLeaves/LeafMass.lean): the number of leaves
  (Theorem 3.1, Corollary 3.3).
- [BGWLeaves/StableAnalysis.lean](BGWLeaves/StableAnalysis.lean): the local
  limit theorem 1.10 with the corrected norming.
- [BGWLeaves/GeneralAInf.lean](BGWLeaves/GeneralAInf.lean) and
  [BGWLeaves/GeneralAFunctional.lean](BGWLeaves/GeneralAFunctional.lean):
  Theorem 8.1.
- [BGWLeaves/Coding/Defs.lean](BGWLeaves/Coding/Defs.lean): the conditioned
  laws, the rescaled coding paths and the limit law.
- [Vendor/bgw](Vendor/VENDORED.md): trees, the Bienaymé law, Skorokhod space,
  stable processes and excursions, from the
  [Bienaymé–Galton–Watson trees](https://github.com/igor-kortchemski/Bienayme-Galton-Watson-Trees)
  formalization.

## Verify

The project pins Lean 4.35.0 and Mathlib v4.35.0; the exact dependencies are
in [lake-manifest.json](lake-manifest.json). Install Lean with
[the official guide](https://leanprover-community.github.io/install/project.html),
then run:

```bash
git clone https://github.com/igor-kortchemski/invariance-principles-galton-watson-lean.git
cd invariance-principles-galton-watson-lean
lake exe cache get
lake build
lake env lean scripts/AxiomAudit.lean
lake build Challenge Solution
# Linux, with Bubblewrap and nanoda_bin on PATH:
lake comparator --config comparator.json
```

Do not run `lake update`. A full build compiles about 1,000 project and
vendored modules on top of Mathlib. Only the deliberate Challenge placeholders
for theorem proofs and two characterized typeclass constructions in
`Challenge.lean` use `sorry`; that module is separate from the proved library. The axiom audit
fails if any project or vendored declaration depends on an axiom other than
the three above. To browse
the code, open the cloned folder in VS Code with the Lean 4 extension.

The [build workflow](.github/workflows/lean.yml) runs these checks on every
push. The [Comparator workflow](.github/workflows/comparator.yml) checks the
selected statements with the Linux sandbox and NanoDa. It covers only
the declarations in [comparator.json](comparator.json). Local comparison and
kernel replay are diagnostics; the official full Palomar verification remains
separate. Actual results are dated in [verification/](verification/README.md).
The Comparator badge reports the aggregate official full preflight, including
comparison and kernel replays; the standalone Linux workflow is a diagnostic.

## How it was made

The formalization was produced with AI agents: Claude Code (Claude Opus 5.5)
as coordinator, with Lean written by GPT-6.1 Sol, GPT-6 Luna, Claude Opus 5.5,
Kimi K3.1 Pro and DeepSeek V4.1 Flash, research and statement reviews by GPT-6
Astra, and independent statement, seal and coverage audits by Claude Sonnet 5.5
and GPT-6.1 Sol. The Lean kernel checks the proofs; no human has reviewed them
line by line.

## License and citation

The Lean code is licensed under [Apache-2.0](LICENSE), as are the vendored
packages under [Vendor/](Vendor/VENDORED.md), whose notices are preserved. The
license does not cover the paper. Maintainer: Igor Kortchemski. To cite the
mathematics, cite the paper; to cite this formalization, see
[CITATION.cff](CITATION.cff). Report problems in the
[issue tracker](https://github.com/igor-kortchemski/invariance-principles-galton-watson-lean/issues).
