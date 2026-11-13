# Discrete submission candidate

Prepared from the curated export at
`73edc6fee68b05eb89a448ba5f2fddab39869b56` on 13 November 2026.
The development checkout is separate and was not edited by this preparation.
The vendored source provenance remains documented in [VENDORED.md](../Vendor/VENDORED.md).

## Selected statements

The [configuration](../comparator.json) selects exactly these declarations:

| Paper | Declaration in `BGWLeaves` | Meaning |
| --- | --- | --- |
| 1.10(i) | `StableAnalysis.locallimit_i` | The corrected explicit normalizer gives scalar stable convergence. |
| 1.10(ii) | `StableAnalysis.locallimit_ii` | That normalizer is nondecreasing and is a power times a slowly varying function. |
| 1.10(iii) | `StableAnalysis.locallimit_iii` | The uniform local limit estimate, for a non-lattice integer step law. |
| 3.1(i) | `thm_ltn_i` | The eventual admissible leaf counts are exactly one arithmetic progression. |
| 3.1(ii), Introduction (I) | `thm_ltn_ii` | The leaf-count probability asymptotic on that progression. |
| 8.1(I), corrected | `thm81_corrected_general` | The corrected arithmetic factor and asymptotic for counts of vertices with degree in a set. |
| 7.1(ii) | `thm_max_ii` | Maximum-degree concentration under hypothesis H, conditional on a non-null leaf count. |

`Challenge.lean` imports only Mathlib and Lean core and gives concrete values
for every definition. Exactly seven theorem proofs are deliberate placeholders.
`Solution.lean` imports the proved modules and does not import Challenge.
There are no definition holes or added axioms. The functional invariance
principles remain in the repository, outside this comparison and submission.

## Mathematical interface review

This is a self-review by the preparing agent, not an independent review of the
new Challenge. The earlier independent audits of the development are recorded
in [FORMALIZATION_REPORT.md](../FORMALIZATION_REPORT.md).

The interface was checked against the paper's Theorems 1.10, 3.1, 7.1(ii)
and 8.1(I), their standing assumptions, and the existing correction record:

- The stable law has Laplace transform $\exp(\lambda^\theta)$, with
  $1<\theta\le2$. Its density is defined by Fourier inversion, not an
  unspecified limiting distribution. The scalar attraction hypotheses state
  weak convergence through bounded continuous test functions.
- Theorem 3.1 uses $\lambda=n+1$ and the filter of multiples of
  $\gcd(b-1,d)$. The support-span predicate includes the maximality of $d$
  and minimality of $b$. Lattice cases are retained.
- Theorem 8.1(I) uses the corrected gcd of the degrees in
  $\operatorname{supp}\mu\cap A$ and of $k-1$ outside $A$. It includes the
  zero probabilities off the admissible progression. Positive offspring
  mass of $A$ is explicit. The arbitrary-set and non-aperiodic extension is
  described as a strengthening; the printed false arithmetic factor is
  not claimed proved.
- Hypothesis H includes criticality, nondegeneracy, aperiodicity, finite
  variance, and the generating-function radius and root conditions.
  Theorem 7.1(ii) retains bounded-support laws and quantifies only over
  non-null conditioning events. The conditional law uses Mathlib's
  conditional probability, and the maximum counts offspring, not increments.

## Interface alignment

Two vendored helper proofs, `canonical_pruneRaw` and
`canonical_offspringAt`, use explicit steps to eliminate module-private
simplifier auxiliaries. Their types and the tree definitions are unchanged.
This is a proof adaptation of the vendored copy, not a new mathematical claim.

The Challenge also spells out two instance paths and preserves the original
auxiliary matcher/proof names. Its commented cache reset affects only Lean's
auxiliary-lemma elaboration cache; it changes no mathematical declaration.
Lake targets were added only in the curated export, which has no freeze
records. The development checkout and its freeze records are untouched.

## Verification and remaining steps

Actual results are recorded in [README.md](README.md). Local comparison and
kernel replay are diagnostics, not the official sandboxed Linux Comparator
or the full Palomar verifier. The prepared
[Comparator workflow](../.github/workflows/comparator.yml) runs the former;
the [full-preflight workflow](../.github/workflows/palomar-full.yml) uses the
official reusable verifier with `mode: full`. The inactive
[template](palomar-full.workflow.yml.template) records the same call.

The pipeline revision was checked on 13 November 2026:
`14aa8d6b3c2f14a8540605e37144560b9a00e7e7`.
The [submission policy](https://github.com/PalomarRegistry/PalomarPolicy/blob/main/CONTRIBUTING.md)
and Challenge allowlist were checked on the same date.

The public source repository includes the vendored BGW source slice from
`ce30db3f3563cd6ce35dd3f6e7d19107baef813a`, including material for which a
compatible public upstream revision was unavailable during preparation.
The two existing commits use the maintainer's GitHub noreply identity; a
targeted scan found no private filesystem paths or common credential-token
markers in their first-party contents. Registration additionally preserves the full Git
history and publishes the returned review, under the Palomar publication
contract. GitHub publication and mechanical verification are separate from
registry intake and the later decision about registering the returned review.
