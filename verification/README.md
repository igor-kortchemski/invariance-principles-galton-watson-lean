# Verification

Checks on the published tree, with their dates and what they cover.

## 13 November 2026, local (macOS, Lean 4.35.0, Mathlib v4.35.0)

- **Build.** `lake build` in the exported tree: all 4,522 jobs up to date.
  The modules had been compiled from byte-identical sources in the development
  checkouts, so this confirms the configuration and the sources; it is not a
  clean build (the build workflow is).
- **No `sorry`.** The build log contains no `declaration uses 'sorry'`.
- **Axioms.** `lake env lean scripts/AxiomAudit.lean` passes: the 6,705
  exported declarations of the project and vendored modules depend only on
  `propext`, `Classical.choice` and `Quot.sound`. The same audit run from a
  file outside the module system, which also sees the private declarations,
  passes for all 18,714 declarations (16,893 theorems).
- **Names.** Every declaration named in the README and the
  [correspondence record](../FORMALIZATION_REPORT.md) was resolved in the
  Lean environment.

## Continuous integration

The [build workflow](../.github/workflows/lean.yml) runs a clean build with
the Mathlib cache, the `sorry` check and the axiom audit on every push. On 13
November 2026 it passed for the first commit, `1dec62b` (GitHub Actions run
43380746073, ubuntu-24.04): a clean build of 4,522 jobs, no `sorry`, and the
axiom audit on 6,705 declarations.

## Not run

- Comparator: there is no Challenge/Solution interface yet. The statements
  reach the vendored definitions of stable processes, their excursion measure
  and height process, which a self-contained Challenge depending only on
  Mathlib would have to restate.
- Kernel replay with `leanchecker`, and the Palomar preflight.
