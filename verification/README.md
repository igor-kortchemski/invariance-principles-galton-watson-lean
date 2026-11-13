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

## 13 November 2026, discrete submission candidate (local)

The [candidate account](DISCRETE_SUBMISSION.md) describes the seven selected
declarations, corrections, source review and the two helper-proof adaptations.

- **Focused build:** `lake build Challenge Solution` passes. The only proof-hole
  warnings are the seven deliberate theorem placeholders in Challenge.
- **Exact comparison:** Lake's `compareAt` and `checkAxioms` pass on the NDJSON
  exports: every selected statement and reached constant matches, and the
  Solution uses only `propext`, `Classical.choice` and `Quot.sound`.
- **Kernel replays:** `leanchecker --silent --from-export` and `nanoda_bin`
  both exit successfully on the same Solution export. NanoDa uses a hard error
  for unpermitted axioms. These are local diagnostics without the Linux sandbox.
- **All-declaration axiom audit:** passes for 6,705 exported declarations and
  their transitive proof dependencies, using the existing incremental build
  state. This is not a clean build or a replay of every repository theorem.
- **Layout:** 1,015 Lean files, no missing module headers, no Lean symlinks or
  committed compiled artifacts; the largest file is 2,214 lines. Challenge is
  678 lines and below 32 KiB, with no definition holes.
- **Scope preservation:** only the bodies of two existing helper proofs
  changed; their signatures and all surrounding source text are unchanged.
  Every other existing Lean source is unchanged.

The [machine record](2026-11-13-discrete/local-comparison.json) binds the
comparison and replays to the hashes of every Lean source, the Lake files,
toolchain and configuration. The final Challenge was freshly exported; the
Solution export was reused after checking that every recorded proof source,
configuration and toolchain was unchanged. The comparison and both kernel
replays then ran afresh. The large exports are not committed. Small evidence:
[comparison](2026-11-13-discrete/comparison.log),
[axiom audit](2026-11-13-discrete/axiom-audit.log),
[proof adaptations](2026-11-13-discrete/proof-adaptations.json),
[layout](2026-11-13-discrete/layout.json).

To reproduce all local diagnostics from a fresh output directory:

```bash
python3 -I scripts/local_compare.py /absolute/path/to/new-empty-output-directory
```

A broader local rebuild was started and stopped; it is not reported as a
passing full-candidate build. The completed checks above apply to the selected
discrete interface. A clean whole-repository build remains part of the final
Linux verification and official full preflight on the public candidate commit.

## Continuous integration

The [build workflow](../.github/workflows/lean.yml) runs a clean build with
the Mathlib cache, the `sorry` check and the axiom audit on every push. On 13
November 2026 it passed for the first commit, `1dec62b` (GitHub Actions run
43380746073, ubuntu-24.04): a clean build of 4,522 jobs, no `sorry`, and the
axiom audit on 6,705 declarations.
The same workflow also passed at the preparation baseline `73edc6f`
([run 43387354297](https://github.com/igor-kortchemski/invariance-principles-galton-watson-lean/actions/runs/43387354297)),
before the new interface and helper-proof adaptations. The new Linux
[Comparator workflow](../.github/workflows/comparator.yml) runs the sandboxed
NanoDa-backed check on demand. The [full-preflight workflow](../.github/workflows/palomar-full.yml)
calls the pinned official verifier on an explicitly selected public commit.
Their Actions runs identify the checked source revision and preserve diagnostics.

## Checks outside the local record

- Official sandboxed Linux Comparator for the new discrete interface: see
  the corresponding exact-commit Actions runs.
- Full Palomar mechanical preflight on an exact public candidate commit:
  see the corresponding Actions run and its mechanical report.
- Independent review of the new single-file Challenge presentation; the
  existing development audits are retained and its mathematical interface
  has been self-reviewed against the paper.
