# Vendored packages

The proofs use three Lean packages that are not on a public commit compatible
with this project's pins, so the modules they import are copied here, with
their package configurations, licenses and file notices preserved:

- [bgw](bgw/lakefile.toml): the
  [Bienaymé–Galton–Watson trees](https://github.com/igor-kortchemski/Bienayme-Galton-Watson-Trees)
  formalization by Igor Kortchemski (Apache-2.0): plane and locally finite
  trees, the Bienaymé law, Skorokhod space, stable processes, their
  excursions, bridges and height processes, the Vervaat transform and the
  Gromov–Hausdorff–Prokhorov topology. Copied from its development revision
  `ce30db3f3563cd6ce35dd3f6e7d19107baef813a` (11 November 2026).
- [BrownianMotion](bgw/vendor/brownian-motion/README.md) and
  [KolmogorovExtension4](bgw/vendor/kolmogorov-extension4/README.md): source
  slices of the projects of Rémy Degenne and contributors (Apache-2.0), as
  vendored by the library above; their README files give the upstream
  revisions and the local adaptations.

Only the modules in the import closure of `BGWLeaves` are included (770, 26
and 4 files). The packages keep their own Lake configurations and Lean options
and are path dependencies of this project.
