module

public import BGWLeaves.Coding.Defs
public import BGWLeaves.Vervaat.Defs

/-!
# Tranche 2, package M14 `MaxDegreeLimit`: proved bridges

Source: arXiv:1110.2163v4 (`.orchestration/t2-arch/paper_utf8.tex`): Theorem 7.1(i) (`thm:max`,
line 2357) and the remark of line 2351.

Package M14 has no new definition: the maximal out-degree `Δ(τ)` is tranche 1's `maxDegree` of the plane
tree `toPlaneTree τ` (package M11).  This file contains the PROVED measurability of the rescaled maximal
degree pushed forward in the statements of `BGWLeaves.MaxDegreeLimit`.  No proof hole, no axiom.  It will
be frozen whole.
-/

@[expose] public section

namespace BGWLeaves

open MeasureTheory ProbabilityTheory Filter BGW
open BGW.StableTrees BGW.LocallyFinite BGWLeaves.StableAnalysis
open scoped ENNReal NNReal Topology

/-- `τ ↦ Δ(τ)` (maximal out-degree of the finite tree, junk for infinite trees) is measurable. -/
theorem measurable_maxDegree_toPlaneTree :
    Measurable (fun τ : LocallyFinite.Tree => (maxDegree (toPlaneTree τ) : ℝ)) :=
  measurable_comp_toPlaneTree (fun t => (maxDegree t : ℝ))

/-- The rescaled maximal degree `τ ↦ c Δ(τ) / b` of Theorem 7.1(i) is measurable. -/
theorem measurable_scaledMaxDegree (c b : ℝ) :
    Measurable (fun τ : LocallyFinite.Tree => c * (maxDegree (toPlaneTree τ) : ℝ) / b) :=
  measurable_comp_toPlaneTree (fun t => c * (maxDegree t : ℝ) / b)

end BGWLeaves
