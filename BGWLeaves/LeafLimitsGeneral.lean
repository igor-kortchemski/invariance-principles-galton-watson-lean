module

public import BGWLeaves.LeafLimits.Defs
public import BGWLeaves.Coding.Defs
public import BGWLeaves.Conditioning.Defs
public import BGWLeaves.StableAnalysis
public import BGW.StableTrees.RealAttraction
public import BGW.StableTrees.JointExcursion
public import BGW.Skorokhod.ExitPartition
public import BGW.StableTrees.Defs
public import BGW.Skorokhod.Basic
public import BGW.Skorokhod.Measurable
public import BGW.LocallyFinite.Basic
public import BGWLeaves.StableAnalysis.Defs
import BGWLeaves.LeafLimitsGeneral.Proof

/-!
# Tranche 2: Introduction (II) in the printed generality (OPTIONAL)

Source: arXiv:1110.2163v4 (`.orchestration/t2-arch/paper_utf8.tex`), Introduction (II), line 254.

OPTIONAL statement, kept apart from package M13 by owner decision (scope question Q2, `CLAUDE.md`,
12 November 2026) so that M13 can be sealed without it.  It is NOT counted as proved until its hole is
filled.  Its proof is to be supplied in `BGWLeaves.LeafLimitsGeneral.General` (imported through
`BGWLeaves.LeafLimitsGeneral.Proof`).
-/

@[expose] public section

namespace BGWLeaves

open MeasureTheory ProbabilityTheory Filter BGW
open BGW.StableTrees BGW.LocallyFinite BGWLeaves.StableAnalysis
open scoped ENNReal NNReal Topology

/-- **Introduction (II) (line 254) in the PRINTED generality**: aperiodic `μ`, possibly lattice
`supp μ ∖ {0}`, along the admissible `n` (no `hnl`).  Form: PRINTED generality (STRONGER than printed only
through the arbitrary admissible norming `B`).  OPTIONAL (owner decision Q2): the paper proves only the
non-lattice case (standing assumption of line 1269; lines 1602-1603 and 1996-1997 announce the weaker
"`P[λ = n] > 0` for `n` large"); the lattice case needs lattice forms of 5.4(ii), 5.11-5.13 and 6.11
(which FAIL as printed when `g ≥ 2`, R12 D6/D10).  Believed true (no counterexample).  The restricted
version actually frozen in M13 is `intro_II` (with `hnl`).  HARD. -/
theorem intro_II_general {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hap : Aperiodic μ) (hB : IsRealStableAttracted (realOffspringStepLaw μ) θ B) {q : ℕ → ℕ}
    (hqtop : Tendsto q atTop atTop) (hq : ∀ k, LeafAdmissible μ (q k)) :
    Tendsto (fun k => (leafTreeLaw μ (q k)).map (codingTriple B)) atTop (𝓝 (excTripleLaw θ)) := by
  exact BGWLeaves.LeafLimitsGeneral.General.intro_II_general hc hne hap hB hqtop hq

end BGWLeaves
