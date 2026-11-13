module

public import BGWLeaves.LeafLimitsGeneral.JointLattice

/-!
# Introduction (II) along admissible leaf counts, with no non-lattice assumption

The proof follows the marked-block lattice local limits, admissible denominator
asymptotics, and residue-projected densities through the joint functional limit.
The statement is `BGWLeaves.intro_II_general` (`BGWLeaves.LeafLimitsGeneral`).
-/

@[expose] public section
namespace BGWLeaves.LeafLimitsGeneral.General
open MeasureTheory ProbabilityTheory Filter BGW
open BGW.StableTrees BGW.LocallyFinite BGWLeaves.StableAnalysis
open scoped ENNReal NNReal Topology

theorem intro_II_general {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hap : Aperiodic μ) (hB : IsRealStableAttracted (realOffspringStepLaw μ) θ B) {q : ℕ → ℕ}
    (hqtop : Tendsto q atTop atTop) (hq : ∀ k, LeafAdmissible μ (q k)) :
    Tendsto (fun k => (leafTreeLaw μ (q k)).map (codingTriple B)) atTop (𝓝 (excTripleLaw θ)) := by
  exact JointLattice.intro_II hc hne hap hB hqtop hq


end BGWLeaves.LeafLimitsGeneral.General
