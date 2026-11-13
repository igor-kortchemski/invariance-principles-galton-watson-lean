module

public import BGWLeaves.LeafLimitsGeneral.FullBridgeLattice
public import BGWLeaves.LeafLimits.Walk

/-! Lattice Theorem 6.1, by the proved Vervaat-law identity and the lattice bridge.
Adapted from `LeafLimits.Walk.thm_cvW3`. -/

@[expose] public section
namespace BGWLeaves.LeafLimitsGeneral.WalkLattice
open MeasureTheory ProbabilityTheory Filter BGW BGW.StableTrees BGW.LocallyFinite
open BGWLeaves.StableAnalysis BGWLeaves.LeafLimits.Walk
open BGWLeaves.LeafLimits
open scoped ENNReal NNReal Topology

theorem thm_cvW3 {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hap : Aperiodic μ) (hB : IsRealStableAttracted (realOffspringStepLaw μ) θ B)
 {q : ℕ → ℕ}
    (hqtop : Tendsto q atTop atTop) (hq : ∀ k, LeafAdmissible μ (q k)) :
    Tendsto (fun k => (leafTreeLaw μ (q k)).map
        (fun τ => rescaledLuka (treeSize τ) (B (treeSize τ)) τ))
      atTop (𝓝 (levyExcLaw θ)) := by
  have ht := BGW.Probability.tendsto_map_of_ae_continuousAt
    (FullBridgeLattice.tendsto_bridgeWalkPath hc hne hap hB hqtop hq)
    (fun _ => Skorokhod.measurable_vervaatD.aemeasurable)
    (ClassicalLimits.Cited.prop_bridge_i hB.index_mem).1
  rw [(ClassicalLimits.Cited.prop_bridge_i hB.index_mem).2] at ht
  apply ht.congr'
  filter_upwards [eventually_map_leafTreeLaw_eq_map_vervaat hB hqtop hq] with k hk
  exact hk.symm


end BGWLeaves.LeafLimitsGeneral.WalkLattice
