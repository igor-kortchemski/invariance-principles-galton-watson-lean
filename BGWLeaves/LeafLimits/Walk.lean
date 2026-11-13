module

public import BGWLeaves.LeafLimits.Defs
public import BGWLeaves.LeafLimits.Bridge
public import BGWLeaves.LeafLimits.VervaatLaw

/-!
# Theorem 6.1: the Łukasiewicz path under `λ = n`

Theorem 6.1 from the bridge invariance principle, Corollary 6.7 and the continuous mapping theorem
with Proposition 6.9(i) (`prop_bridge_i`).
The law identity is first proved for positive normings; finite modification and the stopped-clock
lower bound then handle arbitrary admissible normings, whose positivity is only eventual.
-/

@[expose] public section

namespace BGWLeaves.LeafLimits.Walk

open MeasureTheory ProbabilityTheory Filter BGW
open BGW.StableTrees BGW.LocallyFinite BGWLeaves.StableAnalysis
open scoped ENNReal NNReal Topology

/-- Corollary 6.7 as an equality of probability laws at an admissible leaf count. -/
theorem map_leafTreeLaw_eq_map_vervaat (μ : PMF ℕ) (B : ℕ → ℝ)
    (hBpos : ∀ m, 1 ≤ m → 0 < B m) {n : ℕ} (hn : 1 ≤ n)
    (hadm : LeafAdmissible μ n) :
    (leafTreeLaw μ n).map (fun τ => rescaledLuka (treeSize τ) (B (treeSize τ)) τ) =
      ((bridgeWalkLaw μ n).map (bridgeWalkPath B n)).map Skorokhod.vervaatD := by
  apply ProbabilityMeasure.toMeasure_injective
  rw [ProbabilityMeasure.toMeasure_map,
    ProbabilityMeasure.toMeasure_map,
    ProbabilityMeasure.toMeasure_map,
    Measure.map_map Skorokhod.measurable_vervaatD (measurable_bridgeWalkPath B n),
    coe_leafTreeLaw hadm,
    coe_bridgeWalkLaw ((iidWalk_bridgeAtMark_ne_zero_iff μ hn).mpr hadm)]
  exact VervaatLaw.cor_vervaatC μ B hBpos hn

/-- Finite modifications of the norming do not affect the leaf-conditioned path laws. -/
theorem eventually_map_rescaledLuka_eq {μ : PMF ℕ} {B B' : ℕ → ℝ}
    (hBB' : ∀ᶠ n in atTop, B n = B' n) {q : ℕ → ℕ}
    (hqtop : Tendsto q atTop atTop) (hq : ∀ k, LeafAdmissible μ (q k)) :
    ∀ᶠ k in atTop,
      (leafTreeLaw μ (q k)).map (fun τ => rescaledLuka (treeSize τ) (B (treeSize τ)) τ) =
      (leafTreeLaw μ (q k)).map (fun τ => rescaledLuka (treeSize τ) (B' (treeSize τ)) τ) := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp hBB'
  filter_upwards [hqtop.eventually_ge_atTop N] with k hk
  apply ProbabilityMeasure.toMeasure_injective
  rw [ProbabilityMeasure.toMeasure_map,
    ProbabilityMeasure.toMeasure_map,
    coe_leafTreeLaw (hq k)]
  apply Measure.map_congr
  filter_upwards [ae_cond_mem (measurableSet_leafCountEvent (q k))] with τ hτ
  obtain ⟨t, rfl, ht⟩ := hτ
  have hsize : N ≤ treeSize t.toLocallyFinite := by
    rw [treeSize_toLocallyFinite]
    exact hk.trans (ht ▸ t.degreeCount_le_size 0)
  rw [hN _ hsize]

/-- An admissible norming can be made positive at every size without changing any limiting law. -/
theorem exists_positive_norming {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ}
    (hB : IsRealStableAttracted (realOffspringStepLaw μ) θ B) :
    ∃ B' : ℕ → ℝ, (∀ m, 0 < B' m) ∧
      (∀ᶠ m in atTop, B m = B' m) ∧
      IsRealStableAttracted (realOffspringStepLaw μ) θ B' := by
  classical
  let B' : ℕ → ℝ := fun m => if 0 < B m then B m else 1
  have heq : ∀ᶠ m in atTop, B m = B' m := by
    filter_upwards [hB.pos] with m hm
    simp [B', hm]
  refine ⟨B', ?_, heq, hB.congr_eventually heq⟩
  intro m
  dsimp [B']
  split_ifs with hm
  · exact hm
  · exact zero_lt_one

/-- The law identity needed for Theorem 6.1 holds eventually for every admissible norming,
even when its finitely many initial values fail to be positive. -/
theorem eventually_map_leafTreeLaw_eq_map_vervaat {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ}
    (hB : IsRealStableAttracted (realOffspringStepLaw μ) θ B) {q : ℕ → ℕ}
    (hqtop : Tendsto q atTop atTop) (hq : ∀ k, LeafAdmissible μ (q k)) :
    ∀ᶠ k in atTop,
      (leafTreeLaw μ (q k)).map (fun τ => rescaledLuka (treeSize τ) (B (treeSize τ)) τ) =
        ((bridgeWalkLaw μ (q k)).map (bridgeWalkPath B (q k))).map Skorokhod.vervaatD := by
  obtain ⟨B', hpos, heq, -⟩ := exists_positive_norming hB
  filter_upwards [eventually_map_rescaledLuka_eq heq hqtop hq,
    Bridge.eventually_map_bridgeWalkPath_eq heq hqtop hq,
    hqtop.eventually_ge_atTop 1] with k htree hbridge hk
  rw [htree, map_leafTreeLaw_eq_map_vervaat μ B' (fun m _ => hpos m) hk (hq k), hbridge]

/-- Theorem 6.1, by the bridge invariance principle, Corollary 6.7 and the continuous
mapping theorem at the almost surely continuous Vervaat transform. -/
theorem thm_cvW3 {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hap : Aperiodic μ) (hB : IsRealStableAttracted (realOffspringStepLaw μ) θ B)
    (hnl : ¬ IsLatticeLaw (etaLaw μ)) {q : ℕ → ℕ}
    (hqtop : Tendsto q atTop atTop) (hq : ∀ k, LeafAdmissible μ (q k)) :
    Tendsto (fun k => (leafTreeLaw μ (q k)).map
        (fun τ => rescaledLuka (treeSize τ) (B (treeSize τ)) τ))
      atTop (𝓝 (levyExcLaw θ)) := by
  have ht := BGW.Probability.tendsto_map_of_ae_continuousAt
    (Bridge.tendsto_bridgeWalkPath hc hne hap hB hnl hqtop hq)
    (fun _ => Skorokhod.measurable_vervaatD.aemeasurable)
    (ClassicalLimits.Cited.prop_bridge_i hB.index_mem).1
  rw [(ClassicalLimits.Cited.prop_bridge_i hB.index_mem).2] at ht
  apply ht.congr'
  filter_upwards [eventually_map_leafTreeLaw_eq_map_vervaat hB hqtop hq] with k hk
  exact hk.symm

end BGWLeaves.LeafLimits.Walk
