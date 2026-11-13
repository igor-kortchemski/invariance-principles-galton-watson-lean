module

public import BGWLeaves.GeneralAFunctional.WalkLocal
public import BGWLeaves.GeneralAFunctional.WalkReversal
public import BGWLeaves.GeneralAFunctional.WalkFCLT
public import BGWLeaves.GeneralAInf.Asymptotic
public import BGWLeaves.ClassicalLimits.Cited
public import BGW.Probability.WeakConvergence

/-! Assembly interfaces for the arbitrary-mark walk limit.
The full marked-bridge invariance principle remains a separate obligation.
-/

@[expose] public section
namespace BGWLeaves.GeneralAFunctional.Walk

open MeasureTheory ProbabilityTheory Filter BGW BGW.StableTrees BGW.LocallyFinite
open BGWLeaves.StableAnalysis
open BGWLeaves.GeneralAFunctional.WalkCyclic BGWLeaves.GeneralAFunctional.WalkVervaat
open scoped ENNReal NNReal Topology

noncomputable section
attribute [local instance] Classical.propDecidable

theorem bridgeAtAMark_ne_zero_iff (μ : PMF ℕ) (A : Set ℕ) {n : ℕ} (hn : 1 ≤ n) :
    iidWalk μ (bridgeAtAMark A n) ≠ 0 ↔ ZetaAAdmissible μ A n := by
  rw [iidWalk, WalkCyclic.prop_vervaatdiscrete_total, mul_ne_zero_iff]
  have hn0 : (n : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  exact and_iff_right hn0

/-- The A-stopped walk conditioned to end at `-1`. -/
def aBridgeLaw (μ : PMF ℕ) (A : Set ℕ) (n : ℕ) : ProbabilityMeasure (ℕ → ℕ) :=
  if h : iidWalk μ (bridgeAtAMark A n) ≠ 0 then
    ⟨(iidWalk μ)[|bridgeAtAMark A n], cond_isProbabilityMeasure h⟩
  else ⟨Measure.dirac (fun _ => 0), inferInstance⟩

theorem coe_aBridgeLaw {μ : PMF ℕ} {A : Set ℕ} {n : ℕ} (hn : 1 ≤ n)
    (hadm : ZetaAAdmissible μ A n) :
    (aBridgeLaw μ A n : Measure (ℕ → ℕ)) = (iidWalk μ)[|bridgeAtAMark A n] := by
  have hp := (bridgeAtAMark_ne_zero_iff μ A hn).mpr hadm
  have he : aBridgeLaw μ A n = ⟨(iidWalk μ)[|bridgeAtAMark A n], cond_isProbabilityMeasure hp⟩ := by
    unfold aBridgeLaw
    exact dite_eq_left hp
  rw [he]
  rfl

theorem map_tree_eq_map_vervaat (μ : PMF ℕ) (A : Set ℕ) (B : ℕ → ℝ)
    (hBpos : ∀ m, 1 ≤ m → 0 < B m) {n : ℕ} (hn : 1 ≤ n)
    (hadm : ZetaAAdmissible μ A n) :
    (zetaATreeLaw μ A n).map (fun τ => rescaledLuka (treeSize τ) (B (treeSize τ)) τ) =
      ((aBridgeLaw μ A n).map (aBridgeWalkPath A B n)).map Skorokhod.vervaatD := by
  apply ProbabilityMeasure.toMeasure_injective
  rw [ProbabilityMeasure.toMeasure_map, ProbabilityMeasure.toMeasure_map,
    ProbabilityMeasure.toMeasure_map, coe_zetaATreeLaw hadm, coe_aBridgeLaw hn hadm,
    Measure.map_map Skorokhod.measurable_vervaatD (measurable_aBridgeWalkPath A B n)]
  exact WalkVervaat.cor_vervaatC μ A B hBpos hn

theorem mark_mass_ne_zero_of_admissible_sequence {μ : PMF ℕ} {A : Set ℕ}
    (hc : IsCritical μ) (hne : μ 1 ≠ 1) {q : ℕ → ℕ}
    (hqtop : Tendsto q atTop atTop) (hq : ∀ k, ZetaAAdmissible μ A (q k)) :
    μ.toMeasure A ≠ 0 := by
  intro hz
  obtain ⟨K, hK⟩ := eventually_atTop.mp (hqtop.eventually_ge_atTop 1)
  have he := GeneralAInf.Asymptotic.zetaA_eq_zero_of_measure_zero hc hne hz (hK K le_rfl)
  apply hq K
  exact measure_mono_null (fun _ h => h.2) he

theorem treeSize_ge_mark_count {A : Set ℕ} {n : ℕ} {τ : LocallyFinite.Tree}
    (hτ : FiniteVertices τ ∧ zetaA A τ = (n : ℕ∞)) : n ≤ treeSize τ := by
  obtain ⟨t, rfl⟩ := (exists_toLocallyFinite_iff τ).mpr hτ.1
  have hn : GeneralA.Marked.treeACount A t = n := by
    simpa only [GeneralA.MarkedLaw.zetaA_toLocallyFinite, ENat.natCast_inj] using hτ.2
  rw [treeSize_toLocallyFinite, ← hn, GeneralA.Marked.treeACount]
  exact List.countP_le_length.trans (PlaneTree.length_degrees t).le

theorem aMarkTime_ge_mark_count {A : Set ℕ} {n : ℕ} {ω : ℕ → ℕ}
    (hω : ω ∈ bridgeAtAMark A n) : n ≤ aMarkTime A n ω := by
  obtain ⟨m, hm, -⟩ := hω
  rw [aMarkTime_eq hm, ← hm.1]
  exact (Finset.card_filter_le _ _).trans (by simp)

/-- Eventual positivity suffices in the Vervaat law identity: changing finitely
many norming values is harmless because both random sizes are at least `n`. -/
theorem eventually_map_tree_eq_map_vervaat {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ} {A : Set ℕ}
    (hB : IsRealStableAttracted (realOffspringStepLaw μ) θ B) {q : ℕ → ℕ}
    (hqtop : Tendsto q atTop atTop) (hq : ∀ k, ZetaAAdmissible μ A (q k)) :
    ∀ᶠ k in atTop,
      (zetaATreeLaw μ A (q k)).map
          (fun τ => rescaledLuka (treeSize τ) (B (treeSize τ)) τ) =
        ((aBridgeLaw μ A (q k)).map (aBridgeWalkPath A B (q k))).map Skorokhod.vervaatD := by
  let B' : ℕ → ℝ := fun m => if 0 < B m then B m else 1
  have hpos (m : ℕ) : 0 < B' m := by
    dsimp [B']
    split_ifs with hm
    · exact hm
    · exact zero_lt_one
  obtain ⟨N, hN⟩ := eventually_atTop.mp hB.pos
  filter_upwards [hqtop.eventually_ge_atTop (max N 1)] with k hk
  have hq1 : 1 ≤ q k := (le_max_right _ _).trans hk
  have htree : (zetaATreeLaw μ A (q k)).map
        (fun τ => rescaledLuka (treeSize τ) (B (treeSize τ)) τ) =
      (zetaATreeLaw μ A (q k)).map
        (fun τ => rescaledLuka (treeSize τ) (B' (treeSize τ)) τ) := by
    apply ProbabilityMeasure.toMeasure_injective
    rw [ProbabilityMeasure.toMeasure_map, ProbabilityMeasure.toMeasure_map,
      coe_zetaATreeLaw (hq k)]
    apply Measure.map_congr
    filter_upwards [ae_cond_mem (measurableSet_zetaAEvent A (q k))] with τ hτ
    have hsize := treeSize_ge_mark_count hτ
    have hp := hN (treeSize τ) (le_trans ((le_max_left _ _).trans hk) hsize)
    simp only [B', ite_eq_left hp]
  have hwalk : (aBridgeLaw μ A (q k)).map (aBridgeWalkPath A B (q k)) =
      (aBridgeLaw μ A (q k)).map (aBridgeWalkPath A B' (q k)) := by
    apply ProbabilityMeasure.toMeasure_injective
    rw [ProbabilityMeasure.toMeasure_map, ProbabilityMeasure.toMeasure_map,
      coe_aBridgeLaw hq1 (hq k)]
    apply Measure.map_congr
    filter_upwards [ae_cond_mem (measurableSet_bridgeAtAMark A (q k))] with ω hω
    have hsize := aMarkTime_ge_mark_count hω
    have hp := hN (aMarkTime A (q k) ω) (le_trans ((le_max_left _ _).trans hk) hsize)
    simp only [aBridgeWalkPath, B', ite_eq_left hp]
  rw [htree, map_tree_eq_map_vervaat μ A B' (fun m _ => hpos m) hq1 (hq k), hwalk]

/-- Once the full A-marked bridge invariance principle is proved, H and Vervaat
continuity give the required tree-walk limit at the original random total size. -/
theorem walk_tendsto_of_bridge {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ} {A : Set ℕ}
    (hB : IsRealStableAttracted (realOffspringStepLaw μ) θ B) {q : ℕ → ℕ}
    (hqtop : Tendsto q atTop atTop) (hq : ∀ k, ZetaAAdmissible μ A (q k))
    (hbridge : Tendsto (fun k => (aBridgeLaw μ A (q k)).map (aBridgeWalkPath A B (q k)))
      atTop (𝓝 (stableBridgeLaw θ))) :
    Tendsto (fun k => (zetaATreeLaw μ A (q k)).map
        (fun τ => rescaledLuka (treeSize τ) (B (treeSize τ)) τ))
      atTop (𝓝 (levyExcLaw θ)) := by
  have ht := BGW.Probability.tendsto_map_of_ae_continuousAt hbridge
    (fun _ => Skorokhod.measurable_vervaatD.aemeasurable)
    (ClassicalLimits.Cited.prop_bridge_i hB.index_mem).1
  rw [(ClassicalLimits.Cited.prop_bridge_i hB.index_mem).2] at ht
  apply ht.congr'
  filter_upwards [eventually_map_tree_eq_map_vervaat hB hqtop hq] with k hk
  exact hk.symm

end
end BGWLeaves.GeneralAFunctional.Walk
