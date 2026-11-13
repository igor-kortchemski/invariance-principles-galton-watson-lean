module

public import BGWLeaves.LeafLimitsGeneral.ChiBlock
public import BGWLeaves.LocalEstimates.LeafWindow
public import BGWLeaves.LeafMass.LeafLocalLimit
public import BGWLeaves.Conditioning.Basics

/-! Lattice local estimates for leaf conditioning. The forest adapter specializes
`GeneralAInf.BlockLocal`; the signed estimate uses the exact block-clock law.
Proofs adapted from `GeneralAInf.BlockLocal` and `LocalEstimates.LeafWindow`. -/

@[expose] public section
namespace BGWLeaves.LeafLimitsGeneral.LocalLattice
open MeasureTheory ProbabilityTheory Filter BGW BGW.StableTrees BGW.LocallyFinite
open BGWLeaves.StableAnalysis
open BGWLeaves.GeneralA Marked MarkedLaw MarkedWalk Regroup MarkedTime MarkedSpan
open scoped ENNReal Topology

/-- Marking offspring zero counts leaves. -/
theorem treeACount_zero (t : PlaneTree) : treeACount {0} t = t.degreeCount 0 := by
  classical
  simp only [treeACount, PlaneTree.degreeCount, List.count_eq_countP, Set.mem_singleton_iff]
  congr 1

/-- The marked forest and the finite leaf forest have equal probabilities.
Critical nondegenerate trees are finite almost surely. -/
theorem psi_eq_markedForest {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (n j : ℕ) :
    psi μ n j = (forestLaw μ j) {F | ∑ i, zetaA {0} (F i) = (n : ℕ∞)} := by
  have hmean : (∫⁻ k : ℕ, (k : ℝ≥0∞) ∂μ.toMeasure) = 1 := by
    rw [lintegral_countable']
    simp only [PMF.toMeasure_apply_singleton μ _ (measurableSet_singleton _)]
    exact hc
  have hne' : μ.toMeasure {1} ≠ 1 := by
    simpa only [PMF.toMeasure_apply_singleton μ _ (measurableSet_singleton _)] using hne
  have hae := LocallyFinite.ae_finiteVertices_bienaymeLaw μ.toMeasure hmean.le hne'
  have hfinite : ∀ᵐ F ∂forestLaw μ j, ∀ i, LocallyFinite.FiniteVertices (F i) :=
    ae_all_iff.2 fun _ => Measure.tendsto_eval_ae_ae.eventually hae
  unfold psi
  apply measure_congr
  filter_upwards [hfinite] with F hF
  apply propext
  constructor
  · intro h
    obtain ⟨p, ts, hp, hn, rfl⟩ := Set.mem_iUnion.mp h
    change (∑ i, zetaA {0} ((ts i).toLocallyFinite)) = (n : ℕ∞)
    simp_rw [zetaA_toLocallyFinite, treeACount_zero]
    rw [← Nat.cast_sum, hn]
  · intro hz
    choose ts hts using fun i => (LocallyFinite.exists_toLocallyFinite_iff (F i)).2 (hF i)
    have he : (∑ i, zetaA {0} (F i)) = ((∑ i, (ts i).degreeCount 0 : ℕ) : ℕ∞) := by
      rw [Nat.cast_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [← hts i, zetaA_toLocallyFinite, treeACount_zero]
    rw [he] at hz
    exact Set.mem_iUnion.mpr ⟨∑ i, (ts i).size,
      ⟨ts, rfl, ENat.natCast_inj.mp hz, funext fun i => (hts i).symm⟩⟩

/-- The leaf-forest block-walk identity. -/
theorem psi_eq_blockWalk {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    {n j : ℕ} (hn : 1 ≤ n) (hj : 1 ≤ j) :
    psi μ n j = (j : ℝ≥0∞) * (n : ℝ≥0∞)⁻¹ *
      intWalk (blockStep μ {0}) n {-(j : ℤ)} := by
  rw [psi_eq_markedForest hc hne]
  exact GeneralAInf.Forest.zetaA_forest_blockLaw hc hne {0} hj hn

/-- Lattice replacement for 5.4(ii), with the span factor and endpoint residue. -/
theorem lem_technical_ii {μ : PMF ℕ} {θ : ℝ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hDA : ∃ a, StableDomain μ θ a) {α : ℝ} (hα : 0 < α) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ j : ℕ, 1 ≤ j → (j : ℝ) ≤ α * normB μ θ n →
      |(n : ℝ) * (psi μ n j).toReal -
        (if (arithFactor μ {0} : ℤ) ∣ (n : ℤ) - j then
          (arithFactor μ {0} : ℝ) * qKernel θ 1
            (j / normB μ θ ((n : ℝ) / (μ 0).toReal)) else 0)| ≤ ε := by
  have hA : μ.toMeasure ({0} : Set ℕ) ≠ 0 := by
    simpa only [PMF.toMeasure_apply_singleton μ 0 (measurableSet_singleton 0)] using hc.apply_zero_ne_zero hne
  obtain ⟨N, hN⟩ := GeneralAInf.BlockLocal.eq_gen_corrected hc hne hDA hA hα hε
  refine ⟨N, fun n hn j hj hju => ?_⟩
  have h := hN n hn j hj (by simpa only [normB_natCast] using hju)
  rw [psi_eq_markedForest hc hne]
  simpa only [normB, PMF.toMeasure_apply_singleton μ 0 (measurableSet_singleton 0),
    qKernel_one, q₁, forestLaw, measureReal_def] using h

/-- Direct lattice LLT for the stopped walk, retaining its one-step endpoint shift. -/
theorem chi_local_shifted {μ : PMF ℕ} {θ : ℝ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hDA : ∃ a, StableDomain μ θ a) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ j : ℤ,
      |normB μ θ ((n : ℝ) / (μ 0).toReal) * (chi μ n j).toReal -
        (if (arithFactor μ {0} : ℤ) ∣ (n : ℤ) - 1 - j then
          (arithFactor μ {0} : ℝ) * Scalar.stableDensity θ
            ((-1 - (j : ℝ)) / normB μ θ ((n : ℝ) / (μ 0).toReal)) else 0)| ≤ ε := by
  have hA : μ.toMeasure ({0} : Set ℕ) ≠ 0 := by
    simpa only [PMF.toMeasure_apply_singleton μ 0 (measurableSet_singleton 0)] using hc.apply_zero_ne_zero hne
  obtain ⟨hprob, hi, hm⟩ := GeneralAInf.BlockStable.blockStep_firstMoment hc hA
  let := hprob
  change mean (blockStep μ {0}) = 0 at hm
  have hattr := GeneralAInf.BlockStable.blockStep_isStableAttracted hc hne hDA hA
  have hattr' : IsStableAttracted (blockStep μ {0}) θ (mean (blockStep μ {0}))
      (fun n : ℕ => normB μ θ ((n : ℝ) / (μ 0).toReal)) := by
    simpa only [hm, normB, PMF.toMeasure_apply_singleton μ 0 (measurableSet_singleton 0)] using hattr
  obtain ⟨hs, hr⟩ := blockLaw_span hc hne hA
  have hmono : Monotone (fun n : ℕ => normB μ θ ((n : ℝ) / (μ 0).toReal)) := by
    simpa only [normB, PMF.toMeasure_apply_singleton μ 0 (measurableSet_singleton 0)] using
      GeneralAInf.BlockStable.monotone_norming_floor hc hne hDA hA
  obtain ⟨N, hN⟩ := LeafMass.YLaw.llt_lattice_abstract (blockStep μ {0}) hi hs (-1) hr hmono hattr' hε
  refine ⟨max N 1, fun n hn j => ?_⟩
  rw [ChiBlock.chi_toReal_eq_blockWalk μ (le_trans (le_max_right _ _) hn)]
  have he : -1 - j - (n : ℤ) * (-1) = (n : ℤ) - 1 - j := by ring
  simpa only [he, hm, mul_zero, sub_zero, Int.cast_sub, Int.cast_neg, Int.cast_one] using
    hN n (le_trans (le_max_left _ _) hn) (-1 - j)

/-- The canonical block norming diverges. -/
theorem block_norming_atTop {μ : PMF ℕ} {θ : ℝ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hDA : ∃ a, StableDomain μ θ a) :
    Tendsto (fun n : ℕ => normB μ θ ((n : ℝ) / (μ 0).toReal)) atTop atTop := by
  have hA : μ.toMeasure ({0} : Set ℕ) ≠ 0 := by
    simpa only [PMF.toMeasure_apply_singleton μ 0 (measurableSet_singleton 0)] using hc.apply_zero_ne_zero hne
  obtain ⟨hp, _, _⟩ := GeneralAInf.BlockStable.blockStep_firstMoment hc hA
  let := hp
  have ht := TransformConvergence.tendsto_atTop (blockStep μ {0})
    (GeneralAInf.BlockStable.blockStep_isStableAttracted hc hne hDA hA)
  simpa only [normB, PMF.toMeasure_apply_singleton μ 0 (measurableSet_singleton 0)] using ht

/-- Lattice replacement for 6.11, uniformly over all signed endpoints. -/
theorem lem_technic3 {μ : PMF ℕ} {θ : ℝ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hDA : ∃ a, StableDomain μ θ a) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ j : ℤ,
      |normB μ θ ((n : ℝ) / (μ 0).toReal) * (chi μ n j).toReal -
        (if (arithFactor μ {0} : ℤ) ∣ (n : ℤ) - 1 - j then
          (arithFactor μ {0} : ℝ) * Scalar.stableDensity θ
            (-((j : ℝ) / normB μ θ ((n : ℝ) / (μ 0).toReal))) else 0)| ≤ ε := by
  obtain ⟨b, hb⟩ := hDA
  let g : ℝ := arithFactor μ {0}
  have hg : 0 < g := by dsimp [g]; exact_mod_cast GeneralA.Arithmetic.arithFactor_pos hc hne {0}
  obtain ⟨δ, hδ, hd⟩ := (Metric.uniformContinuous_iff.1
    (Scalar.uniformContinuous_stableDensity hb.alpha_mem)) (ε / (2 * g)) (by positivity)
  obtain ⟨N, hN⟩ := chi_local_shifted hc hne ⟨b, hb⟩ (half_pos hε)
  have htop := block_norming_atTop hc hne ⟨b, hb⟩
  have hi : Tendsto (fun n : ℕ => 1 / normB μ θ ((n : ℝ) / (μ 0).toReal))
      atTop (𝓝 (0 : ℝ)) := tendsto_const_nhds.div_atTop htop
  obtain ⟨M, hM⟩ := eventually_atTop.1 ((hi.eventually (eventually_lt_nhds hδ)).and
    (htop.eventually (eventually_gt_atTop 0)))
  refine ⟨max N M, fun n hn j => ?_⟩
  obtain ⟨hsmall, hpos⟩ := hM n (le_trans (le_max_right _ _) hn)
  have h := hN n (le_trans (le_max_left _ _) hn) j
  by_cases hr : (arithFactor μ {0} : ℤ) ∣ (n : ℤ) - 1 - j
  · rw [ite_eq_left hr] at h ⊢
    have harg : dist ((-1 - (j : ℝ)) / normB μ θ ((n : ℝ) / (μ 0).toReal))
        (-((j : ℝ) / normB μ θ ((n : ℝ) / (μ 0).toReal))) < δ := by
      rw [Real.dist_eq, show (-1 - (j : ℝ)) / normB μ θ ((n : ℝ) / (μ 0).toReal) -
        (-((j : ℝ) / normB μ θ ((n : ℝ) / (μ 0).toReal))) =
          -(1 / normB μ θ ((n : ℝ) / (μ 0).toReal)) by ring, abs_neg,
        abs_of_pos (one_div_pos.mpr hpos)]
      exact hsmall
    have hp := hd harg
    rw [Real.dist_eq] at hp
    have hmul := mul_lt_mul_of_pos_left hp hg
    have he : g * (ε / (2 * g)) = ε / 2 := by field_simp
    rw [he] at hmul
    have hh := abs_sub_le (normB μ θ ((n : ℝ) / (μ 0).toReal) * (chi μ n j).toReal)
      (g * Scalar.stableDensity θ ((-1 - (j : ℝ)) / normB μ θ ((n : ℝ) / (μ 0).toReal)))
      (g * Scalar.stableDensity θ (-((j : ℝ) / normB μ θ ((n : ℝ) / (μ 0).toReal))))
    rw [← mul_sub, abs_mul, abs_of_pos hg] at hh
    linarith
  · simpa only [ite_eq_right hr] using h.trans (half_le_self hε.le)

end BGWLeaves.LeafLimitsGeneral.LocalLattice
