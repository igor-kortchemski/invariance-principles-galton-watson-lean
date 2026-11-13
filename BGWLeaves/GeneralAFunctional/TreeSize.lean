module

public import BGWLeaves.GeneralAFunctional.TreeSurvival
public import BGWLeaves.GeneralAFunctional.TreeProbability
public import BGWLeaves.GeneralAFunctional.TreeMirror
public import BGWLeaves.Coding.Norming
public import BGW.StableTrees.Attraction.Norming
public import BGW.StableTrees.Attraction.TransformConvergence
public import BGW.StableTrees.ExactPair

@[expose] public section
namespace BGWLeaves.GeneralAFunctional.TreeSize
open MeasureTheory ProbabilityTheory Filter Set BGW
open BGW.StableTrees BGW.LocallyFinite BGWLeaves.StableAnalysis
open BGW.StableTrees.TailPair BGWLeaves.GeneralA.Marked
open BGWLeaves.GeneralAFunctional.TreeEvents BGWLeaves.GeneralAFunctional.TreeSurvival
open BGWLeaves.GeneralA.MarkedLaw
open scoped ENNReal NNReal Topology

theorem treeACount_le_size (A : Set ℕ) (t : PlaneTree) : treeACount A t ≤ t.size := by
  classical
  exact (List.countP_le_length).trans_eq t.length_degrees

theorem ae_finite_marks {μ : PMF ℕ} {A : Set ℕ} {n : ℕ} (hn : ZetaAAdmissible μ A n) :
    ∀ᵐ T ∂(zetaATreeLaw μ A n).toMeasure, ∃ t : PlaneTree,
      t.toLocallyFinite = T ∧ treeACount A t = n := by
  filter_upwards [ae_conditioning_event hn] with T hT
  obtain ⟨t, rfl⟩ := (exists_toLocallyFinite_iff T).mpr hT.1
  exact ⟨t, rfl, ENat.natCast_inj.mp (by simpa only [zetaA_toLocallyFinite] using hT.2)⟩

noncomputable def sizePair (B : ℕ → ℝ) (a : ℝ≥0) (τ : LocallyFinite.Tree) :=
  TailPair.treePairPath B (treeSize τ) a τ

theorem measurable_sizePair (B : ℕ → ℝ) (a : ℝ≥0) : Measurable (sizePair B a) :=
  measurable_comp_nat measurable_treeSize (fun n => TailPair.measurable_treePairPath B n a)

theorem ae_continuousAt_exc_prefix {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    {a b : ℝ≥0} (ha : 0 < a) (hab : a ≤ b) (hb : b < 1) :
    ∀ᵐ z ∂((excLaw θ).map (restrictPair hb.le)).toMeasure,
      ContinuousAt (z.1 : Set.Icc (0 : ℝ) b → ℝ)
        ⟨(a : ℝ), a.coe_nonneg, NNReal.coe_le_coe.mpr hab⟩ := by
  let t : Set.Icc (0 : ℝ) b := ⟨a, a.coe_nonneg, NNReal.coe_le_coe.mpr hab⟩
  have hleft : ∀ᵐ z ∂((excLaw θ).map (restrictPair hb.le)).toMeasure,
      Function.leftLim (z.1 : Set.Icc (0 : ℝ) b → ℝ) t = z.1 t := by
    change ∀ᵐ z ∂(((unitExcursionLaw θ : Measure Excursion).map (excursionPair θ 1)).map
      (restrictPair hb.le)), _
    rw [Measure.map_map (measurable_restrictPair hb.le) (measurable_excursionPair θ 1)]
    apply (ae_map_iff ((measurable_restrictPair hb.le).comp
      (measurable_excursionPair θ 1)).aemeasurable
      (measurableSet_eq_fun ((Skorokhod.measurable_leftLim_eval t).comp measurable_fst)
        ((Skorokhod.measurable_eval t).comp measurable_fst))).mpr
    filter_upwards [levyExcLaw_noFixedJump hθ a ⟨ha, hab.trans_lt hb⟩] with e he
    change Function.leftLim (excursionRestrict b e) t = excursionRestrict b e t
    rw [leftLim_excursionRestrict b a ha hab e]
    exact he
  filter_upwards [hleft] with z hz
  rw [continuousAt_iff_continuous_left'_right']
  refine ⟨?_, (Skorokhod.isCadlag z.1).isRightContinuous _⟩
  change Tendsto z.1 (𝓝[<] t) (𝓝 (z.1 t))
  simpa only [hz] using (Skorokhod.isCadlag z.1).tendsto_nhdsLT_leftLim t


theorem exists_stableDomain_ratio {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ}
    (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hB : IsRealStableAttracted (realOffspringStepLaw μ) θ B) :
    ∃ B' : ℕ → ℝ, StableDomain μ θ B' ∧
      Tendsto (fun n => B n / B' n) atTop (𝓝 1) := by
  have hatt := BGWLeaves.Coding.Norming.isStableAttracted_of_isRealStableAttracted hB
  have hmean : Attraction.mean (stepLaw μ) = 0 := Attraction.mean_stepLaw hc
  have hattm : Attraction.IsStableAttracted (stepLaw μ) θ
      (Attraction.mean (stepLaw μ)) B := by rwa [hmean]
  have hcanm := Attraction.Norming.locallimit_i (stepLaw μ)
    (Attraction.stepLaw_lt_neg_one μ) (Attraction.integrable_stepLaw hc) ⟨B, hattm⟩
  have hmono := (Attraction.Norming.locallimit_ii (stepLaw μ)
    (Attraction.stepLaw_lt_neg_one μ) (Attraction.integrable_stepLaw hc) ⟨B, hattm⟩).1
  have hcan : Attraction.IsStableAttracted (stepLaw μ) θ 0
      (Attraction.norming (stepLaw μ) θ) := by rwa [hmean] at hcanm
  obtain ⟨B', hEq, hdom⟩ := hcan.exists_stableDomain hc hne hmono
  refine ⟨B', hdom, ?_⟩
  have hratio := Attraction.TransformConvergence.norming_ratio_tendsto_one
    (stepLaw μ) hatt hcan
  apply hratio.congr'
  filter_upwards [hEq] with n hn
  rw [hn]


theorem probability_size_tendsto {μ : PMF ℕ} {A : Set ℕ} {q : ℕ → ℕ}
    (hqtop : Tendsto q atTop atTop) (hq : ∀ k, ZetaAAdmissible μ A (q k))
    {f : ℕ → ℝ} {c : ℝ} (hf : Tendsto f atTop (𝓝 c)) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun k => (zetaATreeLaw μ A (q k)).toMeasure.real
      {τ | ε < dist (f (treeSize τ)) c}) atTop (𝓝 0) := by
  apply tendsto_const_nhds.congr'
  obtain ⟨N, hN⟩ := eventually_atTop.mp ((Metric.tendsto_nhds.mp hf) ε hε)
  filter_upwards [hqtop.eventually_ge_atTop N] with k hk
  have hmem := ae_finite_marks (hq k)
  have hz : (zetaATreeLaw μ A (q k)).toMeasure
      {τ | ε < dist (f (treeSize τ)) c} = 0 := by
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [hmem] with τ hτ
    obtain ⟨t, rfl, ht⟩ := hτ
    rw [treeSize_toLocallyFinite]
    exact not_lt_of_ge (hN t.size (hk.trans (ht ▸ treeACount_le_size A t))).le
  simp only [Measure.real, hz, ENNReal.toReal_zero]


end BGWLeaves.GeneralAFunctional.TreeSize
