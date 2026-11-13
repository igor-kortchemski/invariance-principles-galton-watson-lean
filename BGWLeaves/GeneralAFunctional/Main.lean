module

public import BGWLeaves.GeneralAFunctional.TreeContour
public import BGWLeaves.GeneralAFunctional.WalkMain
public import BGWLeaves.Coding
public import BGWLeaves.ClassicalLimits
public import BGW.Skorokhod.Prefix
public import BGW.Skorokhod.RestrictContinuity
public import BGW.Skorokhod.OptionalGaps
public import BGW.Skorokhod.ContinuousEmbedding
public import BGW.Skorokhod.ScalingMultiplication

/-! Theorem 8.1(II): the joint prefix limit and terminal marginal controls
retain the excursion coupling. The checked walk provider discharges the sole
walk hypothesis of the private assembly theorem. -/
@[expose] public section
namespace BGWLeaves.GeneralAFunctional.Main
open MeasureTheory ProbabilityTheory Filter BGW
open BGW.StableTrees BGW.LocallyFinite BGWLeaves.StableAnalysis
open scoped ENNReal NNReal Topology BoundedContinuousFunction

/-- Marginal weak convergence controls the error of an a.e.-continuous approximation.
The bounded cost avoids any integrability assumption on the path norm. -/
private theorem stop_control {Ω S : Type*} [MeasurableSpace Ω]
    [MetricSpace S] [MeasurableSpace S] [BorelSpace S] [SecondCountableTopology S]
    (P : ℕ → ProbabilityMeasure Ω) (X : Ω → S) (hX : Measurable X)
    {Q : ProbabilityMeasure S} (hlim : Tendsto (fun n => (P n).map X) atTop (𝓝 Q))
    (g : ℕ → S → S) (hg : ∀ j, Measurable (g j))
    (hcont : ∀ j, ∀ᵐ x ∂Q.toMeasure, ContinuousAt (g j) x)
    (happ : ∀ᵐ x ∂Q.toMeasure, Tendsto (fun j => g j x) atTop (𝓝 x))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ L : ℕ → ℝ, Tendsto L atTop (𝓝 0) ∧ ∀ j δ, 0 < δ → ∀ᶠ n in atTop,
      (P n).toMeasure.real {ω | ε ≤ dist (g j (X ω)) (X ω)} ≤ L j + δ := by
  have hbounds (p : S × S) : 0 ≤ min 1 (dist p.1 p.2 / ε) ∧
      min 1 (dist p.1 p.2 / ε) ≤ 1 :=
    ⟨le_min zero_le_one (div_nonneg dist_nonneg hε.le), min_le_left _ _⟩
  let F : (S × S) →ᵇ ℝ :=
    { toFun := fun p => min 1 (dist p.1 p.2 / ε)
      continuous_toFun := by fun_prop
      map_bounded' := ⟨1, fun x y => by
        rw [Real.dist_eq, abs_le]
        constructor <;> linarith [(hbounds x).1, (hbounds x).2, (hbounds y).1, (hbounds y).2]⟩ }
  let J : ℕ → S → S × S := fun j x => (g j x, x)
  have hJ (j : ℕ) : Measurable (J j) := (hg j).prodMk measurable_id
  let L : ℕ → ℝ := fun j => ∫ x, F (J j x) ∂Q.toMeasure
  refine ⟨L, ?_, ?_⟩
  · suffices ht : Tendsto (fun j => ∫ x, F (J j x) ∂Q.toMeasure) atTop
        (𝓝 (∫ _ : S, (0 : ℝ) ∂Q.toMeasure)) by simpa only [integral_zero] using ht
    apply tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ))
    · intro j
      exact (F.continuous.measurable.comp (hJ j)).aestronglyMeasurable
    · exact integrable_const _
    · intro j
      exact ae_of_all _ fun x => by
        change |min 1 (dist (J j x).1 (J j x).2 / ε)| ≤ 1
        rw [abs_of_nonneg (hbounds (J j x)).1]
        exact (hbounds _).2
    · filter_upwards [happ] with x hx
      have hd := (hx.dist (tendsto_const_nhds (x := x))).div_const ε
      have ht := (tendsto_const_nhds (x := (1 : ℝ))).min hd
      simpa only [F, J, BoundedContinuousFunction.coe_mk, dist_self, zero_div, min_eq_right zero_le_one]
        using ht
  · intro j δ hδ
    have ht := BGW.Probability.tendsto_map_of_ae_continuousAt hlim
      (fun _ => (hJ j).aemeasurable)
      ((hcont j).mono fun x hx => hx.prodMk continuousAt_id)
    have hi := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp ht) F
    have hseq (n : ℕ) : ∫ z, F z ∂(((P n).map X).map (J j)).toMeasure =
        ∫ ω, F (J j (X ω)) ∂(P n).toMeasure := by
      change (∫ z, F z ∂(((P n).toMeasure.map X).map (J j))) = _
      rw [Measure.map_map (hJ j) hX]
      exact integral_map ((hJ j).comp hX).aemeasurable F.continuous.aestronglyMeasurable
    have htar : (∫ z, F z ∂(Q.map (J j)).toMeasure) = L j :=
      integral_map (hJ j).aemeasurable F.continuous.aestronglyMeasurable
    rw [htar] at hi
    have hi' := hi.congr fun n => hseq n
    filter_upwards [hi'.eventually (gt_mem_nhds (lt_add_of_pos_right (L j) hδ))] with n hn
    apply le_trans ?_ hn.le
    let A := {ω | ε ≤ dist (g j (X ω)) (X ω)}
    have hA : MeasurableSet A := measurableSet_le measurable_const (((hg j).comp hX).dist hX)
    have hI : Integrable (fun ω => F (J j (X ω))) (P n).toMeasure :=
      (F.integrable ((P n).map (J j ∘ X))).comp_measurable ((hJ j).comp hX)
    have hiA := integral_mono ((integrable_const (1 : ℝ)).indicator hA) hI (fun ω => ?_)
    · rw [integral_indicator_const (1 : ℝ) hA] at hiA
      simpa only [smul_eq_mul, mul_one] using hiA
    · change A.indicator (fun _ => (1 : ℝ)) ω ≤ min 1 (dist (g j (X ω)) (X ω) / ε)
      by_cases hω : ω ∈ A
      · have hh : ε ≤ dist (g j (X ω)) (X ω) := hω
        rw [Set.indicator_of_mem hω, min_eq_left ((le_div_iff₀ hε).mpr (by simpa using hh))]
      · rw [Set.indicator_of_notMem hω]
        exact (hbounds (g j (X ω), X ω)).1


private theorem continuousAt_of_leftLim_eq (f : Skorokhod.D 1 ℝ) (t : Set.Icc (0 : ℝ) 1)
    (ht : Function.leftLim (f : Set.Icc (0 : ℝ) 1 → ℝ) t = f t) : ContinuousAt f t := by
  rw [continuousAt_iff_continuous_left'_right']
  refine ⟨?_, (Skorokhod.isCadlag f).isRightContinuous _⟩
  change Tendsto f (𝓝[<] t) (𝓝 (f t))
  simpa only [ht] using (Skorokhod.isCadlag f).tendsto_nhdsLT_leftLim t

private theorem ae_exc_continuousAt {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    (a : ℝ≥0) (ha : a ∈ Set.Ioo (0 : ℝ≥0) 1) :
    ∀ᵐ (f : Skorokhod.D 1 ℝ) ∂(levyExcLaw θ).toMeasure,
      ContinuousAt (f : Set.Icc (0 : ℝ) 1 → ℝ) ⟨a, a.coe_nonneg, ha.2.le⟩ := by
  let t : Set.Icc (0 : ℝ) 1 := ⟨a, a.coe_nonneg, ha.2.le⟩
  have hl : ∀ᵐ (f : Skorokhod.D 1 ℝ) ∂(levyExcLaw θ).toMeasure, Function.leftLim f t = f t := by
    change ∀ᵐ f ∂((unitExcursionLaw θ).toMeasure.map (excursionRestrict 1)), _
    apply (ae_map_iff (measurable_excursionRestrict 1).aemeasurable
      (measurableSet_eq_fun (Skorokhod.measurable_leftLim_eval t) (Skorokhod.measurable_eval t))).mpr
    filter_upwards [levyExcLaw_noFixedJump hθ a ha] with e he
    erw [leftLim_excursionRestrict 1 a ha.1 ha.2.le]
    exact he
  exact hl.mono fun f hf => continuousAt_of_leftLim_eq f t hf

private theorem ae_exc_continuousAt_one {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ (f : Skorokhod.D 1 ℝ) ∂(levyExcLaw θ).toMeasure,
      ContinuousAt (f : Set.Icc (0 : ℝ) 1 → ℝ) ⟨1, zero_le_one, le_rfl⟩ := by
  filter_upwards [levyExcLaw_endpoints_pos hθ] with f hf
  exact continuousAt_of_leftLim_eq f _ (hf.2.2.2.trans hf.2.2.1.symm)

private theorem tendsto_stop_continuous {a : ℕ → ℝ}
    (ha : ∀ j, a j < 1) (ht : Tendsto a atTop (𝓝 1)) (f : C(Set.Icc (0 : ℝ) 1, ℝ)) :
    Tendsto (fun j => Skorokhod.stopContinuous (a j) f) atTop (𝓝 f) := by
  apply (Skorokhod.isClosedEmbedding_ofContinuous (T := 1) (E := ℝ)).isEmbedding.tendsto_nhds_iff.mpr
  have haLT : Tendsto a atTop (𝓝[<] (1 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨ht, Filter.Eventually.of_forall ha⟩
  have h := (Skorokhod.tendsto_stop_nhdsLT zero_lt_one (f := Skorokhod.ofContinuous f)
    f.continuous.continuousAt).comp haLT
  exact h

private def stopPair (a : ℝ) (p : Skorokhod.D 1 ℝ × C(Set.Icc (0 : ℝ) 1, ℝ)) :=
  (Skorokhod.stop a p.1, Skorokhod.stopContinuous a p.2)

private def extendPair (a : ℝ≥0) (ha : a ≤ 1)
    (p : Skorokhod.D (a : ℝ) ℝ × C(Set.Icc (0 : ℝ) a, ℝ)) :
    Skorokhod.D 1 ℝ × C(Set.Icc (0 : ℝ) 1, ℝ) :=
  (Skorokhod.extendConst a.coe_nonneg (show (a : ℝ) ≤ 1 from ha) p.1,
    Skorokhod.extendContinuous (T := 1) a.coe_nonneg p.2)

private theorem continuous_extendPair (a : ℝ≥0) (ha : a ≤ 1) : Continuous (extendPair a ha) :=
  ((Skorokhod.lipschitzWith_one_extendConst _ _).continuous.comp continuous_fst).prodMk
    ((Skorokhod.lipschitzWith_one_extendContinuous _).continuous.comp continuous_snd)

private theorem extend_restrictPair (a : ℝ≥0) (ha : a ≤ 1)
    (p : Skorokhod.D 1 ℝ × C(Set.Icc (0 : ℝ) 1, ℝ)) :
    extendPair a ha (restrictPair ha p) = stopPair a p := by
  apply Prod.ext
  · exact (Skorokhod.stop_eq_extendConst_restrict a.coe_nonneg (show (a : ℝ) ≤ 1 from ha) p.1).symm
  · ext t
    apply congrArg p.2
    apply Subtype.ext
    exact (max_eq_right (le_min t.2.1 a.coe_nonneg)).symm


private theorem measurable_stopPair (a : ℝ≥0) (ha : a ≤ 1) : Measurable (stopPair a) :=
  ((Skorokhod.measurable_stop_of_nonneg a.coe_nonneg (show (a : ℝ) ≤ 1 from ha)).comp
    measurable_fst).prodMk ((Skorokhod.lipschitzWith_one_stopContinuous _).continuous.measurable.comp
      measurable_snd)

private theorem treePair_restrict (B : ℕ → ℝ) (a : ℝ≥0) (ha : a ≤ 1) (τ : LocallyFinite.Tree) :
    TailPair.treePairPath B (treeSize τ) a τ =
      restrictPair ha ((codingTriple B τ).1, (codingTriple B τ).2.2) := by
  apply Prod.ext
  · rfl
  · ext t
    simp only [TailPair.treePairPath, TailPair.treeHeightPath,
      dite_eq_left (TailPair.continuous_treeHeightLin _), codingTriple, rescaledHeight,
      restrictPair, ContinuousMap.coe_mk]
    rfl

private theorem tendsto_codingHeight {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ}
    (hc : IsCritical μ) (hne : μ 1 ≠ 1) (hap : Aperiodic μ)
    (hB : IsRealStableAttracted (realOffspringStepLaw μ) θ B)
 {A : Set ℕ} {q : ℕ → ℕ}
    (hqtop : Tendsto q atTop atTop) (hq : ∀ k, ZetaAAdmissible μ A (q k)) :
    Tendsto (fun k => (zetaATreeLaw μ A (q k)).map (fun τ => (codingTriple B τ).2.2)) atTop
      (𝓝 ((excLaw θ).map Prod.snd)) := by
  have ht := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _
    (TreeContour.thm_cvG_ii hc hne hap hB hqtop hq) continuous_snd
  have hlim : ((excLaw θ).map (fun p => (p.2, p.2))).map Prod.snd =
      (excLaw θ).map Prod.snd := by
    apply Subtype.ext
    exact Measure.map_map measurable_snd (measurable_snd.prodMk measurable_snd)
  rw [hlim] at ht
  apply ht.congr
  intro k
  apply Subtype.ext
  exact Measure.map_map measurable_snd (measurable_snd.comp (measurable_codingTriple B))

/-- Whole-interval joint walk/height convergence. Marginals control stopping errors;
the stopped joint laws retain precisely the coupling from Lemma 5.8. -/
private theorem tendsto_codingPair {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ}
    (hc : IsCritical μ) (hne : μ 1 ≠ 1) (hap : Aperiodic μ)
    (hB : IsRealStableAttracted (realOffspringStepLaw μ) θ B)
 {A : Set ℕ} {q : ℕ → ℕ}
    (hqtop : Tendsto q atTop atTop) (hq : ∀ k, ZetaAAdmissible μ A (q k))
    (hw : Tendsto (fun k => (zetaATreeLaw μ A (q k)).map
      (fun τ => rescaledLuka (treeSize τ) (B (treeSize τ)) τ)) atTop (𝓝 (levyExcLaw θ))) :
    Tendsto (fun k => (zetaATreeLaw μ A (q k)).map
      (fun τ => ((codingTriple B τ).1, (codingTriple B τ).2.2))) atTop (𝓝 (excLaw θ)) := by
  let P := fun k => zetaATreeLaw μ A (q k)
  let X := fun τ => (codingTriple B τ).1
  let H := fun τ => (codingTriple B τ).2.2
  let Y := fun τ => (X τ, H τ)
  have hX : Measurable X := measurable_fst.comp (measurable_codingTriple B)
  have hH : Measurable H := measurable_snd.comp (measurable_snd.comp (measurable_codingTriple B))
  have hY : Measurable Y := hX.prodMk hH
  let a : ℕ → ℝ≥0 := fun j => ⟨1 - 1 / ((j : ℝ) + 2), by
    have hj := Nat.cast_nonneg (α := ℝ) j
    exact sub_nonneg.mpr ((div_le_one (by positivity : (0 : ℝ) < j + 2)).mpr (by linarith))⟩
  have ha (j : ℕ) : 0 < a j ∧ a j < 1 := by
    have hj := Nat.cast_nonneg (α := ℝ) j
    have hd : (0 : ℝ) < j + 2 := by positivity
    constructor
    · exact sub_pos.mpr ((div_lt_one hd).mpr (by linarith))
    · exact sub_lt_self _ (by positivity)
  have hatop : Tendsto (fun j => (a j : ℝ)) atTop (𝓝 1) := by
    have ht := (tendsto_const_nhds (x := (1 : ℝ))).sub
      ((tendsto_atTop_add_const_right atTop (2 : ℝ)
        tendsto_natCast_atTop_atTop).const_div_atTop (1 : ℝ))
    change Tendsto (fun j : ℕ => 1 - 1 / ((j : ℝ) + 2)) atTop (𝓝 1)
    simpa only [sub_zero] using ht
  have haLT : Tendsto (fun j => (a j : ℝ)) atTop (𝓝[<] (1 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hatop, Eventually.of_forall fun j => (ha j).2⟩
  have hWapp : ∀ᵐ f ∂(levyExcLaw θ).toMeasure,
      Tendsto (fun j => Skorokhod.stop (a j) f) atTop (𝓝 f) := by
    filter_upwards [ae_exc_continuousAt_one hB.index_mem] with f hf
    exact (Skorokhod.tendsto_stop_nhdsLT zero_lt_one hf).comp haLT
  have hHapp : ∀ᵐ f ∂((excLaw θ).map Prod.snd).toMeasure,
      Tendsto (fun j => Skorokhod.stopContinuous (a j) f) atTop (𝓝 f) :=
    ae_of_all _ fun f => tendsto_stop_continuous (fun j => (ha j).2) hatop f
  have hQapp : ∀ᵐ p ∂(excLaw θ).toMeasure,
      Tendsto (fun j => stopPair (a j) p) atTop (𝓝 p) := by
    have hw := hWapp
    rw [← excLaw_map_fst θ] at hw
    have hw' := ae_of_ae_map measurable_fst.aemeasurable hw
    filter_upwards [hw'] with p hp
    exact hp.prodMk_nhds (tendsto_stop_continuous (fun j => (ha j).2) hatop p.2)
  apply BGW.Probability.tendsto_of_tendsto_approx P (fun _ => hY)
    (X := fun j _ => stopPair (a j) ∘ Y)
    (Z := fun j => (excLaw θ).map (stopPair (a j)))
    (fun j _ => (measurable_stopPair _ (ha j).2.le).comp hY)
  · intro j
    have ht := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _
      (TreeClockTransport.tendsto_sizePair hc hne hap hB (ha j) hqtop hq)
      (continuous_extendPair (a j) (ha j).2.le)
    have hlim : ((excLaw θ).map (restrictPair (ha j).2.le)).map
        (extendPair (a j) (ha j).2.le) = (excLaw θ).map (stopPair (a j)) := by
      apply Subtype.ext
      change ((excLaw θ).toMeasure.map (restrictPair (ha j).2.le)).map
        (extendPair (a j) (ha j).2.le) = (excLaw θ).toMeasure.map (stopPair (a j))
      erw [Measure.map_map (continuous_extendPair _ _).measurable (measurable_restrictPair _)]
      congr 1
      funext p
      exact extend_restrictPair _ _ p
    rw [hlim] at ht
    apply ht.congr
    intro k
    apply Subtype.ext
    change ((P k).toMeasure.map _).map _ = _
    rw [Measure.map_map (continuous_extendPair _ _).measurable
      (TreeSize.measurable_sizePair B (a j))]
    congr 1
    funext τ
    change extendPair (a j) (ha j).2.le
      (TailPair.treePairPath B (treeSize τ) (a j) τ) = _
    rw [treePair_restrict]
    exact extend_restrictPair _ _ (Y τ)
  · rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
    intro F
    simp_rw [ProbabilityMeasure.toMeasure_map,
      integral_map (measurable_stopPair _ (ha _).2.le).aemeasurable F.continuous.aestronglyMeasurable]
    apply tendsto_integral_of_dominated_convergence (fun _ => ‖F‖)
    · intro j
      exact (F.continuous.measurable.comp (measurable_stopPair _ (ha j).2.le)).aestronglyMeasurable
    · exact integrable_const _
    · intro j
      exact ae_of_all _ fun p => F.norm_coe_le_norm _
    · exact hQapp.mono fun p hp => F.continuous.continuousAt.tendsto.comp hp
  · intro ε hε
    obtain ⟨Lw, hLw, hbw⟩ := stop_control P X hX
      hw
      (fun j => Skorokhod.stop (a j))
      (fun j => Skorokhod.measurable_stop_of_nonneg (a j).coe_nonneg (ha j).2.le)
      (fun j => (ae_exc_continuousAt hB.index_mem (a j) (ha j)).mono fun f hf =>
        Skorokhod.continuousAt_stop (a j).coe_nonneg (ha j).2.le hf) hWapp hε
    obtain ⟨Lh, hLh, hbh⟩ := stop_control P H hH
      (tendsto_codingHeight hc hne hap hB hqtop hq)
      (fun j => Skorokhod.stopContinuous (a j))
      (fun j => (Skorokhod.lipschitzWith_one_stopContinuous _).continuous.measurable)
      (fun j => ae_of_all _ fun _ => (Skorokhod.lipschitzWith_one_stopContinuous _).continuous.continuousAt)
      hHapp hε
    rw [Metric.tendsto_nhds]
    intro η hη
    filter_upwards [(hLw.add hLh).eventually
      (gt_mem_nhds (show (0 : ℝ) + 0 < η / 4 by linarith))] with j hj
    have hnn : 0 ≤ limsup (fun n => (P n).toMeasure.real
        {ω | ε ≤ dist ((stopPair (a j) ∘ Y) ω) (Y ω)}) atTop :=
      le_limsup_of_frequently_le (Frequently.of_forall fun _ => measureReal_nonneg)
        (isBoundedUnder_of ⟨1, fun _ => measureReal_le_one⟩)
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hnn]
    apply lt_of_le_of_lt _ (half_lt_self hη)
    apply limsup_le_of_le (Filter.isCoboundedUnder_le_of_le atTop fun _ => measureReal_nonneg)
    filter_upwards [hbw j (η / 8) (by positivity), hbh j (η / 8) (by positivity)] with n hnw hnh
    have hsub : {ω | ε ≤ dist ((stopPair (a j) ∘ Y) ω) (Y ω)} ⊆
        {ω | ε ≤ dist (Skorokhod.stop (a j) (X ω)) (X ω)} ∪
        {ω | ε ≤ dist (Skorokhod.stopContinuous (a j) (H ω)) (H ω)} := by
      intro ω hω
      simpa only [Set.mem_ofPred_eq, Set.mem_union, Function.comp_apply, stopPair, Y, Prod.dist_eq, le_max_iff] using hω
    exact (measureReal_mono hsub).trans ((measureReal_union_le _ _).trans (by linarith))

private theorem coding_contour_height_error {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ}
    (hc : IsCritical μ) (hne : μ 1 ≠ 1) (hap : Aperiodic μ)
    (hB : IsRealStableAttracted (realOffspringStepLaw μ) θ B)
 {A : Set ℕ} {q : ℕ → ℕ}
    (hqtop : Tendsto q atTop atTop) (hq : ∀ k, ZetaAAdmissible μ A (q k))
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun k => (zetaATreeLaw μ A (q k)).toMeasure.real
      {τ | ε < dist (codingTriple B τ).2.1 (codingTriple B τ).2.2}) atTop (𝓝 0) := by
  let D : Set (C(unitInterval, ℝ) × C(unitInterval, ℝ)) := {p | ε < dist p.1 p.2}
  have hA : MeasurableSet D := isOpen_lt continuous_const (continuous_fst.dist continuous_snd) |>.measurableSet
  let d : Skorokhod.D 1 ℝ × C(unitInterval, ℝ) → C(unitInterval, ℝ) × C(unitInterval, ℝ) :=
    fun p => (p.2, p.2)
  have hd : Measurable d := measurable_snd.prodMk measurable_snd
  have hempty : d ⁻¹' D = ∅ := by ext p; simp [D, d, hε.le]
  have hfront : d ⁻¹' frontier D = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro p hp
    have hh := frontier_lt_subset_eq continuous_const (continuous_fst.dist continuous_snd) hp
    change ε = dist p.2 p.2 at hh
    rw [dist_self] at hh
    exact hε.ne' hh
  have hnull : ((excLaw θ).map d).toMeasure (frontier D) = 0 := by
    rw [ProbabilityMeasure.toMeasure_map, Measure.map_apply hd isClosed_frontier.measurableSet,
      hfront, measure_empty]
  have hzero : ((excLaw θ).map d).toMeasure D = 0 := by
    rw [ProbabilityMeasure.toMeasure_map, Measure.map_apply hd hA, hempty, measure_empty]
  have ht := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto'
    (TreeContour.thm_cvG_ii hc hne hap hB hqtop hq) hnull
  rw [hzero] at ht
  have hr := (ENNReal.tendsto_toReal (by simp : (0 : ℝ≥0∞) ≠ ∞)).comp ht
  have hseq (k : ℕ) :
      (ENNReal.toReal ∘ fun i => (((zetaATreeLaw μ A (q i)).map
        (fun τ => (codingTriple B τ).2)).toMeasure D)) k =
      (zetaATreeLaw μ A (q k)).toMeasure.real
        {τ | ε < dist (codingTriple B τ).2.1 (codingTriple B τ).2.2} := by
    change ((zetaATreeLaw μ A (q k)).toMeasure.map (fun τ => (codingTriple B τ).2) D).toReal = _
    erw [Measure.map_apply (measurable_snd.comp (measurable_codingTriple B)) hA]
    rfl
  exact hr.congr fun k => hseq k

/-- Introduction (II), retaining the joint walk/height coupling from Lemma 5.8. -/
private theorem assembly_of_walk {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hap : Aperiodic μ) (hB : IsRealStableAttracted (realOffspringStepLaw μ) θ B)
 {A : Set ℕ} {q : ℕ → ℕ}
    (hqtop : Tendsto q atTop atTop) (hq : ∀ k, ZetaAAdmissible μ A (q k))
    (hw : Tendsto (fun k => (zetaATreeLaw μ A (q k)).map
      (fun τ => rescaledLuka (treeSize τ) (B (treeSize τ)) τ)) atTop (𝓝 (levyExcLaw θ))) :
    Tendsto (fun k => (zetaATreeLaw μ A (q k)).map (codingTriple B)) atTop (𝓝 (excTripleLaw θ)) := by
  let d : Skorokhod.D 1 ℝ × C(unitInterval, ℝ) →
      Skorokhod.D 1 ℝ × C(unitInterval, ℝ) × C(unitInterval, ℝ) := fun p => (p.1, p.2, p.2)
  have hd : Continuous d := continuous_fst.prodMk (continuous_snd.prodMk continuous_snd)
  have ht := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _
    (tendsto_codingPair hc hne hap hB hqtop hq hw) hd
  have hseq (k : ℕ) : ((zetaATreeLaw μ A (q k)).map
      (fun τ => ((codingTriple B τ).1, (codingTriple B τ).2.2))).map d =
      (zetaATreeLaw μ A (q k)).map
        (fun τ => ((codingTriple B τ).1, (codingTriple B τ).2.2, (codingTriple B τ).2.2)) := by
    apply Subtype.ext
    exact Measure.map_map hd.measurable
      ((measurable_fst.comp (measurable_codingTriple B)).prodMk
        (measurable_snd.comp (measurable_snd.comp (measurable_codingTriple B))))
  apply BGW.MetricMeasure.tendsto_probabilityMap_of_error_probability
    (fun k => zetaATreeLaw μ A (q k)) (fun _ => measurable_codingTriple B)
    (fun _ => (measurable_fst.comp (measurable_codingTriple B)).prodMk
      ((measurable_snd.comp (measurable_snd.comp (measurable_codingTriple B))).prodMk
        (measurable_snd.comp (measurable_snd.comp (measurable_codingTriple B))))) ?_
    (ht.congr fun k => hseq k)
  intro ε hε
  have hd (τ : LocallyFinite.Tree) :
      dist (codingTriple B τ) ((codingTriple B τ).1, (codingTriple B τ).2.2, (codingTriple B τ).2.2) =
        dist (codingTriple B τ).2.1 (codingTriple B τ).2.2 := by
    generalize codingTriple B τ = p
    rcases p with ⟨w, c, h⟩
    simp only [dist_prod_same_left, dist_prod_same_right]
  simpa only [Function.comp_apply, hd] using
    coding_contour_height_error hc hne hap hB hqtop hq hε



/-- Theorem 8.1(II), with the frozen arbitrary-norming signature. -/
theorem thm_general_II {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ} {A : Set ℕ} (hA : A.Nonempty)
    (hc : IsCritical μ) (hne : μ 1 ≠ 1) (hap : Aperiodic μ)
    (hB : IsRealStableAttracted (realOffspringStepLaw μ) θ B)
    (hAfin : ¬ Integrable (fun z : ℤ => (z : ℝ) ^ 2) (stepLaw μ) → A.Finite ∨ Aᶜ.Finite)
    {q : ℕ → ℕ} (hqtop : Tendsto q atTop atTop) (hq : ∀ k, ZetaAAdmissible μ A (q k)) :
    Tendsto (fun k => (zetaATreeLaw μ A (q k)).map (codingTriple B)) atTop
      (𝓝 (excTripleLaw θ)) := by
  exact assembly_of_walk hc hne hap hB hqtop hq
    (WalkMain.general_walk_tendsto hA hc hne hap hB hAfin hqtop hq)


/-- The corrected canonical-norming specialization. -/
theorem thm_general_II_canonical {μ : PMF ℕ} {θ : ℝ} {A : Set ℕ} (hA : A.Nonempty)
    (hc : IsCritical μ) (hne : μ 1 ≠ 1) (hap : Aperiodic μ) (hDA : ∃ a, StableDomain μ θ a)
    (hAfin : ¬ Integrable (fun z : ℤ => (z : ℝ) ^ 2) (stepLaw μ) → A.Finite ∨ Aᶜ.Finite)
    {q : ℕ → ℕ} (hqtop : Tendsto q atTop atTop) (hq : ∀ k, ZetaAAdmissible μ A (q k)) :
    Tendsto (fun k => (zetaATreeLaw μ A (q k)).map (codingTriple (norming (stepLaw μ) θ))) atTop
      (𝓝 (excTripleLaw θ)) := by
  exact thm_general_II hA hc hne hap (isRealStableAttracted_norming hc hne hDA) hAfin hqtop hq


end BGWLeaves.GeneralAFunctional.Main
