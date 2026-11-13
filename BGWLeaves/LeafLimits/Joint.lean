module

public import BGWLeaves.LeafLimits.Defs
public import BGWLeaves.Coding
public import BGWLeaves.ClassicalLimits
public import BGWLeaves.LeafLimits.ContourHeight
public import BGWLeaves.LeafLimits.Walk
public import BGW.Skorokhod.Prefix
public import BGW.Skorokhod.RestrictContinuity
public import BGW.Skorokhod.OptionalGaps
public import BGW.StableTrees.RealAttractionBounds
public import BGW.Skorokhod.ContinuousEmbedding
public import BGW.Skorokhod.ScalingMultiplication

/-!
# M13 provider `Joint`

Introduction (II), its canonical corollary, and Remark 5.10, at the frozen signatures.

The local joint walk/height law is retained from Lemma 5.8 through the larger-horizon
perturbation in ContourHeight. Stopping both coordinates extends this joint law to the
whole interval. The proved marginal limits control only the stopping errors, using a bounded
continuous distance cost and a.s. continuity at the terminal endpoint. Thus the argument
retains the excursion coupling required by R7. The vanishing contour/height distance adds
the contour coordinate to this joint pair.

Remark 5.10 uses size concentration, uniform regular variation, and joint Slutsky for the
two amplitude factors. The canonical corollary shifts beyond the finitely many inadmissible
indices. Inputs are the provider modules of this package, and the sealed M11 and M12 packages.
-/

@[expose] public section

namespace BGWLeaves.LeafLimits.Joint

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
    (hnl : ¬ IsLatticeLaw (etaLaw μ)) {q : ℕ → ℕ}
    (hqtop : Tendsto q atTop atTop) (hq : ∀ k, LeafAdmissible μ (q k)) :
    Tendsto (fun k => (leafTreeLaw μ (q k)).map (fun τ => (codingTriple B τ).2.2)) atTop
      (𝓝 ((excLaw θ).map Prod.snd)) := by
  have ht := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _
    (ContourHeight.thm_cvG_ii hc hne hap hB hnl hqtop hq) continuous_snd
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
    (hnl : ¬ IsLatticeLaw (etaLaw μ)) {q : ℕ → ℕ}
    (hqtop : Tendsto q atTop atTop) (hq : ∀ k, LeafAdmissible μ (q k)) :
    Tendsto (fun k => (leafTreeLaw μ (q k)).map
      (fun τ => ((codingTriple B τ).1, (codingTriple B τ).2.2))) atTop (𝓝 (excLaw θ)) := by
  let P := fun k => leafTreeLaw μ (q k)
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
      (ContourHeight.tendsto_treePairPath_treeSize hc hne hap hB hnl (ha j) hqtop hq)
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
      (measurable_comp_nat measurable_treeSize (fun n => TailPair.measurable_treePairPath B n (a j)))]
    congr 1
    funext τ
    rw [Function.comp_apply, treePair_restrict]
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
      (Walk.thm_cvW3 hc hne hap hB hnl hqtop hq)
      (fun j => Skorokhod.stop (a j))
      (fun j => Skorokhod.measurable_stop_of_nonneg (a j).coe_nonneg (ha j).2.le)
      (fun j => (ae_exc_continuousAt hB.index_mem (a j) (ha j)).mono fun f hf =>
        Skorokhod.continuousAt_stop (a j).coe_nonneg (ha j).2.le hf) hWapp hε
    obtain ⟨Lh, hLh, hbh⟩ := stop_control P H hH
      (tendsto_codingHeight hc hne hap hB hnl hqtop hq)
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
    (hnl : ¬ IsLatticeLaw (etaLaw μ)) {q : ℕ → ℕ}
    (hqtop : Tendsto q atTop atTop) (hq : ∀ k, LeafAdmissible μ (q k))
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun k => (leafTreeLaw μ (q k)).toMeasure.real
      {τ | ε < dist (codingTriple B τ).2.1 (codingTriple B τ).2.2}) atTop (𝓝 0) := by
  let A : Set (C(unitInterval, ℝ) × C(unitInterval, ℝ)) := {p | ε < dist p.1 p.2}
  have hA : MeasurableSet A := isOpen_lt continuous_const (continuous_fst.dist continuous_snd) |>.measurableSet
  let d : Skorokhod.D 1 ℝ × C(unitInterval, ℝ) → C(unitInterval, ℝ) × C(unitInterval, ℝ) :=
    fun p => (p.2, p.2)
  have hd : Measurable d := measurable_snd.prodMk measurable_snd
  have hempty : d ⁻¹' A = ∅ := by ext p; simp [A, d, hε.le]
  have hfront : d ⁻¹' frontier A = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro p hp
    have hh := frontier_lt_subset_eq continuous_const (continuous_fst.dist continuous_snd) hp
    change ε = dist p.2 p.2 at hh
    rw [dist_self] at hh
    exact hε.ne' hh
  have hnull : ((excLaw θ).map d).toMeasure (frontier A) = 0 := by
    rw [ProbabilityMeasure.toMeasure_map, Measure.map_apply hd isClosed_frontier.measurableSet,
      hfront, measure_empty]
  have hzero : ((excLaw θ).map d).toMeasure A = 0 := by
    rw [ProbabilityMeasure.toMeasure_map, Measure.map_apply hd hA, hempty, measure_empty]
  have ht := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto'
    (ContourHeight.thm_cvG_ii hc hne hap hB hnl hqtop hq) hnull
  rw [hzero] at ht
  have hr := (ENNReal.tendsto_toReal (by simp : (0 : ℝ≥0∞) ≠ ∞)).comp ht
  have hseq (k : ℕ) :
      (ENNReal.toReal ∘ fun i => (((leafTreeLaw μ (q i)).map
        (fun τ => (codingTriple B τ).2)).toMeasure A)) k =
      (leafTreeLaw μ (q k)).toMeasure.real
        {τ | ε < dist (codingTriple B τ).2.1 (codingTriple B τ).2.2} := by
    change ((leafTreeLaw μ (q k)).toMeasure.map (fun τ => (codingTriple B τ).2) A).toReal = _
    erw [Measure.map_apply (measurable_snd.comp (measurable_codingTriple B)) hA]
    rfl
  exact hr.congr fun k => hseq k

/-- Introduction (II), retaining the joint walk/height coupling from Lemma 5.8. -/
theorem intro_II {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hap : Aperiodic μ) (hB : IsRealStableAttracted (realOffspringStepLaw μ) θ B)
    (hnl : ¬ IsLatticeLaw (etaLaw μ)) {q : ℕ → ℕ}
    (hqtop : Tendsto q atTop atTop) (hq : ∀ k, LeafAdmissible μ (q k)) :
    Tendsto (fun k => (leafTreeLaw μ (q k)).map (codingTriple B)) atTop (𝓝 (excTripleLaw θ)) := by
  let d : Skorokhod.D 1 ℝ × C(unitInterval, ℝ) →
      Skorokhod.D 1 ℝ × C(unitInterval, ℝ) × C(unitInterval, ℝ) := fun p => (p.1, p.2, p.2)
  have hd : Continuous d := continuous_fst.prodMk (continuous_snd.prodMk continuous_snd)
  have ht := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _
    (tendsto_codingPair hc hne hap hB hnl hqtop hq) hd
  have hseq (k : ℕ) : ((leafTreeLaw μ (q k)).map
      (fun τ => ((codingTriple B τ).1, (codingTriple B τ).2.2))).map d =
      (leafTreeLaw μ (q k)).map
        (fun τ => ((codingTriple B τ).1, (codingTriple B τ).2.2, (codingTriple B τ).2.2)) := by
    apply Subtype.ext
    exact Measure.map_map hd.measurable
      ((measurable_fst.comp (measurable_codingTriple B)).prodMk
        (measurable_snd.comp (measurable_snd.comp (measurable_codingTriple B))))
  apply BGW.MetricMeasure.tendsto_probabilityMap_of_error_probability
    (fun k => leafTreeLaw μ (q k)) (fun _ => measurable_codingTriple B)
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
    coding_contour_height_error hc hne hap hB hnl hqtop hq hε

private theorem probability_continuous_pair {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, ProbabilityMeasure (Ω n)) {X Y : ∀ n, Ω n → ℝ} {c d : ℝ}
    (hX : ∀ ε > 0, Tendsto (fun n => (P n).toMeasure.real {ω | ε < dist (X n ω) c}) atTop (𝓝 0))
    (hY : ∀ ε > 0, Tendsto (fun n => (P n).toMeasure.real {ω | ε < dist (Y n ω) d}) atTop (𝓝 0))
    {E : Type*} [PseudoMetricSpace E] {G : ℝ × ℝ → E} (hG : ContinuousAt G (c, d)) :
    ∀ ε > 0, Tendsto (fun n => (P n).toMeasure.real
      {ω | ε < dist (G (X n ω, Y n ω)) (G (c, d))}) atTop (𝓝 0) := by
  intro ε hε
  obtain ⟨δ, hδ, hclose⟩ := Metric.continuousAt_iff.mp hG ε hε
  have hlim := (hX (δ / 2) (half_pos hδ)).add (hY (δ / 2) (half_pos hδ))
  simp only [zero_add] at hlim
  refine squeeze_zero (fun _ => measureReal_nonneg) (fun n => ?_) hlim
  apply (measureReal_mono (s₂ := {ω | δ / 2 < dist (X n ω) c} ∪
    {ω | δ / 2 < dist (Y n ω) d}) ?_).trans (measureReal_union_le _ _)
  intro ω hω
  by_contra hout
  have hx : dist (X n ω) c ≤ δ / 2 := le_of_not_gt (fun h => hout (Or.inl h))
  have hy : dist (Y n ω) d ≤ δ / 2 := le_of_not_gt (fun h => hout (Or.inr h))
  have hp : dist (X n ω, Y n ω) (c, d) < δ := by
    rw [Prod.dist_eq]
    exact max_lt (hx.trans_lt (half_lt_self hδ)) (hy.trans_lt (half_lt_self hδ))
  exact (not_lt_of_ge (hclose hp).le) hω

private theorem tendsto_norming_ratio_prob {Ω : Type*} [MeasurableSpace Ω]
    {ν : ProbabilityMeasure ℝ} {θ : ℝ} {B : ℕ → ℝ}
    (hB : IsRealStableAttracted ν θ B) {P : ℕ → ProbabilityMeasure Ω}
    {q : ℕ → ℕ} (hq : Tendsto q atTop atTop) (M : Ω → ℕ) {c : ℝ} (hc : 0 < c)
    (hM : ∀ ε > 0, Tendsto (fun n => (P n).toMeasure.real {ω | ε < |(M ω : ℝ) / q n - c|})
      atTop (𝓝 0)) :
    ∀ ε > 0, Tendsto (fun n => (P n).toMeasure.real
      {ω | ε < |B (M ω) / B (q n) - c ^ (1 / θ)|}) atTop (𝓝 0) := by
  intro ε hε
  obtain ⟨δ, hδ, hlocal⟩ := Metric.continuousAt_iff.mp
    (Real.continuousAt_rpow_const c (1 / θ) (Or.inl hc.ne')) (ε / 2) (half_pos hε)
  let d := min (c / 2) (min 1 (δ / 2))
  have hd : 0 < d := lt_min (half_pos hc) (lt_min zero_lt_one (half_pos hδ))
  obtain ⟨N, hN⟩ := hB.uniform_ratio (show 0 < c / 2 by positivity)
    (show c / 2 ≤ c + 1 by linarith) (ε / 2) (half_pos hε)
  apply squeeze_zero' (Eventually.of_forall fun _ => measureReal_nonneg) _ (hM d hd)
  filter_upwards [hq.eventually_ge_atTop N] with n hn
  refine measureReal_mono ?_
  intro ω hω
  have hω' : ε < |B (M ω) / B (q n) - c ^ (1 / θ)| := hω
  change d < |(M ω : ℝ) / q n - c|
  by_contra h
  have habs : |(M ω : ℝ) / q n - c| ≤ d := not_lt.mp h
  have hlow : c / 2 * q n ≤ (M ω : ℝ) := by
    have h := (abs_le.mp habs).1
    have hdle : d ≤ c / 2 := min_le_left _ _
    by_cases hqzero : q n = 0
    · simp [hqzero]
    · have : (0 : ℝ) < q n := by exact_mod_cast Nat.pos_of_ne_zero hqzero
      apply (le_div_iff₀ this).mp
      linarith
  have hhigh : (M ω : ℝ) ≤ (c + 1) * q n := by
    have h := (abs_le.mp habs).2
    have hdle : d ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
    by_cases hqzero : q n = 0
    · have : c ≤ d := by simpa [hqzero, abs_of_pos hc] using habs
      have : d ≤ c / 2 := min_le_left _ _
      linarith
    · have : (0 : ℝ) < q n := by exact_mod_cast Nat.pos_of_ne_zero hqzero
      apply (div_le_iff₀ this).mp
      linarith
  have happrox := hN (q n) hn (M ω) hlow hhigh
  have hrpow : |((M ω : ℝ) / q n) ^ (1 / θ) - c ^ (1 / θ)| < ε / 2 := by
    apply hlocal
    exact habs.trans_lt (lt_of_le_of_lt ((min_le_right _ _).trans (min_le_right _ _))
      (half_lt_self hδ))
  have hh := abs_sub_le (B (M ω) / B (q n)) (((M ω : ℝ) / q n) ^ (1 / θ)) (c ^ (1 / θ))
  linarith


theorem intro_II_canonical {μ : PMF ℕ} {θ : ℝ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hap : Aperiodic μ) (hDA : ∃ a, StableDomain μ θ a) (hnl : ¬ IsLatticeLaw (etaLaw μ)) :
    (∀ᶠ n in atTop, 0 < norming (stepLaw μ) θ n) ∧
      Tendsto (norming (stepLaw μ) θ) atTop atTop ∧
      Tendsto (fun n : ℕ => (leafTreeLaw μ n).map (codingTriple (norming (stepLaw μ) θ)))
        atTop (𝓝 (excTripleLaw θ)) := by
  have hB := BGWLeaves.isRealStableAttracted_norming hc hne hDA
  refine ⟨hB.pos, hB.tendsto_norming_atTop, ?_⟩
  obtain ⟨N, hN⟩ := eventually_atTop.mp (BGWLeaves.eventually_leafAdmissible hc hne hap hDA hnl)
  apply (tendsto_add_atTop_iff_nat N).mp
  exact intro_II hc hne hap hB hnl (tendsto_add_atTop_nat N)
    (fun k => hN (k + N) (Nat.le_add_left _ _))

private abbrev Triple := Skorokhod.D 1 ℝ × C(unitInterval, ℝ) × C(unitInterval, ℝ)

private def scaleTriple (p : Triple × (ℝ × ℝ)) : Triple :=
  (Skorokhod.mulPath p.2.1 p.1.1, p.2.2 • p.1.2.1, p.2.2 • p.1.2.2)

private theorem measurable_mulPath :
    Measurable (fun p : ℝ × Skorokhod.D 1 ℝ => Skorokhod.mulPath p.1 p.2) := by
  rw [measurable_iff_comap_le]
  change MeasurableSpace.comap (fun p : ℝ × Skorokhod.D 1 ℝ => Skorokhod.mulPath p.1 p.2)
    (inferInstance : MeasurableSpace (Skorokhod.D 1 ℝ)) ≤ _
  rw [Skorokhod.measurableSpace_eq_iSup_comap_eval (T := 1) (E := ℝ) (S := Set.univ)
    dense_univ zero_le_one (by simp)]
  simp only [MeasurableSpace.comap_iSup, iSup_le_iff, MeasurableSpace.comap_comp, Function.comp_def]
  intro t ht
  exact (measurable_fst.mul ((Skorokhod.measurable_eval t).comp measurable_snd)).comap_le

private theorem measurable_scaleTriple : Measurable scaleTriple :=
  (measurable_mulPath.comp (measurable_snd.fst.prodMk measurable_fst.fst)).prodMk
    ((measurable_snd.snd.smul measurable_fst.snd.fst).prodMk
      (measurable_snd.snd.smul measurable_fst.snd.snd))

private theorem scaleTriple_one (p : Triple) : scaleTriple (p, (1, 1)) = p := by
  apply Prod.ext
  · apply Skorokhod.ext
    intro t
    exact one_mul _
  · exact Prod.ext (one_smul _ _) (one_smul _ _)

private theorem continuousAt_scaleTriple_one (p : Triple) :
    ContinuousAt scaleTriple (p, (1, 1)) := by
  have hw := Skorokhod.tendsto_mulPath_one (T := 1) (E := ℝ) zero_le_one
    (continuous_fst.fst.tendsto (p, ((1 : ℝ), (1 : ℝ))))
    (continuous_snd.fst.tendsto (p, ((1 : ℝ), (1 : ℝ))))
  have hc : Continuous (fun z : Triple × (ℝ × ℝ) => z.2.2 • z.1.2.1) :=
    continuous_snd.snd.smul continuous_fst.snd.fst
  have hh : Continuous (fun z : Triple × (ℝ × ℝ) => z.2.2 • z.1.2.2) :=
    continuous_snd.snd.smul continuous_fst.snd.snd
  have ht := hw.prodMk_nhds ((hc.tendsto (p, (1, 1))).prodMk_nhds (hh.tendsto (p, (1, 1))))
  change Tendsto scaleTriple (𝓝 (p, (1, 1))) (𝓝 (scaleTriple (p, (1, 1))))
  rw [scaleTriple_one]
  simp only [Prod.eta, one_smul] at ht
  exact ht

private noncomputable def normFactors (p θ : ℝ) (B : ℕ → ℝ) (n : ℕ) (τ : LocallyFinite.Tree) : ℝ × ℝ :=
  (p ^ (1 / θ) * (B (treeSize τ) / B n),
    p ^ (1 - 1 / θ) * ((treeSize τ : ℝ) / n) / (B (treeSize τ) / B n))

private theorem measurable_normFactors (p θ : ℝ) (B : ℕ → ℝ) (n : ℕ) :
    Measurable (normFactors p θ B n) :=
  (measurable_of_countable (fun m : ℕ =>
    (p ^ (1 / θ) * (B m / B n), p ^ (1 - 1 / θ) * ((m : ℝ) / n) / (B m / B n)))).comp
      measurable_treeSize

private theorem normFactors_probability {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ}
    (hc : IsCritical μ) (hne : μ 1 ≠ 1) (hap : Aperiodic μ)
    (hB : IsRealStableAttracted (realOffspringStepLaw μ) θ B)
    {q : ℕ → ℕ} (hqtop : Tendsto q atTop atTop) (hq : ∀ k, LeafAdmissible μ (q k)) :
    ∀ ε > 0, Tendsto (fun k => (leafTreeLaw μ (q k)).toMeasure.real
      {τ | ε < dist (normFactors (μ 0).toReal θ B (q k) τ) (1, 1)}) atTop (𝓝 0) := by
  let p := (μ 0).toReal
  have hp : 0 < p := ENNReal.toReal_pos (hc.apply_zero_ne_zero hne) (PMF.apply_ne_top μ 0)
  have hsize : ∀ ε > 0, Tendsto (fun k => (leafTreeLaw μ (q k)).toMeasure.real
      {τ | ε < |(treeSize τ : ℝ) / q k - 1 / p|}) atTop (𝓝 0) :=
    fun _ hε => Helpers.tendsto_treeSize_div_leaf hc hne hap
      (BGWLeaves.stableDomain_of_isRealStableAttracted hc hne hB).1 hqtop hq hε
  have hratio := tendsto_norming_ratio_prob hB hqtop treeSize (one_div_pos.mpr hp) hsize
  let G : ℝ × ℝ → ℝ × ℝ := fun z =>
    (p ^ (1 / θ) * z.2, p ^ (1 - 1 / θ) * z.1 / z.2)
  have hG : ContinuousAt G (1 / p, (1 / p) ^ (1 / θ)) := by
    apply ContinuousAt.prodMk
    · exact (continuous_const.mul continuous_snd).continuousAt
    · exact (continuous_const.mul continuous_fst).continuousAt.div continuous_snd.continuousAt
        (Real.rpow_pos_of_pos (one_div_pos.mpr hp) _).ne'
  have hGval : G (1 / p, (1 / p) ^ (1 / θ)) = (1, 1) := by
    have hpow : p ^ (1 - 1 / θ) = p / p ^ (1 / θ) := by
      rw [Real.rpow_sub hp, Real.rpow_one]
    have hpowinv : (1 / p) ^ (1 / θ) = (p ^ (1 / θ))⁻¹ := by
      rw [one_div, Real.inv_rpow hp.le]
    dsimp [G]
    rw [hpow, hpowinv]
    have hpp : p ^ (1 / θ) ≠ 0 := (Real.rpow_pos_of_pos hp _).ne'
    field_simp
  have ht := probability_continuous_pair (fun k => leafTreeLaw μ (q k))
    (X := fun k τ => (treeSize τ : ℝ) / q k) (Y := fun k τ => B (treeSize τ) / B (q k))
    (by simpa only [Real.dist_eq] using hsize)
    (by simpa only [Real.dist_eq] using hratio) hG
  rw [hGval] at ht
  exact ht

private theorem scale_codingTripleAt (p θ : ℝ) (hp : 0 < p) (B : ℕ → ℝ) (n : ℕ)
    (τ : LocallyFinite.Tree) (hz : treeSize τ ≠ 0) (hBn : B n ≠ 0) (hBz : B (treeSize τ) ≠ 0) :
    scaleTriple (codingTriple B τ, normFactors p θ B n τ) = codingTripleAt p θ B n τ := by
  have hzR : (treeSize τ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hz
  have hc : p ^ (1 / θ) ≠ 0 := (Real.rpow_pos_of_pos hp _).ne'
  have hheight : (p ^ (1 - 1 / θ) * ((treeSize τ : ℝ) / n) / (B (treeSize τ) / B n)) *
      (B (treeSize τ) / treeSize τ) = p ^ (1 - 1 / θ) * B n / n := by
    field_simp
  apply Prod.ext
  · apply Skorokhod.ext
    intro t
    change (p ^ (1 / θ) * (B (treeSize τ) / B n)) *
      (BGW.Probability.RealWalk.partialSum (PathTail.treeIncrementSeq τ)
        ⌊(treeSize τ : ℝ) * t⌋₊ / B (treeSize τ)) =
      BGW.Probability.RealWalk.partialSum (PathTail.treeIncrementSeq τ)
        ⌊(treeSize τ : ℝ) * t⌋₊ / (B n / p ^ (1 / θ))
    field_simp

  · apply Prod.ext
    · apply ContinuousMap.ext
      intro t
      change (p ^ (1 - 1 / θ) * ((treeSize τ : ℝ) / n) / (B (treeSize τ) / B n)) *
        (B (treeSize τ) / treeSize τ * ExactContour.treeContourLin τ (2 * (treeSize τ : ℝ) * t)) = _
      rw [← mul_assoc, hheight]
      rfl
    · apply ContinuousMap.ext
      intro t
      change (p ^ (1 - 1 / θ) * ((treeSize τ : ℝ) / n) / (B (treeSize τ) / B n)) *
        (B (treeSize τ) / treeSize τ * TailPair.treeHeightLin τ ((treeSize τ : ℝ) * t)) = _
      rw [← mul_assoc, hheight]
      rfl

/-- Remark 5.10, jointly on the whole unit interval. -/
theorem rem_changement {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hap : Aperiodic μ) (hB : IsRealStableAttracted (realOffspringStepLaw μ) θ B)
    (hnl : ¬ IsLatticeLaw (etaLaw μ)) {q : ℕ → ℕ}
    (hqtop : Tendsto q atTop atTop) (hq : ∀ k, LeafAdmissible μ (q k)) :
    Tendsto (fun k => (leafTreeLaw μ (q k)).map (codingTripleAt (μ 0).toReal θ B (q k)))
      atTop (𝓝 (excTripleLaw θ)) := by
  let R := fun k => normFactors (μ 0).toReal θ B (q k)
  have hR (k : ℕ) : Measurable (R k) := measurable_normFactors _ _ _ _
  have ht := BGW.Probability.tendsto_map_prodMk_of_tendsto_of_error
    (fun k => leafTreeLaw μ (q k)) (fun _ => measurable_codingTriple B) hR
    (intro_II hc hne hap hB hnl hqtop hq) (normFactors_probability hc hne hap hB hqtop hq)
  have hcont : ∀ᵐ p ∂((excTripleLaw θ).map (fun x => (x, ((1 : ℝ), (1 : ℝ))))).toMeasure,
      ContinuousAt scaleTriple p := by
    apply (ae_map_iff (measurable_id.prodMk measurable_const).aemeasurable
      (IsGδ.setOfPred_continuousAt scaleTriple).measurableSet).mpr
    exact ae_of_all _ continuousAt_scaleTriple_one
  have hs := BGW.Probability.tendsto_map_of_ae_continuousAt ht
    (fun _ => measurable_scaleTriple.aemeasurable) hcont
  have hlim : ((excTripleLaw θ).map (fun x => (x, ((1 : ℝ), (1 : ℝ))))).map scaleTriple =
      excTripleLaw θ := by
    apply Subtype.ext
    change ((excTripleLaw θ).toMeasure.map _).map scaleTriple = _
    erw [Measure.map_map measurable_scaleTriple (measurable_id.prodMk measurable_const)]
    have heq : (scaleTriple ∘ fun x : Triple => (x, ((1 : ℝ), (1 : ℝ)))) = id := by
      funext x
      exact scaleTriple_one x
    erw [heq, Measure.map_id]
    rfl
  rw [hlim] at hs
  apply hs.congr'
  have hp : 0 < (μ 0).toReal :=
    ENNReal.toReal_pos (hc.apply_zero_ne_zero hne) (PMF.apply_ne_top μ 0)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hB.pos
  filter_upwards [hqtop.eventually_ge_atTop N, hqtop.eventually_ge_atTop 1] with k hk hk1
  apply Subtype.ext
  change ((leafTreeLaw μ (q k)).toMeasure.map _).map scaleTriple =
    (leafTreeLaw μ (q k)).toMeasure.map (codingTripleAt (μ 0).toReal θ B (q k))
  erw [Measure.map_map measurable_scaleTriple ((measurable_codingTriple B).prodMk (hR k))]
  apply Measure.map_congr
  have hmem : ∀ᵐ τ ∂(leafTreeLaw μ (q k)).toMeasure, τ ∈ leafCountEvent (q k) := by
    rw [coe_leafTreeLaw (hq k)]
    exact ae_cond_mem (measurableSet_leafCountEvent _)
  filter_upwards [hmem] with τ hτ
  obtain ⟨t, rfl, ht⟩ := hτ
  have hsize : q k ≤ t.size := ht ▸ t.degreeCount_le_size 0
  apply scale_codingTripleAt _ _ hp
  · rw [treeSize_toLocallyFinite]
    omega
  · exact (hN (q k) hk).ne'
  · rw [treeSize_toLocallyFinite]
    exact (hN t.size (hk.trans hsize)).ne'

end BGWLeaves.LeafLimits.Joint
