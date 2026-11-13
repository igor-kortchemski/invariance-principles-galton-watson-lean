module

public import BGWLeaves.LeafLimitsGeneral.SupportLattice

/-! Lattice Lemma 5.8. The tail-law transfer and reweighting proof are copied
from `LeafLimits.Absolue`; the local input and supported density are lattice versions. -/

@[expose] public section
namespace BGWLeaves.LeafLimitsGeneral.AbsolueLattice
open MeasureTheory ProbabilityTheory Filter BGW BGW.StableTrees BGW.LocallyFinite
open BGWLeaves.StableAnalysis BGWLeaves.LeafLimits BGWLeaves.LeafLimits.Absolue
open BGWLeaves.LeafLimitsGeneral.DensityLattice BGWLeaves.LeafLimitsGeneral.SupportLattice
open scoped ENNReal NNReal Topology

private theorem mu0_bounds {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1) :
    0 < (μ 0).toReal ∧ (μ 0).toReal < 1 := by
  refine ⟨ENNReal.toReal_pos (hc.apply_zero_ne_zero hne) (μ.apply_ne_top 0), ?_⟩
  have hle : (μ 0).toReal ≤ 1 := by
    simpa using ENNReal.toReal_mono ENNReal.one_ne_top (PMF.coe_le_one μ 0)
  refine lt_of_le_of_ne hle fun heq => BGWLeaves.mu0_ne_one hc hne ?_
  exact (ENNReal.toReal_eq_toReal_iff' (μ.apply_ne_top 0) ENNReal.one_ne_top).1
    (by simpa using heq)

private theorem integral_add_norm {E : Type*} [TopologicalSpace E] [MeasurableSpace E]
    [OpensMeasurableSpace E] {ν : Measure LocallyFinite.Tree} [IsProbabilityMeasure ν]
    (f : BoundedContinuousFunction E ℝ) {Φ : LocallyFinite.Tree → E} (hΦ : Measurable Φ) :
    ∫ τ, (f (Φ τ) + ‖f‖) ∂ν = ∫ τ, f (Φ τ) ∂ν + ‖f‖ := by
  have hint : Integrable (fun τ => f (Φ τ)) ν :=
    Integrable.of_bound (f.continuous.measurable.comp hΦ).aestronglyMeasurable ‖f‖
      (Eventually.of_forall fun τ => f.norm_coe_le_norm (Φ τ))
  rw [integral_add hint (integrable_const _), integral_const]
  simp

/-- Proposition 4.4(ii), then substitution of the attained inverse cutoff. -/
private theorem leafGe_absPair_tendsto_of_tail {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ}
    (hc : IsCritical μ) (hne : μ 1 ≠ 1) (hap : Aperiodic μ)
    (hB : IsRealStableAttracted (realOffspringStepLaw μ) θ B)
    {a : ℝ≥0} (ha : a ∈ Set.Ioo (0 : ℝ≥0) 1)
    (hT : Tendsto (fun n : ℕ => (DiscreteForest.tailTreeLaw μ n).map
        (absPair (μ 0).toReal B n a (NNReal.coe_pos.mpr ha.1)))
      atTop (𝓝 (tailExcLaw θ a)))
    {q : ℕ → ℕ} (hqtop : Tendsto q atTop atTop) :
    Tendsto (fun k => (leafGeTreeLaw μ (q k)).map
        (absPair (μ 0).toReal B (rGreatest μ (q k)) a (NNReal.coe_pos.mpr ha.1)))
      atTop (𝓝 (tailExcLaw θ a)) := by
  have hDA := (BGWLeaves.stableDomain_of_isRealStableAttracted hc hne hB).1
  obtain ⟨hp, hp1⟩ := mu0_bounds hc hne
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto] at hT ⊢
  intro f
  let Φ := fun n => absPair (μ 0).toReal B n a (NNReal.coe_pos.mpr ha.1)
  have hΦ : ∀ n, Measurable (Φ n) := fun n => measurable_absPair _ _ _ _ _
  let U := fun n τ => f (Φ n τ) + ‖f‖
  have hU : ∀ n, IsBoundedTest (2 * ‖f‖) (U n) := by
    intro n
    refine ⟨(f.continuous.measurable.comp (hΦ n)).add_const _, fun τ => ?_⟩
    have hb := abs_le.1 (show |f (Φ n τ)| ≤ ‖f‖ by
      simpa only [Real.norm_eq_abs] using f.norm_coe_le_norm (Φ n τ))
    constructor <;> dsimp [U] <;> linarith [hb.1, hb.2]
  have hbase : Tendsto (fun n : ℕ => ∫ τ, U n τ
      ∂((bienaymeLaw μ.toMeasure)[|sizeGeEvent n])) atTop
      (𝓝 ((∫ z, f z ∂(tailExcLaw θ a).toMeasure) + ‖f‖)) := by
    apply ((hT f).add_const ‖f‖).congr fun n => ?_
    have hn := BGWLeaves.sizeGeEvent_ne_zero hc hne n
    have := cond_isProbabilityMeasure (μ := bienaymeLaw μ.toMeasure) hn
    rw [ProbabilityMeasure.toMeasure_map,
      DiscreteForest.tailTreeLaw_toMeasure μ n hn,
      integral_map (hΦ n).aemeasurable f.continuous.aestronglyMeasurable]
    exact (integral_add_norm (ν := (bienaymeLaw μ.toMeasure)[|sizeGeEvent n]) f (hΦ n)).symm
  have hpass := BGWLeaves.prop_passage_ii hc hne hap hDA hU hbase
  have hcomp := hpass.comp ((tendsto_rGreatest hp hp1).comp hqtop)
  have hsub := hcomp.sub_const ‖f‖
  rw [add_sub_cancel_right] at hsub
  apply hsub.congr'
  filter_upwards [hqtop.eventually_ge_atTop 1] with k hk
  have hs := (rGreatest_spec hp hp1 hk).2
  have hn := BGWLeaves.leafGeEvent_ne_zero hc hne (q k)
  have := cond_isProbabilityMeasure (μ := bienaymeLaw μ.toMeasure) hn
  simp only [Function.comp_apply, hs]
  rw [integral_add_norm f (hΦ _), add_sub_cancel_right,
    ProbabilityMeasure.toMeasure_map, coe_leafGeTreeLaw hn,
    integral_map (hΦ _).aemeasurable f.continuous.aestronglyMeasurable]

private theorem cutoff_tendsto {v : ℕ → ℝ} {x l u : ℝ}
    (hv : Tendsto v atTop (𝓝 x)) (hl : x ≠ l) (hu : x ≠ u) :
    Tendsto (fun n => if l < v n ∧ v n < u then (1 : ℝ) else 0) atTop
      (𝓝 (if l < x ∧ x < u then 1 else 0)) := by
  by_cases hmem : l < x ∧ x < u
  · rw [ite_eq_left hmem]
    apply tendsto_const_nhds.congr'
    filter_upwards [hv.eventually (lt_mem_nhds hmem.1),
      hv.eventually (gt_mem_nhds hmem.2)] with n hn1 hn2
    simp [hn1, hn2]
  · rw [ite_eq_right hmem]
    apply tendsto_const_nhds.congr'
    rcases le_or_gt x l with hxl | hlx
    · have hlt : x < l := lt_of_le_of_ne hxl hl
      filter_upwards [hv.eventually (gt_mem_nhds hlt)] with n hn
      have hnot : ¬ (l < v n ∧ v n < u) := by intro h; linarith [h.1]
      simp [hnot]
    · have hlt : u < x := lt_of_le_of_ne (le_of_not_gt (fun h => hmem ⟨hlx, h⟩)) hu.symm
      filter_upwards [hv.eventually (lt_mem_nhds hlt)] with n hn
      have hnot : ¬ (l < v n ∧ v n < u) := by intro h; linarith [h.2]
      simp [hnot]

private theorem lintegral_le_liminf_of_ae_tendsto {Ω : Type*} [MeasurableSpace Ω]
    {ν : Measure Ω} {f : ℕ → Ω → ℝ≥0∞} {g : Ω → ℝ≥0∞}
    (hf : ∀ n, Measurable (f n))
    (ht : ∀ᵐ ω ∂ν, Tendsto (fun n => f n ω) atTop (𝓝 (g ω))) :
    ∫⁻ ω, g ω ∂ν ≤ liminf (fun n => ∫⁻ ω, f n ω ∂ν) atTop := by
  calc
    _ = ∫⁻ ω, liminf (fun n => f n ω) atTop ∂ν :=
      lintegral_congr_ae (ht.mono fun _ h => h.liminf_eq.symm)
    _ ≤ _ := lintegral_liminf_le hf

/-- Cutoffs avoid both endpoint atoms. No assumption that every deterministic cutoff is a
continuity set is made. -/
private theorem exists_atom_free_cutoffs {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsFiniteMeasure ν] {e : Ω → ℝ} (he : Measurable e) :
    ∃ α : ℕ → ℝ, Tendsto α atTop atTop ∧ ∀ m,
      1 < α m ∧ ν {ω | e ω = α m} = 0 ∧ ν {ω | e ω = 1 / α m} = 0 := by
  let A := {x : ℝ | 0 < ν {ω | e ω = x}}
  have hA : A.Countable := Measure.countable_meas_level_set_pos he
  have hbad : (A ∪ (Inv.inv ⁻¹' A)).Countable := hA.union (hA.preimage inv_injective)
  have hex (m : ℕ) : ∃ α ∈ Set.Ioo ((m : ℝ) + 2) ((m : ℝ) + 3),
      α ∉ A ∪ (Inv.inv ⁻¹' A) := by
    have hz := hbad.measure_zero volume
    have hpos : 0 < volume (Set.Ioo ((m : ℝ) + 2) ((m : ℝ) + 3) \
        (A ∪ (Inv.inv ⁻¹' A))) := by
      rw [measure_sdiff_null hz, Real.volume_Ioo]
      norm_num
    exact nonempty_of_measure_ne_zero hpos.ne'
  choose α hα hn using hex
  refine ⟨α, tendsto_atTop_mono (fun m => ?_) tendsto_natCast_atTop_atTop, fun m => ?_⟩
  · exact le_trans (by linarith : (m : ℝ) ≤ m + 2) (hα m).1.le
  · have hnot1 : ¬ 0 < ν {ω | e ω = α m} := fun h => hn m (Or.inl h)
    have hnot2 : ¬ 0 < ν {ω | e ω = 1 / α m} := by
      intro h
      apply hn m
      right
      change 0 < ν {ω | e ω = (α m)⁻¹}
      simpa only [one_div] using h
    have hlarge : 1 < α m := by
      have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      have hm2 : (m : ℝ) + 2 < α m := (hα m).1
      linarith
    exact ⟨hlarge,
      le_antisymm (le_of_not_gt hnot1) bot_le, le_antisymm (le_of_not_gt hnot2) bot_le⟩

/-- The bounded-test change-of-measure argument, with atom-free endpoint cutoffs and cutoff
removal. Fatou gives the lower bound; probability mass gives convergence for all bounded tests. -/
private theorem weighted_tendsto_of_cutoffs {E : Type*} [MetricSpace E] [MeasurableSpace E]
    [BorelSpace E] [TopologicalSpace.SeparableSpace E]
    {P Q : ℕ → ProbabilityMeasure E} {P₀ Q₀ : ProbabilityMeasure E}
    (hP : Tendsto P atTop (𝓝 P₀)) (w : ℕ → E → ℝ≥0∞) (g e : E → ℝ)
    (hw : ∀ n, Measurable (w n)) (hg : Measurable g) (he : Measurable e)
    (hgnn : ∀ x, 0 ≤ g x)
    (hQ : ∀ᶠ n in atTop, (Q n).toMeasure = (P n).toMeasure.withDensity (w n))
    (hΓ : ∀ f : BoundedContinuousFunction E ℝ,
      ∫ x, f x ∂Q₀.toMeasure = ∫ x, f x * g x ∂P₀.toMeasure)
    (hgood : ∀ᵐ x ∂P₀.toMeasure, ContinuousAt e x ∧ 0 < e x)
    (hconv : ∀ x, ContinuousAt e x → 0 < e x → ∀ z : ℕ → E,
      Tendsto z atTop (𝓝 x) →
      Tendsto (fun n => (w n (z n)).toReal) atTop (𝓝 (g x))) :
    Tendsto Q atTop (𝓝 Q₀) := by
  obtain ⟨Ω, mΩ, ν, hν, X, Y, hXm, hYm, hXlaw, hYlaw, hXY⟩ :=
    BGW.Probability.exists_probabilitySpace_tendsto_ae_of_tendsto_metric hP
  let : MeasurableSpace Ω := mΩ
  let : IsProbabilityMeasure ν := hν
  have hgoodY : ∀ᵐ ω ∂ν, ContinuousAt e (Y ω) ∧ 0 < e (Y ω) := by
    rw [← hYlaw] at hgood
    exact ae_of_ae_map hYm.aemeasurable hgood
  obtain ⟨α, hαtop, hα⟩ := exists_atom_free_cutoffs ν (he.comp hYm)
  let χ := fun m x => if 1 / α m < e x ∧ e x < α m then (1 : ℝ) else 0
  have hχm : ∀ m, Measurable (χ m) := fun m =>
    measurable_const.ite ((measurableSet_lt measurable_const he).inter
      (measurableSet_lt he measurable_const)) measurable_const
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
  apply BoundedContinuousFunction.tendsto_integral_of_forall_integral_le_liminf_integral
  intro f hfnn
  let L := liminf (fun n => ∫⁻ x, ENNReal.ofReal (f x) ∂(Q n).toMeasure) atTop
  have hcut (m : ℕ) :
      ∫⁻ ω, ENNReal.ofReal (f (Y ω) * g (Y ω) * χ m (Y ω)) ∂ν ≤ L := by
    let H := fun n ω => ENNReal.ofReal (f (X n ω) * (w n (X n ω)).toReal * χ m (X n ω))
    have hHm : ∀ n, Measurable (H n) := fun n => by
      exact ((f.continuous.measurable.comp (hXm n)).mul
        ((hw n).ennreal_toReal.comp (hXm n)) |>.mul ((hχm m).comp (hXm n))).ennreal_ofReal
    have hHt : ∀ᵐ ω ∂ν, Tendsto (fun n => H n ω) atTop
        (𝓝 (ENNReal.ofReal (f (Y ω) * g (Y ω) * χ m (Y ω)))) := by
      have hnull : ∀ᵐ ω ∂ν, e (Y ω) ≠ α m ∧ e (Y ω) ≠ 1 / α m := by
        have h1 : ∀ᵐ ω ∂ν, e (Y ω) ≠ α m := by
          rw [ae_iff]
          simpa only [not_not, Function.comp_apply] using (hα m).2.1
        have h2 : ∀ᵐ ω ∂ν, e (Y ω) ≠ 1 / α m := by
          rw [ae_iff]
          simpa only [not_not, Function.comp_apply] using (hα m).2.2
        exact h1.and h2
      filter_upwards [hgoodY, hXY, hnull] with ω hgω hxy hnω
      have hc := cutoff_tendsto (hgω.1.tendsto.comp hxy) hnω.2 hnω.1
      exact ENNReal.continuous_ofReal.continuousAt.tendsto.comp
        (((f.continuous.tendsto _).comp hxy).mul
          (hconv _ hgω.1 hgω.2 _ hxy) |>.mul hc)
    have hbound : ∀ᶠ n in atTop, (∫⁻ ω, H n ω ∂ν) ≤
        ∫⁻ x, ENNReal.ofReal (f x) ∂(Q n).toMeasure := by
      filter_upwards [hQ] with n hQn
      rw [hQn, lintegral_withDensity_eq_lintegral_mul _ (hw n) f.continuous.measurable.ennreal_ofReal]
      rw [← hXlaw n, lintegral_map (f := fun x => (w n * fun x => ENNReal.ofReal (f x)) x)
        ((hw n).mul f.continuous.measurable.ennreal_ofReal) (hXm n)]
      apply lintegral_mono
      intro ω
      dsimp only [H, χ]
      split_ifs with hmem
      · simp only [mul_one, Pi.mul_apply]
        rw [mul_comm (w n (X n ω))]
        calc
          _ = ENNReal.ofReal (f (X n ω)) * ENNReal.ofReal (w n (X n ω)).toReal :=
            ENNReal.ofReal_mul (hfnn _)
          _ ≤ _ := by gcongr; exact ENNReal.ofReal_toReal_le
      · simp
    exact (lintegral_le_liminf_of_ae_tendsto hHm hHt).trans
      (Filter.liminf_le_liminf hbound)
  have hfull : ∫⁻ ω, ENNReal.ofReal (f (Y ω) * g (Y ω)) ∂ν ≤ L := by
    have hm : ∀ m, Measurable (fun ω => ENNReal.ofReal
        (f (Y ω) * g (Y ω) * χ m (Y ω))) := fun m =>
      ((f.continuous.measurable.mul hg).mul (hχm m) |>.comp hYm).ennreal_ofReal
    have ht : ∀ᵐ ω ∂ν, Tendsto (fun m => ENNReal.ofReal
        (f (Y ω) * g (Y ω) * χ m (Y ω))) atTop
        (𝓝 (ENNReal.ofReal (f (Y ω) * g (Y ω)))) := by
      filter_upwards [hgoodY] with ω hω
      apply tendsto_const_nhds.congr'
      filter_upwards [(hαtop.const_div_atTop 1).eventually (gt_mem_nhds hω.2),
        hαtop.eventually_gt_atTop (e (Y ω))] with m hm1 hm2
      simp only [χ]
      rw [ite_eq_left (show 1 / α m < e (Y ω) ∧ e (Y ω) < α m from ⟨hm1, hm2⟩), mul_one]
    exact (lintegral_le_liminf_of_ae_tendsto hm ht).trans
      (liminf_le_of_frequently_le' (Eventually.of_forall hcut).frequently)
  have htarget : ∫⁻ ω, ENNReal.ofReal (f (Y ω) * g (Y ω)) ∂ν =
      ∫⁻ x, ENNReal.ofReal (f x * g x) ∂P₀.toMeasure := by
    rw [← hYlaw, lintegral_map (f := fun x : E => ENNReal.ofReal (f x * g x))
      (f.continuous.measurable.mul hg).ennreal_ofReal hYm]
  rw [htarget] at hfull
  have hbound : ∀ n, (∫⁻ x, ENNReal.ofReal (f x) ∂(Q n).toMeasure) ≤
      ENNReal.ofReal ‖f‖ := by
    intro n
    calc
      _ ≤ ∫⁻ x, ENNReal.ofReal ‖f‖ ∂(Q n).toMeasure := by
        apply lintegral_mono
        intro x
        exact ENNReal.ofReal_le_ofReal
          ((le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using f.norm_coe_le_norm x))
      _ = _ := by simp
  have hLfin : L ≠ ⊤ := ne_of_lt (lt_of_le_of_lt
    (liminf_le_of_frequently_le' (Eventually.of_forall hbound).frequently) ENNReal.ofReal_lt_top)
  rw [hΓ f, integral_eq_lintegral_of_nonneg_ae (f := fun x : E => f x * g x)
    (Eventually.of_forall fun x => mul_nonneg (hfnn x) (hgnn x))
    (f.continuous.measurable.mul hg).aestronglyMeasurable]
  have hreal := ENNReal.toReal_mono hLfin hfull
  dsimp only [L] at hreal
  rw [← ENNReal.liminf_toReal_eq ENNReal.ofReal_ne_top (Eventually.of_forall hbound)] at hreal
  have hi (n : ℕ) : (∫⁻ x, ENNReal.ofReal (f x) ∂(Q n).toMeasure).toReal =
      ∫ x, f x ∂(Q n).toMeasure :=
    (integral_eq_lintegral_of_nonneg_ae (f := fun x : E => f x)
      (Eventually.of_forall hfnn) f.continuous.measurable.aestronglyMeasurable).symm
  simpa only [hi] using hreal


private theorem lem_absolue_of_tail {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ}
    (hc : IsCritical μ) (hne : μ 1 ≠ 1) (hap : Aperiodic μ)
    (hB : IsRealStableAttracted (realOffspringStepLaw μ) θ B)
    (hT : ∀ {a : ℝ≥0} (ha : a ∈ Set.Ioo (0 : ℝ≥0) 1),
      Tendsto (fun n : ℕ => (DiscreteForest.tailTreeLaw μ n).map
          (absPair (μ 0).toReal B n a (NNReal.coe_pos.mpr ha.1)))
        atTop (𝓝 (tailExcLaw θ a)))
    {a : ℝ≥0} (ha : a ∈ Set.Ioo (0 : ℝ≥0) 1) {q : ℕ → ℕ}
    (hqtop : Tendsto q atTop atTop) (hq : ∀ k, LeafAdmissible μ (q k)) :
    Tendsto (fun k => (leafTreeLaw μ (q k)).map
        (absPair (μ 0).toReal B (rGreatest μ (q k)) a (NNReal.coe_pos.mpr ha.1)))
      atTop (𝓝 ((excLaw θ).map (restrictPair ha.2.le))) := by
  change 0 < a ∧ a < 1 at ha
  let E := Skorokhod.D (a : ℝ) ℝ × C(Set.Icc (0 : ℝ) a, ℝ)
  let P := fun k => (leafGeTreeLaw μ (q k)).map
    (absPair (μ 0).toReal B (rGreatest μ (q k)) a (NNReal.coe_pos.mpr ha.1))
  let Q := fun k => (leafTreeLaw μ (q k)).map
    (absPair (μ 0).toReal B (rGreatest μ (q k)) a (NNReal.coe_pos.mpr ha.1))
  let e := fun z : E => evalEnd a z.1
  let g := fun z : E => max (gammaA θ a (e z)) 0
  have ha0 : 0 < (a : ℝ) := NNReal.coe_pos.mpr ha.1
  have ha1 : (a : ℝ) < 1 := NNReal.coe_lt_coe.mpr ha.2
  obtain ⟨hp, hp1⟩ := mu0_bounds hc hne
  have hrtop := (tendsto_rGreatest hp hp1).comp hqtop
  have hP : Tendsto P atTop (𝓝 (tailExcLaw θ a)) :=
    leafGe_absPair_tendsto_of_tail hc hne hap hB ha (hT ha) hqtop
  have hgoodraw : ∀ᵐ z : E ∂(tailExcLaw θ a).toMeasure,
      ContinuousAt z.1 ⟨(a : ℝ), a.coe_nonneg, le_rfl⟩ ∧ 0 < e z := by
    have hfst : (tailExcLaw θ a).toMeasure.map Prod.fst =
        (PathTail.tailPrefixLimit θ a).toMeasure :=
      congrArg ProbabilityMeasure.toMeasure (tailExcLaw_map_fst θ a)
    have hh := ExactPrefix.ae_tailPrefix_continuousAt_pos hB.index_mem a ha
    rw [← hfst] at hh
    exact ae_of_ae_map measurable_fst.aemeasurable hh
  have hgood : ∀ᵐ z : E ∂(tailExcLaw θ a).toMeasure, ContinuousAt e z ∧ 0 < e z := by
    filter_upwards [hgoodraw] with z hz
    exact ⟨(Skorokhod.continuousAt_eval hz.1).comp continuous_fst.continuousAt, hz.2⟩
  have he : Measurable e := (measurable_evalEnd a).comp measurable_fst
  have hg0 : Measurable (fun z : E => gammaA θ a (e z)) :=
    (measurable_gammaA θ).comp (measurable_const.prodMk he)
  have hgeq : g =ᵐ[(tailExcLaw θ a).toMeasure] (fun z => gammaA θ a (e z)) := by
    filter_upwards [hgood] with z hz
    exact max_eq_left (gammaA_nonneg hB.index_mem ha1 hz.2)
  have hQ : ∀ᶠ k in atTop, (Q k).toMeasure = (P k).toMeasure.withDensity
      (absWeight μ B (rGreatest μ (q k)) (q k) a) := by
    have hclocktop : Tendsto (fun k => ⌊(a : ℝ) * (μ 0).toReal * rGreatest μ (q k)⌋₊)
        atTop atTop := tendsto_nat_floor_atTop.comp
      ((tendsto_natCast_atTop_atTop.comp hrtop).const_mul_atTop (mul_pos ha0 hp))
    filter_upwards [hclocktop.eventually_ge_atTop 1,
      hqtop.eventually (eventually_clock_index_lt hp hp1 ha0 ha1),
      hrtop.eventually hB.pos] with k hk hkn hbr
    exact map_leaf_eq_withDensity_absWeight hc hne ha0 hbr.ne' (hq k) hk hkn
  have hΓ : ∀ f : BoundedContinuousFunction E ℝ,
      ∫ z, f z ∂((excLaw θ).map (restrictPair ha.2.le)).toMeasure =
        ∫ z, f z * g z ∂(tailExcLaw θ a).toMeasure := by
    intro f
    have hf : Measurable (fun z : E => f z * gammaA θ a (e z)) :=
      f.continuous.measurable.mul hg0
    calc
      _ = ∫ z, f (restrictPair ha.2.le z) ∂(excLaw θ).toMeasure := by
        exact integral_map (measurable_restrictPair ha.2.le).aemeasurable
          f.continuous.aestronglyMeasurable
      _ = ∫ z, f (restrictPair ha.2.le z) * gammaA θ a
          (evalEnd a (restrictPair ha.2.le z).1) ∂(tailExcLaw θ 1).toMeasure :=
        ClassicalLimits.Cited.prop_Gamma hB.index_mem a ha f f.continuous.measurable
          ⟨‖f‖, fun z => by simpa only [Real.norm_eq_abs] using f.norm_coe_le_norm z⟩
      _ = ∫ z, f z * gammaA θ a (e z) ∂(tailExcLaw θ a).toMeasure := by
        rw [← tailExcLaw_map_restrictPair θ ha.2.le, ProbabilityMeasure.toMeasure_map,
          integral_map (measurable_restrictPair ha.2.le).aemeasurable hf.aestronglyMeasurable]
      _ = _ := integral_congr_ae (hgeq.mono fun z hz => by rw [hz])
  apply weighted_tendsto_of_cutoffs hP
    (fun k => absWeight μ B (rGreatest μ (q k)) (q k) a) g e
    (fun k => measurable_absWeight _ _ _ _ _) (hg0.max measurable_const) he
    (fun z => le_max_right _ _) hQ hΓ hgood
  intro x hx hxp z hz
  have ht := absWeight_contConv hc hne hap hB ha hqtop hq hxp (hx.tendsto.comp hz)
  simpa only [g, max_eq_left (gammaA_nonneg hB.index_mem ha1 hxp)] using ht

theorem lem_absolue {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hap : Aperiodic μ) (hB : IsRealStableAttracted (realOffspringStepLaw μ) θ B)
    {a : ℝ≥0} (ha : a ∈ Set.Ioo (0 : ℝ≥0) 1) {q : ℕ → ℕ}
    (hqtop : Tendsto q atTop atTop) (hq : ∀ k, LeafAdmissible μ (q k)) :
    Tendsto (fun k => (leafTreeLaw μ (q k)).map
        (absPair (μ 0).toReal B (rGreatest μ (q k)) a (NNReal.coe_pos.mpr ha.1)))
      atTop (𝓝 ((excLaw θ).map (restrictPair ha.2.le))) := by
  exact lem_absolue_of_tail hc hne hap hB
    (fun {_} ha => AbsolueTail.tail_absPair_tendsto hc hne hap hB ha) ha hqtop hq


end BGWLeaves.LeafLimitsGeneral.AbsolueLattice
