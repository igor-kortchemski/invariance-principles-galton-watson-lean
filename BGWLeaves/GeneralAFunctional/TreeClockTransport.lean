module

public import BGWLeaves.GeneralAFunctional.TreePrefixLimit
public import BGWLeaves.GeneralAFunctional.TreeSize

@[expose] public section
namespace BGWLeaves.GeneralAFunctional.TreeClockTransport
open MeasureTheory ProbabilityTheory Filter Set BGW
open BGW.StableTrees BGW.LocallyFinite BGWLeaves.StableAnalysis
open BGW.StableTrees.TailPair BGW.Skorokhod
open BGWLeaves.GeneralAFunctional.TreeClocks BGWLeaves.GeneralAFunctional.TreeEvents
open BGWLeaves.GeneralAFunctional.TreeConcentration BGWLeaves.GeneralAFunctional.TreeProbability
open BGWLeaves.GeneralAFunctional.TreeSize BGWLeaves.GeneralAFunctional.TreePrefixLimit
open scoped ENNReal NNReal Topology

theorem marked_pair_prefix_all {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ}
    (h : StableDomain μ θ B) (hap : Aperiodic μ) {A : Set ℕ}
    {q : ℕ → ℕ} (hqtop : Tendsto q atTop atTop) (hq : ∀ i, ZetaAAdmissible μ A (q i))
    (a : ℝ≥0) (ha : a ∈ Ioo (0 : ℝ≥0) 1) :
    Tendsto (fun i => (zetaATreeLaw μ A (q i)).map
      (treePairPath B (explorationIndex μ A (q i)) a)) atTop
      (𝓝 ((excLaw θ).map (restrictPair ha.2.le))) := by
  have hA := measure_ne_zero_of_sequence h.critical h.nondegenerate hqtop hq
  by_cases hA1 : μ.toMeasure A = 1
  · have hadm (i : ℕ) : Admissible μ (q i) := by
      change bienaymeLaw μ.toMeasure (sizeEvent (q i)) ≠ 0
      rw [← measure_congr (full_marks_event_ae h.critical h.nondegenerate hA1 (q i))]
      exact hq i
    have ht := ExactPair.tendsto_exactPairLaw_prefix h hqtop hadm a ha
    apply ht.congr
    intro i
    rw [full_marks_law_eq h.critical h.nondegenerate hA1 (hq i)]
    simp only [explorationIndex, hA1, ENNReal.toReal_one, div_one, Nat.floor_natCast]
    rfl
  · exact marked_pair_prefix_tendsto h hap hA hA1 hqtop hq a ha

noncomputable def clockScale (r : ℕ) (τ : LocallyFinite.Tree) : Ioi (0 : ℝ) :=
  ⟨(max (treeSize τ) 1 : ℕ) / (max r 1 : ℕ),
    div_pos (by exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one (le_max_right _ _))
      (by exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one (le_max_right _ _))⟩

theorem measurable_clockScale (r : ℕ) : Measurable (fun τ => (clockScale r τ : ℝ)) :=
  (((measurable_from_nat (f := fun z : ℕ => ((max z 1 : ℕ) : ℝ))).comp
    measurable_treeSize)).div_const _

theorem scale_treePair_eq_sizePair (B B' : ℕ → ℝ) {r : ℕ}
    (hr : 0 < r) (hBr : B' r ≠ 0) (a b : ℝ≥0)
    (τ : LocallyFinite.Tree) (hz : 0 < treeSize τ) (S : Ioi (0 : ℝ))
    (hS : (S : ℝ) = treeSize τ / (r : ℝ)) (hSa : (S : ℝ) * a ≤ b) :
    (timeSpaceScale (a : ℝ) b.coe_nonneg
        ((treePairPath B' r b τ).1, B' r / B (treeSize τ), S),
      timeSpaceScaleC (a : ℝ) b.coe_nonneg
        ((treePairPath B' r b τ).2, (B (treeSize τ) / B' r) * (r / (treeSize τ : ℝ)), S)) =
      sizePair B a τ := by
  let z := treeSize τ
  have hzR : (z : ℝ) ≠ 0 := by exact_mod_cast hz.ne'
  have hrR : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
  have htime (u : Icc (0 : ℝ) a) : (S : ℝ) * u ≤ b :=
    (mul_le_mul_of_nonneg_left u.2.2 S.2.le).trans hSa
  have harg (u : Icc (0 : ℝ) a) : (r : ℝ) * ((S : ℝ) * u) = (z : ℝ) * u := by
    rw [hS]
    dsimp only [z]
    field_simp
  apply Prod.ext
  · apply Skorokhod.ext
    intro u
    change B' r / B z *
      (BGW.Probability.RealWalk.partialSum (PathTail.treeIncrementSeq τ)
        ⌊(r : ℝ) * min ((S : ℝ) * u) b⌋₊ / B' r) =
      BGW.Probability.RealWalk.partialSum (PathTail.treeIncrementSeq τ)
        ⌊(z : ℝ) * u⌋₊ / B z
    rw [min_eq_left (htime u), harg u]
    exact div_mul_div_cancel₀' hBr _ _
  · apply ContinuousMap.ext
    intro u
    simp only [timeSpaceScaleC, treePairPath, treeHeightPath,
      dite_eq_left (continuous_treeHeightLin τ), ContinuousMap.coe_mk, sizePair]
    change (B z / B' r * (r / (z : ℝ))) *
        (B' r / r * treeHeightLin τ ((r : ℝ) * min ((S : ℝ) * u) b)) =
      B z / z * treeHeightLin τ ((z : ℝ) * u)
    rw [min_eq_left (htime u), harg u]
    field_simp [hBr, hrR, hzR]

theorem tendsto_sizePair {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ}
    (hc : IsCritical μ) (hne : μ 1 ≠ 1) (hap : Aperiodic μ)
    (hB : IsRealStableAttracted (realOffspringStepLaw μ) θ B) {A : Set ℕ}
    {a : ℝ≥0} (ha : a ∈ Set.Ioo (0 : ℝ≥0) 1)
    {q : ℕ → ℕ} (hqtop : Tendsto q atTop atTop) (hq : ∀ k, ZetaAAdmissible μ A (q k)) :
    Tendsto (fun k => (zetaATreeLaw μ A (q k)).map (sizePair B a)) atTop
      (𝓝 ((excLaw θ).map (restrictPair ha.2.le))) := by
  change 0 < a ∧ a < 1 at ha
  let b : ℝ≥0 := (a + 1) / 2
  have hab : a < b := by
    change (a : ℝ) < (b : ℝ)
    dsimp [b]
    linarith [show (a : ℝ) < 1 from ha.2]
  have hb : b ∈ Set.Ioo (0 : ℝ≥0) 1 := by
    refine ⟨ha.1.trans hab, ?_⟩
    change (b : ℝ) < 1
    dsimp [b]
    linarith [show (a : ℝ) < 1 from ha.2]
  have ha0 : (0 : ℝ) < a := NNReal.coe_pos.mpr ha.1
  have hb0 : (0 : ℝ) < b := NNReal.coe_pos.mpr hb.1
  have habR : (a : ℝ) < b := NNReal.coe_lt_coe.mpr hab
  have hDA := (BGWLeaves.stableDomain_of_isRealStableAttracted hc hne hB).1
  have hA := measure_ne_zero_of_sequence hc hne hqtop hq
  have hp : 0 < (μ.toMeasure A).toReal := ENNReal.toReal_pos hA (measure_ne_top _ _)
  obtain ⟨B', hdom, hnorm⟩ := exists_stableDomain_ratio hc hne hB
  let P := fun k => zetaATreeLaw μ A (q k)
  let r := fun k => explorationIndex μ A (q k)
  let Z := fun k => treePairPath B' (r k) b
  let K := fun k τ => (B' (r k) / B (treeSize τ),
    B (treeSize τ) / B' (r k) * ((r k : ℝ) / treeSize τ))
  let S := fun k => clockScale (r k)
  let G := fun k τ =>
    (Skorokhod.timeSpaceScale (a : ℝ) b.coe_nonneg ((Z k τ).1, (K k τ).1, S k τ),
      Skorokhod.timeSpaceScaleC (a : ℝ) b.coe_nonneg ((Z k τ).2, (K k τ).2, S k τ))
  have hrtop : Tendsto r atTop atTop := (explorationIndex_atTop hA).comp hqtop
  have hrdet : Tendsto (fun k => (r k : ℝ) / q k) atTop (𝓝 (1 / (μ.toMeasure A).toReal)) :=
    (explorationIndex_ratio hA).comp hqtop
  have hsize : ∀ ε > 0, Tendsto (fun k => (P k).toMeasure.real
      {τ | ε < dist ((treeSize τ : ℝ) / q k) (1 / (μ.toMeasure A).toReal)}) atTop (𝓝 0) := by
    intro ε hε
    simpa only [Real.dist_eq] using conditional_size_concentration hc hne hDA hA hqtop hq hε
  have hratio := probability_index_ratio P hqtop (one_div_pos.mpr hp) hrdet hsize
  have hBNraw := probability_norming_ratio P hB hrtop hratio
  have hBN := probability_continuous_pair P (G := fun p : ℝ × ℝ => p.1 * p.2)
    hBNraw (probability_const P (hnorm.comp hrtop))
    (continuous_fst.mul continuous_snd).continuousAt
  simp only [one_mul] at hBN
  have hBN' : ∀ ε > 0, Tendsto (fun k => (P k).toMeasure.real
      {τ | ε < dist (B (treeSize τ) / B' (r k)) 1}) atTop (𝓝 0) := by
    intro ε hε
    apply (hBN ε hε).congr'
    filter_upwards [hrtop.eventually hB.pos] with k hk
    congr 1
    ext τ
    change (ε < dist (B (treeSize τ) / B (r k) * (B (r k) / B' (r k))) 1) ↔ _
    rw [div_mul_div_cancel₀ hk.ne']
    rfl
  have hK₁ := probability_continuous P (G := fun x : ℝ => 1 / x) hBN'
    (continuousAt_const.div continuousAt_id one_ne_zero)
  simp only [one_div_div, div_one] at hK₁
  have hRinv := probability_continuous P (G := fun x : ℝ => 1 / x) hratio
    (continuousAt_const.div continuousAt_id one_ne_zero)
  simp only [one_div_div, div_one] at hRinv
  have hK₂ := probability_continuous_pair P (G := fun p : ℝ × ℝ => p.1 * p.2) hBN' hRinv
    (continuous_fst.mul continuous_snd).continuousAt
  simp only [one_mul] at hK₂
  have hKerr : ∀ ε > 0, Tendsto (fun k => (P k).toMeasure.real
      {τ | ε < dist (K k τ) 1}) atTop (𝓝 0) := by
    intro ε hε
    have hlim := (hK₁ ε hε).add (hK₂ ε hε)
    simp only [zero_add] at hlim
    refine squeeze_zero (fun _ => measureReal_nonneg) (fun k => ?_) hlim
    have heq : {τ | ε < dist (K k τ) 1} =
        {τ | ε < dist (B' (r k) / B (treeSize τ)) 1} ∪
          {τ | ε < dist (B (treeSize τ) / B' (r k) * ((r k : ℝ) / treeSize τ)) 1} := by
      ext τ
      change ε < max _ _ ↔ (_ ∨ _)
      exact lt_max_iff
    rw [heq]
    exact measureReal_union_le _ _
  have hmaxsize := probability_max_index P hqtop (one_div_pos.mpr hp) hsize
  have hSratio := probability_index_ratio P hqtop (one_div_pos.mpr hp) hrdet hmaxsize
  have hSerr : ∀ ε > 0, Tendsto (fun k => (P k).toMeasure.real
      {τ | ε < dist (S k τ : ℝ) 1}) atTop (𝓝 0) := by
    intro ε hε
    apply (hSratio ε hε).congr'
    filter_upwards [hrtop.eventually_ge_atTop 1] with k hk
    congr 1
    ext τ
    change (ε < dist ((max (treeSize τ) 1 : ℕ) / (r k : ℝ)) 1) ↔ _
    simp only [S, clockScale, max_eq_left hk]
    rfl
  have hZm : ∀ k, Measurable (Z k) := fun k => measurable_treePairPath B' (r k) b
  have hBz : Measurable (fun τ => B (treeSize τ)) :=
    (measurable_from_nat (f := B)).comp measurable_treeSize
  have hzr : Measurable (fun τ => (treeSize τ : ℝ)) :=
    (measurable_from_nat (f := fun z : ℕ => (z : ℝ))).comp measurable_treeSize
  have hKm : ∀ k, Measurable (K k) := fun k =>
    (measurable_const.div hBz).prodMk ((hBz.div measurable_const).mul (measurable_const.div hzr))
  have hSm : ∀ k, Measurable (fun τ => (S k τ : ℝ)) := fun k => measurable_clockScale _
  have hGm : ∀ k, Measurable (G k) := fun k =>
    ((measurable_timeSpaceScale (a : ℝ) b.coe_nonneg).comp
      ((hZm k).fst.prodMk ((hKm k).fst.prodMk (hSm k).subtype_mk))).prodMk
    ((measurable_timeSpaceScaleC (a : ℝ) b.coe_nonneg).comp
      ((hZm k).snd.prodMk ((hKm k).snd.prodMk (hSm k).subtype_mk)))
  have hlim := ClassicalLimits.Perturbation.lem_CVproba_pair ha.1 hab P Z K S hZm hKm hSm
    ((excLaw θ).map (restrictPair hb.2.le))
    (marked_pair_prefix_all hdom hap hqtop hq b hb)
    (ae_continuousAt_exc_prefix hB.index_mem ha.1 hab.le hb.2) hKerr hSerr
  have hlimlaw : ((excLaw θ).map (restrictPair hb.2.le)).map (restrictPair hab.le) =
      (excLaw θ).map (restrictPair ha.2.le) := by
    apply Subtype.ext
    change ((excLaw θ).toMeasure.map (restrictPair hb.2.le)).map (restrictPair hab.le) =
      (excLaw θ).toMeasure.map (restrictPair ha.2.le)
    erw [Measure.map_map (measurable_restrictPair hab.le) (measurable_restrictPair hb.2.le)]
    rfl
  rw [hlimlaw] at hlim
  have herr : ∀ ε > 0, Tendsto (fun k => (P k).toMeasure.real
      {τ | ε < dist (sizePair B a τ) (G k τ)}) atTop (𝓝 0) := by
    intro ε hε
    let η := ((b : ℝ) - a) / (2 * a)
    have hη : 0 < η := div_pos (sub_pos.mpr habR) (mul_pos (by norm_num) ha0)
    refine squeeze_zero' (Eventually.of_forall fun _ => measureReal_nonneg) ?_ (hSerr η hη)
    filter_upwards [hqtop.eventually_ge_atTop 1, hrtop.eventually_ge_atTop 1,
      hrtop.eventually_ge_atTop 1] with k hqk hrk _
    have hmem := ae_finite_marks (hq k)
    have hsub : {τ | ε < dist (sizePair B a τ) (G k τ)} ≤ᵐ[(P k).toMeasure]
        {τ | η < dist (S k τ : ℝ) 1} := by
      filter_upwards [hmem] with τ hτ hbadτ
      by_contra hout
      have hsg : dist (S k τ : ℝ) 1 ≤ η := le_of_not_gt hout
      have hz : 0 < treeSize τ := by
        obtain ⟨t, rfl, _⟩ := hτ
        rw [treeSize_toLocallyFinite]
        exact t.size_pos
      have hSeq : (S k τ : ℝ) = treeSize τ / (r k : ℝ) := by
        change ((max (treeSize τ) 1 : ℕ) : ℝ) / (max (r k) 1 : ℕ) = _
        rw [max_eq_left (Nat.succ_le_iff.mpr hz), max_eq_left hrk]
      have hSa : (S k τ : ℝ) * a ≤ b := by
        rw [Real.dist_eq] at hsg
        have hsupper := (abs_le.mp hsg).2
        have heq : η * (a : ℝ) = ((b : ℝ) - a) / 2 := by
          dsimp [η]
          field_simp [ha0.ne']
        have hmul := mul_le_mul_of_nonneg_right (show (S k τ : ℝ) ≤ 1 + η by linarith) a.coe_nonneg
        nlinarith
      have hid : G k τ = sizePair B a τ :=
        scale_treePair_eq_sizePair B B' (by omega : 0 < r k)
          (hdom.pos _ (by omega)).ne' a b τ hz (S k τ) hSeq hSa
      change ε < dist (sizePair B a τ) (G k τ) at hbadτ
      rw [hid, dist_self] at hbadτ
      exact (not_lt.mpr hε.le) hbadτ
    exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hsub)
  exact BGW.MetricMeasure.tendsto_probabilityMap_of_error_probability P
    (fun _ => measurable_sizePair B a) hGm herr hlim


end BGWLeaves.GeneralAFunctional.TreeClockTransport
