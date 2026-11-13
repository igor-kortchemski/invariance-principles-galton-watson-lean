module

public import BGWLeaves.GeneralAFunctional.TreeClockTransport
public import BGWLeaves.LeafLimits.Helpers
public import BGW.StableTrees.ExactContourGlobal
public import BGW.Skorokhod.OptionalGaps
public import Mathlib.Topology.ContinuousMap.SecondCountableSpace
public import BGW.StableTrees.UnitExcursionDensity

/-! Reflection and contour–height comparison under arbitrary offspring-mark conditioning. -/
@[expose] public section
namespace BGWLeaves.GeneralAFunctional.TreeContour
open MeasureTheory ProbabilityTheory Filter BGW
open BGW.StableTrees BGW.LocallyFinite BGWLeaves.StableAnalysis
open BGW.StableTrees.ExactContour Set
open BGWLeaves.GeneralAFunctional.TreeSize BGWLeaves.GeneralAFunctional.TreeClockTransport
open BGWLeaves.GeneralAFunctional.TreeMirror
open scoped ENNReal NNReal Topology

noncomputable def sizeHeight (B : ℕ → ℝ) (a : ℝ≥0) (τ : LocallyFinite.Tree) :=
  TailPair.treeHeightPath B (treeSize τ) a τ

noncomputable def sizeContour (B : ℕ → ℝ) (a : ℝ≥0) (τ : LocallyFinite.Tree) :=
  ExactContour.treeContourPath B (treeSize τ) a τ

theorem measurable_sizeHeight (B : ℕ → ℝ) (a : ℝ≥0) : Measurable (sizeHeight B a) :=
  measurable_comp_nat measurable_treeSize (fun n => TailPair.measurable_treeHeightPath B n a)

theorem measurable_sizeContour (B : ℕ → ℝ) (a : ℝ≥0) : Measurable (sizeContour B a) :=
  measurable_comp_nat measurable_treeSize (fun n => ExactContour.measurable_treeContourPath B n a)

theorem tendsto_sizeHeight {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ}
    (hc : IsCritical μ) (hne : μ 1 ≠ 1) (hap : Aperiodic μ)
    (hB : IsRealStableAttracted (realOffspringStepLaw μ) θ B)
    {a : ℝ≥0} (ha : a ∈ Set.Ioo (0 : ℝ≥0) 1)
    {A : Set ℕ} {q : ℕ → ℕ} (hqtop : Tendsto q atTop atTop) (hq : ∀ k, ZetaAAdmissible μ A (q k)) :
    Tendsto (fun k => (zetaATreeLaw μ A (q k)).map (sizeHeight B a)) atTop
      (𝓝 (((excLaw θ).map (restrictPair ha.2.le)).map Prod.snd)) := by
  have ht := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _
    (tendsto_sizePair hc hne hap hB ha hqtop hq) continuous_snd
  have heq (k : ℕ) : ((zetaATreeLaw μ A (q k)).map (sizePair B a)).map Prod.snd =
      (zetaATreeLaw μ A (q k)).map (sizeHeight B a) := by
    apply Subtype.ext
    change ((zetaATreeLaw μ A (q k)).toMeasure.map (sizePair B a)).map Prod.snd = _
    rw [Measure.map_map measurable_snd (measurable_sizePair B a)]
    rfl
  exact ht.congr fun k => heq k

theorem compact_containment {a : ℝ≥0}
    {P : ℕ → ProbabilityMeasure C(Set.Icc (0 : ℝ) a, ℝ)} {Q : ProbabilityMeasure C(Set.Icc (0 : ℝ) a, ℝ)}
    (hP : Tendsto P atTop (𝓝 Q)) {η : ℝ} (hη : 0 < η) :
    ∃ K : Set C(Set.Icc (0 : ℝ) a, ℝ), IsCompact K ∧
      ∀ n, (P n).toMeasure Kᶜ ≤ ENNReal.ofReal η := by
  have hc : IsCompact (insert Q (Set.range P)) := hP.isCompact_insert_range
  have ht := isTightMeasureSet_of_isCompact_closure
    (S := insert Q (Set.range P)) (by rw [hc.isClosed.closure_eq]; exact hc)
  obtain ⟨K, hK, hp⟩ := isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mp ht
    (ENNReal.ofReal η) (ENNReal.ofReal_pos.mpr hη)
  refine ⟨K, hK, fun n => ?_⟩
  exact hp (P n).toMeasure ⟨P n, Set.mem_insert_of_mem _ (Set.mem_range_self n), rfl⟩

theorem tendsto_prefix_contour_error {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ}
    (h : StableDomain μ θ B) (hap : Aperiodic μ)
    {a : ℝ≥0} (ha : a ∈ Set.Ioo (0 : ℝ≥0) 1) {A : Set ℕ} {q : ℕ → ℕ}
    (hqtop : Tendsto q atTop atTop) (hq : ∀ k, ZetaAAdmissible μ A (q k))
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun k => (zetaATreeLaw μ A (q k)).toMeasure.real
      {τ | ε < ExactContour.contourHeightError B (treeSize τ) a τ}) atTop (𝓝 0) := by
  let a' : ℝ≥0 := (a + 1) / 2
  have haa' : a < a' := by
    change (a : ℝ) < (a' : ℝ)
    dsimp [a']
    linarith [show (a : ℝ) < 1 from ha.2]
  have ha' : a' ∈ Set.Ioo (0 : ℝ≥0) 1 := by
    refine ⟨ha.1.trans haa', ?_⟩
    change (a' : ℝ) < 1
    dsimp [a']
    linarith [show (a : ℝ) < 1 from ha.2]
  have ht := tendsto_sizeHeight h.critical h.nondegenerate hap h.isRealStableAttracted ha' hqtop hq
  rw [Metric.tendsto_nhds]
  intro η hη
  obtain ⟨K, hK, hp⟩ := compact_containment ht (half_pos hη)
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (ExactContour.eventually_contourHeightError_le_of_compact h haa' ha'.2 K hK hε)
  filter_upwards [hqtop.eventually_ge_atTop N] with k hk
  rw [Real.dist_eq, sub_zero, abs_of_nonneg measureReal_nonneg]
  have hmem := ae_finite_marks (hq k)
  have hsub : {τ | ε < ExactContour.contourHeightError B (treeSize τ) a τ} ≤ᵐ[
      (zetaATreeLaw μ A (q k)).toMeasure] {τ | sizeHeight B a' τ ∉ K} := by
    filter_upwards [hmem] with τ hτ hbad
    intro hgood
    obtain ⟨t, rfl, ht⟩ := hτ
    have hqsize : q k ≤ t.size := ht ▸ treeACount_le_size A t
    have hbound := hN t.size (hk.trans hqsize) t rfl
    dsimp only [sizeHeight] at hgood
    rw [treeSize_toLocallyFinite] at hgood hbad
    exact (not_le_of_gt hbad) (hbound hgood)
  have hpK := hp k
  rw [ProbabilityMeasure.toMeasure_map,
    Measure.map_apply (measurable_sizeHeight B a') hK.measurableSet.compl] at hpK
  have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top ((measure_mono_ae hsub).trans hpK)
  rw [ENNReal.toReal_ofReal (half_pos hη).le] at hr
  exact hr.trans_lt (half_lt_self hη)

theorem tendsto_sizeContour_prefix {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ}
    (h : StableDomain μ θ B) (hap : Aperiodic μ)
    {a : ℝ≥0} (ha : a ∈ Set.Ioo (0 : ℝ≥0) 1) {A : Set ℕ} {q : ℕ → ℕ}
    (hqtop : Tendsto q atTop atTop) (hq : ∀ k, ZetaAAdmissible μ A (q k)) :
    Tendsto (fun k => (zetaATreeLaw μ A (q k)).map (sizeContour B a)) atTop
      (𝓝 (((excLaw θ).map (restrictPair ha.2.le)).map Prod.snd)) := by
  apply BGW.MetricMeasure.tendsto_probabilityMap_of_error_probability
    (fun k => zetaATreeLaw μ A (q k)) (fun _ => measurable_sizeContour B a)
    (fun _ => measurable_sizeHeight B a) ?_
    (tendsto_sizeHeight h.critical h.nondegenerate hap h.isRealStableAttracted ha hqtop hq)
  intro ε hε
  simpa only [sizeContour, sizeHeight, ExactContour.contourHeightError_eq_dist] using
    tendsto_prefix_contour_error h hap ha hqtop hq hε

def initialExceed (a : ℝ≥0) (δ ε : ℝ) : Set C(Icc (0 : ℝ) (a : ℝ), ℝ) :=
  {f | ∃ t : Icc (0 : ℝ) (a : ℝ), (t : ℝ) ≤ δ ∧ ε < f t}

theorem isOpen_initialExceed (a : ℝ≥0) (δ ε : ℝ) :
    IsOpen (initialExceed a δ ε) := by
  have he : initialExceed a δ ε = ⋃ t : Icc (0 : ℝ) (a : ℝ),
      ⋃ (_ : (t : ℝ) ≤ δ), {f : C(Icc (0 : ℝ) (a : ℝ), ℝ) | ε < f t} := by
    ext f
    simp [initialExceed]
  rw [he]
  exact isOpen_iUnion fun t => isOpen_iUnion fun _ =>
    isOpen_lt continuous_const (continuous_eval_const t)


theorem terminal_reflection (B : ℕ → ℝ) {n : ℕ} (t : PlaneTree) (ht : t.size = n)
    {δ ε : ℝ} (hδ : δ ≤ 1 / 2) (hε : 0 < ε)
    (hbad : ∃ x : Icc (0 : ℝ) 1, 1 - δ ≤ (x : ℝ) ∧
      ε < B n / n * treeContourLin t.toLocallyFinite (2 * (n : ℝ) * (x : ℝ))) :
    treeContourPath B n (1 / 2) (treeMirror t.toLocallyFinite) ∈ initialExceed (1 / 2) δ ε := by
  obtain ⟨x, hx, hbad⟩ := hbad
  rw [treeContourLin_toLocallyFinite] at hbad
  have hn : (0 : ℝ) < n := by rw [← ht]; exact_mod_cast PlaneTree.size_pos t
  have hN : ((2 * (t.size - 1) : ℕ) : ℝ) = 2 * (n : ℝ) - 2 := by
    rw [Nat.cast_mul, Nat.cast_sub (by have := PlaneTree.size_pos t; omega), ht]
    norm_num
    ring
  have htime : 2 * (n : ℝ) * (x : ℝ) < 2 * (n : ℝ) - 2 := by
    by_contra hnot
    have hh := PlaneTree.contourLin_of_end_le t (s := 2 * (n : ℝ) * (x : ℝ))
      (by rw [hN]; exact le_of_not_gt hnot)
    rw [hh, mul_zero] at hbad
    linarith
  let y : ℝ := (2 * (n : ℝ) - 2 - 2 * n * (x : ℝ)) / (2 * n)
  have hy0 : 0 ≤ y := div_nonneg (by linarith) (by positivity)
  have hyδ : y ≤ δ := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * n)).mpr
    have hh := mul_le_mul_of_nonneg_left hx hn.le
    nlinarith
  let s : Icc (0 : ℝ) ((1 / 2 : ℝ≥0) : ℝ) := ⟨y, hy0, by norm_num; linarith⟩
  refine ⟨s, hyδ, ?_⟩
  rw [treeMirror_toLocallyFinite, treeContourPath_toLocallyFinite]
  have hys : 2 * (n : ℝ) * (s : ℝ) = 2 * (n : ℝ) - 2 - 2 * n * (x : ℝ) := by
    dsimp [s, y]
    field_simp
  have hsizeR : 2 * ((t.size : ℝ) - 1) = 2 * (n : ℝ) - 2 := by rw [ht]; ring
  rw [hys, PlaneTree.contourLin_mirror t (by linarith)
    (by rw [hsizeR]; nlinarith [x.property.1]), hsizeR,
    show 2 * (n : ℝ) - 2 - (2 * n - 2 - 2 * n * (x : ℝ)) =
      2 * n * (x : ℝ) by ring]
  exact hbad


theorem sizeContour_zero (B : ℕ → ℝ) (a : ℝ≥0) (τ : LocallyFinite.Tree) :
    sizeContour B a τ ⟨0, le_rfl, a.coe_nonneg⟩ = 0 := by
  rw [sizeContour, treeContourPath, dite_eq_left (continuous_treeContourLin _)]
  change B (treeSize τ) / treeSize τ * treeContourLin τ (2 * (treeSize τ : ℝ) * 0) = 0
  rw [mul_zero, treeContourLin]
  split_ifs
  · simp [PlaneTree.contourLin, PlaneTree.contourAt_zero]
  · simp

theorem initial_small {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ}
    (h : StableDomain μ θ B) (hap : Aperiodic μ)
    {A : Set ℕ} {q : ℕ → ℕ} (hqtop : Tendsto q atTop atTop) (hq : ∀ k, ZetaAAdmissible μ A (q k))
    {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) :
    ∃ δ > 0, δ ≤ (1 / 2 : ℝ) ∧ ∀ k,
      (zetaATreeLaw μ A (q k)).toMeasure.real
        ((sizeContour B (1 / 2)) ⁻¹' initialExceed (1 / 2) δ ε) ≤ η := by
  let a : ℝ≥0 := 1 / 2
  have ha : a ∈ Ioo (0 : ℝ≥0) 1 := by norm_num [a]
  obtain ⟨K, hK, hp⟩ := compact_containment
    (tendsto_sizeContour_prefix h hap ha hqtop hq) hη
  let K' := K ∩ {f | f ⟨0, le_rfl, a.coe_nonneg⟩ = 0}
  have hK' : IsCompact K' := hK.inter_right (isClosed_eq (continuous_eval_const _) continuous_const)
  have hosc : ∃ δ > 0, ∀ f ∈ K', ∀ t : Icc (0 : ℝ) (a : ℝ),
      (t : ℝ) ≤ δ → |f t| ≤ ε := by
    let : CompactSpace K' := isCompact_iff_compactSpace.mp hK'
    have heval : Continuous (fun p : K' × Icc (0 : ℝ) (a : ℝ) => p.1.val p.2) := by fun_prop
    obtain ⟨d, hd, hbd⟩ := Metric.uniformContinuous_iff.mp
      (CompactSpace.uniformContinuous_of_continuous heval) ε hε
    refine ⟨d / 2, half_pos hd, ?_⟩
    intro f hf t ht
    have hdist : dist ((⟨f, hf⟩ : K'), t)
        ((⟨f, hf⟩ : K'), (⟨0, le_rfl, a.coe_nonneg⟩ : Icc (0 : ℝ) (a : ℝ))) < d := by
      rw [Prod.dist_eq, dist_self, max_eq_right dist_nonneg, Subtype.dist_eq,
        Real.dist_eq, sub_zero, abs_of_nonneg t.property.1]
      exact ht.trans_lt (half_lt_self hd)
    have hh := hbd hdist
    change |f t - f ⟨0, le_rfl, a.coe_nonneg⟩| < ε at hh
    rw [hf.2, sub_zero] at hh
    exact hh.le
  obtain ⟨d, hd, hosc⟩ := hosc
  let δ := min d (1 / 2)
  refine ⟨δ, lt_min hd (by norm_num), min_le_right _ _, ?_⟩
  intro k
  have hsub : (sizeContour B a) ⁻¹' initialExceed a δ ε ⊆
      {τ | sizeContour B a τ ∉ K} := by
    rintro τ ⟨t, ht, hbad⟩ hmem
    have hh := hosc _ ⟨hmem, sizeContour_zero B a τ⟩ t (ht.trans (min_le_left _ _))
    exact (not_le_of_gt hbad) ((le_abs_self _).trans hh)
  have hpK := hp k
  rw [ProbabilityMeasure.toMeasure_map,
    Measure.map_apply (measurable_sizeContour B a) hK.measurableSet.compl] at hpK
  have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top ((measure_mono hsub).trans hpK)
  rw [ENNReal.toReal_ofReal hη.le] at hr
  exact hr

theorem terminal_small {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ}
    (h : StableDomain μ θ B) (hap : Aperiodic μ)
    {A : Set ℕ} {q : ℕ → ℕ} (hqtop : Tendsto q atTop atTop) (hq : ∀ k, ZetaAAdmissible μ A (q k))
    {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) :
    ∃ δ > 0, δ ≤ (1 / 2 : ℝ) ∧ ∀ k,
      (zetaATreeLaw μ A (q k)).toMeasure.real
        {τ | ∃ t : Icc (0 : ℝ) 1, 1 - δ ≤ (t : ℝ) ∧ ε < sizeContour B 1 τ t} ≤ η := by
  obtain ⟨δ, hδ, hδhalf, hp⟩ := initial_small h hap hqtop hq hε hη
  refine ⟨δ, hδ, hδhalf, ?_⟩
  intro k
  let D := (sizeContour B (1 / 2)) ⁻¹' initialExceed (1 / 2) δ ε
  have hA : MeasurableSet D := (isOpen_initialExceed _ _ _).measurableSet.preimage
    (measurable_sizeContour B (1 / 2))
  have hsize := ae_finite_marks (hq k)
  have hsub : {τ | ∃ t : Icc (0 : ℝ) 1, 1 - δ ≤ (t : ℝ) ∧ ε < sizeContour B 1 τ t} ≤ᵐ[
      (zetaATreeLaw μ A (q k)).toMeasure] treeMirror ⁻¹' D := by
    filter_upwards [hsize] with τ hτ hbad
    obtain ⟨t, rfl, _⟩ := hτ
    have hh : ∃ x : Icc (0 : ℝ) 1, 1 - δ ≤ (x : ℝ) ∧
        ε < B t.size / t.size * treeContourLin t.toLocallyFinite (2 * (t.size : ℝ) * (x : ℝ)) := by
      simpa only [sizeContour, treeSize_toLocallyFinite, treeContourPath,
        dite_eq_left (continuous_treeContourLin _), ContinuousMap.coe_mk] using hbad
    have hh' := terminal_reflection B t rfl hδhalf hε hh
    simpa only [D, Set.mem_preimage, sizeContour, treeMirror_toLocallyFinite,
      treeSize_toLocallyFinite, PlaneTree.size_mirror] using hh'
  have hmap : (zetaATreeLaw μ A (q k)).toMeasure (treeMirror ⁻¹' D) =
      (zetaATreeLaw μ A (q k)).toMeasure D := by
    rw [← Measure.map_apply measurable_treeMirror hA]
    exact congrArg (fun P : ProbabilityMeasure LocallyFinite.Tree => P.toMeasure D)
      (map_treeMirror_zetaATreeLaw (hq k))
  have hle := ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hsub)
  rw [hmap] at hle
  exact hle.trans (hp k)

theorem contourLin_nonneg (t : PlaneTree) {s : ℝ} (hs : 0 ≤ s) :
    0 ≤ t.contourLin s := by
  have hf := Nat.floor_le hs
  have hfl := Nat.lt_floor_add_one s
  apply add_nonneg <;> apply mul_nonneg
  · linarith
  · positivity
  · linarith
  · positivity

theorem sizeContour_nonneg {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ}
    (h : StableDomain μ θ B) (τ : LocallyFinite.Tree) (s : Icc (0 : ℝ) 1) :
    0 ≤ sizeContour B 1 τ s := by
  rw [sizeContour, treeContourPath, dite_eq_left (continuous_treeContourLin _)]
  change 0 ≤ B (treeSize τ) / treeSize τ * treeContourLin τ (2 * (treeSize τ : ℝ) * s)
  by_cases hz : treeSize τ = 0
  · simp [hz]
  apply mul_nonneg (div_nonneg (h.pos _ (Nat.pos_of_ne_zero hz)).le (Nat.cast_nonneg _))
  rw [treeContourLin]
  split_ifs
  · exact contourLin_nonneg _ (by nlinarith [s.property.1, Nat.cast_nonneg (α := ℝ) (treeSize τ)])
  · exact le_rfl

set_option backward.isDefEq.respectTransparency false in
theorem tendsto_sizeContour {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ}
    (h : StableDomain μ θ B) (hap : Aperiodic μ)
    {A : Set ℕ} {q : ℕ → ℕ} (hqtop : Tendsto q atTop atTop) (hq : ∀ k, ZetaAAdmissible μ A (q k)) :
    Tendsto (fun k => (zetaATreeLaw μ A (q k)).map (sizeContour B 1)) atTop
      (𝓝 ((excLaw θ).map Prod.snd)) := by
  let Y : LocallyFinite.Tree → C(Icc (0 : ℝ) 1, ℝ) := sizeContour B 1
  let ν : ProbabilityMeasure C(Icc (0 : ℝ) 1, ℝ) := (excLaw θ).map Prod.snd
  change Tendsto (fun k => (zetaATreeLaw μ A (q k)).map Y) atTop (𝓝 ν)
  let a : ℕ → ℝ := fun j => 1 - 1 / ((j : ℝ) + 2)
  have ha (j : ℕ) : 0 < a j ∧ a j < 1 := by
    have hj := Nat.cast_nonneg (α := ℝ) j
    have hd : (0 : ℝ) < j + 2 := by positivity
    constructor
    · exact sub_pos.mpr ((div_lt_one hd).mpr (by linarith))
    · exact sub_lt_self _ (by positivity)
  have hatop : Tendsto a atTop (𝓝 1) := by
    have hh := (tendsto_const_nhds (x := (1 : ℝ))).sub
      ((tendsto_atTop_add_const_right atTop (2 : ℝ)
        tendsto_natCast_atTop_atTop).const_div_atTop (1 : ℝ))
    simpa only [sub_zero] using hh
  apply BGW.Skorokhod.tendsto_continuous_of_tendsto_restrict_of_oscillation
    (T := (1 : ℝ)) (fun k => zetaATreeLaw μ A (q k)) (fun _ => (show Measurable Y from measurable_sizeContour B 1))
    (by norm_num) (fun j => (ha j).1.le) (fun j => (ha j).2) hatop
  · intro j
    let a' : ℝ≥0 := ⟨a j, (ha j).1.le⟩
    have ha' : a' ∈ Ioo (0 : ℝ≥0) 1 := ⟨(ha j).1, (ha j).2⟩
    have ht := tendsto_sizeContour_prefix h hap ha' hqtop hq
    have hseq (k : ℕ) : (zetaATreeLaw μ A (q k)).map
        (BGW.Skorokhod.restrictContinuous (ha j).2.le ∘ Y) =
        (zetaATreeLaw μ A (q k)).map (sizeContour B a') := by
      congr 1
      funext τ
      apply ContinuousMap.ext
      intro t
      dsimp only [Function.comp_def, BGW.Skorokhod.restrictContinuous, Y,
        ContinuousMap.comp_apply, ContinuousMap.coe_mk]
      simp only [sizeContour, treeContourPath, dite_eq_left (continuous_treeContourLin _),
        ContinuousMap.coe_mk]
    have hlim : ν.map
        (BGW.Skorokhod.restrictContinuous (ha j).2.le) =
        ((excLaw θ).map (restrictPair ha'.2.le)).map Prod.snd := by
      apply Subtype.ext
      change ((excLaw θ).toMeasure.map Prod.snd).map _ =
        ((excLaw θ).toMeasure.map (restrictPair ha'.2.le)).map Prod.snd
      erw [Measure.map_map (BGW.Skorokhod.lipschitzWith_one_restrictContinuous _).continuous.measurable
        measurable_snd, Measure.map_map measurable_snd (measurable_restrictPair _)]
      rfl
    erw [← hlim] at ht
    exact ht.congr fun k => (hseq k).symm
  · intro ε hε
    rw [Metric.tendsto_atTop]
    intro η hη
    obtain ⟨δ, hδ, _, hp⟩ := terminal_small h hap hqtop hq (half_pos hε) (half_pos hη)
    obtain ⟨N, hN⟩ := eventually_atTop.mp
      (hatop.eventually (lt_mem_nhds (show 1 - δ < 1 by linarith)))
    refine ⟨N, ?_⟩
    intro j hj
    have hnn : 0 ≤ limsup (fun k => (zetaATreeLaw μ A (q k)).toMeasure.real
        {τ | ε < ⨆ s : {s : Icc (0 : ℝ) 1 // a j ≤ (s : ℝ)},
          dist (Y τ s.val) (Y τ ⟨a j, (ha j).1.le, (ha j).2.le⟩)}) atTop :=
      le_limsup_of_frequently_le (Frequently.of_forall fun _ => measureReal_nonneg)
        (isBoundedUnder_of ⟨1, fun _ => measureReal_le_one⟩)
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hnn]
    apply lt_of_le_of_lt _ (half_lt_self hη)
    apply limsup_le_of_le (Filter.isCoboundedUnder_le_of_le atTop fun _ => measureReal_nonneg)
    apply Eventually.of_forall
    intro k
    have hsub : {τ | ε < ⨆ s : {s : Icc (0 : ℝ) 1 // a j ≤ (s : ℝ)},
        dist (Y τ s.val) (Y τ ⟨a j, (ha j).1.le, (ha j).2.le⟩)} ⊆
        {τ | ∃ t : Icc (0 : ℝ) 1, 1 - δ ≤ (t : ℝ) ∧ ε / 2 < Y τ t} := by
      intro τ hbad
      by_contra hh
      have hb (t : Icc (0 : ℝ) 1) (ht : a j ≤ (t : ℝ)) : Y τ t ≤ ε / 2 :=
        le_of_not_gt (fun hb => hh ⟨t, (hN j hj).le.trans ht, hb⟩)
      have hdist : (⨆ s : {s : Icc (0 : ℝ) 1 // a j ≤ (s : ℝ)},
          dist (Y τ s.val) (Y τ ⟨a j, (ha j).1.le, (ha j).2.le⟩)) ≤ ε := by
        let : Nonempty {s : Icc (0 : ℝ) 1 // a j ≤ (s : ℝ)} :=
          ⟨⟨⟨a j, (ha j).1.le, (ha j).2.le⟩, le_rfl⟩⟩
        apply ciSup_le
        intro s
        rw [Real.dist_eq, abs_le]
        have hs0 := sizeContour_nonneg h τ s.val
        have ha0 := sizeContour_nonneg h τ ⟨a j, (ha j).1.le, (ha j).2.le⟩
        have hs := hb s.val s.property
        have haa := hb ⟨a j, (ha j).1.le, (ha j).2.le⟩ le_rfl
        change 0 ≤ Y τ s.val at hs0
        change 0 ≤ Y τ ⟨a j, (ha j).1.le, (ha j).2.le⟩ at ha0
        constructor <;> linarith
      exact (not_le_of_gt hbad) hdist
    exact (measureReal_mono hsub).trans (hp k)

theorem tendsto_global_contour_error {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ}
    (h : StableDomain μ θ B) (hap : Aperiodic μ)
    {A : Set ℕ} {q : ℕ → ℕ} (hqtop : Tendsto q atTop atTop) (hq : ∀ k, ZetaAAdmissible μ A (q k))
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun k => (zetaATreeLaw μ A (q k)).toMeasure.real
      {τ | ε < contourHeightError B (treeSize τ) 1 τ}) atTop (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro η hη
  obtain ⟨K, hK, hp⟩ := compact_containment
    (tendsto_sizeContour h hap hqtop hq) (half_pos hη)
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (eventually_globalError_le_of_compact h K hK hε)
  filter_upwards [hqtop.eventually_ge_atTop N] with k hk
  rw [Real.dist_eq, sub_zero, abs_of_nonneg measureReal_nonneg]
  have hmem := ae_finite_marks (hq k)
  have hsub : {τ | ε < contourHeightError B (treeSize τ) 1 τ} ≤ᵐ[
      (zetaATreeLaw μ A (q k)).toMeasure] {τ | sizeContour B 1 τ ∉ K} := by
    filter_upwards [hmem] with τ hτ hbad
    intro hgood
    obtain ⟨t, rfl, ht⟩ := hτ
    have hqsize : q k ≤ t.size := ht ▸ treeACount_le_size A t
    have hbound := hN t.size (hk.trans hqsize) t rfl
    dsimp only [sizeContour] at hgood
    rw [treeSize_toLocallyFinite] at hgood hbad
    exact (not_le_of_gt hbad) (hbound hgood)
  have hpK := hp k
  rw [ProbabilityMeasure.toMeasure_map,
    Measure.map_apply (measurable_sizeContour B 1) hK.measurableSet.compl] at hpK
  have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top ((measure_mono_ae hsub).trans hpK)
  rw [ENNReal.toReal_ofReal (half_pos hη).le] at hr
  exact hr.trans_lt (half_lt_self hη)

set_option backward.isDefEq.respectTransparency false in
theorem tendsto_contour_height_stableDomain {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ}
    (h : StableDomain μ θ B) (hap : Aperiodic μ)
    {A : Set ℕ} {q : ℕ → ℕ} (hqtop : Tendsto q atTop atTop) (hq : ∀ k, ZetaAAdmissible μ A (q k)) :
    Tendsto (fun k => (zetaATreeLaw μ A (q k)).map (fun τ => (codingTriple B τ).2))
      atTop (𝓝 ((excLaw θ).map (fun p => (p.2, p.2)))) := by
  have ht := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _
    (tendsto_sizeContour h hap hqtop hq) (continuous_id.prodMk continuous_id)
  have hlim : ((excLaw θ).map Prod.snd).map (fun f => (f, f)) =
      (excLaw θ).map (fun p => (p.2, p.2)) := by
    apply Subtype.ext
    exact Measure.map_map (measurable_id.prodMk measurable_id) measurable_snd
  erw [hlim] at ht
  have hseq (k : ℕ) : ((zetaATreeLaw μ A (q k)).map (sizeContour B 1)).map (fun f => (f, f)) =
      (zetaATreeLaw μ A (q k)).map (fun τ => (sizeContour B 1 τ, sizeContour B 1 τ)) := by
    apply Subtype.ext
    exact Measure.map_map (measurable_id.prodMk measurable_id) (measurable_sizeContour B 1)
  have ht' := ht.congr fun k => hseq k
  apply BGW.MetricMeasure.tendsto_probabilityMap_of_error_probability
    (fun k => zetaATreeLaw μ A (q k)) (fun _ => measurable_snd.comp (measurable_codingTriple B))
    (fun _ => (measurable_sizeContour B 1).prodMk (measurable_sizeContour B 1)) ?_ ht'
  intro ε hε
  have heq (τ : LocallyFinite.Tree) : (codingTriple B τ).2 =
      (sizeContour B 1 τ, sizeHeight B 1 τ) := by
    simp only [codingTriple, rescaledContour_eq_treeContourPath,
      rescaledHeight_eq_treeHeightPath, sizeContour, sizeHeight]
  have herr := tendsto_global_contour_error h hap hqtop hq hε
  simp only [contourHeightError_eq_dist] at herr
  simpa only [Function.comp_apply, heq, dist_prod_same_left, sizeContour, sizeHeight, dist_comm] using herr

theorem codingPair_scale {μ : PMF ℕ} {θ : ℝ} {B B' : ℕ → ℝ}
    (h : StableDomain μ θ B') (τ : LocallyFinite.Tree) :
    (codingTriple B τ).2 =
      ((B (treeSize τ) / B' (treeSize τ)) • (codingTriple B' τ).2.1,
       (B (treeSize τ) / B' (treeSize τ)) • (codingTriple B' τ).2.2) := by
  have hfactor : B (treeSize τ) / treeSize τ =
      (B (treeSize τ) / B' (treeSize τ)) * (B' (treeSize τ) / treeSize τ) := by
    by_cases hz : treeSize τ = 0
    · simp [hz]
    · field_simp [(h.pos _ (Nat.pos_of_ne_zero hz)).ne']
  apply Prod.ext
  · apply ContinuousMap.ext
    intro t
    simp only [codingTriple, rescaledContour, ContinuousMap.coe_mk,
      ContinuousMap.smul_apply, smul_eq_mul]
    rw [hfactor, mul_assoc]
  · apply ContinuousMap.ext
    intro t
    simp only [codingTriple, rescaledHeight, ContinuousMap.coe_mk,
      ContinuousMap.smul_apply, smul_eq_mul]
    rw [hfactor, mul_assoc]

/-- Theorem 5.9(ii): joint contour/height convergence on the whole unit interval. -/
theorem thm_cvG_ii {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hap : Aperiodic μ) (hB : IsRealStableAttracted (realOffspringStepLaw μ) θ B)
    {A : Set ℕ} {q : ℕ → ℕ}
    (hqtop : Tendsto q atTop atTop) (hq : ∀ k, ZetaAAdmissible μ A (q k)) :
    Tendsto (fun k => (zetaATreeLaw μ A (q k)).map (fun τ => (codingTriple B τ).2))
      atTop (𝓝 ((excLaw θ).map (fun p => (p.2, p.2)))) := by
  obtain ⟨B', hdom, hratio⟩ := exists_stableDomain_ratio hc hne hB
  let R : LocallyFinite.Tree → ℝ := fun τ => B (treeSize τ) / B' (treeSize τ)
  have hR : Measurable R :=
    (measurable_from_top : Measurable (fun n : ℕ => B n / B' n)).comp measurable_treeSize
  have ht := BGW.Probability.tendsto_map_prodMk_of_tendsto_of_error
    (fun k => zetaATreeLaw μ A (q k))
    (fun _ => measurable_snd.comp (measurable_codingTriple B')) (fun _ => hR)
    (tendsto_contour_height_stableDomain hdom hap hqtop hq)
    (fun ε hε => probability_size_tendsto hqtop hq hratio hε)
  let G : (C(unitInterval, ℝ) × C(unitInterval, ℝ)) × ℝ →
      C(unitInterval, ℝ) × C(unitInterval, ℝ) := fun p => (p.2 • p.1.1, p.2 • p.1.2)
  have hG : Continuous G :=
    (continuous_snd.smul continuous_fst.fst).prodMk (continuous_snd.smul continuous_fst.snd)
  have hs := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _ ht hG
  have hseq (k : ℕ) : ((zetaATreeLaw μ A (q k)).map
      (fun τ => ((codingTriple B' τ).2, R τ))).map G =
      (zetaATreeLaw μ A (q k)).map (fun τ => (codingTriple B τ).2) := by
    apply Subtype.ext
    change ((zetaATreeLaw μ A (q k)).toMeasure.map _).map G = _
    erw [Measure.map_map hG.measurable
      ((measurable_snd.comp (measurable_codingTriple B')).prodMk hR)]
    congr 1
    funext τ
    exact (codingPair_scale hdom τ).symm
  have hlim : (((excLaw θ).map (fun p => (p.2, p.2))).map
      (fun p => (p, (1 : ℝ)))).map G = (excLaw θ).map (fun p => (p.2, p.2)) := by
    apply Subtype.ext
    change ((((excLaw θ).toMeasure.map (fun p => (p.2, p.2))).map
      (fun p => (p, (1 : ℝ)))).map G) = _
    erw [Measure.map_map hG.measurable (measurable_id.prodMk measurable_const),
      Measure.map_map (hG.measurable.comp (measurable_id.prodMk measurable_const))
        (measurable_snd.prodMk measurable_snd)]
    simp only [Function.comp_def, G, one_smul, id_eq]
    rfl
  erw [hlim] at hs
  exact hs.congr fun k => hseq k


end BGWLeaves.GeneralAFunctional.TreeContour
