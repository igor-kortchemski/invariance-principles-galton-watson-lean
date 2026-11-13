/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.ExactContourPrefixError

/-!
# The terminal contour window under exact-size conditioning

Mirror invariance transfers the initial-window control supplied by height-prefix tightness.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal Classical
open BGW.Skorokhod BGW.StableTrees

namespace BGW.StableTrees.ExactContour

open BGW.StableTrees.DiscreteForest BGW.StableTrees.TailPair

private def initialExceed (a : ℝ≥0) (δ ε : ℝ) : Set C(Icc (0 : ℝ) (a : ℝ), ℝ) :=
  {f | ∃ t : Icc (0 : ℝ) (a : ℝ), (t : ℝ) ≤ δ ∧ ε < f t}

private theorem isOpen_initialExceed (a : ℝ≥0) (δ ε : ℝ) :
    IsOpen (initialExceed a δ ε) := by
  have he : initialExceed a δ ε = ⋃ t : Icc (0 : ℝ) (a : ℝ),
      ⋃ (_ : (t : ℝ) ≤ δ), {f : C(Icc (0 : ℝ) (a : ℝ), ℝ) | ε < f t} := by
    ext f
    simp [initialExceed]
  rw [he]
  exact isOpen_iUnion fun t => isOpen_iUnion fun _ =>
    isOpen_lt continuous_const (continuous_eval_const t)

/-- Every pointwise contour/height difference is bounded by the uniform prefix error. -/
theorem contourHeightError_ge (B : ℕ → ℝ) (n : ℕ) (a : ℝ≥0)
    (τ : LocallyFinite.Tree) (s : Icc (0 : ℝ) (a : ℝ)) :
    |treeContourPath B n a τ s - treeHeightPath B n a τ s| ≤ contourHeightError B n a τ := by
  have hcont : Continuous (fun s : Icc (0 : ℝ) (a : ℝ) =>
      |treeContourPath B n a τ s - treeHeightPath B n a τ s|) := by fun_prop
  have hb : BddAbove (Set.range fun s : Icc (0 : ℝ) (a : ℝ) =>
      |treeContourPath B n a τ s - treeHeightPath B n a τ s|) :=
    (isCompact_range hcont).bddAbove
  have hh := le_ciSup hb s
  simpa only [treeContourPath, dite_eq_left (continuous_treeContourLin _),
    treeHeightPath, dite_eq_left (continuous_treeHeightLin _), ContinuousMap.coe_mk,
      contourHeightError] using hh

private theorem exactContour_initial_small {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ}
    (h : StableDomain μ θ B) {q : ℕ → ℕ} (hqtop : Tendsto q atTop atTop)
    (hq : ∀ k, Admissible μ (q k)) {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) :
    ∃ δ > 0, δ ≤ (1 / 2 : ℝ) ∧ ∀ᶠ k in atTop,
      (exactTreeLaw μ (q k) : Measure LocallyFinite.Tree).real
        ((treeContourPath B (q k) (1 / 2)) ⁻¹' initialExceed (1 / 2) δ ε) ≤ η := by
  let a : ℝ≥0 := 1 / 2
  have ha : a ∈ Ioo (0 : ℝ≥0) 1 := by norm_num [a]
  have htight := isTightMeasureSet_exactHeight_prefix h hqtop hq a ha
  obtain ⟨K, hK, hp⟩ := isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mp htight
    (ENNReal.ofReal (η / 2)) (ENNReal.ofReal_pos.mpr (half_pos hη))
  let K' := K ∩ {f | f ⟨0, le_rfl, a.coe_nonneg⟩ = 0}
  have hK' : IsCompact K' := hK.inter_right (isClosed_eq (continuous_eval_const _) continuous_const)
  have hosc : ∃ δ > 0, ∀ f ∈ K', ∀ t : Icc (0 : ℝ) (a : ℝ),
      (t : ℝ) ≤ δ → |f t| ≤ ε / 3 := by
    let : CompactSpace K' := isCompact_iff_compactSpace.mp hK'
    have heval : Continuous (fun p : K' × Icc (0 : ℝ) (a : ℝ) => p.1.val p.2) := by fun_prop
    obtain ⟨d, hd, hbd⟩ := Metric.uniformContinuous_iff.mp
      (CompactSpace.uniformContinuous_of_continuous heval) (ε / 3) (by positivity)
    refine ⟨d / 2, half_pos hd, ?_⟩
    intro f hf t ht
    have hdist : dist ((⟨f, hf⟩ : K'), t)
        ((⟨f, hf⟩ : K'), (⟨0, le_rfl, a.coe_nonneg⟩ : Icc (0 : ℝ) (a : ℝ))) < d := by
      rw [Prod.dist_eq, dist_self, max_eq_right dist_nonneg, Subtype.dist_eq,
        Real.dist_eq, sub_zero, abs_of_nonneg t.property.1]
      exact ht.trans_lt (half_lt_self hd)
    have hh := hbd hdist
    change |f t - f ⟨0, le_rfl, a.coe_nonneg⟩| < ε / 3 at hh
    rw [hf.2, sub_zero] at hh
    exact hh.le
  obtain ⟨d, hd, hosc⟩ := hosc
  let δ := min d (1 / 2)
  refine ⟨δ, lt_min hd (by norm_num), min_le_right _ _, ?_⟩
  have herr := (tendsto_contourHeightError_prefix h hqtop hq a ha
    (show 0 < ε / 3 by positivity)).eventually_le_const (half_pos hη)
  filter_upwards [herr] with k hk
  have hsub : (treeContourPath B (q k) a) ⁻¹' initialExceed a δ ε ⊆
      {τ | ε / 3 < contourHeightError B (q k) a τ} ∪
      {τ | treeHeightPath B (q k) a τ ∉ K} := by
    rintro τ ⟨s, hs, hbad⟩
    by_cases he : ε / 3 < contourHeightError B (q k) a τ
    · exact Or.inl he
    · right
      intro hmem
      have hz : treeHeightPath B (q k) a τ ⟨0, le_rfl, a.coe_nonneg⟩ = 0 := by
        rw [treeHeightPath, dite_eq_left (continuous_treeHeightLin _)]
        change B (q k) / q k * treeHeightLin τ ((q k : ℝ) * 0) = 0
        rw [mul_zero, treeHeightLin]
        split_ifs with hτ
        · have hz0 : (PlaneTree.equivFiniteVertices.symm ⟨τ, hτ⟩).heightSeq 0 = 0 :=
            Nat.eq_zero_of_le_zero (PlaneTree.heightSeq_le _ 0)
          simp [PlaneTree.heightLin, hz0]
        · simp
      have hh := hosc _ ⟨hmem, hz⟩ s (hs.trans (min_le_left _ _))
      have hc := (contourHeightError_ge B (q k) a τ s).trans (le_of_not_gt he)
      have hH := le_abs_self (treeHeightPath B (q k) a τ s)
      have hC := (abs_le.mp hc).2
      linarith
  have hpK := hp _ (mem_range_self k)
  rw [ProbabilityMeasure.toMeasure_map, Measure.map_apply (measurable_treeHeightPath B (q k) a)
    hK.measurableSet.compl] at hpK
  have hpR := ENNReal.toReal_mono ENNReal.ofReal_ne_top hpK
  rw [ENNReal.toReal_ofReal (half_pos hη).le] at hpR
  change (exactTreeLaw μ (q k) : Measure LocallyFinite.Tree).real
    {τ | treeHeightPath B (q k) a τ ∉ K} ≤ η / 2 at hpR
  exact (measureReal_mono hsub).trans ((measureReal_union_le _ _).trans (by linarith))

private theorem terminal_reflection (B : ℕ → ℝ) {n : ℕ} (t : PlaneTree) (ht : t.size = n)
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

/-- For any fixed probability tolerance, a sufficiently small terminal contour window is
uniformly small for all sufficiently large admissible sizes. -/
theorem exactContour_terminal_small {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ}
    (h : StableDomain μ θ B) {q : ℕ → ℕ} (hqtop : Tendsto q atTop atTop)
    (hq : ∀ k, Admissible μ (q k)) {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) :
    ∃ δ > 0, δ ≤ (1 / 2 : ℝ) ∧ ∀ᶠ k in atTop,
      (exactTreeLaw μ (q k) : Measure LocallyFinite.Tree).real
        {τ | ∃ t : Icc (0 : ℝ) 1, 1 - δ ≤ (t : ℝ) ∧
          ε < B (q k) / q k * treeContourLin τ (2 * (q k : ℝ) * (t : ℝ))} ≤ η := by
  obtain ⟨δ, hδ, hδhalf, hp⟩ := exactContour_initial_small h hqtop hq hε hη
  refine ⟨δ, hδ, hδhalf, ?_⟩
  filter_upwards [hp] with k hk
  let A := (treeContourPath B (q k) (1 / 2)) ⁻¹' initialExceed (1 / 2) δ ε
  have hA : MeasurableSet A := (isOpen_initialExceed _ _ _).measurableSet.preimage
    (measurable_treeContourPath B (q k) (1 / 2))
  have hsize : ∀ᵐ τ ∂(exactTreeLaw μ (q k) : Measure LocallyFinite.Tree),
      τ ∈ LocallyFinite.sizeEvent (q k) := by
    rw [exactTreeLaw_toMeasure μ (q k) (hq k)]
    exact ae_cond_mem (LocallyFinite.measurableSet_sizeEvent _)
  have hsub : {τ | ∃ t : Icc (0 : ℝ) 1, 1 - δ ≤ (t : ℝ) ∧
      ε < B (q k) / q k * treeContourLin τ (2 * (q k : ℝ) * (t : ℝ))} ≤ᵐ[
      (exactTreeLaw μ (q k) : Measure LocallyFinite.Tree)] treeMirror ⁻¹' A := by
    filter_upwards [hsize] with τ hτ hbad
    obtain ⟨t, rfl⟩ := (LocallyFinite.exists_toLocallyFinite_iff τ).mpr hτ.1
    exact terminal_reflection B t
      ((LocallyFinite.toLocallyFinite_mem_sizeEvent_iff t (q k)).mp hτ) hδhalf hε hbad
  have hmap : (exactTreeLaw μ (q k) : Measure LocallyFinite.Tree) (treeMirror ⁻¹' A) =
      (exactTreeLaw μ (q k) : Measure LocallyFinite.Tree) A := by
    rw [← Measure.map_apply measurable_treeMirror hA]
    exact congrArg (fun P : ProbabilityMeasure LocallyFinite.Tree => P.toMeasure A)
      (map_treeMirror_exactTreeLaw μ (q k))
  have hle := ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hsub)
  rw [hmap] at hle
  exact hle.trans hk

/-- **Terminal contour window** (mirror symmetry and `H^exc(0) = 0`): the probability that the
normalized contour exceeds `ε` on `[1 - δ, 1]` is asymptotically small as `δ ↓ 0`. -/
theorem tendsto_exactContour_terminalWindow {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ}
    (h : StableDomain μ θ B) {q : ℕ → ℕ} (hqtop : Tendsto q atTop atTop)
    (hq : ∀ k, Admissible μ (q k)) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun δ : ℝ => limsup (fun k : ℕ =>
        (exactTreeLaw μ (q k) : Measure BGW.LocallyFinite.Tree).real
          {τ | ∃ t : Set.Icc (0 : ℝ) 1, 1 - δ ≤ (t : ℝ) ∧
            ε < B (q k) / q k * treeContourLin τ (2 * (q k : ℝ) * (t : ℝ))}) atTop)
      (𝓝[>] 0) (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro η hη
  obtain ⟨d, hd, _, hp⟩ := exactContour_terminal_small h hqtop hq hε (half_pos hη)
  filter_upwards [Ioo_mem_nhdsGT hd] with δ hδ
  have hnn : 0 ≤ limsup (fun k : ℕ =>
      (exactTreeLaw μ (q k) : Measure LocallyFinite.Tree).real
        {τ | ∃ t : Icc (0 : ℝ) 1, 1 - δ ≤ (t : ℝ) ∧
          ε < B (q k) / q k * treeContourLin τ (2 * (q k : ℝ) * (t : ℝ))}) atTop :=
    le_limsup_of_frequently_le (Frequently.of_forall fun _ => measureReal_nonneg)
      (isBoundedUnder_of ⟨1, fun _ => measureReal_le_one⟩)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hnn]
  apply lt_of_le_of_lt _ (half_lt_self hη)
  apply limsup_le_of_le (Filter.isCoboundedUnder_le_of_le atTop fun _ => measureReal_nonneg)
  filter_upwards [hp] with k hk
  apply (measureReal_mono (show {τ | ∃ t : Icc (0 : ℝ) 1, 1 - δ ≤ (t : ℝ) ∧
      ε < B (q k) / q k * treeContourLin τ (2 * (q k : ℝ) * (t : ℝ))} ⊆
      {τ | ∃ t : Icc (0 : ℝ) 1, 1 - d ≤ (t : ℝ) ∧
      ε < B (q k) / q k * treeContourLin τ (2 * (q k : ℝ) * (t : ℝ))} from ?_)).trans hk
  rintro τ ⟨t, ht, hb⟩
  exact ⟨t, by linarith [hδ.2], hb⟩

end BGW.StableTrees.ExactContour
