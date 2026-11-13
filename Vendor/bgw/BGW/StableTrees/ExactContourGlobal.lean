/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.ExactContourConvergence
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap

/-!
# The global contour and height comparison

First-visit times recover all DFS heights from the contour. Compact sets of contours
control their suprema and oscillations, making the first-visit clock displacement vanish.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal Classical
open BGW.Skorokhod BGW.StableTrees

namespace BGW.StableTrees.ExactContour

open BGW.StableTrees.DiscreteForest BGW.StableTrees.TailPair

private theorem firstVisit_clock (B : ℕ → ℝ) {n : ℕ} (hn : 0 < n) (t : PlaneTree)
    (ht : t.size = n) {i : ℕ} (hi : i ≤ n) :
    ∃ s : unitInterval, treeContourPath B n 1 t.toLocallyFinite s = B n / n * t.heightSeq i ∧
      (s : ℝ) ≤ (i : ℝ) / n ∧ (i : ℝ) / n - (s : ℝ) = (t.heightSeq i : ℝ) / (2 * n) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hH := PlaneTree.heightSeq_le t i
  let v := 2 * i - t.heightSeq i
  have hv : (v : ℝ) = 2 * (i : ℝ) - t.heightSeq i := by
    dsimp [v]
    rw [Nat.cast_sub (by omega), Nat.cast_mul]
    norm_num
  have hvn : (v : ℝ) ≤ 2 * n := by
    have hiR : (i : ℝ) ≤ n := by exact_mod_cast hi
    nlinarith [Nat.cast_nonneg (α := ℝ) (t.heightSeq i)]
  let s : unitInterval := ⟨(v : ℝ) / (2 * n), by
    exact ⟨div_nonneg (Nat.cast_nonneg _) (by positivity),
      (div_le_one (by positivity : (0 : ℝ) < 2 * n)).mpr hvn⟩⟩
  refine ⟨s, ?_, ?_, ?_⟩
  · erw [treeContourPath_toLocallyFinite]
    have hs : 2 * (n : ℝ) * (s : ℝ) = v := by dsimp [s]; field_simp
    rw [hs, PlaneTree.contourLin_natCast]
    congr 2
    rcases hi.lt_or_eq with hi | he
    · exact_mod_cast PlaneTree.contourAt_firstVisit t (by omega : i < t.size)
    · subst i
      have hz : t.heightSeq n = 0 := PlaneTree.heightSeq_of_le t (by omega)
      simp only [v, hz, Nat.sub_zero]
      rw [PlaneTree.contourAt_of_lt t (by rw [ht]; omega)]
  · change (v : ℝ) / (2 * n) ≤ (i : ℝ) / n
    rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < 2 * n) hnR, hv]
    nlinarith [Nat.cast_nonneg (α := ℝ) (t.heightSeq i)]
  · change (i : ℝ) / n - (v : ℝ) / (2 * n) = _
    rw [hv]
    field_simp
    ring

private theorem compact_contour_oscillation
    (K : Set C(unitInterval, ℝ)) (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ g ∈ K, ∀ s t : unitInterval,
      |(s : ℝ) - t| ≤ δ → |g s - g t| ≤ ε := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have heval : Continuous (fun p : K × unitInterval => p.1.val p.2) := by fun_prop
  obtain ⟨η, hη, hb⟩ := Metric.uniformContinuous_iff.mp
    (CompactSpace.uniformContinuous_of_continuous heval) ε hε
  refine ⟨η / 2, half_pos hη, ?_⟩
  intro g hg s t hst
  have hd : dist ((⟨g, hg⟩ : K), s) ((⟨g, hg⟩ : K), t) < η := by
    rw [Prod.dist_eq, dist_self, max_eq_right dist_nonneg, Subtype.dist_eq, Real.dist_eq]
    exact hst.trans_lt (half_lt_self hη)
  exact (show |g s - g t| < ε by simpa only [Real.dist_eq] using hb hd).le

/-- On compact sets of normalized contours, the global height/contour error vanishes. -/
theorem eventually_globalError_le_of_compact {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ}
    (h : StableDomain μ θ B) (K : Set C(unitInterval, ℝ)) (hK : IsCompact K)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ t : PlaneTree, t.size = n → treeContourPath B n 1 t.toLocallyFinite ∈ K →
      contourHeightError B n 1 t.toLocallyFinite ≤ ε := by
  obtain ⟨M, hM, hbound⟩ := hK.isBounded.exists_pos_norm_le
  obtain ⟨δ, hδ, hosc⟩ := compact_contour_oscillation K hK (half_pos hε)
  have hclock : Tendsto (fun n : ℕ => 1 / (n : ℝ) + M / (2 * B n)) atTop (𝓝 0) := by
    have h1 := tendsto_natCast_atTop_atTop.const_div_atTop (1 : ℝ)
    have h2 := ((Scalar.tendsto_atTop h).const_mul_atTop (by norm_num : (0 : ℝ) <
      2)).const_div_atTop M
    simpa only [zero_add] using h1.add h2
  filter_upwards [eventually_ge_atTop 1, hclock.eventually_le_const hδ] with n hn hsmall
  intro t ht hmem
  have hn0 : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  have hB := h.pos n hn0
  have hc : 0 < B n / n := div_pos hB hnR
  let g := treeContourPath B n 1 t.toLocallyFinite
  have hval (i : ℕ) (hi : i ≤ n) (s : unitInterval)
      (hsi : |(i : ℝ) / n - (s : ℝ)| ≤ 1 / n) :
      |B n / n * (t.heightSeq i : ℝ) - g s| ≤ ε / 2 := by
    obtain ⟨v, hv, hvle, hdiff⟩ := firstVisit_clock B hn0 t ht hi
    have hheight : B n / n * (t.heightSeq i : ℝ) ≤ M := by
      rw [← hv]
      exact (le_abs_self _).trans ((Real.norm_eq_abs _ ▸
        ContinuousMap.norm_coe_le_norm _ _).trans (hbound _ hmem))
    have hdis : (t.heightSeq i : ℝ) / (2 * n) ≤ M / (2 * B n) := by
      rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < 2 * n) (by positivity)]
      have hh := (div_le_iff₀ hnR).mp (show B n * (t.heightSeq i : ℝ) / n ≤ M by
        simpa only [div_mul_eq_mul_div] using hheight)
      nlinarith
    have hdist : |(v : ℝ) - s| ≤ δ := by
      have hh := abs_sub_le (v : ℝ) ((i : ℝ) / n) (s : ℝ)
      rw [abs_of_nonpos (sub_nonpos.mpr hvle)] at hh
      have he : -((v : ℝ) - (i : ℝ) / n) = (t.heightSeq i : ℝ) / (2 * n) := by linarith
      rw [he] at hh
      linarith
    rw [← hv]
    exact hosc g hmem v s hdist
  change (⨆ s : unitInterval,
    |B n / n * treeContourLin t.toLocallyFinite (2 * (n : ℝ) * (s : ℝ)) -
      B n / n * treeHeightLin t.toLocallyFinite ((n : ℝ) * (s : ℝ))|) ≤ ε
  apply ciSup_le
  intro s
  rw [treeContourLin_toLocallyFinite]
  have hheight : treeHeightLin t.toLocallyFinite ((n : ℝ) * s) = t.heightLin ((n : ℝ) * s) := by
    rw [treeHeightLin, dite_eq_left t.finiteVertices_toLocallyFinite]
    change (PlaneTree.equivFiniteVertices.symm (PlaneTree.equivFiniteVertices t)).heightLin _ = _
    rw [Equiv.symm_apply_apply]
  rw [hheight]
  have hgs : g s = B n / n * t.contourLin (2 * (n : ℝ) * (s : ℝ)) :=
    treeContourPath_toLocallyFinite B n 1 t s
  rw [← hgs, abs_sub_comm]
  by_cases hs1 : (s : ℝ) = 1
  · have hs : s = 1 := Subtype.ext hs1
    subst s
    rw [hgs]
    have hz : t.heightLin (n : ℝ) = 0 := by
      rw [PlaneTree.heightLin_natCast, PlaneTree.heightSeq_of_le t (by omega)]
      norm_num
    have hcont : t.contourLin (2 * (n : ℝ) * (1 : ℝ)) = 0 :=
      PlaneTree.contourLin_of_end_le t (by
        rw [Nat.cast_mul, Nat.cast_sub (by have := PlaneTree.size_pos t; omega), ht]
        norm_num)
    simp only [Set.Icc.coe_one, mul_one]
    change |B n / n * t.heightLin (n : ℝ) - B n / n * t.contourLin (2 * n)| ≤ ε
    have hcend : t.contourLin (2 * (n : ℝ)) = 0 := by simpa only [mul_one] using hcont
    rw [hz, hcend]
    simpa only [mul_zero, sub_zero, abs_zero] using hε.le
  · let k := ⌊(n : ℝ) * (s : ℝ)⌋₊
    have hns : 0 ≤ (n : ℝ) * (s : ℝ) := mul_nonneg hnR.le s.property.1
    have hk0 : (k : ℝ) ≤ (n : ℝ) * (s : ℝ) := Nat.floor_le hns
    have hk1 : (n : ℝ) * (s : ℝ) < (k : ℝ) + 1 := Nat.lt_floor_add_one _
    have hslt : (s : ℝ) < 1 := lt_of_le_of_ne s.property.2 hs1
    have hklt : k < n := (Nat.floor_lt hns).mpr (by nlinarith [hslt])
    have hki : |(k : ℝ) / n - (s : ℝ)| ≤ 1 / n := by
      have he : (k : ℝ) / n - (s : ℝ) = ((k : ℝ) - n * s) / n := by field_simp
      rw [he, abs_div, abs_of_pos hnR]
      apply (div_le_div_iff_of_pos_right hnR).mpr
      rw [abs_of_nonpos (by linarith)]
      linarith
    have hki' : |((k + 1 : ℕ) : ℝ) / n - (s : ℝ)| ≤ 1 / n := by
      have he : ((k + 1 : ℕ) : ℝ) / n - (s : ℝ) =
          (((k + 1 : ℕ) : ℝ) - n * s) / n := by field_simp
      rw [he, abs_div, abs_of_pos hnR]
      apply (div_le_div_iff_of_pos_right hnR).mpr
      push_cast
      rw [abs_of_nonneg (by linarith)]
      linarith
    have h0 := hval k hklt.le s hki
    have h1 := hval (k + 1) (by omega) s hki'
    let f := (n : ℝ) * (s : ℝ) - k
    have hf0 : 0 ≤ f := by dsimp [f]; linarith
    have hf1 : f ≤ 1 := by dsimp [f]; linarith
    have he : B n / n * t.heightLin ((n : ℝ) * s) - g s =
        (1 - f) * (B n / n * (t.heightSeq k : ℝ) - g s) +
        f * (B n / n * (t.heightSeq (k + 1) : ℝ) - g s) := by
      simp only [PlaneTree.heightLin]
      change B n / n * ((1 - f) * _ + f * _) - g s = _
      ring
    rw [he]
    have hh := abs_add_le ((1 - f) * (B n / n * (t.heightSeq k : ℝ) - g s))
      (f * (B n / n * (t.heightSeq (k + 1) : ℝ) - g s))
    rw [abs_mul, abs_mul, abs_of_nonneg (by linarith : 0 ≤ 1 - f), abs_of_nonneg hf0] at hh
    have h0' := mul_le_mul_of_nonneg_left h0 (by linarith : 0 ≤ 1 - f)
    have h1' := mul_le_mul_of_nonneg_left h1 hf0
    linarith

/-- The uniform contour/height error is exactly the distance between the continuous paths. -/
theorem contourHeightError_eq_dist (B : ℕ → ℝ) (n : ℕ) (a : ℝ≥0) (τ : LocallyFinite.Tree) :
    contourHeightError B n a τ = dist (treeContourPath B n a τ) (treeHeightPath B n a τ) := by
  rw [ContinuousMap.dist_eq_iSup]
  simp only [contourHeightError, Real.dist_eq, treeContourPath,
    dite_eq_left (continuous_treeContourLin _), treeHeightPath,
    dite_eq_left (continuous_treeHeightLin _), ContinuousMap.coe_mk]

/-- **Global contour/height error** on `[0,1]` (first visits `H_i = C(2i - H_i)`,
`sup H ≤ sup C`, contour equicontinuity): it tends to `0` in probability. -/
theorem tendsto_contourHeightError {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ}
    (h : StableDomain μ θ B) {q : ℕ → ℕ} (hqtop : Tendsto q atTop atTop)
    (hq : ∀ k, Admissible μ (q k)) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun k => (exactTreeLaw μ (q k) : Measure BGW.LocallyFinite.Tree).real
      {τ | ε < contourHeightError B (q k) 1 τ}) atTop (𝓝 0) := by
  let P := fun k => (exactTreeLaw μ (q k)).map (treeContourPath B (q k) 1)
  let Q := (excLaw θ).map Prod.snd
  have hcompact : IsCompact (insert Q (range P)) :=
    (tendsto_exactContourLaw h hqtop hq).isCompact_insert_range
  have htight := isTightMeasureSet_of_isCompact_closure
    (S := insert Q (range P)) (by rw [hcompact.isClosed.closure_eq]; exact hcompact)
  rw [Metric.tendsto_nhds]
  intro η hη
  obtain ⟨K, hK, hp⟩ := isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mp htight
    (ENNReal.ofReal (η / 2)) (ENNReal.ofReal_pos.mpr (half_pos hη))
  have hgood := hqtop.eventually (eventually_globalError_le_of_compact h K hK hε)
  filter_upwards [hgood] with k hk
  rw [Real.dist_eq, sub_zero, abs_of_nonneg measureReal_nonneg]
  have hsize : ∀ᵐ τ ∂(exactTreeLaw μ (q k) : Measure LocallyFinite.Tree),
      τ ∈ LocallyFinite.sizeEvent (q k) := by
    rw [exactTreeLaw_toMeasure μ (q k) (hq k)]
    exact ae_cond_mem (LocallyFinite.measurableSet_sizeEvent _)
  have hsub : {τ | ε < contourHeightError B (q k) 1 τ} ≤ᵐ[
      (exactTreeLaw μ (q k) : Measure LocallyFinite.Tree)]
      {τ | treeContourPath B (q k) 1 τ ∉ K} := by
    filter_upwards [hsize] with τ hτ hbad
    intro hmem
    obtain ⟨t, rfl⟩ := (LocallyFinite.exists_toLocallyFinite_iff τ).mpr hτ.1
    exact (not_le_of_gt hbad) (hk t
      ((LocallyFinite.toLocallyFinite_mem_sizeEvent_iff t (q k)).mp hτ) hmem)
  have hpK := hp (P k).toMeasure
    ⟨P k, mem_insert_of_mem _ (mem_range_self k), rfl⟩
  change (P k).toMeasure Kᶜ ≤ _ at hpK
  rw [ProbabilityMeasure.toMeasure_map,
    Measure.map_apply (measurable_treeContourPath B (q k) 1) hK.measurableSet.compl] at hpK
  have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top ((measure_mono_ae hsub).trans hpK)
  rw [ENNReal.toReal_ofReal (half_pos hη).le] at hr
  exact hr.trans_lt (half_lt_self hη)

end BGW.StableTrees.ExactContour
