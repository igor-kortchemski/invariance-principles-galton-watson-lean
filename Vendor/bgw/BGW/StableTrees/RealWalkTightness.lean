/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.RealAttractionBounds
public import BGW.Probability.RealWalkMaximal
public import BGW.StableTrees.StableLaw
public import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.TightNormed

/-!
# Tightness and maximal estimates for real stable-attracted walks

Uniform tightness of the scaled sums yields safe-remainder estimates for Ottaviani's inequality.
Together with the normalizer ratio bounds, this gives small-block and finite-horizon maximum
control for arbitrary real iid increments.

Reference: P. Billingsley, *Convergence of Probability Measures*, 2nd ed., 1999, Theorem 9.7
(Ottaviani) and §16 (tightness for processes with independent increments).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal

namespace BGW.StableTrees

open BGW.Probability.RealWalk

private lemma measurableSet_abs_gt (r : ℝ) : MeasurableSet {x : ℝ | r < |x|} := by
  exact measurableSet_lt measurable_const (by fun_prop)

private lemma measurableSet_abs_le (r : ℝ) : MeasurableSet {x : ℝ | |x| ≤ r} := by
  exact measurableSet_le (by fun_prop) measurable_const

private theorem compact_closure_range_of_tendsto {α : Type*} [TopologicalSpace α]
    [T2Space α] {f : ℕ → α} {x : α} (hf : Tendsto f atTop (𝓝 x)) :
    IsCompact (closure (Set.range f)) := by
  have hc : IsCompact (insert x (Set.range f)) := hf.isCompact_insert_range
  apply hc.of_isClosed_subset isClosed_closure
  exact closure_minimal (Set.subset_insert x _) hc.isClosed

/-- The whole sequence of scaled sum laws is uniformly tight (a convergent sequence in the space
of probability measures on `ℝ` has compact closure; Mathlib's
`isTightMeasureSet_of_isCompact_closure`). This absorbs the finite beginning of the sequence. -/
theorem IsRealStableAttracted.isTightMeasureSet_scaledSumLaw {ν : ProbabilityMeasure ℝ}
    {θ : ℝ} {B : ℕ → ℝ} (h : IsRealStableAttracted ν θ B) :
    IsTightMeasureSet (Set.range fun n => (scaledSumLaw ν B n : Measure ℝ)) := by
  let f : ℕ → ProbabilityMeasure ℝ := fun n => scaledSumLaw ν B n
  have hf : Tendsto f atTop (𝓝 (stableLaw θ)) := h.converges
  have hc : IsCompact (closure (Set.range f)) := compact_closure_range_of_tendsto hf
  have ht := MeasureTheory.isTightMeasureSet_of_isCompact_closure hc
  change IsTightMeasureSet {μ : Measure ℝ | ∃ p : ProbabilityMeasure ℝ,
    p ∈ Set.range f ∧ (p : Measure ℝ) = μ} at ht
  have heq : {μ : Measure ℝ | ∃ p : ProbabilityMeasure ℝ,
      p ∈ Set.range f ∧ (p : Measure ℝ) = μ} = Set.range fun n => (f n : Measure ℝ) := by
    ext μ
    constructor
    · rintro ⟨p, ⟨n, rfl⟩, hμ⟩
      exact ⟨n, hμ⟩
    · rintro ⟨n, hμ⟩
      exact ⟨f n, ⟨n, rfl⟩, hμ⟩
  rw [heq] at ht
  simpa [f] using ht

private theorem exists_scaled_tail_bound {ν : ProbabilityMeasure ℝ} {θ : ℝ}
    {B : ℕ → ℝ} (h : IsRealStableAttracted ν θ B) {η : ℝ} (hη : 0 < η) :
    ∃ R > 0, ∀ j : ℕ,
      (scaledSumLaw ν B j : Measure ℝ).real {x | R < |x|} ≤ η := by
  have ht := MeasureTheory.tendsto_measure_norm_gt_of_isTightMeasureSet
    h.isTightMeasureSet_scaledSumLaw
  have hηe : 0 < ENNReal.ofReal η := ENNReal.ofReal_pos.mpr hη
  have hev := ht.eventually (Iio_mem_nhds hηe)
  obtain ⟨R₀, hR₀⟩ := Filter.eventually_atTop.1 hev
  let R := max R₀ 1
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  refine ⟨R, hRpos, fun j => ?_⟩
  have hsup : (⨆ μ ∈ Set.range fun n => (scaledSumLaw ν B n : Measure ℝ),
      μ {x | R < ‖x‖}) < ENNReal.ofReal η := hR₀ R (le_max_left _ _)
  have hmem : (scaledSumLaw ν B j : Measure ℝ) ∈
      Set.range fun n => (scaledSumLaw ν B n : Measure ℝ) := ⟨j, rfl⟩
  have hle : (scaledSumLaw ν B j : Measure ℝ) {x | R < ‖x‖} ≤
      ⨆ μ ∈ Set.range fun n => (scaledSumLaw ν B n : Measure ℝ), μ {x | R < ‖x‖} :=
    le_iSup_of_le _ (le_iSup_of_le hmem le_rfl)
  have hmass : (scaledSumLaw ν B j : Measure ℝ) {x | R < ‖x‖} ≤ ENNReal.ofReal η :=
    hle.trans hsup.le
  have hreal : (scaledSumLaw ν B j : Measure ℝ).real {x | R < ‖x‖} ≤ η := by
    rw [measureReal_def]
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hmass).trans_eq
      (ENNReal.toReal_ofReal hη.le)
  simpa only [Real.norm_eq_abs] using hreal

private theorem eventually_measureReal_abs_tail_le (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {η : ℝ} (hη : 0 < η) :
    ∀ᶠ r : ℝ in atTop, μ.real {x | r < |x|} ≤ η := by
  have ht := MeasureTheory.tendsto_measure_norm_gt_of_isTightMeasureSet
    (S := {μ}) (MeasureTheory.isTightMeasureSet_singleton : IsTightMeasureSet {μ})
  have hηe : 0 < ENNReal.ofReal η := ENNReal.ofReal_pos.mpr hη
  have hev := ht.eventually (Iio_mem_nhds hηe)
  filter_upwards [hev] with r hr
  have hmass : μ {x | r < ‖x‖} ≤ ENNReal.ofReal η := by
    simpa using hr.le
  have hreal : μ.real {x | r < ‖x‖} ≤ η := by
    rw [measureReal_def]
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hmass).trans_eq
      (ENNReal.toReal_ofReal hη.le)
  simpa only [Real.norm_eq_abs] using hreal

private theorem scaledSumLaw_abs_tail (ν : ProbabilityMeasure ℝ) (B : ℕ → ℝ) (j : ℕ)
    (R : ℝ) :
    (scaledSumLaw ν B j : Measure ℝ).real {x | R < |x|} =
      (sumLaw ν j : Measure ℝ).real {x | R < |x / B j|} := by
  change ((sumLaw ν j : Measure ℝ).map (fun x : ℝ => x / B j)).real {x | R < |x|} = _
  rw [MeasureTheory.map_measureReal_apply (μ := (sumLaw ν j : Measure ℝ))
    (f := fun x : ℝ => x / B j) (by fun_prop) (measurableSet_abs_gt R)]
  rfl

private theorem map_div_abs_tail (μ : Measure ℝ) (c R : ℝ) (hc : 0 < c) :
    (μ.map (fun x : ℝ => x / c)).real {x | R < |x|} =
      μ.real {x | R * c < |x|} := by
  rw [MeasureTheory.map_measureReal_apply (μ := μ) (f := fun x : ℝ => x / c)
    (by fun_prop) (measurableSet_abs_gt R)]
  congr 1
  ext x
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, abs_div, abs_of_pos hc]
  exact lt_div_iff₀ hc

private theorem safe_of_tail_bound (ν : ProbabilityMeasure ℝ) (j : ℕ) (r η : ℝ)
    (hη : η ≤ 1 / 2)
    (htail : (sumLaw ν j : Measure ℝ).real {x | r < |x|} ≤ η) :
    (1 / 2 : ℝ) ≤ (sumLaw ν j : Measure ℝ).real {x | |x| ≤ r} := by
  have hcompl : {x : ℝ | |x| ≤ r} = {x | r < |x|}ᶜ := by
    ext x
    simp
  rw [hcompl, measureReal_compl (measurableSet_abs_gt r), probReal_univ]
  linarith

/-- Uniform tightness of `S_j / B_n`, `j ≤ n` (audit item 7), quantitative form: the exceedance
probability of the level `K B n` is small, for all `j ≤ n` simultaneously, once `n` is large. -/
theorem IsRealStableAttracted.uniform_tight_partial_sums {ν : ProbabilityMeasure ℝ} {θ : ℝ}
    {B : ℕ → ℝ} (h : IsRealStableAttracted ν θ B) :
    ∀ η > 0, ∃ K > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ j ≤ n,
      (sumLaw ν j : Measure ℝ).real {x | K * B n < |x|} ≤ η := by
  intro η hη
  obtain ⟨R, hRpos, hscaled⟩ := exists_scaled_tail_bound h hη
  obtain ⟨C, hCpos, Nratio, hratio⟩ := h.bounded_index_ratio 1
  obtain ⟨Npos, hpos⟩ := Filter.eventually_atTop.1 h.pos
  let J := max Npos 1
  let K := C * R
  have hKpos : 0 < K := mul_pos hCpos hRpos
  have hfinite_eventually : ∀ᶠ r : ℝ in atTop, ∀ j ∈ Finset.range J,
      (sumLaw ν j : Measure ℝ).real {x | r < |x|} ≤ η := by
    rw [Filter.eventually_all_finset]
    intro j hj
    exact eventually_measureReal_abs_tail_le (sumLaw ν j : Measure ℝ) hη
  have hthreshold : Tendsto (fun n : ℕ => K * B n) atTop atTop :=
    Filter.Tendsto.const_mul_atTop hKpos h.tendsto_norming_atTop
  have hfiniteN := hthreshold.eventually hfinite_eventually
  have heventually := (Filter.eventually_ge_atTop Nratio).and h.pos |>.and hfiniteN
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 heventually
  refine ⟨K, hKpos, N, fun n hn j hj => ?_⟩
  obtain ⟨hnratio, hnpos⟩ := (hN n hn).1
  have hnfinite := (hN n hn).2
  by_cases hjsmall : j < J
  · exact hnfinite j (Finset.mem_range.mpr hjsmall)
  · have hjJ : J ≤ j := Nat.le_of_not_gt hjsmall
    have hjpos : 1 ≤ j := le_trans (le_max_right _ _) hjJ
    have hBj : 0 < B j := hpos j (le_trans (le_max_left _ _) hjJ)
    have hjbound : (j : ℝ) ≤ (1 : ℝ) * n + 2 := by
      calc
        (j : ℝ) ≤ n := Nat.cast_le.mpr hj
        _ ≤ (1 : ℝ) * n + 2 := by norm_num
    have hratio' := hratio n hnratio j hjpos hjbound
    have hratioPos : 0 < B j / B n := div_pos hBj hnpos
    rw [abs_of_pos hratioPos] at hratio'
    have hBj_le : B j ≤ C * B n := by
      calc
        B j = (B j / B n) * B n := by field_simp [hnpos.ne']
        _ ≤ C * B n := mul_le_mul_of_nonneg_right hratio' hnpos.le
    have hRscale : R * B j ≤ K * B n := by
      calc
        R * B j ≤ R * (C * B n) := mul_le_mul_of_nonneg_left hBj_le hRpos.le
        _ = K * B n := by dsimp [K]; ring
    have hsubset : {x : ℝ | K * B n < |x|} ⊆ {x | R < |x / B j|} := by
      intro x hx
      have hx' : R * B j < |x| := lt_of_le_of_lt hRscale hx
      have hxdiv := div_lt_div_of_pos_right hx' hBj
      simpa [abs_div, abs_of_pos hBj, hBj.ne'] using hxdiv
    calc
      (sumLaw ν j : Measure ℝ).real {x | K * B n < |x|} ≤
          (sumLaw ν j : Measure ℝ).real {x | R < |x / B j|} :=
        measureReal_mono hsubset (measure_ne_top _ _)
      _ = (scaledSumLaw ν B j : Measure ℝ).real {x | R < |x|} :=
        (scaledSumLaw_abs_tail ν B j R).symm
      _ ≤ η := hscaled j

/-- Small-block maxima (Node 6): maxima over blocks of length `≤ δ n + 2` exceed `ε B n` with
probability at most `η`, uniformly for large `n`. The threshold is `ε * B n` for `B n > 0`
(eventually). Proof: Ottaviani at half the threshold, with the safe-remainder hypothesis from
`small_index_ratio` and tightness of the full scaled sequence. -/
theorem IsRealStableAttracted.small_block_max {ν : ProbabilityMeasure ℝ} {θ : ℝ}
    {B : ℕ → ℝ}
    (h : IsRealStableAttracted ν θ B) :
    ∀ ε > 0, ∀ η > 0, ∃ δ > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ m : ℕ,
      (m : ℝ) ≤ δ * n + 2 → maxTail ν m (ε * B n) ≤ η := by
  intro ε hε η hη
  let η₀ := min (η / 2) (1 / 2)
  have hη₀pos : 0 < η₀ := lt_min (by positivity) (by norm_num)
  have hη₀half : η₀ ≤ 1 / 2 := min_le_right _ _
  have hη₀final : 2 * η₀ ≤ η := by
    dsimp [η₀]
    nlinarith [min_le_left (η / 2) (1 / 2)]
  obtain ⟨R, hRpos, hscaled⟩ := exists_scaled_tail_bound h hη₀pos
  let ρ := ε / (2 * R)
  have hρpos : 0 < ρ := by dsimp [ρ]; positivity
  obtain ⟨δ, hδpos, Nratio, hratio⟩ := h.small_index_ratio ρ hρpos
  obtain ⟨Npos, hpos⟩ := Filter.eventually_atTop.1 h.pos
  let J := max Npos 1
  have hfinite_eventually : ∀ᶠ r : ℝ in atTop, ∀ j ∈ Finset.range J,
      (sumLaw ν j : Measure ℝ).real {x | r < |x|} ≤ η₀ := by
    rw [Filter.eventually_all_finset]
    intro j hj
    exact eventually_measureReal_abs_tail_le (sumLaw ν j : Measure ℝ) hη₀pos
  have hradius : Tendsto (fun n : ℕ => (ε / 2) * B n) atTop atTop :=
    Filter.Tendsto.const_mul_atTop (by positivity) h.tendsto_norming_atTop
  have hfiniteN := hradius.eventually hfinite_eventually
  have heventually := ((Filter.eventually_ge_atTop Nratio).and h.pos).and hfiniteN
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 heventually
  refine ⟨δ, hδpos, N, fun n hn m hm => ?_⟩
  obtain ⟨hnratio, hnpos⟩ := (hN n hn).1
  have hnfinite := (hN n hn).2
  let r := (ε / 2) * B n
  have hrpos : 0 < r := mul_pos (by positivity) hnpos
  have htail (j : ℕ) (hj : j ≤ m) :
      (sumLaw ν j : Measure ℝ).real {x | r < |x|} ≤ η₀ := by
    by_cases hjsmall : j < J
    · exact hnfinite j (Finset.mem_range.mpr hjsmall)
    · have hjJ : J ≤ j := Nat.le_of_not_gt hjsmall
      have hjpos : 1 ≤ j := le_trans (le_max_right _ _) hjJ
      have hBj : 0 < B j := hpos j (le_trans (le_max_left _ _) hjJ)
      have hjbound : (j : ℝ) ≤ δ * n + 2 :=
        (Nat.cast_le.mpr hj).trans hm
      have hratio' := hratio n hnratio j hjpos hjbound
      have hratioPos : 0 < B j / B n := div_pos hBj hnpos
      rw [abs_of_pos hratioPos] at hratio'
      have hBj_le : B j ≤ ρ * B n := by
        calc
          B j = (B j / B n) * B n := by field_simp [hnpos.ne']
          _ ≤ ρ * B n := mul_le_mul_of_nonneg_right hratio' hnpos.le
      have hscale : R * B j ≤ (ε / 2) * B n := by
        calc
          R * B j ≤ R * (ρ * B n) := mul_le_mul_of_nonneg_left hBj_le hRpos.le
          _ = (ε / 2) * B n := by
            dsimp [ρ]
            have hRne : R ≠ 0 := hRpos.ne'
            field_simp [hRne]
      have hsubset : {x : ℝ | r < |x|} ⊆ {x | R < |x / B j|} := by
        intro x hx
        have hx' : R * B j < |x| := lt_of_le_of_lt hscale hx
        have hxdiv := div_lt_div_of_pos_right hx' hBj
        simpa [r, abs_div, abs_of_pos hBj, hBj.ne'] using hxdiv
      calc
        (sumLaw ν j : Measure ℝ).real {x | r < |x|} ≤
            (sumLaw ν j : Measure ℝ).real {x | R < |x / B j|} :=
          measureReal_mono hsubset (measure_ne_top _ _)
        _ = (scaledSumLaw ν B j : Measure ℝ).real {x | R < |x|} :=
          (scaledSumLaw_abs_tail ν B j R).symm
        _ ≤ η₀ := hscaled j
  have hsafe (j : ℕ) (hj : j ≤ m) := safe_of_tail_bound ν j r η₀ hη₀half (htail j hj)
  have hmax := maximal_le_two_mul_tail ν m r hsafe
  have htwo : 2 * r = ε * B n := by dsimp [r]; ring
  rw [htwo] at hmax
  have hend := htail m le_rfl
  calc
    maxTail ν m (ε * B n) ≤ 2 * (sumLaw ν m : Measure ℝ).real {x | r < |x|} := hmax
    _ ≤ 2 * η₀ := mul_le_mul_of_nonneg_left hend (by norm_num)
    _ ≤ η := hη₀final

/-- Compact containment on a finite horizon (Node 6): maxima up to `⌊n T⌋₊` stay below
`K * B n` with probability at least `1 - η`, for all large `n`. -/
theorem IsRealStableAttracted.horizon_max_tight {ν : ProbabilityMeasure ℝ} {θ : ℝ}
    {B : ℕ → ℝ} (h : IsRealStableAttracted ν θ B) {T : ℝ} (hT : 0 < T) :
    ∀ η > 0, ∃ K > 0, ∃ N : ℕ, ∀ n ≥ N,
      maxTail ν ⌊(n : ℝ) * T⌋₊ (K * B n) ≤ η := by
  intro η hη
  let η₀ := min (η / 2) (1 / 2)
  have hη₀pos : 0 < η₀ := lt_min (by positivity) (by norm_num)
  have hη₀half : η₀ ≤ 1 / 2 := min_le_right _ _
  have hη₀final : 2 * η₀ ≤ η := by
    dsimp [η₀]
    nlinarith [min_le_left (η / 2) (1 / 2)]
  obtain ⟨K₀, hK₀pos, Ntight, htail⟩ := h.uniform_tight_partial_sums η₀ hη₀pos
  obtain ⟨C, hCpos, Nratio, hratio⟩ := h.bounded_index_ratio T
  let M : ℕ → ℕ := fun n => ⌊(n : ℝ) * T⌋₊
  have hMtop : Tendsto M atTop atTop := by
    simpa [M, mul_comm] using tendsto_nat_floor_mul_atTop T hT
  have heventually := (Filter.eventually_ge_atTop Nratio).and
    ((hMtop.eventually (Filter.eventually_ge_atTop 1)).and
      (h.pos.and ((hMtop.eventually h.pos).and
        (hMtop.eventually (Filter.eventually_ge_atTop Ntight)))))
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 heventually
  let K := 2 * K₀ * C
  have hKpos : 0 < K := by dsimp [K]; positivity
  refine ⟨K, hKpos, N, fun n hn => ?_⟩
  obtain ⟨hnratio, ⟨hMone, ⟨hnpos, ⟨hBMpos, hMlarge⟩⟩⟩⟩ := hN n hn
  have hBM := htail (M n) hMlarge (M n) le_rfl
  let r := K₀ * B (M n)
  have htailAll (j : ℕ) (hj : j ≤ M n) :
      (sumLaw ν j : Measure ℝ).real {x | r < |x|} ≤ η₀ := by
    simpa [r] using htail (M n) hMlarge j hj
  have hsafe (j : ℕ) (hj : j ≤ M n) :=
    safe_of_tail_bound ν j r η₀ hη₀half (htailAll j hj)
  have hmax := maximal_le_two_mul_tail ν (M n) r hsafe
  have hend := htailAll (M n) le_rfl
  have hfloor : (M n : ℝ) ≤ (n : ℝ) * T := by
    dsimp [M]
    exact Nat.floor_le (by positivity)
  have hMbound : (M n : ℝ) ≤ T * n + 2 := by
    nlinarith [hfloor]
  have hratio' := hratio n hnratio (M n) hMone hMbound
  have hratioPos : 0 < B (M n) / B n := div_pos hBMpos hnpos
  rw [abs_of_pos hratioPos] at hratio'
  have hBMle : B (M n) ≤ C * B n := by
    calc
      B (M n) = (B (M n) / B n) * B n := by field_simp [hnpos.ne']
      _ ≤ C * B n := mul_le_mul_of_nonneg_right hratio' hnpos.le
  have hthreshold : 2 * r ≤ K * B n := by
    calc
      2 * r = 2 * K₀ * B (M n) := by dsimp [r]; ring
      _ ≤ 2 * K₀ * (C * B n) := mul_le_mul_of_nonneg_left hBMle (by positivity)
      _ = K * B n := by dsimp [K]; ring
  have hmax' : maxTail ν (M n) (2 * r) ≤ 2 * η₀ := by
    calc
      maxTail ν (M n) (2 * r) ≤
          2 * (sumLaw ν (M n) : Measure ℝ).real {x | r < |x|} := hmax
      _ ≤ 2 * η₀ := mul_le_mul_of_nonneg_left hend (by norm_num)
  calc
    maxTail ν (M n) (K * B n) ≤ maxTail ν (M n) (2 * r) :=
      maxTail_anti_threshold ν (M n) hthreshold
    _ ≤ 2 * η₀ := hmax'
    _ ≤ η := hη₀final

/-- The family `{law of S_j / B_n : j ≤ n}` over all `n` is tight (as a set of measures). The
finitely many `n` with small `N` contribute finitely many tight laws; `B n ≤ 0` is harmless
because the division by `B n` is then still a measurable map and each law is a single tight law. -/
theorem IsRealStableAttracted.isTightMeasureSet_scaled_partial_sums {ν : ProbabilityMeasure ℝ}
    {θ : ℝ} {B : ℕ → ℝ} (h : IsRealStableAttracted ν θ B) :
    IsTightMeasureSet {μ : Measure ℝ | ∃ n j : ℕ, j ≤ n ∧
      μ = (sumLaw ν j : Measure ℝ).map (fun x => x / B n)} := by
  let S : Set (Measure ℝ) := {μ | ∃ n j : ℕ, j ≤ n ∧
    μ = (sumLaw ν j : Measure ℝ).map (fun x => x / B n)}
  have htailBound (η : ℝ) (hη : 0 < η) :
      ∃ R : ℝ, ∀ r ≥ R, ∀ μ ∈ S, μ {x | r < ‖x‖} ≤ ENNReal.ofReal η := by
    obtain ⟨K, hKpos, Npartial, hpartial⟩ := h.uniform_tight_partial_sums η hη
    obtain ⟨Npos, hpos⟩ := Filter.eventually_atTop.1 h.pos
    have hfinite_eventually : ∀ᶠ r : ℝ in atTop, ∀ n ∈ Finset.range (max Npartial Npos),
        ∀ j ∈ Finset.range (n + 1),
          ((sumLaw ν j : Measure ℝ).map (fun x => x / B n)).real
            {x | r < |x|} ≤ η := by
      rw [Filter.eventually_all_finset]
      intro n hn
      rw [Filter.eventually_all_finset]
      intro j hj
      exact eventually_measureReal_abs_tail_le
        ((sumLaw ν j : Measure ℝ).map (fun x => x / B n)) hη
    obtain ⟨Rsmall, hsmall⟩ := Filter.eventually_atTop.1 hfinite_eventually
    let N := max Npartial Npos
    let R := max K Rsmall
    refine ⟨R, fun r hr μ hμ => ?_⟩
    rcases hμ with ⟨n, j, hj, rfl⟩
    by_cases hn : n < N
    · have hreal := hsmall r (le_trans (le_max_right _ _) hr) n
        (Finset.mem_range.mpr hn) j (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))
      have hreal' : ((sumLaw ν j : Measure ℝ).map (fun x => x / B n)).real
          {x | r < ‖x‖} ≤ η := by simpa only [Real.norm_eq_abs] using hreal
      have hmass : ((sumLaw ν j : Measure ℝ).map (fun x => x / B n))
          {x | r < ‖x‖} ≤ ENNReal.ofReal η := by
        rw [← ofReal_measureReal (μ :=
          ((sumLaw ν j : Measure ℝ).map (fun x => x / B n))) (s := {x | r < ‖x‖})]
        exact ENNReal.ofReal_le_ofReal hreal'
      exact hmass
    · have hnN : N ≤ n := Nat.le_of_not_gt hn
      have hnpartial : Npartial ≤ n := le_trans (le_max_left _ _) hnN
      have hnposIndex : Npos ≤ n := le_trans (le_max_right _ _) hnN
      have hBn : 0 < B n := hpos n hnposIndex
      have hRlarge : K ≤ r := le_trans (le_max_left _ _) hr
      have htail := hpartial n hnpartial j hj
      have hsubset : {x : ℝ | r * B n < |x|} ⊆ {x | K * B n < |x|} := by
        intro x hx
        exact (mul_le_mul_of_nonneg_right hRlarge hBn.le).trans_lt hx
      have htail' : (sumLaw ν j : Measure ℝ).real {x | r * B n < |x|} ≤ η :=
        (measureReal_mono hsubset (measure_ne_top _ _)).trans htail
      have hmap := map_div_abs_tail (sumLaw ν j : Measure ℝ) (B n) r hBn
      have hreal : ((sumLaw ν j : Measure ℝ).map (fun x => x / B n)).real
          {x | r < |x|} ≤ η := hmap ▸ htail'
      have hreal' : ((sumLaw ν j : Measure ℝ).map (fun x => x / B n)).real
          {x | r < ‖x‖} ≤ η := by simpa only [Real.norm_eq_abs] using hreal
      have hmass : ((sumLaw ν j : Measure ℝ).map (fun x => x / B n))
          {x | r < ‖x‖} ≤ ENNReal.ofReal η := by
        rw [← ofReal_measureReal (μ :=
          ((sumLaw ν j : Measure ℝ).map (fun x => x / B n))) (s := {x | r < ‖x‖})]
        exact ENNReal.ofReal_le_ofReal hreal'
      exact hmass
  have htendsto :
      Tendsto (fun r : ℝ => ⨆ μ ∈ S, μ {x | r < ‖x‖}) atTop (𝓝 0) := by
    rw [ENNReal.tendsto_atTop_zero]
    intro ε hε
    by_cases hεtop : ε = ∞
    · refine ⟨1, fun r hr => ?_⟩
      simp [hεtop]
    · have hη : 0 < ε.toReal := ENNReal.toReal_pos (ne_of_gt hε) hεtop
      obtain ⟨R, hR⟩ := htailBound ε.toReal hη
      refine ⟨R, fun r hr => ?_⟩
      calc
        ⨆ μ ∈ S, μ {x | r < ‖x‖} ≤ ENNReal.ofReal ε.toReal := by
          apply iSup_le
          intro μ
          apply iSup_le
          intro hμ
          exact hR r hr μ hμ
        _ = ε := ENNReal.ofReal_toReal hεtop
  have htight := MeasureTheory.isTightMeasureSet_of_tendsto_measure_norm_gt
    (S := S) htendsto
  change IsTightMeasureSet S
  exact htight
