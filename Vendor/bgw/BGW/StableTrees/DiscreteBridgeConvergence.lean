/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.DiscreteBridgeRN
public import BGW.StableTrees.DiscreteBridgeLocalLimit
public import BGW.StableTrees.BridgeProjective
import BGW.StableTrees.StableProcessLaw
import BGW.Probability.SkorokhodRepresentation
import BGW.Skorokhod.PolishTightness
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import BGW.Probability.Rounding

/-!
# Convergence of strict prefixes of the discrete bridge

Skorokhod representation of the unconditioned FCLT and the signed lattice local
limit theorem give convergence of bounded weighted expectations. Conditioning is
handled by the prefix Radon–Nikodym identity.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal Classical

namespace BGW.StableTrees.DiscreteBridge

open BGW BGW.Skorokhod BGW.Probability.RealWalk BGW.StableTrees.DiscreteForest
open BGW.Probability

private theorem measurable_rounded_end (B : ℕ → ℝ) (n : ℕ) (a : ℝ≥0) :
    Measurable (fun x : D (a : ℝ) ℝ => round (endValue a x * B n)) := by
  exact measurable_round.comp ((measurable_eval _).mul_const _)

private theorem ae_prefix_lattice {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ}
    (h : StableDomain μ θ B) {n : ℕ} (hn : 1 ≤ n) (a : ℝ≥0) :
    ∀ᵐ x ∂(stepPathLaw (realOffspringStepLaw μ) (a : ℝ) B n : Measure (D (a : ℝ) ℝ)),
      (Scalar.latticeSpan μ : ℤ) ∣ round (endValue a x * B n) + ⌊(a : ℝ) * n⌋₊ := by
  let m := ⌊(a : ℝ) * n⌋₊
  have hlaw : ∀ᵐ z ∂walkLaw μ m, (Scalar.latticeSpan μ : ℤ) ∣ z + m := by
    apply ae_iff_of_countable.mpr
    intro z hz
    by_contra hnot
    apply hz
    apply (measureReal_eq_zero_iff).mp
    exact Scalar.walkProb_eq_zero_of_not_dvd h hnot
  have hseq : ∀ᵐ ω ∂(offspringSeqLaw μ).toMeasure,
      (Scalar.latticeSpan μ : ℤ) ∣ walk ω m + m := by
    have hh : ∀ᵐ z ∂((offspringSeqLaw μ).toMeasure.map (fun ω => walk ω m)),
        (Scalar.latticeSpan μ : ℤ) ∣ z + m := by
      rw [map_offspringSeqLaw_walk]
      exact hlaw
    exact ae_of_ae_map (measurable_walk m).aemeasurable hh
  rw [← map_forestWalkPath]
  have hm : MeasurableSet {x : D (a : ℝ) ℝ | (Scalar.latticeSpan μ : ℤ) ∣
      round (endValue a x * B n) + m} :=
    (measurable_rounded_end B n a)
      (Set.to_countable {z : ℤ | (Scalar.latticeSpan μ : ℤ) ∣ z + m}).measurableSet
  apply (ae_map_iff ((measurable_forestPairPath B n a).fst).aemeasurable hm).mpr
  filter_upwards [hseq] with ω hω
  change (Scalar.latticeSpan μ : ℤ) ∣ round (endValue a (forestWalkPath B n a ω) * B n) + m
  rw [endValue_forestWalkPath, div_mul_cancel₀ _ (h.pos n hn).ne', round_intCast]
  exact hω

private theorem density_tendsto_on_lattice {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ}
    (h : StableDomain μ θ B) {q : ℕ → ℕ} (hqtop : Tendsto q atTop atTop)
    (hq : ∀ k, Admissible μ (q k)) (a : ℝ≥0) (ha : a ∈ Ioo (0 : ℝ≥0) 1)
    {x : ℕ → D (a : ℝ) ℝ} {y : D (a : ℝ) ℝ} (hx : Tendsto x atTop (𝓝 y))
    (hlat : ∀ᶠ k in atTop, (Scalar.latticeSpan μ : ℤ) ∣
      round (endValue a (x k) * B (q k)) + ⌊(a : ℝ) * q k⌋₊) :
    Tendsto (fun k => bridgePathDensity μ B (q k) a (x k)) atTop
      (𝓝 (bridgePrefixWeight θ (a : ℝ) a.coe_nonneg y)) := by
  have he := ((lipschitzWith_one_eval_right (E := ℝ) a.coe_nonneg).continuous.tendsto y).comp hx
  have hBtop := (Scalar.tendsto_atTop h).comp hqtop
  have hr := round_normalized_tendsto he hBtop
  have hz : Tendsto (fun k => (((-1 - round (endValue a (x k) * B (q k))) : ℤ) : ℝ) /
      B (q k)) atTop (𝓝 (-endValue a y)) := by
    have ht := (hBtop.const_div_atTop (-1 : ℝ)).sub hr
    simpa only [Function.comp_def, endValue, Int.cast_sub, Int.cast_neg, Int.cast_one,
      sub_div, zero_sub] using ht
  have hdiv : ∀ᶠ k in atTop, (Scalar.latticeSpan μ : ℤ) ∣
      (-1 - round (endValue a (x k) * B (q k))) +
        (q k - ⌊(a : ℝ) * q k⌋₊ : ℕ) := by
    filter_upwards [hlat] with k hk
    have hdivn : (Scalar.latticeSpan μ : ℤ) ∣ (-1 : ℤ) + q k := by
      by_contra hn
      have hzero := Scalar.walkProb_eq_zero_of_not_dvd h hn
      have hpos := walkProb_neg_one_pos (hq k)
      rw [hzero] at hpos
      exact (lt_irrefl 0) hpos
    have hfloor : ⌊(a : ℝ) * q k⌋₊ ≤ q k := by
      apply Nat.floor_le_of_le
      have haR : (a : ℝ) ≤ 1 := by exact_mod_cast ha.2.le
      exact mul_le_of_le_one_left (Nat.cast_nonneg _) haR
    have hh := dvd_sub hdivn hk
    simpa only [Nat.cast_sub hfloor] using (show (Scalar.latticeSpan μ : ℤ) ∣
      (-1 - round (endValue a (x k) * B (q k))) + ((q k : ℤ) - ⌊(a : ℝ) * q k⌋₊) by
        convert hh using 1; ring)
  exact bridgeRatio_tendsto h hqtop hq a ha hz hdiv

/-- **Prefix convergence of the walk bridge**: for every `a ∈ (0,1)` the law of the walk bridge
on `[0,a]` converges to the corresponding prefix of the stable bridge. -/
theorem tendsto_restrictLaw_walkBridgeLaw {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ}
    (h : StableDomain μ θ B) {q : ℕ → ℕ} (hqtop : Tendsto q atTop atTop)
    (hq : ∀ k, Admissible μ (q k)) (a : ℝ≥0) (ha : a ∈ Ioo (0 : ℝ≥0) 1) :
    Tendsto (fun k => restrictLaw a ha.2.le (walkBridgeLaw μ B (q k) (hq k))) atTop
      (𝓝 (restrictLaw a ha.2.le (stableBridgeLaw θ))) := by
  have ha0 : 0 < (a : ℝ) := by exact_mod_cast ha.1
  have ha1 : (a : ℝ) < 1 := by exact_mod_cast ha.2
  have hq1 (k : ℕ) : 1 ≤ q k := by
    by_contra hk
    have : q k = 0 := by omega
    have hh := hq k
    rw [this] at hh
    exact hh (by simp [LocallyFinite.sizeEvent_zero])
  let P := fun k => stepPathLaw (realOffspringStepLaw μ) (a : ℝ) B (q k)
  let Q := stableProcessLaw θ (a : ℝ)
  have hconv : Tendsto P atTop (𝓝 Q) := (h.tendsto_stepPathLaw ha0).comp hqtop
  obtain ⟨X, Y, hXm, hYm, hXlaw, hYlaw, hXY⟩ :=
    BGW.Probability.exists_tendsto_ae_of_tendsto hconv
  have hlat : ∀ᵐ ω ∂(volume : Measure unitInterval), ∀ k,
      (Scalar.latticeSpan μ : ℤ) ∣ round (endValue a (X k ω) * B (q k)) +
        ⌊(a : ℝ) * q k⌋₊ := by
    apply ae_all_iff.mpr
    intro k
    have hh := ae_prefix_lattice h (hq1 k) a
    change ∀ᵐ x ∂(P k : Measure (D (a : ℝ) ℝ)), _ at hh
    rw [← hXlaw k] at hh
    exact ae_of_ae_map (hXm k).aemeasurable hh
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
  intro φ
  let F := fun k ω => bridgePathDensity μ B (q k) a (X k ω) * φ (X k ω)
  let F₀ := fun ω => bridgePrefixWeight θ (a : ℝ) a.coe_nonneg (Y ω) * φ (Y ω)
  have hFm (k : ℕ) : Measurable (F k) :=
    ((measurable_bridgePathDensity μ B (q k) a).comp (hXm k)).mul
      (φ.continuous.measurable.comp (hXm k))
  have hlim : ∀ᵐ ω ∂(volume : Measure unitInterval),
      Tendsto (fun k => F k ω) atTop (𝓝 (F₀ ω)) := by
    filter_upwards [hXY, hlat] with ω hω hlω
    exact (density_tendsto_on_lattice h hqtop hq a ha hω
      (Eventually.of_forall hlω)).mul (φ.continuous.tendsto _ |>.comp hω)
  obtain ⟨C, hC⟩ := bridgePathDensity_le h a ha
  have hbound : ∃ K : ℝ, ∀ᶠ k in atTop,
      ∀ᵐ ω ∂(volume : Measure unitInterval), ‖F k ω‖ ≤ K := by
    refine ⟨max C 0 * ‖φ‖, ?_⟩
    filter_upwards [hqtop.eventually hC] with k hk
    apply ae_of_all
    intro ω
    have hd := hk (hq k) (X k ω)
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg hd.1]
    exact mul_le_mul (hd.2.trans (le_max_left _ _)) (φ.norm_coe_le_norm _)
      (norm_nonneg _) (le_max_right _ _)
  have hint := tendsto_integral_filter_of_norm_le_const
    (Eventually.of_forall fun k => (hFm k).aestronglyMeasurable) hbound hlim
  have hnn (n : ℕ) (x : D (a : ℝ) ℝ) : 0 ≤ bridgePathDensity μ B n a x :=
    div_nonneg (Scalar.walkProb_nonneg _ _ _) (Scalar.walkProb_nonneg _ _ _)
  have hsrc (k : ℕ) : (∫ x, φ x ∂(restrictLaw a ha.2.le (walkBridgeLaw μ B (q k) (hq k)))) =
      ∫ ω, F k ω ∂(volume : Measure unitInterval) := by
    rw [restrictLaw_walkBridgeLaw_eq_withDensity (hq k) (h.pos (q k) (hq1 k)).ne' a ha,
      integral_withDensity_eq_integral_toReal_smul
        (f := fun x => ENNReal.ofReal (bridgePathDensity μ B (q k) a x))
        (ENNReal.measurable_ofReal.comp (measurable_bridgePathDensity μ B (q k) a))
        (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
    simp only [ENNReal.toReal_ofReal (hnn _ _), smul_eq_mul]
    change (∫ x, bridgePathDensity μ B (q k) a x * φ x ∂(P k : Measure _)) = _
    rw [← hXlaw k, integral_map (hXm k).aemeasurable]
    exact ((measurable_bridgePathDensity μ B (q k) a).mul
        φ.continuous.measurable).aestronglyMeasurable
  have htgt : (∫ x, φ x ∂(restrictLaw a ha.2.le (stableBridgeLaw θ))) =
      ∫ ω, F₀ ω ∂(volume : Measure unitInterval) := by
    change (∫ x, φ x ∂((stableBridgeLaw θ : Measure (D 1 ℝ)).map
      (BGW.Skorokhod.restrict (show (a : ℝ) ≤ 1 by exact_mod_cast ha.2.le)))) = _
    rw [map_restrict_stableBridgeLaw h.alpha_mem ha0 ha1, bridgePrefixLaw,
      integral_withDensity_eq_integral_toReal_smul
        (f := fun x => ENNReal.ofReal (bridgePrefixWeight θ (a : ℝ) a.coe_nonneg x))
        (ENNReal.measurable_ofReal.comp (measurable_bridgePrefixWeight h.alpha_mem a.coe_nonneg))
        (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
    simp only [ENNReal.toReal_ofReal
      (bridgePrefixWeight_nonneg h.alpha_mem a.coe_nonneg ha1 _), smul_eq_mul]
    change (∫ x, bridgePrefixWeight θ (a : ℝ) a.coe_nonneg x * φ x ∂(Q : Measure _)) = _
    rw [← hYlaw, integral_map hYm.aemeasurable]
    exact ((measurable_bridgePrefixWeight h.alpha_mem a.coe_nonneg).mul
        φ.continuous.measurable).aestronglyMeasurable
  simpa only [hsrc, htgt] using hint


end BGW.StableTrees.DiscreteBridge
