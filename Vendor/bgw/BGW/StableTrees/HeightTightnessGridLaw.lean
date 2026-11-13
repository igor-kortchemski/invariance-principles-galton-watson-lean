/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.DiscreteHeightApprox
public import BGW.StableTrees.HeightContinuity
public import BGW.StableTrees.HeightTightnessBasic
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.Topology.UniformSpace.HeineCantor

/-!
# Probabilistic control of height increments on deterministic grids

K09 and portmanteau control every finite grid of discrete heights. Agreement with
the continuous H03 height, uniform continuity on a compact horizon, and dominated
convergence make the limiting grid-increment probabilities tend to zero.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal Classical
open BGW.StableTrees.DiscreteForest BGW.Skorokhod BGW.StableTrees.DiscreteHeightApprox
namespace BGW.StableTrees.HeightTightness

/-- Equally spaced observation times, including both endpoints of the horizon. -/
noncomputable def heightGridTime (R : ℝ≥0) (N : ℕ) (i : Fin (N + 1)) : ℝ≥0 :=
  ⟨(R : ℝ) * (i : ℝ) / N, by positivity⟩

/-- Every uniform grid observation lies in its horizon, including the totalized zero mesh. -/
theorem heightGridTime_le (R : ℝ≥0) (N : ℕ) (i : Fin (N + 1)) :
    heightGridTime R N i ≤ R := by
  change (R : ℝ) * (i : ℝ) / N ≤ R
  by_cases hN : N = 0
  · simp [hN]
  · have hn : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
    apply (div_le_iff₀ hn).mpr
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast (show i.val ≤ N by omega)) R.coe_nonneg

private theorem isClosed_gridBad (N : ℕ) (η : ℝ) :
    IsClosed {v : Fin (N + 1) → ℝ | ∃ i : Fin N, η ≤ |v i.castSucc - v i.succ|} := by
  simp only [ofPred_exists]
  apply isClosed_iUnion_of_finite
  intro i
  exact isClosed_le continuous_const (by fun_prop)

/-- K09 and portmanteau control every finite grid of height increments. -/
theorem height_grid_limsup_probability_le {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ}
    (h : StableDomain μ θ B) {R : ℝ≥0} (hR : 0 < R) (N : ℕ) (η : ℝ) :
    limsup (fun n : ℕ => (offspringSeqLaw μ).toMeasure.real
      {ω | ∃ i : Fin N, η ≤
        |scaledHeight B n ω (heightGridTime R N i.castSucc) -
          scaledHeight B n ω (heightGridTime R N i.succ)|}) atTop ≤
      (stableLocalLaw θ).toMeasure.real
        {f | ∃ i : Fin N, η ≤ |height θ f (heightGridTime R N i.castSucc) -
          height θ f (heightGridTime R N i.succ)|} := by
  let F : Set (D (R : ℝ) ℝ × (Fin (N + 1) → ℝ)) :=
    {p | ∃ i : Fin N, η ≤ |p.2 i.castSucc - p.2 i.succ|}
  have hF : IsClosed F := (isClosed_gridBad N η).preimage continuous_snd
  have hconv := tendsto_walk_height_fdd h hR (heightGridTime R N) (heightGridTime_le R N)
  have hport := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hconv hF
  have hn (n : ℕ) : (((offspringSeqLaw μ).map (heightJoint B n R (heightGridTime R N)) :
      ProbabilityMeasure (D (R : ℝ) ℝ × (Fin (N + 1) → ℝ))) : Measure _) F =
        (offspringSeqLaw μ).toMeasure
          {ω | ∃ i : Fin N, η ≤ |scaledHeight B n ω (heightGridTime R N i.castSucc) -
            scaledHeight B n ω (heightGridTime R N i.succ)|} := by
    rw [ProbabilityMeasure.toMeasure_map,
      Measure.map_apply (measurable_heightJoint B n R (heightGridTime R N)) hF.measurableSet]
    rfl
  have hz : (((stableLocalLaw θ).map (heightLimitJoint θ R (heightGridTime R N)) :
      ProbabilityMeasure (D (R : ℝ) ℝ × (Fin (N + 1) → ℝ))) : Measure _) F =
        (stableLocalLaw θ).toMeasure
          {f | ∃ i : Fin N, η ≤ |height θ f (heightGridTime R N i.castSucc) -
            height θ f (heightGridTime R N i.succ)|} := by
    rw [ProbabilityMeasure.toMeasure_map,
      Measure.map_apply (measurable_heightLimitJoint θ R (heightGridTime R N)) hF.measurableSet]
    rfl
  simp_rw [hn, hz] at hport
  have hr := ENNReal.toReal_mono (measure_ne_top _ _) hport
  have hrw := ENNReal.toReal_limsup
    (u := fun n : ℕ => (offspringSeqLaw μ).toMeasure
      {ω | ∃ i : Fin N, η ≤ |scaledHeight B n ω (heightGridTime R N i.castSucc) -
        scaledHeight B n ω (heightGridTime R N i.succ)|})
    (f := atTop) (Eventually.of_forall fun _ => measure_ne_top _ _) (by
      refine ⟨1, ?_⟩
      change ∀ᶠ n : ℕ in atTop, _ ≤ (1 : ℝ)
      exact Eventually.of_forall fun _ => measureReal_le_one)
  rw [hrw] at hr
  exact hr

/-- Adjacent grid times are separated by exactly one mesh width. -/
theorem dist_heightGridTime_adjacent (R : ℝ≥0) (N : ℕ) (i : Fin N) :
    dist (heightGridTime R N i.castSucc) (heightGridTime R N i.succ) = (R : ℝ) / N := by
  rw [NNReal.dist_eq]
  change |(R : ℝ) * (i.val : ℝ) / N - (R : ℝ) * ((i.val + 1 : ℕ) : ℝ) / N| = _
  rw [Nat.cast_add_one,
    show (R : ℝ) * (i.val : ℝ) / N - (R : ℝ) * ((i.val : ℝ) + 1) / N =
      -((R : ℝ) / N) by ring, abs_neg, abs_of_nonneg (by positivity)]

private theorem measurableSet_height_grid_bad (θ : ℝ) (R : ℝ≥0) (N : ℕ) (η : ℝ) :
    MeasurableSet {f : DLoc | ∃ i : Fin N, η ≤
      |height θ f (heightGridTime R N i.castSucc) - height θ f (heightGridTime R N i.succ)|} := by
  have hm : Measurable (fun f : DLoc => fun i : Fin (N + 1) =>
      height θ f (heightGridTime R N i)) := by
    simpa only [heightLimitJoint, Function.comp_def] using
      (measurable_heightLimitJoint θ R (heightGridTime R N)).snd
  exact (isClosed_gridBad N η).measurableSet.preimage hm

/-- Continuity of the H03 height sends the limiting grid-increment probability to zero. -/
theorem tendsto_height_grid_bad_probability_zero {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    (R : ℝ≥0) {η : ℝ} (hη : 0 < η) :
    Tendsto (fun N : ℕ => (stableLocalLaw θ).toMeasure.real
      {f | ∃ i : Fin N, η ≤ |height θ f (heightGridTime R N i.castSucc) -
        height θ f (heightGridTime R N i.succ)|}) atTop (𝓝 0) := by
  let P := (stableLocalLaw θ).toMeasure
  let E (N : ℕ) : Set DLoc := {f | ∃ i : Fin N, η ≤
    |height θ f (heightGridTime R N i.castSucc) - height θ f (heightGridTime R N i.succ)|}
  have hm (N : ℕ) : MeasurableSet (E N) := measurableSet_height_grid_bad θ R N η
  have ha : ∀ᵐ f ∂P, ∀ N : ℕ, ∀ i : Fin (N + 1),
      height θ f (heightGridTime R N i) = heightLoc θ f (heightGridTime R N i) :=
    ae_all_iff.mpr fun N => ae_all_iff.mpr fun i =>
      (ae_heightLoc_eq_height hθ (heightGridTime R N i)).mono fun _ hh => hh.symm
  have hscale : Tendsto (fun N : ℕ => (R : ℝ) / N) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hev : ∀ᵐ f ∂P, ∀ᶠ N : ℕ in atTop, f ∉ E N := by
    filter_upwards [ha] with f hf
    let g : C(Set.Icc (0 : ℝ≥0) R, ℝ) :=
      ⟨fun u => heightLoc θ f u.1, (continuous_heightLoc θ f).comp continuous_subtype_val⟩
    obtain ⟨δ, hδ, hclose⟩ := Metric.uniformContinuous_iff.mp
      (CompactSpace.uniformContinuous_of_continuous g.continuous) η hη
    filter_upwards [hscale.eventually (gt_mem_nhds hδ)] with N hN
    rintro ⟨i, hi⟩
    have hh := hclose
      (a := ⟨heightGridTime R N i.castSucc, bot_le, heightGridTime_le R N i.castSucc⟩)
      (b := ⟨heightGridTime R N i.succ, bot_le, heightGridTime_le R N i.succ⟩)
      (by change dist (heightGridTime R N i.castSucc) (heightGridTime R N i.succ) < δ
          rw [dist_heightGridTime_adjacent]; exact hN)
    change |heightLoc θ f (heightGridTime R N i.castSucc) -
      heightLoc θ f (heightGridTime R N i.succ)| < η at hh
    rw [hf N i.castSucc, hf N i.succ] at hi
    exact (not_le_of_gt hh) hi
  exact tendsto_measureReal_zero_of_eventually_notMem P hm hev

/-- Arbitrarily fine fixed grids have uniformly small increment probabilities eventually in `n`. -/
theorem exists_eventually_height_grid_probability_small {μ : PMF ℕ} {θ : ℝ}
    {B : ℕ → ℝ} (h : StableDomain μ θ B) {R : ℝ≥0} (hR : 0 < R)
    {η ε : ℝ} (hη : 0 < η) (hε : 0 < ε) (N₀ : ℕ) :
    ∃ N : ℕ, N₀ ≤ N ∧ 0 < N ∧ ∀ᶠ n : ℕ in atTop,
      (offspringSeqLaw μ).toMeasure.real {ω | ∃ i : Fin N, η ≤
        |scaledHeight B n ω (heightGridTime R N i.castSucc) -
          scaledHeight B n ω (heightGridTime R N i.succ)|} ≤ ε := by
  have hlim := tendsto_height_grid_bad_probability_zero h.alpha_mem R hη
  obtain ⟨N, hN₀, hsmall⟩ := ((eventually_ge_atTop (max N₀ 1)).and
    (hlim.eventually (gt_mem_nhds hε))).exists
  refine ⟨N, (le_max_left _ _).trans hN₀, by omega, ?_⟩
  have hb : IsBoundedUnder (· ≤ ·) atTop (fun n : ℕ =>
      (offspringSeqLaw μ).toMeasure.real {ω | ∃ i : Fin N, η ≤
        |scaledHeight B n ω (heightGridTime R N i.castSucc) -
          scaledHeight B n ω (heightGridTime R N i.succ)|}) := by
    refine ⟨1, ?_⟩
    change ∀ᶠ n : ℕ in atTop, _ ≤ (1 : ℝ)
    exact Eventually.of_forall fun _ => measureReal_le_one
  exact (eventually_lt_of_limsup_lt
    ((height_grid_limsup_probability_le h hR N η).trans_lt hsmall) hb).mono fun _ hn => hn.le

end BGW.StableTrees.HeightTightness
