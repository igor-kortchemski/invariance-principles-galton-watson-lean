/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import Mathlib.Probability.CDF
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Topology.Order.Monotone
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.Topology.Algebra.Module.Cardinality

/-!
# Real-valued Skorokhod representation by quantiles

The common probability space is the open unit interval with Lebesgue measure. Quantiles are
characterized against the actual CDF, so their pushforward laws are the original measures.
Adapted from the real quantile proof in `PoissonDeclumping/Probability/Skorokhod.lean` of the
author's arXiv:2607.22291v1 formalization (local project, commit
`fc5ef722392b1af41e8b9d5fc45d5a521b7823dd`, Apache-2.0), to permit convergence of CDFs on a
dense set, including limits with atoms. Reference: P. Billingsley, *Convergence of Probability
Measures*, 2nd ed., 1999, proof of Theorem 6.7 (the real case by quantiles).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology

namespace BGW.Probability.RealCoupling

/-- Lebesgue probability on the open unit interval. -/
noncomputable def unitProbability : Measure ℝ := volume.restrict (Ioo 0 1)

/-- Lebesgue measure restricted to the open unit interval has total mass one. -/
instance : IsProbabilityMeasure unitProbability := by
  constructor
  simp [unitProbability]

/-- The lower quantile, with harmless totalization outside `0 < u < 1`. -/
noncomputable def quantile (μ : Measure ℝ) (u : ℝ) : ℝ :=
  sSup {x : ℝ | cdf μ x < u}

private theorem lower_level_nonempty (μ : Measure ℝ) {u : ℝ} (hu : 0 < u) :
    {x : ℝ | cdf μ x < u}.Nonempty := by
  obtain ⟨x, hx⟩ := ((tendsto_cdf_atBot μ).eventually (gt_mem_nhds hu)).exists
  exact ⟨x, hx⟩

private theorem lower_level_bddAbove (μ : Measure ℝ) {u : ℝ} (hu : u < 1) :
    BddAbove {x : ℝ | cdf μ x < u} := by
  obtain ⟨x, hx⟩ := ((tendsto_cdf_atTop μ).eventually (lt_mem_nhds hu)).exists
  refine ⟨x, fun y hy => ?_⟩
  by_contra h
  have := (monotone_cdf μ) (le_of_not_ge h)
  exact (not_lt_of_ge (hx.le.trans this)) hy

/-- Quantile/CDF equivalence, including CDF jumps. -/
theorem quantile_le_iff (μ : Measure ℝ) {u x : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    quantile μ u ≤ x ↔ u ≤ cdf μ x := by
  constructor
  · intro h
    by_contra hux
    have hx : cdf μ x < u := lt_of_not_ge hux
    have ht := ((cdf μ).right_continuous x).mono Ioi_subset_Ici_self
    have he := ht.tendsto.eventually (gt_mem_nhds hx)
    obtain ⟨y, hyF, hyx⟩ := (he.and self_mem_nhdsWithin).exists
    have hyq : y ≤ quantile μ u := le_csSup (lower_level_bddAbove μ hu1) hyF
    exact (not_lt_of_ge (hyq.trans h)) hyx
  · intro h
    apply csSup_le (lower_level_nonempty μ hu0)
    intro y hy
    by_contra hyx
    have := (monotone_cdf μ) (le_of_not_ge hyx)
    exact (not_lt_of_ge (h.trans this)) hy

/-- Quantiles are monotone on their probability-parameter domain. -/
theorem quantile_monotoneOn (μ : Measure ℝ) : MonotoneOn (quantile μ) (Ioo 0 1) := by
  intro u hu v hv huv
  apply csSup_le_csSup (lower_level_bddAbove μ hv.2) (lower_level_nonempty μ hu.1)
  intro x hx
  exact hx.trans_le huv

/-- Quantiles are measurable for the common probability measure. -/
theorem quantile_aemeasurable (μ : Measure ℝ) : AEMeasurable (quantile μ) unitProbability :=
  aemeasurable_restrict_of_monotoneOn measurableSet_Ioo (quantile_monotoneOn μ)

private theorem unitProbability_Iic {c : ℝ} (hc : c ≤ 1) :
    unitProbability (Iic c) = ENNReal.ofReal c := by
  rw [unitProbability, Measure.restrict_apply measurableSet_Iic]
  have hi : Iic c ∩ Ioc (0 : ℝ) 1 = Ioc 0 c := by
    ext t
    simp only [mem_inter_iff, mem_Iic, mem_Ioc]
    constructor
    · exact fun h => ⟨h.2.1, h.1⟩
    · exact fun h => ⟨h.2, h.1, h.2.trans hc⟩
  calc volume (Iic c ∩ Ioo (0 : ℝ) 1) = volume (Iic c ∩ Ioc (0 : ℝ) 1) :=
      measure_congr (Filter.EventuallyEqSet.inter .rfl (Ioo_ae_eq_Ioc' (by simp)))
    _ = ENNReal.ofReal c := by rw [hi, Real.volume_Ioc, sub_zero]

/-- The quantile transforms Lebesgue probability on `(0,1)` into the original real law. -/
theorem map_quantile (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    unitProbability.map (quantile μ) = μ := by
  apply Measure.ext_of_Iic
  intro x
  rw [Measure.map_apply_of_aemeasurable (quantile_aemeasurable μ) measurableSet_Iic]
  have hi : (quantile μ ⁻¹' Iic x) ∩ Ioo 0 1 = Iic (cdf μ x) ∩ Ioo 0 1 := by
    ext u
    simp only [mem_inter_iff, mem_preimage, mem_Iic, mem_Ioo]
    constructor
    · rintro ⟨h, hu⟩
      exact ⟨(quantile_le_iff μ hu.1 hu.2).mp h, hu⟩
    · rintro ⟨h, hu⟩
      exact ⟨(quantile_le_iff μ hu.1 hu.2).mpr h, hu⟩
  change (volume.restrict (Ioo 0 1)) _ = _
  rw [Measure.restrict_apply' measurableSet_Ioo, hi,
    ← Measure.restrict_apply measurableSet_Iic]
  exact (unitProbability_Iic (cdf_le_one μ x)).trans (ofReal_cdf μ x)

/-- Pointwise CDF convergence gives quantile convergence at every continuity point of the
limit quantile in the open unit interval. -/
theorem tendsto_quantile_of_continuousWithinAt
    (μ : ℕ → Measure ℝ) (ν : Measure ℝ)
    {D : Set ℝ} (hD : Dense D)
    (hcdf : ∀ x ∈ D, Tendsto (fun n => cdf (μ n) x) atTop (𝓝 (cdf ν x)))
    {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1)
    (hcont : ContinuousWithinAt (quantile ν) (Ioo 0 1) u) :
    Tendsto (fun n => quantile (μ n) u) atTop (𝓝 (quantile ν u)) := by
  apply tendsto_order.2
  constructor
  · intro x hx
    obtain ⟨z, hzD, hxz, hzq⟩ := hD.exists_between hx
    have hF : cdf ν z < u := by
      by_contra h
      exact (not_le_of_gt hzq) ((quantile_le_iff ν hu.1 hu.2).2 (le_of_not_gt h))
    filter_upwards [(hcdf z hzD).eventually (gt_mem_nhds hF)] with n hn
    apply hxz.trans
    exact lt_of_not_ge fun h => (not_le_of_gt hn) ((quantile_le_iff (μ n) hu.1 hu.2).1 h)
  · intro y hy
    obtain ⟨z, hzD, hqz, hzy⟩ := hD.exists_between hy
    have ht : Tendsto (quantile ν) (𝓝[>] u) (𝓝 (quantile ν u)) :=
      (hcont.continuousAt (isOpen_Ioo.mem_nhds hu)).tendsto.mono_left nhdsWithin_le_nhds
    have hbelow := ht.eventually (gt_mem_nhds hqz)
    have hone : ∀ᶠ v : ℝ in 𝓝[>] u, v < 1 :=
      (eventually_lt_nhds hu.2).filter_mono nhdsWithin_le_nhds
    obtain ⟨v, ⟨hqv, hv1⟩, huv⟩ := ((hbelow.and hone).and self_mem_nhdsWithin).exists
    have hF : u < cdf ν z :=
      huv.trans_le ((quantile_le_iff ν (hu.1.trans huv) hv1).1 hqv.le)
    filter_upwards [(hcdf z hzD).eventually (lt_mem_nhds hF)] with n hn
    exact ((quantile_le_iff (μ n) hu.1 hu.2).2 hn.le).trans_lt hzy

/-- Real-valued Skorokhod representation on an explicit common probability space. The input
CDF convergence is required only on a dense set. -/
theorem exists_real_coupling
    (μ : ℕ → Measure ℝ) (ν : Measure ℝ)
    [∀ n, IsProbabilityMeasure (μ n)] [IsProbabilityMeasure ν]
    {D : Set ℝ} (hD : Dense D)
    (hcdf : ∀ x ∈ D, Tendsto (fun n => cdf (μ n) x) atTop (𝓝 (cdf ν x))) :
    ∃ X : ℕ → ℝ → ℝ, ∃ Y : ℝ → ℝ,
      (∀ n, AEMeasurable (X n) unitProbability ∧ unitProbability.map (X n) = μ n) ∧
      AEMeasurable Y unitProbability ∧ unitProbability.map Y = ν ∧
      ∀ᵐ u ∂unitProbability, Tendsto (fun n => X n u) atTop (𝓝 (Y u)) := by
  refine ⟨fun n => quantile (μ n), quantile ν,
    fun n => ⟨quantile_aemeasurable _, map_quantile _⟩,
    quantile_aemeasurable ν, map_quantile ν, ?_⟩
  have hcount := (quantile_monotoneOn ν).countable_not_continuousWithinAt
  have hzero :
      unitProbability {u ∈ Ioo 0 1 | ¬ContinuousWithinAt (quantile ν) (Ioo 0 1) u} = 0 := by
    apply le_antisymm _ bot_le
    exact (Measure.restrict_apply_le _ _).trans_eq (hcount.measure_zero volume)
  have hgood : ∀ᵐ u ∂unitProbability,
      u ∉ {u ∈ Ioo 0 1 | ¬ContinuousWithinAt (quantile ν) (Ioo 0 1) u} := by
    exact ae_iff.2 (by simpa only [mem_ofPred_eq, not_not] using hzero)
  filter_upwards [ae_restrict_mem measurableSet_Ioo, hgood] with u hu hg
  apply tendsto_quantile_of_continuousWithinAt μ ν hD hcdf hu
  by_contra hc
  exact hg ⟨hu, hc⟩

/-- The same representation with globally measurable versions of every random variable. -/
theorem exists_measurable_real_coupling
    (μ : ℕ → Measure ℝ) (ν : Measure ℝ)
    [∀ n, IsProbabilityMeasure (μ n)] [IsProbabilityMeasure ν]
    {D : Set ℝ} (hD : Dense D)
    (hcdf : ∀ x ∈ D, Tendsto (fun n => cdf (μ n) x) atTop (𝓝 (cdf ν x))) :
    ∃ X : ℕ → ℝ → ℝ, ∃ Y : ℝ → ℝ,
      (∀ n, Measurable (X n) ∧ unitProbability.map (X n) = μ n) ∧
      Measurable Y ∧ unitProbability.map Y = ν ∧
      ∀ᵐ u ∂unitProbability, Tendsto (fun n => X n u) atTop (𝓝 (Y u)) := by
  obtain ⟨X, Y, hX, hY, hYlaw, hconv⟩ := exists_real_coupling μ ν hD hcdf
  refine ⟨fun n => (hX n).1.mk (X n), hY.mk Y, ?_, hY.measurable_mk, ?_, ?_⟩
  · intro n
    exact ⟨(hX n).1.measurable_mk,
      (Measure.map_congr (hX n).1.ae_eq_mk).symm.trans (hX n).2⟩
  · exact (Measure.map_congr hY.ae_eq_mk).symm.trans hYlaw
  · have hXa : ∀ᵐ u ∂unitProbability, ∀ n, X n u = (hX n).1.mk (X n) u :=
      ae_all_iff.2 (fun n => (hX n).1.ae_eq_mk)
    filter_upwards [hconv, hXa, hY.ae_eq_mk] with u hc hx hy
    simpa only [← hx, ← hy] using hc

/-- Weak convergence of real probability laws admits measurable almost surely convergent
versions on the real line equipped with Lebesgue measure restricted to `(0,1)`. -/
theorem exists_measurable_coupling_of_tendsto
    {P : ℕ → ProbabilityMeasure ℝ} {Q : ProbabilityMeasure ℝ}
    (h : Tendsto P atTop (𝓝 Q)) :
    ∃ X : ℕ → ℝ → ℝ, ∃ Y : ℝ → ℝ,
      (∀ n, Measurable (X n) ∧ unitProbability.map (X n) = (P n : Measure ℝ)) ∧
      Measurable Y ∧ unitProbability.map Y = (Q : Measure ℝ) ∧
      ∀ᵐ u ∂unitProbability, Tendsto (fun n => X n u) atTop (𝓝 (Y u)) := by
  have hcount : {x : ℝ | 0 < (Q : Measure ℝ) {x}}.Countable :=
    Measure.countable_meas_pos_of_disjoint_iUnion
      (fun x => measurableSet_singleton x) (fun x y hxy => by simpa using hxy)
  have hD : Dense {x : ℝ | (Q : Measure ℝ) {x} = 0} := by
    convert hcount.dense_compl ℝ using 1
    ext x
    simp
  apply exists_measurable_real_coupling (fun n => (P n : Measure ℝ)) (Q : Measure ℝ) hD
  intro x hx
  have hf : (Q : Measure ℝ) (frontier (Iic x)) = 0 :=
    measure_mono_null (frontier_Iic_subset x) hx
  simpa only [cdf_eq_real, measureReal_def, Function.comp_def] using
    (ENNReal.tendsto_toReal (measure_ne_top (Q : Measure ℝ) (Iic x))).comp
      (ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' h hf)

end BGW.Probability.RealCoupling
