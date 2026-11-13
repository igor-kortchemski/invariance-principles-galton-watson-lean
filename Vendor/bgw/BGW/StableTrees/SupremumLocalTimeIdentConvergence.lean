/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.SupremumLocalTimeIdentBasic
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Identification for arbitrary simultaneous occupation sequences

A subsequence of any admissible sequence can be paired with the fast auxiliary sequence.
The uniform second-moment bounds and Borel–Cantelli identify all finite-time limits on one
common event, using the sequence's simultaneous convergence hypothesis.

Reference: J. Bertoin, *Lévy Processes*, Cambridge University Press, 1996, Chapter IV.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees

private theorem ae_eventually_geometric_error {θ : ℝ} {E : ℕ → DLoc → ℝ}
    (hi : ∀ k, Integrable (fun f => E k f ^ 2) (stableLocalLaw θ : Measure DLoc))
    (hb : ∀ k, (∫ f, E k f ^ 2 ∂(stableLocalLaw θ : Measure DLoc)) ≤ (1 / 16 : ℝ) ^ k) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∀ᶠ k in atTop,
      E k f ≤ (1 / 2 : ℝ) ^ k := by
  let μ := (stableLocalLaw θ : Measure DLoc)
  let s := fun k => {f : DLoc | (1 / 4 : ℝ) ^ k ≤ E k f ^ 2}
  have hm (k : ℕ) : μ.real (s k) ≤ (1 / 4 : ℝ) ^ k := by
    have hh := mul_meas_ge_le_integral_of_nonneg
      (ae_of_all μ (fun f => sq_nonneg (E k f))) (hi k) ((1 / 4 : ℝ) ^ k)
    have hp : (1 / 4 : ℝ) ^ k * (1 / 4 : ℝ) ^ k = (1 / 16 : ℝ) ^ k := by
      rw [← mul_pow]
      norm_num
    exact le_of_mul_le_mul_left (hh.trans ((hb k).trans_eq hp.symm)) (by positivity)
  have hμ (k : ℕ) : μ (s k) ≤ (1 / 4 : ℝ≥0∞) ^ k := by
    have hh := ENNReal.ofReal_le_ofReal (hm k)
    simpa only [Measure.real, ENNReal.ofReal_toReal (measure_ne_top _ _),
      ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 1 / 4), ENNReal.ofReal_div_of_pos
        (by norm_num : (0 : ℝ) < 4), ENNReal.ofReal_one, ENNReal.ofReal_ofNat] using hh
  have hsum : (∑' k, μ (s k)) ≠ ∞ :=
    ne_top_of_le_ne_top (tsum_geometric_lt_top.mpr (by norm_num : (1 / 4 : ℝ≥0∞) < 1)).ne
      (ENNReal.tsum_le_tsum hμ)
  filter_upwards [ae_eventually_notMem hsum] with f hf
  filter_upwards [hf] with k hk
  have hh : E k f ^ 2 < (1 / 4 : ℝ) ^ k := lt_of_not_ge hk
  have hp : ((1 / 2 : ℝ) ^ k) ^ 2 = (1 / 4 : ℝ) ^ k := by
    rw [sq, ← mul_pow]
    norm_num
  have hpos : 0 ≤ (1 / 2 : ℝ) ^ k := by positivity
  nlinarith only [hh, hp, hpos]

/-- Every simultaneous occupation sequence has the same all-time limit as the auxiliary clock. -/
theorem ae_tendsto_supOccupation_aux {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {ε : ℕ → ℝ}
    (hε : IsSupOccupationSeq θ ε) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∀ t : ℝ≥0,
      Tendsto (fun k => supOccupation (ε k) f t) atTop (𝓝 (supAuxLocalTime θ f t)) := by
  have hp : ∀ k n : ℕ, ∃ m : ℕ, n < m ∧ ε m < supAuxEps θ k := by
    intro k n
    exact ((eventually_gt_atTop n).and
      (hε.2.2.1.eventually (Iio_mem_nhds (supAuxEps_pos θ k)))).exists
  choose next hnext using hp
  let idx : ℕ → ℕ := Nat.rec (next 0 0) (fun k n => next (k + 1) n)
  have hi : StrictMono idx := strictMono_nat_of_lt_succ fun k => (hnext (k + 1) (idx k)).1
  have hs (k : ℕ) : ε (idx k) < supAuxEps θ k := by
    cases k with
    | zero => exact (hnext 0 0).2
    | succ k => exact (hnext (k + 1) (idx k)).2
  let E := fun k f => compactError (supAuxEps θ k) (ε (idx k)) k f
  have hbound (k : ℕ) := (isSupAuxEpsSeq_supAuxEps hθ).2.2.2 k _ (hε.1 _) (hs k).le
  have hae := ae_eventually_geometric_error (fun k => (hbound k).1) (fun k => (hbound k).2)
  filter_upwards [hae, hε.2.2.2, ae_supAuxLocalTime_continuous hθ,
    ae_tendsto_supOccupation_supAuxEps_uniform hθ]
    with f hf hlim hc hu
  intro t
  obtain ⟨l, hl⟩ := hlim t
  have haux : Tendsto (fun k => supOccupation (supAuxEps θ k) f t) atTop
      (𝓝 (supAuxLocalTime θ f t)) := by
    let : CompactSpace (Iic t) := isCompact_iff_compactSpace.mp (by
      simpa only [Icc, Iic, zero_le, true_and] using
        (isCompact_Icc : IsCompact (Icc (0 : ℝ≥0) t)))
    apply tendsto_iff_dist_tendsto_zero.mpr
    simp only [Real.dist_eq]
    apply squeeze_zero (fun _ => abs_nonneg _) _ (hu t)
    intro k
    refine le_ciSup (f := fun u : Iic t =>
      |supOccupation (supAuxEps θ k) f u - supAuxLimit θ f u|) ?_ ⟨t, le_rfl⟩
    exact (isCompact_range ((((continuous_supOccupation (supAuxEps_pos θ k) f).sub
      hc.2.2).abs).comp continuous_subtype_val)).bddAbove
  have hdiff : Tendsto (fun k => supOccupation (ε (idx k)) f t -
      supOccupation (supAuxEps θ k) f t) atTop (𝓝 0) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    simp only [Real.dist_eq, sub_zero]
    apply squeeze_zero' (Eventually.of_forall fun _ => abs_nonneg _) _
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num))
    filter_upwards [hf, (tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop t))]
      with k hk htk
    rw [abs_sub_comm]
    exact (abs_sub_supOccupation_le_compactError (supAuxEps_pos θ k) (hε.1 _)
      k f ⟨t, htk⟩).trans hk
  have hsub : Tendsto (fun k => supOccupation (ε (idx k)) f t) atTop
      (𝓝 (supAuxLocalTime θ f t)) := by
    simpa only [zero_add, sub_add_cancel] using hdiff.add haux
  have he := tendsto_nhds_unique (hl.comp hi.tendsto_atTop) hsub
  simpa only [he] using hl

/-- The public and auxiliary clocks agree at every time on one full-measure event. -/
theorem ae_supLocalTime_eq_aux {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∀ t : ℝ≥0,
      supLocalTime θ f t = supAuxLocalTime θ f t := by
  filter_upwards [ae_tendsto_supOccupation_aux hθ (isSupOccupationSeq_supEps hθ)] with f hf
  exact fun t => (hf t).limsup_eq

/-- The extended public clock agrees with the finite auxiliary clock simultaneously. -/
theorem ae_supLocalTimeENN_eq_aux {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∀ t : ℝ≥0,
      supLocalTimeENN θ f t = ENNReal.ofReal (supAuxLocalTime θ f t) := by
  filter_upwards [ae_tendsto_supOccupation_aux hθ (isSupOccupationSeq_supEps hθ)] with f hf
  exact fun t => (ENNReal.tendsto_ofReal (hf t)).limsup_eq

end BGW.StableTrees
