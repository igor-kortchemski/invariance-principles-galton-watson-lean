/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.SupremumCauchySequence
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Almost sure compact convergence of the fast occupation sequence

Chebyshev and Borel–Cantelli give summable adjacent errors on growing integer horizons.
Completeness of continuous functions on each compact then identifies the raw real limsup.

## References

* [J. Bertoin, *Lévy Processes*, Cambridge University Press, 1996, Chapter IV]
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees

private theorem compact_nnreal_Iic (T : ℝ≥0) : IsCompact (Iic T) := by
  simpa only [Icc, Iic, zero_le, true_and] using
    (isCompact_Icc : IsCompact (Icc (0 : ℝ≥0) T))

/-- Each pointwise error is bounded by its compact supremum. -/
theorem abs_sub_supOccupation_le_compactError {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η)
    (T : ℝ≥0) (f : DLoc) (t : Set.Iic T) :
    |supOccupation ε f t - supOccupation η f t| ≤ compactError ε η T f := by
  let : CompactSpace (Iic T) := isCompact_iff_compactSpace.mp (compact_nnreal_Iic T)
  have hc : Continuous (fun s : Set.Iic T => |supOccupation ε f s - supOccupation η f s|) :=
    (((continuous_supOccupation hε f).sub (continuous_supOccupation hη f)).abs).comp
      continuous_subtype_val
  exact le_ciSup (isCompact_range hc).bddAbove t

/-- Chebyshev and Borel–Cantelli give eventual geometric adjacent compact errors. -/
theorem ae_eventually_compactError_supAuxEps_le {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∀ᶠ k : ℕ in atTop,
      compactError (supAuxEps θ k) (supAuxEps θ (k + 1)) k f ≤ (1 / 2 : ℝ) ^ k := by
  let μ := (stableLocalLaw θ : Measure DLoc)
  let E := fun k f => compactError (supAuxEps θ k) (supAuxEps θ (k + 1)) k f
  let s := fun k => {f : DLoc | (1 / 4 : ℝ) ^ k ≤ E k f ^ 2}
  have hseq := isSupAuxEpsSeq_supAuxEps hθ
  have hi (k : ℕ) : Integrable (fun f => E k f ^ 2) μ ∧
      (∫ f, E k f ^ 2 ∂μ) ≤ (1 / 16 : ℝ) ^ k :=
    hseq.2.2.2 k _ (hseq.1 _) (hseq.2.1.antitone (Nat.le_succ k))
  have hm (k : ℕ) : μ.real (s k) ≤ (1 / 4 : ℝ) ^ k := by
    have hb : 0 < (1 / 4 : ℝ) ^ k := by positivity
    have hh := mul_meas_ge_le_integral_of_nonneg
      (ae_of_all μ (fun f => sq_nonneg (E k f))) (hi k).1 ((1 / 4 : ℝ) ^ k)
    have hp : (1 / 4 : ℝ) ^ k * (1 / 4 : ℝ) ^ k = (1 / 16 : ℝ) ^ k := by
      rw [← mul_pow]
      norm_num
    exact le_of_mul_le_mul_left (hh.trans ((hi k).2.trans_eq hp.symm)) hb
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
  dsimp only [E] at hh
  nlinarith only [hh, hp, hpos]

private noncomputable def occupationOnCompact (θ : ℝ) (hθ : 1 < θ ∧ θ ≤ 2)
    (f : DLoc) (N : ℕ) (k : ℕ) : C(Set.Iic (N : ℝ≥0), ℝ) :=
  ⟨fun t => supOccupation (supAuxEps θ k) f t,
    (continuous_supOccupation ((isSupAuxEpsSeq_supAuxEps hθ).1 k) f).comp continuous_subtype_val⟩

private theorem exists_compact_limit {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (f : DLoc)
    (hf : ∀ᶠ k : ℕ in atTop,
      compactError (supAuxEps θ k) (supAuxEps θ (k + 1)) k f ≤ (1 / 2 : ℝ) ^ k)
    (N : ℕ) :
    ∃ g : C(Set.Iic (N : ℝ≥0), ℝ),
      Tendsto (occupationOnCompact θ hθ f N) atTop (𝓝 g) ∧
        ∀ t : Set.Iic (N : ℝ≥0), supAuxLimit θ f t = g t := by
  let : CompactSpace (Iic (N : ℝ≥0)) :=
    isCompact_iff_compactSpace.mp (compact_nnreal_Iic (N : ℝ≥0))
  let A := occupationOnCompact θ hθ f N
  have hdist : ∀ᶠ k : ℕ in atTop, ‖dist (A k) (A (k + 1))‖ ≤ (1 / 2 : ℝ) ^ k := by
    filter_upwards [hf, eventually_ge_atTop N] with k hk hNk
    rw [Real.norm_of_nonneg dist_nonneg]
    apply (ContinuousMap.dist_le (by positivity)).2
    intro t
    have ht : t.1 ≤ (k : ℝ≥0) := t.2.trans (Nat.cast_le.mpr hNk)
    have hh := (abs_sub_supOccupation_le_compactError
      ((isSupAuxEpsSeq_supAuxEps hθ).1 k)
      ((isSupAuxEpsSeq_supAuxEps hθ).1 (k + 1)) k f ⟨t, ht⟩).trans hk
    simpa only [Real.dist_eq, A, occupationOnCompact, ContinuousMap.coe_mk] using hh
  have hsum := (summable_geometric_of_abs_lt_one
    (by norm_num : |(1 / 2 : ℝ)| < 1)).of_norm_bounded_eventually_nat hdist
  obtain ⟨g, hg⟩ := cauchySeq_tendsto_of_complete (cauchySeq_of_summable_dist hsum)
  refine ⟨g, hg, fun t => ?_⟩
  exact (((continuous_eval_const t).tendsto g).comp hg).limsup_eq

/-- A.s. locally uniform convergence along the fast subsequence, for all `T` simultaneously
(Borel–Cantelli on integer horizons). -/
theorem ae_tendsto_supOccupation_supAuxEps_uniform {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∀ T : ℝ≥0,
      Tendsto (fun k => ⨆ t : Set.Iic T, |supOccupation (supAuxEps θ k) f t - supAuxLimit θ f t|)
        atTop (𝓝 0) := by
  filter_upwards [ae_eventually_compactError_supAuxEps_le hθ] with f hf
  intro T
  obtain ⟨N, hN⟩ := exists_nat_ge T
  obtain ⟨g, hg, he⟩ := exists_compact_limit hθ f hf N
  let : CompactSpace (Iic (N : ℝ≥0)) :=
    isCompact_iff_compactSpace.mp (compact_nnreal_Iic (N : ℝ≥0))
  let A := occupationOnCompact θ hθ f N
  have hbound (k : ℕ) (t : Set.Iic T) :
      |supOccupation (supAuxEps θ k) f t - supAuxLimit θ f t| ≤ dist (A k) g := by
    rw [he ⟨t, t.2.trans hN⟩]
    simpa only [Real.dist_eq, A, occupationOnCompact, ContinuousMap.coe_mk] using
      ContinuousMap.dist_apply_le_dist (f := A k) (g := g) ⟨t, t.2.trans hN⟩
  have hnonneg (k : ℕ) : 0 ≤ ⨆ t : Set.Iic T,
      |supOccupation (supAuxEps θ k) f t - supAuxLimit θ f t| := by
    have hb : BddAbove (range (fun t : Set.Iic T =>
        |supOccupation (supAuxEps θ k) f t - supAuxLimit θ f t|)) :=
      ⟨dist (A k) g, by rintro _ ⟨t, rfl⟩; exact hbound k t⟩
    exact (abs_nonneg _).trans (le_ciSup hb (⟨T, le_rfl⟩ : Set.Iic T))
  apply squeeze_zero hnonneg (fun k => ciSup_le (hbound k))
  simpa only [dist_self, A] using hg.dist (tendsto_const_nhds (x := g))

/-- `M^*_0 = 0`, nondecreasing and continuous, almost surely (uniform limit of continuous
nondecreasing occupations). -/
theorem ae_supAuxLimit_spec {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc),
      supAuxLimit θ f 0 = 0 ∧ Monotone (supAuxLimit θ f) ∧ Continuous (supAuxLimit θ f) := by
  filter_upwards [ae_eventually_compactError_supAuxEps_le hθ] with f hf
  refine ⟨by simp only [supAuxLimit, supOccupation_zero, limsup_const], ?_, ?_⟩
  · intro s t hst
    obtain ⟨N, hN⟩ := exists_nat_ge t
    obtain ⟨g, hg, he⟩ := exists_compact_limit hθ f hf N
    have hsconv := ((continuous_eval_const
      (⟨s, hst.trans hN⟩ : Set.Iic (N : ℝ≥0))).tendsto g).comp hg
    have htconv := ((continuous_eval_const
      (⟨t, hN⟩ : Set.Iic (N : ℝ≥0))).tendsto g).comp hg
    rw [he ⟨s, hst.trans hN⟩, he ⟨t, hN⟩]
    exact le_of_tendsto_of_tendsto hsconv htconv (Eventually.of_forall fun k =>
      monotone_supOccupation ((isSupAuxEpsSeq_supAuxEps hθ).1 k).le f hst)
  · apply continuous_iff_continuousAt.mpr
    intro t
    obtain ⟨N, hN⟩ := exists_nat_gt t
    obtain ⟨g, _, he⟩ := exists_compact_limit hθ f hf N
    have hc : ContinuousOn (supAuxLimit θ f) (Iic (N : ℝ≥0)) := by
      apply continuousOn_iff_continuous_domRestrict.mpr
      convert g.continuous using 1
      funext t
      exact he t
    exact hc.continuousAt (Iic_mem_nhds hN)

end BGW.StableTrees
