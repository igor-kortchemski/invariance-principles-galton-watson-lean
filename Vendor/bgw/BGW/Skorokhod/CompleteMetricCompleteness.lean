/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.Skorokhod.CompleteMetricTopology
public import Mathlib.Topology.Metrizable.CompletelyMetrizable
import BGW.Skorokhod.CompleteMetricLimits
import BGW.Skorokhod.CompleteMetricUniform
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.ContinuousMap.Compact

/-!
# Completeness of Billingsley's logarithmic-slope metric

Geometrically short matchings align a controlled Cauchy sequence. The cumulative time changes
converge in the complete space of continuous maps, and their slope bounds prevent degeneration.
The aligned paths converge uniformly in the complete state space.
-/

@[expose] public section

open Set Filter
open scoped Topology ENNReal

namespace BGW.Skorokhod

variable {T : ℝ} {E : Type*}

private noncomputable def cumulativeChange (μ : ℕ → TimeChange T) : ℕ → TimeChange T
  | 0 => OrderIso.refl _
  | n + 1 => (cumulativeChange μ n).trans (μ n)

private theorem cumulativeChange_relative_bound (μ : ℕ → TimeChange T)
    (hμ : ∀ n, (μ n).logSlope ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ n))
    (k n : ℕ) (hkn : k ≤ n) :
    TimeChange.logSlope ((cumulativeChange μ k).symm.trans (cumulativeChange μ n)) ≤
      ENNReal.ofReal (2 * ((1 / 2 : ℝ) ^ k - (1 / 2 : ℝ) ^ n)) := by
  induction n, hkn using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    have hnonneg : 0 ≤ 2 * ((1 / 2 : ℝ) ^ k - (1 / 2 : ℝ) ^ n) := by
      apply mul_nonneg (by norm_num)
      exact sub_nonneg.mpr (pow_le_pow_of_le_one (by norm_num) (by norm_num) hn)
    have hcomp : (cumulativeChange μ k).symm.trans (cumulativeChange μ (n + 1)) =
        ((cumulativeChange μ k).symm.trans (cumulativeChange μ n)).trans (μ n) := rfl
    rw [hcomp]
    apply (TimeChange.logSlope_trans_le _ _).trans
    apply (add_le_add ih (hμ n)).trans
    rw [← ENNReal.ofReal_add hnonneg (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    rw [pow_succ]
    nlinarith

private theorem controlled_sequence_converges [MetricSpace E] [CompleteSpace E]
    (hT : 0 ≤ T) (u : ℕ → DComplete T E)
    (hu : ∀ N n m : ℕ, N ≤ n → N ≤ m →
      dist (u n) (u m) < (1 / 2 : ℝ) ^ N) :
    ∃ f : DComplete T E, Tendsto u atTop (𝓝 f) := by
  classical
  let v : ℕ → D T E := u
  have hmatching (n : ℕ) : ∃ μ : TimeChange T,
      completeCost (u n) (u (n + 1)) μ < ENNReal.ofReal ((1 / 2 : ℝ) ^ n) :=
    exists_completeCost_lt _ _ (hu n n (n + 1) le_rfl (Nat.le_succ n))
  choose μ hμ using hmatching
  have hμlog (n : ℕ) : (μ n).logSlope ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ n) :=
    (le_max_left _ _).trans (hμ n).le
  have hμpath (n : ℕ) (t : Icc (0 : ℝ) T) :
      dist (v n t) (v (n + 1) (μ n t)) ≤ (1 / 2 : ℝ) ^ n := by
    apply (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp
    rw [← edist_dist]
    exact (le_iSup _ t).trans ((le_max_right _ _).trans (hμ n).le)
  let cum := cumulativeChange μ
  let L : ℕ → C(Icc (0 : ℝ) T, Icc (0 : ℝ) T) := fun n => ⟨cum n, (cum n).continuous⟩
  have hLstep (n : ℕ) : dist (L n) (L (n + 1)) ≤ (2 * T) * (1 / 2 : ℝ) ^ n := by
    apply (ContinuousMap.dist_le (by positivity)).mpr
    intro t
    change dist (cum n t) (μ n (cum n t)) ≤ _
    rw [Subtype.dist_eq, Real.dist_eq, abs_sub_comm]
    have hpow0 : 0 ≤ (1 / 2 : ℝ) ^ n := by positivity
    have hpow1 : (1 / 2 : ℝ) ^ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    have hexp : Real.exp ((1 / 2 : ℝ) ^ n) - 1 ≤ 2 * (1 / 2 : ℝ) ^ n := by
      have := Real.abs_exp_sub_one_le (x := (1 / 2 : ℝ) ^ n)
        (by simpa only [abs_of_nonneg hpow0] using hpow1)
      exact (le_abs_self _).trans (by simpa only [abs_of_nonneg hpow0] using this)
    have hdisp := (μ n).abs_sub_le_mul_exp_sub_one hpow0 (hμlog n) (cum n t)
    have he : 0 ≤ Real.exp ((1 / 2 : ℝ) ^ n) - 1 :=
      sub_nonneg.mpr (Real.one_le_exp_iff.mpr hpow0)
    calc
      |(μ n (cum n t) : ℝ) - cum n t| ≤ (cum n t : ℝ) *
          (Real.exp ((1 / 2 : ℝ) ^ n) - 1) := hdisp
      _ ≤ T * (Real.exp ((1 / 2 : ℝ) ^ n) - 1) :=
        mul_le_mul_of_nonneg_right (cum n t).2.2 he
      _ ≤ (2 * T) * (1 / 2 : ℝ) ^ n := by nlinarith [mul_le_mul_of_nonneg_left hexp hT]
  obtain ⟨Llimit, hLlimit⟩ := cauchySeq_tendsto_of_complete
    (cauchySeq_of_le_geometric (1 / 2 : ℝ) (2 * T) (by norm_num) hLstep)
  have hLpoint (t : Icc (0 : ℝ) T) :
      Tendsto (fun n => (cum n t : ℝ)) atTop (𝓝 (Llimit t : ℝ)) :=
    (continuous_subtype_val.tendsto (Llimit t)).comp
      ((continuous_eval_const t).tendsto Llimit |>.comp hLlimit)
  have hcumlog (n : ℕ) : (cum n).logSlope ≤ ENNReal.ofReal (2 : ℝ) := by
    have h := cumulativeChange_relative_bound μ hμlog 0 n (Nat.zero_le n)
    have heq : (cumulativeChange μ 0).symm.trans (cumulativeChange μ n) = cum n := rfl
    rw [heq] at h
    apply h.trans
    apply ENNReal.ofReal_le_ofReal
    simp only [pow_zero]
    nlinarith [pow_nonneg (show (0 : ℝ) ≤ 1 / 2 by norm_num) n]
  obtain ⟨Λ, hΛ⟩ := exists_timeChange_of_tendsto_bounded_logSlope hT cum Llimit hLpoint
    (by norm_num) hcumlog
  have hrel (n : ℕ) : TimeChange.logSlope ((cum n).symm.trans Λ) ≤
      ENNReal.ofReal (2 * (1 / 2 : ℝ) ^ n) := by
    apply TimeChange.logSlope_le_of_tendsto
      (fun m => (cum n).symm.trans (cum m)) ((cum n).symm.trans Λ)
      (fun t => by simpa only [OrderIso.trans_apply, hΛ] using hLpoint ((cum n).symm t))
      (by positivity)
    filter_upwards [eventually_ge_atTop n] with m hm
    apply (cumulativeChange_relative_bound μ hμlog n m hm).trans
    apply ENNReal.ofReal_le_ofReal
    nlinarith [pow_nonneg (show (0 : ℝ) ≤ 1 / 2 by norm_num) m]
  let G : ℕ → Icc (0 : ℝ) T → E := fun n t => v n (cum n t)
  have hGstep (t : Icc (0 : ℝ) T) (n : ℕ) :
      dist (G n t) (G (n + 1) t) ≤ 1 * (1 / 2 : ℝ) ^ n := by
    simpa only [G, cum, cumulativeChange, OrderIso.trans_apply, one_mul]
      using hμpath n (cum n t)
  have hGcauchy (t : Icc (0 : ℝ) T) : CauchySeq (fun n => G n t) :=
    cauchySeq_of_le_geometric (1 / 2 : ℝ) 1 (by norm_num) (hGstep t)
  choose g hg using fun t => cauchySeq_tendsto_of_complete (hGcauchy t)
  have hGbound (n : ℕ) (t : Icc (0 : ℝ) T) :
      dist (G n t) (g t) ≤ 2 * (1 / 2 : ℝ) ^ n := by
    have := dist_le_of_le_geometric_of_tendsto (1 / 2 : ℝ) 1 (by norm_num)
      (hGstep t) (hg t) n
    norm_num at this ⊢
    linarith
  have hpow : Tendsto (fun n : ℕ => 2 * (1 / 2 : ℝ) ^ n) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul (tendsto_pow_atTop_nhds_zero_of_lt_one
      (show (0 : ℝ) ≤ 1 / 2 by norm_num) (by norm_num))
  have hGunif : TendstoUniformly G g atTop := by
    apply Metric.tendstoUniformly_iff.mpr
    intro ε hε
    filter_upwards [hpow.eventually (gt_mem_nhds hε)] with n hn t
    rw [dist_comm]
    exact (hGbound n t).trans_lt hn
  have hgcadlag : IsCadlag g := isCadlag_of_tendstoUniformly
    (fun n => isCadlag_comp_timeChange (isCadlag (v n)) (cum n)) hGunif
  let f : D T E := ⟨g ∘ Λ.symm, isCadlag_comp_timeChange hgcadlag Λ.symm⟩
  refine ⟨f, ?_⟩
  apply tendsto_iff_dist_tendsto_zero.mpr
  apply squeeze_zero (fun _ => dist_nonneg) _ hpow
  intro n
  change j1CompleteDist (u n) f ≤ 2 * (1 / 2 : ℝ) ^ n
  apply j1CompleteDist_le_of_completeCost_le _ _ ((cum n).symm.trans Λ) (by positivity)
  apply max_le (hrel n)
  refine iSup_le fun t => ?_
  rw [edist_dist]
  apply ENNReal.ofReal_le_ofReal
  simpa only [f, coe_mk, Function.comp_apply, OrderIso.trans_apply,
    OrderIso.symm_apply_apply, G, v, OrderIso.apply_symm_apply] using hGbound n ((cum n).symm t)

/-- `d°` is complete when `E` is complete (Billingsley 1999, Theorem 12.2). -/
instance instCompleteSpaceDComplete [MetricSpace E] [CompleteSpace E] :
    CompleteSpace (DComplete T E) := by
  by_cases hT : 0 ≤ T
  · exact Metric.complete_of_convergent_controlled_sequences
      (fun n => (1 / 2 : ℝ) ^ n) (fun _ => by positivity)
      (controlled_sequence_converges hT)
  · let : Subsingleton (DComplete T E) := ⟨fun f g => by
      apply BGW.Skorokhod.ext
      intro t
      exact (hT (t.2.1.trans t.2.2)).elim⟩
    infer_instance

/-- The Skorokhod space of a complete metric space is completely metrizable (C3). -/
instance instIsCompletelyMetrizableSpace [MetricSpace E] [CompleteSpace E] :
    TopologicalSpace.IsCompletelyMetrizableSpace (D T E) := by
  exact toDComplete.isClosedEmbedding.IsCompletelyMetrizableSpace

end BGW.Skorokhod
