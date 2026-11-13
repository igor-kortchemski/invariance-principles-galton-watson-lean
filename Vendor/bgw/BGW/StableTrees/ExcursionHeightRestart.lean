/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.ExcursionHeightHost
public import BGW.StableTrees.ExcursionHeightCancellation
import Mathlib.MeasureTheory.Group.Measure

/-!
# Height restart after a past minimum

Once a centered future window has a negative infimum, small-cutoff occupation before a past
minimum is empty. A.e.-time agreement and continuity identify the continuous restart at zero.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal Classical
open BGW.Skorokhod

namespace BGW.StableTrees

/-- Translation by any nonnegative time preserves an a.e. property of positive real times. -/
theorem ae_positive_translate {P : ℝ → Prop}
    (hP : ∀ᵐ s : ℝ ∂(volume.restrict (Ioi (0 : ℝ))), P s) (a : ℝ≥0) :
    ∀ᵐ s : ℝ ∂(volume.restrict (Ioi (0 : ℝ))), P ((a : ℝ) + s) := by
  have h := (measurePreserving_add_left volume (a : ℝ)).quasiMeasurePreserving.ae
    ((ae_restrict_iff' measurableSet_Ioi).mp hP)
  apply (ae_restrict_iff' measurableSet_Ioi).mpr
  filter_upwards [h] with s hs hpos
  exact hs (add_pos_of_nonneg_of_pos a.2 hpos)

/-- A centered shift with negative future infimum removes all sufficiently shallow old mass. -/
theorem heightApprox_eq_shift_of_past_min (f : DLoc) (a u : ℝ≥0)
    (hmin : ∀ s : ℝ≥0, s ≤ a → f.1 a ≤ f.1 s)
    {ε : ℝ} (hε : ε ≤ -futureInf (DLoc.shift a f) u 0) :
    heightApprox ε f (a + u) = heightApprox ε (DLoc.shift a f) u := by
  have hsplit := heightApprox_sub_shift_eq ε f (a + u) a (by simp)
  rw [add_tsub_cancel_left] at hsplit
  have hzero : {s : ℝ | 0 ≤ s ∧ s < (a : ℝ) ∧
      f.1 s.toNNReal < futureInf f (a + u) s.toNNReal + ε} = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    rintro s ⟨_, hsa, hmargin⟩
    have hsa' : s.toNNReal ≤ a := Real.toNNReal_le_iff_le_coe.mpr hsa.le
    have hlow := hmin s.toNNReal hsa'
    have hinf := monotone_futureInf f (a + u) hsa'
    have hwindow := futureInf_shift_window f a u (u := 0) (zero_le)
    rw [add_zero] at hwindow
    rw [hwindow] at hinf
    linarith only [hmargin, hlow, hinf, hε]
  rw [hzero, measure_empty, ENNReal.toReal_zero, mul_zero] at hsplit
  exact sub_eq_zero.mp hsplit

/-- Universal heights restart after a past minimum whenever the fresh infimum is negative. -/
theorem heightUniv_eq_shift_of_past_min (θ : ℝ) (f : DLoc) (a u : ℝ≥0)
    (hmin : ∀ s : ℝ≥0, s ≤ a → f.1 a ≤ f.1 s)
    (hneg : futureInf (DLoc.shift a f) u 0 < 0) :
    heightUniv θ f (a + u) = heightUniv θ (DLoc.shift a f) u := by
  unfold heightUniv
  apply Filter.limsup_congr
  have ht := (heightEps_tendsto_nhdsWithin_zero θ).mono_right nhdsWithin_le_nhds
  filter_upwards [ht.eventually (gt_mem_nhds (neg_pos.mpr hneg))] with k hk
  exact heightApprox_eq_shift_of_past_min f a u hmin hk.le

/-- A.e. raw restart and continuity identify the continuous height at the restart time. -/
theorem heightLoc_zero_of_raw_restart (θ : ℝ) (f : DLoc) (a : ℝ≥0)
    (hf : ∀ᵐ s : ℝ ∂(volume.restrict (Ioi (0 : ℝ))),
      heightLoc θ f s.toNNReal = heightUniv θ f s.toNNReal)
    (hg : ∀ᵐ s : ℝ ∂(volume.restrict (Ioi (0 : ℝ))),
      heightLoc θ (DLoc.shift a f) s.toNNReal = heightUniv θ (DLoc.shift a f) s.toNNReal)
    (hraw : ∀ u : ℝ≥0, 0 < u → heightUniv θ f (a + u) =
      heightUniv θ (DLoc.shift a f) u) : heightLoc θ f a = 0 := by
  have he : ∀ᵐ s : ℝ ∂(volume.restrict (Ioi (0 : ℝ))),
      heightLoc θ f (a + s.toNNReal) = heightLoc θ (DLoc.shift a f) s.toNNReal := by
    filter_upwards [ae_positive_translate hf a, hg, ae_restrict_mem measurableSet_Ioi]
      with s hs ht hpos
    have hsum : ((a : ℝ) + s).toNNReal = a + s.toNNReal := by
      simpa only [Real.toNNReal_coe] using
        Real.toNNReal_add (show (0 : ℝ) ≤ a from a.2) (show (0 : ℝ) ≤ s from hpos.le)
    rw [hsum] at hs
    exact hs.trans ((hraw s.toNNReal (Real.toNNReal_pos.mpr hpos)).trans ht.symm)
  have hleft : Continuous (fun s : ℝ => heightLoc θ f (a + s.toNNReal)) :=
    (continuous_heightLoc θ f).comp (continuous_const.add continuous_real_toNNReal)
  have hright : Continuous (fun s : ℝ => heightLoc θ (DLoc.shift a f) s.toNNReal) :=
    (continuous_heightLoc θ (DLoc.shift a f)).comp continuous_real_toNNReal
  have heq := eqOn_Icc_of_ae_eq_Ioo (by norm_num : (0 : ℝ) < 1) hleft hright
    (ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioi_self : Ioo (0 : ℝ) 1 ⊆ Ioi 0) he)
  have hz := heq (show (0 : ℝ) ∈ Icc (0 : ℝ) 1 by constructor <;> norm_num)
  simpa only [Real.toNNReal_zero, add_zero, heightLoc_zero] using hz

end BGW.StableTrees
