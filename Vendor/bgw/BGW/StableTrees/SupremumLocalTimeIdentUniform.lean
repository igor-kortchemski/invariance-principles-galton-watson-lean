/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.SupremumLocalTimeIdentConvergence
import Mathlib.Topology.Sequences

/-!
# Compact uniform convergence of monotone occupation functions

Monotonicity is in time, rather than in the approximation index. Compactness and squeezing
at a moving time give uniform convergence to the continuous auxiliary clock.

Reference: J. Bertoin, *Lévy Processes*, Cambridge University Press, 1996, Chapter IV.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees

private theorem tendsto_monotone_moving {F : ℕ → ℝ≥0 → ℝ} {g : ℝ≥0 → ℝ}
    (hm : ∀ n, Monotone (F n)) (hc : Continuous g)
    (hp : ∀ t, Tendsto (fun n => F n t) atTop (𝓝 (g t)))
    {v : ℕ → ℝ≥0} {t : ℝ≥0} (hv : Tendsto v atTop (𝓝 t)) :
    Tendsto (fun n => F n (v n)) atTop (𝓝 (g t)) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    by_cases ht : t = 0
    · subst t
      filter_upwards [(hp 0).eventually (Ioi_mem_nhds ha)] with n hn
      exact hn.trans_le (hm n (zero_le : 0 ≤ v n))
    · have ht0 : 0 < t := pos_iff_ne_zero.mpr ht
      let : NeBot (𝓝[<] t) := nhdsLT_neBot_of_exists_lt ⟨0, ht0⟩
      have hL : ∀ᶠ s in 𝓝[<] t, s < t := self_mem_nhdsWithin
      obtain ⟨s, hs, hgs⟩ := (hL.and
        ((hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).eventually
          (Ioi_mem_nhds ha))).exists
      filter_upwards [(hp s).eventually (Ioi_mem_nhds hgs),
        hv.eventually (Ioi_mem_nhds hs)] with n hn hvn
      exact hn.trans_le (hm n hvn.le)
  · intro b hb
    have hR : ∀ᶠ s in 𝓝[>] t, t < s := self_mem_nhdsWithin
    obtain ⟨s, hs, hgs⟩ := (hR.and
      ((hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).eventually
        (Iio_mem_nhds hb))).exists
    filter_upwards [(hp s).eventually (Iio_mem_nhds hgs),
      hv.eventually (Iio_mem_nhds hs)] with n hn hvn
    exact (hm n hvn.le).trans_lt hn

/-- Continuous nondecreasing functions converging pointwise to a continuous function
converge uniformly on every compact initial interval. -/
theorem tendsto_compact_sup_of_monotone {F : ℕ → ℝ≥0 → ℝ} {g : ℝ≥0 → ℝ}
    (hm : ∀ n, Monotone (F n)) (hF : ∀ n, Continuous (F n)) (hc : Continuous g)
    (hp : ∀ t, Tendsto (fun n => F n t) atTop (𝓝 (g t))) (T : ℝ≥0) :
    Tendsto (fun n => ⨆ t : Iic T, |F n t - g t|) atTop (𝓝 0) := by
  have hT : IsCompact (Iic T) := by
    simpa only [Icc, Iic, zero_le, true_and] using
      (isCompact_Icc : IsCompact (Icc (0 : ℝ≥0) T))
  let : CompactSpace (Iic T) := isCompact_iff_compactSpace.mp hT
  have hb (n : ℕ) : BddAbove (range (fun t : Iic T => |F n t - g t|)) :=
    (isCompact_range ((((hF n).sub hc).abs).comp continuous_subtype_val)).bddAbove
  apply Metric.tendsto_atTop.mpr
  intro δ hδ
  have hnn (n : ℕ) : 0 ≤ ⨆ t : Iic T, |F n t - g t| :=
    (abs_nonneg _).trans (le_ciSup (hb n) ⟨T, le_rfl⟩)
  suffices ∀ᶠ n in atTop, (⨆ t : Iic T, |F n t - g t|) < δ by
    simpa only [Real.dist_eq, sub_zero, abs_of_nonneg (hnn _), eventually_atTop] using this
  by_contra hn
  obtain ⟨ns, hns, hbad⟩ := exists_seq_forall_of_frequently (not_eventually.mp hn)
  have hex (n : ℕ) : ∃ t : Iic T, δ / 2 < |F (ns n) t - g t| := by
    apply (lt_ciSup_iff (hb _)).mp
    exact (half_lt_self hδ).trans_le (le_of_not_gt (hbad n))
  choose ts hts using hex
  obtain ⟨t, φ, hφ, htφ⟩ := CompactSpace.tendsto_subseq ts
  have hidx : Tendsto (ns ∘ φ) atTop atTop := hns.comp hφ.tendsto_atTop
  have hmoving := tendsto_monotone_moving (fun n => hm (ns (φ n))) hc
    (fun s => (hp s).comp hidx) (continuous_subtype_val.tendsto t |>.comp htφ)
  have hg := hc.continuousAt.tendsto.comp
    (continuous_subtype_val.tendsto t |>.comp htφ)
  have hz : Tendsto (fun n => |F (ns (φ n)) (ts (φ n)) - g (ts (φ n))|)
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, sub_self, abs_zero] using (hmoving.sub hg).abs
  have hle := ge_of_tendsto hz (Eventually.of_forall fun n => (hts (φ n)).le)
  linarith

/-- Locally uniform identification for any simultaneous occupation sequence. -/
theorem ae_tendsto_supOccupation_uniform_aux {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {ε : ℕ → ℝ}
    (hε : IsSupOccupationSeq θ ε) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∀ T : ℝ≥0,
      Tendsto (fun k => ⨆ t : Set.Iic T, |supOccupation (ε k) f t - supAuxLocalTime θ f t|)
        atTop (𝓝 0) := by
  filter_upwards [ae_tendsto_supOccupation_aux hθ hε,
    ae_supAuxLocalTime_continuous hθ] with f hf hc
  exact tendsto_compact_sup_of_monotone
    (fun k => monotone_supOccupation (hε.1 k).le f)
    (fun k => continuous_supOccupation (hε.1 k) f) hc.2.2 hf

/-- Locally uniform convergence to the public clock, simultaneously over horizons. -/
theorem ae_tendsto_supOccupation_uniform {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∀ T : ℝ≥0,
      Tendsto (fun k => ⨆ t : Set.Iic T, |supOccupation (supEps θ k) f t - supLocalTime θ f t|)
        atTop (𝓝 0) := by
  filter_upwards [ae_tendsto_supOccupation_uniform_aux hθ (isSupOccupationSeq_supEps hθ),
    ae_supLocalTime_eq_aux hθ] with f hf he
  simpa only [funext he] using hf

end BGW.StableTrees
