/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
public import Mathlib.Topology.MetricSpace.Polish

import BGW.Probability.SkorokhodRepresentationPartitions
import Mathlib.Topology.Instances.CantorSet
import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-!
# Almost everywhere continuous real encodings

Membership in countably many continuity cells encodes a separable metric space into Cantor
space. The encoding is continuous away from the cell boundaries and reflects convergence.
For a Polish source, its composition with the Cantor embedding is a measurable embedding
into the real line. This reduces Skorokhod representation to the real quantile construction.
-/

@[expose] public section

open Filter MeasureTheory Set TopologicalSpace
open scoped Topology

namespace BGW.Probability

open scoped Classical in
private theorem continuousAt_membership {S : Type*} [TopologicalSpace S]
    (A : Set S) {x : S} (hx : x ∉ frontier A) :
    ContinuousAt (fun y => if y ∈ A then true else false) x := by
  classical
  by_cases hxA : x ∈ A
  · have hi : x ∈ interior A := (mem_interior_iff_notMem_frontier hxA).mpr hx
    apply (continuousAt_const : ContinuousAt (fun _ : S => true) x).congr
    filter_upwards [mem_interior_iff_mem_nhds.mp hi] with y hy
    simp [hy]
  · have hi : x ∈ interior Aᶜ :=
      (mem_interior_iff_notMem_frontier hxA).mpr (by simpa using hx)
    apply (continuousAt_const : ContinuousAt (fun _ : S => false) x).congr
    filter_upwards [mem_interior_iff_mem_nhds.mp hi] with y hy
    have hyA : y ∉ A := hy
    simp [hyA]

/-- A finite Borel measure on a nonempty Polish metric space admits a measurable real
encoding that is continuous almost everywhere and reflects convergence of sequences. -/
theorem exists_ae_continuous_real_encoding {S : Type*} [MetricSpace S] [PolishSpace S]
    [Nonempty S] [MeasurableSpace S] [BorelSpace S] (μ : Measure S) [IsFiniteMeasure μ] :
    ∃ g : S → ℝ, MeasurableEmbedding g ∧ (∀ᵐ x ∂μ, ContinuousAt g x) ∧
      ∀ (u : ℕ → S) (x : S),
        Tendsto (fun n => g (u n)) atTop (𝓝 (g x)) → Tendsto u atTop (𝓝 x) := by
  classical
  choose A hAmeas _hAdisj hAcover hAnull hAmesh using
    fun k : ℕ => exists_continuity_partition μ
      (show 0 < (1 / 2 : ℝ) ^ k by positivity)
  let C : S → ℕ → ℕ → Bool := fun x k j => if x ∈ A k j then true else false
  have hCmeas : Measurable C := by
    apply Measurable.of_eval
    intro k
    apply Measurable.of_eval
    intro j
    exact Measurable.ite (hAmeas k j) measurable_const measurable_const
  let H : (ℕ → ℕ → Bool) ≃ₜ cantorSet :=
    cantorSpaceHomeomorphNatToCantorSpace.symm.trans cantorSetHomeomorphNatToBool.symm
  let e : (ℕ → ℕ → Bool) → ℝ := fun c => (H c : ℝ)
  have he : Topology.IsEmbedding e := Topology.IsEmbedding.subtypeVal.comp H.isEmbedding
  let g : S → ℝ := e ∘ C
  have hreflect (u : ℕ → S) (x : S)
      (hu : Tendsto (fun n => g (u n)) atTop (𝓝 (g x))) : Tendsto u atTop (𝓝 x) := by
    have hcode : Tendsto (fun n => C (u n)) atTop (𝓝 (C x)) :=
      he.isInducing.tendsto_nhds_iff.mpr hu
    apply Metric.tendsto_atTop.mpr
    intro ε hε
    have hpow : Tendsto (fun k : ℕ => (1 / 2 : ℝ) ^ k) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    obtain ⟨k, hk⟩ := (hpow.eventually (gt_mem_nhds hε)).exists
    obtain ⟨j, hj⟩ : ∃ j, x ∈ A k j := by
      have hx : x ∈ ⋃ j, A k j := by rw [hAcover]; trivial
      exact mem_iUnion.mp hx
    have hc := (tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hcode k) j).eventually
      ((isOpen_discrete {C x k j}).mem_nhds rfl)
    have hnear : ∀ᶠ n in atTop, dist (u n) x < ε := by
      filter_upwards [hc] with n hn
      have hnA : u n ∈ A k j := by
        have hn' := Set.mem_singleton_iff.mp hn
        simpa [C, hj] using hn'
      exact (hAmesh k j (u n) hnA x hj).trans hk
    exact eventually_atTop.mp hnear
  have hinj : Function.Injective g := by
    intro x y hxy
    have ht : Tendsto (fun _ : ℕ => x) atTop (𝓝 y) := by
      apply hreflect
      simpa only [hxy] using (tendsto_const_nhds :
        Tendsto (fun _ : ℕ => g y) atTop (𝓝 (g y)))
    exact tendsto_nhds_unique tendsto_const_nhds ht
  refine ⟨g, (he.continuous.measurable.comp hCmeas).measurableEmbedding hinj, ?_, hreflect⟩
  have hgood : ∀ᵐ x ∂μ, ∀ k j, x ∉ frontier (A k j) := by
    apply ae_all_iff.mpr
    intro k
    apply ae_all_iff.mpr
    intro j
    exact ae_iff.mpr (by simpa using hAnull k j)
  filter_upwards [hgood] with x hx
  have hCx : ContinuousAt C x :=
    continuousAt_pi.mpr fun k => continuousAt_pi.mpr fun j =>
      continuousAt_membership (A k j) (hx k j)
  exact he.continuous.continuousAt.comp hCx

end BGW.Probability
