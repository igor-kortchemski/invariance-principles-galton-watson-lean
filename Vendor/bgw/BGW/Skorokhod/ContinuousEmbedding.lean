/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.Skorokhod.Continuous
public import Mathlib.Topology.Sequences
public import Mathlib.Topology.UniformSpace.UniformApproximation

/-!
# Closed embedding of continuous paths

The inclusion of continuous paths into Skorokhod space is a closed embedding. Its topology is
the uniform topology, and its range is closed because a uniform limit of continuous paths is
continuous.
-/

@[expose] public section

open Set Filter Topology

namespace BGW.Skorokhod

variable {T : ℝ} {E : Type*}

/-- Continuous paths form a closed subset of `D`, on which J1 is the uniform topology (C5.3). -/
theorem isClosedEmbedding_ofContinuous [MetricSpace E] :
    Topology.IsClosedEmbedding (ofContinuous (T := T) (E := E)) := by
  have hinj : Function.Injective (ofContinuous (T := T) (E := E)) := by
    intro f g h
    ext t
    exact DFunLike.congr_fun h t
  refine ⟨⟨?_, hinj⟩, ?_⟩
  · apply isInducing_iff_nhds.mpr
    intro f
    apply le_antisymm (lipschitzWith_one_ofContinuous.continuous.tendsto f).le_comap
    have hlim : Tendsto (ofContinuous (T := T) (E := E))
        (comap ofContinuous (𝓝 (ofContinuous f))) (𝓝 (ofContinuous f)) := tendsto_comap
    have hsup := tendsto_iSup_dist_of_tendsto_ofContinuous
      (u := ofContinuous) hlim
    have hdist : Tendsto (fun u : C(Set.Icc (0 : ℝ) T, E) => dist u f)
        (comap ofContinuous (𝓝 (ofContinuous f))) (𝓝 0) := by
      simpa only [ContinuousMap.dist_eq_iSup, ofContinuous, coe_mk] using hsup
    exact tendsto_iff_dist_tendsto_zero.mpr hdist
  · apply IsSeqClosed.isClosed
    intro u g hu hug
    choose v hv using hu
    have hlim : Tendsto (fun n => ofContinuous (v n)) atTop (𝓝 g) := by
      simpa only [hv] using hug
    obtain ⟨σ, _hdisp, hpath⟩ := tendsto_iff_exists_timeChange.mp hlim
    have hgcont : Continuous g := by
      by_cases hT : 0 ≤ T
      · have hunif : TendstoUniformly (fun n t => v n (σ n t)) g atTop := by
          rw [Metric.tendstoUniformly_iff]
          intro ε hε
          have he := Metric.tendsto_nhds.mp hpath ε hε
          filter_upwards [he] with n hn
          have hnonneg : 0 ≤ ⨆ t : Set.Icc (0 : ℝ) T,
              dist (ofContinuous (v n) (σ n t)) (g t) :=
            le_ciSup_of_le (bddAbove_comp_dist hT (ofContinuous (v n)) g (σ n))
              ⟨0, by simp [hT]⟩ dist_nonneg
          rw [Real.dist_eq, sub_zero, abs_of_nonneg hnonneg] at hn
          intro t
          rw [dist_comm]
          exact lt_of_le_of_lt
            (le_ciSup (bddAbove_comp_dist hT (ofContinuous (v n)) g (σ n)) t) hn
        exact hunif.continuous (Frequently.of_forall fun n =>
          (v n).continuous.comp (σ n).continuous)
      · have hempty : IsEmpty (Set.Icc (0 : ℝ) T) :=
          ⟨fun t => (not_le_of_gt (lt_of_not_ge hT)) (le_trans t.property.1 t.property.2)⟩
        exact continuous_iff_continuousAt.mpr fun t => (hempty.false t).elim
    exact ⟨⟨g, hgcont⟩, by ext t; rfl⟩

end BGW.Skorokhod
