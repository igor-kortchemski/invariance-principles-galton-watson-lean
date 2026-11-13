/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.Skorokhod.Basic
public import Mathlib.Topology.UniformSpace.UniformConvergence
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.MetricSpace.Pseudo.Basic

/-!
# Uniform limits of càdlàg paths

Completeness of the state space supplies the left limits of a uniform limit. No completeness
claim for the ordinary J1 metric is used.
-/

@[expose] public section

open Set Filter
open scoped Topology

namespace BGW.Skorokhod

/-- Uniform limits of càdlàg functions into a complete metric space are càdlàg. -/
theorem isCadlag_of_tendstoUniformly {X E : Type*} [TopologicalSpace X] [Preorder X]
    [MetricSpace E] [CompleteSpace E] {F : ℕ → X → E} {f : X → E}
    (hF : ∀ n, IsCadlag (F n)) (h : TendstoUniformly F f atTop) : IsCadlag f where
  isRightContinuous t := h.tendsto_of_eventually_tendsto
    (Filter.Eventually.of_forall fun n => (hF n).isRightContinuous t) (h.tendsto_at t)
  tendsto_nhdsLT t := by
    by_cases hb : 𝓝[<] t = ⊥
    · exact ⟨f t, by rw [hb]; exact tendsto_bot⟩
    let : NeBot (𝓝[<] t) := ⟨hb⟩
    apply cauchy_map_iff_exists_tendsto.mp
    apply Metric.cauchy_iff.mpr
    refine ⟨inferInstance, ?_⟩
    intro ε hε
    obtain ⟨n, hn⟩ := (Metric.tendstoUniformly_iff.mp h (ε / 4) (by linarith)).exists
    obtain ⟨a, ha⟩ := (hF n).tendsto_nhdsLT t
    have hnear : ∀ᶠ s in 𝓝[<] t, dist (F n s) a < ε / 4 :=
      ha.eventually (Metric.ball_mem_nhds a (by linarith))
    have hball : Metric.ball a (ε / 2) ∈ Filter.map f (𝓝[<] t) := by
      change ∀ᶠ s in 𝓝[<] t, dist (f s) a < ε / 2
      filter_upwards [hnear] with s hs
      have := dist_triangle (f s) (F n s) a
      linarith [hn s]
    refine ⟨Metric.ball a (ε / 2), hball, ?_⟩
    intro y hy z hz
    have htri := dist_triangle_right y z a
    change dist y a < ε / 2 at hy
    change dist z a < ε / 2 at hz
    linarith

/-- A uniformly Cauchy sequence of càdlàg functions has a càdlàg uniform limit. -/
theorem exists_cadlag_uniform_limit {X E : Type*} [TopologicalSpace X] [Preorder X]
    [MetricSpace E] [CompleteSpace E] (F : ℕ → X → E) (hF : ∀ n, IsCadlag (F n))
    (hC : UniformCauchySeqOn F atTop Set.univ) :
    ∃ f : X → E, IsCadlag f ∧ TendstoUniformly F f atTop := by
  have hpoint (x : X) : CauchySeq (fun n => F n x) := by
    apply Metric.cauchySeq_iff.mpr
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.uniformCauchySeqOn_iff.mp hC ε hε
    exact ⟨N, fun m hm n hn => hN m hm n hn x (Set.mem_univ x)⟩
  choose f hf using fun x => cauchySeq_tendsto_of_complete (hpoint x)
  have hunif : TendstoUniformly F f atTop :=
    tendstoUniformlyOn_univ.mp (hC.tendstoUniformlyOn_of_tendsto fun x _ => hf x)
  exact ⟨f, isCadlag_of_tendstoUniformly hF hunif, hunif⟩

end BGW.Skorokhod
