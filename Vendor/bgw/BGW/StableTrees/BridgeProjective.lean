/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.BridgeProjectivePinning

/-!
# The projective stable bridge

The open law has the prescribed tilted prefixes and converges to zero at its terminal time
almost surely. Closing gives a measurable compact path with pinned endpoints and the same
strict-prefix laws.

## References

* P. Fitzsimmons, J. Pitman and M. Yor, Markovian bridges: construction, Palm interpretation,
  and splicing, Seminar on Stochastic Processes 1992, Progr. Probab. 33, Birkhäuser, 1993,
  101–134.
* L. Chaumont, Excursion normalisée, méandre et pont pour les processus de Lévy stables, Bull.
  Sci. Math. 121 (1997), 377–403.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open BGW.Skorokhod

namespace BGW.StableTrees

/-- Every closed path has terminal value zero. -/
theorem closeBridge_one (f : BridgeOpen) : closeBridge f ⟨1, zero_le_one, le_rfl⟩ = 0 := by
  classical
  by_cases hf : f ∈ BridgeOpen.terminalLimit
  · have heq : closeBridge f =
        ⟨fun t => if (t : ℝ) < 1 then f.eval t else 0, isCadlag_closeFun hf⟩ :=
      dite_eq_left hf
    rw [heq]
    change (if (1 : ℝ) < 1 then f.eval 1 else 0) = 0
    simp only [lt_self_iff_false, ite_false]
  · have heq : closeBridge f = ⟨fun _ => 0, IsCadlag.const⟩ := dite_eq_right hf
    rw [heq]
    rfl

/-- Every closed path has terminal left limit zero. -/
theorem closeBridge_leftLim_one (f : BridgeOpen) :
    Function.leftLim (closeBridge f) ⟨1, zero_le_one, le_rfl⟩ = 0 := by
  classical
  let top : Set.Icc (0 : ℝ) 1 := ⟨1, zero_le_one, le_rfl⟩
  have hbot : Tendsto (fun u : Set.Icc (0 : ℝ) 1 => (u : ℝ))
      (𝓝[<] top) (𝓝[<] (1 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨continuous_subtype_val.continuousAt.tendsto.mono_left nhdsWithin_le_nhds, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with u hu
    exact hu
  have hleft : ContinuousWithinAt (closeBridge f) (Iio top) top := by
    change Tendsto (closeBridge f) (𝓝[<] top) (𝓝 (closeBridge f top))
    rw [closeBridge_one]
    by_cases hf : f ∈ BridgeOpen.terminalLimit
    · have heq : (fun t => closeBridge f t) =ᶠ[𝓝[<] top] fun t => f.eval t := by
        filter_upwards [self_mem_nhdsWithin] with u hu
        simp only [closeBridge, dite_eq_left hf, BGW.Skorokhod.coe_mk,
          ite_eq_left (show (u : ℝ) < 1 from hu)]
      exact (tendsto_congr' heq).2 (hf.comp hbot)
    · simpa only [closeBridge, dite_eq_right hf, BGW.Skorokhod.coe_mk] using
        (tendsto_const_nhds : Tendsto (fun _ : Set.Icc (0 : ℝ) 1 => (0 : ℝ))
          (𝓝[<] top) (𝓝 0))
  have hclosed : ContinuousWithinAt (closeBridge f) (Iic top) top := by
    simpa only [Iio_insert] using hleft.insert
  exact hclosed.leftLim_eq.trans (closeBridge_one f)

/-- **Terminal pinning** (and start): almost surely `X_0 = 0`, `X_1 = 0` and `X_{1-} = 0`. -/
theorem stableBridgeLaw_endpoints {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f : D 1 ℝ ∂(stableBridgeLaw θ : Measure (D 1 ℝ)),
      f ⟨0, le_rfl, zero_le_one⟩ = 0 ∧ f ⟨1, zero_le_one, le_rfl⟩ = 0 ∧
        Function.leftLim f ⟨1, zero_le_one, le_rfl⟩ = 0 := by
  classical
  have hs : MeasurableSet {f : D 1 ℝ |
      f ⟨0, le_rfl, zero_le_one⟩ = 0 ∧ f ⟨1, zero_le_one, le_rfl⟩ = 0 ∧
        Function.leftLim f ⟨1, zero_le_one, le_rfl⟩ = 0} :=
    ((BGW.Skorokhod.measurable_eval _) (measurableSet_singleton 0)).inter
      (((BGW.Skorokhod.measurable_eval _) (measurableSet_singleton 0)).inter
        ((measurable_leftLim_eval _) (measurableSet_singleton 0)))
  change ∀ᵐ f : D 1 ℝ ∂((bridgeOpenLaw θ : Measure BridgeOpen).map closeBridge),
    f ⟨0, le_rfl, zero_le_one⟩ = 0 ∧ f ⟨1, zero_le_one, le_rfl⟩ = 0 ∧
      Function.leftLim f ⟨1, zero_le_one, le_rfl⟩ = 0
  rw [ae_map_iff measurable_closeBridge.aemeasurable hs]
  filter_upwards [bridgeOpenLaw_ae_zero hθ] with f hf
  refine ⟨?_, closeBridge_one f, closeBridge_leftLim_one f⟩
  by_cases h : f ∈ BridgeOpen.terminalLimit <;> simp [closeBridge, h, hf]

/-- Given terminal pinning of the open law, every closed dyadic prefix has its tilted law. -/
theorem map_restrict_stableBridgeLaw_horizon_of_terminal_limit {θ : ℝ}
    (hθ : 1 < θ ∧ θ ≤ 2)
    (hpin : ∀ᵐ f ∂(bridgeOpenLaw θ : Measure BridgeOpen),
      Tendsto f.eval (𝓝[<] (1 : ℝ)) (𝓝 0)) (n : ℕ) :
    (stableBridgeLaw θ : Measure (D 1 ℝ)).map
        (restrict (bridgeHorizon_lt_one n).le) =
      bridgePrefixLaw θ (bridgeHorizon n) (bridgeHorizon_pos n).le
        (stableProcessLaw θ (bridgeHorizon n) : Measure (D (bridgeHorizon n) ℝ)) := by
  change ((bridgeOpenLaw θ : Measure BridgeOpen).map closeBridge).map
    (restrict (bridgeHorizon_lt_one n).le) = _
  rw [Measure.map_map (measurable_restrict _) measurable_closeBridge]
  have heq : (restrict (bridgeHorizon_lt_one n).le ∘ closeBridge) =ᵐ[
      (bridgeOpenLaw θ : Measure BridgeOpen)] CompatiblePaths.coord n := by
    filter_upwards [hpin] with f hf
    exact restrict_closeBridge hf n
  rw [Measure.map_congr heq]
  exact map_coord_bridgeOpenLaw hθ n

/-- Given terminal pinning of the open law, every strict closed prefix has its tilted law. -/
theorem map_restrict_stableBridgeLaw_of_terminal_limit {θ a : ℝ}
    (hθ : 1 < θ ∧ θ ≤ 2) (ha : 0 < a) (ha1 : a < 1)
    (hpin : ∀ᵐ f ∂(bridgeOpenLaw θ : Measure BridgeOpen),
      Tendsto f.eval (𝓝[<] (1 : ℝ)) (𝓝 0)) :
    (stableBridgeLaw θ : Measure (D 1 ℝ)).map (restrict ha1.le) =
      bridgePrefixLaw θ a ha.le (stableProcessLaw θ a : Measure (D a ℝ)) := by
  obtain ⟨n, hn⟩ := exists_bridgeHorizon_ge ha1
  have hcomp : restrict ha1.le =
      (restrict hn : D (bridgeHorizon n) ℝ → D a ℝ) ∘
        restrict (bridgeHorizon_lt_one n).le := rfl
  rw [hcomp, ← Measure.map_map (measurable_restrict _) (measurable_restrict _),
    map_restrict_stableBridgeLaw_horizon_of_terminal_limit hθ hpin n]
  exact bridgePrefix_consistent hθ ha hn (bridgeHorizon_lt_one n)
    (isStableLevyLaw_stableProcessLaw hθ ha)
    (isStableLevyLaw_stableProcessLaw hθ (bridgeHorizon_pos n))

/-- Prefix identity: for `0 < a < 1`, the restriction to `[0, a]` is the tilted stable law
`w_a · P_a` (`bridgePrefixLaw`, i.e. `withDensity` of `bridgePrefixWeight`). -/
theorem map_restrict_stableBridgeLaw {θ a : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (ha : 0 < a) (ha1 : a < 1) :
    (stableBridgeLaw θ : Measure (D 1 ℝ)).map (restrict ha1.le) =
      bridgePrefixLaw θ a ha.le (stableProcessLaw θ a : Measure (D a ℝ)) := by
  exact map_restrict_stableBridgeLaw_of_terminal_limit hθ ha ha1
    (bridgeOpenLaw_ae_terminal_limit hθ)


end BGW.StableTrees
