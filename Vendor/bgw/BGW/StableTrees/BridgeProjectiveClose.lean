/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.BridgeProjectiveOpen
import BGW.Skorokhod.MeasurableExtrema

/-!
# Measurable closure of open bridge paths

The full terminal-limit event is measurable. On that event, adding the terminal value zero
preserves the càdlàg property.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open BGW.Skorokhod

namespace BGW.StableTrees

/-- The terminal-limit event: `f(t) → 0` as `t ↑ 1` (full path limit, not convergence in
probability of `X_t`). -/
def BridgeOpen.terminalLimit : Set BridgeOpen :=
  {f | Tendsto f.eval (𝓝[<] (1 : ℝ)) (𝓝 0)}

private theorem measurableSet_coord_tail_bound (n m : ℕ) (r : ℝ) :
    MeasurableSet {f : BridgeOpen | ∀ t : Set.Icc (0 : ℝ) (bridgeHorizon m),
      bridgeHorizon n < (t : ℝ) → |f.1 m t| ≤ r} := by
  let J : Set (Set.Icc (0 : ℝ) (bridgeHorizon m)) :=
    {t | bridgeHorizon n < (t : ℝ)}
  have hJ : J.OrdConnected := by
    constructor
    intro a ha b _ u hu
    change bridgeHorizon n < (a : ℝ) at ha
    exact ha.trans_le hu.1
  obtain ⟨K, hKc, hK⟩ := exists_countable_detecting_times hJ
  let : Countable K := hKc
  have heq : {f : BridgeOpen | ∀ t : Set.Icc (0 : ℝ) (bridgeHorizon m),
      bridgeHorizon n < (t : ℝ) → |f.1 m t| ≤ r} =
      ⋂ q : K, {f : BridgeOpen | |f.1 m q.val.val| ≤ r} := by
    ext f
    simp only [mem_ofPred_eq, mem_iInter]
    constructor
    · intro h q
      exact h q.val.val q.val.property
    · intro h t ht
      by_contra! hbad
      obtain ⟨q, hq, hbadq⟩ := hK ℝ (f.1 m) {x | r < |x|}
        (isOpen_lt continuous_const continuous_abs) ⟨t, ht⟩ hbad
      exact not_lt_of_ge (h ⟨q, hq⟩) hbadq
  rw [heq]
  exact MeasurableSet.iInter fun q => measurableSet_le
    (continuous_abs.measurable.comp ((BGW.Skorokhod.measurable_eval q.val.val).comp
      (CompatiblePaths.measurable_coord bridgeHorizon strictMono_bridgeHorizon m)))
    measurable_const

private theorem terminalLimit_iff_bounds (f : BridgeOpen) :
    f ∈ BridgeOpen.terminalLimit ↔ ∀ k : ℕ, ∃ n : ℕ, ∀ m : ℕ,
      ∀ t : Set.Icc (0 : ℝ) (bridgeHorizon m),
        bridgeHorizon n < (t : ℝ) → |f.1 m t| ≤ 1 / (k + 1 : ℝ) := by
  constructor
  · intro hf k
    have hr : 0 < 1 / (k + 1 : ℝ) := by positivity
    have hev := (Metric.tendsto_nhds.mp hf) _ hr
    obtain ⟨b, hb, hbound⟩ := (nhdsLT_basis (1 : ℝ)).mem_iff.mp hev
    obtain ⟨n, hn⟩ := exists_bridgeHorizon_ge hb
    refine ⟨n, fun m t ht => ?_⟩
    have hval := hbound ⟨hn.trans_lt ht, t.property.2.trans_lt (bridgeHorizon_lt_one m)⟩
    have hv : dist (f.eval t) 0 < 1 / (k + 1 : ℝ) := hval
    rw [BridgeOpen.eval_eq_coord f m t, Real.dist_eq, sub_zero] at hv
    exact hv.le
  · intro hf
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
    obtain ⟨n, hn⟩ := hf k
    filter_upwards [Ioo_mem_nhdsLT (bridgeHorizon_lt_one n)] with t ht
    obtain ⟨m, hm⟩ := exists_bridgeHorizon_ge ht.2
    have ht0 : 0 ≤ t := (bridgeHorizon_pos n).le.trans ht.1.le
    have hval := hn m ⟨t, ht0, hm⟩ ht.1
    have heval := BridgeOpen.eval_eq_coord f m ⟨t, ht0, hm⟩
    simpa only [Real.dist_eq, sub_zero, heval] using hval.trans_lt hk

/-- The full terminal-limit event is measurable. -/
theorem BridgeOpen.measurableSet_terminalLimit : MeasurableSet BridgeOpen.terminalLimit := by
  have heq : BridgeOpen.terminalLimit = ⋂ k : ℕ, ⋃ n : ℕ, ⋂ m : ℕ,
      {f : BridgeOpen | ∀ t : Set.Icc (0 : ℝ) (bridgeHorizon m),
        bridgeHorizon n < (t : ℝ) → |f.1 m t| ≤ 1 / (k + 1 : ℝ)} := by
    ext f
    simp only [mem_iInter, mem_iUnion, mem_ofPred_eq]
    exact terminalLimit_iff_bounds f
  rw [heq]
  exact MeasurableSet.iInter fun k => MeasurableSet.iUnion fun n =>
    MeasurableSet.iInter fun m => measurableSet_coord_tail_bound n m (1 / (k + 1 : ℝ))

private theorem exists_bridgeHorizon_gt {t : ℝ} (ht : t < 1) :
    ∃ n, t < bridgeHorizon n := by
  obtain ⟨n, hn⟩ := exists_bridgeHorizon_ge ht
  exact ⟨n + 1, hn.trans_lt (strictMono_bridgeHorizon (Nat.lt_succ_self n))⟩

private theorem closeFun_eq_extendConst (f : BridgeOpen) (n : ℕ)
    (t : Set.Icc (0 : ℝ) 1) (ht : (t : ℝ) ≤ bridgeHorizon n) :
    (if (t : ℝ) < 1 then f.eval t else 0) =
      extendConst (bridgeHorizon_pos n).le (bridgeHorizon_lt_one n).le (f.1 n) t := by
  rw [ite_eq_left (ht.trans_lt (bridgeHorizon_lt_one n))]
  simpa only [extendConst, coe_mk, min_eq_left ht] using
    BridgeOpen.eval_eq_coord f n ⟨t, t.property.1, ht⟩

/-- On the terminal-limit event, extending an open path by `0` at time `1` gives a càdlàg path on
`[0, 1]`. -/
theorem isCadlag_closeFun {f : BridgeOpen} (h : f ∈ BridgeOpen.terminalLimit) :
    IsCadlag (fun t : Set.Icc (0 : ℝ) 1 => if (t : ℝ) < 1 then f.eval t else 0) := by
  let g : Set.Icc (0 : ℝ) 1 → ℝ := fun t => if (t : ℝ) < 1 then f.eval t else 0
  have hlocal (t : Set.Icc (0 : ℝ) 1) (ht : (t : ℝ) < 1) :
      ∃ e : D 1 ℝ, g =ᶠ[𝓝 t] e ∧ g t = e t := by
    obtain ⟨n, hn⟩ := exists_bridgeHorizon_gt ht
    refine ⟨extendConst (bridgeHorizon_pos n).le (bridgeHorizon_lt_one n).le (f.1 n),
      ?_, closeFun_eq_extendConst f n t hn.le⟩
    have hev : ∀ᶠ u : Set.Icc (0 : ℝ) 1 in 𝓝 t, (u : ℝ) < bridgeHorizon n :=
      (continuous_subtype_val.tendsto t).eventually (eventually_lt_nhds hn)
    filter_upwards [hev] with u hu
    exact closeFun_eq_extendConst f n u hu.le
  constructor
  · intro t
    by_cases ht : (t : ℝ) < 1
    · obtain ⟨e, he, het⟩ := hlocal t ht
      change Tendsto g (𝓝[>] t) (𝓝 (g t))
      rw [het]
      exact (tendsto_congr' (he.filter_mono nhdsWithin_le_nhds)).2
        ((isCadlag e).isRightContinuous t)
    · have hempty : Set.Ioi t = ∅ := by
        ext u
        simp only [mem_Ioi, mem_empty_iff_false, iff_false]
        exact not_lt_of_ge (show u ≤ t from by
          change (u : ℝ) ≤ (t : ℝ)
          exact le_trans u.property.2 (le_of_not_gt ht))
      simp only [ContinuousWithinAt, hempty, nhdsWithin_empty]
      exact tendsto_bot
  · intro t
    by_cases ht : (t : ℝ) < 1
    · obtain ⟨e, he, _⟩ := hlocal t ht
      obtain ⟨l, hl⟩ := (isCadlag e).tendsto_nhdsLT t
      exact ⟨l, (tendsto_congr' (he.filter_mono nhdsWithin_le_nhds)).2 hl⟩
    · have ht1 : (t : ℝ) = 1 := le_antisymm t.property.2 (le_of_not_gt ht)
      have hcoe : Tendsto (fun u : Set.Icc (0 : ℝ) 1 => (u : ℝ))
          (𝓝[<] t) (𝓝[<] (1 : ℝ)) := by
        apply tendsto_nhdsWithin_iff.mpr
        refine ⟨?_, ?_⟩
        · have hc : Tendsto (fun u : Set.Icc (0 : ℝ) 1 => (u : ℝ))
              (𝓝[<] t) (𝓝 (t : ℝ)) :=
            continuous_subtype_val.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
          simpa only [ht1] using hc
        · filter_upwards [self_mem_nhdsWithin] with u hu
          change (u : ℝ) < 1
          change (u : ℝ) < (t : ℝ) at hu
          linarith
      refine ⟨0, ?_⟩
      have heq : g =ᶠ[𝓝[<] t] fun u => f.eval u := by
        filter_upwards [self_mem_nhdsWithin] with u hu
        have hu1 : (u : ℝ) < 1 := by
          change (u : ℝ) < (t : ℝ) at hu
          linarith
        exact ite_eq_left hu1
      exact (tendsto_congr' heq).2 (h.comp hcoe)

open Classical in
/-- Closing the bridge: extend an open path by the value `0` at time `1` on the terminal-limit
event; the zero path on its complement. -/
noncomputable def closeBridge (f : BridgeOpen) : D 1 ℝ :=
  if h : f ∈ BridgeOpen.terminalLimit then
    ⟨fun t => if (t : ℝ) < 1 then f.eval t else 0, isCadlag_closeFun h⟩
  else ⟨fun _ => 0, IsCadlag.const⟩

/-- Closing is measurable (D 1 ℝ carries its Borel σ-algebra, generated by evaluations). -/
theorem measurable_closeBridge : Measurable closeBridge := by
  classical
  have hEval (t : Set.Icc (0 : ℝ) 1) : Measurable (fun f => closeBridge f t) := by
    have heq : (fun f => closeBridge f t) = fun f : BridgeOpen =>
        if f ∈ BridgeOpen.terminalLimit then (if (t : ℝ) < 1 then f.eval t else 0) else 0 := by
      funext f
      by_cases h : f ∈ BridgeOpen.terminalLimit <;> simp [closeBridge, h]
    rw [heq]
    apply Measurable.ite BridgeOpen.measurableSet_terminalLimit
    · split_ifs
      · exact BridgeOpen.measurable_eval t
      · exact measurable_const
    · exact measurable_const
  rw [measurable_iff_comap_le]
  change MeasurableSpace.comap closeBridge
      (inferInstance : MeasurableSpace (D 1 ℝ)) ≤
    (inferInstance : MeasurableSpace BridgeOpen)
  rw [measurableSpace_eq_iSup_comap_eval (T := 1) (E := ℝ) (S := Set.univ)
    dense_univ zero_le_one (by simp)]
  simp only [MeasurableSpace.comap_iSup, iSup_le_iff, MeasurableSpace.comap_comp,
    Function.comp_def]
  intro t _
  exact (hEval t).comap_le

/-- On the terminal-limit event, the closed path restricts to the `n`-th coordinate. -/
theorem restrict_closeBridge {f : BridgeOpen} (hf : f ∈ BridgeOpen.terminalLimit) (n : ℕ) :
    restrict (bridgeHorizon_lt_one n).le (closeBridge f) = f.1 n := by
  classical
  ext t
  simp only [BGW.Skorokhod.restrict, closeBridge, dite_eq_left hf, coe_mk]
  rw [ite_eq_left (t.property.2.trans_lt (bridgeHorizon_lt_one n))]
  exact BridgeOpen.eval_eq_coord f n t

/-- **The stable bridge law on `D 1 ℝ`** (bridge from `0` to `0`): image of the open law under
`closeBridge`. Junk value: image of the junk open law (a Dirac mass at the zero path). -/
noncomputable def stableBridgeLaw (θ : ℝ) : ProbabilityMeasure (D 1 ℝ) :=
  (bridgeOpenLaw θ).map closeBridge

end BGW.StableTrees
