/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.HeightTightnessLaw
public import BGW.StableTrees.HeightTightnessPairExt
public import BGW.StableTrees.HeightTightnessInterpolatedFDD
public import BGW.StableTrees.HeightContinuity
import BGW.StableTrees.StableProcessCompactness
import BGW.Skorokhod.Separable
import BGW.Skorokhod.CompleteMetricCompleteness
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.Topology.ContinuousMap.SecondCountableSpace

/-!
# Joint convergence of the forest walk and height

The walk marginal has the sealed CT5 step-path laws and the height marginal has the
tight laws obtained by Arzelà-Ascoli, so the joint path laws are tight. Finite height
observations retain the whole walk and are continuous. The interpolated K09 limits and
the H03 graph identities identify every finite observation law, hence every
subsequential limit. Prokhorov and uniqueness of the limit give convergence of the
whole sequence.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal Classical
open BGW.StableTrees.DiscreteForest BGW.Skorokhod BGW.Probability.RealWalk
open BGW.StableTrees.DiscreteHeightApprox
namespace BGW.StableTrees.HeightTightness

/-- Product tightness of the whole walk and interpolated forest-height paths. -/
theorem isTightMeasureSet_forestPairLaw {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ}
    (h : StableDomain μ θ B) {T : ℝ≥0} (hT : 0 < T) :
    IsTightMeasureSet (Set.range fun n : ℕ =>
      ((offspringSeqLaw μ).map (forestPairPath B n T) :
        Measure (D (T : ℝ) ℝ × C(Set.Icc (0 : ℝ) (T : ℝ), ℝ)))) := by
  let S := Set.range fun n : ℕ => ((offspringSeqLaw μ).map (forestPairPath B n T) :
    Measure (D (T : ℝ) ℝ × C(Set.Icc (0 : ℝ) (T : ℝ), ℝ)))
  have hfst : Measure.fst '' S = Set.range (fun n : ℕ =>
      (stepPathLaw (realOffspringStepLaw μ) (T : ℝ) B n : Measure (D (T : ℝ) ℝ))) := by
    dsimp only [S]
    rw [← Set.range_comp']
    congr 1
    funext n
    exact forestPairLaw_fst μ B n T
  have hsnd : Measure.snd '' S = Set.range (fun n : ℕ =>
      ((offspringSeqLaw μ).map (forestHeightPath B n T) :
        Measure C(Set.Icc (0 : ℝ) (T : ℝ), ℝ))) := by
    dsimp only [S]
    rw [← Set.range_comp']
    congr 1
    funext n
    rw [Measure.snd, ProbabilityMeasure.toMeasure_map,
      Measure.map_map measurable_snd (measurable_forestPairPath B n T)]
    rfl
  apply IsTightMeasureSet.prodMk
  · rw [hfst]
    exact h.isRealStableAttracted.isTightMeasureSet_stepPathLaw hT
  · rw [hsnd]
    exact isTightMeasureSet_forestHeightLaw h T

private theorem measurable_heightGraph (θ : ℝ) (T : ℝ≥0) :
    Measurable (fun f : DLoc => (DLoc.restrict T f, heightPrefix θ T (DLoc.restrict T f))) :=
  (DLoc.measurable_restrict T).prodMk ((measurable_heightPrefix θ T).comp
    (DLoc.measurable_restrict T))

/-- Observing a forest pair gives the interpolated finite-dimensional object. -/
theorem map_forestPair_heightPairEval (μ : PMF ℕ) (B : ℕ → ℝ) (n : ℕ) (T : ℝ≥0)
    {r : ℕ} (t : Fin r → Set.Icc (0 : ℝ) (T : ℝ)) :
    ((offspringSeqLaw μ).map (forestPairPath B n T)).map (heightPairEval T t) =
      (offspringSeqLaw μ).map (interpolatedHeightJoint B n T t) := by
  apply ProbabilityMeasure.toMeasure_injective
  simp only [ProbabilityMeasure.toMeasure_map,
    Measure.map_map (continuous_heightPairEval T t).measurable (measurable_forestPairPath B n T)]
  rfl

/-- The H03 graph has the finite height observations appearing in K09. -/
theorem map_heightGraph_heightPairEval {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (T : ℝ≥0)
    {r : ℕ} (t : Fin r → Set.Icc (0 : ℝ) (T : ℝ)) :
    ((stableLocalLaw θ).map
      (fun f : DLoc => (DLoc.restrict T f, heightPrefix θ T (DLoc.restrict T f)))).map
        (heightPairEval T t) =
      (stableLocalLaw θ).map (heightLimitJoint θ T (fun i => ⟨t i, (t i).property.1⟩)) := by
  apply ProbabilityMeasure.toMeasure_injective
  simp only [ProbabilityMeasure.toMeasure_map,
    Measure.map_map (continuous_heightPairEval T t).measurable (measurable_heightGraph θ T)]
  apply Measure.map_congr
  filter_upwards [ae_all_iff.mpr (fun i => ae_heightPrefix_eval hθ T (t i))] with f hf
  change (DLoc.restrict T f, fun i => heightPrefix θ T (DLoc.restrict T f) (t i)) =
    (DLoc.restrict T f, fun i => height θ f ⟨t i, (t i).property.1⟩)
  exact Prod.ext rfl (funext fun i => hf i)

/-- Every subsequential joint limit is the H03 walk/height graph law. -/
theorem forestPair_subseq_limit_eq_graph {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ}
    (h : StableDomain μ θ B) {T : ℝ≥0} (hT : 0 < T) {q : ℕ → ℕ}
    (hq : Tendsto q atTop atTop)
    {P : ProbabilityMeasure (D (T : ℝ) ℝ × C(Set.Icc (0 : ℝ) (T : ℝ), ℝ))}
    (hP : Tendsto (fun j => (offspringSeqLaw μ).map (forestPairPath B (q j) T))
      atTop (𝓝 P)) :
    P = (stableLocalLaw θ).map
      (fun f : DLoc => (DLoc.restrict T f, heightPrefix θ T (DLoc.restrict T f))) := by
  apply pairLaw_ext_of_height_observations
  intro r t
  have hmap := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
    (fun j => (offspringSeqLaw μ).map (forestPairPath B (q j) T)) P hP
    (continuous_heightPairEval T t)
  simp_rw [map_forestPair_heightPairEval] at hmap
  have hlim := (tendsto_interpolatedHeightJoint h hT t).comp hq
  rw [← map_heightGraph_heightPairEval h.alpha_mem T t] at hlim
  exact tendsto_nhds_unique hmap hlim

/-- **Joint walk/height limit** on every positive horizon: the forest pair converges to the H03
graph of the stable process. -/
theorem tendsto_forestPairLaw {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ} (h : StableDomain μ θ B)
    {T : ℝ≥0} (hT : 0 < T) :
    Tendsto (fun n : ℕ => (offspringSeqLaw μ).map (forestPairPath B n T)) atTop
      (𝓝 ((stableLocalLaw θ).map
        (fun f : DLoc => (DLoc.restrict T f, heightPrefix θ T (DLoc.restrict T f))))) := by
  have htight : IsTightMeasureSet
      {((ν : ProbabilityMeasure (D (T : ℝ) ℝ × C(Set.Icc (0 : ℝ) (T : ℝ), ℝ))) :
        Measure (D (T : ℝ) ℝ × C(Set.Icc (0 : ℝ) (T : ℝ), ℝ))) |
        ν ∈ Set.range (fun n : ℕ => (offspringSeqLaw μ).map (forestPairPath B n T))} := by
    convert isTightMeasureSet_forestPairLaw h hT using 1
    ext ν
    simp
  have hc := isCompact_closure_of_isTightMeasureSet htight
  apply Filter.tendsto_of_subseq_tendsto
  intro q hq
  obtain ⟨P, _, r, hr, hP⟩ := hc.tendsto_subseq
    (fun j => subset_closure (Set.mem_range_self (q j)))
  have heq := forestPair_subseq_limit_eq_graph h hT (hq.comp hr.tendsto_atTop) hP
  exact ⟨r, heq ▸ hP⟩

end BGW.StableTrees.HeightTightness
