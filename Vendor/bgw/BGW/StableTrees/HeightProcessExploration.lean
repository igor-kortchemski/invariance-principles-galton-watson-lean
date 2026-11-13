/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.HeightProcessTwo
import Mathlib.Probability.Kernel.MeasurableLIntegral

/-!
# Measurability of the exploration measure

The restricted Stieltjes measures form a measurable family of finite measures.
A measurable height map then gives the exploration measure by pushforward.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod
namespace BGW.StableTrees

private noncomputable def heightSource (p : ℝ≥0 × DLoc) : Measure ℝ :=
  (explorationStieltjes p.2 p.1).measure.restrict (Ioc 0 (p.1 : ℝ))

private theorem heightSource_univ (p : ℝ≥0 × DLoc) :
    heightSource p univ = ENNReal.ofReal (p.2.1 p.1 - futureInf p.2 p.1 0) := by
  have he (x : ℝ) : explorationStieltjes p.2 p.1 x = futureInfFun p.2 p.1 x := by
    simp only [explorationStieltjes, dite_eq_left (explorationStieltjes_spec p.2 p.1)]
  rw [heightSource, Measure.restrict_apply_univ, StieltjesFunction.measure_Ioc, he, he]
  simp only [futureInfFun, Real.toNNReal_coe, Real.toNNReal_zero, futureInf_self]

private theorem heightSource_finite (p : ℝ≥0 × DLoc) : IsFiniteMeasure (heightSource p) :=
  ⟨by rw [heightSource_univ]; exact ENNReal.ofReal_lt_top⟩

private theorem measurable_futureInfFun_pair :
    Measurable (fun p : (ℝ≥0 × DLoc) × ℝ => futureInfFun p.1.2 p.1.1 p.2) := by
  exact Measurable.comp
    (g := fun q : (ℝ≥0 × ℝ≥0) × DLoc => futureInf q.2 q.1.1 q.1.2)
    (f := fun p : (ℝ≥0 × DLoc) × ℝ => ((p.1.1, p.2.toNNReal), p.1.2))
    measurable_futureInf_uncurry
    ((measurable_fst.fst.prodMk (measurable_real_toNNReal.comp measurable_snd)).prodMk
      measurable_fst.snd)

private theorem measurable_heightSource : Measurable heightSource := by
  let : ∀ p, IsFiniteMeasure (heightSource p) := heightSource_finite
  apply Measurable.measure_of_isPiSystem (borel_eq_generateFrom_Ioc ℝ) (isPiSystem_Ioc id id)
  · rintro _ ⟨a, b, _hab, rfl⟩
    have he (p : ℝ≥0 × DLoc) : heightSource p (Ioc a b) =
        ENNReal.ofReal (futureInfFun p.2 p.1 (min b (p.1 : ℝ)) -
          futureInfFun p.2 p.1 (max a 0)) := by
      have hF (x : ℝ) : explorationStieltjes p.2 p.1 x = futureInfFun p.2 p.1 x := by
        simp only [explorationStieltjes, dite_eq_left (explorationStieltjes_spec p.2 p.1)]
      rw [heightSource, Measure.restrict_apply measurableSet_Ioc, Ioc_inter_Ioc,
        StieltjesFunction.measure_Ioc, hF, hF]
    simp_rw [he]
    have hm1 : Measurable (fun p : ℝ≥0 × DLoc =>
        futureInfFun p.2 p.1 (min b (p.1 : ℝ))) :=
      Measurable.comp
        (g := fun q : (ℝ≥0 × DLoc) × ℝ => futureInfFun q.1.2 q.1.1 q.2)
        (f := fun p : ℝ≥0 × DLoc => (p, min b (p.1 : ℝ)))
        measurable_futureInfFun_pair
        (measurable_id.prodMk (measurable_const.min
          (measurable_coe_nnreal_real.comp measurable_fst)))
    have hm2 : Measurable (fun p : ℝ≥0 × DLoc => futureInfFun p.2 p.1 (max a 0)) :=
      Measurable.comp
        (g := fun q : (ℝ≥0 × DLoc) × ℝ => futureInfFun q.1.2 q.1.1 q.2)
        (f := fun p : ℝ≥0 × DLoc => (p, max a 0))
        measurable_futureInfFun_pair (measurable_id.prodMk measurable_const)
    exact (hm1.sub hm2).ennreal_ofReal
  · simp_rw [heightSource_univ]
    have hm : Measurable (fun p : ℝ≥0 × DLoc => futureInf p.2 p.1 0) :=
      Measurable.comp
        (g := fun q : (ℝ≥0 × ℝ≥0) × DLoc => futureInf q.2 q.1.1 q.1.2)
        (f := fun p : ℝ≥0 × DLoc => ((p.1, 0), p.2))
        measurable_futureInf_uncurry
        ((measurable_fst.prodMk measurable_const).prodMk measurable_snd)
    exact ((DLoc.measurable_eval₂.comp measurable_swap).sub hm).ennreal_ofReal

/-- `(t, f) ↦ ρ_t(B)` is measurable for measurable `B`. -/
theorem measurable_exploration_apply (θ : ℝ) {B : Set ℝ≥0} (hB : MeasurableSet B) :
    Measurable (fun p : ℝ≥0 × DLoc => exploration θ p.2 p.1 B) := by
  let κ : Kernel (ℝ≥0 × DLoc) ℝ := ⟨heightSource, measurable_heightSource⟩
  let A : Set ((ℝ≥0 × DLoc) × ℝ) :=
    {p | (height θ p.1.2 p.2.toNNReal).toNNReal ∈ B}
  have hA : MeasurableSet A := by
    have hm : Measurable (fun p : (ℝ≥0 × DLoc) × ℝ =>
        height θ p.1.2 p.2.toNNReal) :=
      Measurable.comp (g := fun q : ℝ≥0 × DLoc => height θ q.2 q.1)
        (f := fun p : (ℝ≥0 × DLoc) × ℝ => (p.2.toNNReal, p.1.2))
        (measurable_height_uncurry θ)
        ((measurable_real_toNNReal.comp measurable_snd).prodMk measurable_fst.snd)
    exact (measurable_real_toNNReal.comp hm) hB
  have hm := Kernel.measurable_kernel_prodMk_left_of_finite (κ := κ) hA heightSource_finite
  convert hm using 1
  funext p
  exact Measure.map_apply (measurable_exploration_heightMap θ p.2) hB

end BGW.StableTrees
