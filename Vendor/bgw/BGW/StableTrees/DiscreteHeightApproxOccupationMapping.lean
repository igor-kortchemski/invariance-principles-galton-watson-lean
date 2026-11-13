/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.DiscreteHeightApproxJoint
public import BGW.StableTrees.DiscreteHeightApproxOccupationContinuity
import BGW.Probability.WeakConvergence
import BGW.StableTrees.StableProcessLaw

/-!
# Continuous mapping for fixed-band occupations

Outside the countable union of boundary levels, the finite-path occupation map
is continuous almost surely under the stable process law.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal Classical
open BGW.Skorokhod BGW.StableTrees.DiscreteForest BGW.Probability.RealWalk

namespace BGW.StableTrees.DiscreteHeightApprox

/-- Pair a finite path with its exact Lebesgue occupations at the chosen times. -/
noncomputable def finiteOccupationJoint (T : ℝ≥0) (ε : ℝ) {r : ℕ} (t : Fin r → ℝ≥0)
    (f : D (T : ℝ) ℝ) : D (T : ℝ) ℝ × (Fin r → ℝ) :=
  (f, fun i => finiteHeightApprox T (t i) ε f)

/-- The finite-path joint occupation map is measurable. -/
theorem measurable_finiteOccupationJoint (T : ℝ≥0) (ε : ℝ) {r : ℕ} (t : Fin r → ℝ≥0) :
    Measurable (finiteOccupationJoint T ε t) :=
  measurable_id.prodMk (Measurable.of_eval fun i => measurable_finiteHeightApprox T (t i) ε)

private theorem finiteGap_restrict_eq (T t : ℝ≥0) (ht : t ≤ T) (f : DLoc) {s : ℝ}
    (hs : s ∈ Icc 0 (t : ℝ)) :
    finiteGap T t (DLoc.restrict T f) s = f.1 s.toNNReal - futureInf f t s.toNNReal := by
  have he (u : ℝ≥0) (hu : u ≤ t) :
      (extendFinitePath T (DLoc.restrict T f)).1 u = f.1 u := by
    rw [extendFinitePath_apply T _ u (hu.trans ht)]
    rfl
  have hst : s.toNNReal ≤ t := Real.toNNReal_le_iff_le_coe.mpr hs.2
  rw [finiteGap, he _ hst, futureInf_eq_of_prefix he]

private theorem ae_continuousAt_finiteOccupationJoint {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    {T : ℝ≥0} (hT : 0 < T) {r : ℕ} (t : Fin r → ℝ≥0) (ht : ∀ i, t i ≤ T)
    {ε : ℝ} (hε : 0 < ε)
    (hexc : ∀ i, ε ∉ {ε : ℝ | 0 < ε ∧ 0 < (stableLocalLaw θ : Measure DLoc)
      {f | 0 < volume {s : ℝ | 0 ≤ s ∧ s ≤ (t i : ℝ) ∧
        f.1 s.toNNReal = futureInf f (t i) s.toNNReal + ε}}}) :
    ∀ᵐ f : D (T : ℝ) ℝ ∂(stableProcessLaw θ (T : ℝ) : Measure (D (T : ℝ) ℝ)),
      ContinuousAt (finiteOccupationJoint T ε t) f := by
  rw [← map_restrict_stableLocalLaw hθ hT]
  apply (ae_map_iff (DLoc.measurable_restrict T).aemeasurable
    (measurableSet_of_continuousAt (finiteOccupationJoint T ε t))).mpr
  have hboundary (i : Fin r) : ∀ᵐ f : DLoc ∂(stableLocalLaw θ : Measure DLoc),
      volume {s : ℝ | 0 ≤ s ∧ s ≤ (t i : ℝ) ∧
        f.1 s.toNNReal = futureInf f (t i) s.toNNReal + ε} = 0 := by
    have hz : (stableLocalLaw θ : Measure DLoc)
        {f | 0 < volume {s : ℝ | 0 ≤ s ∧ s ≤ (t i : ℝ) ∧
          f.1 s.toNNReal = futureInf f (t i) s.toNNReal + ε}} = 0 := by
      exact le_antisymm (le_of_not_gt (fun hh => hexc i ⟨hε, hh⟩)) bot_le
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hz] with f hf
    exact le_antisymm (le_of_not_gt hf) bot_le
  filter_upwards [ae_all_iff.mpr hboundary,
    ae_all_iff.mpr (fun i => ae_continuousAt_stableLocalLaw hθ (t i))] with f hb hc
  apply continuousAt_id.prodMk
  apply continuousAt_pi.mpr
  intro i
  have hcont : ContinuousAt (DLoc.restrict T f) ⟨t i, (t i).2, ht i⟩ := by
    have hinc : Continuous (fun u : Icc (0 : ℝ) (T : ℝ) => (⟨u, u.2.1⟩ : ℝ≥0)) :=
      Continuous.subtype_mk continuous_subtype_val _
    have hci : ContinuousAt f.1 (t i) := hc i
    exact ContinuousAt.comp (f := fun u : Icc (0 : ℝ) (T : ℝ) =>
      (⟨u, u.2.1⟩ : ℝ≥0)) (g := f.1) hci hinc.continuousAt
  apply continuousAt_finiteHeightApprox T (t i) (ht i) ε (Or.inr hcont)
  have hset : {s : ℝ | s ∈ Icc 0 (t i : ℝ) ∧ finiteGap T (t i) (DLoc.restrict T f) s = ε} =
      {s : ℝ | 0 ≤ s ∧ s ≤ (t i : ℝ) ∧
        f.1 s.toNNReal = futureInf f (t i) s.toNNReal + ε} := by
    ext s
    by_cases hs : s ∈ Icc 0 (t i : ℝ)
    · rw [mem_ofPred_eq, finiteGap_restrict_eq T (t i) (ht i) f hs]
      simp only [hs, true_and, mem_ofPred_eq, mem_Icc.mp hs, true_and]
      constructor <;> intro hh <;> linarith only [hh]
    · simp only [mem_ofPred_eq, hs, false_and]
      tauto
  rw [hset]
  exact hb i

/-- Exact finite-path occupations converge jointly with the walk outside countably many bands. -/
theorem tendsto_joint_finiteOccupation {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ}
    (h : StableDomain μ θ B) {T : ℝ≥0} (hT : 0 < T) {r : ℕ} (t : Fin r → ℝ≥0)
    (ht : ∀ i, t i ≤ T) :
    ∃ Exc : Set ℝ, Exc.Countable ∧ ∀ ε : ℝ, 0 < ε → ε ∉ Exc →
      Tendsto (fun n : ℕ => (offspringSeqLaw μ).map
        (fun ω => finiteOccupationJoint T ε t (forestWalkPath B n T ω))) atTop
          (𝓝 ((stableLocalLaw θ).map (continuumJoint T ε t))) := by
  let Exc : Set ℝ := ⋃ i : Fin r, {ε : ℝ | 0 < ε ∧ 0 < (stableLocalLaw θ : Measure DLoc)
    {f | 0 < volume {s : ℝ | 0 ≤ s ∧ s ≤ (t i : ℝ) ∧
      f.1 s.toNNReal = futureInf f (t i) s.toNNReal + ε}}}
  refine ⟨Exc, Set.countable_iUnion (fun i => countable_boundaryLevels h.alpha_mem (t i)), ?_⟩
  intro ε hε hexc
  have he (i : Fin r) : ε ∉ {ε : ℝ | 0 < ε ∧ 0 < (stableLocalLaw θ : Measure DLoc)
      {f | 0 < volume {s : ℝ | 0 ≤ s ∧ s ≤ (t i : ℝ) ∧
        f.1 s.toNNReal = futureInf f (t i) s.toNNReal + ε}}} :=
    fun hh => hexc (Set.mem_iUnion.mpr ⟨i, hh⟩)
  have hc := BGW.Probability.tendsto_map_of_ae_continuousAt (h.tendsto_stepPathLaw hT)
    (fun _ => (measurable_finiteOccupationJoint T ε t).aemeasurable)
    (ae_continuousAt_finiteOccupationJoint h.alpha_mem hT t ht hε he)
  have hmap (n : ℕ) : (offspringSeqLaw μ).map
      (fun ω => finiteOccupationJoint T ε t (forestWalkPath B n T ω)) =
      (stepPathLaw (realOffspringStepLaw μ) (T : ℝ) B n).map (finiteOccupationJoint T ε t) := by
    apply Subtype.ext
    have hlaw := forestPairLaw_fst μ B n T
    change ((offspringSeqLaw μ).toMeasure.map (forestPairPath B n T)).map Prod.fst = _ at hlaw
    rw [Measure.map_map measurable_fst (measurable_forestPairPath B n T)] at hlaw
    change (offspringSeqLaw μ).toMeasure.map _ =
      (stepPathLaw (realOffspringStepLaw μ) (T : ℝ) B n).toMeasure.map _
    rw [← hlaw, Measure.map_map (measurable_finiteOccupationJoint T ε t)
      (measurable_fst.comp (measurable_forestPairPath B n T))]
    rfl
  have hlimit : (stableProcessLaw θ (T : ℝ)).map (finiteOccupationJoint T ε t) =
      (stableLocalLaw θ).map (continuumJoint T ε t) := by
    apply Subtype.ext
    change (stableProcessLaw θ (T : ℝ)).toMeasure.map _ =
      (stableLocalLaw θ).toMeasure.map _
    rw [← map_restrict_stableLocalLaw h.alpha_mem hT,
      Measure.map_map (measurable_finiteOccupationJoint T ε t) (DLoc.measurable_restrict T)]
    congr 1
    funext f
    change (DLoc.restrict T f, fun i => finiteHeightApprox T (t i) ε (DLoc.restrict T f)) =
      (DLoc.restrict T f, fun i => heightApprox ε f (t i))
    apply Prod.ext
    · rfl
    · funext i
      exact finiteHeightApprox_restrict T (t i) (ht i) ε f
  simp only [hmap]
  convert hc using 1
  · rfl
  · exact congrArg nhds hlimit.symm

end BGW.StableTrees.DiscreteHeightApprox
