/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.DiscreteHeightApproxTwoLimit
public import BGW.StableTrees.HeightProcess

/-!
# Joint walk and height observables

Discrete and continuum joint observables are measurable. Exceptional boundary
levels are countable by disjointness of their level sets in path-time product measure.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal Classical
open BGW.StableTrees.DiscreteForest BGW.Skorokhod

namespace BGW.StableTrees.DiscreteHeightApprox

/-- The discrete joint object: the rescaled walk path and the `ε`-occupations at times `t`. -/
noncomputable def discreteJoint (B : ℕ → ℝ) (n : ℕ) (T : ℝ≥0) (ε : ℝ) {r : ℕ} (t : Fin r → ℝ≥0)
    (ω : ℕ → ℕ) : D (T : ℝ) ℝ × (Fin r → ℝ) :=
  (forestWalkPath B n T ω, fun i => discreteOccupation B n ε ω (t i))

/-- The continuum joint object: the restricted path and `heightApprox ε` at times `t`. -/
noncomputable def continuumJoint (T : ℝ≥0) (ε : ℝ) {r : ℕ} (t : Fin r → ℝ≥0)
    (f : DLoc) : D (T : ℝ) ℝ × (Fin r → ℝ) :=
  (DLoc.restrict T f, fun i => heightApprox ε f (t i))

/-- The discrete joint walk and occupation observable is measurable. -/
theorem measurable_discreteJoint (B : ℕ → ℝ) (n : ℕ) (T : ℝ≥0) (ε : ℝ) {r : ℕ}
    (t : Fin r → ℝ≥0) : Measurable (discreteJoint B n T ε t) := by
  exact (measurable_forestPairPath B n T).fst.prodMk
    (Measurable.of_eval fun i => measurable_discreteOccupation B n ε (t i))

/-- The continuum joint walk and occupation observable is measurable. -/
theorem measurable_continuumJoint (T : ℝ≥0) (ε : ℝ) {r : ℕ} (t : Fin r → ℝ≥0) :
    Measurable (continuumJoint T ε t) := by
  apply (DLoc.measurable_restrict T).prodMk
  apply Measurable.of_eval
  intro i
  exact measurable_heightApprox_uncurry.comp
    (measurable_const.prodMk (measurable_const.prodMk measurable_id))

/-- The joint object (scaled walk, normalized discrete heights). -/
noncomputable def heightJoint (B : ℕ → ℝ) (n : ℕ) (T : ℝ≥0) {r : ℕ} (t : Fin r → ℝ≥0)
    (ω : ℕ → ℕ) : D (T : ℝ) ℝ × (Fin r → ℝ) :=
  (forestWalkPath B n T ω, fun i => scaledHeight B n ω (t i))

/-- The limit object (restricted path, continuum height `height θ`) at times `t`. -/
noncomputable def heightLimitJoint (θ : ℝ) (T : ℝ≥0) {r : ℕ} (t : Fin r → ℝ≥0) (f : DLoc) :
    D (T : ℝ) ℝ × (Fin r → ℝ) :=
  (DLoc.restrict T f, fun i => height θ f (t i))

/-- The discrete joint walk and height observable is measurable. -/
theorem measurable_heightJoint (B : ℕ → ℝ) (n : ℕ) (T : ℝ≥0) {r : ℕ}
    (t : Fin r → ℝ≥0) : Measurable (heightJoint B n T t) := by
  exact (measurable_forestPairPath B n T).fst.prodMk
    (Measurable.of_eval fun i => measurable_scaledHeight B n (t i))

/-- The continuum joint walk and height observable is measurable. -/
theorem measurable_heightLimitJoint (θ : ℝ) (T : ℝ≥0) {r : ℕ} (t : Fin r → ℝ≥0) :
    Measurable (heightLimitJoint θ T t) := by
  apply (DLoc.measurable_restrict T).prodMk
  apply Measurable.of_eval
  intro i
  exact Measurable.comp
    (g := fun p : ℝ≥0 × DLoc => height θ p.2 p.1)
    (f := fun f : DLoc => (t i, f))
    (measurable_height_uncurry θ) (measurable_const.prodMk measurable_id)

private def boundarySet (t : ℝ≥0) (ε : ℝ) : Set (DLoc × ℝ) :=
  {p | 0 ≤ p.2 ∧ p.2 ≤ (t : ℝ) ∧ p.1.1 p.2.toNNReal = futureInf p.1 t p.2.toNNReal + ε}

private theorem measurableSet_boundarySet (t : ℝ≥0) (ε : ℝ) :
    MeasurableSet (boundarySet t ε) := by
  have hx : Measurable (fun p : DLoc × ℝ => p.1.1 p.2.toNNReal) :=
    Measurable.comp (g := fun q : DLoc × ℝ≥0 => q.1.1 q.2)
      (f := fun p : DLoc × ℝ => (p.1, p.2.toNNReal))
      DLoc.measurable_eval₂
      (measurable_fst.prodMk (measurable_real_toNNReal.comp measurable_snd))
  have hi : Measurable (fun p : DLoc × ℝ => futureInf p.1 t p.2.toNNReal) :=
    Measurable.comp
      (g := fun q : (ℝ≥0 × ℝ≥0) × DLoc => futureInf q.2 q.1.1 q.1.2)
      (f := fun p : DLoc × ℝ => ((t, p.2.toNNReal), p.1))
      measurable_futureInf_uncurry
      ((measurable_const.prodMk (measurable_real_toNNReal.comp measurable_snd)).prodMk
        measurable_fst)
  exact (measurableSet_le measurable_const measurable_snd).inter
    ((measurableSet_le measurable_snd measurable_const).inter
      (measurableSet_eq_fun hx (hi.add measurable_const)))

/-- **Boundary levels are countable** (Fubini): at most countably many `ε > 0` have
`P(Leb{s ≤ t | X_s = I^s_t + ε} > 0) > 0` (the level sets are disjoint in `Ω × [0,t]`). -/
theorem countable_boundaryLevels {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (t : ℝ≥0) :
    {ε : ℝ | 0 < ε ∧ 0 < (stableLocalLaw θ : Measure DLoc)
        {f | 0 < volume {s : ℝ | 0 ≤ s ∧ s ≤ (t : ℝ) ∧
          f.1 s.toNNReal = futureInf f t s.toNNReal + ε}}}.Countable := by
  -- Countability only uses a path law and Fubini; keep the frozen stable-index premise.
  have _hθ := hθ
  let P := (stableLocalLaw θ : Measure DLoc)
  have hdisj : Pairwise (fun ε δ => Disjoint (boundarySet t ε) (boundarySet t δ)) := by
    intro ε δ hne
    apply Set.disjoint_left.mpr
    intro p hp hq
    have he := hp.2.2
    have hd := hq.2.2
    exact hne (by linarith)
  have hc := Measure.countable_meas_pos_of_disjoint_iUnion
    (μ := P.prod (volume : Measure ℝ)) (measurableSet_boundarySet t) hdisj
  apply hc.mono
  intro ε hε
  change 0 < (P.prod volume) (boundarySet t ε)
  rw [Measure.prod_apply (measurableSet_boundarySet t ε)]
  apply (lintegral_pos_iff_support (measurable_measure_prodMk_left
    (measurableSet_boundarySet t ε))).mpr
  have he : Function.support (fun f : DLoc => volume (Prod.mk f ⁻¹' boundarySet t ε)) =
      {f | 0 < volume {s : ℝ | 0 ≤ s ∧ s ≤ (t : ℝ) ∧
        f.1 s.toNNReal = futureInf f t s.toNNReal + ε}} := by
    ext f
    simp only [Function.mem_support, ne_eq, pos_iff_ne_zero]
    rfl
  rw [he]
  exact hε.2

end BGW.StableTrees.DiscreteHeightApprox
