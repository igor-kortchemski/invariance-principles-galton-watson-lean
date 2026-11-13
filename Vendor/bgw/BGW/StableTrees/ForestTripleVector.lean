/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.Skorokhod.ProductPathsVector
public import BGW.StableTrees.ForestTriple

/-!
# Vector-path form of the joint forest convergence

The walk, interpolated height and padded contour are packaged as one càdlàg path with values in
`ℝ × ℝ × ℝ`. The packaging map is continuous, so the joint product-space convergence of the
forest triple implies convergence in law of the vector path by the continuous mapping theorem.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal Classical
open BGW.Skorokhod BGW.StableTrees

namespace BGW.StableTrees.ForestTriple

open BGW.StableTrees.DiscreteForest BGW.StableTrees.ForestContour

/-- A walk/height/contour triple as one path in `D_T(ℝ × ℝ × ℝ)`. -/
noncomputable def tripleVec (T : ℝ≥0)
    (x : D (T : ℝ) ℝ × C(Set.Icc (0 : ℝ) (T : ℝ), ℝ) × C(Set.Icc (0 : ℝ) (T : ℝ), ℝ)) :
    D (T : ℝ) (ℝ × ℝ × ℝ) :=
  prodWithCont x.1 (x.2.1.prodMk x.2.2)

theorem tripleVec_apply (T : ℝ≥0)
    (x : D (T : ℝ) ℝ × C(Set.Icc (0 : ℝ) (T : ℝ), ℝ) × C(Set.Icc (0 : ℝ) (T : ℝ), ℝ))
    (t : Set.Icc (0 : ℝ) (T : ℝ)) :
    tripleVec T x t = (x.1 t, x.2.1 t, x.2.2 t) := rfl

theorem continuous_tripleVec (T : ℝ≥0) : Continuous (tripleVec T) := by
  unfold tripleVec
  have hpair : Continuous (fun x : D (T : ℝ) ℝ × C(Set.Icc (0 : ℝ) (T : ℝ), ℝ) ×
      C(Set.Icc (0 : ℝ) (T : ℝ), ℝ) => x.2.1.prodMk x.2.2) := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    simp only [Function.uncurry_def, ContinuousMap.prod_eval]
    have h1 := (continuous_eval (F := C(Set.Icc (0 : ℝ) (T : ℝ), ℝ))
      (X := Set.Icc (0 : ℝ) (T : ℝ)))
    exact (h1.comp
      ((continuous_fst.comp (continuous_snd.comp continuous_fst)).prodMk continuous_snd)).prodMk
      (h1.comp ((continuous_snd.comp (continuous_snd.comp continuous_fst)).prodMk continuous_snd))
  exact continuous_prodWithCont.comp (continuous_fst.prodMk hpair)

/-- The law of the forest triple as a path in `D_T(ℝ × ℝ × ℝ)`: walk `W_{⌊nt⌋}/B_n`, height
`(B_n/n) H_lin(nt)`, padded contour `(B_n/n) C_lin(2nt)`. -/
noncomputable def forestTripleVecLaw (μ : PMF ℕ) (B : ℕ → ℝ) (n : ℕ) (T : ℝ≥0) :
    ProbabilityMeasure (D (T : ℝ) (ℝ × ℝ × ℝ)) :=
  (forestTripleLaw μ B n T).map (tripleVec T)

/-- The vector C27 limit on `[0,T]`: the path `t ↦ (X_t, H_t, H_t)`. -/
noncomputable def forestTripleVecLimit (θ : ℝ) (T : ℝ≥0) :
    ProbabilityMeasure (D (T : ℝ) (ℝ × ℝ × ℝ)) :=
  (forestTripleLimit θ T).map (tripleVec T)

/-- The vector law is the image of the offspring sequence law by the vector forest path. -/
theorem forestTripleVecLaw_eq_map (μ : PMF ℕ) (B : ℕ → ℝ) (n : ℕ) (T : ℝ≥0) :
    (forestTripleVecLaw μ B n T : Measure (D (T : ℝ) (ℝ × ℝ × ℝ))) =
      (offspringSeqLaw μ : Measure (ℕ → ℕ)).map
        (fun ω => tripleVec T (forestTriplePath B n T ω)) := by
  change (Measure.map (forestTriplePath B n T) _).map (tripleVec T) = _
  rw [Measure.map_map (continuous_tripleVec T).measurable (measurable_forestTriplePath B n T)]
  rfl

/-- The vector limit is the image of the stable process law on `[0,T]` by
`g ↦ (g_t, H_t, H_t)_t`. -/
theorem forestTripleVecLimit_eq {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (T : ℝ≥0) :
    (forestTripleVecLimit θ T : Measure (D (T : ℝ) (ℝ × ℝ × ℝ))) =
      (stableProcessLaw θ (T : ℝ) : Measure (D (T : ℝ) ℝ)).map
        (fun g => tripleVec T (g, heightPrefix θ T g, heightPrefix θ T g)) := by
  change ((forestTripleLimit θ T : Measure _).map (tripleVec T)) = _
  rw [forestTripleLimit_eq_map_stableProcessLaw hθ T]
  have hmeas : Measurable (fun g : D (T : ℝ) ℝ =>
      (g, heightPrefix θ T g, heightPrefix θ T g)) :=
    measurable_id.prodMk ((measurable_heightPrefix θ T).prodMk (measurable_heightPrefix θ T))
  rw [Measure.map_map (continuous_tripleVec T).measurable hmeas]
  rfl

/-- **C27, vector-path form (Duquesne-Le Gall, Corollary 2.5.1), every positive horizon**: the
rescaled walk, interpolated height and padded contour of the iid BGW forest, as one path in
`D_T(ℝ × ℝ × ℝ)`, converge in law to `(X, H, H)` on `[0,T]`. -/
theorem tendsto_forestTripleVecLaw {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ} (h : StableDomain μ θ B)
    {T : ℝ≥0} (hT : 0 < T) :
    Tendsto (fun n : ℕ => forestTripleVecLaw μ B n T) atTop (𝓝 (forestTripleVecLimit θ T)) :=
  ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _
    (tendsto_forestTripleLaw h hT) (continuous_tripleVec T)

end BGW.StableTrees.ForestTriple
