/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.ExactContour
public import BGW.StableTrees.Scalar.FiniteVariance
public import BGW.StableTrees.BrownianPair
public import BGW.ContinuumTrees.CodingScaling
public import BGW.MetricMeasure.RootedScaling

/-!
# Finite-variance contours and Brownian tree scaling

The stable norming gives the joint limit `(√2 e, √2 e)`. Rescaling gives Aldous's
height and contour normalization in both contour clocks. Spatial scaling of the
coded Brownian tree preserves its root and probability mass.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace BGW.StableTrees.ExactContour

open BGW.StableTrees.DiscreteForest BGW.StableTrees.TailPair

/-! ### Deterministic norming identities -/

/-- The contour path is linear in the norming sequence. -/
theorem treeContourPath_const_mul (c : ℝ) (B : ℕ → ℝ) (n : ℕ) (T : ℝ≥0)
    (τ : LocallyFinite.Tree) :
    treeContourPath (fun m => c * B m) n T τ = c • treeContourPath B n T τ := by
  rw [treeContourPath, treeContourPath,
    dite_eq_left (continuous_treeContourLin τ), dite_eq_left (continuous_treeContourLin τ)]
  ext s
  change c * B n / n * _ = c * (B n / n * _)
  ring

/-- The height/contour pair is linear in the norming sequence. -/
theorem heightContourPath_const_mul (c : ℝ) (B : ℕ → ℝ) (n : ℕ) (τ : LocallyFinite.Tree) :
    heightContourPath (fun m => c * B m) n τ = c • heightContourPath B n τ := by
  apply Prod.ext
  · change treeHeightPath (fun m => c * B m) n 1 τ = c • treeHeightPath B n 1 τ
    rw [treeHeightPath, treeHeightPath,
      dite_eq_left (continuous_treeHeightLin τ), dite_eq_left (continuous_treeHeightLin τ)]
    ext s
    change c * B n / n * _ = c * (B n / n * _)
    ring
  · exact treeContourPath_const_mul c B n 1 τ

/-- The Aldous norming `(σ/2)√n` is `1/√2` times the stable norming `(σ/√2)√n` of
`Scalar.stableDomain_of_finiteVariance`. -/
theorem finiteVarianceNorming_eq (σ : ℝ) :
    (fun n : ℕ => (σ / 2) * Real.sqrt n) =
      fun n : ℕ => (1 / Real.sqrt 2) * ((σ / Real.sqrt 2) * Real.sqrt n) := by
  funext n
  have hs := Real.mul_self_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hp : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  field_simp
  simp only [pow_two, hs]
  ring

/-- **Coefficient identity for every positive size `z`** (deterministic, so usable with a
random size): the Aldous amplitude is `σ / (2√z)`. -/
theorem finiteVarianceNorming_div (σ : ℝ) {z : ℕ} (hz : 0 < z) :
    (σ / 2) * Real.sqrt z / z = σ / (2 * Real.sqrt z) := by
  have hp : (0 : ℝ) < z := Nat.cast_pos.mpr hz
  have hs := Real.mul_self_sqrt hp.le
  have hr : Real.sqrt z ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hp)
  field_simp
  simp only [pow_two, hs]

/-- For one finite tree of any size `z = t.size`, the Aldous-normed contour path is
`σ / (2√z)` times the sealed paper contour `PlaneTree.paperContourFunction` (`s ↦ C_{2z s}`). -/
theorem treeContourPath_finiteVariance_paper (σ : ℝ) (t : PlaneTree) (s : unitInterval) :
    treeContourPath (fun n => (σ / 2) * Real.sqrt n) t.size 1 t.toLocallyFinite s =
      σ / (2 * Real.sqrt t.size) * t.paperContourFunction s := by
  rw [treeContourPath_eq_paperContourFunction _ t rfl,
    finiteVarianceNorming_div σ t.size_pos]

/-! ### C30: finite-variance exact-size contours -/

/-- **C30, stable normalization** `B₀ n = σ √(n/2)`: the exact-size height and contour converge
jointly to `(√2 e, √2 e)`. -/
theorem tendsto_exactHeightContour_finiteVariance_stable {μ : PMF ℕ}
    (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hfinite : MemLp (fun j : ℕ => (j : ℝ)) 2 μ.toMeasure)
    {q : ℕ → ℕ} (hqtop : Tendsto q atTop atTop)
    (hq : ∀ k, Admissible μ (q k)) :
    let σ := Real.sqrt (∫ z : ℤ, (z : ℝ) ^ 2 ∂stepLaw μ)
    Tendsto (fun k => exactHeightContourLaw μ (fun n => (σ / Real.sqrt 2) * Real.sqrt n)
        (q k) (hq k)) atTop
      (𝓝 (BGW.ContinuumTrees.VervaatBridge.law.map
        (fun e => (Real.sqrt 2 • e, Real.sqrt 2 • e)))) := by
  dsimp only
  have h := tendsto_exactHeightContourLaw
    (Scalar.stableDomain_of_finiteVariance hc hne hfinite) hqtop hq
  rwa [BrownianIdentification.excLaw_two_map_diag] at h

private theorem treeHeightPath_const_mul (c : ℝ) (B : ℕ → ℝ) (n : ℕ) (T : ℝ≥0)
    (τ : LocallyFinite.Tree) :
    treeHeightPath (fun m => c * B m) n T τ = c • treeHeightPath B n T τ := by
  rw [treeHeightPath, treeHeightPath,
    dite_eq_left (continuous_treeHeightLin τ), dite_eq_left (continuous_treeHeightLin τ)]
  ext s
  change c * B n / n * _ = c * (B n / n * _)
  ring

private theorem heightLibContourPath_const_mul (c : ℝ) (B : ℕ → ℝ) (n : ℕ)
    (τ : LocallyFinite.Tree) :
    heightLibContourPath (fun m => c * B m) n τ = c • heightLibContourPath B n τ := by
  classical
  apply Prod.ext
  · exact treeHeightPath_const_mul c B n 1 τ
  · change (if h : LocallyFinite.FiniteVertices τ then
        (c * B n / n) • (PlaneTree.equivFiniteVertices.symm ⟨τ, h⟩).contourFunction
      else 0) = c • (if h : LocallyFinite.FiniteVertices τ then
        (B n / n) • (PlaneTree.equivFiniteVertices.symm ⟨τ, h⟩).contourFunction
      else 0)
    split
    · simp only [smul_smul, mul_div_assoc]
    · simp only [smul_zero]

private theorem rescale_brownian_limit
    {ν : ℕ → ProbabilityMeasure (C(unitInterval, ℝ) × C(unitInterval, ℝ))}
    (h : Tendsto ν atTop
      (𝓝 (BGW.ContinuumTrees.VervaatBridge.law.map
        (fun e => (Real.sqrt 2 • e, Real.sqrt 2 • e))))) :
    Tendsto (fun k => (ν k).map (fun p => (1 / Real.sqrt 2) • p)) atTop
      (𝓝 (BGW.ContinuumTrees.VervaatBridge.law.map (fun e => (e, e)))) := by
  have hm : Continuous (fun p : C(unitInterval, ℝ) × C(unitInterval, ℝ) =>
      (1 / Real.sqrt 2) • p) := by fun_prop
  have hh := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _ h hm
  have heq : (BGW.ContinuumTrees.VervaatBridge.law.map
      (fun e => (Real.sqrt 2 • e, Real.sqrt 2 • e))).map
      (fun p => (1 / Real.sqrt 2) • p) =
      BGW.ContinuumTrees.VervaatBridge.law.map (fun e => (e, e)) := by
    apply Subtype.ext
    change Measure.map _ (Measure.map _ _) = Measure.map _ _
    rw [Measure.map_map hm.measurable (by fun_prop)]
    congr 1
    funext e
    simp [Prod.smul_mk, smul_smul]
  rwa [heq] at hh

/-- **C30, Aldous normalization, joint form**: with amplitude `σ / (2√n)`, the exact-size
height (time `nt`) and contour (time `2nt`) converge jointly to `(e, e)`. -/
theorem tendsto_exactHeightContour_finiteVariance {μ : PMF ℕ}
    (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hfinite : MemLp (fun j : ℕ => (j : ℝ)) 2 μ.toMeasure)
    {q : ℕ → ℕ} (hqtop : Tendsto q atTop atTop)
    (hq : ∀ k, Admissible μ (q k)) :
    let σ := Real.sqrt (∫ z : ℤ, (z : ℝ) ^ 2 ∂stepLaw μ)
    Tendsto (fun k => exactHeightContourLaw μ (fun n => (σ / 2) * Real.sqrt n) (q k) (hq k))
      atTop (𝓝 (BGW.ContinuumTrees.VervaatBridge.law.map (fun e => (e, e)))) := by
  dsimp only
  have h := rescale_brownian_limit
    (tendsto_exactHeightContour_finiteVariance_stable hc hne hfinite hqtop hq)
  have heq (k : ℕ) :
      (exactHeightContourLaw μ
        (fun n => (Real.sqrt (∫ z : ℤ, (z : ℝ) ^ 2 ∂stepLaw μ) / Real.sqrt 2) *
          Real.sqrt n) (q k) (hq k)).map (fun p => (1 / Real.sqrt 2) • p) =
      exactHeightContourLaw μ
        (fun n => (Real.sqrt (∫ z : ℤ, (z : ℝ) ^ 2 ∂stepLaw μ) / 2) *
          Real.sqrt n) (q k) (hq k) := by
    rw [finiteVarianceNorming_eq]
    apply Subtype.ext
    change Measure.map _ (Measure.map _ _) = Measure.map _ _
    rw [Measure.map_map
      (g := fun p : C(unitInterval, ℝ) × C(unitInterval, ℝ) => (1 / Real.sqrt 2) • p)
      (by fun_prop)
      (measurable_heightContourPath _ _)]
    congr 1
    funext τ
    exact (heightContourPath_const_mul _ _ _ τ).symm
  simpa only [heq] using h

/-- **C30 (Aldous's theorem along admissible sizes)**: `(σ / (2√n)) C_{2nt} ⇒ e`, the normalized
Brownian excursion. -/
theorem tendsto_exactContour_finiteVariance {μ : PMF ℕ}
    (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hfinite : MemLp (fun j : ℕ => (j : ℝ)) 2 μ.toMeasure)
    {q : ℕ → ℕ} (hqtop : Tendsto q atTop atTop)
    (hq : ∀ k, Admissible μ (q k)) :
    let σ := Real.sqrt (∫ z : ℤ, (z : ℝ) ^ 2 ∂stepLaw μ)
    Tendsto (fun k => (exactTreeLaw μ (q k)).map
      (treeContourPath (fun n => (σ / 2) * Real.sqrt n) (q k) 1))
      atTop (𝓝 BGW.ContinuumTrees.VervaatBridge.law) := by
  dsimp only
  have h := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _
    (tendsto_exactHeightContour_finiteVariance hc hne hfinite hqtop hq) continuous_snd
  have heq (B : ℕ → ℝ) (n : ℕ) (hn : Admissible μ n) :
      (exactHeightContourLaw μ B n hn).map Prod.snd =
      (exactTreeLaw μ n).map (treeContourPath B n 1) := by
    apply Subtype.ext
    exact Measure.map_map measurable_snd (measurable_heightContourPath B n)
  have hlim : (BGW.ContinuumTrees.VervaatBridge.law.map (fun e => (e, e))).map
      Prod.snd = BGW.ContinuumTrees.VervaatBridge.law := by
    apply Subtype.ext
    change Measure.map _ (Measure.map _ _) = _
    rw [Measure.map_map (f := fun e : C(unitInterval, ℝ) => (e, e))
      measurable_snd (by fun_prop)]
    exact Measure.map_id
  let b : ℕ → ℝ := fun n =>
    (Real.sqrt (∫ z : ℤ, (z : ℝ) ^ 2 ∂stepLaw μ) / 2) * Real.sqrt n
  change Tendsto (fun k => (exactHeightContourLaw μ b (q k) (hq k)).map Prod.snd) atTop _ at h
  change Tendsto (fun k => (exactTreeLaw μ (q k)).map (treeContourPath b (q k) 1)) atTop _
  have hseq :
      (fun k => (exactHeightContourLaw μ b (q k) (hq k)).map Prod.snd) =
        (fun k => (exactTreeLaw μ (q k)).map (treeContourPath b (q k) 1)) :=
    funext fun k => heq b (q k) (hq k)
  rw [hseq, hlim] at h
  exact h

/-- **C30 in the library contour clock** (`s ↦ C(2(z-1)s)`): the same joint limit `(e, e)`. -/
theorem tendsto_exactHeightLibContour_finiteVariance {μ : PMF ℕ}
    (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hfinite : MemLp (fun j : ℕ => (j : ℝ)) 2 μ.toMeasure)
    {q : ℕ → ℕ} (hqtop : Tendsto q atTop atTop)
    (hq : ∀ k, Admissible μ (q k)) :
    let σ := Real.sqrt (∫ z : ℤ, (z : ℝ) ^ 2 ∂stepLaw μ)
    Tendsto (fun k => exactHeightLibContourLaw μ (fun n => (σ / 2) * Real.sqrt n) (q k) (hq k))
      atTop (𝓝 (BGW.ContinuumTrees.VervaatBridge.law.map (fun e => (e, e)))) := by
  dsimp only
  have h := tendsto_exactHeightLibContourLaw
    (Scalar.stableDomain_of_finiteVariance hc hne hfinite) hqtop hq
  rw [BrownianIdentification.excLaw_two_map_diag] at h
  have hh := rescale_brownian_limit h
  have heq (k : ℕ) :
      (exactHeightLibContourLaw μ
        (fun n => (Real.sqrt (∫ z : ℤ, (z : ℝ) ^ 2 ∂stepLaw μ) / Real.sqrt 2) *
          Real.sqrt n) (q k) (hq k)).map (fun p => (1 / Real.sqrt 2) • p) =
      exactHeightLibContourLaw μ
        (fun n => (Real.sqrt (∫ z : ℤ, (z : ℝ) ^ 2 ∂stepLaw μ) / 2) *
          Real.sqrt n) (q k) (hq k) := by
    rw [finiteVarianceNorming_eq]
    apply Subtype.ext
    change Measure.map _ (Measure.map _ _) = Measure.map _ _
    rw [Measure.map_map
      (g := fun p : C(unitInterval, ℝ) × C(unitInterval, ℝ) => (1 / Real.sqrt 2) • p)
      (by fun_prop)
      (measurable_heightLibContourPath _ _)]
    congr 1
    funext τ
    exact (heightLibContourPath_const_mul _ _ _ τ).symm
  simpa only [heq] using hh

end BGW.StableTrees.ExactContour

namespace BGW.StableTrees.BrownianIdentification

/-! ### Deterministic CRT scaling and the `θ = 2` tree law -/

/-- **Deterministic CRT scaling** `T_{√2 e} = (1/√2) T_{2e}`: spatial scaling by `1/√2`, with
unchanged root and probability mass. -/
theorem rootedMeasuredGHSpace_sqrt_two_smul (hpos : 0 < 1 / Real.sqrt 2)
    (e : C(unitInterval, ℝ)) :
    BGW.ContinuumTrees.Coding.rootedMeasuredGHSpace (Real.sqrt 2 • e) =
      BGW.MetricMeasure.RootedMeasuredGHSpace.scale (1 / Real.sqrt 2) hpos
        (BGW.ContinuumTrees.Coding.rootedMeasuredGHSpace ((2 : ℝ) • e)) := by
  rw [BGW.ContinuumTrees.Coding.rootedMeasuredGHSpace_smul, smul_smul]
  congr 2
  have hs := Real.mul_self_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hn : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  field_simp
  nlinarith

/-- **The `θ = 2` height-coded tree law**: the tree coded by the excursion height `H^exc` has the
law of Aldous's CRT `T_{2e}` with distances multiplied by `1/√2`. -/
theorem stableTreeLaw_two (hpos : 0 < 1 / Real.sqrt 2) :
    (excLaw 2).map
      (fun p => BGW.ContinuumTrees.Coding.rootedMeasuredGHSpace p.2) =
    BGW.ContinuumTrees.VervaatBridge.treeLaw.map
      (BGW.MetricMeasure.RootedMeasuredGHSpace.scale
        (1 / Real.sqrt 2) hpos) := by
  have hc := BGW.ContinuumTrees.Coding.continuous_rootedMeasuredGHSpace.measurable
  have hs := BGW.MetricMeasure.RootedMeasuredGHSpace.measurable_scale _ hpos
  have hheight :
      Measure.map Prod.snd (excLaw 2 :
        Measure (BGW.Skorokhod.D 1 ℝ × C(unitInterval, ℝ))) =
      Measure.map (fun e => Real.sqrt 2 • e)
        (BGW.ContinuumTrees.VervaatBridge.law : Measure C(unitInterval, ℝ)) :=
    congrArg ProbabilityMeasure.toMeasure excLaw_two_map_snd
  rw [BGW.ContinuumTrees.VervaatBridge.treeLaw_eq_map]
  apply Subtype.ext
  change Measure.map _ _ = Measure.map _ (Measure.map _ _)
  rw [Measure.map_map
    (f := fun e : C(unitInterval, ℝ) =>
      BGW.ContinuumTrees.Coding.rootedMeasuredGHSpace ((2 : ℝ) • e)) hs (by fun_prop)]
  calc
    _ = Measure.map BGW.ContinuumTrees.Coding.rootedMeasuredGHSpace
        (Measure.map Prod.snd (excLaw 2 :
          Measure (BGW.Skorokhod.D 1 ℝ × C(unitInterval, ℝ)))) := by
      exact (Measure.map_map hc measurable_snd).symm
    _ = Measure.map BGW.ContinuumTrees.Coding.rootedMeasuredGHSpace
        (Measure.map (fun e => Real.sqrt 2 • e)
          (BGW.ContinuumTrees.VervaatBridge.law : Measure C(unitInterval, ℝ))) :=
      congrArg (Measure.map BGW.ContinuumTrees.Coding.rootedMeasuredGHSpace) hheight
    _ = _ := by
      rw [Measure.map_map (f := fun e : C(unitInterval, ℝ) => Real.sqrt 2 • e)
        hc (by fun_prop)]
      congr 1
      funext e
      exact rootedMeasuredGHSpace_sqrt_two_smul hpos e

end BGW.StableTrees.BrownianIdentification
