/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.DiscreteForest
public import BGW.StableTrees.ForestContour
public import BGW.StableTrees.HeightContinuity
public import BGW.StableTrees.HeightTightnessJoint
public import BGW.Probability.WeakConvergence
public import Mathlib.Topology.ContinuousMap.SecondCountableSpace

import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-!
# Joint convergence of the forest walk, height and contour

On every compact horizon, the padded contour is a uniformly vanishing perturbation of the
interpolated height. Slutsky's theorem therefore upgrades the joint walk/height limit to the
joint walk/height/contour limit, with the same continuous height in the last two coordinates.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal Classical
open BGW.Skorokhod BGW.StableTrees

namespace BGW.StableTrees.ForestTriple

open BGW.StableTrees.DiscreteForest BGW.StableTrees.ForestContour

/-- **Forest triple path** on `[0,T]`: the walk `W_{⌊nt⌋}/B_n`, the interpolated height
`(B_n/n) H_lin(nt)` and the padded contour `(B_n/n) C_lin(2nt)`. -/
noncomputable def forestTriplePath (B : ℕ → ℝ) (n : ℕ) (T : ℝ≥0) (ω : ℕ → ℕ) :
    D (T : ℝ) ℝ × C(Set.Icc (0 : ℝ) (T : ℝ), ℝ) × C(Set.Icc (0 : ℝ) (T : ℝ), ℝ) :=
  (forestWalkPath B n T ω, forestHeightPath B n T ω, forestContourPath B n T ω)

/-- The law of the forest triple path under the iid offspring sequence. -/
noncomputable def forestTripleLaw (μ : PMF ℕ) (B : ℕ → ℝ) (n : ℕ) (T : ℝ≥0) :
    ProbabilityMeasure
      (D (T : ℝ) ℝ × C(Set.Icc (0 : ℝ) (T : ℝ), ℝ) × C(Set.Icc (0 : ℝ) (T : ℝ), ℝ)) :=
  (offspringSeqLaw μ).map (forestTriplePath B n T)

/-- **The C27 limit** on `[0,T]`: the stable path restricted to `[0,T]` and its continuous
height (H03 prefix map), the height being used for both the height and contour coordinates. -/
noncomputable def forestTripleLimit (θ : ℝ) (T : ℝ≥0) :
    ProbabilityMeasure
      (D (T : ℝ) ℝ × C(Set.Icc (0 : ℝ) (T : ℝ), ℝ) × C(Set.Icc (0 : ℝ) (T : ℝ), ℝ)) :=
  (stableLocalLaw θ).map (fun f : DLoc =>
    (DLoc.restrict T f, heightPrefix θ T (DLoc.restrict T f),
      heightPrefix θ T (DLoc.restrict T f)))

theorem measurable_forestTriplePath (B : ℕ → ℝ) (n : ℕ) (T : ℝ≥0) :
    Measurable (forestTriplePath B n T) := by
  exact (measurable_forestPairPath B n T).fst.prodMk
    ((measurable_forestPairPath B n T).snd.prodMk (measurable_forestContourPath B n T))

/-- The walk/height coordinates of the triple law form the sealed forest pair law. -/
theorem forestTripleLaw_map_pair (μ : PMF ℕ) (B : ℕ → ℝ) (n : ℕ) (T : ℝ≥0) :
    (forestTripleLaw μ B n T : Measure
        (D (T : ℝ) ℝ × C(Set.Icc (0 : ℝ) (T : ℝ), ℝ) × C(Set.Icc (0 : ℝ) (T : ℝ), ℝ))).map
        (fun x => (x.1, x.2.1)) =
      (forestPairLaw μ B n T : Measure (D (T : ℝ) ℝ × C(Set.Icc (0 : ℝ) (T : ℝ), ℝ))) := by
  change (Measure.map (forestTriplePath B n T) (offspringSeqLaw μ : Measure (ℕ → ℕ))).map
    (fun x => (x.1, x.2.1)) = Measure.map (forestPairPath B n T) (offspringSeqLaw μ : Measure _)
  rw [Measure.map_map (measurable_fst.prodMk measurable_snd.fst)
    (measurable_forestTriplePath B n T)]
  rfl

/-- The limit in the blueprint §2 form: the graph `g ↦ (g, H g, H g)` pushed forward by the
stable process law on `[0,T]` (all `T`). -/
theorem forestTripleLimit_eq_map_stableProcessLaw {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (T : ℝ≥0) :
    (forestTripleLimit θ T : Measure
        (D (T : ℝ) ℝ × C(Set.Icc (0 : ℝ) (T : ℝ), ℝ) × C(Set.Icc (0 : ℝ) (T : ℝ), ℝ))) =
      (stableProcessLaw θ (T : ℝ) : Measure (D (T : ℝ) ℝ)).map
        (fun g => (g, heightPrefix θ T g, heightPrefix θ T g)) := by
  let F : DLoc → D (T : ℝ) ℝ × C(Set.Icc (0 : ℝ) (T : ℝ), ℝ) := fun f =>
    (DLoc.restrict T f, heightPrefix θ T (DLoc.restrict T f))
  let G : D (T : ℝ) ℝ × C(Set.Icc (0 : ℝ) (T : ℝ), ℝ) →
      D (T : ℝ) ℝ × C(Set.Icc (0 : ℝ) (T : ℝ), ℝ) × C(Set.Icc (0 : ℝ) (T : ℝ), ℝ) :=
    fun x => (x.1, x.2, x.2)
  have hF : Measurable F := (DLoc.measurable_restrict T).prodMk
    ((measurable_heightPrefix θ T).comp (DLoc.measurable_restrict T))
  have hG : Measurable G := measurable_fst.prodMk (measurable_snd.prodMk measurable_snd)
  change Measure.map (fun f : DLoc => (_, _, _)) (stableLocalLaw θ : Measure DLoc) = _
  calc
    Measure.map (fun f : DLoc => (DLoc.restrict T f, heightPrefix θ T (DLoc.restrict T f),
        heightPrefix θ T (DLoc.restrict T f))) (stableLocalLaw θ : Measure DLoc) =
        (Measure.map F (stableLocalLaw θ : Measure DLoc)).map G := by
      rw [Measure.map_map hG hF]
      rfl
    _ = _ := by
      rw [map_heightPrefix_pair hθ T]
      exact Measure.map_map hG (measurable_id.prodMk (measurable_heightPrefix θ T))

/-- **C27 (Duquesne-Le Gall), every positive horizon**: the rescaled walk, interpolated height
and padded contour of the iid BGW forest converge jointly to `(X, H, H)` on `[0,T]`. -/
theorem tendsto_forestTripleLaw {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ} (h : StableDomain μ θ B)
    {T : ℝ≥0} (hT : 0 < T) :
    Tendsto (fun n : ℕ => forestTripleLaw μ B n T) atTop (𝓝 (forestTripleLimit θ T)) := by
  let X : ℕ → (ℕ → ℕ) → D (T : ℝ) ℝ × C(Set.Icc (0 : ℝ) (T : ℝ), ℝ) :=
    fun n => forestPairPath B n T
  let Y : ℕ → (ℕ → ℕ) → C(Set.Icc (0 : ℝ) (T : ℝ), ℝ) := fun n ω =>
    forestContourPath B n T ω - forestHeightPath B n T ω
  let P : ProbabilityMeasure (D (T : ℝ) ℝ × C(Set.Icc (0 : ℝ) (T : ℝ), ℝ)) :=
    (stableLocalLaw θ).map
      (fun f : DLoc => (DLoc.restrict T f, heightPrefix θ T (DLoc.restrict T f)))
  have hX (n : ℕ) : Measurable (X n) := measurable_forestPairPath B n T
  have hY (n : ℕ) : Measurable (Y n) := by
    apply ContinuousMap.measurable_iff_eval.mpr
    intro t
    exact ((ContinuousMap.measurable_eval t).comp (measurable_forestContourPath B n T)).sub
      ((ContinuousMap.measurable_eval t).comp (measurable_forestPairPath B n T).snd)
  have hdist (n : ℕ) (ω : ℕ → ℕ) :
      dist (Y n ω) 0 = forestContourHeightError B n T ω := by
    simpa only [Y, dist_eq_norm, sub_zero] using
      dist_forestContourPath_forestHeightPath B n T ω
  have herr : ∀ ε > 0, Tendsto (fun n =>
      (offspringSeqLaw μ : Measure (ℕ → ℕ)).real {ω | ε < dist (Y n ω) 0}) atTop (𝓝 0) := by
    intro ε hε
    have herror := tendstoInMeasure_iff_measureReal_dist.mp
      (contour_height_error_tendstoInMeasure h hT) (ε / 2) (half_pos hε)
    apply squeeze_zero (fun _ => measureReal_nonneg) _ herror
    intro n
    apply measureReal_mono _ (measure_ne_top _ _)
    intro ω hω
    change ε / 2 ≤ dist (forestContourHeightError B n T ω) 0
    have hnonneg : 0 ≤ forestContourHeightError B n T ω :=
      Real.iSup_nonneg fun _ => abs_nonneg _
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hnonneg]
    change ε < dist (Y n ω) 0 at hω
    rw [hdist] at hω
    exact (half_lt_self hε).trans hω |>.le
  have hlim : Tendsto (fun n => (offspringSeqLaw μ).map (X n)) atTop (𝓝 P) := by
    simpa only [X, P] using HeightTightness.tendsto_forestPairLaw h hT
  have hjoint := BGW.Probability.tendsto_map_prodMk_of_tendsto_of_error
    (fun _ => offspringSeqLaw μ) hX hY hlim herr
  let Φ : (D (T : ℝ) ℝ × C(Set.Icc (0 : ℝ) (T : ℝ), ℝ)) ×
      C(Set.Icc (0 : ℝ) (T : ℝ), ℝ) →
      D (T : ℝ) ℝ × C(Set.Icc (0 : ℝ) (T : ℝ), ℝ) × C(Set.Icc (0 : ℝ) (T : ℝ), ℝ) :=
    fun z => (z.1.1, z.1.2, z.1.2 + z.2)
  have hΦ : Continuous Φ := by fun_prop
  have hmap := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
    (fun n => ((offspringSeqLaw μ).map (fun ω => (X n ω, Y n ω))))
    (P.map (fun x => (x, 0))) hjoint hΦ
  have hseq (n : ℕ) :
      ((offspringSeqLaw μ).map (fun ω => (X n ω, Y n ω))).map Φ = forestTripleLaw μ B n T := by
    apply Subtype.ext
    change Measure.map Φ (Measure.map (fun ω => (X n ω, Y n ω))
      (offspringSeqLaw μ : Measure (ℕ → ℕ))) =
      Measure.map (forestTriplePath B n T) (offspringSeqLaw μ : Measure (ℕ → ℕ))
    rw [Measure.map_map hΦ.measurable ((hX n).prodMk (hY n))]
    congr 1
    funext ω
    simp [Φ, X, Y, forestTriplePath, forestPairPath]
  have hzero : Measurable (fun x : D (T : ℝ) ℝ × C(Set.Icc (0 : ℝ) (T : ℝ), ℝ) =>
      (x, (0 : C(Set.Icc (0 : ℝ) (T : ℝ), ℝ)))) := measurable_id.prodMk measurable_const
  have hlimit : (P.map (fun x => (x, 0))).map Φ = forestTripleLimit θ T := by
    apply Subtype.ext
    change Measure.map Φ (Measure.map (fun x => (x, 0)) (P : Measure _)) =
      Measure.map (fun f : DLoc =>
        (DLoc.restrict T f, heightPrefix θ T (DLoc.restrict T f),
          heightPrefix θ T (DLoc.restrict T f))) (stableLocalLaw θ : Measure DLoc)
    rw [Measure.map_map hΦ.measurable hzero]
    have hp : Measurable (fun f : DLoc =>
        (DLoc.restrict T f, heightPrefix θ T (DLoc.restrict T f))) :=
      (DLoc.measurable_restrict T).prodMk
        ((measurable_heightPrefix θ T).comp (DLoc.measurable_restrict T))
    change Measure.map _ (Measure.map _ (stableLocalLaw θ : Measure DLoc)) = _
    rw [Measure.map_map (by fun_prop) hp]
    simp [Φ, Function.comp_def]
  simpa only [hseq, hlimit] using hmap

end BGW.StableTrees.ForestTriple
