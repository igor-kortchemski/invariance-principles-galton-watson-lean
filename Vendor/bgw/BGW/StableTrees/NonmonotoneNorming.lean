/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.ForestTripleVector
public import BGW.StableTrees.TailPair
public import BGW.StableTrees.ExactContourJoint
public import BGW.StableTrees.RealAttraction

import BGW.Probability.WeakConvergence
import BGW.Skorokhod.MeasurableCylinders
import BGW.Skorokhod.ScalingMultiplication
import BGW.StableTrees.Attraction.Norming

/-!
# C27--C29 for arbitrary admissible normings

A real attracted norming is first converted to the integer attraction predicate. The canonical
monotone norming and convergence of types provide a stable-domain norming whose ratio to the
given one tends to one. Deterministic spatial scaling then transfers the sealed forest, tail,
and exact-size convergence theorems.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal Classical
open BGW.Skorokhod

namespace BGW.StableTrees

open BGW.Probability.RealWalk

private theorem isStableAttracted_of_isRealStableAttracted
    {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ}
    (hB : IsRealStableAttracted (realOffspringStepLaw μ) θ B) :
    Attraction.IsStableAttracted (stepLaw μ) θ 0 B := by
  refine ⟨hB.index_mem, ?_, (stableLaw θ : Measure ℝ), inferInstance, ?_, ?_⟩
  · obtain ⟨N, hN⟩ := eventually_atTop.mp hB.pos
    exact ⟨N, hN⟩
  · intro lam hlam
    exact integral_exp_neg_mul_stableLaw hB.index_mem hlam.le
  · intro f
    have h := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hB.converges) f
    refine h.congr' ?_
    filter_upwards [] with n
    have hmap : (scaledSumLaw (realOffspringStepLaw μ) B n : Measure ℝ) =
        (Attraction.intWalk (stepLaw μ) n).map (fun z : ℤ => (z : ℝ) / B n) := by
      change Measure.map (fun x : ℝ => x / B n)
        (sumLaw (castLaw (stepLaw μ)) n : Measure ℝ) = _
      rw [sumLaw_castLaw, Measure.map_map (by fun_prop) (by fun_prop)]
      rfl
    rw [hmap]
    simp

private theorem exists_stableDomain_norming_ratio {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ}
    (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hB : IsRealStableAttracted (realOffspringStepLaw μ) θ B) :
    ∃ B' : ℕ → ℝ, StableDomain μ θ B' ∧
      Tendsto (fun n => B n / B' n) atTop (𝓝 1) := by
  have hatt := isStableAttracted_of_isRealStableAttracted hB
  have hmean : Attraction.mean (stepLaw μ) = 0 := Attraction.mean_stepLaw hc
  have hattm : Attraction.IsStableAttracted (stepLaw μ) θ
      (Attraction.mean (stepLaw μ)) B := by
    rwa [hmean]
  have hcanm := Attraction.Norming.locallimit_i (stepLaw μ)
    (Attraction.stepLaw_lt_neg_one μ) (Attraction.integrable_stepLaw hc) ⟨B, hattm⟩
  have hmono := (Attraction.Norming.locallimit_ii (stepLaw μ)
    (Attraction.stepLaw_lt_neg_one μ) (Attraction.integrable_stepLaw hc) ⟨B, hattm⟩).1
  have hcan : Attraction.IsStableAttracted (stepLaw μ) θ 0
      (Attraction.norming (stepLaw μ) θ) := by
    rwa [hmean] at hcanm
  obtain ⟨B', hEq, hdom⟩ := hcan.exists_stableDomain hc hne hmono
  refine ⟨B', hdom, ?_⟩
  have hratio := Attraction.TransformConvergence.norming_ratio_tendsto_one
    (stepLaw μ) hatt hcan
  apply hratio.congr'
  filter_upwards [hEq] with n hn
  rw [hn]

private theorem tendsto_map_of_tendsto_of_tendsto
    {A S X : Type*} [PseudoMetricSpace A] [MeasurableSpace A] [BorelSpace A]
    [MeasurableSingletonClass A] [SecondCountableTopology A]
    [PseudoMetricSpace S] [MeasurableSpace S] [BorelSpace S] [SecondCountableTopology S]
    [PseudoMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (P : ℕ → ProbabilityMeasure S) (Q : ProbabilityMeasure S)
    (hP : Tendsto P atTop (𝓝 Q)) {a : ℕ → A} {a₀ : A}
    (ha : Tendsto a atTop (𝓝 a₀)) (F : A × S → X)
    (hF : ∀ n, Measurable (fun x => F (a n, x)))
    (hF₀ : Measurable (fun x => F (a₀, x)))
    (hcont : ∀ x, ContinuousAt F (a₀, x)) :
    Tendsto (fun n => (P n).map (fun x => F (a n, x))) atTop
      (𝓝 (Q.map (fun x => F (a₀, x)))) := by
  let pair : ℕ → S → S × A := fun n x => (x, a n)
  let pair₀ : S → S × A := fun x => (x, a₀)
  let Φ : S × A → X := fun z => F (z.2, z.1)
  have hpair (n : ℕ) : Measurable (pair n) := measurable_id.prodMk measurable_const
  have hpair₀ : Measurable pair₀ := measurable_id.prodMk measurable_const
  have herr : ∀ ε > 0, Tendsto (fun n => (P n : Measure S).real
      {x | ε < dist (pair n x) (pair₀ x)}) atTop (𝓝 0) := by
    intro ε hε
    have he : ∀ᶠ n in atTop, (P n : Measure S).real
        {x | ε < dist (pair n x) (pair₀ x)} = 0 := by
      filter_upwards [Metric.tendsto_nhds.mp ha ε hε] with n hn
      have hs : {x : S | ε < dist (pair n x) (pair₀ x)} = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro x hx
        change ε < dist (pair n x) (pair₀ x) at hx
        have hx' : ε < dist (a n) a₀ := by
          simpa only [pair, pair₀, dist_prod_same_left] using hx
        exact (not_lt_of_ge hn.le) hx'
      rw [hs]
      simp
    exact tendsto_const_nhds.congr' (he.mono fun _ hn => hn.symm)
  have hlim₀ : Tendsto (fun n => (P n).map pair₀) atTop (𝓝 (Q.map pair₀)) :=
    ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous P Q hP
      (continuous_id.prodMk continuous_const)
  have hjoint := BGW.MetricMeasure.tendsto_probabilityMap_of_error_probability P
    (fun n => hpair n) (fun _ => hpair₀) herr hlim₀
  have hΦ (n : ℕ) : AEMeasurable Φ ((P n).map (pair n) : Measure (S × A)) := by
    apply (measurableEmbedding_prod_mk_right (a n)).aemeasurable_map_iff.mpr
    exact (hF n).aemeasurable
  have hcontΦ (x : S) : ContinuousAt Φ (pair₀ x) := by
    change ContinuousAt (fun z : S × A => F (z.2, z.1)) (x, a₀)
    exact ContinuousAt.comp (f := fun z : S × A => (z.2, z.1)) (hcont x)
      (continuous_snd.prodMk continuous_fst).continuousAt
  have hcont_ae : ∀ᵐ z ∂(Q.map pair₀ : Measure (S × A)), ContinuousAt Φ z := by
    apply (ae_map_iff hpair₀.aemeasurable (IsGδ.setOfPred_continuousAt Φ).measurableSet).mpr
    exact Eventually.of_forall hcontΦ
  have hm := BGW.Probability.tendsto_map_of_ae_continuousAt hjoint hΦ hcont_ae
  have hseq (n : ℕ) : ((P n).map (pair n)).map Φ = (P n).map (fun x => F (a n, x)) := by
    apply Subtype.ext
    exact AEMeasurable.map_map_of_aemeasurable (hΦ n) (hpair n).aemeasurable
  have hΦ₀ : AEMeasurable Φ (Q.map pair₀ : Measure (S × A)) := by
    apply (measurableEmbedding_prod_mk_right a₀).aemeasurable_map_iff.mpr
    exact hF₀.aemeasurable
  have hlim : (Q.map pair₀).map Φ = Q.map (fun x => F (a₀, x)) := by
    apply Subtype.ext
    exact AEMeasurable.map_map_of_aemeasurable hΦ₀ hpair₀.aemeasurable
  simpa only [hseq, hlim] using hm

private theorem measurable_mulPath {T : ℝ} (hT : 0 ≤ T) (k : ℝ) :
    Measurable (mulPath (T := T) (E := ℝ) k) := by
  rw [measurable_iff_comap_le]
  change MeasurableSpace.comap (mulPath k) (inferInstance : MeasurableSpace (D T ℝ)) ≤
    (inferInstance : MeasurableSpace (D T ℝ))
  conv_lhs =>
    rw [measurableSpace_eq_iSup_comap_eval (T := T) (E := ℝ) (S := Set.univ)
      dense_univ hT (by simp)]
  simp only [MeasurableSpace.comap_iSup, iSup_le_iff, MeasurableSpace.comap_comp,
    Function.comp_def]
  intro t _ht
  have heval : Measurable (fun f : D T ℝ => k * f t) :=
    measurable_const.mul (measurable_eval t)
  exact heval.comap_le

private theorem mulPath_one {T : ℝ} (x : D T ℝ) : mulPath 1 x = x := by
  ext t
  simp [mulPath]

private noncomputable def scaleWalkPair (c : ℝ × ℝ) {T : ℝ≥0}
    (x : D (T : ℝ) ℝ × C(Set.Icc (0 : ℝ) (T : ℝ), ℝ)) :
    D (T : ℝ) ℝ × C(Set.Icc (0 : ℝ) (T : ℝ), ℝ) :=
  (mulPath c.1 x.1, c.2 • x.2)

private noncomputable def scaleForestTriple (c : ℝ × ℝ) {T : ℝ≥0}
    (x : D (T : ℝ) ℝ × C(Set.Icc (0 : ℝ) (T : ℝ), ℝ) ×
      C(Set.Icc (0 : ℝ) (T : ℝ), ℝ)) :
    D (T : ℝ) ℝ × C(Set.Icc (0 : ℝ) (T : ℝ), ℝ) ×
      C(Set.Icc (0 : ℝ) (T : ℝ), ℝ) :=
  (mulPath c.1 x.1, c.2 • x.2.1, c.2 • x.2.2)

private noncomputable def scaleContPair (c : ℝ)
    (x : C(Set.Icc (0 : ℝ) 1, ℝ) × C(Set.Icc (0 : ℝ) 1, ℝ)) :
    C(Set.Icc (0 : ℝ) 1, ℝ) × C(Set.Icc (0 : ℝ) 1, ℝ) :=
  (c • x.1, c • x.2)

private theorem measurable_scaleWalkPair {T : ℝ≥0} (hT : 0 < T) (c : ℝ × ℝ) :
    Measurable (scaleWalkPair (T := T) c) := by
  exact ((measurable_mulPath hT.le c.1).comp measurable_fst).prodMk
    ((measurable_const_smul c.2).comp measurable_snd)

private theorem measurable_scaleForestTriple {T : ℝ≥0} (hT : 0 < T) (c : ℝ × ℝ) :
    Measurable (scaleForestTriple (T := T) c) := by
  exact ((measurable_mulPath hT.le c.1).comp measurable_fst).prodMk
    (((measurable_const_smul c.2).comp (measurable_fst.comp measurable_snd)).prodMk
      ((measurable_const_smul c.2).comp (measurable_snd.comp measurable_snd)))

private theorem measurable_scaleContPair (c : ℝ) : Measurable (scaleContPair c) := by
  exact (measurable_const_smul c).comp measurable_fst |>.prodMk
    ((measurable_const_smul c).comp measurable_snd)

private theorem continuousAt_scaleWalkPair {T : ℝ≥0} (hT : 0 < T)
    (x : D (T : ℝ) ℝ × C(Set.Icc (0 : ℝ) (T : ℝ), ℝ)) :
    ContinuousAt (fun z : (ℝ × ℝ) ×
      (D (T : ℝ) ℝ × C(Set.Icc (0 : ℝ) (T : ℝ), ℝ)) => scaleWalkPair z.1 z.2)
      ((1, 1), x) := by
  change ContinuousAt (fun z : (ℝ × ℝ) ×
    (D (T : ℝ) ℝ × C(Set.Icc (0 : ℝ) (T : ℝ), ℝ)) =>
      (mulPath z.1.1 z.2.1, z.1.2 • z.2.2)) ((1, 1), x)
  refine ContinuousAt.prodMk ?_ ?_
  · unfold ContinuousAt
    change Tendsto (fun z : (ℝ × ℝ) ×
      (D (T : ℝ) ℝ × C(Set.Icc (0 : ℝ) (T : ℝ), ℝ)) => mulPath z.1.1 z.2.1)
      (𝓝 (((1, 1) : ℝ × ℝ), x)) (𝓝 (mulPath (1 : ℝ) x.1))
    rw [mulPath_one]
    exact (tendsto_mulPath_one hT.le (l := 𝓝 (((1, 1) : ℝ × ℝ), x)) (f := x.1)
        (u := fun z : (ℝ × ℝ) ×
          (D (T : ℝ) ℝ × C(Set.Icc (0 : ℝ) (T : ℝ), ℝ)) => z.2.1)
        (k := fun z : (ℝ × ℝ) ×
          (D (T : ℝ) ℝ × C(Set.Icc (0 : ℝ) (T : ℝ), ℝ)) => z.1.1)
        (continuousAt_fst.comp continuousAt_snd)
        (continuousAt_fst.comp continuousAt_fst))
  · fun_prop

private theorem continuousAt_scaleForestTriple {T : ℝ≥0} (hT : 0 < T)
    (x : D (T : ℝ) ℝ × C(Set.Icc (0 : ℝ) (T : ℝ), ℝ) ×
      C(Set.Icc (0 : ℝ) (T : ℝ), ℝ)) :
    ContinuousAt (fun z : (ℝ × ℝ) ×
      (D (T : ℝ) ℝ × C(Set.Icc (0 : ℝ) (T : ℝ), ℝ) ×
        C(Set.Icc (0 : ℝ) (T : ℝ), ℝ)) => scaleForestTriple z.1 z.2)
      ((1, 1), x) := by
  change ContinuousAt (fun z : (ℝ × ℝ) ×
    (D (T : ℝ) ℝ × C(Set.Icc (0 : ℝ) (T : ℝ), ℝ) ×
      C(Set.Icc (0 : ℝ) (T : ℝ), ℝ)) =>
      (mulPath z.1.1 z.2.1, z.1.2 • z.2.2.1, z.1.2 • z.2.2.2)) ((1, 1), x)
  refine ContinuousAt.prodMk ?_ (ContinuousAt.prodMk ?_ ?_)
  · unfold ContinuousAt
    change Tendsto (fun z : (ℝ × ℝ) ×
      (D (T : ℝ) ℝ × C(Set.Icc (0 : ℝ) (T : ℝ), ℝ) ×
        C(Set.Icc (0 : ℝ) (T : ℝ), ℝ)) => mulPath z.1.1 z.2.1)
      (𝓝 (((1, 1) : ℝ × ℝ), x)) (𝓝 (mulPath (1 : ℝ) x.1))
    rw [mulPath_one]
    exact (tendsto_mulPath_one hT.le (l := 𝓝 (((1, 1) : ℝ × ℝ), x)) (f := x.1)
        (u := fun z : (ℝ × ℝ) ×
          (D (T : ℝ) ℝ × C(Set.Icc (0 : ℝ) (T : ℝ), ℝ) ×
            C(Set.Icc (0 : ℝ) (T : ℝ), ℝ)) => z.2.1)
        (k := fun z : (ℝ × ℝ) ×
          (D (T : ℝ) ℝ × C(Set.Icc (0 : ℝ) (T : ℝ), ℝ) ×
            C(Set.Icc (0 : ℝ) (T : ℝ), ℝ)) => z.1.1)
        (continuousAt_fst.comp continuousAt_snd)
        (continuousAt_fst.comp continuousAt_fst))
  · fun_prop
  · fun_prop

private theorem continuous_uncurry_scaleContPair :
    Continuous (Function.uncurry scaleContPair) := by
  change Continuous (fun z : ℝ ×
    (C(Set.Icc (0 : ℝ) 1, ℝ) × C(Set.Icc (0 : ℝ) 1, ℝ)) =>
      (z.1 • z.2.1, z.1 • z.2.2))
  fun_prop

private theorem scaleWalkPair_one {T : ℝ≥0}
    (x : D (T : ℝ) ℝ × C(Set.Icc (0 : ℝ) (T : ℝ), ℝ)) :
    scaleWalkPair (1, 1) x = x := by
  apply Prod.ext
  · ext t
    simp [scaleWalkPair, mulPath]
  · simp [scaleWalkPair]

private theorem scaleForestTriple_one {T : ℝ≥0}
    (x : D (T : ℝ) ℝ × C(Set.Icc (0 : ℝ) (T : ℝ), ℝ) ×
      C(Set.Icc (0 : ℝ) (T : ℝ), ℝ)) :
    scaleForestTriple (1, 1) x = x := by
  apply Prod.ext
  · ext t
    simp [scaleForestTriple, mulPath]
  · apply Prod.ext <;> simp [scaleForestTriple]

private theorem scaleContPair_one
    (x : C(Set.Icc (0 : ℝ) 1, ℝ) × C(Set.Icc (0 : ℝ) 1, ℝ)) :
    scaleContPair 1 x = x := by
  apply Prod.ext <;> simp [scaleContPair]

private theorem realStepPath_eq_scale {T : ℝ} (n : ℕ) {b b' : ℝ} (hb' : b' ≠ 0)
    (ω : ℕ → ℝ) :
    realStepPath T n b ω = mulPath (b' / b) (realStepPath T n b' ω) := by
  ext t
  change partialSum ω ⌊(n : ℝ) * (t : ℝ)⌋₊ / b =
    (b' / b) * (partialSum ω ⌊(n : ℝ) * (t : ℝ)⌋₊ / b')
  by_cases hb : b = 0
  · simp [hb]
  · field_simp [hb, hb']

private theorem forestHeightPath_eq_scale (B B' : ℕ → ℝ) (n : ℕ) (hB' : B' n ≠ 0)
    (T : ℝ≥0) (ω : ℕ → ℕ) :
    DiscreteForest.forestHeightPath B n T ω =
      (B n / B' n) • DiscreteForest.forestHeightPath B' n T ω := by
  ext t
  change B n / n * DiscreteForest.forestHeightLin ω ((n : ℝ) * (t : ℝ)) =
    (B n / B' n) * (B' n / n * DiscreteForest.forestHeightLin ω ((n : ℝ) * (t : ℝ)))
  by_cases hn : n = 0
  · simp [hn]
  · have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    field_simp [hB', hn']

private theorem treeHeightPath_eq_scale (B B' : ℕ → ℝ) (n : ℕ) (hB' : B' n ≠ 0)
    (T : ℝ≥0) (τ : BGW.LocallyFinite.Tree) :
    TailPair.treeHeightPath B n T τ = (B n / B' n) • TailPair.treeHeightPath B' n T τ := by
  ext t
  simp only [TailPair.treeHeightPath,
    dite_eq_left (TailPair.continuous_treeHeightLin τ),
    ContinuousMap.smul_apply, smul_eq_mul]
  change B n / n * TailPair.treeHeightLin τ ((n : ℝ) * (t : ℝ)) =
    (B n / B' n) * (B' n / n * TailPair.treeHeightLin τ ((n : ℝ) * (t : ℝ)))
  by_cases hn : n = 0
  · simp [hn]
  · have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    field_simp [hB', hn']

private theorem forestTriplePath_eq_scale (B B' : ℕ → ℝ) (n : ℕ) (hB' : B' n ≠ 0)
    (T : ℝ≥0) (ω : ℕ → ℕ) :
    ForestTriple.forestTriplePath B n T ω =
      scaleForestTriple (B' n / B n, B n / B' n) (ForestTriple.forestTriplePath B' n T ω) := by
  apply Prod.ext
  · exact realStepPath_eq_scale n hB' (fun i => ((ω i : ℤ) - 1 : ℝ))
  · apply Prod.ext
    · exact forestHeightPath_eq_scale B B' n hB' T ω
    · ext t
      change ForestContour.forestContourPath B n T ω t =
        (B n / B' n) * ForestContour.forestContourPath B' n T ω t
      rw [ForestContour.forestContourPath_apply, ForestContour.forestContourPath_apply]
      by_cases hn : n = 0
      · simp [hn]
      · have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
        field_simp [hB', hn']

private theorem treePairPath_eq_scale (B B' : ℕ → ℝ) (n : ℕ) (hB' : B' n ≠ 0)
    (T : ℝ≥0) (τ : BGW.LocallyFinite.Tree) :
    TailPair.treePairPath B n T τ =
      scaleWalkPair (B' n / B n, B n / B' n) (TailPair.treePairPath B' n T τ) := by
  apply Prod.ext
  · exact realStepPath_eq_scale n hB' (PathTail.treeIncrementSeq τ)
  · exact treeHeightPath_eq_scale B B' n hB' T τ

private theorem heightContourPath_eq_scale (B B' : ℕ → ℝ) (n : ℕ) (hB' : B' n ≠ 0)
    (τ : BGW.LocallyFinite.Tree) :
    ExactContour.heightContourPath B n τ =
      scaleContPair (B n / B' n) (ExactContour.heightContourPath B' n τ) := by
  apply Prod.ext
  · exact treeHeightPath_eq_scale B B' n hB' 1 τ
  · ext t
    change ExactContour.treeContourPath B n 1 τ t =
      (B n / B' n) * ExactContour.treeContourPath B' n 1 τ t
    simp only [ExactContour.treeContourPath,
      dite_eq_left (ExactContour.continuous_treeContourLin τ)]
    change B n / n * ExactContour.treeContourLin τ (2 * (n : ℝ) * (t : ℝ)) =
      (B n / B' n) *
        (B' n / n * ExactContour.treeContourLin τ (2 * (n : ℝ) * (t : ℝ)))
    by_cases hn : n = 0
    · simp [hn]
    · have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
      field_simp [hB', hn']

private theorem heightLibContourPath_eq_scale (B B' : ℕ → ℝ) (n : ℕ) (hB' : B' n ≠ 0)
    (τ : BGW.LocallyFinite.Tree) :
    ExactContour.heightLibContourPath B n τ =
      scaleContPair (B n / B' n) (ExactContour.heightLibContourPath B' n τ) := by
  apply Prod.ext
  · exact treeHeightPath_eq_scale B B' n hB' 1 τ
  · change (if h : BGW.LocallyFinite.FiniteVertices τ then
        (B n / n) • (PlaneTree.equivFiniteVertices.symm ⟨τ, h⟩).contourFunction else 0) =
      (B n / B' n) • (if h : BGW.LocallyFinite.FiniteVertices τ then
        (B' n / n) • (PlaneTree.equivFiniteVertices.symm ⟨τ, h⟩).contourFunction else 0)
    by_cases hτ : BGW.LocallyFinite.FiniteVertices τ
    · simp only [dite_eq_left hτ, smul_smul]
      congr 1
      by_cases hn : n = 0
      · simp [hn]
      · have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
        field_simp [hB', hn']
    · simp [hτ]

/-- **C27 for an arbitrary admissible norming.** -/
theorem ForestTriple.tendsto_forestTripleLaw_of_attracted
    {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ}
    (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hB : IsRealStableAttracted (realOffspringStepLaw μ) θ B) {T : ℝ≥0} (hT : 0 < T) :
    Tendsto (fun n : ℕ => ForestTriple.forestTripleLaw μ B n T) atTop
      (𝓝 (ForestTriple.forestTripleLimit θ T)) := by
  obtain ⟨B', hdom, hratio⟩ := exists_stableDomain_norming_ratio hc hne hB
  have hinv : Tendsto (fun n => B' n / B n) atTop (𝓝 1) := by
    simpa only [inv_div, inv_one] using hratio.inv₀ one_ne_zero
  let a : ℕ → ℝ × ℝ := fun n => (B' n / B n, B n / B' n)
  have ha : Tendsto a atTop (𝓝 (1, 1)) := hinv.prodMk_nhds hratio
  have ht := tendsto_map_of_tendsto_of_tendsto
    (fun n => ForestTriple.forestTripleLaw μ B' n T) (ForestTriple.forestTripleLimit θ T)
    (ForestTriple.tendsto_forestTripleLaw hdom hT) ha
    (Function.uncurry (scaleForestTriple (T := T)))
    (fun n => measurable_scaleForestTriple hT (a n))
    (measurable_scaleForestTriple hT (1, 1)) (continuousAt_scaleForestTriple hT)
  have hid : (fun x => Function.uncurry (scaleForestTriple (T := T)) ((1, 1), x)) = id := by
    funext x
    exact scaleForestTriple_one x
  rw [hid] at ht
  have hmapid : (ForestTriple.forestTripleLimit θ T).map id =
      ForestTriple.forestTripleLimit θ T := by
    apply Subtype.ext
    exact Measure.map_id
  rw [hmapid] at ht
  apply ht.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  symm
  apply Subtype.ext
  change Measure.map (ForestTriple.forestTriplePath B n T)
      (DiscreteForest.offspringSeqLaw μ : Measure _) =
    Measure.map (fun x => scaleForestTriple (a n) x)
      (Measure.map (ForestTriple.forestTriplePath B' n T)
        (DiscreteForest.offspringSeqLaw μ : Measure _))
  rw [Measure.map_map (measurable_scaleForestTriple hT (a n))
    (ForestTriple.measurable_forestTriplePath B' n T)]
  congr 1
  funext ω
  exact forestTriplePath_eq_scale B B' n (hdom.pos n hn).ne' T ω

/-- **C27, vector-path form, for an arbitrary admissible norming.** -/
theorem ForestTriple.tendsto_forestTripleVecLaw_of_attracted
    {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ}
    (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hB : IsRealStableAttracted (realOffspringStepLaw μ) θ B) {T : ℝ≥0} (hT : 0 < T) :
    Tendsto (fun n : ℕ => ForestTriple.forestTripleVecLaw μ B n T) atTop
      (𝓝 (ForestTriple.forestTripleVecLimit θ T)) :=
  ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _
    (tendsto_forestTripleLaw_of_attracted hc hne hB hT) (ForestTriple.continuous_tripleVec T)

/-- **C28 for an arbitrary admissible norming.** -/
theorem TailPair.tendsto_tailPairLaw_of_attracted {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ}
    (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hB : IsRealStableAttracted (realOffspringStepLaw μ) θ B) {T : ℝ≥0} (hT : 0 < T) :
    Tendsto (fun n : ℕ => TailPair.tailPairLaw μ B n T) atTop (𝓝 (tailExcLaw θ T)) := by
  obtain ⟨B', hdom, hratio⟩ := exists_stableDomain_norming_ratio hc hne hB
  have hinv : Tendsto (fun n => B' n / B n) atTop (𝓝 1) := by
    simpa only [inv_div, inv_one] using hratio.inv₀ one_ne_zero
  let a : ℕ → ℝ × ℝ := fun n => (B' n / B n, B n / B' n)
  have ha : Tendsto a atTop (𝓝 (1, 1)) := hinv.prodMk_nhds hratio
  have ht := tendsto_map_of_tendsto_of_tendsto
    (fun n => TailPair.tailPairLaw μ B' n T) (tailExcLaw θ T)
    (TailPair.tendsto_tailPairLaw hdom hT) ha
    (Function.uncurry (scaleWalkPair (T := T)))
    (fun n => measurable_scaleWalkPair hT (a n)) (measurable_scaleWalkPair hT (1, 1))
    (continuousAt_scaleWalkPair hT)
  have hid : (fun x => Function.uncurry (scaleWalkPair (T := T)) ((1, 1), x)) = id := by
    funext x
    exact scaleWalkPair_one x
  rw [hid] at ht
  have hmapid : (tailExcLaw θ T).map id = tailExcLaw θ T := by
    apply Subtype.ext
    exact Measure.map_id
  rw [hmapid] at ht
  apply ht.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  symm
  apply Subtype.ext
  change Measure.map (TailPair.treePairPath B n T) (DiscreteForest.tailTreeLaw μ n : Measure _) =
    Measure.map (fun x => scaleWalkPair (a n) x)
      (Measure.map (TailPair.treePairPath B' n T) (DiscreteForest.tailTreeLaw μ n : Measure _))
  rw [Measure.map_map (measurable_scaleWalkPair hT (a n))
    (TailPair.measurable_treePairPath B' n T)]
  congr 1
  funext τ
  exact treePairPath_eq_scale B B' n (hdom.pos n hn).ne' T τ

/-- **C29 for an arbitrary admissible norming.** -/
theorem ExactContour.tendsto_exactHeightContourLaw_of_attracted
    {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ}
    (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hB : IsRealStableAttracted (realOffspringStepLaw μ) θ B) {q : ℕ → ℕ}
    (hqtop : Tendsto q atTop atTop) (hq : ∀ k, Admissible μ (q k)) :
    Tendsto (fun k => ExactContour.exactHeightContourLaw μ B (q k) (hq k)) atTop
      (𝓝 ((excLaw θ).map (fun p => (p.2, p.2)))) := by
  obtain ⟨B', hdom, hratio⟩ := exists_stableDomain_norming_ratio hc hne hB
  have hr : Tendsto (fun k => B (q k) / B' (q k)) atTop (𝓝 1) := hratio.comp hqtop
  let Q : ProbabilityMeasure (C(Set.Icc (0 : ℝ) 1, ℝ) × C(Set.Icc (0 : ℝ) 1, ℝ)) :=
    (excLaw θ).map (fun p => (p.2, p.2))
  have ht := tendsto_map_of_tendsto_of_tendsto
    (fun k => ExactContour.exactHeightContourLaw μ B' (q k) (hq k)) Q
    (ExactContour.tendsto_exactHeightContourLaw hdom hqtop hq) hr
    (Function.uncurry scaleContPair)
    (fun _ => measurable_scaleContPair _) (measurable_scaleContPair 1)
    (fun _ => continuous_uncurry_scaleContPair.continuousAt)
  have hid : (fun x => Function.uncurry scaleContPair (1, x)) = id := by
    funext x
    exact scaleContPair_one x
  rw [hid] at ht
  have hmapid : Q.map id = Q := by
    apply Subtype.ext
    exact Measure.map_id
  rw [hmapid] at ht
  apply ht.congr'
  filter_upwards [hqtop.eventually (eventually_ge_atTop 1)] with k hk
  symm
  apply Subtype.ext
  change Measure.map (ExactContour.heightContourPath B (q k))
      (DiscreteForest.exactTreeLaw μ (q k) : Measure _) =
    Measure.map (fun x => scaleContPair (B (q k) / B' (q k)) x)
      (Measure.map (ExactContour.heightContourPath B' (q k))
        (DiscreteForest.exactTreeLaw μ (q k) : Measure _))
  rw [Measure.map_map (measurable_scaleContPair _)
    (ExactContour.measurable_heightContourPath B' (q k))]
  congr 1
  funext τ
  exact heightContourPath_eq_scale B B' (q k) (hdom.pos (q k) hk).ne' τ

/-- **C29 in the library contour convention, for an arbitrary admissible norming.** -/
theorem ExactContour.tendsto_exactHeightLibContourLaw_of_attracted {μ : PMF ℕ} {θ : ℝ}
    {B : ℕ → ℝ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hB : IsRealStableAttracted (realOffspringStepLaw μ) θ B) {q : ℕ → ℕ}
    (hqtop : Tendsto q atTop atTop) (hq : ∀ k, Admissible μ (q k)) :
    Tendsto (fun k => ExactContour.exactHeightLibContourLaw μ B (q k) (hq k)) atTop
      (𝓝 ((excLaw θ).map (fun p => (p.2, p.2)))) := by
  obtain ⟨B', hdom, hratio⟩ := exists_stableDomain_norming_ratio hc hne hB
  have hr : Tendsto (fun k => B (q k) / B' (q k)) atTop (𝓝 1) := hratio.comp hqtop
  let Q : ProbabilityMeasure (C(Set.Icc (0 : ℝ) 1, ℝ) × C(Set.Icc (0 : ℝ) 1, ℝ)) :=
    (excLaw θ).map (fun p => (p.2, p.2))
  have ht := tendsto_map_of_tendsto_of_tendsto
    (fun k => ExactContour.exactHeightLibContourLaw μ B' (q k) (hq k)) Q
    (ExactContour.tendsto_exactHeightLibContourLaw hdom hqtop hq) hr
    (Function.uncurry scaleContPair)
    (fun _ => measurable_scaleContPair _) (measurable_scaleContPair 1)
    (fun _ => continuous_uncurry_scaleContPair.continuousAt)
  have hid : (fun x => Function.uncurry scaleContPair (1, x)) = id := by
    funext x
    exact scaleContPair_one x
  rw [hid] at ht
  have hmapid : Q.map id = Q := by
    apply Subtype.ext
    exact Measure.map_id
  rw [hmapid] at ht
  apply ht.congr'
  filter_upwards [hqtop.eventually (eventually_ge_atTop 1)] with k hk
  symm
  apply Subtype.ext
  change Measure.map (ExactContour.heightLibContourPath B (q k))
      (DiscreteForest.exactTreeLaw μ (q k) : Measure _) =
    Measure.map (fun x => scaleContPair (B (q k) / B' (q k)) x)
      (Measure.map (ExactContour.heightLibContourPath B' (q k))
        (DiscreteForest.exactTreeLaw μ (q k) : Measure _))
  rw [Measure.map_map (measurable_scaleContPair _)
    (ExactContour.measurable_heightLibContourPath B' (q k))]
  congr 1
  funext τ
  exact heightLibContourPath_eq_scale B B' (q k) (hdom.pos (q k) hk).ne' τ

end BGW.StableTrees
