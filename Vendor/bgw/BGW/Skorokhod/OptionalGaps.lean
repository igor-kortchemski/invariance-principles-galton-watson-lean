/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.Skorokhod.ProductPathsVector
public import BGW.Skorokhod.Prefix
public import BGW.Skorokhod.MeasurableMaps
public import BGW.Skorokhod.VervaatContinuity
public import BGW.Skorokhod.Jump
public import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import BGW.Skorokhod.StepApprox

/-!
# Optional results on Skorokhod space

This module proves the continuous-locus converse for pairing paths, restriction and stopping in
continuous path space, the signed jump and localization of the Vervaat wrap, and attainment and
characterizations of the largest upward jump.
-/

@[expose] public section

open Filter MeasureTheory Set Topology
open scoped Topology Classical BoundedContinuousFunction

namespace BGW.Skorokhod

variable {T : ℝ} {E F : Type*} [MetricSpace E] [MetricSpace F]

/-- First coordinate of a product-valued càdlàg path. -/
def fstWithCont (f : D T (E × F)) : D T E :=
  ⟨fun t => (f t).1, (isCadlag f).continuous_comp continuous_fst⟩

private def sndWithCont (f : D T (E × F)) : D T F :=
  ⟨fun t => (f t).2, (isCadlag f).continuous_comp continuous_snd⟩

/-- Split a product-valued path when its second coordinate is continuous.  Outside that locus,
use the constant continuous path `default` as an explicit junk value. -/
noncomputable def splitProdWithCont [Inhabited F] (f : D T (E × F)) :
    D T E × C(Set.Icc (0 : ℝ) T, F) :=
  (fstWithCont f, if h : Continuous (fun t => (f t).2) then
    ⟨fun t => (f t).2, h⟩ else ContinuousMap.const _ default)

private def continuousSecondLocus : Set (D T (E × F)) :=
  {f | Continuous (fun t => (f t).2)}

private theorem iSup_dist_withCont_le (u f : D T (E × F)) (σ : TimeChange T) :
    ((⨆ t, dist (fstWithCont u (σ t)) (fstWithCont f t)) ≤
        ⨆ t, dist (u (σ t)) (f t)) ∧
      ((⨆ t, dist (sndWithCont u (σ t)) (sndWithCont f t)) ≤
        ⨆ t, dist (u (σ t)) (f t)) := by
  constructor <;> apply Real.iSup_le
  · intro t
    let _ : Nonempty (Set.Icc (0 : ℝ) T) := ⟨t⟩
    have h := le_ciSup (bddAbove_comp_dist (le_trans t.2.1 t.2.2) u f σ) t
    rw [Prod.dist_eq] at h
    exact (le_max_left _ _).trans h
  · exact Real.iSup_nonneg fun t => dist_nonneg
  · intro t
    let _ : Nonempty (Set.Icc (0 : ℝ) T) := ⟨t⟩
    have h := le_ciSup (bddAbove_comp_dist (le_trans t.2.1 t.2.2) u f σ) t
    rw [Prod.dist_eq] at h
    exact (le_max_right _ _).trans h
  · exact Real.iSup_nonneg fun t => dist_nonneg

private theorem continuous_fstWithCont : Continuous (fstWithCont (T := T) (E := E) (F := F)) := by
  rw [continuous_iff_continuousAt]
  intro f
  obtain ⟨σ, hdisp, hpath⟩ := tendsto_iff_exists_timeChange.mp
    (tendsto_id : Tendsto (id : D T (E × F) → D T (E × F)) (𝓝 f) (𝓝 f))
  apply tendsto_iff_exists_timeChange.mpr
  refine ⟨σ, hdisp, ?_⟩
  exact squeeze_zero' (Filter.Eventually.of_forall fun u => Real.iSup_nonneg fun t => dist_nonneg)
    (Filter.Eventually.of_forall fun u => (iSup_dist_withCont_le u f (σ u)).1) hpath

private theorem continuous_sndWithCont : Continuous (sndWithCont (T := T) (E := E) (F := F)) := by
  rw [continuous_iff_continuousAt]
  intro f
  obtain ⟨σ, hdisp, hpath⟩ := tendsto_iff_exists_timeChange.mp
    (tendsto_id : Tendsto (id : D T (E × F) → D T (E × F)) (𝓝 f) (𝓝 f))
  apply tendsto_iff_exists_timeChange.mpr
  refine ⟨σ, hdisp, ?_⟩
  exact squeeze_zero' (Filter.Eventually.of_forall fun u => Real.iSup_nonneg fun t => dist_nonneg)
    (Filter.Eventually.of_forall fun u => (iSup_dist_withCont_le u f (σ u)).2) hpath

private theorem continuousSecondLocus_eq (f : D T (E × F)) :
    f ∈ continuousSecondLocus ↔
      sndWithCont f ∈ Set.range (ofContinuous (T := T) (E := F)) := by
  constructor
  · intro hf
    exact ⟨⟨fun t => (f t).2, hf⟩, rfl⟩
  · rintro ⟨g, hg⟩
    change Continuous (sndWithCont f)
    rw [← hg]
    exact g.continuous

private theorem isClosed_continuousSecondLocus : IsClosed (continuousSecondLocus (T := T)
    (E := E) (F := F)) := by
  have heq : continuousSecondLocus (T := T) (E := E) (F := F) =
      sndWithCont ⁻¹' Set.range (ofContinuous (T := T) (E := F)) := by
    ext f
    exact continuousSecondLocus_eq f
  rw [heq]
  exact isClosedEmbedding_ofContinuous.isClosed_range.preimage continuous_sndWithCont

private theorem ofContinuous_split_second [Inhabited F] {f : D T (E × F)}
    (hf : f ∈ continuousSecondLocus) :
    ofContinuous (splitProdWithCont f).2 = sndWithCont f := by
  apply DFunLike.ext
  intro t
  change (splitProdWithCont f).2 t = (f t).2
  rw [show (splitProdWithCont f).2 = ⟨fun t => (f t).2, hf⟩ by
    simp only [splitProdWithCont]
    rw [dite_eq_left (show Continuous (fun t => (f t).2) from hf)]]
  rfl

private theorem continuousOn_split_second [Inhabited F] :
    ContinuousOn (fun f => (splitProdWithCont (T := T) (E := E) (F := F) f).2)
      continuousSecondLocus := by
  intro f hf
  apply (isClosedEmbedding_ofContinuous (T := T) (E := F)).isEmbedding.tendsto_nhds_iff.mpr
  have hlim : Tendsto (sndWithCont (T := T) (E := E) (F := F))
      (𝓝[continuousSecondLocus] f) (𝓝 (sndWithCont f)) :=
    (continuous_sndWithCont (T := T) (E := E) (F := F)).continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds
  rw [ofContinuous_split_second hf]
  apply (tendsto_congr' ?_).2 hlim
  filter_upwards [self_mem_nhdsWithin] with g hg
  exact ofContinuous_split_second hg

private theorem continuousOn_splitProdWithCont [Inhabited F] :
    ContinuousOn (splitProdWithCont (T := T) (E := E) (F := F)) continuousSecondLocus := by
  intro f hf
  exact (continuous_fstWithCont (T := T) (E := E) (F := F)).continuousAt.continuousWithinAt.prodMk
    (continuousOn_split_second f hf)

private theorem measurable_splitProdWithCont [Inhabited F] :
    Measurable (splitProdWithCont (T := T) (E := E) (F := F)) := by
  refine Measurable.prodMk continuous_fstWithCont.measurable ?_
  change Measurable (fun f => (splitProdWithCont (T := T) (E := E) (F := F) f).2)
  let c : C(Set.Icc (0 : ℝ) T, F) := ContinuousMap.const _ default
  have hpiece : Measurable (continuousSecondLocus.piecewise
      (fun f => (splitProdWithCont (T := T) (E := E) (F := F) f).2) (fun _ => c)) :=
    continuousOn_split_second.measurable_piecewise continuousOn_const
      isClosed_continuousSecondLocus.measurableSet
  have heq : (fun f => (splitProdWithCont (T := T) (E := E) (F := F) f).2) =
      continuousSecondLocus.piecewise
        (fun f => (splitProdWithCont (T := T) (E := E) (F := F) f).2) (fun _ => c) := by
    funext f
    by_cases hf : Continuous (fun t => (f t).2)
    · simp [Set.piecewise, continuousSecondLocus, hf, splitProdWithCont]
    · simp [Set.piecewise, continuousSecondLocus, hf, splitProdWithCont, c]
  rw [heq]
  exact hpiece

/-- **C5 item 4, converse.**  Convergence in law in `D_T(E × F)`, on the locus where the second
coordinate is continuous, implies convergence in law in `D_T(E) × C([0,T],F)`. -/
theorem tendsto_map_splitProdWithCont [Inhabited F] [TopologicalSpace.SeparableSpace F]
    {μ : ℕ → ProbabilityMeasure (D T (E × F))} {ν : ProbabilityMeasure (D T (E × F))}
    (hlim : Tendsto μ atTop (𝓝 ν))
    (hμ : ∀ n, ∀ᵐ f ∂(μ n : Measure (D T (E × F))), Continuous (fun t => (f t).2))
    (hν : ∀ᵐ f ∂(ν : Measure (D T (E × F))), Continuous (fun t => (f t).2)) :
    Tendsto (fun n => (μ n).map (splitProdWithCont (T := T))) atTop
      (𝓝 (ν.map (splitProdWithCont (T := T)))) := by
  apply MeasureTheory.tendsto_of_forall_isClosed_limsup_le'
  intro A hA
  let K : Set (D T (E × F)) := continuousSecondLocus ∩
    (splitProdWithCont (T := T) (E := E) (F := F)) ⁻¹' A
  have hK : IsClosed K :=
    continuousOn_splitProdWithCont.preimage_isClosed_of_isClosed
      isClosed_continuousSecondLocus hA
  have hmap (P : ProbabilityMeasure (D T (E × F))) :
      ((P.map (splitProdWithCont (T := T) (E := E) (F := F)) :
        ProbabilityMeasure (D T E × C(Set.Icc (0 : ℝ) T, F))) : Measure _) A =
        (P : Measure (D T (E × F)))
          ((splitProdWithCont (T := T) (E := E) (F := F)) ⁻¹' A) := by
    rw [ProbabilityMeasure.toMeasure_map,
      Measure.map_apply measurable_splitProdWithCont hA.measurableSet]
  calc
    limsup (fun n => (((μ n).map (splitProdWithCont (T := T))) : Measure _) A) atTop =
        limsup (fun n => (μ n : Measure (D T (E × F))) K) atTop := by
      apply congrArg (fun v => limsup v atTop)
      funext n
      rw [hmap]
      exact (Measure.measure_inter_eq_of_ae (hμ n)).symm
    _ ≤ (ν : Measure (D T (E × F))) K :=
      ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hlim hK
    _ = (((ν.map (splitProdWithCont (T := T)))) : Measure _) A := by
      rw [hmap]
      exact Measure.measure_inter_eq_of_ae (μ := (ν : Measure (D T (E × F))))
        (t := continuousSecondLocus) hν

/-- Splitting followed by `prodWithCont` is the identity on paths with continuous second
coordinate. -/
theorem prodWithCont_splitProdWithCont [Inhabited F] (f : D T (E × F))
    (hf : Continuous (fun t => (f t).2)) :
    prodWithCont (splitProdWithCont f).1 (splitProdWithCont f).2 = f := by
  apply DFunLike.ext
  intro t
  change ((f t).1, (splitProdWithCont f).2 t) = f t
  rw [show (splitProdWithCont f).2 = ⟨fun t => (f t).2, hf⟩ by
    simp only [splitProdWithCont]
    rw [dite_eq_left hf]]
  rfl

/-- Restriction of a continuous path to `[0,a]`. -/
def restrictContinuous {a : ℝ} (haT : a ≤ T) (f : C(Set.Icc (0 : ℝ) T, E)) :
    C(Set.Icc (0 : ℝ) a, E) :=
  f.comp ⟨fun t => ⟨t.1, t.2.1, t.2.2.trans haT⟩, by fun_prop⟩

/-- Extend a continuous path on `[0,a]` constantly to `[0,T]`. -/
def extendContinuous {a : ℝ} (ha : 0 ≤ a)
    (f : C(Set.Icc (0 : ℝ) a, E)) : C(Set.Icc (0 : ℝ) T, E) :=
  f.comp ⟨fun t => ⟨min t.1 a, le_min t.2.1 ha, min_le_right _ _⟩, by fun_prop⟩

/-- Stop a continuous path at `a`, with the same clamped-time convention as `Skorokhod.stop`. -/
def stopContinuous (a : ℝ) (f : C(Set.Icc (0 : ℝ) T, E)) : C(Set.Icc (0 : ℝ) T, E) :=
  f.comp ⟨fun t => ⟨max 0 (min t.1 a), le_max_left _ _,
    max_le (t.2.1.trans t.2.2) ((min_le_left _ _).trans t.2.2)⟩, by fun_prop⟩

/-- Restricting a continuous path to an initial interval is `1`-Lipschitz. -/
theorem lipschitzWith_one_restrictContinuous {a : ℝ} (haT : a ≤ T) :
    LipschitzWith 1 (restrictContinuous (T := T) (E := E) haT) := by
  apply LipschitzWith.mk_one
  intro f g
  rw [ContinuousMap.dist_eq_iSup]
  apply Real.iSup_le
  · intro t
    exact ContinuousMap.dist_apply_le_dist
      (f := f) (g := g) ⟨(t : ℝ), t.2.1, t.2.2.trans haT⟩
  · exact dist_nonneg

/-- Constant extension of a continuous path is `1`-Lipschitz. -/
theorem lipschitzWith_one_extendContinuous {a : ℝ} (ha : 0 ≤ a) :
    LipschitzWith 1 (extendContinuous (T := T) (E := E) ha) := by
  apply LipschitzWith.mk_one
  intro f g
  rw [ContinuousMap.dist_eq_iSup]
  apply Real.iSup_le
  · intro t
    exact ContinuousMap.dist_apply_le_dist
      (f := f) (g := g) ⟨min (t : ℝ) a, le_min t.2.1 ha, min_le_right _ _⟩
  · exact dist_nonneg

/-- Stopping a continuous path is `1`-Lipschitz. -/
theorem lipschitzWith_one_stopContinuous (a : ℝ) :
    LipschitzWith 1 (stopContinuous (T := T) (E := E) a) := by
  apply LipschitzWith.mk_one
  intro f g
  rw [ContinuousMap.dist_eq_iSup]
  apply Real.iSup_le
  · intro t
    exact ContinuousMap.dist_apply_le_dist (f := f) (g := g)
      ⟨max 0 (min (t : ℝ) a), le_max_left _ _,
        max_le (t.2.1.trans t.2.2) ((min_le_left _ _).trans t.2.2)⟩
  · exact dist_nonneg

private theorem stopContinuous_eq_extendContinuous_restrictContinuous {a : ℝ}
    (ha : 0 ≤ a) (haT : a ≤ T) (f : C(Set.Icc (0 : ℝ) T, E)) :
    stopContinuous a f = extendContinuous ha (restrictContinuous haT f) := by
  ext t
  apply congrArg f
  apply Subtype.ext
  exact max_eq_right (le_min t.2.1 ha)

private theorem ofContinuous_stopContinuous (a : ℝ) (f : C(Set.Icc (0 : ℝ) T, E)) :
    ofContinuous (stopContinuous a f) = stop a (ofContinuous f) := rfl

private theorem tendsto_stopContinuous (hT : 0 < T) {a : ℕ → ℝ}
    (_ha0 : ∀ k, 0 ≤ a k) (haT : ∀ k, a k < T) (hlim : Tendsto a atTop (𝓝 T))
    (f : C(Set.Icc (0 : ℝ) T, E)) :
    Tendsto (fun k => stopContinuous (a k) f) atTop (𝓝 f) := by
  apply (isClosedEmbedding_ofContinuous (T := T) (E := E)).isEmbedding.tendsto_nhds_iff.mpr
  have haLT : Tendsto a atTop (𝓝[<] T) :=
    tendsto_nhdsWithin_iff.mpr ⟨hlim, Filter.Eventually.of_forall haT⟩
  have h := (tendsto_stop_nhdsLT hT (f := ofContinuous f)
    f.continuous.continuousAt).comp haLT
  simpa only [Function.comp_def, ofContinuous_stopContinuous] using h

private theorem map_extendContinuous_restrictContinuous
    (P : ProbabilityMeasure C(Set.Icc (0 : ℝ) T, E)) {a : ℝ} (ha : 0 ≤ a) (haT : a ≤ T) :
    (P.map (restrictContinuous haT)).map (extendContinuous ha) = P.map (stopContinuous a) := by
  apply Subtype.ext
  change Measure.map (extendContinuous ha) (Measure.map (restrictContinuous haT)
    (P : Measure C(Set.Icc (0 : ℝ) T, E))) =
      Measure.map (stopContinuous a) (P : Measure C(Set.Icc (0 : ℝ) T, E))
  rw [Measure.map_map (lipschitzWith_one_extendContinuous ha).continuous.measurable
    (lipschitzWith_one_restrictContinuous haT).continuous.measurable]
  congr 1
  funext f
  exact (stopContinuous_eq_extendContinuous_restrictContinuous ha haT f).symm

/-- **C7 in `C_T`.**  Stopping at `a` is controlled by the uniform oscillation after `a`. -/
theorem dist_stopContinuous_le {a : ℝ} (ha : 0 ≤ a) (haT : a ≤ T)
    (f : C(Set.Icc (0 : ℝ) T, E)) :
    dist (stopContinuous a f) f ≤ ⨆ s : {s : Set.Icc (0 : ℝ) T // a ≤ (s : ℝ)},
      dist (f s) (f ⟨a, ha, haT⟩) := by
  let a' : Set.Icc (0 : ℝ) T := ⟨a, ha, haT⟩
  let c : D T E := ⟨fun _ => f a', IsCadlag.const⟩
  have hbdd : BddAbove (Set.range fun s : {s : Set.Icc (0 : ℝ) T // a ≤ (s : ℝ)} =>
      dist (f s) (f a')) := by
    obtain ⟨C, hC⟩ := bddAbove_range_dist (ofContinuous f) c (OrderIso.refl _)
    refine ⟨C, ?_⟩
    rintro x ⟨s, rfl⟩
    exact hC ⟨s, rfl⟩
  let osc := ⨆ s : {s : Set.Icc (0 : ℝ) T // a ≤ (s : ℝ)}, dist (f s) (f a')
  have hosc : 0 ≤ osc := le_ciSup_of_le hbdd ⟨a', le_rfl⟩ dist_nonneg
  rw [ContinuousMap.dist_eq_iSup]
  apply Real.iSup_le _ hosc
  intro t
  by_cases hta : a ≤ (t : ℝ)
  · have hstop : (stopContinuous a f) t = f a' := by
      apply congrArg f
      apply Subtype.ext
      change max 0 (min (t : ℝ) a) = a
      rw [min_eq_right hta, max_eq_right ha]
    rw [hstop]
    exact (dist_comm (f a') (f t)).trans_le (le_ciSup hbdd ⟨t, hta⟩)
  · have hta' : (t : ℝ) < a := lt_of_not_ge hta
    have hstop : (stopContinuous a f) t = f t := by
      apply congrArg f
      apply Subtype.ext
      change max 0 (min (t : ℝ) a) = t
      rw [min_eq_left hta'.le, max_eq_right t.2.1]
    rw [hstop, dist_self]
    exact hosc

/-- **C11 item 2 in `C_T`.**  Convergence of continuous prefixes and terminal oscillation control
imply convergence in law on the full continuous path space. -/
theorem tendsto_continuous_of_tendsto_restrict_of_oscillation {Ω : ℕ → Type*}
    [∀ n, MeasurableSpace (Ω n)] [TopologicalSpace.SeparableSpace E]
    (μ : (n : ℕ) → ProbabilityMeasure (Ω n))
    {Y : (n : ℕ) → Ω n → C(Set.Icc (0 : ℝ) T, E)} (hY : ∀ n, Measurable (Y n))
    {ν : ProbabilityMeasure C(Set.Icc (0 : ℝ) T, E)} (hT : 0 < T) {a : ℕ → ℝ}
    (ha0 : ∀ k, 0 ≤ a k) (haT : ∀ k, a k < T) (hlim : Tendsto a atTop (𝓝 T))
    (hpre : ∀ k, Tendsto (fun n => (μ n).map (restrictContinuous (haT k).le ∘ Y n)) atTop
      (𝓝 (ν.map (restrictContinuous (haT k).le))))
    (hosc : ∀ η > 0, Tendsto (fun k => limsup (fun n => (μ n : Measure (Ω n)).real
      {ω | η < ⨆ s : {s : Set.Icc (0 : ℝ) T // a k ≤ (s : ℝ)},
        dist (Y n ω s) (Y n ω ⟨a k, ha0 k, (haT k).le⟩)}) atTop) atTop (𝓝 0)) :
    Tendsto (fun n => (μ n).map (Y n)) atTop (𝓝 ν) := by
  refine BGW.Probability.tendsto_of_tendsto_approx μ hY
    (X := fun k n => stopContinuous (a k) ∘ Y n) (Z := fun k => ν.map (stopContinuous (a k)))
    ?_ ?_ ?_ ?_
  · intro k n
    exact (lipschitzWith_one_stopContinuous (a k)).continuous.measurable.comp (hY n)
  · intro k
    have hm := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
      (fun n => (μ n).map (restrictContinuous (haT k).le ∘ Y n))
      (ν.map (restrictContinuous (haT k).le)) (hpre k)
      (lipschitzWith_one_extendContinuous (T := T) (ha0 k)).continuous
    have hleft (n : ℕ) :
        ((μ n).map (restrictContinuous (haT k).le ∘ Y n)).map
          (extendContinuous (T := T) (ha0 k)) = (μ n).map (stopContinuous (a k) ∘ Y n) := by
      apply Subtype.ext
      change Measure.map (extendContinuous (T := T) (ha0 k))
        (Measure.map (restrictContinuous (haT k).le ∘ Y n) (μ n : Measure (Ω n))) =
        Measure.map (stopContinuous (a k) ∘ Y n) (μ n : Measure (Ω n))
      rw [Measure.map_map
        (lipschitzWith_one_extendContinuous (T := T) (ha0 k)).continuous.measurable
        ((lipschitzWith_one_restrictContinuous (haT k).le).continuous.measurable.comp (hY n))]
      congr 1
      funext ω
      exact (stopContinuous_eq_extendContinuous_restrictContinuous
        (ha0 k) (haT k).le (Y n ω)).symm
    have hright := map_extendContinuous_restrictContinuous ν (ha0 k) (haT k).le
    simpa only [hleft, hright] using hm
  · rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
    intro φ
    have hmeas (k : ℕ) : AEMeasurable (stopContinuous (a k))
        (ν : Measure C(Set.Icc (0 : ℝ) T, E)) :=
      (lipschitzWith_one_stopContinuous (a k)).continuous.measurable.aemeasurable
    simp_rw [ProbabilityMeasure.toMeasure_map,
      integral_map (hmeas _) φ.continuous.aestronglyMeasurable]
    apply tendsto_integral_of_dominated_convergence (fun _ => ‖φ‖)
    · intro k
      exact (φ.continuous.measurable.comp
        (lipschitzWith_one_stopContinuous (a k)).continuous.measurable).aestronglyMeasurable
    · exact integrable_const _
    · intro k
      exact Filter.Eventually.of_forall fun f => φ.norm_coe_le_norm (stopContinuous (a k) f)
    · exact Filter.Eventually.of_forall fun f => φ.continuous.continuousAt.tendsto.comp
        (tendsto_stopContinuous hT ha0 haT hlim f)
  · intro ε hε
    apply squeeze_zero (g := fun k => limsup (fun n => (μ n : Measure (Ω n)).real
      {ω | ε / 2 < ⨆ s : {s : Set.Icc (0 : ℝ) T // a k ≤ (s : ℝ)},
        dist (Y n ω s) (Y n ω ⟨a k, ha0 k, (haT k).le⟩)}) atTop)
    · intro k
      exact le_limsup_of_frequently_le
        (Filter.Frequently.of_forall fun n => measureReal_nonneg)
        (isBoundedUnder_of ⟨1, fun n => measureReal_le_one⟩)
    · intro k
      apply Filter.limsup_le_limsup
      · exact Filter.Eventually.of_forall fun n => measureReal_mono (by
          intro ω hω
          change ε ≤ dist (stopContinuous (a k) (Y n ω)) (Y n ω) at hω
          change ε / 2 < ⨆ s : {s : Set.Icc (0 : ℝ) T // a k ≤ (s : ℝ)},
            dist (Y n ω s) (Y n ω ⟨a k, ha0 k, (haT k).le⟩)
          have hd := dist_stopContinuous_le (ha0 k) (haT k).le (Y n ω)
          linarith)
      · exact Filter.isCoboundedUnder_le_of_le atTop fun n => measureReal_nonneg
      · exact isBoundedUnder_of ⟨1, fun n => measureReal_le_one⟩
    · exact hosc (ε / 2) (by positivity)

/-- The wrap time `1 - g`, viewed as a point of `[0,1]`. -/
noncomputable def vervaatWrapTime (f : D 1 ℝ) : Set.Icc (0 : ℝ) 1 :=
  Set.projIcc 0 1 zero_le_one (1 - (vervaatTime f : ℝ))

private theorem vervaatWrapTime_val (f : D 1 ℝ) :
    (vervaatWrapTime f : ℝ) = 1 - (vervaatTime f : ℝ) := by
  rw [vervaatWrapTime, projIcc_of_mem zero_le_one]
  constructor <;> linarith [(vervaatTime f).2.1, (vervaatTime f).2.2]

private theorem leftLim_vervaatD_of_le (f : D 1 ℝ) (t : Set.Icc (0 : ℝ) 1)
    (ht0 : 0 < (t : ℝ)) (ht : (vervaatTime f : ℝ) + t ≤ 1) :
    Function.leftLim (vervaatD f) t =
      Function.leftLim f (Set.projIcc 0 1 zero_le_one ((vervaatTime f : ℝ) + t)) -
        ⨅ s, f s := by
  let _ : (𝓝[<] t).NeBot := nhdsLT_neBot_of_exists_lt
    ⟨⟨0, le_rfl, zero_le_one⟩, ht0⟩
  let A : Set.Icc (0 : ℝ) 1 → Set.Icc (0 : ℝ) 1 :=
    fun s => Set.projIcc 0 1 zero_le_one ((vervaatTime f : ℝ) + s)
  have hA : Continuous A := continuous_projIcc.comp
    (continuous_const.add continuous_subtype_val)
  have hAleft : Tendsto A (𝓝[<] t) (𝓝[<] A t) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨hA.continuousAt.tendsto.mono_left nhdsWithin_le_nhds, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hst : (s : ℝ) < t := hs
    have hsumt : (vervaatTime f : ℝ) + t ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨add_nonneg (vervaatTime f).2.1 t.2.1, ht⟩
    have hsums : (vervaatTime f : ℝ) + s ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨add_nonneg (vervaatTime f).2.1 s.2.1, by linarith⟩
    change Set.projIcc 0 1 zero_le_one ((vervaatTime f : ℝ) + s) <
      Set.projIcc 0 1 zero_le_one ((vervaatTime f : ℝ) + t)
    rw [projIcc_of_mem zero_le_one hsums, projIcc_of_mem zero_le_one hsumt]
    change (vervaatTime f : ℝ) + s < (vervaatTime f : ℝ) + t
    linarith
  apply leftLim_eq_of_tendsto
  have hlim := (((isCadlag f).tendsto_nhdsLT_leftLim (A t)).comp hAleft).sub_const
    (⨅ s, f s)
  apply (tendsto_congr' ?_).2 hlim
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hst : (s : ℝ) < t := hs
  exact ite_eq_left (by linarith)

private theorem leftLim_vervaatD_of_gt (f : D 1 ℝ) (t : Set.Icc (0 : ℝ) 1)
    (ht0 : 0 < (t : ℝ)) (ht : 1 < (vervaatTime f : ℝ) + t) :
    Function.leftLim (vervaatD f) t =
      Function.leftLim f (Set.projIcc 0 1 zero_le_one ((vervaatTime f : ℝ) + t - 1)) +
        f ⟨1, zero_le_one, le_rfl⟩ - (⨅ s, f s) - f ⟨0, le_rfl, zero_le_one⟩ := by
  let _ : (𝓝[<] t).NeBot := nhdsLT_neBot_of_exists_lt
    ⟨⟨0, le_rfl, zero_le_one⟩, ht0⟩
  let B : Set.Icc (0 : ℝ) 1 → Set.Icc (0 : ℝ) 1 :=
    fun s => Set.projIcc 0 1 zero_le_one ((vervaatTime f : ℝ) + s - 1)
  have hB : Continuous B := continuous_projIcc.comp
    ((continuous_const.add continuous_subtype_val).sub continuous_const)
  have hBleft : Tendsto B (𝓝[<] t) (𝓝[<] B t) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨hB.continuousAt.tendsto.mono_left nhdsWithin_le_nhds, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hst : (s : ℝ) < t := hs
    have hsumt : (vervaatTime f : ℝ) + t - 1 ∈ Set.Icc (0 : ℝ) 1 := by
      constructor <;> linarith [(vervaatTime f).2.2, t.2.2]
    change max 0 (min 1 ((vervaatTime f : ℝ) + s - 1)) <
      (Set.projIcc 0 1 zero_le_one ((vervaatTime f : ℝ) + t - 1) : ℝ)
    rw [projIcc_of_mem zero_le_one hsumt]
    change max 0 (min 1 ((vervaatTime f : ℝ) + s - 1)) <
      (vervaatTime f : ℝ) + t - 1
    apply max_lt (by linarith)
    exact (min_le_right _ _).trans_lt (by linarith)
  apply leftLim_eq_of_tendsto
  have hlim := ((((isCadlag f).tendsto_nhdsLT_leftLim (B t)).comp hBleft).add_const
    (f ⟨1, zero_le_one, le_rfl⟩)).sub_const (⨅ s, f s) |>.sub_const
      (f ⟨0, le_rfl, zero_le_one⟩)
  apply (tendsto_congr' ?_).2 hlim
  have he : ∀ᶠ s : Set.Icc (0 : ℝ) 1 in 𝓝[<] t,
      1 < (vervaatTime f : ℝ) + s :=
    ((continuous_const.add continuous_subtype_val).continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds).eventually (eventually_gt_nhds ht)
  exact he.mono fun s hs => ite_eq_right hs.not_ge

/-- Value of the Vervaat transform at its wrap time. -/
theorem vervaatD_wrap (f : D 1 ℝ) :
    vervaatD f (vervaatWrapTime f) = f ⟨1, zero_le_one, le_rfl⟩ - ⨅ s, f s := by
  change (if (vervaatTime f : ℝ) + vervaatWrapTime f ≤ 1 then _ else _) = _
  rw [ite_eq_left (by rw [vervaatWrapTime_val]; linarith)]
  rw [show (vervaatTime f : ℝ) + vervaatWrapTime f = 1 by
    rw [vervaatWrapTime_val]; ring, projIcc_right]

/-- Left limit of the Vervaat transform at its wrap time. -/
theorem leftLim_vervaatD_wrap (f : D 1 ℝ) (hc : 0 < (vervaatWrapTime f : ℝ)) :
    Function.leftLim (vervaatD f) (vervaatWrapTime f) =
      Function.leftLim f ⟨1, zero_le_one, le_rfl⟩ - ⨅ s, f s := by
  rw [leftLim_vervaatD_of_le f (vervaatWrapTime f) hc (by
    rw [vervaatWrapTime_val]; linarith)]
  rw [show (vervaatTime f : ℝ) + vervaatWrapTime f = 1 by
    rw [vervaatWrapTime_val]; ring, projIcc_right]

/-- **C33 item 3b.**  The signed jump at the wrap is `f(1) - f(1-)`. -/
theorem vervaatD_wrap_sub_leftLim (f : D 1 ℝ) (hc : 0 < (vervaatWrapTime f : ℝ)) :
    vervaatD f (vervaatWrapTime f) - Function.leftLim (vervaatD f) (vervaatWrapTime f) =
      f ⟨1, zero_le_one, le_rfl⟩ - Function.leftLim f ⟨1, zero_le_one, le_rfl⟩ := by
  rw [vervaatD_wrap, leftLim_vervaatD_wrap f hc]
  ring

/-- **C33 item 3b, localization** (audit g3, finding 2): away from the wrap time, the jump of the
Vervaat transform at `t > 0` is the jump of `f` at the rotated time `g + t` (mod 1). -/
theorem vervaatD_jump_of_ne_wrap (f : D 1 ℝ) (t : Set.Icc (0 : ℝ) 1) (ht0 : 0 < (t : ℝ))
    (htc : t ≠ vervaatWrapTime f) :
    vervaatD f t - Function.leftLim (vervaatD f) t =
      f (Set.projIcc 0 1 zero_le_one (if (vervaatTime f : ℝ) + t < 1
          then (vervaatTime f : ℝ) + t else (vervaatTime f : ℝ) + t - 1)) -
        Function.leftLim f (Set.projIcc 0 1 zero_le_one (if (vervaatTime f : ℝ) + t < 1
          then (vervaatTime f : ℝ) + t else (vervaatTime f : ℝ) + t - 1)) := by
  by_cases ht : (vervaatTime f : ℝ) + t < 1
  · simp only [ite_eq_left ht]
    rw [leftLim_vervaatD_of_le f t ht0 ht.le]
    change (if (vervaatTime f : ℝ) + t ≤ 1 then _ else _) - _ = _
    rw [ite_eq_left ht.le]
    ring
  · have htgt : 1 < (vervaatTime f : ℝ) + t := by
      have hge : 1 ≤ (vervaatTime f : ℝ) + t := le_of_not_gt ht
      apply lt_of_le_of_ne hge
      intro heq
      apply htc
      apply Subtype.ext
      rw [vervaatWrapTime_val]
      linarith
    simp only [ite_eq_right ht]
    rw [leftLim_vervaatD_of_gt f t ht0 htgt]
    change (if (vervaatTime f : ℝ) + t ≤ 1 then _ else _) - _ = _
    rw [ite_eq_right (not_le_of_gt htgt)]
    ring

/-- **C36, attainment.**  On a nonempty bounded time interval, `maxJump` is attained. -/
theorem exists_eq_maxJump (hT : 0 ≤ T) (f : D T ℝ) :
    ∃ t, max (f t - Function.leftLim f t) 0 = maxJump f := by
  let z : Set.Icc (0 : ℝ) T := ⟨0, le_rfl, hT⟩
  let _ : Nonempty (Set.Icc (0 : ℝ) T) := ⟨z⟩
  have hz : max (f z - Function.leftLim f z) 0 = 0 := by
    have hbot : IsBot z := fun t => t.2.1
    rw [leftLim_eq_of_isBot hbot, sub_self, max_eq_right le_rfl]
  by_cases hzero : maxJump f = 0
  · exact ⟨z, hz.trans hzero.symm⟩
  have hnonneg : 0 ≤ maxJump f := by
    unfold maxJump
    exact Real.iSup_nonneg fun t => le_max_right _ _
  have hpos : 0 < maxJump f := lt_of_le_of_ne hnonneg (Ne.symm hzero)
  let J : Set.Icc (0 : ℝ) T → ℝ := fun t => max (f t - Function.leftLim f t) 0
  let A : Set (Set.Icc (0 : ℝ) T) := {t | maxJump f / 2 < J t}
  have hA : A.Nonempty := by
    obtain ⟨t, ht⟩ := exists_lt_of_lt_ciSup (show maxJump f / 2 < ⨆ t, J t by
      change maxJump f / 2 < maxJump f
      linarith)
    exact ⟨t, ht⟩
  have hAfin : A.Finite := by
    apply (finite_setOf_jump_gt f (show 0 < maxJump f / 2 by linarith)).subset
    intro t ht
    change maxJump f / 2 < dist (Function.leftLim f t) (f t)
    change maxJump f / 2 < J t at ht
    have hle : J t ≤ |f t - Function.leftLim f t| :=
      max_le (le_abs_self _) (abs_nonneg _)
    exact ht.trans_le (by simpa only [Real.dist_eq, abs_sub_comm] using hle)
  obtain ⟨t, htA, htmax⟩ := Set.exists_max_image A J hAfin hA
  refine ⟨t, le_antisymm (le_ciSup (bddAbove_maxJump f) t) ?_⟩
  unfold maxJump
  apply Real.iSup_le
  · intro s
    by_cases hs : s ∈ A
    · exact htmax s hs
    · change J s ≤ J t
      have hst : J s ≤ maxJump f / 2 := le_of_not_gt hs
      have htt : maxJump f / 2 < J t := htA
      exact hst.trans htt.le
  · exact le_max_right _ _

/-- The exact meaning of `maxJump f = 0`: there are no upward jumps.  Downward jumps are
invisible to `maxJump`. -/
theorem maxJump_eq_zero_iff (f : D T ℝ) :
    maxJump f = 0 ↔ ∀ t, f t ≤ Function.leftLim f t := by
  constructor
  · intro h t
    let _ : Nonempty (Set.Icc (0 : ℝ) T) := ⟨t⟩
    have ht : max (f t - Function.leftLim f t) 0 ≤ maxJump f :=
      le_ciSup (bddAbove_maxJump f) t
    rw [h, max_le_iff] at ht
    exact sub_nonpos.mp ht.1
  · intro h
    apply le_antisymm
    · unfold maxJump
      apply Real.iSup_nonpos
      intro t
      exact max_le (sub_nonpos.mpr (h t)) le_rfl
    · unfold maxJump
      exact Real.iSup_nonneg fun t => le_max_right _ _

end BGW.Skorokhod
