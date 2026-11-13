/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.Skorokhod.DLoc
public import BGW.StableTrees.StableProcessLaw
public import BGW.StableTrees.StableProcessNoNegativeJumps
public import BGW.StableTrees.StableLevyLaw
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# The stable process as a law on local càdlàg paths

This module constructs the stable process law on `DLoc` from its compatible integer-horizon
marginals. It proves the characterization by compact restrictions and the coordinate properties
used downstream: initial value, fixed-time marginals and continuity, and simultaneous spectral
positivity (J. Bertoin, *Lévy Processes*, Cambridge University Press, 1996, Chapters I and VIII;
P. Billingsley, *Convergence of Probability Measures*, 2nd ed., Wiley, 1999, Section 16).
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped NNReal
open BGW.Skorokhod

/-- The zero local path. -/
def BGW.Skorokhod.DLoc.zero : DLoc := ⟨fun _ => 0, IsCadlag.const⟩

namespace BGW.StableTrees

/-- At horizon zero, the stable process law is the Dirac mass at the zero path. -/
theorem stableProcessLaw_zero (θ : ℝ) :
    (stableProcessLaw θ 0 : Measure (D 0 ℝ)) =
      Measure.dirac (Skorokhod.ofContinuous (ContinuousMap.const _ 0)) := by
  simp [stableProcessLaw]

/-- Compatibility of the integer-horizon stable process laws under restriction (the compatibility
hypothesis of `exists_unique_compatiblePathLaw`). -/
theorem stableProcessLaw_succ_restrict {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (n : ℕ) :
    (stableProcessLaw θ (((n + 1 : ℕ) : ℝ) + 1)).map
        (restrict (strictMono_succHorizon.monotone (Nat.le_succ n))) =
      stableProcessLaw θ ((n : ℝ) + 1) := by
  exact map_restrict_stableProcessLaw (θ := θ) (a := (n : ℝ) + 1)
      (T := (((n + 1 : ℕ) : ℝ) + 1)) hθ (by positivity) (by push_cast; linarith)

/-- **The local stable law.** For `1 < θ ≤ 2`: the unique law on `DLoc` whose integer-horizon
restrictions are `stableProcessLaw θ (n + 1)`, obtained from `exists_unique_compatiblePathLaw`
and transported along `measurableEquivCompatible.symm`. Junk value (Dirac at the zero path)
otherwise. -/
noncomputable def stableLocalLaw (θ : ℝ) : ProbabilityMeasure DLoc :=
  if hθ : 1 < θ ∧ θ ≤ 2 then
    (Classical.choose
        (exists_unique_compatiblePathLaw (fun n : ℕ => (n : ℝ) + 1) strictMono_succHorizon
          (fun n => by positivity) (fun n => stableProcessLaw θ ((n : ℝ) + 1))
          (fun n => stableProcessLaw_succ_restrict hθ n)).exists).map
      DLoc.measurableEquivCompatible.symm
  else ⟨Measure.dirac DLoc.zero, inferInstance⟩

private theorem map_restrict_succ_stableLocalLaw_aux {θ : ℝ}
    (hθ : 1 < θ ∧ θ ≤ 2) (n : ℕ) :
    (stableLocalLaw θ : Measure DLoc).map
        (DLoc.restrict ((n : ℝ≥0) + 1)) =
      (stableProcessLaw θ (((n : ℝ≥0) + 1 : ℝ≥0) : ℝ) :
        Measure (D (((n : ℝ≥0) + 1 : ℝ≥0) : ℝ) ℝ)) := by
  have hlaw : stableLocalLaw θ =
      (Classical.choose
        (exists_unique_compatiblePathLaw (fun n : ℕ => (n : ℝ) + 1) strictMono_succHorizon
          (fun n => by positivity) (fun n => stableProcessLaw θ ((n : ℝ) + 1))
          (fun n => stableProcessLaw_succ_restrict hθ n)).exists).map
        DLoc.measurableEquivCompatible.symm := by
    exact dite_eq_left hθ
  rw [hlaw, ProbabilityMeasure.toMeasure_map, Measure.map_map
    (DLoc.measurable_restrict _) DLoc.measurableEquivCompatible.symm.measurable]
  have hfun : DLoc.restrict ((n : ℝ≥0) + 1) ∘ DLoc.measurableEquivCompatible.symm =
      CompatiblePaths.coord n := by
    funext p
    apply BGW.Skorokhod.ext
    intro t
    exact DLoc.restrict_glue p n t
  rw [hfun]
  exact Classical.choose_spec
    (exists_unique_compatiblePathLaw (fun n : ℕ => (n : ℝ) + 1) strictMono_succHorizon
      (fun n => by positivity) (fun n => stableProcessLaw θ ((n : ℝ) + 1))
      (fun n => stableProcessLaw_succ_restrict hθ n)).exists n

/-- **Restriction.** The restriction of the local stable law to every positive real horizon
`T` is the compact stable process law `P_T`. -/
theorem map_restrict_stableLocalLaw {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {T : ℝ≥0}
    (hT : 0 < T) :
    (stableLocalLaw θ : Measure DLoc).map (DLoc.restrict T) =
      (stableProcessLaw θ (T : ℝ) : Measure (D (T : ℝ) ℝ)) := by
  let n : ℕ := ⌈(T : ℝ)⌉₊
  let N : ℝ≥0 := (n : ℝ≥0) + 1
  have hTN : T ≤ N := by
    have hle : (T : ℝ) ≤ (n : ℝ) := by
      dsimp [n]
      exact Nat.le_ceil _
    have hle' : (T : ℝ) ≤ (N : ℝ) := by
      dsimp [N]
      push_cast
      linarith
    exact_mod_cast hle'
  have hTpos : 0 < (T : ℝ) := hT
  calc
    (stableLocalLaw θ : Measure DLoc).map (DLoc.restrict T) =
        ((stableLocalLaw θ : Measure DLoc).map (DLoc.restrict N)).map
          (Skorokhod.restrict (show (T : ℝ) ≤ (N : ℝ) from hTN)) := by
      rw [Measure.map_map (measurable_restrict _) (DLoc.measurable_restrict _)]
      apply Measure.map_congr
      filter_upwards [] with f
      exact (DLoc.restrict_restrict hTN f).symm
    _ = ((stableProcessLaw θ (N : ℝ) : ProbabilityMeasure (D (N : ℝ) ℝ)) :
          Measure (D (N : ℝ) ℝ)).map
          (Skorokhod.restrict (show (T : ℝ) ≤ (N : ℝ) from hTN)) := by
      have h := map_restrict_succ_stableLocalLaw_aux hθ n
      exact congrArg (Measure.map
        (Skorokhod.restrict (show (T : ℝ) ≤ (N : ℝ) from hTN))) h
    _ = (stableProcessLaw θ (T : ℝ) : Measure (D (T : ℝ) ℝ)) := by
      exact congrArg ProbabilityMeasure.toMeasure
        (map_restrict_stableProcessLaw hθ hTpos
          (show (T : ℝ) ≤ (N : ℝ) from hTN))

/-- Junk branch of the definition. -/
theorem stableLocalLaw_of_not {θ : ℝ} (hθ : ¬ (1 < θ ∧ θ ≤ 2)) :
    stableLocalLaw θ = ⟨Measure.dirac DLoc.zero, inferInstance⟩ := by
  exact dite_eq_right hθ

/-- The same statement in `ProbabilityMeasure` form. -/
theorem stableLocalLaw_restrict {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {T : ℝ≥0} (hT : 0 < T) :
    (stableLocalLaw θ).map (DLoc.restrict T) =
      stableProcessLaw θ (T : ℝ) := by
  apply Subtype.ext
  exact map_restrict_stableLocalLaw hθ hT

private theorem map_restrict_eq_of_map_restrict_aux {μ ν : Measure DLoc} {a T : ℝ≥0}
    (haT : a ≤ T) (h : μ.map (DLoc.restrict T) = ν.map (DLoc.restrict T)) :
    μ.map (DLoc.restrict a) = ν.map (DLoc.restrict a) := by
  calc
    μ.map (DLoc.restrict a) = (μ.map (DLoc.restrict T)).map
        (Skorokhod.restrict (show (a : ℝ) ≤ (T : ℝ) from haT)) := by
      rw [Measure.map_map (BGW.Skorokhod.measurable_restrict _)
        (DLoc.measurable_restrict _)]
      apply Measure.map_congr
      filter_upwards [] with f
      exact (DLoc.restrict_restrict haT f).symm
    _ = (ν.map (DLoc.restrict T)).map
        (Skorokhod.restrict (show (a : ℝ) ≤ (T : ℝ) from haT)) := by rw [h]
    _ = ν.map (DLoc.restrict a) := by
      rw [Measure.map_map (BGW.Skorokhod.measurable_restrict _)
        (DLoc.measurable_restrict _)]
      apply Measure.map_congr
      filter_upwards [] with f
      exact DLoc.restrict_restrict haT f

/-- Uniqueness, restricted to the integer horizons (the form used with
`exists_unique_compatiblePathLaw`). -/
theorem eq_stableLocalLaw_of_forall_nat {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    {Q : ProbabilityMeasure DLoc}
    (h : ∀ n : ℕ, (Q : Measure DLoc).map (DLoc.restrict ((n : ℝ≥0) + 1)) =
      (stableProcessLaw θ (((n : ℝ≥0) + 1 : ℝ≥0) : ℝ) :
        Measure (D (((n : ℝ≥0) + 1 : ℝ≥0) : ℝ) ℝ))) :
    Q = stableLocalLaw θ := by
  apply ProbabilityMeasure.toMeasure_injective
  apply DLoc.measure_ext_of_restrict
  intro n
  cases n with
  | zero =>
      apply map_restrict_eq_of_map_restrict_aux
        (T := ((0 : ℕ) : ℝ≥0) + 1) (by simp)
      exact (h 0).trans (map_restrict_succ_stableLocalLaw_aux hθ 0).symm
  | succ n =>
      have hcast : ((n + 1 : ℕ) : ℝ≥0) = (n : ℝ≥0) + 1 := by norm_num
      rw [hcast]
      exact (h n).trans (map_restrict_succ_stableLocalLaw_aux hθ n).symm

/-- **Characterization and uniqueness.** A law on `DLoc` is the local stable law iff its
restriction to every positive horizon is the stable process law. -/
theorem eq_stableLocalLaw_iff {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {Q : ProbabilityMeasure DLoc} :
    Q = stableLocalLaw θ ↔
      ∀ T : ℝ≥0, 0 < T →
        (Q : Measure DLoc).map (DLoc.restrict T) =
          (stableProcessLaw θ (T : ℝ) : Measure (D (T : ℝ) ℝ)) := by
  constructor
  · rintro rfl T hT
    exact map_restrict_stableLocalLaw hθ hT
  · intro h
    apply ProbabilityMeasure.toMeasure_injective
    apply DLoc.measure_ext_of_restrict
    intro n
    cases n with
    | zero =>
        apply map_restrict_eq_of_map_restrict_aux
          (T := ((0 : ℕ) : ℝ≥0) + 1) (by simp)
        have h0 := h (((0 : ℕ) : ℝ≥0) + 1) (by simp)
        have hs0 := map_restrict_succ_stableLocalLaw_aux hθ 0
        exact h0.trans hs0.symm
    | succ n =>
        have hcast : ((n + 1 : ℕ) : ℝ≥0) = (n : ℝ≥0) + 1 := by norm_num
        rw [hcast]
        have hn := h ((n : ℝ≥0) + 1) (by positivity)
        have hsn := map_restrict_succ_stableLocalLaw_aux hθ n
        exact hn.trans hsn.symm

private theorem ae_eval_zero_stableLocalLaw_aux {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f : DLoc ∂(stableLocalLaw θ : Measure DLoc), f.1 0 = 0 := by
  have hT : 0 < (((((0 : ℕ) : ℝ≥0) + 1 : ℝ≥0) : ℝ)) := by positivity
  have hcomp := ae_eval_zero_stableProcessLaw hθ hT
  have hlaw := map_restrict_succ_stableLocalLaw_aux hθ 0
  rw [← hlaw] at hcomp
  rw [ae_map_iff (DLoc.measurable_restrict _).aemeasurable
    (p := fun g : D (((((0 : ℕ) : ℝ≥0) + 1 : ℝ≥0) : ℝ)) ℝ =>
      g ⟨0, le_rfl, hT.le⟩ = 0)
    (measurableSet_eq_fun (BGW.Skorokhod.measurable_eval _) measurable_const)] at hcomp
  filter_upwards [hcomp] with f hf
  exact hf

/-- Restriction to horizon zero: the zero-path Dirac mass, i.e. `stableProcessLaw θ 0`. -/
theorem map_restrict_zero_stableLocalLaw {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    (stableLocalLaw θ : Measure DLoc).map (DLoc.restrict 0) =
      (stableProcessLaw θ 0 : Measure (D 0 ℝ)) := by
  let z : D (((0 : ℝ≥0) : ℝ)) ℝ := Skorokhod.ofContinuous (ContinuousMap.const _ 0)
  have hae : DLoc.restrict 0 =ᵐ[(stableLocalLaw θ : Measure DLoc)] (fun _ => z) := by
    filter_upwards [ae_eval_zero_stableLocalLaw_aux hθ] with f hf
    apply BGW.Skorokhod.ext
    intro t
    have ht : t = ⟨0, le_rfl, le_rfl⟩ := by
      apply Subtype.ext
      exact le_antisymm t.2.2 t.2.1
    subst t
    change f.1 0 = 0
    exact hf
  have hmain : (stableLocalLaw θ : Measure DLoc).map (DLoc.restrict 0) =
      Measure.dirac z := by
    rw [Measure.map_congr hae]
    simpa only [measure_univ, one_smul] using
      (Measure.map_const (stableLocalLaw θ : Measure DLoc) z)
  rw [stableProcessLaw_zero]
  exact hmain

/-- Fixed-time marginals: `X_t ∼ stableLawAt θ t` for `t > 0`. -/
theorem map_eval_stableLocalLaw {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {t : ℝ≥0} (ht : 0 < t) :
    (stableLocalLaw θ : Measure DLoc).map (DLoc.eval t) =
      (stableLawAt θ (t : ℝ) : Measure ℝ) := by
  let T : ℝ≥0 := t + 1
  have htT : t ≤ T := by simp [T]
  have hTnn : 0 < T := ht.trans_le htT
  have hT : 0 < (T : ℝ) := hTnn
  let t' : Set.Icc (0 : ℝ) (T : ℝ) := ⟨t, t.2, htT⟩
  have ht' : 0 < (t' : ℝ) := ht
  have hfun : DLoc.eval t = (fun g : D (T : ℝ) ℝ => g t') ∘ DLoc.restrict T := by
    funext f
    rfl
  rw [hfun, ← Measure.map_map (BGW.Skorokhod.measurable_eval t')
    (DLoc.measurable_restrict T), map_restrict_stableLocalLaw hθ hTnn]
  exact map_eval_stableProcessLaw hθ hT t' ht'

private theorem continuousAt_of_restrict_aux {f : DLoc} {t T : ℝ≥0} (htT : t < T)
    (h : ContinuousAt (DLoc.restrict T f)
      ⟨t, t.2, (show (t : ℝ) ≤ (T : ℝ) from htT.le)⟩) :
    ContinuousAt f.1 t := by
  let t' : Set.Icc (0 : ℝ) (T : ℝ) := ⟨t, t.2, htT.le⟩
  rw [Metric.continuousAt_iff] at h ⊢
  intro ε hε
  obtain ⟨δ, hδ, hδf⟩ := h ε hε
  refine ⟨min δ ((T : ℝ) - (t : ℝ)), lt_min hδ (sub_pos.mpr htT), ?_⟩
  intro u hu
  have huδ : dist u t < δ := hu.trans_le (min_le_left _ _)
  have huTdist : dist u t < (T : ℝ) - (t : ℝ) := hu.trans_le (min_le_right _ _)
  have huT : u < T := by
    have hu_abs : |(u : ℝ) - (t : ℝ)| < (T : ℝ) - (t : ℝ) := by
      simpa only [NNReal.dist_eq, Real.dist_eq] using huTdist
    have huT' : (u : ℝ) < (T : ℝ) := by
      have hh := (abs_lt.mp hu_abs).2
      linarith
    exact_mod_cast huT'
  let u' : Set.Icc (0 : ℝ) (T : ℝ) := ⟨u, u.2, huT.le⟩
  have hu' : dist u' t' < δ := by
    simpa [u', t', Subtype.dist_eq, NNReal.dist_eq, Real.dist_eq] using huδ
  exact hδf hu'

/-- The local stable process starts at `0` almost surely. -/
theorem ae_eval_zero_stableLocalLaw {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f : DLoc ∂(stableLocalLaw θ : Measure DLoc), f.1 0 = 0 :=
  ae_eval_zero_stableLocalLaw_aux hθ

/-- No fixed discontinuities: for each deterministic time `t`, almost surely the path is continuous
at `t` (at `t = 0` this is right-continuity in `ℝ≥0`). -/
theorem ae_continuousAt_stableLocalLaw {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (t : ℝ≥0) :
    ∀ᵐ f : DLoc ∂(stableLocalLaw θ : Measure DLoc), ContinuousAt f.1 t := by
  let T : ℝ≥0 := t + 1
  have htT : t < T := by simp [T]
  have hTnn : 0 < T := by simp [T]
  have hT : 0 < (T : ℝ) := hTnn
  let t' : Set.Icc (0 : ℝ) (T : ℝ) := ⟨t, t.2, htT.le⟩
  have hcomp := ae_continuousAt_stableProcessLaw hθ hT t'
  rw [← map_restrict_stableLocalLaw hθ hTnn] at hcomp
  have hcomp' := ae_of_ae_map (DLoc.measurable_restrict T).aemeasurable hcomp
  filter_upwards [hcomp'] with f hf
  exact continuousAt_of_restrict_aux htT hf

private theorem leftLim_restrict_aux {f : DLoc} {t T : ℝ≥0} (ht : 0 < t) (htT : t < T) :
    Function.leftLim (DLoc.restrict T f)
      ⟨t, t.2, (show (t : ℝ) ≤ (T : ℝ) from htT.le)⟩ = Function.leftLim f.1 t := by
  let t' : Set.Icc (0 : ℝ) (T : ℝ) := ⟨t, t.2, htT.le⟩
  let inc : Set.Icc (0 : ℝ) (T : ℝ) → ℝ≥0 := fun u => ⟨u, u.2.1⟩
  have hinc : Continuous inc := Continuous.subtype_mk continuous_subtype_val fun u => u.2.1
  have hleft : Tendsto inc (𝓝[<] t') (𝓝[<] t) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨tendsto_nhdsWithin_of_tendsto_nhds hinc.continuousAt, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with u hu
    change (u : ℝ) < (t : ℝ) at hu
    exact hu
  let z : Set.Icc (0 : ℝ) (T : ℝ) := ⟨0, le_rfl, T.2⟩
  have hz : z < t' := by
    change (0 : ℝ) < (t : ℝ)
    exact ht
  have : (𝓝[<] t).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, ht⟩
  have : (𝓝[<] t').NeBot := nhdsLT_neBot_of_exists_lt ⟨z, hz⟩
  apply leftLim_eq_of_tendsto
  exact (f.2.tendsto_nhdsLT_leftLim t).comp hleft

/-- Spectral positivity, simultaneously at all times: almost surely, for every `t : ℝ≥0`,
the left limit does not exceed the value. -/
theorem ae_leftLim_le_stableLocalLaw {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f : DLoc ∂(stableLocalLaw θ : Measure DLoc),
      ∀ t : ℝ≥0, Function.leftLim f.1 t ≤ f.1 t := by
  have hall : ∀ᵐ f : DLoc ∂(stableLocalLaw θ : Measure DLoc),
      ∀ n : ℕ, ∀ s : Set.Icc (0 : ℝ) (((n : ℝ≥0) + 1 : ℝ≥0) : ℝ),
        Function.leftLim (DLoc.restrict ((n : ℝ≥0) + 1) f) s ≤
          (DLoc.restrict ((n : ℝ≥0) + 1) f) s := by
    apply ae_all_iff.mpr
    intro n
    have hT : 0 < (((n : ℝ≥0) + 1 : ℝ≥0) : ℝ) := by positivity
    have hcomp := ae_leftLim_le_stableProcessLaw hθ hT
    rw [← map_restrict_succ_stableLocalLaw_aux hθ n] at hcomp
    exact ae_of_ae_map (DLoc.measurable_restrict _).aemeasurable hcomp
  filter_upwards [hall] with f hf
  intro t
  by_cases ht0 : t = 0
  · subst t
    rw [leftLim_eq_of_isBot isBot_zero]
  · let n : ℕ := ⌈(t : ℝ)⌉₊
    let T : ℝ≥0 := (n : ℝ≥0) + 1
    have htT : t < T := by
      have hceil : (t : ℝ) ≤ (n : ℝ) := by
        dsimp [n]
        exact Nat.le_ceil _
      have htT' : (t : ℝ) < (T : ℝ) := by
        dsimp [T]
        push_cast
        linarith
      exact_mod_cast htT'
    let t' : Set.Icc (0 : ℝ) (T : ℝ) := ⟨t, t.2, htT.le⟩
    have htpos : 0 < t := lt_of_le_of_ne t.2 (Ne.symm ht0)
    have hle := hf n t'
    change Function.leftLim (DLoc.restrict T f) t' ≤ (DLoc.restrict T f) t' at hle
    rw [leftLim_restrict_aux htpos htT] at hle
    exact hle

end BGW.StableTrees
