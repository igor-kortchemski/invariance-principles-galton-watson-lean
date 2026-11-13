/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.MetricMeasure.RootedMeasuredGHSpace
public import BGW.MetricMeasure.RootedCommonSource
public import BGW.MetricMeasure.GHPFiniteApproximation
public import BGW.MetricMeasure.GHPFiniteCoding
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Separability of the existing rooted GHP metric

A finite net approximates the entire compact carrier, sends its probability
measure to the net, and sends its root to the chosen covering point. Rounded
distance and mass arrays, together with the finite index of this root, give
countably many codes. Equal codes control the actual rooted GHP distance.

The finite approximation costs at most three radii. Matching rooted finite
codes costs at most four radii: the common-source gluing contributes three,
and correcting the measure in the same target carrier contributes one.
Thus two approximations and the code comparison cost ten radii.

This proves second countability for the existing metric quotient, without
introducing another metric or discarding points of zero mass. The root need
not lie in the measure support. The finite-net and coding arguments adapt
`Freezing2/Geometry/GHPSeparability.lean` and `GHPFiniteCoding.lean` in
`igor-kortchemski/uniform-attachment-freezing-scaling-limits`, commit
`8bace72d36cdf7d250414f3d98acfaa415de23d9` (Apache-2.0).
-/

@[expose] public section

open MeasureTheory Metric Set TopologicalSpace
open scoped BigOperators

universe u

namespace BGW.MetricMeasure

private theorem rootedGHPDistance_finite_projection_le
    {X : Type u} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (s : Finset X)
    (q : X → ↥s) (hq : Measurable q) {ε : ℝ} (hε : 0 ≤ ε)
    (hclose : ∀ x, dist x (q x : X) ≤ ε) (x : X) :
    rootedGHPDistance μ (μ.map q) x (q x) ≤ 3 * ε := by
  classical
  have hH : hausdorffDist (range (id : X → X))
      (range (fun y : ↥s ↦ (y : X))) ≤ ε := by
    apply hausdorffDist_le_of_mem_dist hε
    · intro y _
      exact ⟨q y, ⟨q y, rfl⟩, hclose y⟩
    · intro y _
      exact ⟨y, ⟨y, rfl⟩, by simpa using hε⟩
  have hP : levyProkhorovDist (μ.map (id : X → X))
      ((μ.map q).map (fun y : ↥s ↦ (y : X))) ≤ ε := by
    rw [Measure.map_map measurable_subtype_coe hq]
    exact levyProkhorovDist_map_le_of_dist_le μ measurable_id
      (measurable_subtype_coe.comp hq) hε hclose
  have hG := rootedGHPDistance_le_of_isometries μ (μ.map q) x (q x) X id
    (fun y : ↥s ↦ (y : X)) isometry_id (Isometry.of_dist_eq fun _ _ ↦ rfl)
  have hb : borel X = ‹MeasurableSpace X› := BorelSpace.measurable_eq.symm
  apply hG.trans
  calc
    _ ≤ ε + (ε + ε) := by
      convert add_le_add (hclose x) (add_le_add hP hH) using 1
      rw [hb]
      rfl
    _ = 3 * ε := by ring

private theorem rootedGHPDistance_same_carrier_le
    {X : Type u} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X]
    (μ ν : Measure X) (x : X) :
    rootedGHPDistance μ ν x x ≤ levyProkhorovDist μ ν := by
  have h := rootedGHPDistance_le_of_isometries μ ν x x X id id isometry_id isometry_id
  have hb : borel X = ‹MeasurableSpace X› := BorelSpace.measurable_eq.symm
  apply h.trans
  apply le_of_eq
  rw [hb]
  simp only [id_eq, dist_self, Measure.map_id,
    hausdorffDist_self_zero, add_zero, zero_add]

private theorem rootedGHPDistance_le_of_finiteMeasuredCode_eq
    {X Y : Type u} [MetricSpace X] [MeasurableSpace X]
    [MetricSpace Y] [MeasurableSpace Y]
    [Fintype X] [Fintype Y] [Nonempty X] [BorelSpace X] [BorelSpace Y]
    (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {n : ℕ} (e : X ≃ Fin n) (f : Y ≃ Fin n) {ε : ℝ} (hε : 0 < ε)
    (hcode : finiteMeasuredCode μ e ε = finiteMeasuredCode ν f ε)
    (x : X) (y : Y) (hroot : e x = f y) :
    rootedGHPDistance μ ν x y ≤ 4 * ε := by
  classical
  let φ : X ≃ Y := e.trans f.symm
  have hφ : Measurable φ := measurable_of_countable _
  have hn : (0 : ℝ) < n := by
    have hcard : Fintype.card X = n := by simpa using Fintype.card_congr e
    rw [← hcard]
    exact_mod_cast Fintype.card_pos
  have hdist (a b : X) : |dist a b - dist (φ a) (φ b)| ≤ ε := by
    apply abs_sub_le_of_floor_div_eq hε
    have h := congrFun (congrFun (congrArg Prod.fst hcode) (e a)) (e b)
    simpa only [finiteMeasuredCode, Equiv.symm_apply_apply, φ, Equiv.trans_apply] using h
  have hmass (z : Y) : (μ.map φ).real {z} = μ.real {φ.symm z} := by
    have hpre : φ ⁻¹' {z} = {φ.symm z} := by
      ext a
      exact φ.eq_symm_apply.symm
    simp only [measureReal_def, Measure.map_apply hφ (measurableSet_singleton z), hpre]
  have hatom (z : Y) : |(μ.map φ).real {z} - ν.real {z}| ≤ ε / (n : ℝ) := by
    rw [hmass]
    apply abs_sub_le_of_floor_div_eq (div_pos hε hn)
    have h := congrFun (congrArg Prod.snd hcode) (f z)
    simpa only [finiteMeasuredCode, Equiv.symm_apply_apply, φ, Equiv.symm_trans_apply,
      Equiv.symm_symm] using h
  have hP : levyProkhorovDist (μ.map φ) ν ≤ ε := by
    have hcard : Fintype.card Y = n := by simpa using Fintype.card_congr f
    calc
      _ ≤ ∑ z, |(μ.map φ).real {z} - ν.real {z}| :=
        levyProkhorovDist_le_sum_atoms _ _
      _ ≤ ∑ _z : Y, ε / (n : ℝ) := Finset.sum_le_sum (fun z _ ↦ hatom z)
      _ = ε := by
        simp only [Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul]
        field_simp
  have hroot' : φ x = y := by
    change f.symm (e x) = y
    rw [hroot, f.symm_apply_apply]
  have hnear := rootedGHPDistance_map_le_of_distortion μ (id : X → X) φ
    measurable_id hφ Function.surjective_id φ.surjective hε
    (fun a b ↦ (hdist a b).trans (by linarith)) x
  simp only [Measure.map_id, id_eq, hroot'] at hnear
  have hfar := (rootedGHPDistance_same_carrier_le (μ.map φ) ν y).trans hP
  have htri := rootedGHPDistance_triangle μ (μ.map φ) ν x y y
  linarith

private theorem rootedGHPDistance_le_of_sigma_finiteMeasuredCode_eq
    {X Y : Type u} [MetricSpace X] [MeasurableSpace X]
    [MetricSpace Y] [MeasurableSpace Y]
    [Fintype X] [Fintype Y] [Nonempty X] [BorelSpace X] [BorelSpace Y]
    (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {n m : ℕ} (e : X ≃ Fin n) (f : Y ≃ Fin m) {ε : ℝ} (hε : 0 < ε)
    (x : X) (y : Y)
    (hcode : (⟨n, (finiteMeasuredCode μ e ε, e x)⟩ :
        Σ k : ℕ, ((Fin k → Fin k → ℤ) × (Fin k → ℤ)) × Fin k) =
      ⟨m, (finiteMeasuredCode ν f ε, f y)⟩) :
    rootedGHPDistance μ ν x y ≤ 4 * ε := by
  obtain ⟨hn, hc⟩ := Sigma.mk.inj_iff.mp hcode
  subst m
  have h := eq_of_heq hc
  exact rootedGHPDistance_le_of_finiteMeasuredCode_eq μ ν e f hε
    (congrArg Prod.fst h) x y (congrArg Prod.snd h)

namespace RootedMeasuredGHSpace

/-- Countable rounded distance, mass and root data determine a rooted class to any accuracy. -/
theorem exists_countable_discretization (δ : ℝ) (hδ : 0 < δ) :
    ∃ (β : Type) (_ : Encodable β) (F : RootedMeasuredGHSpace.{u} → β),
      ∀ p q, F p = F q → dist p q ≤ δ := by
  classical
  let ε : ℝ := δ / 10
  have hε : 0 < ε := div_pos hδ (by norm_num)
  let R : RootedMeasuredGHSpace.{u} → RootedCompactMeasuredSpace.{u} := fun p ↦ Quotient.out p
  have hR (p : RootedMeasuredGHSpace.{u}) : toRootedMeasuredGHSpace (R p) = p := Quotient.out_eq p
  have hnet (p : RootedMeasuredGHSpace.{u}) := exists_finite_measurable_net (X := (R p).space) hε
  choose s hs q hq hclose using hnet
  let (p : RootedMeasuredGHSpace.{u}) : Nonempty ↥(s p) :=
    ⟨⟨(hs p).choose, (hs p).choose_spec⟩⟩
  let ν (p : RootedMeasuredGHSpace.{u}) : Measure ↥(s p) :=
    ((R p).space.law : Measure (R p).space).map (q p)
  let E (p : RootedMeasuredGHSpace.{u}) : ↥(s p) ≃ Fin (Fintype.card ↥(s p)) := Fintype.equivFin _
  let F : RootedMeasuredGHSpace.{u} →
      Σ n : ℕ, ((Fin n → Fin n → ℤ) × (Fin n → ℤ)) × Fin n :=
    fun p ↦ ⟨Fintype.card ↥(s p), (finiteMeasuredCode (ν p) (E p) ε, E p (q p (R p).root))⟩
  refine ⟨_, inferInstance, F, ?_⟩
  intro p p' hpp'
  have hnear (z : RootedMeasuredGHSpace.{u}) :
      rootedGHPDistance ((R z).space.law : Measure (R z).space) (ν z)
        (R z).root (q z (R z).root) ≤ 3 * ε :=
    rootedGHPDistance_finite_projection_le _ (s z) (q z) (hq z) hε.le
      (fun x ↦ (hclose z x).le) (R z).root
  have hmid : rootedGHPDistance (ν p) (ν p') (q p (R p).root) (q p' (R p').root) ≤
      4 * ε :=
    rootedGHPDistance_le_of_sigma_finiteMeasuredCode_eq (ν p) (ν p') (E p) (E p') hε
      (q p (R p).root) (q p' (R p').root) hpp'
  have hlast : rootedGHPDistance (ν p') ((R p').space.law : Measure (R p').space)
      (q p' (R p').root) (R p').root ≤ 3 * ε := by
    rw [rootedGHPDistance_comm]
    exact hnear p'
  have htri := rootedGHPDistance_triangle ((R p).space.law : Measure (R p).space) (ν p)
    ((R p').space.law : Measure (R p').space) (R p).root (q p (R p).root) (R p').root
  have htri' := rootedGHPDistance_triangle (ν p) (ν p') ((R p').space.law : Measure (R p').space)
    (q p (R p).root) (q p' (R p').root) (R p').root
  have hd : dist p p' = rootedGHPDistance
      ((R p).space.law : Measure (R p).space) ((R p').space.law : Measure (R p').space)
      (R p).root (R p').root := by
    calc
      dist p p' = dist (toRootedMeasuredGHSpace (R p)) (toRootedMeasuredGHSpace (R p')) := by
        rw [hR p, hR p']
      _ = _ := rfl
  rw [hd]
  have hn := hnear p
  dsimp [ε] at hn hmid hlast htri htri'
  linarith

/-- The topology of the existing rooted GHP metric quotient is second countable. -/
noncomputable instance : SecondCountableTopology RootedMeasuredGHSpace.{u} :=
  secondCountable_of_countable_discretization exists_countable_discretization

/-- The existing rooted GHP metric has a countable dense subset. -/
theorem separableSpace : SeparableSpace RootedMeasuredGHSpace.{u} := inferInstance

end RootedMeasuredGHSpace

end BGW.MetricMeasure
