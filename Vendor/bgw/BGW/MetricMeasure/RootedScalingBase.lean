/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
public import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# Positive rescaling of a metric carrier

`ScaledMetric c X` is a fresh carrier with distance multiplied by the positive
number `c`. Its topology and measurable structure are transported from `X`.
`MetricSpace.ofDistTopology` makes the metric induce that very topology.
No metric instance on the original carrier is changed.

The two quantitative helpers control Hausdorff distance on compact sets and
Lévy–Prokhorov distance under Lipschitz maps. The latter uses the factor
`max K 1`, since the probability-error term is not spatially rescaled.
-/

@[expose] public section

open MeasureTheory Metric Set
open scoped ENNReal NNReal

universe u

namespace BGW.MetricMeasure

/-- A carrier whose distances are multiplied by one fixed positive real number. -/
def ScaledMetric (_c : Set.Ioi (0 : ℝ)) (X : Type u) : Type u := X

namespace ScaledMetric

variable (c : Set.Ioi (0 : ℝ)) {X : Type u}

/-- View a point in the carrier whose distances are scaled by `c`. -/
def toScaled (x : X) : ScaledMetric c X := x
/-- Recover the original point from the scaled carrier. -/
def ofScaled (x : ScaledMetric c X) : X := x

@[simp] theorem ofScaled_toScaled (x : X) : ofScaled c (toScaled c x) = x := rfl
@[simp] theorem toScaled_ofScaled (x : ScaledMetric c X) : toScaled c (ofScaled c x) = x := rfl

/-- The identity bijection between the original and scaled carriers. -/
def equiv (X : Type u) : X ≃ ScaledMetric c X where
  toFun := toScaled c
  invFun := ofScaled c
  left_inv := ofScaled_toScaled c
  right_inv := toScaled_ofScaled c

instance [Nonempty X] : Nonempty (ScaledMetric c X) := inferInstanceAs (Nonempty X)
instance [TopologicalSpace X] : TopologicalSpace (ScaledMetric c X) :=
  inferInstanceAs (TopologicalSpace X)
instance [MeasurableSpace X] : MeasurableSpace (ScaledMetric c X) :=
  inferInstanceAs (MeasurableSpace X)
instance [TopologicalSpace X] [CompactSpace X] : CompactSpace (ScaledMetric c X) :=
  inferInstanceAs (CompactSpace X)
instance [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] :
    BorelSpace (ScaledMetric c X) := inferInstanceAs (BorelSpace X)

@[fun_prop] theorem continuous_toScaled [TopologicalSpace X] :
    Continuous (toScaled c : X → ScaledMetric c X) := continuous_id

@[fun_prop] theorem continuous_ofScaled [TopologicalSpace X] :
    Continuous (ofScaled c : ScaledMetric c X → X) := continuous_id

@[fun_prop] theorem measurable_toScaled [MeasurableSpace X] :
    Measurable (toScaled c : X → ScaledMetric c X) := measurable_id

@[fun_prop] theorem measurable_ofScaled [MeasurableSpace X] :
    Measurable (ofScaled c : ScaledMetric c X → X) := measurable_id

/-- The identity homeomorphism for the topology retained by the scaled carrier. -/
def homeomorph [TopologicalSpace X] : X ≃ₜ ScaledMetric c X where
  toEquiv := equiv c X
  continuous_toFun := continuous_toScaled c
  continuous_invFun := continuous_ofScaled c

instance [MetricSpace X] : MetricSpace (ScaledMetric c X) :=
  MetricSpace.ofDistTopology (fun x y => (c : ℝ) * dist (ofScaled c x) (ofScaled c y))
    (by intro x; simp)
    (by intro x y; rw [dist_comm])
    (by
      intro x y z
      simpa only [mul_add] using
        mul_le_mul_of_nonneg_left (dist_triangle (ofScaled c x) (ofScaled c y) (ofScaled c z))
          c.property.le)
    (by
      intro s
      change IsOpen (s : Set X) ↔
        ∀ x : X, x ∈ (s : Set X) → ∃ ε > 0, ∀ y : X,
          (c : ℝ) * dist x y < ε → y ∈ (s : Set X)
      constructor
      · intro hs x hx
        obtain ⟨ε, hε, hball⟩ := (Metric.isOpen_iff (α := X)).mp hs x hx
        refine ⟨(c : ℝ) * ε, mul_pos c.property hε, fun y hy => hball ?_⟩
        have hxy : dist (x : X) (y : X) < ε := by
          by_contra hn
          have hp := mul_nonneg c.property.le (sub_nonneg.mpr (le_of_not_gt hn))
          nlinarith
        change dist (y : X) (x : X) < ε
        rw [dist_comm]
        exact hxy
      · intro hs
        apply (Metric.isOpen_iff (α := X)).mpr
        intro x hx
        obtain ⟨ε, hε, hball⟩ := hs x hx
        refine ⟨ε / (c : ℝ), div_pos hε c.property, fun y hy => hball y ?_⟩
        change dist (y : X) (x : X) < ε / (c : ℝ) at hy
        rw [dist_comm (y : X) (x : X)] at hy
        have hprod := (lt_div_iff₀ c.property).mp hy
        nlinarith)
    (by
      intro x y h
      change (c : ℝ) * dist (ofScaled c x) (ofScaled c y) = 0 at h
      change ofScaled c x = ofScaled c y
      exact dist_eq_zero.mp ((mul_eq_zero.mp h).resolve_left c.property.ne'))

@[simp] theorem dist_toScaled [MetricSpace X] (x y : X) :
    dist (toScaled c x) (toScaled c y) = (c : ℝ) * dist x y := rfl

theorem lipschitzWith_toScaled [MetricSpace X] :
    LipschitzWith ⟨(c : ℝ), c.property.le⟩ (toScaled c : X → ScaledMetric c X) :=
  lipschitzWith_iff_dist_le_mul.mpr fun _ _ => le_rfl

theorem map_ofScaled_map_toScaled [MeasurableSpace X] (μ : Measure X) :
    (μ.map (toScaled c)).map (ofScaled c) = μ := by
  rw [Measure.map_map (measurable_ofScaled c) (measurable_toScaled c)]
  exact Measure.map_id

theorem map_toScaled_univ [MeasurableSpace X] (μ : Measure X) :
    μ.map (toScaled c) Set.univ = μ Set.univ := by
  rw [Measure.map_apply (measurable_toScaled c) MeasurableSet.univ]
  rfl

end ScaledMetric

/-- A Lipschitz map controls the Prokhorov radius and the unchanged mass-error term. -/
theorem levyProkhorovDist_map_le_mul
    {X Y : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {K : ℝ≥0} {f : X → Y} (hf : LipschitzWith K f) :
    levyProkhorovDist (μ.map f) (ν.map f) ≤
      max (K : ℝ) 1 * levyProkhorovDist μ ν := by
  let c : ℝ := max (K : ℝ) 1
  have hc1 : 1 ≤ c := le_max_right _ _
  have hc : 0 < c := lt_of_lt_of_le zero_lt_one hc1
  have hδ : 0 ≤ c * levyProkhorovDist μ ν :=
    mul_nonneg hc.le ENNReal.toReal_nonneg
  apply levyProkhorovDist_le_of_forall_le _ _ hδ
  intro ε B hε hB
  have hε0 : 0 < ε := hδ.trans_lt hε
  have hη0 : 0 ≤ ε / c := div_nonneg hε0.le hc.le
  have hη : levyProkhorovDist μ ν < ε / c := by
    rw [lt_div_iff₀ hc]
    simpa only [mul_comm] using hε
  have hηE : levyProkhorovEDist μ ν < ENNReal.ofReal (ε / c) :=
    (ENNReal.lt_ofReal_iff_toReal_lt (levyProkhorovEDist_ne_top μ ν)).mpr hη
  have hb := left_measure_le_of_levyProkhorovEDist_lt hηE
    (hB.preimage hf.continuous.measurable)
  rw [ENNReal.toReal_ofReal hη0] at hb
  rw [Measure.map_apply hf.continuous.measurable hB,
    Measure.map_apply hf.continuous.measurable isOpen_thickening.measurableSet]
  apply hb.trans
  apply add_le_add
  · apply measure_mono
    intro x hx
    obtain ⟨z, hz, hxz⟩ := mem_thickening_iff.mp hx
    refine mem_thickening_iff.mpr ⟨f z, hz, ?_⟩
    calc dist (f x) (f z) ≤ (K : ℝ) * dist x z := hf.dist_le_mul x z
      _ ≤ c * dist x z := mul_le_mul_of_nonneg_right (le_max_left _ _) dist_nonneg
      _ < c * (ε / c) := mul_lt_mul_of_pos_left hxz hc
      _ = ε := by field_simp
  · exact ENNReal.ofReal_le_ofReal (div_le_self hε0.le hc1)

/-- A Lipschitz map controls Hausdorff distance between nonempty compact sets. -/
theorem hausdorffDist_image_le_mul_of_lipschitz
    {X Y : Type*} [MetricSpace X] [MetricSpace Y] {K : ℝ≥0} {f : X → Y}
    (hf : LipschitzWith K f) {s t : Set X} (hs : IsCompact s) (ht : IsCompact t)
    (hsne : s.Nonempty) (htne : t.Nonempty) :
    hausdorffDist (f '' s) (f '' t) ≤ (K : ℝ) * hausdorffDist s t := by
  have hfinite := hausdorffEDist_ne_top_of_nonempty_of_bounded hsne htne hs.isBounded ht.isBounded
  apply hausdorffDist_le_of_mem_dist (mul_nonneg K.coe_nonneg hausdorffDist_nonneg)
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨y, hy, hmin⟩ := ht.exists_infDist_eq_dist htne x
    refine ⟨f y, ⟨y, hy, rfl⟩, (hf.dist_le_mul x y).trans ?_⟩
    rw [← hmin]
    exact mul_le_mul_of_nonneg_left (infDist_le_hausdorffDist_of_mem hx hfinite) K.coe_nonneg
  · rintro _ ⟨y, hy, rfl⟩
    obtain ⟨x, hx, hmin⟩ := hs.exists_infDist_eq_dist hsne y
    refine ⟨f x, ⟨x, hx, rfl⟩, (hf.dist_le_mul y x).trans ?_⟩
    rw [← hmin]
    have hfinite' : hausdorffEDist t s ≠ ⊤ := by rwa [hausdorffEDist_comm]
    have h := infDist_le_hausdorffDist_of_mem hy hfinite'
    rw [hausdorffDist_comm] at h
    exact mul_le_mul_of_nonneg_left h K.coe_nonneg

end BGW.MetricMeasure
