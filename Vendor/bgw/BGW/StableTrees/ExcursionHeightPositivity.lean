/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.ExcursionHeightPositiveHost
public import BGW.StableTrees.ExcursionHeightUnitScaling

/-!
# Simultaneous interior positivity

Positivity on every compact interior rational window is a Borel event in the compact-open
continuous-map space. Compensation transfers host positivity to the excursion measure;
the shape/lifetime law and fixed-scale unit scaling transfer it to the unit law.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal Classical
open BGW.Skorokhod

namespace BGW.StableTrees

private theorem positive_interior_iff_windows (θ : ℝ) (e : Excursion) :
    (∀ t : ℝ≥0, 0 < t → t < e.lifetime → 0 < excursionHeight θ e t) ↔
      ∀ a b : ℚ, 0 < (a : ℝ) → a ≤ b → (b : ℝ).toNNReal < e.lifetime →
        MapsTo (excursionHeight θ e) (Icc (a : ℝ).toNNReal (b : ℝ).toNNReal) (Ioi 0) := by
  refine ⟨?_, ?_⟩
  · intro h a b ha _ hb t ht
    exact h t ((Real.toNNReal_pos.mpr ha).trans_le ht.1) (ht.2.trans_lt hb)
  · intro h t ht htl
    obtain ⟨a, ha0, hat⟩ := exists_rat_btwn (show (0 : ℝ) < t from ht)
    obtain ⟨b, htb, hbζ⟩ := exists_rat_btwn (show (t : ℝ) < e.lifetime from htl)
    have hab : a ≤ b := by exact_mod_cast hat.le.trans htb.le
    have hb0 : 0 < (b : ℝ) := (show (0 : ℝ) < t from ht).trans htb
    have hb : (b : ℝ).toNNReal < e.lifetime := by
      change ((b : ℝ).toNNReal : ℝ) < e.lifetime
      rwa [Real.coe_toNNReal _ hb0.le]
    apply h a b ha0 hab hb
    constructor
    · change ((a : ℝ).toNNReal : ℝ) ≤ t
      rw [Real.coe_toNNReal _ ha0.le]
      exact hat.le
    · change (t : ℝ) ≤ ((b : ℝ).toNNReal : ℝ)
      rw [Real.coe_toNNReal _ hb0.le]
      exact htb.le

/-- Strict positivity at every interior age is a Borel event of the excursion. -/
theorem measurableSet_excursionHeight_pos (θ : ℝ) :
    MeasurableSet {e : Excursion | ∀ t : ℝ≥0, 0 < t → t < e.lifetime →
      0 < excursionHeight θ e t} := by
  simp_rw [positive_interior_iff_windows, ofPred_forall]
  apply MeasurableSet.iInter
  intro a
  apply MeasurableSet.iInter
  intro b
  apply MeasurableSet.iInter
  intro ha
  apply MeasurableSet.iInter
  intro hab
  have hA : MeasurableSet {e : Excursion | (b : ℝ).toNNReal < e.lifetime} :=
    measurableSet_lt measurable_const measurable_excursion_lifetime
  have hB : MeasurableSet {e : Excursion | MapsTo (excursionHeight θ e)
      (Icc (a : ℝ).toNNReal (b : ℝ).toNNReal) (Ioi (0 : ℝ))} :=
    (ContinuousMap.isOpen_setOfPred_mapsTo isCompact_Icc isOpen_Ioi).measurableSet.preimage
      (measurable_excursionHeight θ)
  convert hA.compl.union hB using 1
  ext e
  exact imp_iff_not_or

/-- **Positivity inside**, simultaneously for all times of `(0, ζ)`, under `N`. -/
theorem ae_excursionHeight_pos {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ e ∂(excursionMeasure θ), ∀ t : ℝ≥0, 0 < t → t < e.lifetime →
      0 < excursionHeight θ e t := by
  exact ae_excursionMeasure_of_ae_jumpExcursion hθ
    (measurableSet_excursionHeight_pos θ) (ae_jumpExcursion_height_pos hθ)

/-- **Positivity inside**, simultaneously for all times of `(0, ζ)`, under the unit law. -/
theorem ae_excursionHeight_pos_unit {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ e ∂(unitExcursionLaw θ : Measure Excursion), ∀ t : ℝ≥0, 0 < t → t < e.lifetime →
      0 < excursionHeight θ e t := by
  let : NeZero (lifetimeLaw θ) := ⟨lifetimeLaw_ne_zero_of_height_index hθ⟩
  have ha : ∀ᵐ e ∂(((lifetimeLaw θ).prod (unitExcursionLaw θ : Measure Excursion)).map
      (fromShapeLifetime θ)), ∀ t : ℝ≥0, 0 < t → t < e.lifetime →
        0 < excursionHeight θ e t := by
    rw [map_fromShapeLifetime_product hθ]
    exact ae_excursionHeight_pos hθ
  have hp := ae_of_ae_map (measurable_fromShapeLifetime θ).aemeasurable ha
  obtain ⟨c, hc⟩ := (MeasureTheory.Measure.ae_ae_of_ae_prod hp).exists
  filter_upwards [hc, ae_excursionHeight_scale_unit hθ c] with e he hs t ht htl
  have hk : 0 < (c : ℝ).toNNReal := Real.toNNReal_pos.mpr c.2
  have hpos := he ((c : ℝ).toNNReal * t) (mul_pos hk ht)
    (show (c : ℝ).toNNReal * t < (excursionScale θ c e).lifetime from
      mul_lt_mul_of_pos_left htl hk)
  change 0 < excursionHeight θ (excursionScale θ c e) ((c : ℝ).toNNReal * t) at hpos
  rw [hs t] at hpos
  exact (mul_pos_iff_of_pos_left (Real.rpow_pos_of_pos c.2 (1 - 1 / θ))).mp hpos

end BGW.StableTrees
