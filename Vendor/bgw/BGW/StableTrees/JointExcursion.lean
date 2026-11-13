/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.Skorokhod.DLoc
public import BGW.Skorokhod.Restrict
public import BGW.StableTrees.StableLocalLaw
public import BGW.StableTrees.SupremumLocalTimePublic
public import BGW.StableTrees.MarkedExcursionsBasic
public import BGW.StableTrees.UnitExcursionLaw
public import BGW.StableTrees.GammaIdentity
public import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
public import BGW.StableTrees.HeightProcess
public import BGW.StableTrees.HeightBridges
public import BGW.StableTrees.HeightContinuity
public import BGW.StableTrees.ExcursionHeight

/-!
# Joint excursion path and height laws

This module constructs the unit and tail laws of an excursion together with its continuous
height.  It proves their marginals and projectivity, identifies their prefixes using the common
measurable height graph, transfers the lifetime mixture and Gamma identity, and gives the
Brownian specialization.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal Classical
open BGW.Skorokhod BGW.StableTrees

namespace BGW.StableTrees

/-! ### Pair maps -/

/-- Restriction of a continuous function on `ℝ≥0` to `[0,T]`. -/
noncomputable def heightRestrict (T : ℝ≥0) (g : C(ℝ≥0, ℝ)) :
    C(Set.Icc (0 : ℝ) T, ℝ) :=
  g.comp ⟨fun t => ⟨t.1, t.2.1⟩, continuous_subtype_val.subtype_mk fun t => t.2.1⟩

/-- **The excursion/height pair on `[0,T]`**: the restricted path and the restricted height of
the same excursion. -/
noncomputable def excursionPair (θ : ℝ) (T : ℝ≥0) (e : Excursion) :
    D (T : ℝ) ℝ × C(Set.Icc (0 : ℝ) T, ℝ) :=
  (excursionRestrict T e, heightRestrict T (excursionHeight θ e))

/-- Restriction of a pair on `[0,T]` to `[0,a]`, for `a ≤ T`. -/
noncomputable def restrictPair {a T : ℝ≥0} (h : a ≤ T)
    (z : D (T : ℝ) ℝ × C(Set.Icc (0 : ℝ) T, ℝ)) :
    D (a : ℝ) ℝ × C(Set.Icc (0 : ℝ) a, ℝ) :=
  (BGW.Skorokhod.restrict (NNReal.coe_le_coe.2 h) z.1,
    z.2.comp ⟨Set.inclusion (Set.Icc_subset_Icc_right (NNReal.coe_le_coe.2 h)),
      continuous_inclusion _⟩)

/-- Extension of a continuous function on `[0,1]` to `ℝ≥0` by its terminal value. -/
noncomputable def extendHeight (h : C(Set.Icc (0 : ℝ) 1, ℝ)) : C(ℝ≥0, ℝ) :=
  h.comp ⟨fun t => Set.projIcc (0 : ℝ) 1 zero_le_one t,
    continuous_projIcc.comp NNReal.continuous_coe⟩

/-- Height scaling `t ↦ c^(1-1/θ) g(t/c)`, with the time convention of the sealed `scaleLoc`. -/
noncomputable def scaleHeight (θ : ℝ) (c : Set.Ioi (0 : ℝ)) (g : C(ℝ≥0, ℝ)) :
    C(ℝ≥0, ℝ) :=
  ⟨fun t => (c : ℝ) ^ (1 - 1 / θ) * g (t / (c : ℝ).toNNReal),
    continuous_const.mul (g.continuous.comp (continuous_id.div_const _))⟩

/-- **A unit pair stretched to lifetime `u`** on the horizon `[0,T]`, with one common `u`:
path `t ↦ u^(1/θ) x((t/u) ∧ 1)` and height `t ↦ u^(1-1/θ) h((t/u) ∧ 1)`
(both stopped at time
`1` of the unit pair, whose terminal values vanish a.s. under `excLaw θ`). -/
noncomputable def pairStretch (θ : ℝ) (T : ℝ≥0) (u : Set.Ioi (0 : ℝ))
    (z : D 1 ℝ × C(Set.Icc (0 : ℝ) 1, ℝ)) : D (T : ℝ) ℝ × C(Set.Icc (0 : ℝ) T, ℝ) :=
  (DLoc.restrict T (scaleLoc θ u (BGW.StableTrees.extendConst 1 z.1)),
    heightRestrict T (scaleHeight θ u (extendHeight z.2)))

/-! ### Joint laws -/

/-- **The normalized excursion/height law** on `D 1 ℝ × C([0,1], ℝ)`: the image of the unit
excursion law under the pair map (path and height of the same excursion). -/
noncomputable def excLaw (θ : ℝ) : ProbabilityMeasure (D 1 ℝ × C(Set.Icc (0 : ℝ) 1, ℝ)) :=
  (unitExcursionLaw θ).map (excursionPair θ 1)

/-- **The tail excursion/height law** on the horizon `[0,T]`: the image of `N(· | ζ > 1)` under
the pair map (the whole excursion, stopped at zero after its lifetime). -/
noncomputable def tailExcLaw (θ : ℝ) (T : ℝ≥0) :
    ProbabilityMeasure (D (T : ℝ) ℝ × C(Set.Icc (0 : ℝ) T, ℝ)) :=
  (tailExcursionLaw θ).map (excursionPair θ T)

private theorem measurable_heightRestrict (T : ℝ≥0) : Measurable (heightRestrict T) := by
  rw [ContinuousMap.measurable_iff_eval]
  intro t
  exact ContinuousMap.measurable_eval _

private theorem measurable_extendHeight : Measurable extendHeight := by
  rw [ContinuousMap.measurable_iff_eval]
  intro t
  exact ContinuousMap.measurable_eval _

private theorem measurable_scaleHeight (θ : ℝ) (c : Set.Ioi (0 : ℝ)) :
    Measurable (scaleHeight θ c) := by
  rw [ContinuousMap.measurable_iff_eval]
  intro t
  exact measurable_const.mul (ContinuousMap.measurable_eval _)

/-! ### Measurability guards -/

/-- The pair map is measurable (so `excLaw` and `tailExcLaw` are not junk images). -/
theorem measurable_excursionPair (θ : ℝ) (T : ℝ≥0) : Measurable (excursionPair θ T) := by
  exact (measurable_excursionRestrict T).prodMk
    ((measurable_heightRestrict T).comp (measurable_excursionHeight θ))

/-- Restriction of pairs is measurable. -/
theorem measurable_restrictPair {a T : ℝ≥0} (h : a ≤ T) : Measurable (restrictPair h) := by
  apply Measurable.prodMk
  · exact (BGW.Skorokhod.measurable_restrict (NNReal.coe_le_coe.2 h)).comp measurable_fst
  · rw [ContinuousMap.measurable_iff_eval]
    intro t
    change Measurable (fun z : D (T : ℝ) ℝ × C(Set.Icc (0 : ℝ) T, ℝ) =>
      z.2 (Set.inclusion (Set.Icc_subset_Icc_right (NNReal.coe_le_coe.2 h)) t))
    exact (ContinuousMap.measurable_eval _).comp measurable_snd

/-- Stretching of pairs is measurable, for each lifetime `u`. -/
theorem measurable_pairStretch (θ : ℝ) (T : ℝ≥0) (u : Set.Ioi (0 : ℝ)) :
    Measurable (pairStretch θ T u) := by
  apply Measurable.prodMk
  · exact ((DLoc.measurable_restrict T).comp (measurable_scaleLoc θ u)).comp
      ((measurable_extendConst 1).comp measurable_fst)
  · exact ((measurable_heightRestrict T).comp (measurable_scaleHeight θ u)).comp
      (measurable_extendHeight.comp measurable_snd)

private theorem restrictPair_excursionPair (θ : ℝ) {a T : ℝ≥0} (h : a ≤ T)
    (e : Excursion) :
    restrictPair h (excursionPair θ T e) = excursionPair θ a e := by
  apply Prod.ext
  · exact DLoc.restrict_restrict h e.path
  · rfl

/-! ### Marginals and projectivity -/

/-- **First marginal of `excLaw`**: exactly the sealed `levyExcLaw θ` (every `θ`). -/
theorem excLaw_map_fst (θ : ℝ) : (excLaw θ).map Prod.fst = levyExcLaw θ := by
  apply Subtype.ext
  exact Measure.map_map measurable_fst (measurable_excursionPair θ 1)

/-- **First marginal of `tailExcLaw`**: exactly the sealed `tailLevyExcLaw θ T` (every `θ`,
every horizon). -/
theorem tailExcLaw_map_fst (θ : ℝ) (T : ℝ≥0) :
    (tailExcLaw θ T).map Prod.fst = tailLevyExcLaw θ T := by
  apply Subtype.ext
  exact Measure.map_map measurable_fst (measurable_excursionPair θ T)

/-- **Projectivity** of the tail pair laws in the horizon. -/
theorem tailExcLaw_map_restrictPair (θ : ℝ) {a T : ℝ≥0} (h : a ≤ T) :
    (tailExcLaw θ T).map (restrictPair h) = tailExcLaw θ a := by
  apply Subtype.ext
  change ((tailExcLaw θ T : Measure _).map (restrictPair h)) =
    (tailExcLaw θ a : Measure _)
  change (((tailExcursionLaw θ : Measure Excursion).map (excursionPair θ T)).map
    (restrictPair h)) = (tailExcursionLaw θ : Measure Excursion).map (excursionPair θ a)
  rw [Measure.map_map (measurable_restrictPair h) (measurable_excursionPair θ T)]
  exact Measure.map_congr (Eventually.of_forall (restrictPair_excursionPair θ h))

private theorem ae_excursionPair_unit_prefix {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (a : ℝ≥0)
    (ha : a ∈ Ioo (0 : ℝ≥0) 1) :
    (fun e => restrictPair ha.2.le (excursionPair θ 1 e)) =ᵐ[
      (unitExcursionLaw θ : Measure Excursion)]
      (fun e => (excursionRestrict a e, heightPrefixAE θ a (excursionRestrict a e))) := by
  filter_upwards [ae_heightPrefixAE_unitExcursionLaw hθ,
    ae_lifetime_unitExcursionLaw hθ] with e he hl
  rw [restrictPair_excursionPair]
  apply Prod.ext
  · rfl
  · ext t
    exact (he a (hl ▸ ha.2) t).symm

private theorem ae_excursionPair_tail_prefix {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (a : ℝ≥0)
    (ha : a ≤ 1) :
    excursionPair θ a =ᵐ[(tailExcursionLaw θ : Measure Excursion)]
      (fun e => (excursionRestrict a e, heightPrefixAE θ a (excursionRestrict a e))) := by
  filter_upwards [ae_heightPrefixAE_tailExcursionLaw hθ,
    ae_tailExcursionLaw_support hθ] with e he hl
  apply Prod.ext
  · rfl
  · ext t
    exact (he a (ha.trans_lt hl.1) t).symm

/-! ### Common graph -/

/-- **Joint unit prefix** on `[0,a]`, `0 < a < 1`: the graph image of the unit path prefix under
the H04 a.e.-time prefix map. -/
theorem map_restrictPair_excLaw {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (a : ℝ≥0)
    (ha : a ∈ Ioo (0 : ℝ≥0) 1) :
    ((excLaw θ).map (restrictPair ha.2.le)).toMeasure =
      (unitPrefix θ a).map (fun x => (x, heightPrefixAE θ a x)) := by
  change (((unitExcursionLaw θ : Measure Excursion).map (excursionPair θ 1)).map
    (restrictPair ha.2.le)) = _
  have hg : Measurable (fun x : D (a : ℝ) ℝ =>
      (x, heightPrefixAE θ a x)) := measurable_id.prodMk (measurable_heightPrefixAE θ a)
  rw [Measure.map_map (measurable_restrictPair ha.2.le) (measurable_excursionPair θ 1),
    unitPrefix, Measure.map_map hg (measurable_excursionRestrict a)]
  exact Measure.map_congr (ae_excursionPair_unit_prefix hθ a ha)

/-- **Joint tail prefix** on `[0,a]`, `a ≤ 1`: the graph image of the tail path prefix under the
same H04 a.e.-time prefix map. -/
theorem tailExcLaw_eq_map_heightPrefixAE {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (a : ℝ≥0)
    (ha : a ≤ 1) :
    (tailExcLaw θ a).toMeasure = (tailPrefix θ a).map (fun x => (x, heightPrefixAE θ a x)) := by
  change ((tailExcursionLaw θ : Measure Excursion).map (excursionPair θ a)) = _
  have hg : Measurable (fun x : D (a : ℝ) ℝ =>
      (x, heightPrefixAE θ a x)) := measurable_id.prodMk (measurable_heightPrefixAE θ a)
  rw [tailPrefix, Measure.map_map hg (measurable_excursionRestrict a)]
  exact Measure.map_congr (ae_excursionPair_tail_prefix hθ a ha)

private theorem extendConst_unitExcursionRestrict (e : Excursion)
    (hl : e.lifetime = 1) : BGW.StableTrees.extendConst 1 (excursionRestrict 1 e) = e.path := by
  apply Subtype.ext
  funext t
  erw [BGW.StableTrees.extendConst,
    dite_eq_left (isCadlag_extendConst_fun 1 (excursionRestrict 1 e))]
  change (excursionRestrict 1 e)
    (Set.projIcc (0 : ℝ) ((1 : ℝ≥0) : ℝ) zero_le_one (t : ℝ)) = e.path.1 t
  by_cases ht : t ≤ 1
  · have hmem : (t : ℝ) ∈ Set.Icc (0 : ℝ) ((1 : ℝ≥0) : ℝ) :=
      ⟨t.2, by exact_mod_cast ht⟩
    have hproj : Set.projIcc (0 : ℝ) ((1 : ℝ≥0) : ℝ) zero_le_one (t : ℝ) =
        ⟨t, hmem⟩ := by
      apply Subtype.ext
      change max 0 (min ((1 : ℝ≥0) : ℝ) (t : ℝ)) = (t : ℝ)
      rw [min_eq_right hmem.2, max_eq_right hmem.1]
    rw [hproj]
    rfl
  · have ht1 : ((1 : ℝ≥0) : ℝ) ≤ (t : ℝ) := by exact_mod_cast (le_of_not_ge ht)
    have hproj : Set.projIcc (0 : ℝ) ((1 : ℝ≥0) : ℝ) zero_le_one (t : ℝ) =
        ⟨1, zero_le_one, le_rfl⟩ := by
      apply Subtype.ext
      change max 0 (min ((1 : ℝ≥0) : ℝ) (t : ℝ)) = 1
      rw [min_eq_left ht1]
      exact max_eq_right (by norm_num)
    rw [hproj]
    change e.path.1 1 = e.path.1 t
    have hzero1 : e.path.1 1 = 0 := e.2.2.2 1 (show e.lifetime ≤ 1 from hl.le)
    have hzerot : e.path.1 t = 0 := e.2.2.2 t
      (show e.lifetime ≤ t from hl.le.trans (le_of_not_ge ht))
    exact hzero1.trans hzerot.symm

private theorem extendHeight_unitExcursionHeight (θ : ℝ) (e : Excursion)
    (hl : e.lifetime = 1) :
    extendHeight (heightRestrict 1 (excursionHeight θ e)) = excursionHeight θ e := by
  ext t
  simp only [extendHeight, heightRestrict]
  let s : Set.Icc (0 : ℝ) ((1 : ℝ≥0) : ℝ) :=
    Set.projIcc (0 : ℝ) ((1 : ℝ≥0) : ℝ) zero_le_one (t : ℝ)
  change excursionHeight θ e ⟨s, s.2.1⟩ = excursionHeight θ e t
  by_cases ht : t ≤ 1
  · have hmem : (t : ℝ) ∈ Set.Icc (0 : ℝ) ((1 : ℝ≥0) : ℝ) :=
      ⟨t.2, by exact_mod_cast ht⟩
    have hproj : s = ⟨t, hmem⟩ := by
      apply Subtype.ext
      change max 0 (min ((1 : ℝ≥0) : ℝ) (t : ℝ)) = (t : ℝ)
      rw [min_eq_right hmem.2, max_eq_right hmem.1]
    rw [hproj]
    rfl
  · have ht1 : ((1 : ℝ≥0) : ℝ) ≤ (t : ℝ) := by exact_mod_cast (le_of_not_ge ht)
    have hproj : s = ⟨1, zero_le_one, le_rfl⟩ := by
      apply Subtype.ext
      change max 0 (min ((1 : ℝ≥0) : ℝ) (t : ℝ)) = 1
      rw [min_eq_left ht1]
      exact max_eq_right (by norm_num)
    rw [hproj]
    change excursionHeight θ e 1 = excursionHeight θ e t
    rw [excursionHeight_eq_zero_of_lifetime_le θ e (t := 1) (by rw [hl]),
      excursionHeight_eq_zero_of_lifetime_le θ e (t := t) (by rw [hl]; exact le_of_not_ge ht)]

private theorem ae_excursionPair_scale_unit {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (T : ℝ≥0)
    (u : Set.Ioi (0 : ℝ)) :
    ∀ᵐ e ∂(unitExcursionLaw θ : Measure Excursion),
      excursionPair θ T (excursionScale θ u e) =
        pairStretch θ T u (excursionPair θ 1 e) := by
  filter_upwards [ae_lifetime_unitExcursionLaw hθ,
    ae_excursionHeight_scale_unit hθ u] with e hl hs
  have hp := extendConst_unitExcursionRestrict e hl
  have hh := extendHeight_unitExcursionHeight θ e hl
  apply Prod.ext
  · change DLoc.restrict T (scaleLoc θ u e.path) =
      DLoc.restrict T (scaleLoc θ u (BGW.StableTrees.extendConst 1 (excursionRestrict 1 e)))
    rw [hp]
  · change heightRestrict T (excursionHeight θ (excursionScale θ u e)) =
      heightRestrict T (scaleHeight θ u (extendHeight (heightRestrict 1 (excursionHeight θ e))))
    rw [hh]
    ext t
    let s : ℝ≥0 := ⟨t, t.2.1⟩
    change excursionHeight θ (excursionScale θ u e) s =
      (u : ℝ) ^ (1 - 1 / θ) * excursionHeight θ e (s / (u : ℝ).toNNReal)
    have hc : 0 < (u : ℝ).toNNReal := Real.toNNReal_pos.mpr u.2
    have htime : (u : ℝ).toNNReal * (s / (u : ℝ).toNNReal) = s :=
      mul_div_cancel₀ _ hc.ne'
    exact (congrArg (excursionHeight θ (excursionScale θ u e)) htime.symm).trans
      (hs (s / (u : ℝ).toNNReal))

/-! ### Common-lifetime mixture -/

/-- **Joint tail mixture** (C28), every horizon `T > 0` (including `T > 1`): under
`N(· | ζ > 1)` the pair is a unit pair stretched to an independent common lifetime `u` with
density `(1/θ) u^(-1-1/θ)` on `(1, ∞)`, path by `u^(1/θ)`, height by `u^(1-1/θ)`. -/
theorem tailExcLaw_eq_mixture {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (T : ℝ≥0) (hT : 0 < T)
    {B : Set (D (T : ℝ) ℝ × C(Set.Icc (0 : ℝ) T, ℝ))} (hB : MeasurableSet B) :
    (tailExcLaw θ T).toMeasure B =
      ∫⁻ u, (excLaw θ).toMeasure (pairStretch θ T u ⁻¹' B) *
        ({u : Set.Ioi (0 : ℝ) | 1 < (u : ℝ)}.indicator
          (fun u => ENNReal.ofReal ((1 / θ) * (u : ℝ) ^ (-1 - 1 / θ))) u) ∂volIoi := by
  change ((tailExcursionLaw θ : Measure Excursion).map (excursionPair θ T)) B = _
  rw [Measure.map_apply (measurable_excursionPair θ T) hB]
  have _hT := hT
  rw [tailExcursionLaw_eq_mixture hθ (hB.preimage (measurable_excursionPair θ T))]
  apply lintegral_congr
  intro u
  congr 1
  rw [excursionAt, Measure.map_apply (measurable_excursionScale θ u)
    (hB.preimage (measurable_excursionPair θ T))]
  change (unitExcursionLaw θ : Measure Excursion)
      (excursionScale θ u ⁻¹' excursionPair θ T ⁻¹' B) =
    ((unitExcursionLaw θ : Measure Excursion).map (excursionPair θ 1))
      (pairStretch θ T u ⁻¹' B)
  rw [Measure.map_apply (measurable_excursionPair θ 1)
    (hB.preimage (measurable_pairStretch θ T u))]
  apply measure_congr
  filter_upwards [ae_excursionPair_scale_unit hθ T u] with e he
  change (excursionPair θ T (excursionScale θ u e) ∈ B) =
    (pairStretch θ T u (excursionPair θ 1 e) ∈ B)
  exact congrArg (fun z => z ∈ B) he

/-! ### Joint Γ identity -/

/-- **Joint Γ identity**, nonnegative measurable tests of the pair prefix on `[0,a]`,
`0 < a < 1`. -/
theorem lintegral_gamma_identity {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (a : ℝ≥0)
    (ha : a ∈ Ioo (0 : ℝ≥0) 1)
    (F : D (a : ℝ) ℝ × C(Set.Icc (0 : ℝ) a, ℝ) → ℝ≥0∞)
    (hF : Measurable F) :
    ∫⁻ z, F (restrictPair ha.2.le z) ∂(excLaw θ).toMeasure =
      ∫⁻ z, F (restrictPair ha.2.le z) *
          ENNReal.ofReal (gammaA θ a (evalEnd a (restrictPair ha.2.le z).1))
        ∂(tailExcLaw θ 1).toMeasure := by
  let G : D (a : ℝ) ℝ → D (a : ℝ) ℝ × C(Set.Icc (0 : ℝ) a, ℝ) :=
    fun x => (x, heightPrefixAE θ a x)
  have hG : Measurable G := measurable_id.prodMk (measurable_heightPrefixAE θ a)
  have hu : ((excLaw θ).map (restrictPair ha.2.le)).toMeasure =
      (unitPrefix θ a).map G := map_restrictPair_excLaw hθ a ha
  have ht : ((tailExcLaw θ 1).map (restrictPair ha.2.le)).toMeasure =
      (tailPrefix θ a).map G := by
    rw [tailExcLaw_map_restrictPair θ ha.2.le]
    exact tailExcLaw_eq_map_heightPrefixAE hθ a ha.2.le
  calc
    _ = ∫⁻ z, F z ∂((excLaw θ).map (restrictPair ha.2.le)).toMeasure :=
      (lintegral_map hF (measurable_restrictPair ha.2.le)).symm
    _ = ∫⁻ z, F z ∂(unitPrefix θ a).map G := by rw [← hu]
    _ = ∫⁻ x, F (G x) ∂unitPrefix θ a := lintegral_map hF hG
    _ = ∫⁻ x, F (G x) * ENNReal.ofReal (gammaA θ a (evalEnd a x))
        ∂tailPrefix θ a := lintegral_gamma_identity_path hθ a ha (F ∘ G) (hF.comp hG)
    _ = ∫⁻ x, F (G x) * ENNReal.ofReal (gammaA θ a (evalEnd a (G x).1))
        ∂tailPrefix θ a := rfl
    _ = ∫⁻ z, F z * ENNReal.ofReal (gammaA θ a (evalEnd a z.1))
        ∂(tailPrefix θ a).map G :=
      (lintegral_map
        (hF.mul ((measurable_gammaA_evalEnd θ a).comp measurable_fst)) hG).symm
    _ = ∫⁻ z, F z * ENNReal.ofReal (gammaA θ a (evalEnd a z.1))
        ∂((tailExcLaw θ 1).map (restrictPair ha.2.le)).toMeasure := by rw [ht]
    _ = _ := lintegral_map
      (hF.mul ((measurable_gammaA_evalEnd θ a).comp measurable_fst))
      (measurable_restrictPair ha.2.le)

/-- **Joint Γ identity** (source-facing form), bounded measurable signed tests of the pair
prefix on `[0,a]`, `0 < a < 1`, with both integrands integrable. -/
theorem gamma_identity {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (a : ℝ≥0)
    (ha : a ∈ Ioo (0 : ℝ≥0) 1)
    (F : D (a : ℝ) ℝ × C(Set.Icc (0 : ℝ) a, ℝ) → ℝ) (hF : Measurable F)
    (hb : ∃ C : ℝ, ∀ z, |F z| ≤ C) :
    Integrable (fun z => F (restrictPair ha.2.le z)) (excLaw θ).toMeasure ∧
    Integrable (fun z => F (restrictPair ha.2.le z) *
        gammaA θ a (evalEnd a (restrictPair ha.2.le z).1)) (tailExcLaw θ 1).toMeasure ∧
    (∫ z, F (restrictPair ha.2.le z) ∂(excLaw θ).toMeasure) =
      ∫ z, F (restrictPair ha.2.le z) * gammaA θ a (evalEnd a (restrictPair ha.2.le z).1)
        ∂(tailExcLaw θ 1).toMeasure := by
  let G : D (a : ℝ) ℝ → D (a : ℝ) ℝ × C(Set.Icc (0 : ℝ) a, ℝ) :=
    fun x => (x, heightPrefixAE θ a x)
  let R : D (a : ℝ) ℝ × C(Set.Icc (0 : ℝ) a, ℝ) → ℝ :=
    fun z => gammaA θ a (evalEnd a z.1)
  have hG : Measurable G := measurable_id.prodMk (measurable_heightPrefixAE θ a)
  have hR : Measurable R := (measurable_gammaA θ).comp
    (measurable_const.prodMk ((measurable_evalEnd a).comp measurable_fst))
  have hu : ((excLaw θ).map (restrictPair ha.2.le)).toMeasure =
      (unitPrefix θ a).map G := map_restrictPair_excLaw hθ a ha
  have ht : ((tailExcLaw θ 1).map (restrictPair ha.2.le)).toMeasure =
      (tailPrefix θ a).map G := by
    rw [tailExcLaw_map_restrictPair θ ha.2.le]
    exact tailExcLaw_eq_map_heightPrefixAE hθ a ha.2.le
  obtain ⟨C, hbC⟩ := hb
  have hleft : Integrable (fun z => F (restrictPair ha.2.le z)) (excLaw θ).toMeasure := by
    change Integrable (fun z => F (restrictPair ha.2.le z))
      ((unitExcursionLaw θ : Measure Excursion).map (excursionPair θ 1))
    exact Integrable.of_bound (hF.comp (measurable_restrictPair ha.2.le)).aestronglyMeasurable C
      (Eventually.of_forall fun z => by simpa only [Real.norm_eq_abs] using hbC _)
  have hIpre : Integrable R ((tailPrefix θ a).map G) := by
    apply (integrable_map_measure hR.aestronglyMeasurable hG.aemeasurable).2
    simpa only [Function.comp_def, R, G] using (integral_gammaA_tail_eq_one hθ a ha).1
  have hImap : Integrable R ((tailExcLaw θ 1).map (restrictPair ha.2.le)).toMeasure := by
    rw [ht]
    exact hIpre
  have hIcomp : Integrable (fun z => R (restrictPair ha.2.le z)) (tailExcLaw θ 1).toMeasure := by
    simpa only [Function.comp_def] using hImap.comp_measurable (measurable_restrictPair ha.2.le)
  have hright : Integrable (fun z => F (restrictPair ha.2.le z) * R (restrictPair ha.2.le z))
      (tailExcLaw θ 1).toMeasure := by
    have hw : Measurable (fun z => F (restrictPair ha.2.le z) * R (restrictPair ha.2.le z)) :=
      (hF.comp (measurable_restrictPair ha.2.le)).mul
        (hR.comp (measurable_restrictPair ha.2.le))
    apply (hIcomp.norm.const_mul C).mono' hw.aestronglyMeasurable
    filter_upwards with z
    simpa only [norm_mul, Real.norm_eq_abs] using
      mul_le_mul_of_nonneg_right (hbC (restrictPair ha.2.le z)) (abs_nonneg (R _))
  refine ⟨hleft, ?_, ?_⟩
  · exact hright
  · calc
      _ = ∫ z, F z ∂((excLaw θ).map (restrictPair ha.2.le)).toMeasure :=
        (integral_map (measurable_restrictPair ha.2.le).aemeasurable
          hF.aestronglyMeasurable).symm
      _ = ∫ z, F z ∂(unitPrefix θ a).map G := by rw [← hu]
      _ = ∫ x, F (G x) ∂unitPrefix θ a :=
        integral_map hG.aemeasurable hF.aestronglyMeasurable
      _ = ∫ x, F (G x) * gammaA θ a (evalEnd a x) ∂tailPrefix θ a :=
        gamma_identity_path hθ a ha (F ∘ G) (hF.comp hG) ⟨C, fun x => hbC (G x)⟩
      _ = ∫ z, F z * R z ∂(tailPrefix θ a).map G :=
        (integral_map hG.aemeasurable (hF.mul hR).aestronglyMeasurable).symm
      _ = ∫ z, F z * R z ∂((tailExcLaw θ 1).map (restrictPair ha.2.le)).toMeasure := by
        rw [ht]
      _ = _ := integral_map (measurable_restrictPair ha.2.le).aemeasurable
        (hF.mul hR).aestronglyMeasurable

/-! ### Endpoints and the Brownian case -/

private theorem pair_height_positive_iff_windows
    (z : D 1 ℝ × C(Set.Icc (0 : ℝ) 1, ℝ)) :
    (∀ t : Set.Icc (0 : ℝ) 1, 0 < (t : ℝ) → (t : ℝ) < 1 → 0 < z.2 t) ↔
      ∀ a b : ℚ, ∀ ha0 : 0 < (a : ℝ), ∀ hab : a ≤ b, ∀ hb : (b : ℝ) < 1,
        MapsTo z.2
          (Set.Icc
            (⟨a, ha0.le, (show (a : ℝ) ≤ (b : ℝ) by exact_mod_cast hab).trans hb.le⟩ :
              Set.Icc (0 : ℝ) 1)
            (⟨b, ha0.le.trans (show (a : ℝ) ≤ (b : ℝ) by exact_mod_cast hab), hb.le⟩ :
              Set.Icc (0 : ℝ) 1))
          (Set.Ioi 0) := by
  refine ⟨?_, ?_⟩
  · intro h a b ha0 hab hb t ht
    exact h t (ha0.trans_le ht.1)
      ((show (t : ℝ) ≤ (b : ℝ) from ht.2).trans_lt hb)
  · intro h t ht0 ht1
    obtain ⟨a, ha0, hat⟩ := exists_rat_btwn ht0
    obtain ⟨b, htb, hb1⟩ := exists_rat_btwn ht1
    have hab : a ≤ b := by exact_mod_cast hat.le.trans htb.le
    exact h a b ha0 hab hb1 ⟨hat.le, htb.le⟩

private theorem measurableSet_pair_height_pos :
    MeasurableSet {z : D 1 ℝ × C(Set.Icc (0 : ℝ) 1, ℝ) |
      ∀ t : Set.Icc (0 : ℝ) 1, 0 < (t : ℝ) → (t : ℝ) < 1 → 0 < z.2 t} := by
  simp_rw [pair_height_positive_iff_windows, ofPred_forall]
  apply MeasurableSet.iInter
  intro a
  apply MeasurableSet.iInter
  intro b
  apply MeasurableSet.iInter
  intro ha0
  apply MeasurableSet.iInter
  intro hab
  apply MeasurableSet.iInter
  intro hb
  have hB : MeasurableSet {z : D 1 ℝ × C(Set.Icc (0 : ℝ) 1, ℝ) |
      MapsTo z.2
        (Set.Icc
          (⟨a, ha0.le, (show (a : ℝ) ≤ (b : ℝ) by exact_mod_cast hab).trans hb.le⟩ :
            Set.Icc (0 : ℝ) 1)
          (⟨b, ha0.le.trans (show (a : ℝ) ≤ (b : ℝ) by exact_mod_cast hab), hb.le⟩ :
          Set.Icc (0 : ℝ) 1)) (Set.Ioi 0)} :=
    (ContinuousMap.isOpen_setOfPred_mapsTo isCompact_Icc isOpen_Ioi).measurableSet.preimage
      measurable_snd
  exact hB

private theorem measurableSet_pair_height_endpoints_pos :
    MeasurableSet {z : D 1 ℝ × C(Set.Icc (0 : ℝ) 1, ℝ) |
      z.2 ⟨0, le_rfl, zero_le_one⟩ = 0 ∧ z.2 ⟨1, zero_le_one, le_rfl⟩ = 0 ∧
        ∀ t : Set.Icc (0 : ℝ) 1, 0 < (t : ℝ) → (t : ℝ) < 1 → 0 < z.2 t} := by
  have h0 : MeasurableSet {z : D 1 ℝ × C(Set.Icc (0 : ℝ) 1, ℝ) |
      z.2 ⟨0, le_rfl, zero_le_one⟩ = 0} := measurableSet_eq_fun
    ((ContinuousMap.measurable_eval _).comp measurable_snd) measurable_const
  have h1 : MeasurableSet {z : D 1 ℝ × C(Set.Icc (0 : ℝ) 1, ℝ) |
      z.2 ⟨1, zero_le_one, le_rfl⟩ = 0} := measurableSet_eq_fun
    ((ContinuousMap.measurable_eval _).comp measurable_snd) measurable_const
  simpa only [Set.ofPred_and, Set.inter_assoc] using
    (h0.inter h1).inter measurableSet_pair_height_pos

/-- Under `excLaw θ` the height vanishes at `0` and `1` and is positive on `(0,1)`, all times
at once. -/
theorem excLaw_height_endpoints_pos {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ z ∂(excLaw θ).toMeasure,
      z.2 ⟨0, le_rfl, zero_le_one⟩ = 0 ∧ z.2 ⟨1, zero_le_one, le_rfl⟩ = 0 ∧
        ∀ t : Set.Icc (0 : ℝ) 1, 0 < (t : ℝ) → (t : ℝ) < 1 → 0 < z.2 t := by
  rw [show (excLaw θ).toMeasure =
    (unitExcursionLaw θ : Measure Excursion).map (excursionPair θ 1) from rfl]
  apply (ae_map_iff (measurable_excursionPair θ 1).aemeasurable
    measurableSet_pair_height_endpoints_pos).2
  filter_upwards [ae_lifetime_unitExcursionLaw hθ,
    ae_excursionHeight_pos_unit hθ] with e hl hp
  refine ⟨excursionHeight_zero θ e, ?_, ?_⟩
  · exact excursionHeight_eq_zero_of_lifetime_le θ e (t := 1) (by rw [hl])
  · intro t ht0 ht1
    exact hp ⟨t, t.2.1⟩ (by exact_mod_cast ht0) (by rw [hl]; exact_mod_cast ht1)

private theorem pair_height_eq_path_iff_rat
    (z : D 1 ℝ × C(Set.Icc (0 : ℝ) 1, ℝ)) :
    (∀ t : Set.Icc (0 : ℝ) 1, z.2 t = z.1 t) ↔
      ∀ q : ℚ, ∀ hq0 : 0 ≤ (q : ℝ), ∀ hq1 : (q : ℝ) ≤ 1,
        z.2 (⟨q, hq0, hq1⟩ : Set.Icc (0 : ℝ) 1) = z.1 ⟨q, hq0, hq1⟩ := by
  constructor
  · intro h q hq0 hq1
    exact h _
  · intro h t
    by_cases ht : (t : ℝ) = 1
    · have ht' : t = (⟨1, zero_le_one, le_rfl⟩ : Set.Icc (0 : ℝ) 1) := Subtype.ext ht
      rw [ht']
      simpa only [Rat.cast_one] using h 1 (by norm_num) (by norm_num)
    · have ht1 : (t : ℝ) < 1 := lt_of_le_of_ne t.2.2 ht
      obtain ⟨u, huanti, humem, hulim⟩ :=
        Rat.denseRange_cast.exists_seq_strictAnti_tendsto_of_lt Rat.cast_strictMono.monotone ht1
      let v : ℕ → Set.Icc (0 : ℝ) 1 := fun n =>
        ⟨(u n : ℝ), t.2.1.trans (humem n).1.le, (humem n).2.le⟩
      have hv : Tendsto v atTop (𝓝 t) := tendsto_subtype_rng.mpr
        (by simpa only [Function.comp_def] using hulim)
      have hvIoi : Tendsto v atTop (𝓝[>] t) := tendsto_nhdsWithin_iff.mpr
        ⟨hv, Eventually.of_forall fun n => (humem n).1⟩
      have heq (n : ℕ) : z.2 (v n) = z.1 (v n) := by
        exact h (u n) (t.2.1.trans (humem n).1.le) (humem n).2.le
      exact tendsto_nhds_unique (z.2.continuous.continuousAt.tendsto.comp hv)
        (((BGW.Skorokhod.isCadlag z.1).isRightContinuous t).tendsto.comp hvIoi |>.congr
          (fun n => (heq n).symm))

private theorem measurableSet_pair_height_eq_path :
    MeasurableSet {z : D 1 ℝ × C(Set.Icc (0 : ℝ) 1, ℝ) |
      ∀ t : Set.Icc (0 : ℝ) 1, z.2 t = z.1 t} := by
  simp_rw [pair_height_eq_path_iff_rat, ofPred_forall]
  apply MeasurableSet.iInter
  intro q
  apply MeasurableSet.iInter
  intro hq0
  apply MeasurableSet.iInter
  intro hq1
  exact measurableSet_eq_fun
    ((ContinuousMap.measurable_eval _).comp measurable_snd)
    ((measurable_eval _).comp measurable_fst)

/-- **Brownian specialization** (`θ = 2`, Laplace exponent `λ²`): under `excLaw 2` the height
equals the path at every time, almost surely. -/
theorem excLaw_height_eq_path_two :
    ∀ᵐ z ∂(excLaw 2).toMeasure, ∀ t : Set.Icc (0 : ℝ) 1, z.2 t = z.1 t := by
  rw [show (excLaw 2).toMeasure =
    (unitExcursionLaw 2 : Measure Excursion).map (excursionPair 2 1) from rfl]
  apply (ae_map_iff (measurable_excursionPair 2 1).aemeasurable
    measurableSet_pair_height_eq_path).2
  filter_upwards [ae_excursionHeight_two_unit] with e he t
  exact he ⟨t, t.2.1⟩

end BGW.StableTrees
