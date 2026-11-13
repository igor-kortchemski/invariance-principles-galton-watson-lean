/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.ExcursionHeightScaling
import BGW.StableTrees.HeightBridgesUnitTransfer

/-!
# Raw scaling under the unit law before continuous reconstruction

Convergence along the rescaled cutoffs is a prefix event. The excursion prefix density
transfers this event at almost every age, without presupposing the unit terminal trace.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal Classical
open BGW.Skorokhod

namespace BGW.StableTrees

/-- Rescaled universal cutoffs converge at almost every surviving excursion age. -/
theorem ae_tendsto_rescaled_heightUniv_ages {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    (c : Ioi (0 : ℝ)) (S : ℝ≥0) :
    ∀ᵐ p ∂heightExcursionAgeMeasure θ S,
      Tendsto (fun n => heightApprox (heightEps θ n / (c : ℝ) ^ (1 / θ))
        p.2.path p.1.toNNReal) atTop (𝓝 (heightUniv θ p.2.path p.1.toNNReal)) := by
  let := sigmaFinite_excursionMeasure hθ
  have hs := (quasiMeasurePreserving_excursion_age_scale hθ c S).ae
    (ae_tendsto_excursionHeight_ages hθ ((c : ℝ).toNNReal * S))
  have hscale : ∀ᵐ p ∂heightExcursionAgeMeasure θ S,
      excursionHeight θ (excursionScale θ c p.2) ((c : ℝ).toNNReal * p.1.toNNReal) =
        (c : ℝ) ^ (1 - 1 / θ) * excursionHeight θ p.2 p.1.toNNReal :=
    ae_excursionHeight_scale_ages hθ c S
  have hb : (c : ℝ) ^ (1 - 1 / θ) ≠ 0 := (Real.rpow_pos_of_pos c.2 _).ne'
  filter_upwards [hs, hscale, ae_heightUniv_eq_excursionHeight_ages hθ S] with p hp he hr
  have ht : Tendsto (fun n => (c : ℝ) ^ (1 - 1 / θ) *
      heightApprox (heightEps θ n / (c : ℝ) ^ (1 / θ)) p.2.path p.1.toNNReal) atTop
      (𝓝 ((c : ℝ) ^ (1 - 1 / θ) * excursionHeight θ p.2 p.1.toNNReal)) := by
    simp only [Real.toNNReal_mul c.2.le] at hp
    change Tendsto (fun n => heightApprox (heightEps θ n) (scaleLoc θ c p.2.path)
      ((c : ℝ).toNNReal * p.1.toNNReal)) atTop
      (𝓝 (excursionHeight θ (excursionScale θ c p.2)
        ((c : ℝ).toNNReal * p.1.toNNReal))) at hp
    simp_rw [heightApprox_scaleLoc] at hp
    rwa [he] at hp
  have hh := ht.const_mul ((c : ℝ) ^ (1 - 1 / θ))⁻¹
  simpa only [← mul_assoc, inv_mul_cancel₀ hb, one_mul, hr] using hh

/-- A convergent cutoff sequence with its universal-height limit transfers through prefix laws. -/
theorem ae_tendsto_heightUniv_unit_of_prefix {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    (t : ℝ≥0) (ht0 : 0 < t) (ht1 : t < 1) (δ : ℕ → ℝ)
    (hN : ∀ᵐ e ∂((excursionMeasure θ).restrict {e : Excursion | t < e.lifetime}),
      Tendsto (fun n => heightApprox (δ n) e.path t) atTop
        (𝓝 (heightUniv θ e.path t))) :
    ∀ᵐ e ∂(unitExcursionLaw θ : Measure Excursion),
      Tendsto (fun n => heightApprox (δ n) e.path t) atTop
        (𝓝 (heightUniv θ e.path t)) := by
  let P : D (t : ℝ) ℝ → Prop := fun g =>
    Tendsto (fun n => horizonHeightApprox (δ n) t g) atTop
      (𝓝 (heightUniv θ (extendConst t g) t))
  have hraw : Measurable (fun g : D (t : ℝ) ℝ => heightUniv θ (extendConst t g) t) :=
    Measurable.comp (g := fun p : ℝ≥0 × DLoc => heightUniv θ p.2 p.1)
      (f := fun g : D (t : ℝ) ℝ => (t, extendConst t g))
      (measurable_heightUniv_uncurry θ)
      (measurable_const.prodMk (measurable_extendConst t))
  have hP : MeasurableSet {g | P g} := measurableSet_tendsto_fun
    (l := (atTop : Filter ℕ)) (fun n => measurable_horizonHeightApprox (δ n) t) hraw
  have he (e : Excursion) : P (excursionRestrict t e) ↔
      Tendsto (fun n => heightApprox (δ n) e.path t) atTop
        (𝓝 (heightUniv θ e.path t)) := by
    have hr := heightUniv_eq_of_restrict_eq θ t
      (extendConst t (DLoc.restrict t e.path)) e.path (restrict_extendConst t _) t le_rfl
    simp only [P, excursionRestrict, horizonHeightApprox_restrict, hr]
  have hbase : ∀ᵐ g ∂(((excursionMeasure θ).restrict
      {e : Excursion | t < e.lifetime}).map (excursionRestrict t)), P g :=
    (ae_map_iff (measurable_excursionRestrict t).aemeasurable hP).mpr
      (hN.mono fun e h => (he e).mpr h)
  have hu := (unitPrefix_absolutelyContinuous_excursion hθ t ht0 ht1).ae_le hbase
  have hunit : ∀ᵐ e ∂(unitExcursionLaw θ : Measure Excursion), P (excursionRestrict t e) :=
    ae_of_ae_map (measurable_excursionRestrict t).aemeasurable hu
  exact hunit.mono fun e h => (he e).mp h

/-- At almost every unit age the rescaled cutoff sequence has the universal-height limit. -/
theorem ae_age_tendsto_rescaled_heightUniv_unit {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    (c : Ioi (0 : ℝ)) :
    ∀ᵐ s : ℝ ∂volume.restrict (Ioo (0 : ℝ) 1),
      ∀ᵐ e ∂(unitExcursionLaw θ : Measure Excursion),
        Tendsto (fun n => heightApprox (heightEps θ n / (c : ℝ) ^ (1 / θ))
          e.path s.toNNReal) atTop (𝓝 (heightUniv θ e.path s.toNNReal)) := by
  let := sigmaFinite_excursionMeasure hθ
  have hm : MeasurableSet {p : ℝ × Excursion | p.1.toNNReal < p.2.lifetime →
      Tendsto (fun n : ℕ => heightApprox (heightEps θ n / (c : ℝ) ^ (1 / θ))
        p.2.path p.1.toNNReal) atTop (𝓝 (heightUniv θ p.2.path p.1.toNNReal))} := by
    convert measurableSet_heightExcursionAge_survival.compl.union
      (measurableSet_tendsto_fun (l := (atTop : Filter ℕ))
        (fun n => measurable_heightApprox_age_excursion (heightEps θ n / (c : ℝ) ^ (1 / θ)))
        (measurable_heightUniv_excursion_real_age θ)) using 1
    ext p
    exact imp_iff_not_or
  have ha := (MeasureTheory.Measure.ae_prod_iff_ae_ae hm).mp
    ((ae_restrict_iff' measurableSet_heightExcursionAge_survival).mp
      (ae_tendsto_rescaled_heightUniv_ages hθ c 1))
  filter_upwards [ha, ae_restrict_mem measurableSet_Ioo] with s hs hmem
  have hs0 : 0 < s.toNNReal := Real.toNNReal_pos.mpr hmem.1
  have hs1 : s.toNNReal < 1 := by
    change (s.toNNReal : ℝ) < 1
    rw [Real.coe_toNNReal _ hmem.1.le]
    exact hmem.2
  exact ae_tendsto_heightUniv_unit_of_prefix hθ s.toNNReal hs0 hs1 _
    ((ae_restrict_iff'
      (measurableSet_lt measurable_const measurable_excursion_lifetime)).mpr hs)

/-- Raw height scaling at almost every unit age, before choosing a unit continuous version. -/
theorem ae_heightUniv_scale_unit_ages {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    (c : Ioi (0 : ℝ)) :
    ∀ᵐ e ∂(unitExcursionLaw θ : Measure Excursion),
      ∀ᵐ s : ℝ ∂volume.restrict (Ioo (0 : ℝ) 1),
        heightUniv θ (excursionScale θ c e).path ((c : ℝ).toNNReal * s.toNNReal) =
          (c : ℝ) ^ (1 - 1 / θ) * heightUniv θ e.path s.toNNReal := by
  have hm : MeasurableSet {p : ℝ × Excursion |
      Tendsto (fun n : ℕ => heightApprox (heightEps θ n / (c : ℝ) ^ (1 / θ))
        p.2.path p.1.toNNReal) atTop (𝓝 (heightUniv θ p.2.path p.1.toNNReal))} :=
    measurableSet_tendsto_fun (l := (atTop : Filter ℕ))
      (fun n => measurable_heightApprox_age_excursion (heightEps θ n / (c : ℝ) ^ (1 / θ)))
      (measurable_heightUniv_excursion_real_age θ)
  have ha := (MeasureTheory.Measure.ae_ae_comm hm).mp
    (ae_age_tendsto_rescaled_heightUniv_unit hθ c)
  filter_upwards [ha] with e he
  filter_upwards [he] with s hs
  have h := hs.const_mul ((c : ℝ) ^ (1 - 1 / θ))
  change limsup (fun n => heightApprox (heightEps θ n)
    (scaleLoc θ c e.path) ((c : ℝ).toNNReal * s.toNNReal)) atTop = _
  simp_rw [heightApprox_scaleLoc]
  exact h.limsup_eq

end BGW.StableTrees
