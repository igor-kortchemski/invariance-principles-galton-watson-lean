/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.ExcursionMarkovProof

import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Consequences of the excursion Markov property

The measurable lifetime bridge gives the residual passage law. Finite survival measures
also permit bounded signed tests. Restarting at half the observation time proves the absence
of fixed jumps under the excursion measure.

Reference: J. Bertoin, *Lévy Processes*, Cambridge University Press, 1996, Chapter IV.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees

/-- **Remaining-lifetime identity.**  Given the prefix up to age `t`, the remaining lifetime
`ζ - t` has the law of the passage time `T_{e(t)}` of the stable process, i.e.
`passageLaw θ (e(t))` (whose density is `qKernel`, see `passageLaw_eq_qKernel`).
For measurable `H : ℝ → ℝ≥0∞`.
Proof route: the bridge `ae_lastPositiveTime_futureFrom`/`_killedPath`, not `firstHitBelow`. -/
theorem excursion_remainingLifetime_lintegral {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (t : ℝ≥0)
    (ht : 0 < t) (F : D (t : ℝ) ℝ → ℝ≥0∞) (hF : Measurable F)
    (H : ℝ → ℝ≥0∞) (hH : Measurable H) :
    (∫⁻ e in {e : Excursion | t < e.lifetime},
        F (excursionRestrict t e) * H ((e.lifetime : ℝ) - (t : ℝ)) ∂(excursionMeasure θ)) =
      ∫⁻ e in {e : Excursion | t < e.lifetime},
        F (excursionRestrict t e) *
          (∫⁻ s, H s ∂(passageLaw θ (e.valueNN t))) ∂(excursionMeasure θ) := by
  classical
  let G : DLoc → ℝ≥0∞ := fun f => H (((lastPositiveTime f).untopD 0 : ℝ≥0) : ℝ)
  have hG : Measurable G :=
    hH.comp ((measurable_lastPositiveTime.untopD 0).coe_nnreal_real)
  have hk (y : ℝ≥0) (hy : 0 < y) :
      (∫⁻ f, G f ∂killedStableKernel θ y) = ∫⁻ s, H s ∂passageLaw θ y := by
    have hkm : Measurable (killedPath y) :=
      measurable_killedPath_uncurry.comp (measurable_const.prodMk measurable_id)
    have hpass : Measurable (fun f : DLoc => (passageTime y f : ℝ)) :=
      ((isStoppingTime_firstPassageBelow y).measurable'.untopD 0).coe_nnreal_real
    rw [killedStableKernel_apply, lintegral_map hG hkm,
      passageLaw, lintegral_map hH hpass]
    apply lintegral_congr_ae
    filter_upwards [ae_lastPositiveTime_killedPath hθ y hy] with f hf
    simp only [G, hf, passageTime]
  have hsurv : MeasurableSet {e : Excursion | t < e.lifetime} :=
    measurableSet_lt measurable_const measurable_excursion_lifetime
  calc
    _ = ∫⁻ e in {e : Excursion | t < e.lifetime},
        F (excursionRestrict t e) * G (futureFrom t e) ∂excursionMeasure θ := by
      apply lintegral_congr_ae
      filter_upwards [ae_lastPositiveTime_futureFrom hθ t ht, ae_restrict_mem hsurv]
        with e he htζ
      simp only [G, he, WithTop.untopD_coe, NNReal.coe_sub htζ.le]
    _ = ∫⁻ e in {e : Excursion | t < e.lifetime}, F (excursionRestrict t e) *
        (∫⁻ f, G f ∂killedStableKernel θ (e.valueNN t)) ∂excursionMeasure θ :=
      excursion_markov_lintegral hθ t ht F hF G hG
    _ = _ := by
      apply lintegral_congr_ae
      filter_upwards [ae_valueNN_pos hθ t ht] with e he
      rw [hk (e.valueNN t) he]

/-- Signed bounded-test version of the Markov property (finite survival measure, Markov
kernel). -/
theorem excursion_markov_integral {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    (t : ℝ≥0) (ht : 0 < t)
    (F : D (t : ℝ) ℝ → ℝ) (hF : Measurable F)
    (hFb : ∃ C : ℝ, ∀ p, |F p| ≤ C)
    (G : DLoc → ℝ) (hG : Measurable G)
    (hGb : ∃ C : ℝ, ∀ f, |G f| ≤ C) :
    (∫ e in {e : Excursion | t < e.lifetime},
      F (excursionRestrict t e) * G (futureFrom t e) ∂(excursionMeasure θ)) =
    ∫ e in {e : Excursion | t < e.lifetime},
      F (excursionRestrict t e) *
        (∫ f, G f ∂(killedStableKernel θ (e.valueNN t)))
        ∂(excursionMeasure θ) := by
  classical
  let _ := isMarkovKernel_killedStableKernel θ
  let μ : Measure Excursion := (excursionMeasure θ).restrict {e : Excursion | t < e.lifetime}
  let _ : IsFiniteMeasure μ := isFiniteMeasure_excursionMeasure_survival hθ t ht
  let κ : Kernel Excursion DLoc := (killedStableKernel θ).comap
    (fun e : Excursion => e.valueNN t) (measurable_excursion_valueNN t)
  have hκapply (e : Excursion) : κ e = killedStableKernel θ (e.valueNN t) :=
    Kernel.comap_apply _ _ e
  let _ : IsMarkovKernel κ := Kernel.IsMarkovKernel.comap _ _
  let L : Excursion → D (t : ℝ) ℝ × DLoc := fun e => (excursionRestrict t e, futureFrom t e)
  let R : Excursion × DLoc → D (t : ℝ) ℝ × DLoc := fun p =>
    (excursionRestrict t p.1, p.2)
  have hL : Measurable L := (measurable_excursionRestrict t).prodMk (measurable_futureFrom t)
  have hR : Measurable R :=
    ((measurable_excursionRestrict t).comp measurable_fst).prodMk measurable_snd
  have hjoint : μ.map L = (μ ⊗ₘ κ).map R := by
    apply Measure.ext_prod
    intro U V hU hV
    have hB : MeasurableSet (L ⁻¹' (U ×ˢ V)) := hL (hU.prod hV)
    have hC : MeasurableSet (R ⁻¹' (U ×ˢ V)) := hR (hU.prod hV)
    rw [Measure.map_apply hL (hU.prod hV), Measure.map_apply hR (hU.prod hV)]
    have hsm := excursion_markov_lintegral hθ t ht (U.indicator 1)
      (measurable_const.indicator hU) (V.indicator 1) (measurable_const.indicator hV)
    have hleft : (∫⁻ e, U.indicator 1 (excursionRestrict t e) *
        V.indicator 1 (futureFrom t e) ∂μ) = μ (L ⁻¹' (U ×ˢ V)) := by
      rw [← lintegral_indicator_one hB]
      apply lintegral_congr
      intro e
      by_cases heU : excursionRestrict t e ∈ U <;>
        by_cases heV : futureFrom t e ∈ V <;> simp [L, heU, heV]
    have hright : (μ ⊗ₘ κ) (R ⁻¹' (U ×ˢ V)) =
        ∫⁻ e, U.indicator 1 (excursionRestrict t e) *
          (∫⁻ g, V.indicator 1 g ∂killedStableKernel θ (e.valueNN t)) ∂μ := by
      rw [Measure.compProd_apply hC]
      apply lintegral_congr
      intro e
      have hslice : Prod.mk e ⁻¹' (R ⁻¹' (U ×ˢ V)) =
          if excursionRestrict t e ∈ U then V else ∅ := by
        ext g
        by_cases he : excursionRestrict t e ∈ U <;> simp [R, he]
      rw [hslice, hκapply, lintegral_indicator_one hV]
      by_cases he : excursionRestrict t e ∈ U <;> simp [he]
    exact hleft.symm.trans (hsm.trans hright.symm)
  obtain ⟨CF, hCF⟩ := hFb
  obtain ⟨CG, hCG⟩ := hGb
  let H : D (t : ℝ) ℝ × DLoc → ℝ := fun p => F p.1 * G p.2
  have hH : Measurable H := (hF.comp measurable_fst).mul (hG.comp measurable_snd)
  have hInt : Integrable (fun p : Excursion × DLoc => H (R p)) (μ ⊗ₘ κ) := by
    apply Integrable.of_bound (hH.comp hR).aestronglyMeasurable (|CF| * |CG|)
    apply Eventually.of_forall
    intro p
    change ‖F (excursionRestrict t p.1) * G p.2‖ ≤ |CF| * |CG|
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul ((hCF _).trans (le_abs_self CF)) ((hCG _).trans (le_abs_self CG))
      (abs_nonneg _) (abs_nonneg _)
  calc
    _ = ∫ p, H p ∂μ.map L :=
      (integral_map hL.aemeasurable hH.aestronglyMeasurable).symm
    _ = ∫ p, H p ∂(μ ⊗ₘ κ).map R := by rw [hjoint]
    _ = ∫ p, H (R p) ∂(μ ⊗ₘ κ) :=
      integral_map hR.aemeasurable hH.aestronglyMeasurable
    _ = ∫ e, ∫ g, F (excursionRestrict t e) * G g ∂κ e ∂μ :=
      Measure.integral_compProd hInt
    _ = _ := by
      apply integral_congr_ae
      apply Eventually.of_forall
      intro e
      change (∫ g, F (excursionRestrict t e) * G g ∂κ e) =
        F (excursionRestrict t e) * (∫ g, G g ∂killedStableKernel θ (e.valueNN t))
      rw [integral_const_mul, hκapply]

private lemma measurable_leftLim_dLoc (s : ℝ≥0) (hs : 0 < s) :
    Measurable (fun f : DLoc => Function.leftLim f.1 s) := by
  apply measurable_of_tendsto_metrizable (fun n : ℕ =>
    DLoc.measurable_eval (s - 1 / (n + 1 : ℝ≥0)))
  apply tendsto_pi_nhds.mpr
  intro f
  have hu : Tendsto (fun n : ℕ => s - 1 / (n + 1 : ℝ≥0)) atTop (𝓝[<] s) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · simpa only [tsub_zero] using (tendsto_const_nhds (x := s)).sub
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ≥0))
    · exact Eventually.of_forall fun n => tsub_lt_self hs (by positivity)
  exact (f.2.tendsto_nhdsLT_leftLim s).comp hu

private lemma continuousAt_stopLocAt {f : DLoc} {s : ℝ≥0}
    (hf : ContinuousAt f.1 s) (a : WithTop ℝ≥0) :
    ContinuousAt (stopLocAt a f).1 s := by
  induction a using WithTop.recTopCoe with
  | top => exact hf
  | coe a =>
    change ContinuousAt (fun u : ℝ≥0 => f.1 (min u a)) s
    by_cases has : a < s
    · apply continuousAt_const.congr_of_eventuallyEq
      filter_upwards [eventually_gt_nhds has] with u hu
      rw [min_eq_right hu.le]
    · have hmin : min s a = s := min_eq_left (le_of_not_gt has)
      have hfc : ContinuousAt f.1 (min s a) := hmin.symm ▸ hf
      exact hfc.comp (f := fun u : ℝ≥0 => min u a) (x := s)
        (continuous_id.min continuous_const).continuousAt

/-- **No fixed jumps under `N`**: for each `t > 0`, `N`-a.e. excursion is left-continuous at
`t` (restart at `t/2`; the killed path creates no jump since the passage creeps). -/
theorem N_noFixedJump {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (t : ℝ≥0) (ht : 0 < t) :
    ∀ᵐ e ∂(excursionMeasure θ), Function.leftLim e.path.1 t = e.path.1 t := by
  classical
  let r : ℝ≥0 := t / 2
  have hr : 0 < r := div_pos ht (by norm_num)
  have hrt : r < t := div_lt_self ht (by norm_num)
  have hrr : r + r = t := add_halves t
  let B : Set DLoc := {g | Function.leftLim g.1 r ≠ g.1 r}
  have hB : MeasurableSet B :=
    (measurableSet_eq_fun (measurable_leftLim_dLoc r hr) (DLoc.measurable_eval r)).compl
  let G : DLoc → ℝ≥0∞ := B.indicator 1
  have hG : Measurable G := measurable_const.indicator hB
  have hk (y : ℝ≥0) : (∫⁻ g, G g ∂killedStableKernel θ y) = 0 := by
    have hkm : Measurable (killedPath y) :=
      measurable_killedPath_uncurry.comp (measurable_const.prodMk measurable_id)
    rw [killedStableKernel_apply, lintegral_map hG hkm]
    apply lintegral_eq_zero_of_ae_eq_zero
    filter_upwards [ae_continuousAt_stableLocalLaw hθ r] with f hf
    have hcont : ContinuousAt (killedPath y f).1 r :=
      continuousAt_const.add (continuousAt_stopLocAt hf (firstPassageBelow y f))
    have hnot : killedPath y f ∉ B := fun hne => hne hcont.continuousWithinAt.leftLim_eq
    simp only [G, Set.indicator_of_notMem hnot, Pi.zero_apply]
  have hmarkov := excursion_markov_lintegral hθ r hr (fun _ => 1) measurable_const G hG
  have hzero : (∫⁻ e in {e : Excursion | r < e.lifetime},
      G (futureFrom r e) ∂excursionMeasure θ) = 0 := by
    simpa only [one_mul, hk, lintegral_zero] using hmarkov
  have hsurv : MeasurableSet {e : Excursion | r < e.lifetime} :=
    measurableSet_lt measurable_const measurable_excursion_lifetime
  have hfuture : ∀ᵐ e ∂excursionMeasure θ, r < e.lifetime →
      Function.leftLim (futureFrom r e).1 r = (futureFrom r e).1 r := by
    apply (ae_restrict_iff' hsurv).mp
    have hae := (lintegral_eq_zero_iff (hG.comp (measurable_futureFrom r))).mp hzero
    filter_upwards [hae] with e he
    by_contra hn
    have hmem : futureFrom r e ∈ B := hn
    change G (futureFrom r e) = 0 at he
    simp only [G, Set.indicator_of_mem hmem, Pi.one_apply, one_ne_zero] at he
  filter_upwards [hfuture] with e he
  by_cases halive : r < e.lifetime
  · let _ : (𝓝[<] r).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, hr⟩
    have hmap : Tendsto (fun u : ℝ≥0 => r + u) (𝓝[<] r) (𝓝[<] (r + r)) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
      · exact (continuous_const.add continuous_id).continuousAt.tendsto.mono_left
          nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with u hu
        exact add_lt_add_of_le_of_lt le_rfl hu
    have hlim : Tendsto (futureFrom r e).1 (𝓝[<] r)
        (𝓝 (Function.leftLim e.path.1 (r + r))) := by
      have h := (e.path.2.tendsto_nhdsLT_leftLim (r + r)).comp hmap
      convert h using 1
      funext u
      exact futureFrom_apply r e u
    have heq := tendsto_nhds_unique ((futureFrom r e).2.tendsto_nhdsLT_leftLim r) hlim
    have hval := he halive
    rw [heq, futureFrom_apply, hrr] at hval
    exact hval
  · have hζt : e.lifetime < t := (le_of_not_gt halive).trans_lt hrt
    have hcont : ContinuousAt e.path.1 t := by
      apply continuousAt_const.congr_of_eventuallyEq
      filter_upwards [eventually_gt_nhds hζt] with u hu
      exact e.2.2.2 u hu.le
    exact hcont.continuousWithinAt.leftLim_eq

end BGW.StableTrees
