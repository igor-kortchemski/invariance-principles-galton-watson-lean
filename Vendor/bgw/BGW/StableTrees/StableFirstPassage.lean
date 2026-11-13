/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.StableFirstPassagePath
public import BGW.StableTrees.StableLocalMarkov

import Mathlib.Probability.Martingale.OptionalSampling
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# First passage of the spectrally positive local stable process

This file proves downward creeping, finiteness and the Laplace transform of the strict first
passage below a positive level. Bounded stopping is obtained by dyadic approximation from above
(J. Bertoin, *Lévy Processes*, Cambridge University Press, 1996, Chapter VII, Theorem 1;
D. Revuz and M. Yor, *Continuous Martingales and Brownian Motion*, 3rd ed., Springer, 1999,
Chapter II, for optional stopping).
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace BGW.StableTrees
open BGW.Skorokhod

private noncomputable def dyadicUp (n : ℕ) (r : ℝ≥0) : ℝ≥0 :=
  Real.toNNReal (((⌈(r : ℝ) * 2 ^ n⌉₊ : ℕ) : ℝ) / 2 ^ n)

private noncomputable def roundedTime (t : ℝ≥0) (n : ℕ) (τ : WithTop ℝ≥0) : ℝ≥0 :=
  min t (dyadicUp n (τ.untopD 0))

private lemma coe_dyadicUp (n : ℕ) (r : ℝ≥0) :
    (dyadicUp n r : ℝ) = (((⌈(r : ℝ) * 2 ^ n⌉₊ : ℕ) : ℝ) / 2 ^ n) := by
  rw [dyadicUp, Real.coe_toNNReal]
  positivity

private lemma le_dyadicUp (n : ℕ) (r : ℝ≥0) : r ≤ dyadicUp n r := by
  rw [← NNReal.coe_le_coe, coe_dyadicUp]
  apply (le_div_iff₀ (show (0 : ℝ) < 2 ^ n by positivity)).2
  exact Nat.le_ceil _

private lemma tendsto_dyadicUp (r : ℝ≥0) :
    Tendsto (fun n => dyadicUp n r) atTop (𝓝 r) := by
  apply NNReal.tendsto_coe.1
  simp_rw [coe_dyadicUp]
  exact (tendsto_nat_ceil_mul_div_atTop r.2).comp
    (tendsto_pow_atTop_atTop_of_one_lt (show (1 : ℝ) < 2 by norm_num))

private lemma roundedTime_le (t : ℝ≥0) (n : ℕ) (τ : WithTop ℝ≥0) :
    roundedTime t n τ ≤ t := min_le_left _ _

private lemma le_roundedTime {t r : ℝ≥0} {τ : WithTop ℝ≥0}
    (hτ : τ = (r : WithTop ℝ≥0)) (hrt : r ≤ t) (n : ℕ) : r ≤ roundedTime t n τ := by
  rw [roundedTime, hτ, WithTop.untopD_coe]
  exact le_min hrt (le_dyadicUp n r)

private lemma tendsto_roundedTime {t r : ℝ≥0} {τ : WithTop ℝ≥0}
    (hτ : τ = (r : WithTop ℝ≥0)) :
    Tendsto (fun n => roundedTime t n τ) atTop (𝓝 (min t r)) := by
  simpa only [roundedTime, hτ, WithTop.untopD_coe] using
    tendsto_const_nhds.min (tendsto_dyadicUp r)

private lemma countable_range_roundedTime (t : ℝ≥0) (n : ℕ) (τ : DLoc → WithTop ℝ≥0) :
    (Set.range (fun f => (roundedTime t n (τ f) : WithTop ℝ≥0))).Countable := by
  apply (Set.countable_range (fun k : ℕ =>
    (min t (Real.toNNReal ((k : ℝ) / 2 ^ n)) : WithTop ℝ≥0))).mono
  rintro _ ⟨f, rfl⟩
  refine ⟨⌈(((τ f).untopD 0 : ℝ≥0) : ℝ) * 2 ^ n⌉₊, ?_⟩
  simp only [roundedTime, dyadicUp]
  norm_cast

private lemma dyadicUp_le_iff {n : ℕ} {r s : ℝ≥0} :
    dyadicUp n r ≤ s ↔ (r : ℝ) * 2 ^ n ≤ ⌊(s : ℝ) * 2 ^ n⌋₊ := by
  rw [← NNReal.coe_le_coe, coe_dyadicUp, div_le_iff₀ (by positivity)]
  constructor
  · intro h
    have hc : ⌈(r : ℝ) * 2 ^ n⌉₊ ≤ ⌊(s : ℝ) * 2 ^ n⌋₊ := by
      by_cases hz : ⌈(r : ℝ) * 2 ^ n⌉₊ = 0
      · simp [hz]
      · exact (Nat.le_floor_iff' hz).2 h
    exact (Nat.ceil_le).1 hc
  · intro h
    have hn := (Nat.ceil_le).2 h
    have hn' : (⌈(r : ℝ) * 2 ^ n⌉₊ : ℝ) ≤ (⌊(s : ℝ) * 2 ^ n⌋₊ : ℝ) := by
      exact_mod_cast hn
    exact hn'.trans (Nat.floor_le (by positivity : 0 ≤ (s : ℝ) * 2 ^ n))

private lemma roundedTime_le_iff {n : ℕ} {t r s : ℝ≥0} {τ : WithTop ℝ≥0}
    (hτ : τ = (r : WithTop ℝ≥0)) (hst : s < t) :
    roundedTime t n τ ≤ s ↔ (r : ℝ) * 2 ^ n ≤ ⌊(s : ℝ) * 2 ^ n⌋₊ := by
  constructor
  · intro h
    apply dyadicUp_le_iff.mp
    rw [roundedTime, hτ, WithTop.untopD_coe] at h
    have hut : dyadicUp n r ≤ t := by
      by_contra hn
      have htn : t ≤ dyadicUp n r := le_of_not_ge hn
      rw [min_eq_left htn] at h
      exact (not_le_of_gt hst) h
    rwa [min_eq_right hut] at h
  · intro h
    have hu : dyadicUp n r ≤ s := dyadicUp_le_iff.mpr h
    rw [roundedTime, hτ, WithTop.untopD_coe]
    exact (min_le_right _ _).trans hu

private lemma isStoppingTime_roundedTime {t : ℝ≥0} {τ : DLoc → WithTop ℝ≥0}
    (hτ : IsStoppingTime DLoc.filtration τ) (hτ_le : ∀ f, τ f ≤ t) (n : ℕ) :
    IsStoppingTime DLoc.filtration (fun f => (roundedTime t n (τ f) : WithTop ℝ≥0)) := by
  intro s
  by_cases hst : s < t
  · have hset : {f : DLoc | (roundedTime t n (τ f) : WithTop ℝ≥0) ≤ s} =
        {f : DLoc | τ f ≤ (Real.toNNReal
          (((⌊(s : ℝ) * 2 ^ n⌋₊ : ℕ) : ℝ) / 2 ^ n) : WithTop ℝ≥0)} := by
      ext f
      simp only [Set.mem_ofPred_eq, WithTop.coe_le_coe]
      have hfin : τ f ≠ ⊤ := ne_top_of_le_ne_top WithTop.coe_ne_top (hτ_le f)
      obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp hfin
      rw [← hr, WithTop.coe_le_coe,
        roundedTime_le_iff (τ := ((r : ℝ≥0) : WithTop ℝ≥0)) rfl hst]
      constructor
      · intro h
        rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ (by positivity)]
        exact (le_div_iff₀ (show (0 : ℝ) < 2 ^ n by positivity)).2 h
      · intro h
        have hr : (r : ℝ) ≤
            (((⌊(s : ℝ) * 2 ^ n⌋₊ : ℕ) : ℝ) / 2 ^ n) := by
          have hr' : r ≤ Real.toNNReal
              (((⌊(s : ℝ) * 2 ^ n⌋₊ : ℕ) : ℝ) / 2 ^ n) := h
          rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ (by positivity)] at hr'
          exact hr'
        calc
          (r : ℝ) * 2 ^ n ≤ (((⌊(s : ℝ) * 2 ^ n⌋₊ : ℕ) : ℝ) / 2 ^ n) * 2 ^ n :=
            mul_le_mul_of_nonneg_right hr (by positivity)
          _ = (⌊(s : ℝ) * 2 ^ n⌋₊ : ℝ) := div_mul_cancel₀ _ (by positivity)
    rw [hset]
    exact DLoc.filtration.mono (by
      rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ (by positivity)]
      exact (div_le_iff₀ (by positivity)).2 (Nat.floor_le (by positivity))) _ (hτ _)
  · have hset : {f : DLoc | (roundedTime t n (τ f) : WithTop ℝ≥0) ≤ s} = Set.univ := by
      ext f
      simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true, WithTop.coe_le_coe]
      exact (roundedTime_le t n (τ f)).trans (le_of_not_gt hst)
    rw [hset]
    exact MeasurableSet.univ

private lemma untopA_coe_nnreal (r : ℝ≥0) :
    ((r : WithTop ℝ≥0).untopA) = r := by
  rw [WithTop.untopA_eq_untop WithTop.coe_ne_top]
  exact (WithTop.untop_eq_iff _).2 rfl

private lemma integral_stoppedValue_exp_eq_one {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    {u : ℝ} (hu : 0 ≤ u) {t : ℝ≥0} {τ : DLoc → WithTop ℝ≥0}
    (hτ : IsStoppingTime DLoc.filtration τ) (hτ_le : ∀ f, τ f ≤ t) :
    ∫ f, stoppedValue (fun (s : ℝ≥0) (f : DLoc) =>
      Real.exp (-u * DLoc.eval s f - (s : ℝ) * u ^ θ)) τ f ∂(stableLocalLaw θ) = 1 := by
  let M : ℝ≥0 → DLoc → ℝ := fun s f => Real.exp (-u * DLoc.eval s f - (s : ℝ) * u ^ θ)
  let P : Measure DLoc := stableLocalLaw θ
  have hM : Martingale M DLoc.filtration P := martingale_exp_stableLocalLaw hθ hu
  have hM0 : M 0 =ᵐ[P] fun _ => 1 := by
    filter_upwards [ae_eval_zero_stableLocalLaw hθ] with f hf
    change Real.exp (-u * f.1 0 - (0 : ℝ) * u ^ θ) = 1
    rw [hf]
    simp
  have hMt : (∫ f, M t f ∂P) = 1 := by
    have hc := hM.condExp_ae_eq (show (0 : ℝ≥0) ≤ t from bot_le)
    calc
      _ = ∫ f, P[M t | DLoc.filtration 0] f ∂P :=
        (integral_condExp (DLoc.filtration.le 0)).symm
      _ = ∫ f, M 0 f ∂P := integral_congr_ae hc
      _ = 1 := by rw [integral_congr_ae hM0]; simp
  have hleft : ∀ n : ℕ, stoppedValue M
      (fun f => (roundedTime t n (τ f) : WithTop ℝ≥0)) =ᵐ[P]
      P[M t | (isStoppingTime_roundedTime hτ hτ_le n).measurableSpace] := by
    intro n
    exact hM.stoppedValue_ae_eq_condExp_of_le_const_of_countable_range
      (isStoppingTime_roundedTime hτ hτ_le n)
      (fun f => by exact_mod_cast roundedTime_le t n (τ f))
      (countable_range_roundedTime t n τ)
  have hUI : UniformIntegrable (fun n => stoppedValue M
      (fun f => (roundedTime t n (τ f) : WithTop ℝ≥0))) 1 P := by
    apply (hM.integrable t).uniformIntegrable_condExp
      (fun n => (isStoppingTime_roundedTime hτ hτ_le n).measurableSpace_le) |>.ae_eq
    exact fun n => (hleft n).symm
  have hlim : ∀ f : DLoc, Tendsto
      (fun n => stoppedValue M (fun f => (roundedTime t n (τ f) : WithTop ℝ≥0)) f)
      atTop (𝓝 (stoppedValue M τ f)) := by
    intro f
    have hfin : τ f ≠ ⊤ := ne_top_of_le_ne_top WithTop.coe_ne_top (hτ_le f)
    obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp hfin
    have hrt : r ≤ t := by exact_mod_cast hr ▸ hτ_le f
    have htend : Tendsto (fun n => roundedTime t n (τ f)) atTop (𝓝[Set.Ici r] r) := by
      apply tendsto_nhdsWithin_iff.mpr
      refine ⟨?_, Eventually.of_forall fun n => le_roundedTime hr.symm hrt n⟩
      simpa only [← hr, min_eq_right hrt, WithTop.untopD_coe] using
        (tendsto_roundedTime (t := t) hr.symm)
    have hright : ContinuousWithinAt (fun s : ℝ≥0 => M s f) (Set.Ici r) r := by
      apply continuousWithinAt_Ioi_iff_Ici.mp
      change ContinuousWithinAt (fun s : ℝ≥0 =>
        Real.exp (-u * f.1 s - (s : ℝ) * u ^ θ)) (Set.Ioi r) r
      apply Real.continuous_exp.continuousAt.comp_continuousWithinAt
      apply ContinuousWithinAt.sub
      · have heq : (fun s : ℝ≥0 => -u * f.1 s) =
            -((fun _ : ℝ≥0 => u) * f.1) := by
          funext s
          simp only [Pi.neg_apply, Pi.mul_apply, neg_mul]
        rw [heq]
        exact ((continuousWithinAt_const (b := u)).mul (f.2.isRightContinuous r)).neg
      · exact continuous_subtype_val.continuousWithinAt.mul
          (continuousWithinAt_const (b := u ^ θ))
    have hseq : (fun n => stoppedValue M
        (fun f => (roundedTime t n (τ f) : WithTop ℝ≥0)) f) =
        (fun n => M (roundedTime t n (τ f)) f) := by
      funext n
      change M ((roundedTime t n (τ f) : WithTop ℝ≥0).untopA) f =
        M (roundedTime t n (τ f)) f
      rw [untopA_coe_nnreal]
    have hval : stoppedValue M τ f = M r f := by
      change M ((τ f).untopA) f = M r f
      rw [← hr, untopA_coe_nnreal]
    rw [hseq, hval]
    exact hright.tendsto.comp htend
  have hmeas : ∀ n : ℕ, AEStronglyMeasurable (stoppedValue M
      (fun f => (roundedTime t n (τ f) : WithTop ℝ≥0))) P := by
    intro n
    have hτn := isStoppingTime_roundedTime hτ hτ_le n
    have hbdd : ∀ f, (roundedTime t n (τ f) : WithTop ℝ≥0) ≤ t := fun f =>
      WithTop.coe_le_coe.mpr (roundedTime_le t n (τ f))
    have hm := (stronglyMeasurable_stoppedValue_of_le
      DLoc.isStronglyProgressive_eval hτn hbdd).mono
      (DLoc.filtration.le t)
    have htime : Measurable (fun f : DLoc =>
        (roundedTime t n (τ f) : WithTop ℝ≥0).untopA) :=
      ((hτn.measurable_of_le hbdd).mono (DLoc.filtration.le t) le_rfl).untopA
    have htime' : StronglyMeasurable (fun f : DLoc =>
        (((roundedTime t n (τ f) : WithTop ℝ≥0).untopA : ℝ≥0) : ℝ) * u ^ θ) :=
      ((measurable_coe_nnreal_real.comp htime).mul measurable_const).stronglyMeasurable
    exact (Real.continuous_exp.comp_stronglyMeasurable
      ((hm.const_mul (-u)).sub htime')).aestronglyMeasurable
  have htim := tendstoInMeasure_of_tendsto_ae hmeas (Eventually.of_forall hlim)
  have hint : Integrable (stoppedValue M τ) P := hUI.integrable_of_tendstoInMeasure htim
  have hL1 := tendsto_Lp_finite_of_tendstoInMeasure le_rfl ENNReal.one_ne_top hmeas
    (memLp_one_iff_integrable.mpr hint) hUI.1 htim
  have hi := tendsto_integral_of_L1' (stoppedValue M τ)
    (Eventually.of_forall (fun n => integrable_condExp.congr (hleft n).symm)) hL1
  have hnorm : ∀ n : ℕ, ∫ f, stoppedValue M
      (fun f => (roundedTime t n (τ f) : WithTop ℝ≥0)) f ∂P = 1 := by
    intro n
    calc
      _ = ∫ f, P[M t | (isStoppingTime_roundedTime hτ hτ_le n).measurableSpace] f ∂P :=
        integral_congr_ae (hleft n)
      _ = ∫ f, M t f ∂P :=
        integral_condExp (isStoppingTime_roundedTime hτ hτ_le n).measurableSpace_le
      _ = 1 := hMt
  exact tendsto_nhds_unique hi (by simpa only [hnorm] using
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)))

private lemma exp_stopped_aestronglyMeasurable {θ u : ℝ} {t : ℝ≥0}
    {τ : DLoc → WithTop ℝ≥0} (hτ : IsStoppingTime DLoc.filtration τ)
    (hτ_le : ∀ f, τ f ≤ t) :
    AEStronglyMeasurable (stoppedValue (fun (s : ℝ≥0) (f : DLoc) =>
      Real.exp (-u * DLoc.eval s f - (s : ℝ) * u ^ θ)) τ)
      (stableLocalLaw θ : Measure DLoc) := by
  have hm := (stronglyMeasurable_stoppedValue_of_le DLoc.isStronglyProgressive_eval hτ hτ_le).mono
    (DLoc.filtration.le t)
  have htime : Measurable (fun f : DLoc => (τ f).untopA) :=
    ((hτ.measurable_of_le hτ_le).mono (DLoc.filtration.le t) le_rfl).untopA
  have htime' : StronglyMeasurable (fun f : DLoc => (((τ f).untopA : ℝ) * u ^ θ)) :=
    ((measurable_coe_nnreal_real.comp htime).mul measurable_const).stronglyMeasurable
  exact (Real.continuous_exp.comp_stronglyMeasurable
    ((hm.const_mul (-u)).sub htime')).aestronglyMeasurable

private lemma stopped_exp_le_of_good {x : ℝ} (hx : 0 < x) {u : ℝ} (hu : 0 ≤ u) {θ : ℝ}
    {f : DLoc} (hf0 : f.1 0 = 0)
    (hno : ∀ t : ℝ≥0, Function.leftLim f.1 t ≤ f.1 t) (t : ℝ≥0) :
    ‖stoppedValue (fun (s : ℝ≥0) (f : DLoc) =>
      Real.exp (-u * DLoc.eval s f - (s : ℝ) * u ^ θ))
      (fun f => min (t : WithTop ℝ≥0) (DLoc.strictPassageBelow (-x) f)) f‖ ≤
        Real.exp (u * x) := by
  have hstart : -x < f.1 0 := by rw [hf0]; exact neg_lt_zero.mpr hx
  have hub : ∀ r : ℝ≥0, -x ≤ f.1 r →
      Real.exp (-u * f.1 r - (r : ℝ) * u ^ θ) ≤ Real.exp (u * x) := by
    intro r hr
    apply Real.exp_le_exp.mpr
    have hp : 0 ≤ u ^ θ := Real.rpow_nonneg hu θ
    have hnn : 0 ≤ x + f.1 r := by linarith
    exact (sub_le_self _ (mul_nonneg r.2 hp)).trans
      (by nlinarith [mul_nonneg hu hnn])
  change ‖Real.exp (-u * f.1
    ((min (t : WithTop ℝ≥0) (DLoc.strictPassageBelow (-x) f)).untopA) -
    (((min (t : WithTop ℝ≥0) (DLoc.strictPassageBelow (-x) f)).untopA : ℝ≥0) : ℝ) *
      u ^ θ)‖ ≤ Real.exp (u * x)
  rw [Real.norm_of_nonneg (Real.exp_nonneg _)]
  by_cases hT : DLoc.strictPassageBelow (-x) f = ⊤
  · rw [hT, min_eq_left le_top, untopA_coe_nnreal]
    exact hub t (le_eval_of_lt_strictPassageBelow (by rw [hT]; exact WithTop.coe_lt_top t))
  · obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp hT
    rw [← hr]
    by_cases hrt : r ≤ t
    · rw [min_eq_right (WithTop.coe_le_coe.mpr hrt), untopA_coe_nnreal]
      exact hub r ((eval_eq_of_strictPassageBelow_eq_coe hno hr.symm hstart).ge)
    · have htr : t < r := lt_of_not_ge hrt
      rw [min_eq_left (WithTop.coe_le_coe.mpr htr.le), untopA_coe_nnreal]
      exact hub t (le_eval_of_lt_strictPassageBelow (by rw [← hr]; exact_mod_cast htr))

private lemma integral_partial_laplace {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    {x q : ℝ} (hx : 0 < x) (hq : 0 < q) :
    ∫ f : DLoc, (if DLoc.strictPassageBelow (-x) f = ⊤ then 0 else
      Real.exp (-q * (((DLoc.strictPassageBelow (-x) f).untopD 0 : ℝ≥0) : ℝ)))
      ∂(stableLocalLaw θ : Measure DLoc) = Real.exp (-x * q ^ (1 / θ)) := by
  let u : ℝ := q ^ (1 / θ)
  let T : DLoc → WithTop ℝ≥0 := DLoc.strictPassageBelow (-x)
  let M : ℝ≥0 → DLoc → ℝ := fun t f => Real.exp (-u * DLoc.eval t f - (t : ℝ) * u ^ θ)
  let P : Measure DLoc := stableLocalLaw θ
  let F : ℕ → DLoc → ℝ := fun n => stoppedValue M (fun f => min (n : WithTop ℝ≥0) (T f))
  let L : DLoc → ℝ := fun f => if T f = ⊤ then 0 else
    Real.exp (u * x - q * (((T f).untopD 0 : ℝ≥0) : ℝ))
  have hu : 0 ≤ u := Real.rpow_nonneg hq.le _
  have huq : u ^ θ = q := by
    dsimp [u]
    rw [← Real.rpow_mul hq.le]
    have hθ0 : θ ≠ 0 := ne_of_gt (zero_lt_one.trans hθ.1)
    rw [one_div, inv_mul_cancel₀ hθ0, Real.rpow_one]
  have hT : IsStoppingTime DLoc.filtration T := DLoc.isStoppingTime_strictPassageBelow _
  have hTn : ∀ n : ℕ, IsStoppingTime DLoc.filtration
      (fun f => min (n : WithTop ℝ≥0) (T f)) := fun n =>
    (isStoppingTime_const DLoc.filtration n).min hT
  have hgood : ∀ᵐ f ∂P, f.1 0 = 0 ∧
      ∀ t : ℝ≥0, Function.leftLim f.1 t ≤ f.1 t :=
    (ae_eval_zero_stableLocalLaw hθ).and (ae_leftLim_le_stableLocalLaw hθ)
  have hbound : ∀ n : ℕ, ∀ᵐ f ∂P, ‖F n f‖ ≤ Real.exp (u * x) := by
    intro n
    filter_upwards [hgood] with f hf
    exact stopped_exp_le_of_good hx hu hf.1 hf.2 n
  have hmeas : ∀ n : ℕ, AEStronglyMeasurable (F n) P := by
    intro n
    exact exp_stopped_aestronglyMeasurable (hTn n) (fun f => min_le_left _ _)
  have hlim : ∀ᵐ f ∂P, Tendsto (fun n => F n f) atTop (𝓝 (L f)) := by
    filter_upwards [hgood] with f hf
    by_cases hTf : T f = ⊤
    · have he : Tendsto (fun n : ℕ => Real.exp (-((n : ℝ) * q))) atTop (𝓝 0) :=
        Real.tendsto_exp_neg_atTop_nhds_zero.comp
          (tendsto_natCast_atTop_atTop.atTop_mul_const hq)
      have hz : Tendsto (fun n : ℕ => Real.exp (u * x - (n : ℝ) * q)) atTop (𝓝 0) := by
        have hmul : Tendsto (fun n : ℕ => Real.exp (u * x) * Real.exp (-((n : ℝ) * q)))
            atTop (𝓝 (Real.exp (u * x) * 0)) := tendsto_const_nhds.mul he
        simpa only [mul_zero, ← Real.exp_add, sub_eq_add_neg] using hmul
      have hFval : ∀ n : ℕ, F n f = Real.exp (-u * f.1 n - (n : ℝ) * u ^ θ) := by
        intro n
        change Real.exp (-u * f.1 ((min (n : WithTop ℝ≥0) (T f)).untopA) -
          (((min (n : WithTop ℝ≥0) (T f)).untopA : ℝ≥0) : ℝ) * u ^ θ) =
            Real.exp (-u * f.1 n - (n : ℝ) * u ^ θ)
        rw [hTf, min_eq_left le_top]
        congr 1
      have hz0 : Tendsto (fun n : ℕ => Real.exp (-u * f.1 n - (n : ℝ) * u ^ θ))
          atTop (𝓝 0) := by
        apply squeeze_zero (g := fun n : ℕ => Real.exp (u * x - (n : ℝ) * q))
          (fun n => Real.exp_nonneg _)
        · intro n
          apply Real.exp_le_exp.mpr
          rw [huq]
          have hval : -x ≤ f.1 n := le_eval_of_lt_strictPassageBelow
            (show (n : WithTop ℝ≥0) < T f by
              rw [hTf]
              exact WithTop.coe_lt_top _)
          have hnn : 0 ≤ x + f.1 n := by linarith
          nlinarith [mul_nonneg hu hnn]
        · exact hz
      have hz' : Tendsto (fun n : ℕ => F n f) atTop (𝓝 0) :=
        (tendsto_congr' (Eventually.of_forall hFval)).mpr hz0
      simpa only [L, hTf, ite_eq_left] using hz'
    · obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp hTf
      have hrn : ∃ N : ℕ, r ≤ (N : ℝ≥0) := by
        obtain ⟨N, hN⟩ := exists_nat_ge (r : ℝ)
        exact ⟨N, by exact_mod_cast hN⟩
      obtain ⟨N, hN⟩ := hrn
      have hconst : ∀ n ≥ N, F n f = L f := by
        intro n hn
        have hmin : min (n : WithTop ℝ≥0) (T f) = (r : WithTop ℝ≥0) := by
          rw [← hr]
          exact min_eq_right (WithTop.coe_le_coe.mpr
            (hN.trans (by exact_mod_cast hn)))
        have hval : f.1 r = -x := eval_eq_of_strictPassageBelow_eq_coe hf.2 hr.symm (by
          rw [hf.1]
          exact neg_lt_zero.mpr hx)
        change Real.exp (-u * f.1 ((min (n : WithTop ℝ≥0) (T f)).untopA) -
          (((min (n : WithTop ℝ≥0) (T f)).untopA : ℝ≥0) : ℝ) * u ^ θ) =
            if T f = ⊤ then 0 else Real.exp (u * x - q * (((T f).untopD 0 : ℝ≥0) : ℝ))
        rw [hmin, ← hr]
        simp only [WithTop.untopD_coe, WithTop.coe_ne_top, ↓reduceIte]
        rw [hval, huq]
        congr 1
        ring
      exact tendsto_atTop_of_eventually_const hconst
  have hDCT := tendsto_integral_of_dominated_convergence (fun _ : DLoc => Real.exp (u * x))
    hmeas (integrable_const _) hbound hlim
  have hint_L : (∫ f, L f ∂P) = 1 := by
    apply tendsto_nhds_unique hDCT
    have hconst : ∀ n : ℕ, (∫ f, F n f ∂P) = 1 := by
      intro n
      exact integral_stoppedValue_exp_eq_one hθ hu (hTn n) (fun f => min_le_left _ _)
    simpa only [hconst] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1))
  have hfactor : L = fun f => Real.exp (u * x) * (if T f = ⊤ then 0 else
      Real.exp (-q * (((T f).untopD 0 : ℝ≥0) : ℝ))) := by
    funext f
    by_cases hTf : T f = ⊤
    · simp [L, hTf]
    · simp only [L, hTf, ↓reduceIte]
      rw [← Real.exp_add]
      congr 1
      ring
  rw [hfactor, integral_const_mul] at hint_L
  let G : DLoc → ℝ := fun f => if T f = ⊤ then 0 else
    Real.exp (-q * (((T f).untopD 0 : ℝ≥0) : ℝ))
  change (∫ f, G f ∂P) = Real.exp (-x * u)
  change Real.exp (u * x) * (∫ f, G f ∂P) = 1 at hint_L
  calc
    (∫ f, G f ∂P) = Real.exp (-u * x) *
        (Real.exp (u * x) * (∫ f, G f ∂P)) := by
      rw [← mul_assoc, ← Real.exp_add]
      simp
    _ = Real.exp (-u * x) * 1 := by rw [hint_L]
    _ = Real.exp (-x * u) := by rw [mul_one]; dsimp [u]; congr 1; ring

private lemma ae_finite_passage_fixed {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    {x : ℝ} (hx : 0 < x) :
    ∀ᵐ f : DLoc ∂(stableLocalLaw θ : Measure DLoc),
      DLoc.strictPassageBelow (-x) f ≠ ⊤ := by
  let T : DLoc → WithTop ℝ≥0 := DLoc.strictPassageBelow (-x)
  let P : Measure DLoc := stableLocalLaw θ
  let S : Set DLoc := {f | T f ≠ ⊤}
  have hT : IsStoppingTime DLoc.filtration T := DLoc.isStoppingTime_strictPassageBelow _
  have hS : MeasurableSet S := hT.measurableSet_eq_top.compl
  have hm : ∀ q : ℝ, AEStronglyMeasurable (fun f : DLoc => if T f = ⊤ then 0 else
      Real.exp (-q * (((T f).untopD 0 : ℝ≥0) : ℝ))) P := by
    intro q
    have ht : Measurable (fun f : DLoc => (((T f).untopD 0 : ℝ≥0) : ℝ)) :=
      measurable_coe_nnreal_real.comp (hT.measurable'.untopD 0)
    exact (Measurable.ite hT.measurableSet_eq_top measurable_const
      (Real.measurable_exp.comp (measurable_const.mul ht))).aestronglyMeasurable
  have hbound : ∀ᶠ q in 𝓝[Set.Ioi (0 : ℝ)] 0, ∀ᵐ f ∂P,
      ‖if T f = ⊤ then 0 else Real.exp (-q * (((T f).untopD 0 : ℝ≥0) : ℝ))‖ ≤ 1 := by
    filter_upwards [self_mem_nhdsWithin] with q hq
    filter_upwards [] with f
    by_cases hTf : T f = ⊤
    · simp [hTf]
    · simp only [hTf, ↓reduceIte]
      rw [Real.norm_of_nonneg (Real.exp_nonneg _)]
      exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg
        (neg_nonpos.mpr hq.le) ((T f).untopD 0 : ℝ≥0).2)
  have hlim : ∀ f : DLoc, Tendsto
      (fun q : ℝ => if T f = ⊤ then 0 else
        Real.exp (-q * (((T f).untopD 0 : ℝ≥0) : ℝ))) (𝓝[Set.Ioi 0] 0)
      (𝓝 (S.indicator (1 : DLoc → ℝ) f)) := by
    intro f
    by_cases hTf : T f = ⊤
    · simp [S, hTf]
    · have hc : ContinuousAt (fun q : ℝ =>
          Real.exp (-q * (((T f).untopD 0 : ℝ≥0) : ℝ))) 0 := by fun_prop
      simpa [S, hTf] using hc.tendsto.mono_left nhdsWithin_le_nhds
  have hDCT := tendsto_integral_filter_of_dominated_convergence (fun _ : DLoc => (1 : ℝ))
    (Eventually.of_forall hm) hbound (integrable_const _) (Eventually.of_forall hlim)
  have heq : (fun q : ℝ => ∫ f : DLoc, (if T f = ⊤ then 0 else
      Real.exp (-q * (((T f).untopD 0 : ℝ≥0) : ℝ))) ∂P) =ᶠ[𝓝[Set.Ioi 0] 0]
      (fun q => Real.exp (-x * q ^ (1 / θ))) := by
    filter_upwards [self_mem_nhdsWithin] with q hq
    exact integral_partial_laplace hθ hx hq
  have hright : Tendsto (fun q : ℝ => Real.exp (-x * q ^ (1 / θ)))
      (𝓝[Set.Ioi 0] 0) (𝓝 1) := by
    have hθ0 : (1 / θ) ≠ 0 := div_ne_zero one_ne_zero
      (ne_of_gt (zero_lt_one.trans hθ.1))
    have hc : ContinuousAt (fun q : ℝ => Real.exp (-x * q ^ (1 / θ))) 0 := by
      apply Real.continuous_exp.continuousAt.comp
      exact continuousAt_const.mul
        (Real.continuousAt_rpow_const 0 (1 / θ) (Or.inr
          (one_div_nonneg.mpr (zero_le_one.trans hθ.1.le))))
    have hz : (0 : ℝ) ^ (1 / θ) = 0 := Real.zero_rpow hθ0
    simpa only [hz, mul_zero, neg_zero, Real.exp_zero] using
      hc.tendsto.mono_left nhdsWithin_le_nhds
  have hint := tendsto_nhds_unique (hDCT.congr' heq) hright
  rw [integral_indicator_one hS] at hint
  have hPS : P S = 1 := ENNReal.toReal_eq_one_iff _ |>.mp hint
  exact mem_ae_iff_prob_eq_one hS |>.mpr hPS

/-- **Finite first passage.** Almost surely, simultaneously for every level `x > 0`,
`T_x = inf{t | X_t < -x}` is finite. -/
theorem ae_strictPassageBelow_ne_top {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f : DLoc ∂(stableLocalLaw θ : Measure DLoc),
      ∀ x : ℝ, 0 < x → DLoc.strictPassageBelow (-x) f ≠ ⊤ := by
  have hrat : ∀ q : {q : ℚ // 0 < q}, ∀ᵐ f : DLoc ∂(stableLocalLaw θ : Measure DLoc),
      DLoc.strictPassageBelow (-(q : ℝ)) f ≠ ⊤ := by
    intro q
    exact ae_finite_passage_fixed hθ (by exact_mod_cast q.2)
  filter_upwards [ae_all_iff.mpr hrat] with f hf x hx
  obtain ⟨q : ℚ, hq⟩ := exists_rat_gt x
  have hqpos : 0 < q := by exact_mod_cast hx.trans hq
  exact strictPassageBelow_ne_top_of_le_neg hq.le (hf ⟨q, hqpos⟩)

/-- **Downward creeping.** Almost surely, for every level `x > 0` the first passage below `-x`
occurs continuously: `X_{T_x} = -x`. -/
theorem ae_creeping_down_stableLocalLaw {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f : DLoc ∂(stableLocalLaw θ : Measure DLoc),
      ∀ x : ℝ, 0 < x →
        ∃ t : ℝ≥0, DLoc.strictPassageBelow (-x) f = (t : WithTop ℝ≥0) ∧ f.1 t = -x := by
  filter_upwards [ae_strictPassageBelow_ne_top hθ, ae_leftLim_le_stableLocalLaw hθ,
    ae_eval_zero_stableLocalLaw hθ] with f hfin hno hf0 x hx
  obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.mp (hfin x hx)
  exact ⟨t, ht.symm, eval_eq_of_strictPassageBelow_eq_coe hno ht.symm (by
    rw [hf0]
    exact neg_lt_zero.mpr hx)⟩

/-- **Running infimum.** Almost surely `I` is continuous, nonincreasing and tends to `-∞`. -/
theorem ae_runningInf_continuous_antitone_tendsto {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f : DLoc ∂(stableLocalLaw θ : Measure DLoc),
      Continuous (runningInfLoc f) ∧ Antitone (runningInfLoc f) ∧
        Tendsto (runningInfLoc f) atTop atBot := by
  filter_upwards [ae_leftLim_le_stableLocalLaw hθ,
    ae_creeping_down_stableLocalLaw hθ] with f hno hc
  exact ⟨runningInfLoc_continuous hno, runningInfLoc_antitone f, runningInfLoc_tendsto_atBot hc⟩

/-- **Laplace transform of the passage time.** For `x > 0`, `q ≥ 0`:
`E[e^{-q T_x}] = e^{-x q^{1/θ}}` (with `T_x` finite a.s., read via `untopD 0`). -/
theorem integral_exp_neg_strictPassageBelow {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {x q : ℝ}
    (hx : 0 < x) (hq : 0 ≤ q) :
    ∫ f : DLoc, Real.exp (-q * (((DLoc.strictPassageBelow (-x) f).untopD 0 : ℝ≥0) : ℝ))
        ∂(stableLocalLaw θ : Measure DLoc) = Real.exp (-x * q ^ (1 / θ)) := by
  rcases hq.eq_or_lt with rfl | hq
  · have hθ0 : (1 / θ) ≠ 0 := div_ne_zero one_ne_zero
      (ne_of_gt (zero_lt_one.trans hθ.1))
    have hz : (0 : ℝ) ^ (1 / θ) = 0 := Real.zero_rpow hθ0
    simp only [zero_mul, neg_zero, Real.exp_zero, hz, mul_zero, integral_const]
    simp
  rw [← integral_partial_laplace hθ hx hq]
  apply integral_congr_ae
  filter_upwards [ae_finite_passage_fixed hθ hx] with f hf
  simp [hf]

/-- **Joint almost-sure event.** Almost surely, the path starts at `0` and, simultaneously for
every level `x > 0`, the first passage below `-x` is finite, positive, and the path takes the
value `-x` there. -/
theorem ae_firstPassageBelow_spec {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), f.1 0 = 0 ∧ ∀ x : ℝ≥0, 0 < x →
      firstPassageBelow x f < ⊤ ∧ 0 < firstPassageBelow x f ∧
        f.1 ((firstPassageBelow x f).untopD 0) = -(x : ℝ) := by
  filter_upwards [ae_eval_zero_stableLocalLaw hθ,
    ae_creeping_down_stableLocalLaw hθ] with f hf0 hc
  refine ⟨hf0, fun x hx => ?_⟩
  obtain ⟨t, ht, hval⟩ := hc (x : ℝ) (by exact_mod_cast hx)
  have hpos : 0 < firstPassageBelow x f := strictPassageBelow_pos_of_lt_eval_zero (by
    rw [hf0]
    exact neg_lt_zero.mpr (by exact_mod_cast hx))
  refine ⟨?_, hpos, ?_⟩
  · change DLoc.strictPassageBelow (-(x : ℝ)) f < ⊤
    rw [ht]
    exact WithTop.coe_lt_top _
  · change f.1 ((DLoc.strictPassageBelow (-(x : ℝ)) f).untopD 0) = -(x : ℝ)
    rw [ht, WithTop.untopD_coe]
    exact hval

/-- **Laplace transform, nonnegative form.** For `x > 0`, `q ≥ 0`. -/
theorem lintegral_exp_neg_firstPassageBelow {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {x : ℝ≥0}
    (hx : 0 < x) {q : ℝ} (hq : 0 ≤ q) :
    ∫⁻ f, ENNReal.ofReal (Real.exp (-q * (((firstPassageBelow x f).untopD 0 : ℝ≥0) : ℝ)))
        ∂(stableLocalLaw θ : Measure DLoc) =
      ENNReal.ofReal (Real.exp (-(x : ℝ) * q ^ (1 / θ))) := by
  have ht : Measurable (fun f : DLoc => (((firstPassageBelow x f).untopD 0 : ℝ≥0) : ℝ)) :=
    measurable_coe_nnreal_real.comp
      ((isStoppingTime_firstPassageBelow x).measurable'.untopD 0)
  have hm : Measurable (fun f : DLoc =>
      Real.exp (-q * (((firstPassageBelow x f).untopD 0 : ℝ≥0) : ℝ))) :=
    Real.measurable_exp.comp (measurable_const.mul ht)
  have hi : Integrable (fun f : DLoc =>
      Real.exp (-q * (((firstPassageBelow x f).untopD 0 : ℝ≥0) : ℝ)))
      (stableLocalLaw θ : Measure DLoc) := by
    apply Integrable.of_bound hm.aestronglyMeasurable 1
    filter_upwards [] with f
    rw [Real.norm_of_nonneg (Real.exp_nonneg _)]
    exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr hq) ((firstPassageBelow x f).untopD 0 : ℝ≥0).2)
  rw [← ofReal_integral_eq_lintegral_ofReal hi
    (Eventually.of_forall fun _ => Real.exp_nonneg _)]
  exact congrArg ENNReal.ofReal
    (integral_exp_neg_strictPassageBelow hθ (by exact_mod_cast hx) hq)

end BGW.StableTrees

