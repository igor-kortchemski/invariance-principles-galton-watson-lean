/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.SupremumCorrectionPath
import BGW.StableTrees.SupremumAuxLocalTimeConditionalLimit
import Mathlib.Probability.Martingale.OptionalSampling
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Bounded optional sampling with almost surely right continuous paths

Dyadic upper approximations preserve stopping times. Their stopped values are uniformly
integrable conditional expectations of a single terminal value. This permits passing to
a pathwise right continuous limit without completing the filtration or changing the process.

## References

* J. Bertoin, *Lévy Processes*, Cambridge University Press, 1996, Chapter IV.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees

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

/-- Bounded optional sampling for a progressive martingale whose paths are almost surely
right continuous; the raw representative need not be right continuous on exceptional paths. -/
theorem stoppedValue_ae_eq_condExp_of_ae_rightContinuous {P : Measure DLoc}
    [IsProbabilityMeasure P] {M : ℝ≥0 → DLoc → ℝ}
    (hM : Martingale M DLoc.filtration P)
    (hprog : IsStronglyProgressive DLoc.filtration M)
    (hright : ∀ᵐ f ∂P, ∀ r, ContinuousWithinAt (fun s => M s f) (Ici r) r)
    {T : ℝ≥0} {τ : DLoc → WithTop ℝ≥0}
    (hτ : IsStoppingTime DLoc.filtration τ) (hτ_le : ∀ f, τ f ≤ T) :
    stoppedValue M τ =ᵐ[P] P[M T | hτ.measurableSpace] := by
  let A : ℕ → DLoc → ℝ := fun n => stoppedValue M
    (fun f => (roundedTime T n (τ f) : WithTop ℝ≥0))
  have hτn (n : ℕ) := isStoppingTime_roundedTime hτ hτ_le n
  have hle (n : ℕ) (f : DLoc) :
      (roundedTime T n (τ f) : WithTop ℝ≥0) ≤ T :=
    WithTop.coe_le_coe.mpr (roundedTime_le T n (τ f))
  have hleft (n : ℕ) : A n =ᵐ[P] P[M T | (hτn n).measurableSpace] :=
    hM.stoppedValue_ae_eq_condExp_of_le_const_of_countable_range (hτn n) (hle n)
      (countable_range_roundedTime T n τ)
  have hUI : UniformIntegrable A 1 P :=
    ((hM.integrable T).uniformIntegrable_condExp
      (fun n => (hτn n).measurableSpace_le)).ae_eq (fun n => (hleft n).symm)
  have hlim : ∀ᵐ f ∂P, Tendsto (fun n => A n f) atTop (𝓝 (stoppedValue M τ f)) := by
    filter_upwards [hright] with f hf
    have hfin : τ f ≠ ⊤ := ne_top_of_le_ne_top WithTop.coe_ne_top (hτ_le f)
    obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp hfin
    have hrt : r ≤ T := by exact_mod_cast hr ▸ hτ_le f
    have htend : Tendsto (fun n => roundedTime T n (τ f)) atTop (𝓝[Ici r] r) := by
      apply tendsto_nhdsWithin_iff.mpr
      refine ⟨?_, Eventually.of_forall fun n => le_roundedTime hr.symm hrt n⟩
      simpa only [← hr, min_eq_right hrt, WithTop.untopD_coe] using
        (tendsto_roundedTime (t := T) hr.symm)
    have hseq : (fun n => A n f) = fun n => M (roundedTime T n (τ f)) f := by
      funext n
      exact congrArg (fun r => M r f) (untopA_coe_nnreal _)
    have hval : stoppedValue M τ f = M r f := by
      change M ((τ f).untopA) f = M r f
      rw [← hr, untopA_coe_nnreal]
    rw [hseq, hval]
    exact (hf r).tendsto.comp htend
  have hmeas (n : ℕ) : AEStronglyMeasurable (A n) P :=
    ((stronglyMeasurable_stoppedValue_of_le hprog (hτn n) (hle n)).mono
      (DLoc.filtration.le T)).aestronglyMeasurable
  have htim := tendstoInMeasure_of_tendsto_ae hmeas hlim
  have hint : Integrable (stoppedValue M τ) P := hUI.integrable_of_tendstoInMeasure htim
  have hL1 := tendsto_Lp_finite_of_tendstoInMeasure le_rfl ENNReal.one_ne_top hmeas
    (memLp_one_iff_integrable.mpr hint) hUI.1 htim
  have htower (n : ℕ) : P[A n | hτ.measurableSpace] =ᵐ[P]
      P[M T | hτ.measurableSpace] := by
    have hmle : hτ.measurableSpace ≤ (hτn n).measurableSpace :=
      hτ.measurableSpace_mono (hτn n) (fun f => by
        have hfin : τ f ≠ ⊤ := ne_top_of_le_ne_top WithTop.coe_ne_top (hτ_le f)
        obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp hfin
        rw [← hr]
        exact WithTop.coe_le_coe.mpr (le_roundedTime hr.symm
          (by exact_mod_cast hr ▸ hτ_le f) n))
    exact (condExp_congr_ae (hleft n)).trans
      (condExp_condExp_of_le hmle (hτn n).measurableSpace_le)
  have hlabs : Tendsto (fun n => ∫ f, |A n f - stoppedValue M τ f| ∂P) atTop (𝓝 0) := by
    have ht := ENNReal.tendsto_toReal (by simp : (0 : ℝ≥0∞) ≠ ⊤) |>.comp hL1
    have heq (n : ℕ) : (eLpNorm (A n - stoppedValue M τ) 1 P).toReal =
        ∫ f, |A n f - stoppedValue M τ f| ∂P := by
      rw [eLpNorm_one_eq_lintegral_enorm ((hmeas n).sub hint.aestronglyMeasurable)]
      simpa only [Pi.sub_apply, Real.norm_eq_abs] using
        (integral_norm_eq_lintegral_enorm ((hmeas n).sub hint.aestronglyMeasurable)).symm
    simpa only [Function.comp_def, heq, ENNReal.toReal_zero] using ht
  have hc := condExp_eq_of_integral_abs_tendsto hτ.measurableSpace hint
    (integrable_condExp : Integrable (P[M T | hτ.measurableSpace]) P)
    (fun n => integrable_condExp.congr (hleft n).symm)
    (fun _ => integrable_condExp) htower hlabs (by simp)
  rw [condExp_of_stronglyMeasurable hτ.measurableSpace_le
    (measurable_stoppedValue hprog hτ).stronglyMeasurable hint] at hc
  exact hc

end BGW.StableTrees
