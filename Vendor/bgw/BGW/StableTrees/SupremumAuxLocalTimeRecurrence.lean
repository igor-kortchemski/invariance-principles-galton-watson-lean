/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.SupremumAuxLocalTimePositive
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Recurrence of the auxiliary clock

Scaling and unit-time positivity force discounted unit tests to vanish at large times.
Fatou and path monotonicity yield divergence on one event, simultaneously in all time bounds.

## References

* J. Bertoin, *Lévy Processes*, Cambridge University Press, 1996, Chapter IV.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees

/-- Negative exponentials of the nonnegative clock are integrable. -/
theorem integrable_exp_neg_supAuxLocalTime {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (t : ℝ≥0) :
    Integrable (fun f => Real.exp (-supAuxLocalTime θ f t))
      (stableLocalLaw θ : Measure DLoc) := by
  apply Integrable.of_bound
    (Real.measurable_exp.comp (measurable_supAuxLocalTime_eval θ t).neg).aestronglyMeasurable 1
  filter_upwards [ae_supAuxLocalTime_nonneg hθ] with f hf
  change ‖Real.exp (-supAuxLocalTime θ f t)‖ ≤ 1
  rw [Real.norm_of_nonneg (Real.exp_pos _).le]
  exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (hf t))

/-- The negative-exponential tests of the clock vanish in mean at large integer times. -/
theorem tendsto_integral_exp_neg_supAuxLocalTime {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    Tendsto (fun n : ℕ => ∫ f, Real.exp (-supAuxLocalTime θ f (n + 1))
      ∂(stableLocalLaw θ : Measure DLoc)) atTop (𝓝 0) := by
  let d : ℕ → ℝ := fun n => ((n : ℝ) + 1) / ((n : ℝ) + 1) ^ (1 / θ)
  have hdpos (n : ℕ) : 0 < d n :=
    div_pos (by positivity) (Real.rpow_pos_of_pos (by positivity) _)
  have hβ : 0 < 1 - 1 / θ := by
    rw [sub_pos, div_lt_one (by linarith : 0 < θ)]
    exact hθ.1
  have hnat : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_mono (fun n => le_add_of_nonneg_right zero_le_one)
      tendsto_natCast_atTop_atTop
  have hd : Tendsto d atTop atTop := by
    have hh := (tendsto_rpow_atTop hβ).comp hnat
    apply hh.congr'
    filter_upwards with n
    change ((n : ℝ) + 1) ^ (1 - 1 / θ) = ((n : ℝ) + 1) / ((n : ℝ) + 1) ^ (1 / θ)
    rw [Real.rpow_sub (by positivity), Real.rpow_one]
  have he (n : ℕ) :
      (∫ f, Real.exp (-supAuxLocalTime θ f (n + 1))
        ∂(stableLocalLaw θ : Measure DLoc)) =
      ∫ f, Real.exp (-(d n * supAuxLocalTime θ f 1))
        ∂(stableLocalLaw θ : Measure DLoc) := by
    let t : ℝ≥0 := n + 1
    let c : Ioi (0 : ℝ) := ⟨t, by
      change (0 : ℝ) < (t : ℝ)
      dsimp only [t]
      positivity⟩
    have hT : t / (c : ℝ).toNNReal = 1 := by
      change t / (t : ℝ).toNNReal = 1
      rw [Real.toNNReal_coe, div_self (by positivity : t ≠ 0)]
    have hsm : Measurable (fun f : DLoc => ((c : ℝ) / (c : ℝ) ^ (1 / θ)) *
        supAuxLocalTime θ f (t / (c : ℝ).toNNReal)) :=
      (measurable_supAuxLocalTime_eval θ _).const_mul _
    have hg : StronglyMeasurable (fun x : ℝ => Real.exp (-x)) :=
      (Real.measurable_exp.comp measurable_neg).stronglyMeasurable
    have hh := congrArg (fun μ : Measure ℝ => ∫ x, Real.exp (-x) ∂μ)
      (map_supAuxLocalTime_scaling hθ c t)
    rw [integral_map_of_stronglyMeasurable (measurable_supAuxLocalTime_eval θ t) hg,
      integral_map_of_stronglyMeasurable hsm hg, hT] at hh
    simpa only [c, t, NNReal.coe_add, NNReal.coe_natCast, NNReal.coe_one, d] using hh
  have hpoint : ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc),
      Tendsto (fun n => Real.exp (-(d n * supAuxLocalTime θ f 1))) atTop (𝓝 0) := by
    filter_upwards [ae_supAuxLocalTime_pos hθ] with f hf
    exact Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (Tendsto.atTop_mul_const (hf 1 zero_lt_one) hd)
  have hb (n : ℕ) : ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc),
      ‖Real.exp (-(d n * supAuxLocalTime θ f 1))‖ ≤ 1 := by
    filter_upwards [ae_supAuxLocalTime_nonneg hθ] with f hf
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg (hdpos n).le (hf 1)))
  have hl := tendsto_integral_of_dominated_convergence
    (μ := (stableLocalLaw θ : Measure DLoc)) (fun _ => (1 : ℝ))
    (fun n => (Real.measurable_exp.comp
      ((measurable_supAuxLocalTime_eval θ 1).const_mul (d n)).neg).aestronglyMeasurable)
    (integrable_const _) hb hpoint
  have hl' : Tendsto (fun n => ∫ f, Real.exp (-(d n * supAuxLocalTime θ f 1))
      ∂(stableLocalLaw θ : Measure DLoc)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Pi.neg_apply, integral_zero] using hl
  exact hl'.congr' (Eventually.of_forall fun n => (he n).symm)

/-- **Recurrence**: `L^aux_0 = 0`, monotone, continuous, `L^aux_t → ∞` (almost surely). -/
theorem ae_supAuxLocalTime_spec {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc),
      supAuxLocalTime θ f 0 = 0 ∧ Monotone (supAuxLocalTime θ f) ∧
        Continuous (supAuxLocalTime θ f) ∧ Tendsto (supAuxLocalTime θ f) atTop atTop := by
  let L : DLoc → ℝ≥0∞ := fun f => liminf
    (fun n : ℕ => ENNReal.ofReal (Real.exp (-supAuxLocalTime θ f (n + 1)))) atTop
  have hmeas (n : ℕ) : Measurable (fun f : DLoc =>
      ENNReal.ofReal (Real.exp (-supAuxLocalTime θ f (n + 1)))) :=
    (Real.measurable_exp.comp (measurable_supAuxLocalTime_eval θ (n + 1)).neg).ennreal_ofReal
  have hLi : Measurable L := Measurable.liminf hmeas
  have he (n : ℕ) : (∫⁻ f, ENNReal.ofReal (Real.exp (-supAuxLocalTime θ f (n + 1)))
      ∂(stableLocalLaw θ : Measure DLoc)) = ENNReal.ofReal
        (∫ f, Real.exp (-supAuxLocalTime θ f (n + 1))
          ∂(stableLocalLaw θ : Measure DLoc)) :=
    (ofReal_integral_eq_lintegral_ofReal (integrable_exp_neg_supAuxLocalTime hθ (n + 1))
      (ae_of_all _ fun f => (Real.exp_pos _).le)).symm
  have hl := ENNReal.tendsto_ofReal (tendsto_integral_exp_neg_supAuxLocalTime hθ)
  have hlim : Tendsto (fun n : ℕ => ∫⁻ f,
      ENNReal.ofReal (Real.exp (-supAuxLocalTime θ f (n + 1)))
      ∂(stableLocalLaw θ : Measure DLoc)) atTop (𝓝 0) := by
    simpa only [he, ENNReal.ofReal_zero] using hl
  have hfatou := lintegral_liminf_le' (u := atTop) (μ := (stableLocalLaw θ : Measure DLoc))
    (fun n => (hmeas n).aemeasurable)
  rw [hlim.liminf_eq] at hfatou
  have hLzero : L =ᵐ[(stableLocalLaw θ : Measure DLoc)] 0 :=
    (lintegral_eq_zero_iff hLi).mp (le_antisymm hfatou bot_le)
  filter_upwards [hLzero, ae_supAuxLocalTime_continuous hθ] with f hf hm
  refine ⟨hm.1, hm.2.1, hm.2.2, ?_⟩
  apply tendsto_atTop.mpr
  intro a
  have hex : ∃ n : ℕ, a ≤ supAuxLocalTime θ f (n + 1) := by
    by_contra hn
    push Not at hn
    have hb : ENNReal.ofReal (Real.exp (-a)) ≤ L f := by
      exact le_liminf_of_le (h := Eventually.of_forall fun n =>
        ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (neg_le_neg (hn n).le)))
    rw [hf] at hb
    exact (not_le_of_gt (ENNReal.ofReal_pos.mpr (Real.exp_pos _))) hb
  obtain ⟨n, hn⟩ := hex
  filter_upwards [eventually_ge_atTop ((n : ℝ≥0) + 1)] with t ht
  exact hn.trans (hm.2.1 ht)

/-- Bundled interface `exists_auxSupLocalTime`: the raw process `supAuxLocalTime` is
jointly measurable, adapted, a.s. `0`-started monotone continuous unbounded, and is the full
filter compact-time `L²` limit of the occupations. -/
theorem exists_auxSupLocalTime {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∃ Mstar : DLoc → ℝ≥0 → ℝ,
      Measurable (fun p : ℝ≥0 × DLoc => Mstar p.2 p.1) ∧
      StronglyAdapted DLoc.filtration (fun t f => Mstar f t) ∧
      (∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), Mstar f 0 = 0 ∧ Monotone (Mstar f) ∧
        Continuous (Mstar f) ∧ Tendsto (Mstar f) atTop atTop) ∧
      (∀ T : ℝ≥0, Tendsto (fun ε : ℝ =>
        ∫ f, (⨆ t : Set.Iic T, |supOccupation ε f t - Mstar f t|) ^ 2
          ∂(stableLocalLaw θ : Measure DLoc)) (𝓝[>] (0 : ℝ)) (𝓝 0)) := by
  exact ⟨supAuxLocalTime θ, measurable_supAuxLocalTime_uncurry θ,
    stronglyAdapted_supAuxLocalTime θ, ae_supAuxLocalTime_spec hθ,
    fun T => (supOccupation_compact_L2_tendsto_supAuxLimit hθ T).2⟩

end BGW.StableTrees
