/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.SupremumCauchyDoob

/-!
# Removing the discount in occupation estimates

Fubini gives integration by parts for bounded measurable occupation kernels.

## References

* [J. Bertoin, *Lévy Processes*, Cambridge University Press, 1996, Chapter IV]
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees

/-- Fubini integration by parts for a discounted primitive. -/
theorem integral_exp_mul_discountedPrimitive {k : ℝ → ℝ} {t : ℝ} (hk : IntegrableOn k (Ioc 0 t)) :
    (∫ s in Ioc 0 t, Real.exp s * (∫ u in Ioc 0 s, Real.exp (-u) * k u)) =
      Real.exp t * (∫ u in Ioc 0 t, Real.exp (-u) * k u) - ∫ u in Ioc 0 t, k u := by
  let G := fun u => Real.exp (-u) * k u
  have hG : IntegrableOn G (Ioc 0 t) := by
    apply hk.bdd_mul (c := 1) (Real.continuous_exp.comp continuous_neg).aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    change ‖Real.exp (-u)‖ ≤ 1
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.mpr (by linarith [hu.1])
  have hExp : IntegrableOn Real.exp (Ioc 0 t) :=
    Real.continuous_exp.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  let F : ℝ × ℝ → ℝ := {p : ℝ × ℝ | p.2 ≤ p.1}.indicator
    (fun p => Real.exp p.1 * G p.2)
  have hF : Integrable F ((volume.restrict (Ioc 0 t)).prod (volume.restrict (Ioc 0 t))) :=
    (hExp.mul_prod hG).indicator (measurableSet_le measurable_snd measurable_fst)
  have hleft (s : ℝ) (hs : s ∈ Ioc 0 t) :
      (∫ u in Ioc 0 t, F (s, u)) = Real.exp s * ∫ u in Ioc 0 s, G u := by
    have hf : (fun u => F (s, u)) = (Iic s).indicator (fun u => Real.exp s * G u) := by
      ext u
      simp [F, indicator_apply]
    rw [hf, setIntegral_indicator measurableSet_Iic]
    have he : Ioc 0 t ∩ Iic s = Ioc 0 s := by
      ext u
      simp only [mem_inter_iff, mem_Ioc, mem_Iic]
      constructor
      · rintro ⟨⟨hu, _⟩, hus⟩; exact ⟨hu, hus⟩
      · rintro ⟨hu, hus⟩; exact ⟨⟨hu, hus.trans hs.2⟩, hus⟩
    rw [he, integral_const_mul]
  have hright (u : ℝ) (hu : u ∈ Ioc 0 t) :
      (∫ s in Ioc 0 t, F (s, u)) = (Real.exp t - Real.exp u) * G u := by
    have hf : (fun s => F (s, u)) = (Ici u).indicator (fun s => Real.exp s * G u) := by
      ext s
      simp [F, indicator_apply]
    rw [hf, setIntegral_indicator measurableSet_Ici]
    have he : Ioc 0 t ∩ Ici u = Icc u t := by
      ext s
      simp only [mem_inter_iff, mem_Ioc, mem_Ici, mem_Icc]
      constructor
      · rintro ⟨⟨_, hst⟩, hus⟩; exact ⟨hus, hst⟩
      · rintro ⟨hus, hst⟩; exact ⟨⟨hu.1.trans_le hus, hst⟩, hus⟩
    rw [he, integral_mul_const, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le hu.2, integral_exp]
  have hfub := integral_integral_swap (f := fun s u => F (s, u)) hF
  have hident : (∫ u in Ioc 0 t, (Real.exp t - Real.exp u) * G u) =
      Real.exp t * (∫ u in Ioc 0 t, G u) - ∫ u in Ioc 0 t, k u := by
    have hp : (fun u => (Real.exp t - Real.exp u) * G u) =
        (fun u => Real.exp t * G u - k u) := by
      ext u
      dsimp [G]
      rw [sub_mul, ← mul_assoc (Real.exp u), ← Real.exp_add, add_neg_cancel,
        Real.exp_zero, one_mul]
    rw [hp, integral_sub (hG.const_mul _) hk, integral_const_mul]
  calc
    _ = ∫ s in Ioc 0 t, ∫ u in Ioc 0 t, F (s, u) := by
      apply setIntegral_congr_fun measurableSet_Ioc
      intro s hs
      exact (hleft s hs).symm
    _ = ∫ u in Ioc 0 t, ∫ s in Ioc 0 t, F (s, u) := hfub
    _ = ∫ u in Ioc 0 t, (Real.exp t - Real.exp u) * G u := by
      apply setIntegral_congr_fun measurableSet_Ioc
      exact hright
    _ = _ := hident

/-- A bound on a discounted primitive controls its undiscounted integral. -/
theorem abs_integral_le_of_discountedPrimitive_bound {k : ℝ → ℝ} {t H : ℝ}
    (ht : 0 ≤ t) (hk : IntegrableOn k (Icc 0 t))
    (hK : ∀ s ∈ Icc 0 t, |∫ u in Ioc 0 s, Real.exp (-u) * k u| ≤ H) :
    |∫ u in Ioc 0 t, k u| ≤ 2 * Real.exp t * H := by
  let K := fun s => ∫ u in Ioc 0 s, Real.exp (-u) * k u
  have hH : 0 ≤ H := (abs_nonneg _).trans (hK 0 ⟨le_rfl, ht⟩)
  have hG : IntegrableOn (fun u => Real.exp (-u) * k u) (Icc 0 t) := by
    apply hk.bdd_mul (c := 1)
      (Real.continuous_exp.comp continuous_neg).aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
    change ‖Real.exp (-u)‖ ≤ 1
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.mpr (by linarith [hu.1])
  have hcont : ContinuousOn K (Icc 0 t) := intervalIntegral.continuousOn_primitive hG
  have hi : IntegrableOn (fun s => Real.exp s * K s) (Ioc 0 t) :=
    (Real.continuous_exp.continuousOn.mul hcont).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hI : |∫ s in Ioc 0 t, Real.exp s * K s| ≤ Real.exp t * H := by
    calc
      _ ≤ ∫ s in Ioc 0 t, ‖Real.exp s * K s‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ s in Ioc 0 t, Real.exp s * H := by
        apply integral_mono_ae hi.norm
        · exact (Real.continuous_exp.integrableOn_Icc.mono_set
            Ioc_subset_Icc_self).mul_const H
        · filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
          rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
          exact mul_le_mul_of_nonneg_left (hK u ⟨hu.1.le, hu.2⟩) (Real.exp_pos _).le
      _ = (Real.exp t - 1) * H := by
        rw [integral_mul_const, ← intervalIntegral.integral_of_le ht, integral_exp]
        simp only [Real.exp_zero]
      _ ≤ Real.exp t * H := by nlinarith
  have hid := integral_exp_mul_discountedPrimitive (hk.mono_set Ioc_subset_Icc_self)
  have heq : (∫ u in Ioc 0 t, k u) = Real.exp t * K t -
      ∫ s in Ioc 0 t, Real.exp s * K s := by linarith only [hid]
  rw [heq]
  calc
    _ ≤ |Real.exp t * K t| + |∫ s in Ioc 0 t, Real.exp s * K s| := abs_sub _ _
    _ ≤ Real.exp t * H + Real.exp t * H := by
      apply add_le_add _ hI
      rw [abs_mul, abs_of_pos (Real.exp_pos _)]
      exact mul_le_mul_of_nonneg_left (hK t ⟨ht, le_rfl⟩) (Real.exp_pos _).le
    _ = _ := by ring

end BGW.StableTrees
