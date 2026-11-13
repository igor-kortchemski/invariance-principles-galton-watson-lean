/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.SupremumCorrectionLimit

/-!
# Simultaneous domination for the positive-rate errors

## References

* J. Bertoin, *Lévy Processes*, Cambridge University Press, 1996, Chapter IV.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees

/-- The discounted occupation head has the same deterministic bound as occupation. -/
private theorem abs_supOccupationDiscountedHead_le {q ε : ℝ} (hq : 0 < q) (hε : 0 < ε)
    (t : ℝ≥0) (f : DLoc) : |supOccupationDiscountedHead q ε t f| ≤ (t : ℝ) / ε := by
  have hb := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Ioc (0 : ℝ) t)
    (f := fun s => Real.exp (-q * s) * supOccKernel ε (supReflectedFrom 0 f s.toNNReal))
    (C := ε⁻¹) (by simp) (fun s hs => ?_)
  · simpa only [supOccupationDiscountedHead, Real.norm_eq_abs, Measure.real,
      Real.volume_Ioc, sub_zero, ENNReal.toReal_ofReal t.coe_nonneg, div_eq_mul_inv,
      mul_comm] using hb
  · rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _),
      abs_of_nonneg (supOccKernel_mem_Icc hε _).1]
    exact (mul_le_mul_of_nonneg_left (supOccKernel_mem_Icc hε _).2 (Real.exp_pos _).le).trans
      (mul_le_of_le_one_left (inv_pos.mpr hε).le
        (Real.exp_le_one_iff.mpr
          (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hq.le) hs.1.le)))

private theorem integral_exp_head (q : ℝ) (hq : 0 < q) (t : ℝ≥0) :
    q * (∫ s in Ioc (0 : ℝ) t, Real.exp (-q * s)) = 1 - Real.exp (-q * t) := by
  have hi := integrableOn_exp_mul_Ioi (neg_neg_of_pos hq) (0 : ℝ)
  have hs := setIntegral_union (Ioc_disjoint_Ioi_same (a := (0 : ℝ)) (b := (t : ℝ)))
    measurableSet_Ioi (hi.mono_set Ioc_subset_Ioi_self)
    (hi.mono_set (Ioi_subset_Ioi t.coe_nonneg))
  rw [Ioc_union_Ioi_eq_Ioi t.coe_nonneg, integral_exp_mul_Ioi (neg_neg_of_pos hq),
    integral_exp_mul_Ioi (neg_neg_of_pos hq)] at hs
  simp only [mul_zero, Real.exp_zero] at hs
  field_simp at hs ⊢
  nlinarith only [hs]

/-- On any continuous nondecreasing zero-started clock path, the discounted head is between
zero and the undiscounted clock, simultaneously for all positive rates. -/
private theorem supAuxDiscountedHead_mem_Icc {θ q : ℝ} (hq : 0 < q) (t : ℝ≥0) (f : DLoc)
    (hf : supAuxLocalTime θ f 0 = 0 ∧ Monotone (supAuxLocalTime θ f) ∧
      Continuous (supAuxLocalTime θ f)) :
    supAuxDiscountedHead θ q t f ∈ Icc (0 : ℝ) (supAuxLocalTime θ f t) := by
  have hm0 (s : ℝ≥0) : 0 ≤ supAuxLocalTime θ f s := hf.1 ▸ hf.2.1 (zero_le : 0 ≤ s)
  have hc : Continuous (fun s : ℝ => Real.exp (-q * s) * supAuxLocalTime θ f s.toNNReal) :=
    (by fun_prop : Continuous (fun s : ℝ => Real.exp (-q * s))).mul
      (hf.2.2.comp continuous_real_toNNReal)
  have hi : IntegrableOn (fun s : ℝ => Real.exp (-q * s) * supAuxLocalTime θ f s.toNNReal)
      (Ioc (0 : ℝ) t) := hc.continuousOn.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hce : Continuous (fun s : ℝ => Real.exp (-q * s) * supAuxLocalTime θ f t) := by fun_prop
  have hle : (∫ s in Ioc (0 : ℝ) t, Real.exp (-q * s) * supAuxLocalTime θ f s.toNNReal) ≤
      (∫ s in Ioc (0 : ℝ) t, Real.exp (-q * s) * supAuxLocalTime θ f t) := by
    apply setIntegral_mono_on hi
      (hce.continuousOn.integrableOn_Icc.mono_set Ioc_subset_Icc_self) measurableSet_Ioc
    intro s hs
    exact mul_le_mul_of_nonneg_left (hf.2.1 ((Real.toNNReal_le_iff_le_coe).mpr hs.2))
      (Real.exp_pos _).le
  rw [integral_mul_const] at hle
  have hid := integral_exp_head q hq t
  unfold supAuxDiscountedHead
  constructor
  · exact add_nonneg (mul_nonneg (Real.exp_pos _).le (hm0 t))
      (mul_nonneg hq.le (integral_nonneg (fun s => mul_nonneg (Real.exp_pos _).le (hm0 _))))
  · have hh := mul_le_mul_of_nonneg_left hle hq.le
    calc
      _ ≤ Real.exp (-q * t) * supAuxLocalTime θ f t +
          q * ((∫ s in Ioc (0 : ℝ) t, Real.exp (-q * s)) * supAuxLocalTime θ f t) :=
        add_le_add le_rfl hh
      _ = supAuxLocalTime θ f t := by rw [← mul_assoc, hid]; ring

/-- Domination holds on one event for all times and all sufficiently small positive rates. -/
theorem ae_abs_discountedErrorMartingale_le {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {ε : ℝ}
    (hε : 0 < ε) (K : ℝ) (T : ℝ≥0) :
    ∃ q₀ C : ℝ, 0 < q₀ ∧
      ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc),
        ∀ s : ℝ≥0, s ≤ T → supReflectedFrom 0 f s ≤ K →
          ∀ q : ℝ, 0 < q → q < q₀ →
            |discountedErrorMartingale θ q ε s f| ≤
              (T : ℝ) / ε + supAuxLocalTime θ f T + C := by
  have hu := (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact isCompact_Icc).mp
    ((tendstoLocallyUniformlyOn_supOccupationResolvent_sub hθ hε).mono
      (show Icc (0 : ℝ) K ⊆ Ici 0 from fun _ hx => hx.1))
  have hev := (Metric.tendstoUniformlyOn_iff.mp hu) 1 zero_lt_one
  obtain ⟨q₀, hq₀, hbound⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hev
  refine ⟨q₀, 1 + supCorrectionBound θ ε, hq₀, ?_⟩
  filter_upwards [ae_supAuxLocalTime_continuous hθ] with f hf
  intro s hs hK q hq hqq
  have hr := hbound ⟨hq, hqq⟩ (supReflectedFrom 0 f s)
    ⟨supReflectedFrom_nonneg 0 f s, hK⟩
  rw [Real.dist_eq, abs_sub_comm] at hr
  have hv := abs_supCorrection_le hθ hε (supReflectedFrom_nonneg 0 f s)
  have hterm : |supOccupationResolvent θ q ε (supReflectedFrom 0 f s) -
      supPotential θ q (supReflectedFrom 0 f s)| ≤ 1 + supCorrectionBound θ ε := by
    have hh := abs_add_le ((supOccupationResolvent θ q ε (supReflectedFrom 0 f s) -
      supPotential θ q (supReflectedFrom 0 f s)) - supCorrection θ ε (supReflectedFrom 0 f s))
      (supCorrection θ ε (supReflectedFrom 0 f s))
    rw [sub_add_cancel] at hh
    change |supCorrection θ ε (supReflectedFrom 0 f s)| ≤ supCorrectionBound θ ε at hv
    linarith only [hh, hr, hv]
  have hC0 : 0 ≤ 1 + supCorrectionBound θ ε := (abs_nonneg _).trans hterm
  have hexp : Real.exp (-q * (s : ℝ)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hq.le) s.coe_nonneg)
  have hO := abs_supOccupationDiscountedHead_le hq hε s f
  have hM := supAuxDiscountedHead_mem_Icc hq s f hf
  have hT := hf.2.1 hs
  unfold discountedErrorMartingale
  calc
    _ ≤ |supOccupationDiscountedHead q ε s f - supAuxDiscountedHead θ q s f| +
        |Real.exp (-q * s) * (supOccupationResolvent θ q ε (supReflectedFrom 0 f s) -
          supPotential θ q (supReflectedFrom 0 f s))| := abs_add_le _ _
    _ ≤ (|supOccupationDiscountedHead q ε s f| + |supAuxDiscountedHead θ q s f|) +
        (1 + supCorrectionBound θ ε) := by
      apply add_le_add (abs_sub _ _)
      rw [abs_mul, abs_of_pos (Real.exp_pos _)]
      exact (mul_le_mul_of_nonneg_left hterm (Real.exp_pos _).le).trans
        (mul_le_of_le_one_left hC0 hexp)
    _ ≤ (T : ℝ) / ε + supAuxLocalTime θ f T + (1 + supCorrectionBound θ ε) := by
      rw [abs_of_nonneg hM.1]
      have hst : (s : ℝ) / ε ≤ T / ε := div_le_div_of_nonneg_right
        (NNReal.coe_le_coe.mpr hs) hε.le
      linarith only [hO, hM.2, hT, hst]

end BGW.StableTrees
