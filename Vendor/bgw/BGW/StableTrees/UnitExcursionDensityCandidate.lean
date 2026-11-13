/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.UnitExcursionDensityEvaluation
public import BGW.StableTrees.UnitExcursionDensityCutoff

/-!
# The normalized prefix-density candidate at good horizons

Increasing endpoint cutoffs give mass equal to the stable density at zero.
Bounded convergence then removes the cutoffs from every good-time cylinder test.

## References

* L. Chaumont, *Excursion normalisée, méandre et pont pour les processus de Lévy stables*,
  Bull. Sci. Math. 121 (1997), 377–403.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod
namespace BGW.StableTrees

/-- At a good horizon the prefix density has mass equal to the stable density at zero. -/
theorem lintegral_prefix_density_mass_of_good {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    (b : ℝ≥0) (hb : b ∈ Ioo (0 : ℝ≥0) 1) (hbgood : NoFixedJumpUnit θ b) :
    (∫⁻ e, ENNReal.ofReal (qKernel θ (1 - b) (e.path.1 b)) ∂excursionTail θ b) =
      ENNReal.ofReal (Scalar.stableDensity θ 0) := by
  let μ := excursionTail θ b
  let P := (unitExcursionLaw θ : Measure Excursion)
  let c := ENNReal.ofReal (Scalar.stableDensity θ 0)
  let Q : Excursion → ℝ≥0∞ := fun e => ENNReal.ofReal (qKernel θ (1 - b) (e.path.1 b))
  let χ : ℕ → Excursion → ℝ := fun n e => prefixCutoff n (e.path.1 b)
  have hχm (n : ℕ) : Measurable (χ n) :=
    (continuous_prefixCutoff n).measurable.comp (measurable_excursion_eval b)
  have hQ : Measurable Q :=
    (((measurable_qKernel θ).comp
      (measurable_const.prodMk (measurable_excursion_eval b))).ennreal_ofReal)
  have hq (e : Excursion) : 0 ≤ qKernel θ (1 - b) (e.path.1 b) :=
    qKernel_nonneg hθ (sub_pos.mpr hb.2) (e.2.2.1 b)
  have hχ0 (n : ℕ) (e : Excursion) : 0 ≤ χ n e := (prefixCutoff_mem_Icc n _).1
  have hχ1 (n : ℕ) (e : Excursion) : χ n e ≤ 1 := (prefixCutoff_mem_Icc n _).2
  have hχInt (n : ℕ) : Integrable (χ n) P :=
    Integrable.of_bound (hχm n).aestronglyMeasurable 1
      (Eventually.of_forall fun e => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hχ0 n e)]
        exact hχ1 n e)
  have heq (n : ℕ) : (∫⁻ e, ENNReal.ofReal (χ n e) * Q e ∂μ) =
      c * ∫⁻ e, ENNReal.ofReal (χ n e) ∂P := by
    have hr := integral_goodTimes_eq_density_at_one hθ b hb hbgood
      (n := 0) (fun i => Fin.elim0 i) (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)
      (fun _ => 1) continuous_const ⟨1, fun _ => by norm_num⟩
      (prefixCutoff n) (continuous_prefixCutoff n) (hasCompactSupport_prefixCutoff n)
    simp only [one_mul] at hr
    have hr' := congrArg (fun z : ℝ => Scalar.stableDensity θ 0 * z) hr
    rw [← mul_assoc, mul_inv_cancel₀ (Scalar.stableDensity_zero_pos hθ).ne', one_mul] at hr'
    have hint : Integrable (fun e => χ n e * qKernel θ (1 - b) (e.path.1 b)) μ := by
      simpa only [μ, χ, one_mul] using integrable_prefix_cutoff hθ b hb.1 (fun _ => 1)
        measurable_const ⟨1, fun _ => by norm_num⟩ (prefixCutoff n)
        (continuous_prefixCutoff n) (hasCompactSupport_prefixCutoff n)
        (s := 1 - (b : ℝ)) (sub_pos.mpr hb.2)
    calc
      _ = ∫⁻ e, ENNReal.ofReal (χ n e * qKernel θ (1 - b) (e.path.1 b)) ∂μ :=
        lintegral_congr fun e => (ENNReal.ofReal_mul (hχ0 n e)).symm
      _ = ENNReal.ofReal (∫ e, χ n e * qKernel θ (1 - b) (e.path.1 b) ∂μ) :=
        (ofReal_integral_eq_lintegral_ofReal hint
          (Eventually.of_forall fun e => mul_nonneg (hχ0 n e) (hq e))).symm
      _ = ENNReal.ofReal (Scalar.stableDensity θ 0 * ∫ e, χ n e ∂P) := by
        simpa only [μ, P, χ, excursionTail] using congrArg ENNReal.ofReal hr'.symm
      _ = _ := by
        rw [ENNReal.ofReal_mul (Scalar.stableDensity_zero_pos hθ).le,
          ofReal_integral_eq_lintegral_ofReal (hχInt n) (Eventually.of_forall (hχ0 n))]
  have hmono (e : Excursion) : Monotone (fun n => ENNReal.ofReal (χ n e)) :=
    ENNReal.ofReal_mono.comp (monotone_prefixCutoff _)
  have hlim (e : Excursion) : Tendsto (fun n => ENNReal.ofReal (χ n e)) atTop (𝓝 1) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_prefixCutoff_eq_one (e.path.1 b)] with n hn
    simp only [χ, hn, ENNReal.ofReal_one]
  have hlimP : Tendsto (fun n => ∫⁻ e, ENNReal.ofReal (χ n e) ∂P) atTop (𝓝 1) := by
    simpa only [lintegral_one, measure_univ] using
      (lintegral_tendsto_of_tendsto_of_monotone
        (μ := P) (fun n => (hχm n).ennreal_ofReal.aemeasurable)
        (Eventually.of_forall hmono) (Eventually.of_forall hlim))
  have hlimQ : Tendsto (fun n => ∫⁻ e, ENNReal.ofReal (χ n e) * Q e ∂μ) atTop
      (𝓝 (∫⁻ e, Q e ∂μ)) := by
    apply lintegral_tendsto_of_tendsto_of_monotone
      (fun n => ((hχm n).ennreal_ofReal.mul hQ).aemeasurable)
      (Eventually.of_forall fun e => (hmono e).mul_const (show 0 ≤ Q e from zero_le))
    apply Eventually.of_forall
    intro e
    simpa only [Pi.mul_apply, one_mul] using ENNReal.Tendsto.mul_const (hlim e) (by simp)
  apply tendsto_nhds_unique hlimQ
  simp_rw [heq]
  simpa only [mul_one] using ENNReal.Tendsto.const_mul hlimP (by simp [c])

/-- The unnormalized Kendall-weighted excursion survival measure. -/
noncomputable def prefixDensityMeasure (θ : ℝ) (a : ℝ≥0) : Measure Excursion :=
  (excursionTail θ a).withDensity
    (fun e => ENNReal.ofReal (qKernel θ (1 - a) (e.path.1 a)))

/-- Measurability of the prefix density. -/
theorem measurable_prefixDensity (θ : ℝ) (a : ℝ≥0) :
    Measurable (fun e : Excursion => ENNReal.ofReal (qKernel θ (1 - a) (e.path.1 a))) :=
  ((measurable_qKernel θ).comp
    (measurable_const.prodMk (measurable_excursion_eval a))).ennreal_ofReal

/-- Good-horizon normalization of the unnormalized density measure. -/
theorem prefixDensityMeasure_univ_of_good {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    (a : ℝ≥0) (ha : a ∈ Ioo (0 : ℝ≥0) 1) (hgood : NoFixedJumpUnit θ a) :
    prefixDensityMeasure θ a univ = ENNReal.ofReal (Scalar.stableDensity θ 0) := by
  rw [prefixDensityMeasure, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ]
  exact lintegral_prefix_density_mass_of_good hθ a ha hgood

/-- Finiteness of the density measure at a good horizon. -/
theorem isFiniteMeasure_prefixDensityMeasure_of_good {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    (a : ℝ≥0) (ha : a ∈ Ioo (0 : ℝ≥0) 1) (hgood : NoFixedJumpUnit θ a) :
    IsFiniteMeasure (prefixDensityMeasure θ a) :=
  ⟨by rw [prefixDensityMeasure_univ_of_good hθ a ha hgood]; exact ENNReal.ofReal_lt_top⟩

/-- Removing endpoint cutoffs under a finite excursion measure. -/
theorem tendsto_integral_prefixCutoff (μ : Measure Excursion) [IsFiniteMeasure μ]
    (a : ℝ≥0) (F : Excursion → ℝ) (hF : Measurable F)
    (hFb : ∃ C : ℝ, ∀ e, |F e| ≤ C) :
    Tendsto (fun n => ∫ e, F e * prefixCutoff n (e.path.1 a) ∂μ) atTop (𝓝 (∫ e, F e ∂μ)) := by
  obtain ⟨C, hC⟩ := hFb
  apply tendsto_integral_of_dominated_convergence (fun _ => |C|)
  · intro n
    exact (hF.mul ((continuous_prefixCutoff n).measurable.comp
      (measurable_excursion_eval a))).aestronglyMeasurable
  · exact integrable_const _
  · intro n
    apply Eventually.of_forall
    intro e
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (prefixCutoff_mem_Icc n _).1]
    exact (mul_le_mul_of_nonneg_left (prefixCutoff_mem_Icc n _).2 (abs_nonneg _)).trans
      (by simpa only [mul_one] using (hC e).trans (le_abs_self C))
  · apply Eventually.of_forall
    intro e
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_prefixCutoff_eq_one (e.path.1 a)] with n hn
    simp only [hn, mul_one]

/-- Good-time cylinder integrals without the endpoint cutoff. -/
theorem integral_goodTimes_eq_prefixDensityMeasure {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    (b : ℝ≥0) (hb : b ∈ Ioo (0 : ℝ≥0) 1) (hbgood : NoFixedJumpUnit θ b) {n : ℕ}
    (t : Fin n → ℝ≥0) (ht : ∀ i, t i ≤ b) (hgood : ∀ i, NoFixedJumpUnit θ (t i))
    (φ : (Fin n → ℝ) → ℝ) (hφ : Continuous φ) (hφb : ∃ C : ℝ, ∀ x, |φ x| ≤ C) :
    (∫ e, φ (fun i => e.path.1 (t i)) ∂(unitExcursionLaw θ : Measure Excursion)) =
      (Scalar.stableDensity θ 0)⁻¹ *
        ∫ e, φ (fun i => e.path.1 (t i)) ∂prefixDensityMeasure θ b := by
  let _ := isFiniteMeasure_prefixDensityMeasure_of_good hθ b hb hbgood
  have hm : Measurable (fun e : Excursion => φ (fun i => e.path.1 (t i))) :=
    hφ.measurable.comp (Measurable.of_eval fun i => measurable_excursion_eval (t i))
  obtain ⟨C, hC⟩ := hφb
  have hbound : ∃ C : ℝ, ∀ e : Excursion, |φ (fun i => e.path.1 (t i))| ≤ C :=
    ⟨C, fun e => hC _⟩
  have hcut (k : ℕ) :
      (∫ e, φ (fun i => e.path.1 (t i)) * prefixCutoff k (e.path.1 b)
        ∂(unitExcursionLaw θ : Measure Excursion)) =
      (Scalar.stableDensity θ 0)⁻¹ *
        ∫ e, φ (fun i => e.path.1 (t i)) * prefixCutoff k (e.path.1 b)
          ∂prefixDensityMeasure θ b := by
    rw [integral_goodTimes_eq_density_at_one hθ b hb hbgood t ht hgood φ hφ ⟨C, hC⟩
      (prefixCutoff k) (continuous_prefixCutoff k) (hasCompactSupport_prefixCutoff k)]
    congr 1
    rw [prefixDensityMeasure, integral_withDensity_eq_integral_toReal_smul
      (measurable_prefixDensity θ b) (Eventually.of_forall fun e => ENNReal.ofReal_lt_top)]
    apply integral_congr_ae
    apply Eventually.of_forall
    intro e
    change φ (fun i => e.path.1 (t i)) * prefixCutoff k (e.path.1 b) *
        qKernel θ (1 - b) (e.path.1 b) =
      (ENNReal.ofReal (qKernel θ (1 - b) (e.path.1 b))).toReal •
        (φ (fun i => e.path.1 (t i)) * prefixCutoff k (e.path.1 b))
    have hqe : 0 ≤ qKernel θ (1 - b) (e.path.1 b) :=
      qKernel_nonneg hθ (sub_pos.mpr hb.2) (e.2.2.1 b)
    rw [ENNReal.toReal_ofReal hqe, smul_eq_mul]
    ring
  have hleft := tendsto_integral_prefixCutoff (unitExcursionLaw θ : Measure Excursion)
    b _ hm hbound
  have hright := (tendsto_integral_prefixCutoff (prefixDensityMeasure θ b) b _ hm hbound).const_mul
    ((Scalar.stableDensity θ 0)⁻¹)
  have hseq : (fun k => ∫ e, φ (fun i => e.path.1 (t i)) * prefixCutoff k (e.path.1 b)
      ∂(unitExcursionLaw θ : Measure Excursion)) =ᶠ[atTop]
      (fun k => (Scalar.stableDensity θ 0)⁻¹ *
        ∫ e, φ (fun i => e.path.1 (t i)) * prefixCutoff k (e.path.1 b)
          ∂prefixDensityMeasure θ b) := Eventually.of_forall hcut
  exact tendsto_nhds_unique hleft (hright.congr' hseq.symm)

end BGW.StableTrees
