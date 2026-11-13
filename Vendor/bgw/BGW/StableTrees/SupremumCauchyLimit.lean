/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.SupremumCauchyConvergence

/-!
# Compact square-mean convergence to the auxiliary clock

Fatou transfers the compact Cauchy bounds to the raw auxiliary limit, including
integrability at every positive cutoff.

## References

* [J. Bertoin, *Lévy Processes*, Cambridge University Press, 1996, Chapter IV]
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees

private noncomputable def limitError (θ ε : ℝ) (T : ℝ≥0) (f : DLoc) : ℝ :=
  ⨆ t : Set.Iic T, |supOccupation ε f t - supAuxLimit θ f t|

private theorem compact_nnreal_Iic (T : ℝ≥0) : IsCompact (Iic T) := by
  simpa only [Icc, Iic, zero_le, true_and] using
    (isCompact_Icc : IsCompact (Icc (0 : ℝ≥0) T))

/-- Fatou's lemma with an eventual uniform bound for nonnegative real integrals. -/
theorem integrable_ae_limit_of_integral_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {G : ℕ → Ω → ℝ} {F : Ω → ℝ} {C : ℝ}
    (hG : ∀ k, Integrable (G k) μ) (hG0 : ∀ k, ∀ᵐ f ∂μ, 0 ≤ G k f)
    (hF0 : ∀ᵐ f ∂μ, 0 ≤ F f) (hC : 0 ≤ C)
    (hlim : ∀ᵐ f ∂μ, Tendsto (fun k => G k f) atTop (𝓝 (F f)))
    (hb : ∀ᶠ k : ℕ in atTop, (∫ f, G k f ∂μ) ≤ C) :
    Integrable F μ ∧ (∫ f, F f ∂μ) ≤ C := by
  have hFm := aestronglyMeasurable_of_tendsto_ae atTop (fun k => (hG k).aestronglyMeasurable) hlim
  have hfatou : (∫⁻ f, ENNReal.ofReal (F f) ∂μ) ≤
      liminf (fun k => ∫⁻ f, ENNReal.ofReal (G k f) ∂μ) atTop := by
    calc
      _ = ∫⁻ f, liminf (fun k => ENNReal.ofReal (G k f)) atTop ∂μ := by
        apply lintegral_congr_ae
        filter_upwards [hlim] with f hf
        exact (ENNReal.tendsto_ofReal hf).liminf_eq.symm
      _ ≤ _ := lintegral_liminf_le' fun k => (hG k).aestronglyMeasurable.aemeasurable.ennreal_ofReal
  have hevent : ∀ᶠ k : ℕ in atTop,
      (∫⁻ f, ENNReal.ofReal (G k f) ∂μ) ≤ ENNReal.ofReal C := by
    filter_upwards [hb] with k hk
    rw [← ofReal_integral_eq_lintegral_ofReal (hG k) (hG0 k)]
    exact ENNReal.ofReal_le_ofReal hk
  have hle := hfatou.trans (liminf_le_of_frequently_le' hevent.frequently)
  have hi : Integrable F μ := ⟨hFm,
    (hasFiniteIntegral_iff_ofReal hF0).2 (hle.trans_lt ENNReal.ofReal_lt_top)⟩
  refine ⟨hi, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae hF0 hFm]
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hle).trans_eq (ENNReal.toReal_ofReal hC)

private theorem ae_tendsto_compactError_limitError {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    {ε : ℝ} (hε : 0 < ε) (T : ℝ≥0) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc),
      Tendsto (fun k => compactError ε (supAuxEps θ k) T f) atTop (𝓝 (limitError θ ε T f)) := by
  let : CompactSpace (Iic T) := isCompact_iff_compactSpace.mp (compact_nnreal_Iic T)
  filter_upwards [ae_supAuxLimit_spec hθ, ae_tendsto_supOccupation_supAuxEps_uniform hθ]
    with f hf hu
  let A : ℕ → C(Set.Iic T, ℝ) := fun k =>
    ⟨fun t => supOccupation (supAuxEps θ k) f t,
      (continuous_supOccupation ((isSupAuxEpsSeq_supAuxEps hθ).1 k) f).comp
        continuous_subtype_val⟩
  let g : C(Set.Iic T, ℝ) := ⟨fun t => supAuxLimit θ f t, hf.2.2.comp continuous_subtype_val⟩
  let a : C(Set.Iic T, ℝ) :=
    ⟨fun t => supOccupation ε f t, (continuous_supOccupation hε f).comp continuous_subtype_val⟩
  have hconv : Tendsto A atTop (𝓝 g) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    simpa only [ContinuousMap.dist_eq_iSup, Real.dist_eq, A, g, ContinuousMap.coe_mk] using hu T
  simpa only [ContinuousMap.dist_eq_iSup, Real.dist_eq, A, g, a, ContinuousMap.coe_mk,
    compactError, limitError] using (tendsto_const_nhds (x := a)).dist hconv

private theorem integrable_sq_limitError_le {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {ε : ℝ}
    (hε : 0 < ε) (T : ℝ≥0) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ᶠ k : ℕ in atTop,
      (∫ f, compactError ε (supAuxEps θ k) T f ^ 2
        ∂(stableLocalLaw θ : Measure DLoc)) ≤ C) :
    Integrable (fun f => limitError θ ε T f ^ 2) (stableLocalLaw θ : Measure DLoc) ∧
      (∫ f, limitError θ ε T f ^ 2 ∂(stableLocalLaw θ : Measure DLoc)) ≤ C := by
  apply integrable_ae_limit_of_integral_le
    (fun k => integrable_sq_compactError θ hε ((isSupAuxEpsSeq_supAuxEps hθ).1 k) T)
    (fun k => ae_of_all _ fun f => sq_nonneg _) (ae_of_all _ fun f => sq_nonneg _) hC
    _ hb
  filter_upwards [ae_tendsto_compactError_limitError hθ hε T] with f hf
  exact hf.pow 2

/-- **Full-filter compact `L²` convergence** `O_ε → M^*` as `ε ↓ 0` (not only along
`supAuxEps`): Cauchy estimate plus Fatou along the fast subsequence. -/
theorem supOccupation_compact_L2_tendsto_supAuxLimit {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (T : ℝ≥0) :
    (∀ ε : ℝ, 0 < ε →
      Integrable (fun f => (⨆ t : Set.Iic T, |supOccupation ε f t - supAuxLimit θ f t|) ^ 2)
        (stableLocalLaw θ : Measure DLoc)) ∧
    Tendsto (fun ε : ℝ =>
        ∫ f, (⨆ t : Set.Iic T, |supOccupation ε f t - supAuxLimit θ f t|) ^ 2
          ∂(stableLocalLaw θ : Measure DLoc)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hseq := isSupAuxEpsSeq_supAuxEps hθ
  refine ⟨fun ε hε => ?_, ?_⟩
  · apply (integrable_sq_limitError_le hθ hε T
      (by positivity : 0 ≤ 256 * Real.exp (2 * (T : ℝ))) _).1
    apply Eventually.of_forall
    intro k
    have hD (y : ℝ) : |supOccupationResolvent θ 1 ε y -
        supOccupationResolvent θ 1 (supAuxEps θ k) y| ≤ 1 := by
      obtain ⟨ha, hb⟩ := supOccupationResolvent_mem_Icc hθ zero_lt_one hε y
      obtain ⟨hc, hd⟩ := supOccupationResolvent_mem_Icc hθ zero_lt_one (hseq.1 k) y
      norm_num only [Real.one_rpow, div_one] at hb hd
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    have hh := (integral_sq_compactError_le hθ hε (hseq.1 k) hD T).2
    norm_num only [one_pow] at hh
    nlinarith only [hh]
  · apply Metric.tendsto_nhds.mpr
    intro δ hδ
    obtain ⟨a, ha, hb⟩ := supOccupation_compact_L2_cauchy hθ T (δ / 2) (half_pos hδ)
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds ha)]
      with ε hε hεa
    have hbound : ∀ᶠ k : ℕ in atTop,
        (∫ f, compactError ε (supAuxEps θ k) T f ^ 2
          ∂(stableLocalLaw θ : Measure DLoc)) ≤ δ / 2 := by
      filter_upwards [hseq.2.2.1.eventually (Iio_mem_nhds ha)] with k hk
      exact (hb ε _ hε hεa (hseq.1 k) hk).2
    have hh := (integrable_sq_limitError_le hθ hε T (half_pos hδ).le hbound).2
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (integral_nonneg fun f => sq_nonneg _)]
    exact hh.trans_lt (by linarith)

/-- A square-integrable sequence with uniformly bounded second moments has a
square-integrable almost sure limit. -/
theorem integrable_sq_of_ae_tendsto_of_integral_sq_le {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {F : Ω → ℝ} {G : ℕ → Ω → ℝ} {C : ℝ}
    (hF : AEStronglyMeasurable F μ) (hG : ∀ k, Integrable (fun f => G k f ^ 2) μ)
    (hC : 0 ≤ C) (hlim : ∀ᵐ f ∂μ, Tendsto (fun k => G k f) atTop (𝓝 (F f)))
    (hb : ∀ k, (∫ f, G k f ^ 2 ∂μ) ≤ C) : Integrable (fun f => F f ^ 2) μ := by
  have hlim2 : ∀ᵐ f ∂μ, Tendsto (fun k => G k f ^ 2) atTop (𝓝 (F f ^ 2)) := by
    filter_upwards [hlim] with f hf
    exact hf.pow 2
  have hi := (integrable_ae_limit_of_integral_le hG
    (fun k => ae_of_all _ fun f => sq_nonneg _) (ae_of_all _ fun f => sq_nonneg _)
    hC hlim2 (Eventually.of_forall hb)).1
  exact ⟨hF.pow 2, hi.hasFiniteIntegral⟩

private theorem integral_sq_supOccupation_uniform_le {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    {ε : ℝ} (hε : 0 < ε) (T : ℝ≥0) :
    Integrable (fun f => supOccupation ε f T ^ 2) (stableLocalLaw θ : Measure DLoc) ∧
      (∫ f, supOccupation ε f T ^ 2 ∂(stableLocalLaw θ : Measure DLoc)) ≤
        512 * Real.exp (2 * (T : ℝ)) + 2 * (T : ℝ) ^ 2 := by
  have hD (y : ℝ) : |supOccupationResolvent θ 1 ε y -
      supOccupationResolvent θ 1 1 y| ≤ 1 := by
    obtain ⟨ha, hb⟩ := supOccupationResolvent_mem_Icc hθ zero_lt_one hε y
    obtain ⟨hc, hd⟩ := supOccupationResolvent_mem_Icc hθ zero_lt_one zero_lt_one y
    norm_num only [Real.one_rpow, div_one] at hb hd
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  obtain ⟨hEi, hEb⟩ := integral_sq_compactError_le hθ hε zero_lt_one hD T
  have hm : Measurable (fun f : DLoc => supOccupation ε f T) :=
    measurable_supOccupation_uncurry.comp
      (measurable_const.prodMk (measurable_const.prodMk measurable_id))
  have hbound (f : DLoc) : supOccupation ε f T ^ 2 ≤
      2 * (compactError ε 1 T f ^ 2 + (T : ℝ) ^ 2) := by
    have he := abs_sub_supOccupation_le_compactError hε zero_lt_one T f ⟨T, le_rfl⟩
    have hO : supOccupation 1 f T ≤ (T : ℝ) := by
      simpa only [inv_one, one_mul, supOccupation_zero, sub_zero, NNReal.coe_zero] using
        (supOccupation_sub_mem zero_lt_one f (s := 0) (t := T) bot_le).2
    have hh : supOccupation ε f T ≤ compactError ε 1 T f + (T : ℝ) := by
      have ha := le_abs_self (supOccupation ε f T - supOccupation 1 f T)
      linarith only [ha, he, hO]
    have hsq := pow_le_pow_left₀ (supOccupation_nonneg hε.le f T) hh 2
    exact hsq.trans (by nlinarith only [sq_nonneg (compactError ε 1 T f - (T : ℝ))])
  have hdom : Integrable (fun f => 2 * (compactError ε 1 T f ^ 2 + (T : ℝ) ^ 2))
      (stableLocalLaw θ : Measure DLoc) := (hEi.add (integrable_const _)).const_mul 2
  have hi : Integrable (fun f => supOccupation ε f T ^ 2)
      (stableLocalLaw θ : Measure DLoc) := hdom.mono' (hm.aestronglyMeasurable.pow 2)
        (ae_of_all _ fun f => by
          change ‖supOccupation ε f T ^ 2‖ ≤ _
          rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (supOccupation ε f T))]
          exact hbound f)
  refine ⟨hi, ?_⟩
  have hh := integral_mono hi hdom hbound
  rw [integral_const_mul, integral_add hEi (integrable_const _)] at hh
  simp only [integral_const, Measure.real, measure_univ, ENNReal.toReal_one,
    smul_eq_mul, one_mul] at hh
  norm_num only [one_pow] at hEb
  linarith only [hh, hEb]

section AuxLimitSquare

-- Keeps the `limsup` definition opaque so that unification does not unfold it.
attribute [local irreducible] supAuxLimit

private theorem supAuxLimit_fixedTime_facts {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (T : ℝ≥0) :
    AEStronglyMeasurable (fun f : DLoc => supAuxLimit θ f T)
        (stableLocalLaw θ : Measure DLoc) ∧
      (∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), 0 ≤ supAuxLimit θ f T) ∧
      (∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc),
        Tendsto (fun k => supOccupation (supAuxEps θ k) f T) atTop (𝓝 (supAuxLimit θ f T))) ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℕ,
        Integrable (fun f => supOccupation (supAuxEps θ k) f T ^ 2)
            (stableLocalLaw θ : Measure DLoc) ∧
          (∫ f, supOccupation (supAuxEps θ k) f T ^ 2
            ∂(stableLocalLaw θ : Measure DLoc)) ≤ C := by
  have hm : Measurable (fun f : DLoc => supAuxLimit θ f T) :=
    (measurable_supAuxLimit_uncurry θ).comp (measurable_const.prodMk measurable_id)
  refine ⟨hm.aestronglyMeasurable, ?_, ?_,
    512 * Real.exp (2 * (T : ℝ)) + 2 * (T : ℝ) ^ 2, by positivity, fun k =>
      integral_sq_supOccupation_uniform_le hθ ((isSupAuxEpsSeq_supAuxEps hθ).1 k) T⟩
  · filter_upwards [ae_supAuxLimit_spec hθ] with f hf
    have hh := hf.2.1 (zero_le : (0 : ℝ≥0) ≤ T)
    simpa only [hf.1] using hh
  · let : CompactSpace (Iic T) := isCompact_iff_compactSpace.mp (compact_nnreal_Iic T)
    filter_upwards [ae_supAuxLimit_spec hθ, ae_tendsto_supOccupation_supAuxEps_uniform hθ]
      with f hf hu
    apply tendsto_iff_dist_tendsto_zero.mpr
    simp only [Real.dist_eq]
    apply squeeze_zero (fun k => abs_nonneg _) _ (hu T)
    intro k
    have hc : Continuous (fun t : Set.Iic T =>
        |supOccupation (supAuxEps θ k) f t - supAuxLimit θ f t|) :=
      (((continuous_supOccupation ((isSupAuxEpsSeq_supAuxEps hθ).1 k) f).sub hf.2.2).abs).comp
        continuous_subtype_val
    exact le_ciSup (isCompact_range hc).bddAbove (⟨T, le_rfl⟩ : Set.Iic T)

/-- The auxiliary clock has square integrable values on every compact horizon. -/
theorem integrable_sq_supAuxLimit {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (T : ℝ≥0) :
    Integrable (fun f => (supAuxLimit θ f T) ^ 2) (stableLocalLaw θ : Measure DLoc) := by
  set F : DLoc → ℝ := fun f => supAuxLimit θ f T with hF
  obtain ⟨hm, _h0, hl, C, hC, hG⟩ := supAuxLimit_fixedTime_facts hθ T
  change AEStronglyMeasurable F (stableLocalLaw θ : Measure DLoc) at hm
  change ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc),
    Tendsto (fun k => supOccupation (supAuxEps θ k) f T) atTop (𝓝 (F f)) at hl
  change Integrable (fun f => F f ^ 2) (stableLocalLaw θ : Measure DLoc)
  clear_value F
  exact integrable_sq_of_ae_tendsto_of_integral_sq_le hm (fun k => (hG k).1)
    hC hl (fun k => (hG k).2)

end AuxLimitSquare

end BGW.StableTrees
