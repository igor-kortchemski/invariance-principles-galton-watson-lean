module

public import BGWLeaves.LocalEstimates.Defs
import BGWLeaves.LeafMass.YLaw
import BGWLeaves.StableAnalysis.TransformConvergence

/-!
# M7 provider `NormRatios`

Proofs of the arithmetic of `Y` and the norming ratios: `mu0_ne_one`, `nonLattice_etaLaw_iff`, `hS_of_nonLattice`, `normB_ratio_tendsto`, `normBp_ratio_tendsto`, `normBp_div_normB_infVar`, `normBp_div_normB_finVar`.  The theorems to be proved here are the registered holes of
`BGWLeaves.LocalEstimates`; they are exported in namespace `BGWLeaves.LocalEstimates.NormRatios` with exactly the types of the
statements file.
-/

@[expose] public section

namespace BGWLeaves.LocalEstimates.NormRatios

open MeasureTheory ProbabilityTheory Filter BGW BGW.StableTrees
open BGWLeaves.StableAnalysis
open scoped ENNReal Topology

set_option linter.unusedSectionVars false

theorem mu0_ne_one {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1) : μ 0 ≠ 1 := by
  intro h
  simpa only [h, ENNReal.toReal_one, sub_self, lt_self_iff_false] using
    EtaTransfer.one_sub_apply_zero_pos hc hne

theorem nonLattice_etaLaw_iff {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1) :
    ¬ IsLatticeLaw (etaLaw μ) ↔
      ¬ ∃ (b' : ℤ) (d' : ℕ), 2 ≤ d' ∧ ∀ k : ℕ, μ k ≠ 0 → k ≠ 0 → (d' : ℤ) ∣ (k : ℤ) - b' := by
  apply not_congr
  constructor
  · rintro ⟨r, d, hd, hr⟩
    exact ⟨r + 1, d, hd, (LeafMass.YLaw.etaLaw_ae_dvd_iff hc hne d r).mp hr⟩
  · rintro ⟨b, d, hd, hb⟩
    refine ⟨b - 1, d, hd, (LeafMass.YLaw.etaLaw_ae_dvd_iff hc hne d (b - 1)).mpr ?_⟩
    simpa only [sub_add_cancel] using hb

theorem hS_of_nonLattice {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hnl : ¬ IsLatticeLaw (etaLaw μ)) :
    ∃ k₁ k₂ : ℕ, 1 ≤ k₁ ∧ k₁ < k₂ ∧ μ k₁ ≠ 0 ∧ μ k₂ ≠ 0 := by
  obtain ⟨j, hj, hjμ⟩ := hc.exists_two_le_ne_zero hne
  by_contra hS
  have heq : ∀ k : ℕ, μ k ≠ 0 → k ≠ 0 → k = j := by
    intro k hk hk0
    by_contra hkj
    rcases lt_or_gt_of_ne hkj with hlt | hgt
    · exact hS ⟨k, j, by omega, hlt, hk, hjμ⟩
    · exact hS ⟨j, k, by omega, hgt, hjμ, hk⟩
  apply hnl
  refine ⟨(j : ℤ) - 1, 2, by norm_num, ?_⟩
  apply (LeafMass.YLaw.etaLaw_ae_dvd_iff hc hne 2 ((j : ℤ) - 1)).mpr
  intro k hk hk0
  rw [heq k hk hk0]
  simp

private theorem floor_index_ratio {u : ℕ → ℝ} {l : ℝ} (hl : 0 < l)
    (hu : Tendsto (fun n : ℕ => u n / n) atTop (𝓝 l)) :
    Tendsto (fun n : ℕ => (⌊u n⌋₊ : ℝ) / n) atTop (𝓝 l) := by
  have hlow : Tendsto (fun n : ℕ => u n / n - 1 / (n : ℝ)) atTop (𝓝 l) := by
    simpa only [sub_zero] using hu.sub tendsto_one_div_atTop_nhds_zero_nat
  have hpos : ∀ᶠ n : ℕ in atTop, 0 ≤ u n ∧ 0 < (n : ℝ) := by
    filter_upwards [hu.eventually (Ioi_mem_nhds hl), eventually_ge_atTop 1] with n hn hn1
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn1
    rw [lt_div_iff₀ hnR, zero_mul] at hn
    exact ⟨hn.le, hnR⟩
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hu
  · filter_upwards [hpos] with n hn
    rw [← sub_div]
    exact div_le_div_of_nonneg_right (by linarith [Nat.lt_floor_add_one (u n)]) hn.2.le
  · filter_upwards [hpos] with n hn
    exact div_le_div_of_nonneg_right (Nat.floor_le hn.1) hn.2.le

private theorem hS_of_aperiodic {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hap : Aperiodic μ) :
    ∃ k₁ k₂ : ℕ, 1 ≤ k₁ ∧ k₁ < k₂ ∧ μ k₁ ≠ 0 ∧ μ k₂ ≠ 0 := by
  obtain ⟨d, b, hdb⟩ := exists_isSuppSpan hc hne hap
  exact LeafMass.YLaw.isSuppSpan_two_points hc hne hdb

section Htheta
variable {μ : PMF ℕ} {θ : ℝ} (hc : IsCritical μ) (hne : μ 1 ≠ 1) (hap : Aperiodic μ)
  (hDA : ∃ b, StableDomain μ θ b)
include hc hne hap hDA

theorem normB_ratio_tendsto {u : ℕ → ℝ} {l : ℝ} (hl : 0 < l)
    (hu : Tendsto (fun n : ℕ => u n / n) atTop (𝓝 l)) :
    Tendsto (fun n : ℕ => normB μ θ (u n) / normB μ θ n) atTop (𝓝 (l ^ (1 / θ))) := by
  obtain ⟨b, hb⟩ := hDA
  have hDA' : ∃ b, IsStableAttracted (stepLaw μ) θ (mean (stepLaw μ)) b :=
    ⟨b, by rw [mean_stepLaw hc]; exact stableDomain_isStableAttracted hb⟩
  have ha := locallimit_i (stepLaw μ) (stepLaw_lt_neg_one μ) (integrable_stepLaw hc) hDA'
  have ht := TransformConvergence.tendsto_div_of_tendsto_div' (stepLaw μ) ha ha hl
    (floor_index_ratio hl hu)
  simpa only [normB, Nat.floor_natCast] using ht

theorem normBp_ratio_tendsto {u : ℕ → ℝ} {l : ℝ} (hl : 0 < l)
    (hu : Tendsto (fun n : ℕ => u n / n) atTop (𝓝 l)) :
    Tendsto (fun n : ℕ => normBp μ θ (u n) / normBp μ θ n) atTop (𝓝 (l ^ (1 / θ))) := by
  let := EtaTransfer.isProbabilityMeasure_etaLaw hc hne
  have ha := (etaLaw_norming hc hne (hS_of_aperiodic hc hne hap) hDA).1
  have ht := TransformConvergence.tendsto_div_of_tendsto_div' (etaLaw μ) ha ha hl
    (floor_index_ratio hl hu)
  simpa only [normBp, Nat.floor_natCast] using ht

theorem normBp_div_normB_infVar
    (hinf : ¬ Integrable (fun z : ℤ => (z : ℝ) ^ 2) (stepLaw μ)) :
    Tendsto (fun n : ℕ => norming (etaLaw μ) θ n / normB μ θ ((n : ℝ) / (μ 0).toReal)) atTop
      (𝓝 (cC μ ^ (1 / θ))) := by
  have hm : 0 < (μ 0).toReal := ENNReal.toReal_pos (hc.apply_zero_ne_zero hne) (μ.apply_ne_top 0)
  have hq := EtaTransfer.one_sub_apply_zero_pos hc hne
  have hu : Tendsto (fun n : ℕ => ((n : ℝ) / (μ 0).toReal) / n) atTop (𝓝 (1 / (μ 0).toReal)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    field_simp
  have hr := (normB_ratio_tendsto hc hne hap hDA (one_div_pos.mpr hm) hu).inv₀
    (Real.rpow_pos_of_pos (one_div_pos.mpr hm) _).ne'
  simp only [inv_div, normB_natCast] at hr
  have ht := (lem_hhp hc hne hap hDA hinf).mul hr
  have hconst : (1 - (μ 0).toReal) ^ (-(1 / θ)) * ((1 / (μ 0).toReal) ^ (1 / θ))⁻¹ =
      cC μ ^ (1 / θ) := by
    rw [Real.div_rpow (by norm_num : (0 : ℝ) ≤ 1) hm.le, Real.one_rpow]
    simp only [one_div, inv_inv]
    rw [Real.rpow_neg hq.le]
    dsimp [cC]
    rw [Real.div_rpow hm.le hq.le]
    ring
  rw [hconst] at ht
  obtain ⟨b, hb⟩ := hDA
  have ha := locallimit_i (stepLaw μ) (stepLaw_lt_neg_one μ) (integrable_stepLaw hc)
    ⟨b, by rw [mean_stepLaw hc]; exact stableDomain_isStableAttracted hb⟩
  obtain ⟨N, hN⟩ := ha.pos
  apply ht.congr'
  filter_upwards [eventually_ge_atTop N] with n hn
  have hB := (hN n hn).ne'
  field_simp

theorem normBp_div_normB_finVar
    (hfin : Integrable (fun z : ℤ => (z : ℝ) ^ 2) (stepLaw μ)) :
    Tendsto (fun n : ℕ => norming (etaLaw μ) θ n / normB μ θ ((n : ℝ) / (μ 0).toReal)) atTop
      (𝓝 (Real.sqrt (μ 0).toReal * Real.sqrt (variance (etaLaw μ)) /
        Real.sqrt (variance (stepLaw μ)))) := by
  obtain ⟨b, hb⟩ := hDA
  have ha : IsStableAttracted (stepLaw μ) θ (mean (stepLaw μ)) b := by
    rw [mean_stepLaw hc]
    exact stableDomain_isStableAttracted hb
  have hθ := DomainCriterion.index_eq_two_of_integrable_sq ha (integrable_stepLaw hc) hfin
  subst θ
  exact finiteVariance_norming_ratio_eta hc hne hfin

end Htheta
end BGWLeaves.LocalEstimates.NormRatios
