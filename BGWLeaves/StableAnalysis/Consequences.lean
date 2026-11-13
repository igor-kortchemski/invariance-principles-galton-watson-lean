module

public import BGWLeaves.StableAnalysis

/-!
# Scalar stable analysis: consequences of the main statements

Declarations that use at least one of the statements of `BGWLeaves.StableAnalysis`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal

namespace BGWLeaves.StableAnalysis

open BGW.StableTrees
open BGW.LocallyFinite (bienaymeLaw sizeEvent FiniteVertices Present)

/-! ## Theorem 1.10(iii) -/

section LocalLimit

variable (ν : Measure ℤ) [IsProbabilityMeasure ν] {θ : ℝ}

/-- 1.10(iii) with the corrected norming. -/
theorem locallimit_iii (hstep : ν {z | z < -1} = 0) (hint : Integrable (fun z : ℤ => (z : ℝ)) ν)
    (hnl : ¬ IsLatticeLaw ν) (hDA : ∃ b, IsStableAttracted ν θ (mean ν) b) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ k : ℤ,
      |norming ν θ n * intWalkProb ν n k -
          Scalar.stableDensity θ (((k : ℝ) - n * mean ν) / norming ν θ n)| ≤ ε := by
  obtain ⟨hmono, -⟩ := locallimit_ii ν hstep hint hDA
  exact llt_abstract ν hint hnl hmono (locallimit_i ν hstep hint hDA) hε

end LocalLimit

/-! ## Lemma 1.11 -/

/-- Lemma 1.11 in the paper's wording, `B_n := norming (stepLaw μ) θ n = n^{1/θ} h(n)`.
Both bridges `locallimit_i`/`locallimit_ii` are used to see `norming` as a `StableDomain` norming. -/
theorem lem_locallimit {μ : PMF ℕ} {θ : ℝ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hap : Aperiodic μ) (hDA : ∃ b, StableDomain μ θ b) :
    Tendsto (fun n : ℕ => (n : ℝ) * norming (stepLaw μ) θ n *
        (bienaymeLaw μ.toMeasure).real (sizeEvent n)) atTop (𝓝 (Scalar.stableDensity θ 0)) ∧
      Tendsto (fun n : ℕ => norming (stepLaw μ) θ n *
        (bienaymeLaw μ.toMeasure).real (sizeGeEvent n)) atTop
        (𝓝 (θ * Scalar.stableDensity θ 0)) := by
  obtain ⟨b, hb⟩ := hDA
  have := isProbabilityMeasure_stepLaw μ
  have hstep := stepLaw_lt_neg_one μ
  have hmean := mean_stepLaw hc
  have hi := locallimit_i (stepLaw μ) hstep (integrable_stepLaw hc)
    ⟨b, by rw [hmean]; exact stableDomain_isStableAttracted hb⟩
  have hm := (locallimit_ii (stepLaw μ) hstep (integrable_stepLaw hc)
    ⟨b, by rw [hmean]; exact stableDomain_isStableAttracted hb⟩).1
  rw [hmean] at hi
  obtain ⟨a', hae, hdom⟩ := hi.exists_stableDomain hc hne hm
  refine ⟨(sizeProb_asymp hdom hap).congr' (hae.mono fun n hn => by simp [hn]),
    (sizeTail_asymp hdom hap).congr' (hae.mono fun n hn => by simp [hn])⟩

/-- The same lemma for the sequences `h, h'` (`B_n = h(n) n^{1/θ}`). -/
theorem lem_hhp_slow {μ : PMF ℕ} {θ : ℝ} (hc : IsCritical μ) (hne : μ 1 ≠ 1) (hap : Aperiodic μ)
    (hDA : ∃ b, StableDomain μ θ b)
    (hinf : ¬ Integrable (fun z : ℤ => (z : ℝ) ^ 2) (stepLaw μ)) :
    Tendsto (fun n : ℕ => (norming (etaLaw μ) θ n / (n : ℝ) ^ (1 / θ)) /
        (norming (stepLaw μ) θ n / (n : ℝ) ^ (1 / θ))) atTop
      (𝓝 ((1 - (μ 0).toReal) ^ (-(1 / θ)))) := by
  refine (lem_hhp hc hne hap hDA hinf).congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have : (0 : ℝ) < (n : ℝ) ^ (1 / θ) := Real.rpow_pos_of_pos (by exact_mod_cast hn) _
  field_simp

/-- 1.10(iii) in finite variance is the unweighted case of 3.5. -/
theorem llt_finiteVariance_of_strong (ρ : Measure ℤ) [IsProbabilityMeasure ρ]
    (hnl : ¬ IsLatticeLaw ρ) (hL2 : Integrable (fun z : ℤ => (z : ℝ) ^ 2) ρ) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ k : ℤ,
      |norming ρ 2 n * intWalkProb ρ n k -
          Scalar.stableDensity 2 (((k : ℝ) - n * mean ρ) / norming ρ 2 n)| ≤ ε := by
  obtain ⟨N, hN⟩ := strongLLT ρ hnl hL2 hε
  refine ⟨N, fun n hn k => ?_⟩
  rw [norming_of_integrable_sq hL2, stableDensity_two]
  exact le_trans (le_mul_of_one_le_left (abs_nonneg _) (le_max_left _ _)) (hN n hn k)

/-- **Bridge from `(H_θ)(ii)` to `StableDomain`**: the finite-variance branch is BGW's
`stableDomain_of_finiteVariance`; the tail branch is `exists_stableDomain_of_tail`. -/
theorem exists_stableDomain_of_Htheta {μ : PMF ℕ} {θ : ℝ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hθ : 1 < θ ∧ θ ≤ 2) (h : HthetaTail μ θ) : ∃ a : ℕ → ℝ, StableDomain μ θ a := by
  rcases h with ⟨rfl, hfin⟩ | ⟨L, hmeas, hnn, hL, htail⟩
  · exact ⟨_, Scalar.stableDomain_of_finiteVariance hc hne hfin⟩
  · exact exists_stableDomain_of_tail hc hne hθ hmeas hnn hL htail

theorem exists_isStableAttracted_of_Htheta {μ : PMF ℕ} {θ : ℝ} (hc : IsCritical μ)
    (hne : μ 1 ≠ 1) (hθ : 1 < θ ∧ θ ≤ 2) (h : HthetaTail μ θ) :
    ∃ b : ℕ → ℝ, IsStableAttracted (stepLaw μ) θ (mean (stepLaw μ)) b := by
  obtain ⟨a, ha⟩ := exists_stableDomain_of_Htheta hc hne hθ h
  exact ⟨a, by rw [mean_stepLaw hc]; exact stableDomain_isStableAttracted ha⟩

end BGWLeaves.StableAnalysis
