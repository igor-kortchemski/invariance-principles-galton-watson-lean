module

public import BGWLeaves.GeneralA.MarkedSeries
public import BGWLeaves.GeneralA.Moments

/-! The probability law of one A-marked time increment. -/

@[expose] public section

namespace BGWLeaves.GeneralA.MarkedTime

open MeasureTheory ProbabilityTheory BGW BGW.StableTrees BGWLeaves.StableAnalysis
open MarkedWalk Regroup Moments
open scoped ENNReal Topology

noncomputable section
attribute [local instance] Classical.propDecidable

/-- A normalization at zero mass is immaterial after multiplication by that mass;
we use the probability law `δ₀` in that case. -/
noncomputable def normalized (ν : Measure ℤ) : Measure ℤ :=
  if ν Set.univ = 0 then Measure.dirac 0 else (ν Set.univ)⁻¹ • ν

theorem normalized_probability (ν : Measure ℤ) [IsFiniteMeasure ν] :
    IsProbabilityMeasure (normalized ν) := by
  by_cases h : ν Set.univ = 0
  · simp only [normalized, ite_eq_left h]; infer_instance
  · constructor
    rw [normalized, ite_eq_right h, Measure.smul_apply, smul_eq_mul,
      ENNReal.inv_mul_cancel h (measure_ne_top _ _)]

theorem mass_smul_normalized (ν : Measure ℤ) [IsFiniteMeasure ν] :
    (ν Set.univ) • normalized ν = ν := by
  by_cases h : ν Set.univ = 0
  · have hν : ν = 0 := Measure.measure_univ_eq_zero.mp h
    simp [hν]
  · rw [normalized, ite_eq_right h, smul_smul,
      ENNReal.mul_inv_cancel h (measure_ne_top _ _), one_smul]

theorem integrable_normalized (ν : Measure ℤ) [IsFiniteMeasure ν] (f : ℤ → ℝ)
    (hf : Integrable f ν) : Integrable f (normalized ν) := by
  by_cases h : ν Set.univ = 0
  · rw [normalized, ite_eq_left h]
    exact integrable_dirac (by simp)
  · rw [normalized, ite_eq_right h]
    exact hf.smul_measure (ENNReal.inv_ne_top.mpr h)

theorem markedStep_eq_map_restrict (μ : PMF ℕ) (A : Set ℕ) :
    markedStep (fun k => μ k) A =
      (μ.toMeasure.restrict A).map (fun k : ℕ => (k : ℤ) - 1) := by
  rw [← Measure.sum_smul_dirac (μ.toMeasure.restrict A), Measure.map_sum (by fun_prop)]
  simp_rw [Measure.map_smul (f := fun k : ℕ => (k : ℤ) - 1) _ (measurable_of_countable _).aemeasurable,
    Measure.map_dirac' (measurable_of_countable (fun k : ℕ => (k : ℤ) - 1))]
  unfold markedStep weightedStep
  congr 1
  funext k
  by_cases hk : k ∈ A <;>
    simp [Measure.restrict_apply (measurableSet_singleton _), hk,
      PMF.toMeasure_apply_singleton μ _ (measurableSet_singleton _)]

private instance markedStep_finite (μ : PMF ℕ) (A : Set ℕ) :
    IsFiniteMeasure (markedStep (fun k => μ k) A) := by
  rw [markedStep_eq_map_restrict]
  infer_instance

private instance unmarkedStep_finite (μ : PMF ℕ) (A : Set ℕ) :
    IsFiniteMeasure (unmarkedStep (fun k => μ k) A) := by
  unfold unmarkedStep
  infer_instance

theorem markedStep_mass (μ : PMF ℕ) (A : Set ℕ) :
    markedStep (fun k => μ k) A Set.univ = μ.toMeasure A := by
  rw [markedStep_eq_map_restrict, Measure.map_apply (by fun_prop) MeasurableSet.univ]
  simp

theorem stepLaw_decomposition (μ : PMF ℕ) (A : Set ℕ) :
    stepLaw μ = markedStep (fun k => μ k) A + unmarkedStep (fun k => μ k) A := by
  rw [unmarkedStep, markedStep_eq_map_restrict, markedStep_eq_map_restrict,
    ← Measure.map_add _ _ (measurable_of_countable _), Measure.restrict_add_restrict_compl MeasurableSet.of_discrete]
  rfl

private instance walk_probability (ν : Measure ℤ) [IsProbabilityMeasure ν] (n : ℕ) :
    IsProbabilityMeasure (intWalk ν n) := by
  induction n with
  | zero => simp only [intWalk]; infer_instance
  | succ n ih => simpa only [intWalk] using
      (inferInstance : IsProbabilityMeasure ((intWalk ν n).conv ν))

private theorem intWalk_smul (r : ℝ≥0∞) (ν : Measure ℤ) [IsProbabilityMeasure ν] (n : ℕ) :
    intWalk (r • ν) n = r ^ n • intWalk ν n := by
  induction n with
  | zero => simp [intWalk]
  | succ n ih =>
    rw [intWalk, ih, Measure.conv_smul_left, Measure.conv_smul_right, smul_smul, ← pow_succ]
    rfl

theorem blockLaw_eq_normalized (μ : PMF ℕ) (A : Set ℕ) :
    blockLaw (markedStep (fun k => μ k) A) (unmarkedStep (fun k => μ k) A) =
      (normalized (markedStep (fun k => μ k) A)).conv
        (geometricLaw (μ.toMeasure A) (normalized (unmarkedStep (fun k => μ k) A))) := by
  let α := markedStep (fun k => μ k) A
  let β := unmarkedStep (fun k => μ k) A
  have := normalized_probability α
  have := normalized_probability β
  have hα : μ.toMeasure A • normalized α = α := by
    simpa only [α, markedStep_mass] using mass_smul_normalized α
  have hβ : (1 - μ.toMeasure A) • normalized β = β := by
    have hm : β Set.univ = 1 - μ.toMeasure A := by
      dsimp [β, unmarkedStep]
      rw [markedStep_mass, prob_compl_eq_one_sub MeasurableSet.of_discrete]
    rw [← hm]
    exact mass_smul_normalized β
  change blockLaw α β = _
  rw [blockLaw, ← hα, ← hβ]
  simp_rw [intWalk_smul]
  rw [Measure.conv_smul_left, ← Measure.conv_smul_right]
  congr 1
  ext s hs
  simp only [Measure.smul_apply, Measure.sum_apply _ hs, smul_eq_mul, geometricLaw]
  simp only [mul_assoc]
  rw [ENNReal.tsum_mul_left]

theorem blockLaw_probability {μ : PMF ℕ} {A : Set ℕ} (hA : μ.toMeasure A ≠ 0) :
    IsProbabilityMeasure (blockLaw (markedStep (fun k => μ k) A) (unmarkedStep (fun k => μ k) A)) := by
  have := normalized_probability (markedStep (fun k => μ k) A)
  have := normalized_probability (unmarkedStep (fun k => μ k) A)
  have := geometricLaw_probability hA prob_le_one (normalized (unmarkedStep (fun k => μ k) A))
  rw [blockLaw_eq_normalized]
  infer_instance

/-- Wald's two moment identities, proved from the explicit geometric mixture.
The normalized unmarked law may have negative increments or zero variance. -/
theorem blockLaw_moments {μ : PMF ℕ} (hc : IsCritical μ)
    (hfin : Integrable (fun z : ℤ => (z : ℝ) ^ 2) (stepLaw μ))
    {A : Set ℕ} (hA : μ.toMeasure A ≠ 0) :
    let ν := blockLaw (markedStep (fun k => μ k) A) (unmarkedStep (fun k => μ k) A)
    Integrable (fun z : ℤ => (z : ℝ)) ν ∧ mean ν = 0 ∧
      Integrable (fun z : ℤ => (z : ℝ) ^ 2) ν ∧
        variance ν = variance (stepLaw μ) / (μ.toMeasure A).toReal := by
  let α := markedStep (fun k => μ k) A
  let β := unmarkedStep (fun k => μ k) A
  let τ := normalized α
  let ρ := normalized β
  let q := μ.toMeasure A
  have := normalized_probability α
  have := normalized_probability β
  have hqtop : q ≠ ⊤ := measure_ne_top _ _
  have hqle : q ≤ 1 := prob_le_one
  have hq : 0 < q.toReal := ENNReal.toReal_pos hA hqtop
  have hr : 1 - q ≠ ⊤ := by finiteness
  have hα : q • τ = α := by simpa only [α, markedStep_mass] using mass_smul_normalized α
  have hβmass : β Set.univ = 1 - q := by
    dsimp [β, unmarkedStep, q]
    rw [markedStep_mass, prob_compl_eq_one_sub MeasurableSet.of_discrete]
  have hβ : (1 - q) • ρ = β := by rw [← hβmass]; exact mass_smul_normalized β
  have hstep : stepLaw μ = α + β := stepLaw_decomposition μ A
  have hnorm : stepLaw μ = q • τ + (1 - q) • ρ := by rw [hα, hβ]; exact hstep
  have hαle : α ≤ stepLaw μ := by rw [hstep]; exact Measure.le_add_right le_rfl
  have hβle : β ≤ stepLaw μ := by rw [hstep]; exact Measure.le_add_left le_rfl
  have hτ := integrable_normalized α (fun z : ℤ => (z : ℝ)) ((integrable_stepLaw hc).mono_measure hαle)
  have hρ := integrable_normalized β (fun z : ℤ => (z : ℝ)) ((integrable_stepLaw hc).mono_measure hβle)
  have hτsq := integrable_normalized α (fun z : ℤ => (z : ℝ) ^ 2) (hfin.mono_measure hαle)
  have hρsq := integrable_normalized β (fun z : ℤ => (z : ℝ) ^ 2) (hfin.mono_measure hβle)
  have hmean : q.toReal * mean τ + (1 - q.toReal) * mean ρ = 0 := by
    have h := mean_stepLaw hc
    rw [mean, hnorm, integral_add_measure (hτ.smul_measure hqtop) (hρ.smul_measure hr),
      integral_smul_measure, integral_smul_measure] at h
    simpa only [smul_eq_mul, ENNReal.toReal_sub_of_le hqle ENNReal.one_ne_top,
      ENNReal.toReal_one, mean] using h
  have hraw : q.toReal * (∫ z : ℤ, (z : ℝ) ^ 2 ∂τ) +
      (1 - q.toReal) * (∫ z : ℤ, (z : ℝ) ^ 2 ∂ρ) = variance (stepLaw μ) := by
    have h : (∫ z : ℤ, (z : ℝ) ^ 2 ∂stepLaw μ) = variance (stepLaw μ) := by
      rw [BGWLeaves.StableAnalysis.variance, mean_stepLaw hc]
      simp only [sub_zero]
    conv_lhs at h => rw [hnorm]
    rw [integral_add_measure (hτsq.smul_measure hqtop) (hρsq.smul_measure hr),
      integral_smul_measure, integral_smul_measure] at h
    simpa only [smul_eq_mul, ENNReal.toReal_sub_of_le hqle ENNReal.one_ne_top,
      ENNReal.toReal_one] using h
  let H := geometricLaw q ρ
  have := geometricLaw_probability hA hqle ρ
  obtain ⟨hH, hHM⟩ := geometricLaw_firstMoment hA hqle ρ hρ hρsq
  obtain ⟨hHsq, hHS⟩ := geometricLaw_secondMoment hA hqle ρ hρ hρsq
  obtain ⟨hν, hνM⟩ := conv_firstMoment τ H hτ hH
  obtain ⟨hνsq, hνS⟩ := conv_secondMoment τ H hτ hH hτsq hHsq
  have hMA : mean τ = -((1 - q.toReal) / q.toReal) * mean ρ := by
    field_simp
    nlinarith [hmean]
  have hνzero : mean (τ.conv H) = 0 := by rw [hνM, hHM, hMA]; ring
  have hνraw : (∫ z : ℤ, (z : ℝ) ^ 2 ∂τ.conv H) =
      (∫ z : ℤ, (z : ℝ) ^ 2 ∂τ) + (1 - q.toReal) / q.toReal * (∫ z : ℤ, (z : ℝ) ^ 2 ∂ρ) := by
    rw [hνS, hHM, hHS, hMA]
    ring
  have hvar : variance (τ.conv H) = variance (stepLaw μ) / q.toReal := by
    rw [BGWLeaves.StableAnalysis.variance, hνzero]
    simp only [sub_zero]
    rw [hνraw]
    field_simp
    nlinarith [hraw]
  dsimp only
  rw [blockLaw_eq_normalized]
  exact ⟨hν, hνzero, hνsq, hvar⟩

end
end BGWLeaves.GeneralA.MarkedTime
