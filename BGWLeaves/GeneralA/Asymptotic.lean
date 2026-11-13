module

public import BGWLeaves.GeneralA.Arithmetic
public import BGWLeaves.GeneralA.MarkedSpan
public import BGWLeaves.LeafMass.YLaw
public import BGWLeaves.StableAnalysis.StableDomainTail

/-! The corrected finite-variance Theorem 8.1(I). The factor is `arithFactor μ A`,
not the manuscript's incorrect complement-span factor. -/

@[expose] public section

namespace BGWLeaves.GeneralA.Asymptotic

open MeasureTheory ProbabilityTheory Filter BGW BGW.StableTrees BGW.LocallyFinite
open BGWLeaves.StableAnalysis MarkedWalk Regroup MarkedTime MarkedSpan
open scoped ENNReal Topology

/-- The corrected finite-variance local limit for arbitrary offspring marks. -/
theorem thm81_finiteVariance_corrected {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hap : Aperiodic μ) (hvar : Integrable (fun z : ℤ => (z : ℝ) ^ 2) (stepLaw μ))
    {A : Set ℕ} (hA : μ.toMeasure A ≠ 0) :
    (∀ n : ℕ, ¬ ((arithFactor μ A : ℤ) ∣ (n : ℤ) - 1) →
        bienaymeLaw μ.toMeasure {T | zetaA A T = n} = 0) ∧
    Tendsto (fun j : ℕ =>
        ((arithFactor μ A * j + 1 : ℕ) : ℝ) ^ ((3 : ℝ) / 2) *
          (bienaymeLaw μ.toMeasure).real {T | zetaA A T = ((arithFactor μ A * j + 1 : ℕ) : ℕ∞)})
      atTop
      (𝓝 ((arithFactor μ A : ℝ) * Real.sqrt (2 * (μ.toMeasure A).toReal) /
        (2 * Real.sqrt (BGWLeaves.StableAnalysis.variance (stepLaw μ)) * Real.sqrt Real.pi))) := by
  have _ := hap
  refine ⟨fun n hn => MarkedLaw.zetaA_eq_zero_of_not_dvd A hc hne n hn, ?_⟩
  let ν := blockLaw (markedStep (fun k => μ k) A) (unmarkedStep (fun k => μ k) A)
  have : IsProbabilityMeasure ν := blockLaw_probability hA
  obtain ⟨hi, hm, hsq, hV⟩ := blockLaw_moments hc hvar hA
  change mean ν = 0 at hm
  obtain ⟨hspan, hsupp⟩ := blockLaw_span hc hne hA
  have hDA := Scalar.stableDomain_of_finiteVariance hc hne
    (StableDomainTail.memLp_offspring_of_integrable_sq hvar)
  have hσ := DomainCriterion.variance_pos_of_integrable_sq (stableDomain_isStableAttracted hDA)
    (integrable_stepLaw hc) hvar
  have hq : 0 < (μ.toMeasure A).toReal := ENNReal.toReal_pos hA (measure_ne_top _ _)
  have hνvar : 0 < variance ν := by rw [hV]; exact div_pos hσ hq
  have hattr := CanonicalAttraction.isStableAttracted_of_finiteVariance hi hsq hνvar
  have hmono : Monotone (norming ν 2) := by
    intro i j hij
    rw [norming_of_integrable_sq hsq, norming_of_integrable_sq hsq]
    apply mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) (Real.sqrt_nonneg _)
    exact div_le_div_of_nonneg_right (by exact_mod_cast hij) (by norm_num : (0 : ℝ) ≤ 2)
  have hBtop := TransformConvergence.tendsto_atTop ν hattr
  let e := arithFactor μ A
  let N : ℕ → ℕ := fun j => e * j + 1
  have he : 0 < e := Arithmetic.arithFactor_pos hc hne A
  have hNtop : Tendsto N atTop atTop :=
    tendsto_atTop_mono (fun j => by dsimp [N]; nlinarith) tendsto_id
  have herr : Tendsto (fun j : ℕ => norming ν 2 (N j) * intWalkProb ν (N j) (-1) -
      (e : ℝ) * Scalar.stableDensity 2 ((-1 : ℝ) / norming ν 2 (N j))) atTop (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨K, hK⟩ := LeafMass.YLaw.llt_lattice_abstract ν hi hspan (-1) hsupp hmono hattr (half_pos hε)
    filter_upwards [hNtop.eventually (eventually_ge_atTop K)] with j hj
    have hmod : (e : ℤ) ∣ (-1 : ℤ) - (N j : ℤ) * (-1) := by
      have hd : e ∣ e * j := dvd_mul_right _ _
      convert Int.natCast_dvd_natCast.2 hd using 1; dsimp [N]; ring
    have hmod' : (arithFactor μ A : ℤ) ∣ (-1 : ℤ) - (N j : ℤ) * (-1) := hmod
    have hbound := hK (N j) hj (-1)
    simp only [hm, mul_zero, sub_zero, ite_eq_left hmod', Int.cast_neg, Int.cast_one] at hbound
    rw [Real.dist_eq, sub_zero]
    exact lt_of_le_of_lt hbound (half_lt_self hε)
  have harg : Tendsto (fun j => (-1 : ℝ) / norming ν 2 (N j)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (hBtop.comp hNtop)
  have hp := ((Scalar.continuous_stableDensity hattr.alpha_mem).continuousAt.tendsto.comp harg).const_mul (e : ℝ)
  have hllt := herr.add hp
  simp only [sub_add_cancel, zero_add, Function.comp_apply] at hllt
  have hid (j : ℕ) :
      (bienaymeLaw μ.toMeasure).real {T | zetaA A T = ((N j : ℕ) : ℕ∞)} =
        (N j : ℝ)⁻¹ * intWalkProb ν (N j) (-1) := by
    change (bienaymeLaw μ.toMeasure {T | zetaA A T = ((e * j + 1 : ℕ) : ℕ∞)}).toReal = _
    rw [MarkedSeries.zetaA_blockLaw hc hne A (e * j), ENNReal.toReal_mul,
      ENNReal.toReal_inv, ENNReal.toReal_natCast]
    rfl
  have hfun (j : ℕ) :
      (N j : ℝ) ^ ((3 : ℝ) / 2) *
        (bienaymeLaw μ.toMeasure).real {T | zetaA A T = ((N j : ℕ) : ℕ∞)} =
      (Real.sqrt 2 / Real.sqrt (variance ν)) * (norming ν 2 (N j) * intWalkProb ν (N j) (-1)) := by
    have hx : (0 : ℝ) < N j := by dsimp [N]; positivity
    have hroot := (Real.sqrt_pos.2 hνvar).ne'
    have htwo := (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2)).ne'
    have hpow : (N j : ℝ) ^ ((3 : ℝ) / 2) = (N j : ℝ) * Real.sqrt (N j) := by
      rw [show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num, Real.rpow_add hx,
        Real.rpow_one, ← Real.sqrt_eq_rpow]
    rw [hid, hpow, norming_of_integrable_sq hsq, Real.sqrt_div hx.le]
    field_simp
    ring
  have hconstant : (Real.sqrt 2 / Real.sqrt (variance ν)) *
      ((e : ℝ) * Scalar.stableDensity 2 0) =
      (e : ℝ) * Real.sqrt (2 * (μ.toMeasure A).toReal) /
        (2 * Real.sqrt (variance (stepLaw μ)) * Real.sqrt Real.pi) := by
    have hσroot := (Real.sqrt_pos.2 hσ).ne'
    have hqroot := (Real.sqrt_pos.2 hq).ne'
    have hπroot := (Real.sqrt_pos.2 Real.pi_pos).ne'
    have hfour : Real.sqrt (4 * Real.pi) = 2 * Real.sqrt Real.pi := by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4),
        show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num, Real.sqrt_sq_eq_abs,
        abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    rw [stableDensity_two]
    simp only [gaussDensity, zero_pow (by omega : 2 ≠ 0), neg_zero, zero_div, Real.exp_zero]
    rw [hV, Real.sqrt_div hσ.le, hfour, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    field_simp
  have ht := hllt.const_mul (Real.sqrt 2 / Real.sqrt (variance ν))
  rw [hconstant] at ht
  exact ht.congr' (Eventually.of_forall fun j => (hfun j).symm)

end BGWLeaves.GeneralA.Asymptotic
