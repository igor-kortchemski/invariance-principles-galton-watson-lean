module

public import BGWLeaves.StableAnalysis.Defs
public import BGWLeaves.StableAnalysis.QuantileAnalysis

/-!
# Exact identities between the law of `Y` and the step law

`etaLaw μ` is the law of `Y = K - 1` given `K ≥ 1` and `stepLaw μ` the law of `K - 1`.  With
`q = 1 - μ 0` we prove, for any offspring law `μ`:

* `(etaLaw μ)[Y > x] = (stepLaw μ)[X > x] / q` for `x ≥ 0`;
* `K_Y(x) = (K_X(x) - μ 0) / q` for `x ≥ 1`, where `K(x) = E[W² 1_{|W| ≤ x}]`
  (`truncSecondMoment`); the atom of `X` at `-1` has mass `μ 0` and contributes `1 * μ 0`;
* `Y ≥ 0` almost surely.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal

namespace BGWLeaves.StableAnalysis.EtaTransfer

open BGW.StableTrees
open BGWLeaves.StableAnalysis

/-- The conditioning event `K ≥ 1` has real mass `1 - μ 0`. -/
theorem offspring_pos_real (μ : PMF ℕ) :
    (μ.toMeasure (Set.Ici 1)).toReal = 1 - (μ 0).toReal := by
  have hs : (Set.Ici 1 : Set ℕ) = ({0}ᶜ) := by
    ext k
    simp only [Set.mem_Ici, Set.mem_compl_iff, Set.mem_singleton_iff]
    omega
  rw [hs, prob_compl_eq_one_sub (measurableSet_singleton 0),
    PMF.toMeasure_apply_singleton μ 0 (measurableSet_singleton 0)]
  have hle : (μ 0 : ℝ≥0∞) ≤ 1 := by exact_mod_cast μ.coe_le_one 0
  rw [ENNReal.toReal_sub_of_le hle ENNReal.one_ne_top]
  simp

/-- The conditioning event `K ≥ 1` has positive probability for a critical nondegenerate law. -/
theorem offspring_pos_ne_zero {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1) :
    μ.toMeasure (Set.Ici 1) ≠ 0 := by
  obtain ⟨j, hj, hjμ⟩ := hc.exists_two_le_ne_zero hne
  have hpos : 0 < μ.toMeasure {j} := by
    rw [PMF.toMeasure_apply_singleton μ j (measurableSet_singleton j)]
    exact_mod_cast (pos_iff_ne_zero.mpr hjμ)
  have hle : μ.toMeasure {j} ≤ μ.toMeasure (Set.Ici 1) :=
    measure_mono (by
      intro k hk
      simp only [Set.mem_singleton_iff] at hk
      subst k
      exact Set.mem_Ici.mpr (by omega))
  exact (ne_of_gt (lt_of_lt_of_le hpos hle))

/-- `q = 1 - μ 0 > 0` for a critical nondegenerate law. -/
theorem one_sub_apply_zero_pos {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1) :
    0 < 1 - (μ 0).toReal := by
  rw [← offspring_pos_real]
  exact ENNReal.toReal_pos (offspring_pos_ne_zero hc hne) (measure_ne_top _ _)

/-- `etaLaw μ` is a probability measure for a critical nondegenerate law. -/
theorem isProbabilityMeasure_etaLaw {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1) :
    IsProbabilityMeasure (etaLaw μ) := by
  have : IsProbabilityMeasure (ProbabilityTheory.cond μ.toMeasure (Set.Ici 1)) :=
    cond_isProbabilityMeasure_of_finite (offspring_pos_ne_zero hc hne) (measure_ne_top _ _)
  unfold etaLaw
  infer_instance

/-- Mass of a set under `etaLaw`, in terms of the offspring law. -/
theorem etaLaw_apply (μ : PMF ℕ) (t : Set ℤ) :
    etaLaw μ t = (μ.toMeasure (Set.Ici 1))⁻¹ *
      μ.toMeasure (Set.Ici 1 ∩ (fun k : ℕ => (k : ℤ) - 1) ⁻¹' t) := by
  rw [etaLaw, Measure.map_apply (measurable_of_countable _) (MeasurableSet.of_discrete),
    ProbabilityTheory.cond_apply measurableSet_Ici]

/-- Mass of a set under `stepLaw`, in terms of the offspring law. -/
theorem stepLaw_apply (μ : PMF ℕ) (t : Set ℤ) :
    stepLaw μ t = μ.toMeasure ((fun k : ℕ => (k : ℤ) - 1) ⁻¹' t) := by
  rw [stepLaw, Measure.map_apply (measurable_of_countable _) (MeasurableSet.of_discrete)]

/-- (iii) `Y ≥ 0`: `etaLaw` gives no mass to negative integers. -/
theorem etaLaw_lt_zero (μ : PMF ℕ) : etaLaw μ {z : ℤ | z < 0} = 0 := by
  rw [etaLaw_apply]
  have : Set.Ici 1 ∩ (fun k : ℕ => (k : ℤ) - 1) ⁻¹' {z : ℤ | z < 0} = (∅ : Set ℕ) := by
    ext k
    simp only [mem_inter_iff, mem_Ici, mem_preimage, mem_ofPred_eq, mem_empty_iff_false,
      iff_false, not_and, not_lt]
    intro h
    omega
  rw [this]
  simp

/-- (iii') `etaLaw` gives no mass below `-1` (a fortiori). -/
theorem etaLaw_lt_neg_one (μ : PMF ℕ) : etaLaw μ {z : ℤ | z < -1} = 0 :=
  measure_mono_null (fun z hz => by simp only [mem_ofPred_eq] at hz ⊢; omega) (etaLaw_lt_zero μ)

/-- (i) For `x ≥ 0`: `P[Y > x] = P[X > x] / (1 - μ 0)` (tails of `etaLaw` and `stepLaw`). -/
theorem etaLaw_tail_eq (μ : PMF ℕ) {x : ℝ} (hx : 0 ≤ x) :
    (etaLaw μ).real {z : ℤ | x < (z : ℝ)} =
      (stepLaw μ).real {z : ℤ | x < (z : ℝ)} / (1 - (μ 0).toReal) := by
  have hsub : (fun k : ℕ => (k : ℤ) - 1) ⁻¹' {z : ℤ | x < (z : ℝ)} ⊆ Set.Ici 1 := by
    intro k hk
    simp only [mem_preimage, mem_ofPred_eq, Int.cast_sub, Int.cast_natCast, Int.cast_one] at hk
    simp only [mem_Ici]
    by_contra h
    have : (k : ℝ) = 0 := by exact_mod_cast (show k = 0 by omega)
    linarith
  rw [measureReal_def, measureReal_def, etaLaw_apply, stepLaw_apply, inter_eq_right.2 hsub,
    ENNReal.toReal_mul, ENNReal.toReal_inv, offspring_pos_real]
  rw [inv_mul_eq_div]

/-- (ii) For `x ≥ 1`: `K_Y(x) = (K_X(x) - μ 0) / (1 - μ 0)` for the truncated second moments of
`etaLaw` and `stepLaw`.  The atom of `X` at `-1` has mass `μ 0` and contributes `1 * μ 0`, while
`Y` has no mass at `-1`. -/
theorem etaLaw_truncSecondMoment_eq (μ : PMF ℕ) {x : ℝ} (hx : 1 ≤ x) :
    truncSecondMoment (etaLaw μ) x =
      (truncSecondMoment (stepLaw μ) x - (μ 0).toReal) / (1 - (μ 0).toReal) := by
  set B : Set ℕ := (fun k : ℕ => (k : ℤ) - 1) ⁻¹' {z : ℤ | |(z : ℝ)| ≤ x} with hB
  set h : ℕ → ℝ := fun k => (((k : ℤ) - 1 : ℤ) : ℝ) ^ 2 with hh
  have hBm : MeasurableSet B := MeasurableSet.of_discrete
  have hν : truncSecondMoment (stepLaw μ) x = ∫ k in B, h k ∂μ.toMeasure := by
    unfold truncSecondMoment
    rw [stepLaw, setIntegral_map MeasurableSet.of_discrete
      (measurable_of_countable _).aestronglyMeasurable
      (measurable_of_countable _).aemeasurable]
  have hη : truncSecondMoment (etaLaw μ) x =
      (μ.toMeasure (Set.Ici 1)).toReal⁻¹ * ∫ k in B ∩ Set.Ici 1, h k ∂μ.toMeasure := by
    unfold truncSecondMoment
    rw [etaLaw, setIntegral_map MeasurableSet.of_discrete
      (measurable_of_countable _).aestronglyMeasurable
      (measurable_of_countable _).aemeasurable, ProbabilityTheory.cond,
      Measure.restrict_smul, Measure.restrict_restrict hBm, integral_smul_measure, smul_eq_mul,
      ENNReal.toReal_inv]
  have hint : IntegrableOn h B μ.toMeasure := by
    refine Measure.integrableOn_of_bounded (M := x ^ 2) (measure_ne_top _ _)
      (measurable_of_countable _).aestronglyMeasurable ?_
    refine (ae_restrict_iff' hBm).2 (ae_of_all _ fun k hk => ?_)
    have hk' : |(((k : ℤ) - 1 : ℤ) : ℝ)| ≤ x := hk
    rw [Real.norm_eq_abs, hh]
    simp only
    rw [abs_of_nonneg (sq_nonneg _), ← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) hk' 2
  have hdiff : B \ Set.Ici 1 = {0} := by
    ext k
    rw [hB]
    simp only [Set.mem_sdiff, Set.mem_Ici, Set.mem_singleton_iff, not_le]
    constructor
    · rintro ⟨-, hk⟩
      omega
    · rintro rfl
      refine ⟨?_, by norm_num⟩
      show |((((0 : ℕ) : ℤ) - 1 : ℤ) : ℝ)| ≤ x
      simpa using hx
  have hsplit := integral_inter_add_sdiff (μ := μ.toMeasure) (f := h) (s := B)
    (t := Set.Ici 1) MeasurableSet.of_discrete hint
  rw [hdiff, integral_singleton] at hsplit
  have h0 : (μ.toMeasure.real {0}) • h 0 = (μ 0).toReal := by
    simp [hh, measureReal_def, PMF.toMeasure_apply_singleton μ 0 (measurableSet_singleton 0)]
  rw [h0] at hsplit
  rw [hη, offspring_pos_real, hν, ← hsplit, add_sub_cancel_right, inv_mul_eq_div]

end BGWLeaves.StableAnalysis.EtaTransfer
