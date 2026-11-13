module

public import BGWLeaves.LeafMass.Defs
public import BGWLeaves.LeafMass.Arithmetic
public import BGWLeaves.LeafMass.YLaw
public import BGWLeaves.StableAnalysis.CanonicalAttraction
public import BGWLeaves.StableAnalysis.StableDomainTail
public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Data.Int.ModEq

/-!
Theorem 3.1(ii), using a geometric number of excess-offspring steps between
successive leaves. Negative-binomial convolution gives the exact leaf-time walk
identity. The new increment has mean zero and span `arithFactor μ {0}`. In infinite
variance its geometric Laplace resolvent transfers the canonical attraction; in
finite variance the random-sum second moment gives `Var(ν′) = Var(ν)/μ₀` and the CLT.
The lattice LLT and successive-norming ratio then give the exact normalization.
The printed and finite-variance asymptotics are derived from that limit.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Asymptotics BGW
open BGW.StableTrees BGWLeaves.StableAnalysis
open scoped ENNReal Topology

namespace BGWLeaves.LeafMass.LeafLocalLimit

private instance walk_probability (ν : Measure ℤ) [IsProbabilityMeasure ν] (n : ℕ) :
    IsProbabilityMeasure (intWalk ν n) := by
  induction n with
  | zero => simp only [intWalk]; infer_instance
  | succ n ih => simpa only [intWalk] using
      (inferInstance : IsProbabilityMeasure ((intWalk ν n).conv ν))

/-- The sum of a geometric number of `Y` increments, before subtracting one. -/
private noncomputable def geometricWalkLaw (μ : PMF ℕ) : Measure ℤ :=
  Measure.sum fun k : ℕ => (μ 0 * (1 - μ 0) ^ k) • intWalk (etaLaw μ) k

/-- The increment between successive leaves, centered by one. -/
private noncomputable def leafTimeLaw (μ : PMF ℕ) : Measure ℤ :=
  (geometricWalkLaw μ).map (fun z : ℤ => z - 1)

private theorem geometricWalkLaw_probability {μ : PMF ℕ} (hc : IsCritical μ)
    (hne : μ 1 ≠ 1) : IsProbabilityMeasure (geometricWalkLaw μ) := by
  have := EtaTransfer.isProbabilityMeasure_etaLaw hc hne
  constructor
  simp only [geometricWalkLaw, Measure.sum_apply _ MeasurableSet.univ,
    Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric,
    ENNReal.sub_sub_cancel ENNReal.one_ne_top (μ.coe_le_one 0)]
  exact ENNReal.mul_inv_cancel (Arithmetic.mu_zero_ne_zero hc hne) (μ.apply_ne_top 0)

private theorem leafTimeLaw_probability {μ : PMF ℕ} (hc : IsCritical μ)
    (hne : μ 1 ≠ 1) : IsProbabilityMeasure (leafTimeLaw μ) := by
  have := geometricWalkLaw_probability hc hne
  unfold leafTimeLaw
  infer_instance

private theorem intWalk_nonneg (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (hν : ∀ᵐ z ∂ν, 0 ≤ z) (k : ℕ) : ∀ᵐ z ∂intWalk ν k, 0 ≤ z := by
  induction k with
  | zero => simp [intWalk]
  | succ k ih =>
    rw [intWalk, Measure.conv, ae_map_iff (by fun_prop) MeasurableSet.of_discrete]
    apply (Measure.ae_prod_iff_ae_ae MeasurableSet.of_discrete).2
    filter_upwards [ih] with x hx
    filter_upwards [hν] with y hy
    exact add_nonneg hx hy

private theorem geometricWalkLaw_nonneg {μ : PMF ℕ} (hc : IsCritical μ)
    (hne : μ 1 ≠ 1) : ∀ᵐ z ∂geometricWalkLaw μ, 0 ≤ z := by
  have := EtaTransfer.isProbabilityMeasure_etaLaw hc hne
  rw [geometricWalkLaw, Measure.ae_sum_iff]
  intro k
  apply Measure.ae_smul_measure
  apply intWalk_nonneg
  simpa only [ae_iff, not_le] using EtaTransfer.etaLaw_lt_zero μ

private theorem leafTimeLaw_lower_bound {μ : PMF ℕ} (hc : IsCritical μ)
    (hne : μ 1 ≠ 1) : leafTimeLaw μ {z : ℤ | z < -1} = 0 := by
  have ha : ∀ᵐ z ∂leafTimeLaw μ, -1 ≤ z := by
    rw [leafTimeLaw, ae_map_iff (by fun_prop) MeasurableSet.of_discrete]
    filter_upwards [geometricWalkLaw_nonneg hc hne] with z hz
    omega
  simpa only [ae_iff, not_le] using ha

private theorem intWalk_dvd (ν : Measure ℤ) [IsProbabilityMeasure ν] (d : ℕ)
    (hν : ∀ᵐ z ∂ν, (d : ℤ) ∣ z) (k : ℕ) :
    ∀ᵐ z ∂intWalk ν k, (d : ℤ) ∣ z := by
  induction k with
  | zero => simp [intWalk]
  | succ k ih =>
    rw [intWalk, Measure.conv, ae_map_iff (by fun_prop) MeasurableSet.of_discrete]
    apply (Measure.ae_prod_iff_ae_ae MeasurableSet.of_discrete).2
    filter_upwards [ih] with x hx
    filter_upwards [hν] with y hy
    exact dvd_add hx hy

private theorem leafTimeLaw_ae_dvd_iff {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (d : ℕ) (r : ℤ) :
    (∀ᵐ z ∂leafTimeLaw μ, (d : ℤ) ∣ z - r) ↔
      (d : ℤ) ∣ -1 - r ∧ ∀ᵐ z ∂etaLaw μ, (d : ℤ) ∣ z := by
  have := EtaTransfer.isProbabilityMeasure_etaLaw hc hne
  have hq := Arithmetic.mu_zero_ne_zero hc hne
  have hr : 1 - μ 0 ≠ 0 := ne_of_gt (tsub_pos_iff_lt.2
    (lt_of_le_of_ne (μ.coe_le_one 0) (Arithmetic.mu_zero_ne_one hc hne)))
  rw [leafTimeLaw, ae_map_iff (by fun_prop) MeasurableSet.of_discrete,
    geometricWalkLaw, Measure.ae_sum_iff]
  constructor
  · intro h
    have hzero := (Measure.ae_ennreal_smul_measure_iff (by simpa using hq)).1 (h 0)
    have hz : (d : ℤ) ∣ -1 - r := by simpa [intWalk] using hzero
    have hone := (Measure.ae_ennreal_smul_measure_iff (mul_ne_zero hq (pow_ne_zero 1 hr))).1 (h 1)
    have he : ∀ᵐ z ∂etaLaw μ, (d : ℤ) ∣ (z - 1) - r := by
      simpa [intWalk, Measure.dirac_conv] using hone
    refine ⟨hz, ?_⟩
    filter_upwards [he] with z hz'
    convert dvd_sub hz' hz using 1; ring
  · rintro ⟨hz, hy⟩ k
    apply Measure.ae_smul_measure
    filter_upwards [intWalk_dvd (etaLaw μ) d hy k] with z hz'
    convert dvd_add hz' hz using 1; ring

private theorem leafTimeLaw_span {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1) :
    HasSpan (leafTimeLaw μ) (arithFactor μ {0}) ∧
      ∀ᵐ z ∂leafTimeLaw μ, (arithFactor μ {0} : ℤ) ∣ z - (-1) := by
  have hg := Arithmetic.arithFactor_isGreatest_of_two_le (Arithmetic.exists_two_le hc hne)
  have hgcd := Arithmetic.arithFactor_zero_eq_setGcd hc hne
  have hy : ∀ᵐ z ∂etaLaw μ, (arithFactor μ {0} : ℤ) ∣ z := by
    have he := (YLaw.etaLaw_ae_dvd_iff hc hne (arithFactor μ {0}) 0).2 (by
      intro k hk hk0
      obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk0
      have hj : arithFactor μ {0} ∣ j := by
        rw [hgcd]
        exact Nat.setGcd_dvd_of_mem hk
      simpa using Int.natCast_dvd_natCast.2 hj)
    simpa using he
  have hs := (leafTimeLaw_ae_dvd_iff hc hne (arithFactor μ {0}) (-1)).2 ⟨by simp, hy⟩
  refine ⟨⟨?_, ⟨-1, hs⟩, ?_⟩, hs⟩
  · rw [hgcd]
    exact lt_of_lt_of_le Nat.zero_lt_one hg.1.1
  · rintro e ⟨r, hr⟩
    have he := (leafTimeLaw_ae_dvd_iff hc hne e r).1 hr
    rw [hgcd, Nat.dvd_setGcd_iff]
    have hη : ∀ᵐ z ∂etaLaw μ, (e : ℤ) ∣ z - 0 := by simpa using he.2
    intro j hj
    have hd := (YLaw.etaLaw_ae_dvd_iff hc hne e 0).1 hη (j + 1) hj (by omega)
    exact Int.natCast_dvd_natCast.1 (by simpa using hd)

private theorem walk_laplace (ν : Measure ℤ) [IsProbabilityMeasure ν] (s : ℝ) (k : ℕ) :
    (∫ z : ℤ, Real.exp (-s * (z : ℝ)) ∂intWalk ν k) =
      (∫ z : ℤ, Real.exp (-s * (z : ℝ)) ∂ν) ^ k := by
  induction k with
  | zero => simp [intWalk]
  | succ k ih =>
    rw [intWalk, Measure.conv, integral_map (by fun_prop) (by fun_prop)]
    simp_rw [Int.cast_add, mul_add, Real.exp_add]
    rw [integral_prod_mul (fun z : ℤ => Real.exp (-s * (z : ℝ)))
      (fun z : ℤ => Real.exp (-s * (z : ℝ))), ih, pow_succ]

private theorem walk_firstMoment (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (hν : Integrable (fun z : ℤ => (z : ℝ)) ν) (k : ℕ) :
    Integrable (fun z : ℤ => (z : ℝ)) (intWalk ν k) ∧
      (∫ z : ℤ, (z : ℝ) ∂intWalk ν k) = k * mean ν := by
  induction k with
  | zero =>
    constructor
    · exact integrable_dirac (by simp)
    · simp [intWalk]
  | succ k ih =>
    have hp : Integrable (fun p : ℤ × ℤ => ((p.1 + p.2 : ℤ) : ℝ))
        ((intWalk ν k).prod ν) := by
      convert (ih.1.comp_fst ν).add (hν.comp_snd (intWalk ν k)) using 1
      ext p
      simp
    constructor
    · rw [intWalk, Measure.conv]
      exact (integrable_map_measure (by fun_prop) (by fun_prop)).2 hp
    · rw [intWalk, Measure.conv, integral_map (by fun_prop) (by fun_prop)]
      simp_rw [Int.cast_add]
      rw [integral_add (ih.1.comp_fst ν) (hν.comp_snd (intWalk ν k)),
        integral_fun_fst, integral_fun_snd, ih.2]
      simp only [probReal_univ, mean]
      push_cast
      ring

private theorem geometricWalkLaw_firstMoment {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1) :
    Integrable (fun z : ℤ => (z : ℝ)) (geometricWalkLaw μ) ∧
      mean (geometricWalkLaw μ) = 1 := by
  have := EtaTransfer.isProbabilityMeasure_etaLaw hc hne
  have := geometricWalkLaw_probability hc hne
  have hy := YLaw.integrable_etaLaw hc hne
  have hq : 0 < (μ 0).toReal :=
    ENNReal.toReal_pos (Arithmetic.mu_zero_ne_zero hc hne) (μ.apply_ne_top 0)
  have hr := EtaTransfer.one_sub_apply_zero_pos hc hne
  have hrat : ‖1 - (μ 0).toReal‖ < 1 := by rw [Real.norm_eq_abs, abs_of_pos hr]; linarith
  let ρ := fun k : ℕ => (μ 0 * (1 - μ 0) ^ k) • intWalk (etaLaw μ) k
  have hi : ∀ k, Integrable (fun z : ℤ => (z : ℝ)) (ρ k) := by
    intro k
    have ht : μ 0 * (1 - μ 0) ^ k ≠ ⊤ := by
      have hμ := μ.apply_ne_top 0
      finiteness
    exact (walk_firstMoment (etaLaw μ) hy k).1.smul_measure ht
  have he : ∀ k, (∫ z : ℤ, ‖(z : ℝ)‖ ∂ρ k) =
      ((μ 0).toReal * mean (etaLaw μ)) * ((k : ℝ) * (1 - (μ 0).toReal) ^ k) := by
    intro k
    rw [show ρ k = (μ 0 * (1 - μ 0) ^ k) • intWalk (etaLaw μ) k from rfl,
      integral_smul_measure]
    have hn : (∫ z : ℤ, ‖(z : ℝ)‖ ∂intWalk (etaLaw μ) k) =
        ∫ z : ℤ, (z : ℝ) ∂intWalk (etaLaw μ) k := by
      apply integral_congr_ae
      have hn : ∀ᵐ z : ℤ ∂etaLaw μ, 0 ≤ z := by
        simpa only [ae_iff, not_le] using EtaTransfer.etaLaw_lt_zero μ
      filter_upwards [intWalk_nonneg (etaLaw μ) hn k] with z hz
      exact Real.norm_of_nonneg (by exact_mod_cast hz)
    rw [hn, (walk_firstMoment (etaLaw μ) hy k).2]
    simp only [smul_eq_mul, ENNReal.toReal_mul, ENNReal.toReal_pow,
      ENNReal.toReal_sub_of_le (μ.coe_le_one 0) ENNReal.one_ne_top, ENNReal.toReal_one]
    ring
  have hsum : HasSum (fun k => ∫ z : ℤ, ‖(z : ℝ)‖ ∂ρ k) 1 := by
    have h := (hasSum_coe_mul_geometric_of_norm_lt_one hrat).mul_left
      ((μ 0).toReal * mean (etaLaw μ))
    have hconst : ((μ 0).toReal * mean (etaLaw μ)) *
        ((1 - (μ 0).toReal) / (1 - (1 - (μ 0).toReal)) ^ 2) = 1 := by
      rw [mean_etaLaw hc hne]
      rw [show 1 - (1 - (μ 0).toReal) = (μ 0).toReal by ring]
      field_simp [hq.ne', hr.ne']
    rw [hconst] at h
    simpa only [he] using h
  have hmix : Integrable (fun z : ℤ => (z : ℝ)) (geometricWalkLaw μ) :=
    integrable_sum_measure hi hsum.summable
  refine ⟨hmix, ?_⟩
  rw [mean]
  calc
    _ = ∫ z : ℤ, ‖(z : ℝ)‖ ∂geometricWalkLaw μ := by
      apply integral_congr_ae
      filter_upwards [geometricWalkLaw_nonneg hc hne] with z hz
      exact (Real.norm_of_nonneg (by exact_mod_cast hz)).symm
    _ = ∑' k, ∫ z : ℤ, ‖(z : ℝ)‖ ∂ρ k := integral_sum_measure hmix.norm
    _ = 1 := hsum.tsum_eq

private theorem walk_secondMoment (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (hν : Integrable (fun z : ℤ => (z : ℝ)) ν)
    (hνsq : Integrable (fun z : ℤ => (z : ℝ) ^ 2) ν) (k : ℕ) :
    Integrable (fun z : ℤ => (z : ℝ) ^ 2) (intWalk ν k) ∧
      (∫ z : ℤ, (z : ℝ) ^ 2 ∂intWalk ν k) =
        (k : ℝ) * (∫ z : ℤ, (z : ℝ) ^ 2 ∂ν) +
          (k : ℝ) * ((k : ℝ) - 1) * mean ν ^ 2 := by
  induction k with
  | zero =>
    constructor
    · exact integrable_dirac (by simp)
    · simp [intWalk]
  | succ k ih =>
    have hlin := (walk_firstMoment ν hν k).1
    have hcross := (hlin.mul_prod hν).const_mul 2
    have hp : Integrable (fun p : ℤ × ℤ => ((p.1 + p.2 : ℤ) : ℝ) ^ 2)
        ((intWalk ν k).prod ν) := by
      convert ((ih.1.comp_fst ν).add hcross).add (hνsq.comp_snd (intWalk ν k)) using 1
      ext p
      simp only [Int.cast_add, Pi.add_apply]
      ring
    refine ⟨?_, ?_⟩
    · rw [intWalk, Measure.conv]
      exact (integrable_map_measure (by fun_prop) (by fun_prop)).2 hp
    · rw [intWalk, Measure.conv, integral_map (by fun_prop) (by fun_prop)]
      have he : (fun p : ℤ × ℤ => ((p.1 + p.2 : ℤ) : ℝ) ^ 2) =
          fun p => ((p.1 : ℝ) ^ 2 + 2 * ((p.1 : ℝ) * (p.2 : ℝ))) + (p.2 : ℝ) ^ 2 := by
        ext p
        push_cast
        ring
      have hleft : Integrable (fun p : ℤ × ℤ => (p.1 : ℝ) ^ 2 + 2 * ((p.1 : ℝ) * (p.2 : ℝ)))
          ((intWalk ν k).prod ν) := by
        convert (ih.1.comp_fst ν).add hcross using 1
      rw [he, integral_add hleft (hνsq.comp_snd (intWalk ν k)),
        integral_add (f := fun p : ℤ × ℤ => (p.1 : ℝ) ^ 2)
          (g := fun p : ℤ × ℤ => 2 * ((p.1 : ℝ) * (p.2 : ℝ)))
          (ih.1.comp_fst ν) hcross, integral_const_mul,
        integral_prod_mul (fun z : ℤ => (z : ℝ)) (fun z : ℤ => (z : ℝ)),
        integral_fun_fst (fun z : ℤ => (z : ℝ) ^ 2),
        integral_fun_snd (fun z : ℤ => (z : ℝ) ^ 2), ih.2, (walk_firstMoment ν hν k).2]
      simp only [probReal_univ, mean]
      push_cast
      ring

private theorem geometricWalkLaw_secondMoment {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hfin : Integrable (fun z : ℤ => (z : ℝ) ^ 2) (stepLaw μ)) :
    Integrable (fun z : ℤ => (z : ℝ) ^ 2) (geometricWalkLaw μ) ∧
      (∫ z : ℤ, (z : ℝ) ^ 2 ∂geometricWalkLaw μ) =
        (1 - (μ 0).toReal) / (μ 0).toReal * (∫ z : ℤ, (z : ℝ) ^ 2 ∂etaLaw μ) + 2 := by
  have := EtaTransfer.isProbabilityMeasure_etaLaw hc hne
  have hy := YLaw.integrable_etaLaw hc hne
  have hysq := integrable_sq_etaLaw hc hne hfin
  have hq : 0 < (μ 0).toReal :=
    ENNReal.toReal_pos (Arithmetic.mu_zero_ne_zero hc hne) (μ.apply_ne_top 0)
  have hr := EtaTransfer.one_sub_apply_zero_pos hc hne
  have hrat : ‖1 - (μ 0).toReal‖ < 1 := by rw [Real.norm_eq_abs, abs_of_pos hr]; linarith
  let A := ∫ z : ℤ, (z : ℝ) ^ 2 ∂etaLaw μ
  let M := mean (etaLaw μ)
  let ρ := fun k : ℕ => (μ 0 * (1 - μ 0) ^ k) • intWalk (etaLaw μ) k
  have hi : ∀ k, Integrable (fun z : ℤ => (z : ℝ) ^ 2) (ρ k) := by
    intro k
    have ht : μ 0 * (1 - μ 0) ^ k ≠ ⊤ := by
      have hμ := μ.apply_ne_top 0
      finiteness
    exact (walk_secondMoment (etaLaw μ) hy hysq k).1.smul_measure ht
  have he : ∀ k, (∫ z : ℤ, (z : ℝ) ^ 2 ∂ρ k) =
      ((μ 0).toReal * (A - M ^ 2)) * ((k : ℝ) * (1 - (μ 0).toReal) ^ k) +
        ((μ 0).toReal * M ^ 2) * ((k : ℝ) ^ 2 * (1 - (μ 0).toReal) ^ k) := by
    intro k
    rw [show ρ k = (μ 0 * (1 - μ 0) ^ k) • intWalk (etaLaw μ) k from rfl,
      integral_smul_measure, (walk_secondMoment (etaLaw μ) hy hysq k).2]
    simp only [smul_eq_mul, ENNReal.toReal_mul, ENNReal.toReal_pow,
      ENNReal.toReal_sub_of_le (μ.coe_le_one 0) ENNReal.one_ne_top, ENNReal.toReal_one]
    dsimp [A, M]
    ring
  have hsum := ((hasSum_coe_mul_geometric_of_norm_lt_one hrat).mul_left
    ((μ 0).toReal * (A - M ^ 2))).add
      ((hasSum_sq_mul_geometric_of_norm_lt_one hrat).mul_left ((μ 0).toReal * M ^ 2))
  have hconst : (μ 0).toReal * (A - M ^ 2) *
      ((1 - (μ 0).toReal) / (1 - (1 - (μ 0).toReal)) ^ 2) +
      (μ 0).toReal * M ^ 2 * ((1 - (μ 0).toReal) * (1 + (1 - (μ 0).toReal)) /
        (1 - (1 - (μ 0).toReal)) ^ 3) =
      (1 - (μ 0).toReal) / (μ 0).toReal * A + 2 := by
    dsimp [M]
    rw [mean_etaLaw hc hne, show 1 - (1 - (μ 0).toReal) = (μ 0).toReal by ring]
    field_simp [hq.ne', hr.ne']
    ring
  rw [hconst] at hsum
  have hsum' : HasSum (fun k => ∫ z : ℤ, (z : ℝ) ^ 2 ∂ρ k)
      ((1 - (μ 0).toReal) / (μ 0).toReal * A + 2) := by simpa only [he] using hsum
  have hnorm : ∀ k, (∫ z : ℤ, ‖(z : ℝ) ^ 2‖ ∂ρ k) = ∫ z : ℤ, (z : ℝ) ^ 2 ∂ρ k := by
    intro k
    simp only [Real.norm_of_nonneg (sq_nonneg _)]
  have hsumNorm : Summable (fun k => ∫ z : ℤ, ‖(z : ℝ) ^ 2‖ ∂ρ k) :=
    hsum'.summable.congr fun k => (hnorm k).symm
  have hm : Integrable (fun z : ℤ => (z : ℝ) ^ 2) (Measure.sum ρ) :=
    integrable_sum_measure hi hsumNorm
  exact ⟨hm, (integral_sum_measure hm).trans hsum'.tsum_eq⟩

private theorem leafTimeLaw_firstMoment {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1) :
    Integrable (fun z : ℤ => (z : ℝ)) (leafTimeLaw μ) ∧ mean (leafTimeLaw μ) = 0 := by
  have := geometricWalkLaw_probability hc hne
  obtain ⟨hi, hm⟩ := geometricWalkLaw_firstMoment hc hne
  constructor
  · rw [leafTimeLaw]
    apply (integrable_map_measure (by fun_prop) (by fun_prop)).2
    convert hi.sub (integrable_const (1 : ℝ)) using 1
    ext z
    simp
  · simpa [leafTimeLaw, hm, sub_eq_add_neg] using
      YLaw.mean_map_affine (geometricWalkLaw μ) hi 1 (-1)

private theorem stepLaw_decomposition {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1) :
    stepLaw μ = μ 0 • Measure.dirac (-1) + (1 - μ 0) • etaLaw μ := by
  have hp : μ.toMeasure (Set.Ici 1) = 1 - μ 0 := by
    have hs : (Set.Ici 1 : Set ℕ) = ({0}ᶜ) := by ext k; simp; omega
    rw [hs, prob_compl_eq_one_sub (measurableSet_singleton 0),
      PMF.toMeasure_apply_singleton μ 0 (measurableSet_singleton 0)]
  apply Measure.ext_of_singleton
  intro z
  rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
    smul_eq_mul, smul_eq_mul, EtaTransfer.stepLaw_apply, EtaTransfer.etaLaw_apply]
  by_cases hz : z = -1
  · subst z
    have hs : (fun k : ℕ => (k : ℤ) - 1) ⁻¹' ({-1} : Set ℤ) = {0} := by
      ext k
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      omega
    have he : (Set.Ici 1 : Set ℕ) ∩ {0} = ∅ := by ext k; simp
    simp [hs, he, PMF.toMeasure_apply_singleton]
  · have hs : (Set.Ici 1 : Set ℕ) ∩ (fun k : ℕ => (k : ℤ) - 1) ⁻¹' ({z} : Set ℤ) =
        (fun k : ℕ => (k : ℤ) - 1) ⁻¹' ({z} : Set ℤ) := by
      ext k
      simp only [Set.mem_inter_iff, Set.mem_Ici, Set.mem_preimage, Set.mem_singleton_iff]
      constructor
      · exact And.right
      · intro hk
        refine ⟨?_, hk⟩
        by_contra h
        have hk0 : k = 0 := by omega
        subst k
        apply hz
        simpa using hk.symm
    rw [hs, ← hp]
    have hd : Measure.dirac (-1 : ℤ) {z} = 0 := by simp [Ne.symm hz]
    rw [hd, mul_zero, zero_add]
    rw [← mul_assoc, ENNReal.mul_inv_cancel (EtaTransfer.offspring_pos_ne_zero hc hne)
      (measure_ne_top _ _), one_mul]

private theorem leafTimeLaw_secondMoment {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hfin : Integrable (fun z : ℤ => (z : ℝ) ^ 2) (stepLaw μ)) :
    Integrable (fun z : ℤ => (z : ℝ) ^ 2) (leafTimeLaw μ) ∧
      variance (leafTimeLaw μ) = variance (stepLaw μ) / (μ 0).toReal := by
  have := geometricWalkLaw_probability hc hne
  have := EtaTransfer.isProbabilityMeasure_etaLaw hc hne
  obtain ⟨hi, hm⟩ := geometricWalkLaw_firstMoment hc hne
  obtain ⟨hsq, hv⟩ := geometricWalkLaw_secondMoment hc hne hfin
  have hy := integrable_sq_etaLaw hc hne hfin
  have hshift : Integrable (fun z : ℤ => ((z : ℝ) - 1) ^ 2) (geometricWalkLaw μ) := by
    convert (hsq.sub (hi.const_mul 2)).add (integrable_const (1 : ℝ)) using 1
    ext z
    simp only [Pi.add_apply, Pi.sub_apply]
    ring
  have hshiftVal : (∫ z : ℤ, ((z : ℝ) - 1) ^ 2 ∂geometricWalkLaw μ) =
      (∫ z : ℤ, (z : ℝ) ^ 2 ∂geometricWalkLaw μ) - 1 := by
    have he : (fun z : ℤ => ((z : ℝ) - 1) ^ 2) =
        fun z : ℤ => (z : ℝ) ^ 2 - 2 * (z : ℝ) + 1 := by ext z; ring
    have hleft : Integrable (fun z : ℤ => (z : ℝ) ^ 2 - 2 * (z : ℝ)) (geometricWalkLaw μ) := by
      convert hsq.sub (hi.const_mul 2) using 1
    rw [he, integral_add hleft (integrable_const (1 : ℝ)),
      integral_sub (f := fun z : ℤ => (z : ℝ) ^ 2) (g := fun z : ℤ => 2 * (z : ℝ))
        hsq (hi.const_mul 2), integral_const_mul]
    change (∫ z : ℤ, (z : ℝ) ^ 2 ∂geometricWalkLaw μ) - 2 * mean (geometricWalkLaw μ) + _ = _
    simp [hm]
    ring
  have hraw : variance (stepLaw μ) = (μ 0).toReal + (1 - (μ 0).toReal) *
      (∫ z : ℤ, (z : ℝ) ^ 2 ∂etaLaw μ) := by
    rw [BGWLeaves.StableAnalysis.variance, mean_stepLaw hc]
    simp only [sub_zero]
    have hd : Integrable (fun z : ℤ => (z : ℝ) ^ 2) (Measure.dirac (-1)) := integrable_dirac (by simp)
    have hq := μ.apply_ne_top 0
    have hr : 1 - μ 0 ≠ ⊤ := by finiteness
    rw [stepLaw_decomposition hc hne,
      integral_add_measure (hd.smul_measure hq) (hy.smul_measure hr)]
    simp [integral_smul_measure, ENNReal.toReal_sub_of_le (μ.coe_le_one 0) ENNReal.one_ne_top]
  refine ⟨?_, ?_⟩
  · rw [leafTimeLaw]
    apply (integrable_map_measure (by fun_prop) (by fun_prop)).2
    convert hshift using 1
    ext z
    simp
  · rw [BGWLeaves.StableAnalysis.variance, (leafTimeLaw_firstMoment hc hne).2]
    simp only [sub_zero]
    rw [leafTimeLaw, integral_map (by fun_prop) (by fun_prop)]
    simp only [Int.cast_sub, Int.cast_one]
    rw [hshiftVal, hv, hraw]
    have hq : (μ 0).toReal ≠ 0 :=
      (ENNReal.toReal_pos (Arithmetic.mu_zero_ne_zero hc hne) (μ.apply_ne_top 0)).ne'
    field_simp
    ring

private theorem stepLaw_laplace_split {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    {s : ℝ} (hs : 0 ≤ s) :
    (∫ z : ℤ, Real.exp (-s * (z : ℝ)) ∂stepLaw μ) =
      (μ 0).toReal * Real.exp s + (1 - (μ 0).toReal) *
        (∫ z : ℤ, Real.exp (-s * (z : ℝ)) ∂etaLaw μ) := by
  have := EtaTransfer.isProbabilityMeasure_etaLaw hc hne
  have hi : Integrable (fun z : ℤ => Real.exp (-s * (z : ℝ))) (etaLaw μ) :=
    LaplaceExpansion.uncenteredLaplace_integrable (EtaTransfer.etaLaw_lt_neg_one μ) hs
  have hq := μ.apply_ne_top 0
  have hr : 1 - μ 0 ≠ ⊤ := by finiteness
  have hd : Integrable (fun z : ℤ => Real.exp (-s * (z : ℝ))) (Measure.dirac (-1)) :=
    integrable_dirac (by simp)
  rw [stepLaw_decomposition hc hne, integral_add_measure (hd.smul_measure hq) (hi.smul_measure hr)]
  simp [integral_smul_measure, ENNReal.toReal_sub_of_le (μ.coe_le_one 0) ENNReal.one_ne_top]

private theorem geometricWalkLaw_laplace {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    {s : ℝ} (hs : 0 ≤ s) :
    (∫ z : ℤ, Real.exp (-s * (z : ℝ)) ∂geometricWalkLaw μ) =
      (μ 0).toReal / (1 - (1 - (μ 0).toReal) *
        (∫ z : ℤ, Real.exp (-s * (z : ℝ)) ∂etaLaw μ)) := by
  have := EtaTransfer.isProbabilityMeasure_etaLaw hc hne
  have := geometricWalkLaw_probability hc hne
  let L := ∫ z : ℤ, Real.exp (-s * (z : ℝ)) ∂etaLaw μ
  have hL0 : 0 ≤ L := integral_nonneg fun _ => Real.exp_nonneg _
  have hb : ∀ᵐ z : ℤ ∂etaLaw μ, Real.exp (-s * (z : ℝ)) ≤ 1 := by
    have hn : ∀ᵐ z ∂etaLaw μ, 0 ≤ z := by
      simpa only [ae_iff, not_le] using EtaTransfer.etaLaw_lt_zero μ
    filter_upwards [hn] with z hz
    apply Real.exp_le_one_iff.mpr
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hs)
      (show (0 : ℝ) ≤ (z : ℝ) by exact_mod_cast hz)
  have hi : Integrable (fun z : ℤ => Real.exp (-s * (z : ℝ))) (etaLaw μ) := by
    apply Integrable.of_bound (by fun_prop) 1
    simpa only [Real.norm_of_nonneg (Real.exp_nonneg _)] using hb
  have hL1 : L ≤ 1 := by
    simpa [L] using integral_mono_ae hi (integrable_const (1 : ℝ)) hb
  have hq0 : 0 < (μ 0).toReal :=
    ENNReal.toReal_pos (Arithmetic.mu_zero_ne_zero hc hne) (μ.apply_ne_top 0)
  have hr0 : 0 ≤ 1 - (μ 0).toReal := sub_nonneg.mpr (by simpa using ENNReal.toReal_mono ENNReal.one_ne_top (μ.coe_le_one 0))
  have hr1 : 1 - (μ 0).toReal < 1 := by linarith
  have hratio0 : 0 ≤ (1 - (μ 0).toReal) * L := mul_nonneg hr0 hL0
  have hratio1 : (1 - (μ 0).toReal) * L < 1 :=
    lt_of_le_of_lt (mul_le_of_le_one_right hr0 hL1) hr1
  have hgeo := (hasSum_geometric_of_lt_one hratio0 hratio1).mul_left (μ 0).toReal
  have hmix : Integrable (fun z : ℤ => Real.exp (-s * (z : ℝ))) (geometricWalkLaw μ) := by
    apply Integrable.of_bound (by fun_prop) 1
    filter_upwards [geometricWalkLaw_nonneg hc hne] with z hz
    rw [Real.norm_of_nonneg (Real.exp_nonneg _)]
    apply Real.exp_le_one_iff.mpr
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hs)
      (show (0 : ℝ) ≤ (z : ℝ) by exact_mod_cast hz)
  rw [geometricWalkLaw, integral_sum_measure hmix]
  simp only [integral_smul_measure, smul_eq_mul, ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_sub_of_le (μ.coe_le_one 0) ENNReal.one_ne_top, ENNReal.toReal_one,
    walk_laplace]
  simpa only [L, mul_pow, mul_assoc, div_eq_mul_inv] using hgeo.tsum_eq

private theorem leafTimeLaw_laplace {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    {s : ℝ} (hs : 0 ≤ s) :
    (∫ z : ℤ, Real.exp (-s * (z : ℝ)) ∂leafTimeLaw μ) =
      Real.exp s * ((μ 0).toReal / (1 - (1 - (μ 0).toReal) *
        (∫ z : ℤ, Real.exp (-s * (z : ℝ)) ∂etaLaw μ))) := by
  rw [leafTimeLaw, integral_map (by fun_prop) (by fun_prop)]
  have he : (fun z : ℤ => Real.exp (-s * ((z - 1 : ℤ) : ℝ))) =
      fun z : ℤ => Real.exp s * Real.exp (-s * (z : ℝ)) := by
    funext z
    rw [← Real.exp_add]
    congr 1
    push_cast
    ring
  rw [he, integral_const_mul, geometricWalkLaw_laplace hc hne hs]

private theorem leafTimeLaw_laplace_resolvent {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    {s : ℝ} (hs : 0 ≤ s) :
    (∫ z : ℤ, Real.exp (-s * (z : ℝ)) ∂leafTimeLaw μ) =
      Real.exp s * (μ 0).toReal /
        ((μ 0).toReal * Real.exp s + 1 -
          (∫ z : ℤ, Real.exp (-s * (z : ℝ)) ∂stepLaw μ)) := by
  rw [leafTimeLaw_laplace hc hne hs, stepLaw_laplace_split hc hne hs]
  rw [show (μ 0).toReal * Real.exp s + 1 -
      ((μ 0).toReal * Real.exp s + (1 - (μ 0).toReal) *
        (∫ z : ℤ, Real.exp (-s * (z : ℝ)) ∂etaLaw μ)) =
      1 - (1 - (μ 0).toReal) * (∫ z : ℤ, Real.exp (-s * (z : ℝ)) ∂etaLaw μ) by ring]
  ring

/-- The algebraic transfer of a scaled Laplace remainder through the geometric
resolvent. The factor `1/q` is exact; a time change supplies the compensating `q`. -/
private theorem resolvent_remainder_limit {q C : ℝ} (hq : q ≠ 0)
    {s L : ℕ → ℝ} (hs : Tendsto s atTop (𝓝 0)) (hL : Tendsto L atTop (𝓝 1))
    (hscale : Tendsto (fun n : ℕ => (n : ℝ) * (L n - 1)) atTop (𝓝 C)) :
    Tendsto (fun n : ℕ => (n : ℝ) *
      (Real.exp (s n) * q / (q * Real.exp (s n) + 1 - L n) - 1))
      atTop (𝓝 (C / q)) := by
  have he := Real.continuous_exp.continuousAt.tendsto.comp hs
  simp only [Real.exp_zero] at he
  have hd : Tendsto (fun n => q * Real.exp (s n) + 1 - L n) atTop (𝓝 q) := by
    simpa only [Function.comp_apply, mul_one, add_sub_cancel_right] using ((he.const_mul q).add_const 1).sub hL
  refine (hscale.div hd hq).congr' ?_
  filter_upwards [hd.eventually_ne hq] with n hn
  change (n : ℝ) * (L n - 1) / (q * Real.exp (s n) + 1 - L n) = _
  field_simp
  ring

/-- Attraction of the leaf-time increment from a scaled one-step expansion of the
original offspring increment. We apply this interface to the equivalent norming
`Bₙ / q^(1/θ)`, avoiding a floor-time change. -/
private theorem leafTimeLaw_attracted_of_expansion {μ : PMF ℕ} (hc : IsCritical μ)
    (hne : μ 1 ≠ 1) {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {b : ℕ → ℝ}
    (hb : ∀ᶠ n in atTop, 0 < b n) (hbtop : Tendsto b atTop atTop)
    (hL : ∀ lam : ℝ, 0 < lam →
      Tendsto (fun n : ℕ => (n : ℝ) *
        ((∫ z : ℤ, Real.exp (-(lam / b n) * (z : ℝ)) ∂stepLaw μ) - 1))
          atTop (𝓝 ((μ 0).toReal * lam ^ θ))) :
    IsStableAttracted (leafTimeLaw μ) θ 0 b := by
  have := leafTimeLaw_probability hc hne
  obtain ⟨hi, hm⟩ := leafTimeLaw_firstMoment hc hne
  rw [← hm]
  apply CanonicalAttraction.isStableAttracted_of_centered_one_step_limit hθ
    (leafTimeLaw_lower_bound hc hne) hi hb
  intro lam hlam
  have hq : (μ 0).toReal ≠ 0 :=
    (ENNReal.toReal_pos (Arithmetic.mu_zero_ne_zero hc hne) (μ.apply_ne_top 0)).ne'
  have hs : Tendsto (fun n => lam / b n) atTop (𝓝 0) := tendsto_const_nhds.div_atTop hbtop
  let L := fun n => ∫ z : ℤ, Real.exp (-(lam / b n) * (z : ℝ)) ∂stepLaw μ
  have hdev : Tendsto (fun n => L n - 1) atTop (𝓝 0) := by
    have hd := (hL lam hlam).div_atTop tendsto_natCast_atTop_atTop
    refine hd.congr' ?_
    filter_upwards [eventually_ne_atTop 0] with n hn
    dsimp [L]
    have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    field_simp
  have hL1 : Tendsto L atTop (𝓝 1) := by
    simpa only [sub_add_cancel, zero_add] using hdev.add_const 1
  have ht := resolvent_remainder_limit hq hs hL1 (hL lam hlam)
  rw [mul_div_cancel_left₀ _ hq] at ht
  refine ht.congr' ?_
  filter_upwards [hb] with n hn
  rw [LaplaceExpansion.centeredLaplace_eq, hm, mul_zero, Real.exp_zero, one_mul,
    leafTimeLaw_laplace_resolvent hc hne (le_of_lt (div_pos hlam hn))]

private theorem stepLaw_laplace_expansion_infinite {μ : PMF ℕ} {θ : ℝ}
    (hc : IsCritical μ) (hDA : ∃ a, StableDomain μ θ a)
    (hinf : ¬ Integrable (fun z : ℤ => (z : ℝ) ^ 2) (stepLaw μ))
    {lam : ℝ} (hlam : 0 < lam) :
    Tendsto (fun n : ℕ => (n : ℝ) *
      ((∫ z : ℤ, Real.exp (-(lam / norming (stepLaw μ) θ n) * (z : ℝ)) ∂stepLaw μ) - 1))
        atTop (𝓝 (lam ^ θ)) := by
  have := isProbabilityMeasure_stepLaw μ
  obtain ⟨a, ha⟩ := hDA
  have hattr : IsStableAttracted (stepLaw μ) θ (mean (stepLaw μ)) a := by
    rw [mean_stepLaw hc]
    exact stableDomain_isStableAttracted ha
  have ht : Tendsto (fun n : ℕ => (n : ℝ) *
      (LaplaceExpansion.centeredLaplace (stepLaw μ) (lam / norming (stepLaw μ) θ n) - 1))
        atTop (𝓝 (lam ^ θ)) := by
    rcases lt_or_eq_of_le hattr.alpha_mem.2 with hlt | heq
    · exact LaplaceExpansion.norming_centeredLaplace_limit (stepLaw_lt_neg_one μ)
        (integrable_stepLaw hc) hattr.alpha_mem.1 hlt
        (DomainCriterion.rightTail_regularlyVarying hattr (stepLaw_lt_neg_one μ)
          (integrable_stepLaw hc) hinf hlt) hlam
    · subst θ
      obtain ⟨hK, hKinf⟩ := DomainCriterion.truncSecondMoment_slowlyVarying_unbounded
        hattr (integrable_stepLaw hc) hinf
      exact CanonicalAttraction.gaussian_norming_centeredLaplace_limit (stepLaw_lt_neg_one μ)
        (integrable_stepLaw hc) hK hKinf hlam
  simpa only [LaplaceExpansion.centeredLaplace_eq, mean_stepLaw hc, mul_zero,
    Real.exp_zero, one_mul] using ht

private theorem walk_add (ν : Measure ℤ) [IsProbabilityMeasure ν] (i j : ℕ) :
    intWalk ν (i + j) = (intWalk ν i).conv (intWalk ν j) := by
  induction j with
  | zero => simp [intWalk, Measure.conv_dirac]
  | succ j ih =>
    rw [Nat.add_succ, intWalk, ih, Measure.conv_assoc]
    rfl

private theorem mixed_walk_conv (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (u v : ℕ → ℝ≥0∞) :
    (Measure.sum fun i => u i • intWalk ν i).conv
        (Measure.sum fun j => v j • intWalk ν j) =
      Measure.sum fun p : ℕ × ℕ => (u p.1 * v p.2) • intWalk ν (p.1 + p.2) := by
  rw [Measure.conv, Measure.prod_sum, Measure.map_sum (by fun_prop)]
  congr 1
  funext p
  change (u p.1 • intWalk ν p.1).conv (v p.2 • intWalk ν p.2) = _
  rw [Measure.conv_smul_left, Measure.conv_smul_right, smul_smul, walk_add]

private theorem sum_pairs_by_add (f : ℕ × ℕ → Measure ℤ) :
    Measure.sum f = Measure.sum fun k : ℕ => ∑ p ∈ Finset.antidiagonal k, f p := by
  classical
  ext s hs
  simp only [Measure.sum_apply _ hs, Measure.finsetSum_apply]
  rw [← Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd.tsum_eq (fun p => f p s),
    ENNReal.tsum_sigma']
  apply tsum_congr
  intro k
  simp only [Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd, tsum_fintype]
  exact Finset.sum_attach _ (fun p => f p s)

private noncomputable def nbWeight (μ : PMF ℕ) (n k : ℕ) : ℝ≥0∞ :=
  ((k + n).choose n : ℝ≥0∞) * μ 0 ^ (n + 1) * (1 - μ 0) ^ k

private theorem nbWeight_succ (μ : PMF ℕ) (n k : ℕ) :
    ∑ p ∈ Finset.antidiagonal k, nbWeight μ n p.1 * (μ 0 * (1 - μ 0) ^ p.2) =
      nbWeight μ (n + 1) k := by
  classical
  have ht : ∀ p ∈ Finset.antidiagonal k,
      nbWeight μ n p.1 * (μ 0 * (1 - μ 0) ^ p.2) =
        ((p.1 + n).choose n : ℝ≥0∞) * (μ 0 ^ (n + 2) * (1 - μ 0) ^ k) := by
    intro p hp
    have hp' := Finset.mem_antidiagonal.mp hp
    simp only [nbWeight]
    rw [show n + 2 = (n + 1) + 1 by omega, pow_succ, ← hp', pow_add]
    ring
  rw [Finset.sum_congr rfl ht, ← Finset.sum_mul]
  have hc : (∑ p ∈ Finset.antidiagonal k, (p.1 + n).choose n) =
      (k + n + 1).choose (n + 1) := by
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    exact Nat.sum_range_add_choose k n
  have hcast : (∑ p ∈ Finset.antidiagonal k, ((p.1 + n).choose n : ℝ≥0∞)) =
      ((k + n + 1).choose (n + 1) : ℝ≥0∞) := by exact_mod_cast hc
  rw [hcast]
  simp only [nbWeight, Nat.add_assoc]
  ring

/-- Convolution powers of the geometric mixture have negative-binomial weights. -/
private theorem geometricWalkLaw_walk {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (n : ℕ) :
    intWalk (geometricWalkLaw μ) (n + 1) =
      Measure.sum fun k : ℕ => nbWeight μ n k • intWalk (etaLaw μ) k := by
  have := EtaTransfer.isProbabilityMeasure_etaLaw hc hne
  have := geometricWalkLaw_probability hc hne
  induction n with
  | zero => simp [intWalk, geometricWalkLaw, nbWeight, Measure.dirac_conv]
  | succ n ih =>
    rw [intWalk, ih, geometricWalkLaw, mixed_walk_conv, sum_pairs_by_add]
    congr 1
    funext k
    have he : ∀ p ∈ Finset.antidiagonal k,
        (nbWeight μ n p.1 * (μ 0 * (1 - μ 0) ^ p.2)) • intWalk (etaLaw μ) (p.1 + p.2) =
          (nbWeight μ n p.1 * (μ 0 * (1 - μ 0) ^ p.2)) • intWalk (etaLaw μ) k := by
      intro p hp
      rw [Finset.mem_antidiagonal.mp hp]
    rw [Finset.sum_congr rfl he, ← Finset.sum_smul, nbWeight_succ]

/-- Remove the identically zero terms with fewer vertices than leaves. -/
private theorem leafProb_series_shifted {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (n : ℕ) :
    leafProb μ (n + 1) =
      ∑' k : ℕ, (1 / ((k + n + 1 : ℕ) : ℝ)) *
        (((k + n + 1).choose (n + 1) : ℝ) * (μ 0).toReal ^ (n + 1) *
          (1 - (μ 0).toReal) ^ k) * intWalkProb (etaLaw μ) k n := by
  rw [Arithmetic.leafProb_series hc hne (by omega : 1 ≤ n + 1)]
  let f : ℕ → ℝ := fun p => (1 / (p : ℝ)) *
    ((p.choose (n + 1) : ℝ) * (μ 0).toReal ^ (n + 1) *
      (1 - (μ 0).toReal) ^ (p - (n + 1))) *
        intWalkProb (etaLaw μ) (p - (n + 1)) (((n + 1 : ℕ) : ℤ) - 1)
  have hs : Function.support f ⊆ Set.range (fun k : ℕ => k + (n + 1)) := by
    intro p hp
    have hle : n + 1 ≤ p := by
      by_contra h
      have hz := Nat.choose_eq_zero_of_lt (by omega : p < n + 1)
      exact hp (by simp [f, hz])
    exact ⟨p - (n + 1), Nat.sub_add_cancel hle⟩
  have he := (show Function.Injective (fun k : ℕ => k + (n + 1)) from
    fun _ _ h => Nat.add_right_cancel h).tsum_eq hs
  change (∑' p, f p) = _
  rw [← he]
  apply tsum_congr
  intro k
  simp [f, Nat.add_assoc]

/-- The binomial weight becomes a negative binomial weight after the shift. -/
private theorem choose_weight (n k : ℕ) :
    (1 / ((k + n + 1 : ℕ) : ℝ)) * ((k + n + 1).choose (n + 1) : ℝ) =
      (1 / ((n + 1 : ℕ) : ℝ)) * ((k + n).choose n : ℝ) := by
  have h := Nat.add_one_mul_choose_eq (k + n) n
  have hr : ((k + n + 1 : ℕ) : ℝ) * ((k + n).choose n : ℝ) =
      ((k + n + 1).choose (n + 1) : ℝ) * ((n + 1 : ℕ) : ℝ) := by
    exact_mod_cast h
  have hn : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hk : ((k + n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp
  nlinarith [hr]

/-- Exact random-sum form: the coefficient is the negative binomial mass for
the number of non-leaf steps before the `(n+1)`-st leaf step. -/
private theorem leafProb_negativeBinomial_series {μ : PMF ℕ} (hc : IsCritical μ)
    (hne : μ 1 ≠ 1) (n : ℕ) :
    leafProb μ (n + 1) =
      (1 / ((n + 1 : ℕ) : ℝ)) *
        ∑' k : ℕ, ((k + n).choose n : ℝ) * (μ 0).toReal ^ (n + 1) *
          (1 - (μ 0).toReal) ^ k * intWalkProb (etaLaw μ) k n := by
  rw [leafProb_series_shifted hc hne n, ← tsum_mul_left]
  apply tsum_congr
  intro k
  calc
    _ = ((1 / ((k + n + 1 : ℕ) : ℝ)) * ((k + n + 1).choose (n + 1) : ℝ)) *
        ((μ 0).toReal ^ (n + 1) * (1 - (μ 0).toReal) ^ k *
          intWalkProb (etaLaw μ) k n) := by ring
    _ = _ := by rw [choose_weight]; ring

/-- The exact leaf-time walk identity, with the same `n+1` indexing as the target. -/
private theorem leafProb_leafTimeLaw {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (n : ℕ) :
    leafProb μ (n + 1) =
      (1 / ((n + 1 : ℕ) : ℝ)) * intWalkProb (leafTimeLaw μ) (n + 1) (-1) := by
  have := geometricWalkLaw_probability hc hne
  have := EtaTransfer.isProbabilityMeasure_etaLaw hc hne
  have hm : intWalk (leafTimeLaw μ) (n + 1) =
      (intWalk (geometricWalkLaw μ) (n + 1)).map (fun z : ℤ => z - (n + 1)) := by
    simpa only [one_mul, mul_neg_one, sub_eq_add_neg, leafTimeLaw, Nat.cast_add,
      Nat.cast_one] using
      YLaw.intWalk_map_affine (geometricWalkLaw μ) 1 (-1) (n + 1)
  have hs : (fun z : ℤ => z - (n + 1)) ⁻¹' ({-1} : Set ℤ) = {(n : ℤ)} := by
    ext z
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    omega
  rw [leafProb_negativeBinomial_series hc hne n]
  congr 1
  rw [intWalkProb, Measure.real, hm, Measure.map_apply (by fun_prop)
    (measurableSet_singleton _), hs, geometricWalkLaw_walk hc hne n,
    Measure.sum_apply _ (measurableSet_singleton _)]
  rw [ENNReal.tsum_toReal_eq]
  · apply tsum_congr
    intro k
    simp only [nbWeight, Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul,
      ENNReal.toReal_pow, ENNReal.toReal_natCast,
      ENNReal.toReal_sub_of_le (μ.coe_le_one 0) ENNReal.one_ne_top,
      ENNReal.toReal_one, intWalkProb, Measure.real]
  · intro k
    apply ENNReal.mul_ne_top
    · have hμ := μ.apply_ne_top 0
      unfold nbWeight
      finiteness
    · exact measure_ne_top _ _

/-- The lattice LLT completes the leaf asymptotic once attraction of the
leaf-time law with a monotone divergent norming is available. -/
private theorem leafProb_limit_of_leafTime_attraction {μ : PMF ℕ} (hc : IsCritical μ)
    (hne : μ 1 ≠ 1) {θ : ℝ} {b : ℕ → ℝ} (hmono : Monotone b)
    (hbtop : Tendsto b atTop atTop) (hattr : IsStableAttracted (leafTimeLaw μ) θ 0 b) :
    Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ) * b (n + 1) * leafProb μ (n + 1))
      (atTop ⊓ 𝓟 {n : ℕ | arithFactor μ {0} ∣ n})
      (𝓝 ((arithFactor μ {0} : ℝ) * Scalar.stableDensity θ 0)) := by
  have := leafTimeLaw_probability hc hne
  obtain ⟨hi, hm⟩ := leafTimeLaw_firstMoment hc hne
  obtain ⟨hspan, hsupp⟩ := leafTimeLaw_span hc hne
  let F : Filter ℕ := atTop ⊓ 𝓟 {n : ℕ | arithFactor μ {0} ∣ n}
  have hn : Tendsto (fun n : ℕ => n + 1) F atTop :=
    (tendsto_add_atTop_nat 1).mono_left inf_le_left
  have hdvd : ∀ᶠ n in F, arithFactor μ {0} ∣ n :=
    (show ∀ᶠ n in 𝓟 {n : ℕ | arithFactor μ {0} ∣ n}, arithFactor μ {0} ∣ n from
      eventually_principal.mpr fun _ h => h).filter_mono inf_le_right
  have herr : Tendsto (fun n : ℕ => b (n + 1) * intWalkProb (leafTimeLaw μ) (n + 1) (-1) -
      (arithFactor μ {0} : ℝ) * Scalar.stableDensity θ ((-1 : ℝ) / b (n + 1))) F (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨N, hN⟩ := YLaw.llt_lattice_abstract (leafTimeLaw μ) hi hspan (-1) hsupp
      hmono (hm ▸ hattr) (half_pos hε)
    filter_upwards [hn.eventually (eventually_ge_atTop N), hdvd] with n hnN hnd
    have hmod : (arithFactor μ {0} : ℤ) ∣ (-1 : ℤ) - (n + 1 : ℕ) * (-1) := by
      convert Int.natCast_dvd_natCast.2 hnd using 1; push_cast; ring
    have he := hN (n + 1) hnN (-1)
    simp only [hm, mul_zero, sub_zero, ite_eq_left hmod, Int.cast_neg, Int.cast_one] at he
    rw [Real.dist_eq, sub_zero]
    exact lt_of_le_of_lt he (half_lt_self hε)
  have harg : Tendsto (fun n : ℕ => (-1 : ℝ) / b (n + 1)) F (𝓝 0) :=
    tendsto_const_nhds.div_atTop (hbtop.comp hn)
  have hp := ((Scalar.continuous_stableDensity hattr.alpha_mem).continuousAt.tendsto.comp harg).const_mul
    (arithFactor μ {0} : ℝ)
  have ht := herr.add hp
  simp only [sub_add_cancel, zero_add, Function.comp_apply] at ht
  refine ht.congr' (Eventually.of_forall fun n => ?_)
  change b (n + 1) * intWalkProb (leafTimeLaw μ) (n + 1) (-1) =
    ((n + 1 : ℕ) : ℝ) * b (n + 1) * leafProb μ (n + 1)
  rw [leafProb_leafTimeLaw hc hne n]
  have hnR : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp

/-- Assembly of the leaf-time proof from the original one-step Laplace expansion.
The expansion is an analytic input about `stepLaw`, not about leaf probabilities. -/
private theorem ltn_ii_tendsto_of_rescaled_attraction {μ : PMF ℕ} {θ : ℝ}
    (hc : IsCritical μ) (hne : μ 1 ≠ 1) (hDA : ∃ a, StableDomain μ θ a)
    (hbattr : IsStableAttracted (leafTimeLaw μ) θ 0
      (fun n => norming (stepLaw μ) θ n / (μ 0).toReal ^ (1 / θ))) :
    Tendsto (fun n : ℕ => (n : ℝ) * norming (stepLaw μ) θ n * leafProb μ (n + 1))
      (atTop ⊓ 𝓟 {n : ℕ | arithFactor μ {0} ∣ n})
      (𝓝 ((μ 0).toReal ^ (1 / θ) * Scalar.stableDensity θ 0 * (arithFactor μ {0} : ℝ))) := by
  have := isProbabilityMeasure_stepLaw μ
  obtain ⟨a, ha⟩ := hDA
  have ha' : IsStableAttracted (stepLaw μ) θ (mean (stepLaw μ)) a := by
    rw [mean_stepLaw hc]
    exact stableDomain_isStableAttracted ha
  have hcan := locallimit_i (stepLaw μ) (stepLaw_lt_neg_one μ) (integrable_stepLaw hc) ⟨a, ha'⟩
  have hmon := (locallimit_ii (stepLaw μ) (stepLaw_lt_neg_one μ)
    (integrable_stepLaw hc) ⟨a, ha'⟩).1
  have hBtop := TransformConvergence.tendsto_atTop (stepLaw μ) hcan
  let c := (μ 0).toReal ^ (1 / θ)
  have hq : 0 < (μ 0).toReal :=
    ENNReal.toReal_pos (Arithmetic.mu_zero_ne_zero hc hne) (μ.apply_ne_top 0)
  have hcpos : 0 < c := Real.rpow_pos_of_pos hq _
  have hθne : θ ≠ 0 := by linarith [ha'.alpha_mem.1]
  have hcPow : c ^ θ = (μ 0).toReal := by
    dsimp [c]
    rw [← Real.rpow_mul hq.le, one_div_mul_cancel hθne, Real.rpow_one]
  let b := fun n => norming (stepLaw μ) θ n / c
  have hbtop : Tendsto b atTop atTop := hBtop.atTop_div_const hcpos
  have hb : ∀ᶠ n in atTop, 0 < b n := hbtop.eventually_gt_atTop 0
  have hbm : Monotone b := fun i j hij => div_le_div_of_nonneg_right (hmon hij) hcpos.le
  have ht := leafProb_limit_of_leafTime_attraction hc hne hbm hbtop hbattr
  have hnr : Tendsto (fun n : ℕ => (n : ℝ) / ((n + 1 : ℕ) : ℝ)) atTop (𝓝 1) := by
    simpa only [Nat.cast_add, Nat.cast_one] using (tendsto_natCast_div_add_atTop (1 : ℝ))
  have hBr := (TransformConvergence.tendsto_succ_div (stepLaw μ) hcan).inv₀ one_ne_zero
  simp only [inv_one, inv_div] at hBr
  have hcoef : Tendsto (fun n : ℕ => (n : ℝ) / ((n + 1 : ℕ) : ℝ) *
      (norming (stepLaw μ) θ n / norming (stepLaw μ) θ (n + 1)) * c) atTop (𝓝 c) := by
    simpa only [one_mul] using (hnr.mul hBr).mul_const c
  have hl := (hcoef.mono_left inf_le_left).mul ht
  have he : c * ((arithFactor μ {0} : ℝ) * Scalar.stableDensity θ 0) =
      (μ 0).toReal ^ (1 / θ) * Scalar.stableDensity θ 0 * (arithFactor μ {0} : ℝ) := by
    dsimp [c]
    ring
  rw [he] at hl
  refine hl.congr' ?_
  filter_upwards [(hBtop.eventually_gt_atTop 0).filter_mono inf_le_left] with n hn
  have hBn : norming (stepLaw μ) θ (n + 1) ≠ 0 :=
    (lt_of_lt_of_le hn (hmon (Nat.le_succ n))).ne'
  change (n : ℝ) / ((n + 1 : ℕ) : ℝ) *
    (norming (stepLaw μ) θ n / norming (stepLaw μ) θ (n + 1)) * c *
      (((n + 1 : ℕ) : ℝ) * (norming (stepLaw μ) θ (n + 1) / c) * leafProb μ (n + 1)) = _
  have hnR : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp

private theorem ltn_ii_tendsto_of_laplace_expansion {μ : PMF ℕ} {θ : ℝ}
    (hc : IsCritical μ) (hne : μ 1 ≠ 1) (hDA : ∃ a, StableDomain μ θ a)
    (hExp : ∀ lam : ℝ, 0 < lam →
      Tendsto (fun n : ℕ => (n : ℝ) *
        ((∫ z : ℤ, Real.exp (-(lam / norming (stepLaw μ) θ n) * (z : ℝ)) ∂stepLaw μ) - 1))
          atTop (𝓝 (lam ^ θ))) :
    Tendsto (fun n : ℕ => (n : ℝ) * norming (stepLaw μ) θ n * leafProb μ (n + 1))
      (atTop ⊓ 𝓟 {n : ℕ | arithFactor μ {0} ∣ n})
      (𝓝 ((μ 0).toReal ^ (1 / θ) * Scalar.stableDensity θ 0 * (arithFactor μ {0} : ℝ))) := by
  apply ltn_ii_tendsto_of_rescaled_attraction hc hne hDA

  have := isProbabilityMeasure_stepLaw μ
  obtain ⟨a, ha⟩ := hDA
  have ha' : IsStableAttracted (stepLaw μ) θ (mean (stepLaw μ)) a := by
    rw [mean_stepLaw hc]
    exact stableDomain_isStableAttracted ha
  have hcan := locallimit_i (stepLaw μ) (stepLaw_lt_neg_one μ) (integrable_stepLaw hc) ⟨a, ha'⟩
  have hmon := (locallimit_ii (stepLaw μ) (stepLaw_lt_neg_one μ)
    (integrable_stepLaw hc) ⟨a, ha'⟩).1
  have hBtop := TransformConvergence.tendsto_atTop (stepLaw μ) hcan
  let c := (μ 0).toReal ^ (1 / θ)
  have hq : 0 < (μ 0).toReal :=
    ENNReal.toReal_pos (Arithmetic.mu_zero_ne_zero hc hne) (μ.apply_ne_top 0)
  have hcpos : 0 < c := Real.rpow_pos_of_pos hq _
  have hθne : θ ≠ 0 := by linarith [ha'.alpha_mem.1]
  have hcPow : c ^ θ = (μ 0).toReal := by
    dsimp [c]
    rw [← Real.rpow_mul hq.le, one_div_mul_cancel hθne, Real.rpow_one]
  let b := fun n => norming (stepLaw μ) θ n / c
  have hbtop : Tendsto b atTop atTop := hBtop.atTop_div_const hcpos
  have hb : ∀ᶠ n in atTop, 0 < b n := hbtop.eventually_gt_atTop 0
  have hbattr : IsStableAttracted (leafTimeLaw μ) θ 0 b := by
    apply leafTimeLaw_attracted_of_expansion hc hne ha'.alpha_mem hb hbtop
    intro lam hlam
    have ht := hExp (lam * c) (mul_pos hlam hcpos)
    rw [Real.mul_rpow hlam.le hcpos.le, hcPow, mul_comm (lam ^ θ)] at ht
    simpa only [b, div_div_eq_mul_div] using ht
  exact hbattr

private theorem leafTimeLaw_attracted_finiteVariance {μ : PMF ℕ} (hc : IsCritical μ)
    (hne : μ 1 ≠ 1) {θ : ℝ} (hDA : ∃ a, StableDomain μ θ a)
    (hfin : Integrable (fun z : ℤ => (z : ℝ) ^ 2) (stepLaw μ)) :
    IsStableAttracted (leafTimeLaw μ) θ 0
      (fun n => norming (stepLaw μ) θ n / (μ 0).toReal ^ (1 / θ)) := by
  have := isProbabilityMeasure_stepLaw μ
  have := leafTimeLaw_probability hc hne
  obtain ⟨a, ha⟩ := hDA
  have ha' : IsStableAttracted (stepLaw μ) θ (mean (stepLaw μ)) a := by
    rw [mean_stepLaw hc]
    exact stableDomain_isStableAttracted ha
  have hθ := DomainCriterion.index_eq_two_of_integrable_sq ha' (integrable_stepLaw hc) hfin
  subst θ
  obtain ⟨hsq, hv⟩ := leafTimeLaw_secondMoment hc hne hfin
  obtain ⟨hi, hm⟩ := leafTimeLaw_firstMoment hc hne
  have hq : 0 < (μ 0).toReal :=
    ENNReal.toReal_pos (Arithmetic.mu_zero_ne_zero hc hne) (μ.apply_ne_top 0)
  have hvar := DomainCriterion.variance_pos_of_integrable_sq ha' (integrable_stepLaw hc) hfin
  have hvar' : 0 < variance (leafTimeLaw μ) := by rw [hv]; exact div_pos hvar hq
  have ht := CanonicalAttraction.isStableAttracted_of_finiteVariance hi hsq hvar'
  rw [hm] at ht
  have he : norming (leafTimeLaw μ) 2 =
      fun n => norming (stepLaw μ) 2 n / (μ 0).toReal ^ (1 / (2 : ℝ)) := by
    funext n
    rw [norming_of_integrable_sq hsq, norming_of_integrable_sq hfin,
      hv, Real.sqrt_div hvar.le]
    simp only [Real.sqrt_eq_rpow]
    ring
  rwa [he] at ht

/-- The entire exact-leaf local limit in the infinite-variance case, including
all lattice spans. Aperiodicity is not needed for this strengthening. -/
private theorem ltn_ii_tendsto_infiniteVariance {μ : PMF ℕ} {θ : ℝ}
    (hc : IsCritical μ) (hne : μ 1 ≠ 1) (hDA : ∃ a, StableDomain μ θ a)
    (hinf : ¬ Integrable (fun z : ℤ => (z : ℝ) ^ 2) (stepLaw μ)) :
    Tendsto (fun n : ℕ => (n : ℝ) * norming (stepLaw μ) θ n * leafProb μ (n + 1))
      (atTop ⊓ 𝓟 {n : ℕ | arithFactor μ {0} ∣ n})
      (𝓝 ((μ 0).toReal ^ (1 / θ) * Scalar.stableDensity θ 0 * (arithFactor μ {0} : ℝ))) :=
  ltn_ii_tendsto_of_laplace_expansion hc hne hDA fun _ hlam =>
    stepLaw_laplace_expansion_infinite hc hDA hinf hlam

/-- Solvability of the lattice constraint is exactly divisibility by the leaf gcd.
The index here is an integer; passage to nonnegative indices is a separate step. -/
private theorem allowable_summand_exists {μ : PMF ℕ} {d b : ℕ}
    (hdb : IsSuppSpan μ d b) (n : ℕ) :
    (∃ k : ℤ, (d : ℤ) ∣ (n : ℤ) - k * ((b : ℤ) - 1)) ↔
      arithFactor μ {0} ∣ n := by
  rw [← Arithmetic.int_gcd_eq_arithFactor hdb, Int.gcd_dvd_iff]
  constructor
  · rintro ⟨k, l, hl⟩
    exact ⟨k, l, by linarith⟩
  · rintro ⟨k, l, hl⟩
    exact ⟨k, l, by linarith⟩

/-- Two allowable walk lengths differ by a multiple of `d/g`, and every such
translate is allowable. This is the arithmetic input to the mesh of the Riemann sum. -/
private theorem lattice_constraint_class {d : ℕ} {a n r : ℤ} (hd : 0 < d)
    (hr : (d : ℤ) ∣ n - r * a) (k : ℤ) :
    (d : ℤ) ∣ n - k * a ↔ (d : ℤ) / (Int.gcd a d : ℤ) ∣ k - r := by
  constructor
  · intro hk
    have hm : r * a ≡ k * a [ZMOD (d : ℤ)] := by
      apply Int.modEq_iff_dvd.mpr
      convert dvd_sub hr hk using 1; ring
    have hc := hm.cancel_right_div_gcd (by exact_mod_cast hd)
    simpa only [Int.modEq_iff_dvd, Int.gcd_comm] using hc
  · rintro ⟨l, hl⟩
    have ha := Int.ediv_mul_cancel (Int.gcd_dvd_left a (d : ℤ))
    have hdg := Int.ediv_mul_cancel (Int.gcd_dvd_right a (d : ℤ))
    have hm : (d : ℤ) ∣ (k - r) * a := by
      refine ⟨l * (a / (Int.gcd a d : ℤ)), ?_⟩
      calc
        (k - r) * a = ((d : ℤ) / (Int.gcd a d : ℤ)) * l *
            ((a / (Int.gcd a d : ℤ)) * (Int.gcd a d : ℤ)) := by rw [hl, ha]
        _ = (((d : ℤ) / (Int.gcd a d : ℤ)) * (Int.gcd a d : ℤ)) *
            (l * (a / (Int.gcd a d : ℤ))) := by ring
        _ = _ := by rw [hdg]
    convert dvd_sub hr hm using 1; ring

/-- Along the leaf gcd, exactly one integer residue class modulo `d/g` can
contribute to the lattice LLT. Nonnegative walk lengths are obtained by intersecting
this class with `ℕ`; no density or limiting assertion is used here. -/
private theorem allowable_summand_class {μ : PMF ℕ} {d b : ℕ}
    (hdb : IsSuppSpan μ d b) {n : ℕ} (hn : arithFactor μ {0} ∣ n) :
    ∃ r : ℤ, ∀ k : ℤ,
      ((d : ℤ) ∣ (n : ℤ) - k * ((b : ℤ) - 1)) ↔
        (d : ℤ) / (arithFactor μ {0} : ℤ) ∣ k - r := by
  obtain ⟨r, hr⟩ := (allowable_summand_exists hdb n).2 hn
  refine ⟨r, fun k => ?_⟩
  rw [← Arithmetic.int_gcd_eq_arithFactor hdb]
  exact lattice_constraint_class (by have := hdb.1; omega) hr k

/-- The printed slowly varying denominator is exactly the norming denominator
at every positive integer, so its use requires no additional asymptotic shift. -/
private theorem hSlow_mul_rpow {μ : PMF ℕ} {θ : ℝ} {n : ℕ} (hn : 0 < n) :
    hSlow μ θ n * (n : ℝ) ^ (1 / θ + 1) = (n : ℝ) * norming (stepLaw μ) θ n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  rw [hSlow, Nat.floor_natCast, Real.rpow_add hnR, Real.rpow_one]
  have hp : (n : ℝ) ^ (1 / θ) ≠ 0 := (Real.rpow_pos_of_pos hnR _).ne'
  field_simp

/-- The leaf-time local limit does not require aperiodicity of the offspring law.
The span is that of the leaf-time increment, so this includes a constant excess
law `Y` arising from a single positive offspring atom. -/
theorem ltn_ii_tendsto_general {μ : PMF ℕ} {θ : ℝ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hDA : ∃ a, StableDomain μ θ a) :
    Tendsto (fun n : ℕ => (n : ℝ) * norming (stepLaw μ) θ n * leafProb μ (n + 1))
      (atTop ⊓ 𝓟 {n : ℕ | arithFactor μ {0} ∣ n})
      (𝓝 ((μ 0).toReal ^ (1 / θ) * Scalar.stableDensity θ 0 * (arithFactor μ {0} : ℝ))) := by
  by_cases hfin : Integrable (fun z : ℤ => (z : ℝ) ^ 2) (stepLaw μ)
  · exact ltn_ii_tendsto_of_rescaled_attraction hc hne hDA
      (leafTimeLaw_attracted_finiteVariance hc hne hDA hfin)
  · exact ltn_ii_tendsto_infiniteVariance hc hne hDA hfin

/-- Theorem 3.1(ii), via the leaf-time walk. -/
theorem ltn_ii_tendsto {μ : PMF ℕ} {θ : ℝ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hap : Aperiodic μ) (hDA : ∃ a, StableDomain μ θ a) :
    Tendsto (fun n : ℕ => (n : ℝ) * norming (stepLaw μ) θ n * leafProb μ (n + 1))
      (atTop ⊓ 𝓟 {n : ℕ | arithFactor μ {0} ∣ n})
      (𝓝 ((μ 0).toReal ^ (1 / θ) * Scalar.stableDensity θ 0 * (arithFactor μ {0} : ℝ))) := by
  have _ := hap
  exact ltn_ii_tendsto_general hc hne hDA

private theorem thm_ltn_ii_arith {μ : PMF ℕ} {θ : ℝ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hap : Aperiodic μ) (hDA : ∃ a, StableDomain μ θ a) :
    (fun n : ℕ => leafProb μ (n + 1)) ~[atTop ⊓ 𝓟 {n : ℕ | arithFactor μ {0} ∣ n}]
      (fun n : ℕ => (μ 0).toReal ^ (1 / θ) * Scalar.stableDensity θ 0 * (arithFactor μ {0} : ℝ) /
        (hSlow μ θ n * (n : ℝ) ^ (1 / θ + 1))) := by
  obtain ⟨a, ha⟩ := hDA
  have hθ := (stableDomain_isStableAttracted ha).alpha_mem
  have hq : 0 < (μ 0).toReal :=
    ENNReal.toReal_pos (Arithmetic.mu_zero_ne_zero hc hne) (μ.apply_ne_top 0)
  have hg : 0 < arithFactor μ {0} := by
    rw [Arithmetic.arithFactor_zero_eq_setGcd hc hne]
    exact lt_of_lt_of_le Nat.zero_lt_one
      (Arithmetic.arithFactor_isGreatest_of_two_le (Arithmetic.exists_two_le hc hne)).1.1
  let C := (μ 0).toReal ^ (1 / θ) * Scalar.stableDensity θ 0 * (arithFactor μ {0} : ℝ)
  have hC : C ≠ 0 := (mul_pos (mul_pos (Real.rpow_pos_of_pos hq _)
    (Scalar.stableDensity_zero_pos hθ)) (by exact_mod_cast hg)).ne'
  have ht := (ltn_ii_tendsto hc hne hap ⟨a, ha⟩).div_const C
  change Tendsto (fun n : ℕ => (n : ℝ) * norming (stepLaw μ) θ n * leafProb μ (n + 1) / C)
    _ (𝓝 (C / C)) at ht
  rw [div_self hC] at ht
  apply isEquivalent_of_tendsto_one
  refine ht.congr' ?_
  filter_upwards [(eventually_gt_atTop 0).filter_mono inf_le_left] with n hn
  change (n : ℝ) * norming (stepLaw μ) θ n * leafProb μ (n + 1) / C =
    leafProb μ (n + 1) / (C / (hSlow μ θ n * (n : ℝ) ^ (1 / θ + 1)))
  rw [hSlow_mul_rpow hn, div_div_eq_mul_div]
  ring

/-- The printed asymptotic form of Theorem 3.1(ii). -/
theorem thm_ltn_ii {μ : PMF ℕ} {θ : ℝ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hap : Aperiodic μ) (hDA : ∃ a, StableDomain μ θ a) {d b : ℕ} (hdb : IsSuppSpan μ d b) :
    (fun n : ℕ => leafProb μ (n + 1)) ~[atTop ⊓ 𝓟 {n : ℕ | Int.gcd ((b : ℤ) - 1) (d : ℤ) ∣ n}]
      (fun n : ℕ => (μ 0).toReal ^ (1 / θ) * Scalar.stableDensity θ 0 *
        (Int.gcd ((b : ℤ) - 1) (d : ℤ) : ℝ) / (hSlow μ θ n * (n : ℝ) ^ (1 / θ + 1))) := by
  rw [Arithmetic.int_gcd_eq_arithFactor hdb]
  exact thm_ltn_ii_arith hc hne hap hDA

private theorem finiteVariance_constant {q v x g : ℝ} (hq : 0 < q) (hv : 0 < v) (hx : 0 < x) :
    q ^ (1 / (2 : ℝ)) * (1 / Real.sqrt (4 * Real.pi)) * g /
      (x * (Real.sqrt v * Real.sqrt (x / 2))) =
        Real.sqrt (q / (2 * Real.pi * v)) * g * x ^ (-(3 : ℝ) / 2) := by
  have hpow : x ^ (-(3 : ℝ) / 2) = 1 / (x * Real.sqrt x) := by
    rw [show -(3 : ℝ) / 2 = -(1 + 1 / 2) by norm_num, Real.rpow_neg hx.le,
      Real.rpow_add hx, Real.rpow_one, ← Real.sqrt_eq_rpow]
    simp only [one_div]
  have hfour : Real.sqrt (4 * Real.pi) = 2 * Real.sqrt Real.pi := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4),
      show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num, Real.sqrt_sq_eq_abs,
      abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  rw [hpow, ← Real.sqrt_eq_rpow, hfour, Real.sqrt_div hx.le,
    Real.sqrt_div hq.le, Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 2 * Real.pi),
    Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  have hxroot := (Real.sqrt_pos.2 hx).ne'
  have hvroot := (Real.sqrt_pos.2 hv).ne'
  have hπroot := (Real.sqrt_pos.2 Real.pi_pos).ne'
  have htwo := (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2)).ne'
  field_simp
  ring_nf
  norm_num [Real.sq_sqrt]

/-- The finite-variance specialization, derived from the exact-leaf limit. -/
theorem thm_ltn_finiteVariance_arith {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hap : Aperiodic μ) (hfin : Integrable (fun z : ℤ => (z : ℝ) ^ 2) (stepLaw μ)) :
    (fun n : ℕ => leafProb μ (n + 1)) ~[atTop ⊓ 𝓟 {n : ℕ | arithFactor μ {0} ∣ n}]
      (fun n : ℕ => Real.sqrt ((μ 0).toReal / (2 * Real.pi * variance (stepLaw μ))) *
        (arithFactor μ {0} : ℝ) * (n : ℝ) ^ (-(3 : ℝ) / 2)) := by
  have hDA : ∃ a, StableDomain μ 2 a :=
    ⟨_, Scalar.stableDomain_of_finiteVariance hc hne
      (StableDomainTail.memLp_offspring_of_integrable_sq hfin)⟩
  have := isProbabilityMeasure_stepLaw μ
  obtain ⟨a, ha⟩ := hDA
  have hv := DomainCriterion.variance_pos_of_integrable_sq
    (stableDomain_isStableAttracted ha) (integrable_stepLaw hc) hfin
  have hq : 0 < (μ 0).toReal :=
    ENNReal.toReal_pos (Arithmetic.mu_zero_ne_zero hc hne) (μ.apply_ne_top 0)
  have ht := thm_ltn_ii_arith hc hne hap ⟨a, ha⟩
  apply ht.congr_right
  filter_upwards [(eventually_gt_atTop 0).filter_mono inf_le_left] with n hn
  rw [hSlow_mul_rpow hn, norming_of_integrable_sq hfin, stableDensity_two]
  simp only [gaussDensity, neg_zero, zero_pow (by omega : 2 ≠ 0), zero_div,
    Real.exp_zero]
  exact finiteVariance_constant hq hv (by exact_mod_cast hn)

end BGWLeaves.LeafMass.LeafLocalLimit
