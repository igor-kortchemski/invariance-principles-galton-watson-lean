module

public import BGWLeaves.GeneralA.Regroup
public import BGWLeaves.StableAnalysis.CanonicalAttraction
public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-! Finite moments of geometric sums of arbitrary integer increments. No lower
support bound or non-degeneracy of the increment law is assumed. -/

@[expose] public section

namespace BGWLeaves.GeneralA.Moments

open MeasureTheory ProbabilityTheory Filter BGWLeaves.StableAnalysis
open scoped ENNReal Topology

private instance walk_probability (ν : Measure ℤ) [IsProbabilityMeasure ν] (n : ℕ) :
    IsProbabilityMeasure (intWalk ν n) := by
  induction n with
  | zero => simp only [intWalk]; infer_instance
  | succ n ih => simpa only [intWalk] using
      (inferInstance : IsProbabilityMeasure ((intWalk ν n).conv ν))

/-- The mixture `∑ₖ q (1 - q)^k • ν^{*k}`: law of a sum of a geometric(`q`) number of independent `ν`-steps. -/
noncomputable def geometricLaw (q : ℝ≥0∞) (ν : Measure ℤ) : Measure ℤ :=
  Measure.sum fun k : ℕ => (q * (1 - q) ^ k) • intWalk ν k

theorem geometricLaw_probability {q : ℝ≥0∞} (hq0 : q ≠ 0) (hq1 : q ≤ 1)
    (ν : Measure ℤ) [IsProbabilityMeasure ν] : IsProbabilityMeasure (geometricLaw q ν) := by
  constructor
  simp only [geometricLaw, Measure.sum_apply _ MeasurableSet.univ,
    Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric,
    ENNReal.sub_sub_cancel ENNReal.one_ne_top hq1]
  exact ENNReal.mul_inv_cancel hq0 (ne_of_lt (lt_of_le_of_lt hq1 ENNReal.one_lt_top))

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

theorem geometricLaw_secondMoment {q : ℝ≥0∞} (hq0 : q ≠ 0) (hq1 : q ≤ 1)
    (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (hint : Integrable (fun z : ℤ => (z : ℝ)) ν)
    (hfin : Integrable (fun z : ℤ => (z : ℝ) ^ 2) ν) :
    Integrable (fun z : ℤ => (z : ℝ) ^ 2) (geometricLaw q ν) ∧
      (∫ z : ℤ, (z : ℝ) ^ 2 ∂geometricLaw q ν) =
        (1 - q.toReal) / q.toReal * (∫ z : ℤ, (z : ℝ) ^ 2 ∂ν) +
          2 * (1 - q.toReal) ^ 2 / q.toReal ^ 2 * mean ν ^ 2 := by
  have hqtop : q ≠ ⊤ := ne_of_lt (lt_of_le_of_lt hq1 ENNReal.one_lt_top)

  have hy := hint
  have hysq := hfin
  have hq : 0 < q.toReal :=
    ENNReal.toReal_pos hq0 hqtop
  have hr : 0 ≤ 1 - q.toReal := sub_nonneg.mpr
    (by simpa using ENNReal.toReal_mono ENNReal.one_ne_top hq1)
  have hrat : ‖1 - q.toReal‖ < 1 := by rw [Real.norm_eq_abs, abs_of_nonneg hr]; linarith
  let A := ∫ z : ℤ, (z : ℝ) ^ 2 ∂ν
  let M := mean ν
  let ρ := fun k : ℕ => (q * (1 - q) ^ k) • intWalk ν k
  have hi : ∀ k, Integrable (fun z : ℤ => (z : ℝ) ^ 2) (ρ k) := by
    intro k
    have ht : q * (1 - q) ^ k ≠ ⊤ := by
      have hμ := hqtop
      finiteness
    exact (walk_secondMoment ν hy hysq k).1.smul_measure ht
  have he : ∀ k, (∫ z : ℤ, (z : ℝ) ^ 2 ∂ρ k) =
      (q.toReal * (A - M ^ 2)) * ((k : ℝ) * (1 - q.toReal) ^ k) +
        (q.toReal * M ^ 2) * ((k : ℝ) ^ 2 * (1 - q.toReal) ^ k) := by
    intro k
    rw [show ρ k = (q * (1 - q) ^ k) • intWalk ν k from rfl,
      integral_smul_measure, (walk_secondMoment ν hy hysq k).2]
    simp only [smul_eq_mul, ENNReal.toReal_mul, ENNReal.toReal_pow,
      ENNReal.toReal_sub_of_le (hq1) ENNReal.one_ne_top, ENNReal.toReal_one]
    dsimp [A, M]
    ring
  have hsum := ((hasSum_coe_mul_geometric_of_norm_lt_one hrat).mul_left
    (q.toReal * (A - M ^ 2))).add
      ((hasSum_sq_mul_geometric_of_norm_lt_one hrat).mul_left (q.toReal * M ^ 2))
  have hconst : q.toReal * (A - M ^ 2) *
      ((1 - q.toReal) / (1 - (1 - q.toReal)) ^ 2) +
      q.toReal * M ^ 2 * ((1 - q.toReal) * (1 + (1 - q.toReal)) /
        (1 - (1 - q.toReal)) ^ 3) =
      (1 - q.toReal) / q.toReal * A + 2 * (1 - q.toReal) ^ 2 / q.toReal ^ 2 * M ^ 2 := by
    rw [show 1 - (1 - q.toReal) = q.toReal by ring]
    field_simp [hq.ne']
    ring
  rw [hconst] at hsum
  have hsum' : HasSum (fun k => ∫ z : ℤ, (z : ℝ) ^ 2 ∂ρ k)
      ((1 - q.toReal) / q.toReal * A + 2 * (1 - q.toReal) ^ 2 / q.toReal ^ 2 * M ^ 2) := by simpa only [he] using hsum
  have hnorm : ∀ k, (∫ z : ℤ, ‖(z : ℝ) ^ 2‖ ∂ρ k) = ∫ z : ℤ, (z : ℝ) ^ 2 ∂ρ k := by
    intro k
    simp only [Real.norm_of_nonneg (sq_nonneg _)]
  have hsumNorm : Summable (fun k => ∫ z : ℤ, ‖(z : ℝ) ^ 2‖ ∂ρ k) :=
    hsum'.summable.congr fun k => (hnorm k).symm
  have hm : Integrable (fun z : ℤ => (z : ℝ) ^ 2) (Measure.sum ρ) :=
    integrable_sum_measure hi hsumNorm
  exact ⟨hm, (integral_sum_measure hm).trans hsum'.tsum_eq⟩


theorem integrable_cast_of_square (ν : Measure ℤ) [IsFiniteMeasure ν]
    (hfin : Integrable (fun z : ℤ => (z : ℝ) ^ 2) ν) :
    Integrable (fun z : ℤ => (z : ℝ)) ν := by
  apply (hfin.add (integrable_const (1 : ℝ))).mono' (by fun_prop)
  filter_upwards [] with z
  change |(z : ℝ)| ≤ (z : ℝ) ^ 2 + 1
  have h := sq_nonneg (|(z : ℝ)| - 1)
  rw [sub_sq, sq_abs] at h
  nlinarith [abs_nonneg (z : ℝ)]

theorem geometricLaw_firstMoment {q : ℝ≥0∞} (hq0 : q ≠ 0) (hq1 : q ≤ 1)
    (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (hint : Integrable (fun z : ℤ => (z : ℝ)) ν)
    (hfin : Integrable (fun z : ℤ => (z : ℝ) ^ 2) ν) :
    Integrable (fun z : ℤ => (z : ℝ)) (geometricLaw q ν) ∧
      mean (geometricLaw q ν) = (1 - q.toReal) / q.toReal * mean ν := by
  have := geometricLaw_probability hq0 hq1 ν
  have hi := integrable_cast_of_square (geometricLaw q ν)
    (geometricLaw_secondMoment hq0 hq1 ν hint hfin).1
  have hqtop : q ≠ ⊤ := ne_of_lt (lt_of_le_of_lt hq1 ENNReal.one_lt_top)
  have hq : 0 < q.toReal := ENNReal.toReal_pos hq0 hqtop
  have hr : 0 ≤ 1 - q.toReal := sub_nonneg.mpr
    (by simpa using ENNReal.toReal_mono ENNReal.one_ne_top hq1)
  have hrat : ‖1 - q.toReal‖ < 1 := by rw [Real.norm_eq_abs, abs_of_nonneg hr]; linarith
  refine ⟨hi, ?_⟩
  rw [mean, geometricLaw, integral_sum_measure hi]
  have hw (k : ℕ) := (walk_firstMoment ν hint k).2
  simp_rw [integral_smul_measure, smul_eq_mul, ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_sub_of_le hq1 ENNReal.one_ne_top, ENNReal.toReal_one, hw]
  have hsum := (hasSum_coe_mul_geometric_of_norm_lt_one hrat).mul_left (q.toReal * mean ν)
  have he : q.toReal * mean ν * ((1 - q.toReal) / (1 - (1 - q.toReal)) ^ 2) =
      (1 - q.toReal) / q.toReal * mean ν := by
    rw [show 1 - (1 - q.toReal) = q.toReal by ring]
    field_simp
  rw [he] at hsum
  convert hsum.tsum_eq using 1
  apply tsum_congr
  intro k
  ring

theorem conv_firstMoment (α β : Measure ℤ) [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    (hα : Integrable (fun z : ℤ => (z : ℝ)) α)
    (hβ : Integrable (fun z : ℤ => (z : ℝ)) β) :
    Integrable (fun z : ℤ => (z : ℝ)) (α.conv β) ∧ mean (α.conv β) = mean α + mean β := by
  have hp : Integrable (fun p : ℤ × ℤ => ((p.1 + p.2 : ℤ) : ℝ)) (α.prod β) := by
    convert (hα.comp_fst β).add (hβ.comp_snd α) using 1
    ext p
    simp
  constructor
  · rw [Measure.conv]
    exact (integrable_map_measure (by fun_prop) (by fun_prop)).2 hp
  · rw [mean, Measure.conv, integral_map (by fun_prop) (by fun_prop)]
    simp_rw [Int.cast_add]
    rw [integral_add (hα.comp_fst β) (hβ.comp_snd α), integral_fun_fst, integral_fun_snd]
    simp [mean]

theorem conv_secondMoment (α β : Measure ℤ) [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    (hα : Integrable (fun z : ℤ => (z : ℝ)) α)
    (hβ : Integrable (fun z : ℤ => (z : ℝ)) β)
    (hαsq : Integrable (fun z : ℤ => (z : ℝ) ^ 2) α)
    (hβsq : Integrable (fun z : ℤ => (z : ℝ) ^ 2) β) :
    Integrable (fun z : ℤ => (z : ℝ) ^ 2) (α.conv β) ∧
      (∫ z : ℤ, (z : ℝ) ^ 2 ∂α.conv β) =
        (∫ z : ℤ, (z : ℝ) ^ 2 ∂α) + 2 * mean α * mean β + (∫ z : ℤ, (z : ℝ) ^ 2 ∂β) := by
  have hcross := (hα.mul_prod hβ).const_mul 2
  have hp : Integrable (fun p : ℤ × ℤ => ((p.1 + p.2 : ℤ) : ℝ) ^ 2) (α.prod β) := by
    convert ((hαsq.comp_fst β).add hcross).add (hβsq.comp_snd α) using 1
    ext p
    simp only [Int.cast_add, Pi.add_apply]
    ring
  refine ⟨?_, ?_⟩
  · rw [Measure.conv]
    exact (integrable_map_measure (by fun_prop) (by fun_prop)).2 hp
  · rw [Measure.conv, integral_map (by fun_prop) (by fun_prop)]
    have he : (fun p : ℤ × ℤ => ((p.1 + p.2 : ℤ) : ℝ) ^ 2) =
        fun p => ((p.1 : ℝ) ^ 2 + 2 * ((p.1 : ℝ) * (p.2 : ℝ))) + (p.2 : ℝ) ^ 2 := by
      ext p
      push_cast
      ring
    have hleft : Integrable (fun p : ℤ × ℤ => (p.1 : ℝ) ^ 2 + 2 * ((p.1 : ℝ) * (p.2 : ℝ)))
        (α.prod β) := by convert (hαsq.comp_fst β).add hcross using 1
    rw [he, integral_add hleft (hβsq.comp_snd α),
      integral_add (f := fun p : ℤ × ℤ => (p.1 : ℝ) ^ 2)
        (g := fun p : ℤ × ℤ => 2 * ((p.1 : ℝ) * (p.2 : ℝ)))
        (hαsq.comp_fst β) hcross, integral_const_mul,
      integral_prod_mul (fun z : ℤ => (z : ℝ)) (fun z : ℤ => (z : ℝ)),
      integral_fun_fst (fun z : ℤ => (z : ℝ) ^ 2), integral_fun_snd (fun z : ℤ => (z : ℝ) ^ 2)]
    simp only [probReal_univ, mean]
    ring

end BGWLeaves.GeneralA.Moments
