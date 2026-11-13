/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.Attraction.Defs


/-!
# Quantile analysis

Ported from `BGWLeaves/StableAnalysis/QuantileAnalysis.lean` of the author's arXiv:1110.2163v4
formalization (local snapshot of 6 November 2026).
-/
@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal

namespace BGW.StableTrees.Attraction.QuantileAnalysis

open BGW.StableTrees.Attraction

theorem truncSecondMoment_nonneg (ν : Measure ℤ) (x : ℝ) :
    0 ≤ truncSecondMoment ν x := by
  unfold truncSecondMoment
  apply setIntegral_nonneg
  · exact MeasurableSet.of_discrete
  · intro z hz
    exact sq_nonneg (z : ℝ)

theorem truncSecondMoment_mono_nonneg {ν : Measure ℤ} [IsProbabilityMeasure ν]
    {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    truncSecondMoment ν x ≤ truncSecondMoment ν y := by
  unfold truncSecondMoment
  apply setIntegral_mono_set
  · refine IntegrableOn.of_bound ?_ ?_ (y ^ 2) ?_
    · calc
        ν {z : ℤ | |(z : ℝ)| ≤ y} ≤ ν Set.univ := measure_mono (subset_univ _)
        _ < ∞ := by simp
    · exact (measurable_of_countable _).aestronglyMeasurable.restrict
    · filter_upwards [ae_restrict_mem (s := {z : ℤ | |(z : ℝ)| ≤ y})
        MeasurableSet.of_discrete] with z hz
      change |(z : ℝ)| ≤ y at hz
      have : 0 ≤ y := le_trans hx hxy
      rw [Real.norm_of_nonneg (sq_nonneg (z : ℝ))]
      have hsq : |(z : ℝ)| ^ 2 ≤ y ^ 2 :=
        (sq_le_sq₀ (abs_nonneg _) this).2 hz
      simpa [sq_abs] using hsq
  · exact ae_restrict_of_ae (ae_of_all _ fun z => sq_nonneg (z : ℝ))
  · apply ae_of_all
    intro z hz
    change |(z : ℝ)| ≤ x at hz
    change |(z : ℝ)| ≤ y
    exact le_trans hz hxy

private theorem rightTail_tendsto_zero {ν : Measure ℤ} [IsProbabilityMeasure ν] :
    Tendsto (fun n : ℕ => ν {z : ℤ | (n : ℤ) < z}) atTop (𝓝 0) := by
  let s : ℕ → Set ℤ := fun n => {z | (n : ℤ) < z}
  have hanti : Antitone s := by
    intro m n hmn z hz
    change (n : ℤ) < z at hz
    change (m : ℤ) < z
    exact lt_of_le_of_lt (by exact_mod_cast hmn) hz
  have hinter : (⋂ n, s n) = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    intro z hz
    have hz' := (Set.mem_iInter.mp hz) (z.natAbs + 1)
    change ((z.natAbs + 1 : ℕ) : ℤ) < z at hz'
    omega
  have hfinite : ν (s 0) ≠ ∞ := by
    apply ne_of_lt
    calc
      ν (s 0) ≤ ν Set.univ := measure_mono (subset_univ _)
      _ < ∞ := by simp
  have h := tendsto_measure_iInter_atTop (μ := ν) (s := s)
    (fun n => (MeasurableSet.of_discrete : MeasurableSet (s n)).nullMeasurableSet)
    hanti ⟨0, hfinite⟩
  simpa [Function.comp_def, s, hinter] using h

private theorem rightTail_pos {ν : Measure ℤ} [IsProbabilityMeasure ν]
    (hstep : ν {z : ℤ | z < -1} = 0)
    (hinf : ¬ Integrable (fun z : ℤ => (z : ℝ) ^ 2) ν)
    (x : ℝ) : 0 < ν.real {z : ℤ | x < (z : ℝ)} := by
  have hne : ν {z : ℤ | x < (z : ℝ)} ≠ 0 := by
    intro hzero
    have hlow : ∀ᵐ z : ℤ ∂ν, -1 ≤ (z : ℝ) := by
      rw [ae_iff]
      have hset : {z : ℤ | ¬ -1 ≤ (z : ℝ)} = {z : ℤ | z < -1} := by
        ext z
        simp only [Set.mem_ofPred_eq]
        norm_cast
        exact not_le
      rw [hset]
      exact hstep
    have hup : ∀ᵐ z : ℤ ∂ν, (z : ℝ) ≤ x := by
      rw [ae_iff]
      have hset : {z : ℤ | ¬ (z : ℝ) ≤ x} = {z : ℤ | x < (z : ℝ)} := by
        ext z
        simp only [Set.mem_ofPred_eq, not_le]
      rw [hset]
      exact hzero
    have hsq : Integrable (fun z : ℤ => (z : ℝ) ^ 2) ν := by
      refine Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable
        ((max 1 |x|) ^ 2) ?_
      filter_upwards [hlow, hup] with z hlo hhi
      rw [Real.norm_of_nonneg (sq_nonneg (z : ℝ))]
      have habs : |(z : ℝ)| ≤ max 1 |x| := by
        rw [abs_le]
        constructor
        · have h1 : 1 ≤ max 1 |x| := le_max_left _ _
          linarith
        · exact hhi.trans ((le_abs_self x).trans (le_max_right _ _))
      have hsq : |(z : ℝ)| ^ 2 ≤ (max 1 |x|) ^ 2 :=
        (sq_le_sq₀ (abs_nonneg _) (by positivity)).2 habs
      simpa [sq_abs] using hsq
    exact hinf hsq
  rw [measureReal_def]
  exact ENNReal.toReal_pos hne (measure_ne_top _ _)

private theorem tailCrossing_nonempty {ν : Measure ℤ} [IsProbabilityMeasure ν]
    {n : ℕ} (hn : 0 < n) :
    ({x : ℝ | 0 ≤ x ∧ ν.real {z : ℤ | x < (z : ℝ)} ≤ 1 / (n : ℝ)}).Nonempty := by
  have hpos : 0 < 1 / (n : ℝ) := by positivity
  have hsmall : ∀ᶠ k : ℕ in atTop,
      ν {z : ℤ | (k : ℤ) < z} < ENNReal.ofReal (1 / (n : ℝ)) :=
    (rightTail_tendsto_zero (ν := ν)).eventually (Iio_mem_nhds (by positivity))
  obtain ⟨N, hN⟩ := (eventually_atTop.1 hsmall)
  let k := N
  have hk := hN k le_rfl
  refine ⟨(k : ℝ), Nat.cast_nonneg _, ?_⟩
  have hreal : (ν {z : ℤ | (k : ℤ) < z}).toReal < 1 / (n : ℝ) := by
    have h := (ENNReal.toReal_lt_toReal (measure_ne_top _ _) ENNReal.ofReal_ne_top).2 hk
    simpa [ENNReal.toReal_ofReal (le_of_lt hpos)] using h
  have hset : {z : ℤ | (k : ℝ) < (z : ℝ)} = {z : ℤ | (k : ℤ) < z} := by
    ext z
    simp only [Set.mem_ofPred_eq]
    exact_mod_cast (show (k : ℝ) < (z : ℝ) ↔ (k : ℤ) < z by norm_cast)
  simpa [measureReal_def, hset] using hreal.le

private theorem tailQuantile_zero {ν : Measure ℤ} [IsProbabilityMeasure ν]
    (hstep : ν {z : ℤ | z < -1} = 0)
    (hinf : ¬ Integrable (fun z : ℤ => (z : ℝ) ^ 2) ν) :
    tailQuantile ν 0 = 0 := by
  have hempty :
      {x : ℝ | 0 ≤ x ∧ ν.real {z : ℤ | x < (z : ℝ)} ≤ 1 / (0 : ℝ)} = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    intro x hx
    have hp := rightTail_pos hstep hinf x
    have hx' : ν.real {z : ℤ | x < (z : ℝ)} ≤ 0 := by simpa using hx.2
    exact (not_le_of_gt hp) hx'
  unfold tailQuantile
  simp only [Nat.cast_zero]
  rw [hempty]
  simp

private theorem tailQuantile_nonneg {ν : Measure ℤ} [IsProbabilityMeasure ν]
    {n : ℕ} (hn : 0 < n) : 0 ≤ tailQuantile ν n := by
  unfold tailQuantile
  exact le_csInf (tailCrossing_nonempty hn) (by
    intro x hx
    exact hx.1)

private theorem tailQuantile_monotone {ν : Measure ℤ} [IsProbabilityMeasure ν]
    (hstep : ν {z : ℤ | z < -1} = 0)
    (hinf : ¬ Integrable (fun z : ℤ => (z : ℝ) ^ 2) ν) :
    Monotone (tailQuantile ν) := by
  intro m n hmn
  by_cases hm0 : m = 0
  · subst m
    rw [tailQuantile_zero hstep hinf]
    by_cases hn0 : n = 0
    · subst n
      rw [tailQuantile_zero hstep hinf]
    · exact tailQuantile_nonneg (Nat.pos_of_ne_zero hn0)
  · have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
    have hnpos : 0 < n := lt_of_lt_of_le hmpos hmn
    have hmR : 0 < (m : ℝ) := by exact_mod_cast hmpos
    have hnR : 0 < (n : ℝ) := by exact_mod_cast hnpos
    have hinv : 1 / (n : ℝ) ≤ 1 / (m : ℝ) := by
      rw [div_le_div_iff₀ hnR hmR]
      norm_num
      exact_mod_cast hmn
    unfold tailQuantile
    apply csInf_le_csInf (show BddBelow
      {x : ℝ | 0 ≤ x ∧ ν.real {z : ℤ | x < (z : ℝ)} ≤ 1 / (m : ℝ)} from
        ⟨0, fun x hx => hx.1⟩) (tailCrossing_nonempty hnpos)
    intro x hx
    exact ⟨hx.1, hx.2.trans hinv⟩

private theorem integrableOn_sq_trunc {ν : Measure ℤ} [IsProbabilityMeasure ν]
    {x : ℝ} (hx : 0 ≤ x) :
    IntegrableOn (fun z : ℤ => (z : ℝ) ^ 2) {z : ℤ | |(z : ℝ)| ≤ x} ν := by
  refine IntegrableOn.of_bound ?_ ?_ (x ^ 2) ?_
  · calc
      ν {z : ℤ | |(z : ℝ)| ≤ x} ≤ ν Set.univ := measure_mono (subset_univ _)
      _ < ∞ := by simp
  · exact (measurable_of_countable _).aestronglyMeasurable.restrict
  · filter_upwards [ae_restrict_mem (s := {z : ℤ | |(z : ℝ)| ≤ x})
      MeasurableSet.of_discrete] with z hz
    change |(z : ℝ)| ≤ x at hz
    rw [Real.norm_of_nonneg (sq_nonneg (z : ℝ))]
    have hsq : |(z : ℝ)| ^ 2 ≤ x ^ 2 := (sq_le_sq₀ (abs_nonneg _) hx).2 hz
    simpa [sq_abs] using hsq

private theorem truncSecondMoment_le_mul_integral_abs {ν : Measure ℤ} [IsProbabilityMeasure ν]
    (hint : Integrable (fun z : ℤ => (z : ℝ)) ν) {x : ℝ} (hx : 0 ≤ x) :
    truncSecondMoment ν x ≤ x * ∫ z, |(z : ℝ)| ∂ν := by
  let s : Set ℤ := {z : ℤ | |(z : ℝ)| ≤ x}
  have habs : Integrable (fun z : ℤ => |(z : ℝ)|) ν := by
    simpa [Real.norm_eq_abs] using hint.norm
  have hscaled : Integrable (fun z : ℤ => x * |(z : ℝ)|) ν := habs.const_mul x
  have hmono : (∫ z in s, (z : ℝ) ^ 2 ∂ν) ≤ ∫ z in s, x * |(z : ℝ)| ∂ν := by
    apply setIntegral_mono_on (integrableOn_sq_trunc hx) hscaled.integrableOn
      (MeasurableSet.of_discrete)
    intro z hz
    change |(z : ℝ)| ≤ x at hz
    rw [← sq_abs]
    simpa [pow_two] using mul_le_mul_of_nonneg_right hz (abs_nonneg (z : ℝ))
  have hle : (∫ z in s, x * |(z : ℝ)| ∂ν) ≤ ∫ z, x * |(z : ℝ)| ∂ν :=
    setIntegral_le_integral hscaled (ae_of_all _ fun z => mul_nonneg hx (abs_nonneg _))
  calc
    truncSecondMoment ν x = ∫ z in s, (z : ℝ) ^ 2 ∂ν := rfl
    _ ≤ ∫ z in s, x * |(z : ℝ)| ∂ν := hmono
    _ ≤ ∫ z, x * |(z : ℝ)| ∂ν := hle
    _ = x * ∫ z, |(z : ℝ)| ∂ν := integral_const_mul x _

private theorem gaussCrossing_bddAbove {ν : Measure ℤ} [IsProbabilityMeasure ν]
    (hint : Integrable (fun z : ℤ => (z : ℝ)) ν) {n : ℕ} (hn : 0 < n) :
    BddAbove {z : ℝ | 0 ≤ z ∧ 1 / (n : ℝ) ≤ truncSecondMoment ν z / z ^ 2} := by
  let M : ℝ := ∫ z, |(z : ℝ)| ∂ν
  have hM : 0 ≤ M := integral_nonneg (fun z => abs_nonneg (z : ℝ))
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  refine ⟨(n : ℝ) * M, ?_⟩
  intro z hz
  have hzpos : 0 < z := by
    by_contra h
    have hz0 : z = 0 := le_antisymm (le_of_not_gt h) hz.1
    subst z
    have : 0 < 1 / (n : ℝ) := by positivity
    have hbad : 1 / (n : ℝ) ≤ 0 := by simpa using hz.2
    exact (not_le_of_gt this) hbad
  have hK := truncSecondMoment_le_mul_integral_abs hint hz.1
  have hratio : truncSecondMoment ν z / z ^ 2 ≤ M / z := by
    rw [div_le_div_iff₀ (sq_pos_of_pos hzpos) hzpos]
    calc
      truncSecondMoment ν z * z ≤ (z * M) * z :=
        mul_le_mul_of_nonneg_right (by simpa [M] using hK) hzpos.le
      _ = M * z ^ 2 := by ring
  have hbound : z ≤ (n : ℝ) * M := by
    have h := (div_le_div_iff₀ hnR hzpos).mp (hz.2.trans hratio)
    nlinarith [h]
  exact hbound

private theorem gaussQuantile_nonneg (ν : Measure ℤ) (n : ℕ) :
    0 ≤ gaussQuantile ν n := by
  let S : Set ℝ := {z : ℝ | 0 ≤ z ∧ 1 / (n : ℝ) ≤ truncSecondMoment ν z / z ^ 2}
  unfold gaussQuantile
  change 0 ≤ sSup S
  by_cases hB : BddAbove S
  · by_cases hE : S = ∅
    · simp [hE]
    · obtain ⟨z, hz⟩ := Set.nonempty_iff_ne_empty.mpr hE
      exact le_trans hz.1 (le_csSup hB hz)
  · rw [csSup_of_not_bddAbove hB]
    simp

private theorem gaussQuantile_zero {ν : Measure ℤ} : gaussQuantile ν 0 = 0 := by
  let S : Set ℝ := {z : ℝ | 0 ≤ z ∧ 1 / (0 : ℝ) ≤ truncSecondMoment ν z / z ^ 2}
  have hUnbounded : ¬ BddAbove S := by
    intro hb
    obtain ⟨b, hb⟩ := hb
    let z := max b 0 + 1
    have hz : z ∈ S := by
      refine ⟨by dsimp [z]; positivity, ?_⟩
      have hk := truncSecondMoment_nonneg ν z
      have hratio : 0 ≤ truncSecondMoment ν z / z ^ 2 := div_nonneg hk (sq_nonneg z)
      simpa [S] using hratio
    have hlt : b < z := by dsimp [z]; linarith [le_max_left b 0]
    exact (not_lt_of_ge (hb hz)) hlt
  unfold gaussQuantile
  simp only [Nat.cast_zero]
  rw [csSup_of_not_bddAbove (by simpa [S] using hUnbounded)]
  simp

private theorem gaussQuantile_monotone {ν : Measure ℤ} [IsProbabilityMeasure ν]
    (hint : Integrable (fun z : ℤ => (z : ℝ)) ν) :
    Monotone (gaussQuantile ν) := by
  intro m n hmn
  by_cases hm0 : m = 0
  · subst m
    rw [gaussQuantile_zero]
    exact gaussQuantile_nonneg ν n
  · have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
    have hnpos : 0 < n := lt_of_lt_of_le hmpos hmn
    have hmR : 0 < (m : ℝ) := by exact_mod_cast hmpos
    have hnR : 0 < (n : ℝ) := by exact_mod_cast hnpos
    have hinv : 1 / (n : ℝ) ≤ 1 / (m : ℝ) := by
      rw [div_le_div_iff₀ hnR hmR]
      norm_num
      exact_mod_cast hmn
    let Sₘ : Set ℝ := {z : ℝ | 0 ≤ z ∧ 1 / (m : ℝ) ≤ truncSecondMoment ν z / z ^ 2}
    let Sₙ : Set ℝ := {z : ℝ | 0 ≤ z ∧ 1 / (n : ℝ) ≤ truncSecondMoment ν z / z ^ 2}
    have hsubset : Sₘ ⊆ Sₙ := by
      intro z hz
      exact ⟨hz.1, hinv.trans hz.2⟩
    change sSup Sₘ ≤ sSup Sₙ
    by_cases hne : Sₘ.Nonempty
    · exact csSup_le_csSup (gaussCrossing_bddAbove hint hnpos) hne hsubset
    · have he : Sₘ = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
      have hnonneg : 0 ≤ sSup Sₙ := by
        have h := gaussQuantile_nonneg ν n
        change 0 ≤ sSup Sₙ at h
        exact h
      simpa [he] using hnonneg

private theorem truncSecondMoment_tendsto_atTop {ν : Measure ℤ} [IsProbabilityMeasure ν]
    (hinf : ¬ Integrable (fun z : ℤ => (z : ℝ) ^ 2) ν) :
    Tendsto (truncSecondMoment ν) atTop atTop := by
  rw [tendsto_atTop]
  intro M
  by_contra hcon
  rw [not_eventually] at hcon
  have hev : ∃ᶠ x : ℝ in atTop, truncSecondMoment ν x < M := by
    simpa only [not_le] using hcon
  -- bound for all natural truncation levels
  have hbound : ∀ n : ℕ, truncSecondMoment ν n ≤ max M 0 := by
    intro n
    have hlt : ∃ x : ℝ, (n : ℝ) ≤ x ∧ truncSecondMoment ν x < M := by
      obtain ⟨x, hx⟩ := (hev.and_eventually (eventually_ge_atTop (n : ℝ))).exists
      exact ⟨x, hx.2, hx.1⟩
    obtain ⟨x, hx, hxM⟩ := hlt
    exact (truncSecondMoment_mono_nonneg (Nat.cast_nonneg n) hx).trans
      (hxM.le.trans (le_max_left _ _))
  let g : ℤ → ℝ≥0∞ := fun z => ENNReal.ofReal ((z : ℝ) ^ 2)
  let s : ℕ → Set ℤ := fun n => {z : ℤ | |(z : ℝ)| ≤ (n : ℝ)}
  have hsmono : Monotone s := by
    intro m n hmn z hz
    change |(z : ℝ)| ≤ (n : ℝ)
    exact le_trans hz (by exact_mod_cast hmn)
  have hgm : Measurable g := (measurable_of_countable _)
  have hlint : ∫⁻ z, g z ∂ν ≤ ENNReal.ofReal (max M 0) := by
    have hf : ∀ n : ℕ, Measurable ((s n).indicator g) := fun n => (measurable_of_countable _)
    have hsup : ∀ z, g z = ⨆ n : ℕ, (s n).indicator g z := by
      intro z
      apply le_antisymm
      · obtain ⟨n, hn⟩ := exists_nat_ge |(z : ℝ)|
        refine le_trans ?_ (le_iSup _ n)
        rw [Set.indicator_of_mem (show z ∈ s n from hn)]
      · exact iSup_le fun n => Set.indicator_le_self _ _ z
    calc
      ∫⁻ z, g z ∂ν = ∫⁻ z, ⨆ n : ℕ, (s n).indicator g z ∂ν := lintegral_congr hsup
      _ = ⨆ n : ℕ, ∫⁻ z, (s n).indicator g z ∂ν := by
        apply lintegral_iSup hf
        intro m n hmn z
        show (s m).indicator g z ≤ (s n).indicator g z
        by_cases hz : z ∈ s m
        · rw [Set.indicator_of_mem hz, Set.indicator_of_mem (hsmono hmn hz)]
        · rw [Set.indicator_of_notMem hz]; exact bot_le
      _ ≤ ENNReal.ofReal (max M 0) := by
        refine iSup_le fun n => ?_
        rw [lintegral_indicator MeasurableSet.of_discrete]
        have hI : IntegrableOn (fun z : ℤ => (z : ℝ) ^ 2) (s n) ν :=
          integrableOn_sq_trunc (Nat.cast_nonneg n)
        have := ofReal_integral_eq_lintegral_ofReal hI
          (ae_of_all _ fun z => sq_nonneg (z : ℝ))
        change ∫⁻ z in s n, g z ∂ν ≤ _
        rw [← this]
        exact ENNReal.ofReal_le_ofReal (hbound n)
  apply hinf
  refine ⟨(measurable_of_countable _).aestronglyMeasurable, ?_⟩
  rw [HasFiniteIntegral, lt_top_iff_ne_top]
  have : ∫⁻ z : ℤ, ‖(z : ℝ) ^ 2‖ₑ ∂ν = ∫⁻ z, g z ∂ν :=
    lintegral_congr fun z => by
      simp only [g, Real.enorm_eq_ofReal (sq_nonneg (z : ℝ))]
  rw [this]
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hlint

private theorem gaussQuantile_tendsto_atTop {ν : Measure ℤ} [IsProbabilityMeasure ν]
    (hint : Integrable (fun z : ℤ => (z : ℝ)) ν)
    (hinf : ¬ Integrable (fun z : ℤ => (z : ℝ) ^ 2) ν) :
    Tendsto (gaussQuantile ν) atTop atTop := by
  rw [tendsto_atTop]
  intro A
  have hK := truncSecondMoment_tendsto_atTop hinf
  obtain ⟨x, hx⟩ := ((hK.eventually_gt_atTop 0).and
    ((eventually_gt_atTop (0 : ℝ)).and (eventually_ge_atTop A))).exists
  obtain ⟨hKx, hx0, hAx⟩ := hx
  have hr : 0 < truncSecondMoment ν x / x ^ 2 := div_pos hKx (by positivity)
  have hlim : Tendsto (fun n : ℕ => 1 / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_one_div_atTop_nhds_zero_nat
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hlim.eventually (Iio_mem_nhds hr))
  rw [eventually_atTop]
  refine ⟨N + 1, fun n hn => ?_⟩
  have hnpos : 0 < n := by omega
  have hmem : x ∈ {z : ℝ | 0 ≤ z ∧ 1 / (n : ℝ) ≤ truncSecondMoment ν z / z ^ 2} :=
    ⟨hx0.le, (hN n (by omega)).le⟩
  exact hAx.trans (le_csSup (gaussCrossing_bddAbove hint hnpos) hmem)

/-- Under an infinite second moment and the paper's lower support bound, the explicit norming
sequence is nondecreasing for every `1 < θ ≤ 2`. Its `n = 0` values use the stated `sInf`/`sSup`
conventions. -/
theorem norming_monotone_of_infinite_variance {ν : Measure ℤ} [IsProbabilityMeasure ν]
    (hstep : ν {z : ℤ | z < -1} = 0)
    (hint : Integrable (fun z : ℤ => (z : ℝ)) ν)
    (hinf : ¬ Integrable (fun z : ℤ => (z : ℝ) ^ 2) ν)
    (θ : ℝ) (hθ : 1 < θ ∧ θ ≤ 2) : Monotone (norming ν θ) := by
  intro m n hmn
  have hfinite : ¬ Integrable (fun z : ℤ => (z : ℝ) ^ 2) ν := hinf
  by_cases hθ2 : θ < 2
  · simp [norming, hfinite, hθ2]
    have hg : 0 < -Real.Gamma (1 - θ) :=
      (negGamma_eq hθ.1 hθ2).2.2
    have hc : 0 ≤ (-Real.Gamma (1 - θ)) ^ θ⁻¹ :=
      (Real.rpow_pos_of_pos hg (θ⁻¹)).le
    exact mul_le_mul_of_nonneg_left (tailQuantile_monotone hstep hinf hmn) hc
  · have hθeq : θ = 2 := le_antisymm hθ.2 (le_of_not_gt hθ2)
    subst θ
    have hgmono := gaussQuantile_monotone hint hmn
    have hgm0 := gaussQuantile_nonneg ν m
    have hgn0 := gaussQuantile_nonneg ν n
    have hK : truncSecondMoment ν (gaussQuantile ν m) ≤
        truncSecondMoment ν (gaussQuantile ν n) :=
      truncSecondMoment_mono_nonneg hgm0 hgmono
    have hKm : 0 ≤ truncSecondMoment ν (gaussQuantile ν m) :=
      truncSecondMoment_nonneg ν _
    have hprod : (m : ℝ) * truncSecondMoment ν (gaussQuantile ν m) ≤
        (n : ℝ) * truncSecondMoment ν (gaussQuantile ν n) := by
      calc
        (m : ℝ) * truncSecondMoment ν (gaussQuantile ν m) ≤
            (n : ℝ) * truncSecondMoment ν (gaussQuantile ν m) :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hmn) hKm
        _ ≤ (n : ℝ) * truncSecondMoment ν (gaussQuantile ν n) :=
          mul_le_mul_of_nonneg_left hK (Nat.cast_nonneg n)
    simp only [norming, hfinite, ite_false, not_lt_of_ge (le_of_not_gt hθ2)]
    apply Real.sqrt_le_sqrt
    exact div_le_div_of_nonneg_right hprod (by norm_num)

private theorem norming_gauss_ratio_eq {ν : Measure ℤ}
    (hinf : ¬ Integrable (fun z : ℤ => (z : ℝ) ^ 2) ν) {n : ℕ} (hn : 0 < n) :
    norming ν 2 n / Real.sqrt n =
      Real.sqrt (truncSecondMoment ν (gaussQuantile ν n) / 2) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hK : 0 ≤ truncSecondMoment ν (gaussQuantile ν n) :=
    truncSecondMoment_nonneg ν _
  simp only [norming, hinf, ite_false, lt_irrefl]
  rw [show (n : ℝ) * truncSecondMoment ν (gaussQuantile ν n) / 2 =
      (n : ℝ) * (truncSecondMoment ν (gaussQuantile ν n) / 2) by ring,
    Real.sqrt_mul hnR.le]
  have hsqrt : Real.sqrt (n : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hnR)
  rw [mul_div_cancel_left₀ _ hsqrt]

/-- Remark after the strong local limit theorem: for infinite variance and `θ = 2`,
`h(n) = a_n/√n` tends to `∞` and is nondecreasing, for the corrected norming
`a_n = √(n K(z_n)/2)`. -/
theorem locallimit_remark (ν : Measure ℤ) [IsProbabilityMeasure ν] (hstep : ν {z | z < -1} = 0)
    (hint : Integrable (fun z : ℤ => (z : ℝ)) ν) (hDA : ∃ b, IsStableAttracted ν 2 (mean ν) b)
    (hinf : ¬ Integrable (fun z : ℤ => (z : ℝ) ^ 2) ν) :
    Tendsto (fun n : ℕ => norming ν 2 n / Real.sqrt n) atTop atTop ∧
      Monotone (fun n : ℕ => norming ν 2 n / Real.sqrt n) := by
  have _ := hstep
  have _ := hDA
  have hK := truncSecondMoment_tendsto_atTop hinf
  have hg := gaussQuantile_tendsto_atTop hint hinf
  constructor
  · have h1 : Tendsto (fun n : ℕ => truncSecondMoment ν (gaussQuantile ν n)) atTop atTop :=
      hK.comp hg
    have h2 : Tendsto (fun n : ℕ => truncSecondMoment ν (gaussQuantile ν n) / 2) atTop atTop :=
      h1.atTop_div_const (by norm_num)
    have h3 := Real.tendsto_sqrt_atTop.comp h2
    refine h3.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    exact (norming_gauss_ratio_eq hinf hn).symm
  · intro m n hmn
    by_cases hm0 : m = 0
    · subst m
      simp only [Nat.cast_zero, Real.sqrt_zero, div_zero]
      by_cases hn0 : n = 0
      · subst n; simp
      · rw [norming_gauss_ratio_eq hinf (Nat.pos_of_ne_zero hn0)]
        exact Real.sqrt_nonneg _
    · have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
      have hnpos : 0 < n := lt_of_lt_of_le hmpos hmn
      change norming ν 2 m / Real.sqrt m ≤ norming ν 2 n / Real.sqrt n
      rw [norming_gauss_ratio_eq hinf hmpos, norming_gauss_ratio_eq hinf hnpos]
      apply Real.sqrt_le_sqrt
      apply div_le_div_of_nonneg_right _ (by norm_num)
      exact truncSecondMoment_mono_nonneg (gaussQuantile_nonneg ν m)
        (gaussQuantile_monotone hint hmn)

end BGW.StableTrees.Attraction.QuantileAnalysis
