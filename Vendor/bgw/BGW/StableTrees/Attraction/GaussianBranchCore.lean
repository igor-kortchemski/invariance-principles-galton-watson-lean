/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.Attraction.MonotoneDensity
public import BGW.StableTrees.Attraction.QuantileInversion
public import BGW.StableTrees.Attraction.Defs

/-!
# Gaussian branch (index `θ = 2`) of stable analysis

The truncated second moment and Gaussian crossing sequence results cover the index-two branch.
Ported from `BGWLeaves/StableAnalysis/GaussianBranch.lean` of the author's arXiv:1110.2163v4
formalization (local snapshot of 6 November 2026).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set intervalIntegral
open scoped Topology ENNReal

namespace BGW.StableTrees.Attraction.GaussianBranch

open BGW.StableTrees.Attraction BGW.StableTrees.Attraction.MonotoneDensity BGW.StableTrees

/-! ## 1. Abstract tail with index `-2` -/

section Abstract

variable {T : ℝ → ℝ}

private theorem tail_eventually_pos (hT0 : ∀ x, 0 ≤ T x) (hT : IsRegVaryAtTop T (-2)) :
    ∀ᶠ x : ℝ in atTop, 0 < T x := by
  have := (hT 1 one_pos).eventually (isOpen_ne.mem_nhds (show ((1 : ℝ) ^ (-2 : ℝ)) ≠ 0 by simp))
  filter_upwards [this] with x hx
  refine lt_of_le_of_ne (hT0 x) (fun h0 => hx ?_)
  simp [← h0]

private theorem tail_intervalIntegrable (hanti : Antitone T) (a b : ℝ) :
    IntervalIntegrable (fun u => u * T u) volume a b :=
  ((hanti.intervalIntegrable (a := a) (b := b) (μ := volume)).continuousOn_mul
    continuous_id.continuousOn : _)

private theorem incr_lower (hanti : Antitone T) {y : ℝ} (hy : 0 < y) :
    (3 / 8) * (y ^ 2 * T y) ≤ ∫ u in (y / 2)..y, u * T u := by
  have h1 : ∫ u in (y / 2)..y, u * T y = (3 / 8) * (y ^ 2 * T y) := by
    rw [intervalIntegral.integral_mul_const, integral_id]; ring
  rw [← h1]
  refine intervalIntegral.integral_mono_on (by linarith)
    ((continuous_id.mul continuous_const).intervalIntegrable _ _)
    (tail_intervalIntegrable hanti _ _)
    (fun u hu => mul_le_mul_of_nonneg_left (hanti hu.2) (by linarith [hu.1]))

private theorem incr_upper (hanti : Antitone T) {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    ∫ u in x..y, u * T u ≤ (y ^ 2 - x ^ 2) / 2 * T x := by
  have h1 : ∫ u in x..y, u * T x = (y ^ 2 - x ^ 2) / 2 * T x := by
    rw [intervalIntegral.integral_mul_const, integral_id]
  rw [← h1]
  refine intervalIntegral.integral_mono_on hxy (tail_intervalIntegrable hanti _ _)
    ((continuous_id.mul continuous_const).intervalIntegrable _ _)
    (fun u hu => mul_le_mul_of_nonneg_left (hanti hu.1) (by linarith [hu.1]))

private theorem I_mono (hanti : Antitone T) (hT0 : ∀ x, 0 ≤ T x) {a b : ℝ} (ha : 0 ≤ a)
    (hab : a ≤ b) :
    (∫ u in (0 : ℝ)..a, u * T u) ≤ ∫ u in (0 : ℝ)..b, u * T u := by
  have h := intervalIntegral.integral_interval_sub_left (tail_intervalIntegrable hanti 0 b)
    (tail_intervalIntegrable hanti 0 a)
  have h2 : 0 ≤ ∫ u in a..b, u * T u :=
    intervalIntegral.integral_nonneg hab (fun u hu => mul_nonneg (ha.trans hu.1) (hT0 u))
  linarith

private theorem L_half (hT : IsRegVaryAtTop T (-2)) :
    Tendsto (fun x : ℝ => ((x / 2) ^ 2 * T (x / 2)) / (x ^ 2 * T x)) atTop (𝓝 1) := by
  have h := hT (1 / 2) (by norm_num)
  have hv : ((1 : ℝ) / 2) ^ (-2 : ℝ) = 4 := by
    rw [Real.rpow_neg (by norm_num), Real.rpow_two]; norm_num
  rw [hv] at h
  have h2 := h.const_mul (1 / 4)
  rw [show (1 / 4 : ℝ) * 4 = 1 by norm_num] at h2
  refine h2.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  have : T (1 / 2 * x) = T (x / 2) := by congr 1; ring
  rw [this]
  field_simp
  norm_num

private theorem I_ge (hanti : Antitone T) (hT0 : ∀ x, 0 ≤ T x) (hT : IsRegVaryAtTop T (-2))
    (k : ℕ) : ∀ᶠ x : ℝ in atTop, (k / 4) * (x ^ 2 * T x) ≤ ∫ u in (0 : ℝ)..x, u * T u := by
  have hpos := tail_eventually_pos hT0 hT
  induction k with
  | zero =>
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    have : 0 ≤ ∫ u in (0 : ℝ)..x, u * T u :=
      intervalIntegral.integral_nonneg hx.le (fun u hu => mul_nonneg hu.1 (hT0 u))
    simpa using this
  | succ k ih =>
    have hk' : ∀ᶠ x : ℝ in atTop, (k / 4) * ((x / 2) ^ 2 * T (x / 2)) ≤
        ∫ u in (0 : ℝ)..(x / 2), u * T u :=
      (tendsto_id.atTop_div_const (two_pos : (0 : ℝ) < 2)).eventually ih
    have hr : ∀ᶠ x : ℝ in atTop, 1 - 1 / (2 * ((k : ℝ) + 1)) <
        ((x / 2) ^ 2 * T (x / 2)) / (x ^ 2 * T x) :=
      (L_half hT).eventually (lt_mem_nhds (by
        have : (0 : ℝ) < 1 / (2 * ((k : ℝ) + 1)) := by positivity
        linarith))
    filter_upwards [hk', hr, hpos, eventually_gt_atTop (0 : ℝ)] with x h1 h2 h3 h4
    have hLx : 0 < x ^ 2 * T x := by positivity
    rw [lt_div_iff₀ hLx] at h2
    have hsplit := intervalIntegral.integral_interval_sub_left (tail_intervalIntegrable hanti 0 x)
      (tail_intervalIntegrable hanti 0 (x / 2))
    have h5 := incr_lower hanti h4
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have h6 : (k : ℝ) * (1 / (2 * ((k : ℝ) + 1))) ≤ 1 / 2 := by
      rw [mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    push_cast
    nlinarith [mul_le_mul_of_nonneg_left h2.le hk0]

private theorem I_div_tendsto (hanti : Antitone T) (hT0 : ∀ x, 0 ≤ T x)
    (hT : IsRegVaryAtTop T (-2)) :
    Tendsto (fun x : ℝ => (∫ u in (0 : ℝ)..x, u * T u) / (x ^ 2 * T x)) atTop atTop := by
  have hpos := tail_eventually_pos hT0 hT
  rw [tendsto_atTop]
  intro b
  obtain ⟨k, hk⟩ := exists_nat_ge (4 * b)
  filter_upwards [I_ge hanti hT0 hT k, hpos, eventually_gt_atTop (0 : ℝ)] with x h1 h2 h3
  have hLx : 0 < x ^ 2 * T x := by positivity
  rw [le_div_iff₀ hLx]
  nlinarith

private theorem L_div_I_tendsto (hanti : Antitone T) (hT0 : ∀ x, 0 ≤ T x)
    (hT : IsRegVaryAtTop T (-2)) :
    Tendsto (fun x : ℝ => (x ^ 2 * T x) / ∫ u in (0 : ℝ)..x, u * T u) atTop (𝓝 0) := by
  have := (I_div_tendsto hanti hT0 hT).inv_tendsto_atTop
  refine this.congr (fun x => ?_)
  simp [inv_div]

private theorem I_pos_eventually (hanti : Antitone T) (hT0 : ∀ x, 0 ≤ T x)
    (hT : IsRegVaryAtTop T (-2)) : ∀ᶠ x : ℝ in atTop, 0 < ∫ u in (0 : ℝ)..x, u * T u := by
  have hpos := tail_eventually_pos hT0 hT
  filter_upwards [I_ge hanti hT0 hT 1, hpos, eventually_gt_atTop (0 : ℝ)] with x h1 h2 h3
  have : 0 < x ^ 2 * T x := by positivity
  push_cast at h1
  linarith

private theorem I_ratio_ge_one (hanti : Antitone T) (hT0 : ∀ x, 0 ≤ T x)
    (hT : IsRegVaryAtTop T (-2)) {c : ℝ} (hc : 1 ≤ c) :
    Tendsto (fun x : ℝ => (∫ u in (0 : ℝ)..(c * x), u * T u) / ∫ u in (0 : ℝ)..x, u * T u)
      atTop (𝓝 1) := by
  have hup : Tendsto (fun x : ℝ => 1 + (c ^ 2 - 1) / 2 *
      ((x ^ 2 * T x) / ∫ u in (0 : ℝ)..x, u * T u)) atTop (𝓝 1) := by
    have := (L_div_I_tendsto hanti hT0 hT).const_mul ((c ^ 2 - 1) / 2)
    simpa using this.const_add 1
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
  · filter_upwards [I_pos_eventually hanti hT0 hT, eventually_gt_atTop (0 : ℝ)] with x hI hx
    rw [le_div_iff₀ hI, one_mul]
    exact I_mono hanti hT0 hx.le (by nlinarith)
  · filter_upwards [I_pos_eventually hanti hT0 hT, eventually_gt_atTop (0 : ℝ)] with x hI hx
    have hsplit := intervalIntegral.integral_interval_sub_left
      (tail_intervalIntegrable hanti 0 (c * x)) (tail_intervalIntegrable hanti 0 x)
    have h := incr_upper hanti hx (show x ≤ c * x by nlinarith)
    rw [div_le_iff₀ hI]
    have e : (c * x) ^ 2 - x ^ 2 = (c ^ 2 - 1) * x ^ 2 := by ring
    rw [e] at h
    have e2 : (c ^ 2 - 1) * x ^ 2 / 2 * T x = (c ^ 2 - 1) / 2 * (x ^ 2 * T x) := by ring
    rw [e2] at h
    have e3 : (1 + (c ^ 2 - 1) / 2 * ((x ^ 2 * T x) / ∫ u in (0 : ℝ)..x, u * T u)) *
        (∫ u in (0 : ℝ)..x, u * T u) = (∫ u in (0 : ℝ)..x, u * T u) +
        (c ^ 2 - 1) / 2 * (x ^ 2 * T x) := by
      field_simp
    rw [e3]
    linarith

private theorem I_ratio (hanti : Antitone T) (hT0 : ∀ x, 0 ≤ T x)
    (hT : IsRegVaryAtTop T (-2)) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun x : ℝ => (∫ u in (0 : ℝ)..(c * x), u * T u) / ∫ u in (0 : ℝ)..x, u * T u)
      atTop (𝓝 1) := by
  rcases le_total 1 c with h | h
  · exact I_ratio_ge_one hanti hT0 hT h
  · have h1 := I_ratio_ge_one hanti hT0 hT (c := c⁻¹) (one_le_inv_iff₀.2 ⟨hc, h⟩)
    have h2 := h1.comp (tendsto_id.const_mul_atTop hc)
    have h3 := h2.inv₀ one_ne_zero
    rw [inv_one] at h3
    refine h3.congr (fun x => ?_)
    simp only [Function.comp, id, ← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul, inv_div]

end Abstract


/-! ## 2. Truncated second moments -/

section Truncated

variable {ν : Measure ℤ} [IsProbabilityMeasure ν]

omit [IsProbabilityMeasure ν] in
theorem truncSecondMoment_nonneg' (x : ℝ) : 0 ≤ truncSecondMoment ν x := by
  unfold truncSecondMoment
  exact setIntegral_nonneg MeasurableSet.of_discrete (fun z _ => sq_nonneg (z : ℝ))

private theorem integrableOn_sq_trunc {x : ℝ} (hx : 0 ≤ x) :
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

/-- `K = truncSecondMoment ν` is nondecreasing on all of `ℝ`. -/
theorem truncSecondMoment_mono : Monotone (truncSecondMoment (ν := ν)) := by
  intro x y hxy
  by_cases hx : 0 ≤ x
  · unfold truncSecondMoment
    refine setIntegral_mono_set (integrableOn_sq_trunc (hx.trans hxy))
      (ae_of_all _ fun z => sq_nonneg (z : ℝ)) (ae_of_all _ fun z hz => ?_)
    exact le_trans hz hxy
  · have : truncSecondMoment ν x = 0 := by
      have hs : {z : ℤ | |(z : ℝ)| ≤ x} = ∅ := by
        ext z
        simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_le]
        exact lt_of_lt_of_le (not_le.1 hx) (abs_nonneg _)
      unfold truncSecondMoment
      rw [hs]; simp
    rw [this]; exact truncSecondMoment_nonneg' y

omit [IsProbabilityMeasure ν] in
/-- `K(x) = K(⌊x⌋)`: the truncation level only matters through its integer part. -/
theorem truncSecondMoment_floor (x : ℝ) :
    truncSecondMoment ν x = truncSecondMoment ν (⌊x⌋ : ℝ) := by
  have hs : {z : ℤ | |(z : ℝ)| ≤ x} = {z : ℤ | |(z : ℝ)| ≤ (⌊x⌋ : ℝ)} := by
    ext z
    show |(z : ℝ)| ≤ x ↔ |(z : ℝ)| ≤ (⌊x⌋ : ℝ)
    rw [← Int.cast_abs]
    exact Int.le_floor.symm.trans Int.cast_le.symm
  unfold truncSecondMoment
  rw [hs]

/-- Infinite second moment forces `K → ∞`. -/
theorem truncSecondMoment_tendsto_atTop
    (hinf : ¬ Integrable (fun z : ℤ => (z : ℝ) ^ 2) ν) :
    Tendsto (truncSecondMoment ν) atTop atTop := by
  rw [tendsto_atTop]
  intro M
  by_contra hcon
  rw [not_eventually] at hcon
  have hev : ∃ᶠ x : ℝ in atTop, truncSecondMoment ν x < M := by
    simpa only [not_le] using hcon
  have hbound : ∀ n : ℕ, truncSecondMoment ν n ≤ max M 0 := by
    intro n
    have hlt : ∃ x : ℝ, (n : ℝ) ≤ x ∧ truncSecondMoment ν x < M := by
      obtain ⟨x, hx⟩ := (hev.and_eventually (eventually_ge_atTop (n : ℝ))).exists
      exact ⟨x, hx.2, hx.1⟩
    obtain ⟨x, hx, hxM⟩ := hlt
    exact (truncSecondMoment_mono hx).trans (hxM.le.trans (le_max_left _ _))
  let g : ℤ → ℝ≥0∞ := fun z => ENNReal.ofReal ((z : ℝ) ^ 2)
  let s : ℕ → Set ℤ := fun n => {z : ℤ | |(z : ℝ)| ≤ (n : ℝ)}
  have hsmono : Monotone s := by
    intro m n hmn z hz
    change |(z : ℝ)| ≤ (n : ℝ)
    exact le_trans hz (by exact_mod_cast hmn)
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

end Truncated

/-! ## 3. (B3-a) Tail regularly varying of index `-2` -/

section B3a

/-- **(B3-a)** Let `ν` be a probability law on `ℤ` with `ν {z < -1} = 0` and infinite second
moment.  If the right tail `T(x) = ν {z > x}` is regularly varying of index `-2`, then the truncated
second moment `K = truncSecondMoment ν` is slowly varying (ratio form `K(c x)/K(x) → 1`) and
unbounded.  (The proof does not use `T` beyond monotonicity and regular variation at the dyadic
points: `2 ∫₀ˣ u T = K + x² T - ν{-1}` and `x² T(x) = o(∫₀ˣ u T)`.) -/
theorem truncSecondMoment_slowlyVarying_of_regVary (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (hneg : ν {z : ℤ | z < -1} = 0)
    (hinf : ¬ Integrable (fun z : ℤ => (z : ℝ) ^ 2) ν)
    (hT : IsRegVaryAtTop (fun x : ℝ => ν.real {z : ℤ | x < (z : ℝ)}) (-2)) :
    SlowlyVarying (truncSecondMoment ν) ∧ Tendsto (truncSecondMoment ν) atTop atTop := by
  set T : ℝ → ℝ := fun x => ν.real {z : ℤ | x < (z : ℝ)} with hTdef
  have hd := QuantileInversion.tailData_of_regVary ν (θ := 2) two_pos hT
  have hT0 : ∀ x, 0 ≤ T x := hd.nonneg
  have hanti : Antitone T := hd.anti
  have hKinf := truncSecondMoment_tendsto_atTop hinf
  set I : ℝ → ℝ := fun x => ∫ u in (0 : ℝ)..x, u * T u with hIdef
  set c0 : ℝ := ν.real {(-1 : ℤ)} with hc0
  have hlc : ∀ x : ℝ, 1 ≤ x → truncSecondMoment ν x = 2 * I x - x ^ 2 * T x + c0 := by
    intro x hx
    have := layer_cake_trunc ν hneg hx
    simp only [hIdef, hTdef, hc0]
    linarith
  have hLI := L_div_I_tendsto hanti hT0 hT
  have hIpos := I_pos_eventually hanti hT0 hT
  have hIinf : Tendsto I atTop atTop := by
    refine tendsto_atTop_mono' atTop ?_
      ((tendsto_atTop_add_const_right atTop (-c0) hKinf).atTop_div_const (two_pos))
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    have := hlc x hx
    have hL : 0 ≤ x ^ 2 * T x := mul_nonneg (sq_nonneg x) (hT0 x)
    simp only [hIdef] at this ⊢
    show (truncSecondMoment ν x + -c0) / 2 ≤ I x
    simp only [hIdef]
    linarith
  have hKI : Tendsto (fun x => truncSecondMoment ν x / I x) atTop (𝓝 2) := by
    have h1 : Tendsto (fun x => 2 - (x ^ 2 * T x) / I x + c0 / I x) atTop (𝓝 (2 - 0 + 0)) :=
      ((tendsto_const_nhds.sub hLI).add (tendsto_const_nhds.div_atTop hIinf))
    rw [sub_zero, add_zero] at h1
    refine h1.congr' ?_
    filter_upwards [hIpos, eventually_ge_atTop (1 : ℝ)] with x hI hx
    have hI' : I x ≠ 0 := hI.ne'
    rw [hlc x hx]
    field_simp
  refine ⟨?_, hKinf⟩
  intro c hc
  have hcx : Tendsto (fun x : ℝ => c * x) atTop atTop := tendsto_id.const_mul_atTop hc
  have h1 := ((hKI.comp hcx).mul (I_ratio hanti hT0 hT hc)).div hKI (by norm_num)
  rw [show (2 : ℝ) * 1 / 2 = 1 by norm_num] at h1
  refine h1.congr' ?_
  have hIc := hcx.eventually hIpos
  filter_upwards [hIpos, hIc] with x hI hIcx
  simp only [Function.comp, Pi.div_apply, hIdef]
  have h1 := hI.ne'
  have h2 := hIcx.ne'
  field_simp

end B3a


/-! ## 4. (C3) The Gaussian crossing sequence -/

section C3

variable {ν : Measure ℤ} [IsProbabilityMeasure ν]

omit [IsProbabilityMeasure ν] in
private theorem truncSecondMoment_natFloor {x : ℝ} (hx : 0 ≤ x) :
    truncSecondMoment ν x = truncSecondMoment ν (⌊x⌋₊ : ℝ) := by
  rw [truncSecondMoment_floor]
  congr 1
  rw [← Int.natCast_floor_eq_floor hx]
  simp

omit [IsProbabilityMeasure ν] in
/-- `K` is not bounded below an infinite second moment: if `K → ∞` the second moment is infinite. -/
theorem not_integrable_of_tendsto_atTop
    (hKinf : Tendsto (truncSecondMoment ν) atTop atTop) :
    ¬ Integrable (fun z : ℤ => (z : ℝ) ^ 2) ν := by
  intro hint
  have hle : ∀ x : ℝ, truncSecondMoment ν x ≤ ∫ z, (z : ℝ) ^ 2 ∂ν := fun x =>
    setIntegral_le_integral hint (ae_of_all _ fun z => sq_nonneg (z : ℝ))
  obtain ⟨x, hx⟩ := (hKinf.eventually_gt_atTop (∫ z, (z : ℝ) ^ 2 ∂ν)).exists
  exact absurd (hle x) (not_le.2 hx)

private theorem K_div_sq_tendsto (hK : SlowlyVarying (truncSecondMoment ν)) :
    Tendsto (fun x : ℝ => truncSecondMoment ν x / x ^ 2) atTop (𝓝 0) := by
  have h := SlowVariation.slow_rpow_neg_mul_tendsto_zero (L := truncSecondMoment ν)
    (truncSecondMoment_mono (ν := ν)).measurable (fun x _ => truncSecondMoment_nonneg' x) hK
    (ε := 2) two_pos
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  rw [Real.rpow_neg hx.le, Real.rpow_two, inv_mul_eq_div]

/-- The set whose supremum defines `gaussQuantile`. -/
private def gaussSet (ν : Measure ℤ) (n : ℕ) : Set ℝ :=
  {z : ℝ | 0 ≤ z ∧ 1 / (n : ℝ) ≤ truncSecondMoment ν z / z ^ 2}

omit [IsProbabilityMeasure ν] in
private theorem gaussQuantile_eq (n : ℕ) : gaussQuantile ν n = sSup (gaussSet ν n) := rfl

private theorem gaussSet_bddAbove (hK : SlowlyVarying (truncSecondMoment ν)) {n : ℕ}
    (hn : 0 < n) : BddAbove (gaussSet ν n) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have h := (K_div_sq_tendsto hK).eventually
    (gt_mem_nhds (show (0 : ℝ) < 1 / (n : ℝ) by positivity))
  obtain ⟨X, hX⟩ := eventually_atTop.1 h
  refine ⟨X, fun z hz => ?_⟩
  by_contra hzX
  push Not at hzX
  exact absurd hz.2 (not_le.2 (hX z hzX.le))

omit [IsProbabilityMeasure ν] in
private theorem gaussSet_pos {n : ℕ} (hn : 0 < n) {z : ℝ} (hz : z ∈ gaussSet ν n) : 0 < z := by
  rcases hz.1.lt_or_eq with h | h
  · exact h
  · exfalso
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have := hz.2
    rw [← h] at this
    have h0 : truncSecondMoment ν 0 / (0 : ℝ) ^ 2 = 0 := by simp
    rw [h0] at this
    exact absurd this (not_le.2 (by positivity))

omit [IsProbabilityMeasure ν] in
private theorem eventually_mem_gaussSet {z0 : ℝ} (hz0 : 0 < z0)
    (hKz0 : 0 < truncSecondMoment ν z0) : ∀ᶠ n : ℕ in atTop, z0 ∈ gaussSet ν n := by
  have hr : 0 < truncSecondMoment ν z0 / z0 ^ 2 := div_pos hKz0 (by positivity)
  filter_upwards
    [(tendsto_one_div_atTop_nhds_zero_nat :
      Tendsto (fun n : ℕ => 1 / (n : ℝ)) atTop (𝓝 0)).eventually (gt_mem_nhds hr)]
    with n hn
  exact ⟨hz0.le, hn.le⟩

omit [IsProbabilityMeasure ν] in
private theorem exists_big (hKinf : Tendsto (truncSecondMoment ν) atTop atTop) (A : ℝ) :
    ∃ z : ℝ, max A 1 ≤ z ∧ 0 < truncSecondMoment ν z :=
  ((eventually_ge_atTop (max A 1)).and (hKinf.eventually_gt_atTop 0)).exists

/-- The crossing identity: if the crossing set is nonempty, `g_n² = n K(g_n)`. -/
private theorem gauss_eq (hK : SlowlyVarying (truncSecondMoment ν)) {n : ℕ} (hn : 0 < n)
    (hne : (gaussSet ν n).Nonempty) :
    0 < gaussQuantile ν n ∧
      gaussQuantile ν n ^ 2 = n * truncSecondMoment ν (gaussQuantile ν n) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  obtain ⟨z0, hz0⟩ := hne
  have hb := gaussSet_bddAbove hK hn
  set g := gaussQuantile ν n with hg
  have hgdef : g = sSup (gaussSet ν n) := rfl
  have hgz : ∀ z ∈ gaussSet ν n, z ≤ g := fun z hz => le_csSup hb hz
  have hgpos : 0 < g := (gaussSet_pos hn hz0).trans_le (hgz z0 hz0)
  refine ⟨hgpos, le_antisymm ?_ ?_⟩
  · have hup : ∀ z ∈ gaussSet ν n, z ≤ Real.sqrt (n * truncSecondMoment ν g) := by
      intro z hz
      have hzpos := gaussSet_pos hn hz
      have h1 : 1 / (n : ℝ) ≤ truncSecondMoment ν z / z ^ 2 := hz.2
      rw [div_le_div_iff₀ hnR (by positivity)] at h1
      have h2 : truncSecondMoment ν z ≤ truncSecondMoment ν g :=
        truncSecondMoment_mono (hgz z hz)
      have h3 : z ^ 2 ≤ n * truncSecondMoment ν g := by nlinarith
      exact (le_abs_self z).trans (Real.abs_le_sqrt h3)
    have h4 : g ≤ Real.sqrt (n * truncSecondMoment ν g) := csSup_le ⟨z0, hz0⟩ hup
    have h5 := pow_le_pow_left₀ hgpos.le h4 2
    rwa [Real.sq_sqrt (mul_nonneg hnR.le (truncSecondMoment_nonneg' _))] at h5
  · by_contra h
    push Not at h
    have hev1 : ∀ᶠ z in 𝓝[>] g, z ^ 2 < n * truncSecondMoment ν g :=
      (((continuous_pow 2).tendsto g).eventually (gt_mem_nhds h)).filter_mono nhdsWithin_le_nhds
    have hev2 : ∀ᶠ z in 𝓝[>] g, z < (⌊g⌋ : ℝ) + 1 :=
      ((gt_mem_nhds (Int.lt_floor_add_one g))).filter_mono nhdsWithin_le_nhds
    obtain ⟨z, h1, h2, h3⟩ := (hev1.and (hev2.and (self_mem_nhdsWithin : Ioi g ∈ 𝓝[>] g))).exists
    have h3' : g < z := h3
    have hnot : z ∉ gaussSet ν n := fun hz => absurd (hgz z hz) (not_le.2 h3')
    have hz0' : 0 < z := hgpos.trans h3'
    have hlt : truncSecondMoment ν z / z ^ 2 < 1 / (n : ℝ) := by
      by_contra hcon
      exact hnot ⟨hz0'.le, not_lt.1 hcon⟩
    have hfl : ⌊z⌋ = ⌊g⌋ := Int.floor_eq_iff.2 ⟨(Int.floor_le g).trans h3'.le, h2⟩
    have hKz : truncSecondMoment ν z = truncSecondMoment ν g := by
      rw [truncSecondMoment_floor z, truncSecondMoment_floor g, hfl]
    rw [hKz, div_lt_div_iff₀ (by positivity) hnR] at hlt
    nlinarith

private theorem gauss_eventually (hK : SlowlyVarying (truncSecondMoment ν))
    (hKinf : Tendsto (truncSecondMoment ν) atTop atTop) :
    ∀ᶠ n : ℕ in atTop, 0 < gaussQuantile ν n ∧
      gaussQuantile ν n ^ 2 = n * truncSecondMoment ν (gaussQuantile ν n) := by
  obtain ⟨z0, hz0, hKz0⟩ := exists_big hKinf 1
  have hz0pos : 0 < z0 := lt_of_lt_of_le one_pos ((le_max_right _ _).trans hz0)
  filter_upwards [eventually_mem_gaussSet hz0pos hKz0, eventually_gt_atTop 0] with n hn hn0
  exact gauss_eq hK hn0 ⟨z0, hn⟩

/-- `g_n → ∞`. -/
private theorem gauss_tendsto_atTop' (hK : SlowlyVarying (truncSecondMoment ν))
    (hKinf : Tendsto (truncSecondMoment ν) atTop atTop) :
    Tendsto (fun n : ℕ => gaussQuantile ν n) atTop atTop := by
  rw [tendsto_atTop]
  intro A
  obtain ⟨z0, hz0, hKz0⟩ := exists_big hKinf A
  have hz0pos : 0 < z0 := lt_of_lt_of_le one_pos ((le_max_right _ _).trans hz0)
  filter_upwards [eventually_mem_gaussSet hz0pos hKz0, eventually_gt_atTop 0] with n hn hn0
  exact ((le_max_left _ _).trans hz0).trans (le_csSup (gaussSet_bddAbove hK hn0) hn)

/-- Real-base Potter bound for `K`. -/
private theorem potter_real (hK : SlowlyVarying (truncSecondMoment ν))
    (hKinf : Tendsto (truncSecondMoment ν) atTop atTop) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∃ X : ℝ, 1 ≤ X ∧ ∀ x : ℝ, X ≤ x → ∀ y : ℝ, 1 ≤ y →
      truncSecondMoment ν (y * x) ≤ C * y ^ ε * truncSecondMoment ν x := by
  obtain ⟨C, hC1, N, hN⟩ := SlowVariation.slow_potter_nat (L := truncSecondMoment ν)
    (truncSecondMoment_mono (ν := ν)).measurable (fun x _ => truncSecondMoment_nonneg' x) hK hε
  obtain ⟨N', hN'⟩ := eventually_atTop.1
    ((hKinf.comp tendsto_natCast_atTop_atTop).eventually_gt_atTop 0)
  refine ⟨C * 2 ^ ε, by positivity, ((max N N' + 1 : ℕ) : ℝ), ?_, ?_⟩
  · have : (1 : ℝ) ≤ ((max N N' + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_left 1 _
    exact this
  intro x hx y hy
  set n := ⌊x⌋₊ with hn
  have hx0 : 0 ≤ x := le_trans (Nat.cast_nonneg _) hx
  have hnge : max N N' + 1 ≤ n := Nat.le_floor hx
  have hnN : N ≤ n := by omega
  have hnN' : N' ≤ n := by omega
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hKn : 0 < truncSecondMoment ν (n : ℝ) := hN' n hnN'
  have hxn : x < n + 1 := Nat.lt_floor_add_one x
  have hKx : truncSecondMoment ν x = truncSecondMoment ν (n : ℝ) := truncSecondMoment_natFloor hx0
  have hy0 : 0 ≤ y := by linarith
  have h1 : y * x ≤ (n : ℝ) * (2 * y) := by nlinarith
  have h2 := (hN n hnN (2 * y) (by linarith)).2
  rw [div_le_iff₀ hKn, Real.mul_rpow (by norm_num) hy0] at h2
  calc truncSecondMoment ν (y * x) ≤ truncSecondMoment ν ((n : ℝ) * (2 * y)) :=
        truncSecondMoment_mono h1
    _ ≤ C * (2 ^ ε * y ^ ε) * truncSecondMoment ν (n : ℝ) := h2
    _ = C * 2 ^ ε * y ^ ε * truncSecondMoment ν x := by rw [hKx]; ring

private theorem ratio_aux {p q N M KP KQ C y : ℝ} (hp : 0 < p) (hN : 0 < N) (hM : 0 < M)
    (hy1 : 1 ≤ y) (hq : q = y * p) (hpe : p ^ 2 = N * KP) (hqe : q ^ 2 = M * KQ)
    (hpot : KQ ≤ C * y * KP) : y * N ≤ C * M := by
  have hKP : 0 < KP := by
    have : 0 < N * KP := hpe ▸ pow_pos hp 2
    exact (mul_pos_iff_of_pos_left hN).1 this
  have hy0 : 0 < y := by linarith
  have h1 : y ^ 2 * N * KP ≤ M * (C * y * KP) := by
    calc y ^ 2 * N * KP = q ^ 2 := by rw [hq, mul_pow, hpe]; ring
      _ = M * KQ := hqe
      _ ≤ M * (C * y * KP) := mul_le_mul_of_nonneg_left hpot hM.le
  have h2 : y ^ 2 * N ≤ M * (C * y) :=
    le_of_mul_le_mul_right (by calc y ^ 2 * N * KP ≤ M * (C * y * KP) := h1
                                 _ = M * (C * y) * KP := by ring) hKP
  exact le_of_mul_le_mul_right (by calc y * N * y = y ^ 2 * N := by ring
                                       _ ≤ M * (C * y) := h2
                                       _ = C * M * y := by ring) hy0

/-- `g_{⌊l n⌋} / g_n → l^{1/2}` (the sequence `g_n` is regularly varying of index `1/2`). -/
private theorem gauss_ratio (hK : SlowlyVarying (truncSecondMoment ν))
    (hKinf : Tendsto (truncSecondMoment ν) atTop atTop) {l : ℝ} (hl : 0 < l) :
    Tendsto (fun n : ℕ => gaussQuantile ν ⌊l * n⌋₊ / gaussQuantile ν n) atTop
      (𝓝 (l ^ (1 / 2 : ℝ))) := by
  have hae := gauss_eventually hK hKinf
  have hat := gauss_tendsto_atTop' hK hKinf
  have hm : Tendsto (fun n : ℕ => ⌊l * n⌋₊) atTop atTop := tendsto_nat_floor_mul_atTop l hl
  have hmn : Tendsto (fun n : ℕ => ((⌊l * n⌋₊ : ℕ) : ℝ) / n) atTop (𝓝 l) :=
    (tendsto_nat_floor_mul_div_atTop hl.le).comp tendsto_natCast_atTop_atTop
  have hem := hm.eventually hae
  have hamt := hat.comp hm
  obtain ⟨C, hC, X, hX1, hX⟩ := potter_real hK hKinf one_pos
  simp only [Real.rpow_one] at hX
  have hmnb : ∀ᶠ n : ℕ in atTop, l / 2 < ((⌊l * n⌋₊ : ℕ) : ℝ) / n ∧
      ((⌊l * n⌋₊ : ℕ) : ℝ) / n < l + 1 :=
    hmn.eventually (Ioo_mem_nhds (by linarith) (by linarith))
  set δ : ℝ := min 1 (l / (2 * C)) with hδ
  set Δ : ℝ := max 1 (C * (l + 1)) with hΔ
  have hδ0 : 0 < δ := lt_min one_pos (by positivity)
  have hδΔ : δ ≤ Δ := (min_le_left _ _).trans (le_max_left _ _)
  have hbounds : ∀ᶠ n : ℕ in atTop, δ ≤ gaussQuantile ν ⌊l * n⌋₊ / gaussQuantile ν n ∧
      gaussQuantile ν ⌊l * n⌋₊ / gaussQuantile ν n ≤ Δ := by
    filter_upwards [hae, hem, hmnb, hat.eventually_ge_atTop X, hamt.eventually_ge_atTop X,
      eventually_gt_atTop 0, hm.eventually_gt_atTop 0] with n hn hmem hb hXn hXm hn0 hm0
    obtain ⟨hgn, hgne⟩ := hn
    obtain ⟨hgm, hgme⟩ := hmem
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
    have hmR : (0 : ℝ) < ((⌊l * n⌋₊ : ℕ) : ℝ) := by exact_mod_cast hm0
    obtain ⟨hb1, hb2⟩ := hb
    rw [div_lt_iff₀ hnR] at hb2
    rw [lt_div_iff₀ hnR] at hb1
    simp only [Function.comp] at hXm
    set m : ℕ := ⌊l * n⌋₊ with hmdef
    rcases le_total (gaussQuantile ν n) (gaussQuantile ν m) with h | h
    · set y := gaussQuantile ν m / gaussQuantile ν n with hy
      have hy1 : 1 ≤ y := by rw [hy, le_div_iff₀ hgn]; linarith
      have hqy : gaussQuantile ν m = y * gaussQuantile ν n := by
        rw [hy, div_mul_cancel₀ _ hgn.ne']
      have hpot := hX (gaussQuantile ν n) hXn y hy1
      rw [← hqy] at hpot
      have := ratio_aux hgn hnR hmR hy1 hqy hgne hgme hpot
      refine ⟨(min_le_left _ _).trans hy1, ?_⟩
      refine le_trans ?_ (le_max_right _ _)
      have key : y * n ≤ C * (l + 1) * n := by
        nlinarith [mul_le_mul_of_nonneg_left hb2.le hC.le]
      exact le_of_mul_le_mul_right key hnR
    · set y := gaussQuantile ν n / gaussQuantile ν m with hy
      have hy1 : 1 ≤ y := by rw [hy, le_div_iff₀ hgm]; linarith
      have hqy : gaussQuantile ν n = y * gaussQuantile ν m := by
        rw [hy, div_mul_cancel₀ _ hgm.ne']
      have hpot := hX (gaussQuantile ν m) hXm y hy1
      rw [← hqy] at hpot
      have h1 := ratio_aux hgm hmR hnR hy1 hqy hgme hgne hpot
      have hr1 : gaussQuantile ν m / gaussQuantile ν n ≤ 1 := by
        rw [div_le_one hgn]; exact h
      refine ⟨?_, hr1.trans (le_max_left _ _)⟩
      refine (min_le_right _ _).trans ?_
      rw [div_le_div_iff₀ (by positivity) hgn]
      have hyl : y * l ≤ 2 * C := by
        have key : y * l * n ≤ 2 * C * n := by
          nlinarith [mul_le_mul_of_nonneg_left hb1.le (show 0 ≤ y by linarith)]
        exact le_of_mul_le_mul_right key hnR
      rw [hy, div_mul_eq_mul_div, div_le_iff₀ hgm] at hyl
      nlinarith
  have hq : Tendsto (fun n : ℕ => truncSecondMoment ν (gaussQuantile ν ⌊l * n⌋₊) /
      truncSecondMoment ν (gaussQuantile ν n)) atTop (𝓝 1) := by
    refine Metric.tendsto_nhds.2 fun ε hε => ?_
    obtain ⟨X', hX'⟩ := SlowVariation.slow_uniform_convergence (L := truncSecondMoment ν)
      (truncSecondMoment_mono (ν := ν)).measurable (fun x _ => truncSecondMoment_nonneg' x) hK
      hδ0 hδΔ hε
    filter_upwards [hbounds, hat.eventually_ge_atTop X', hae] with n hb hgn hn
    have := hX' _ hgn (gaussQuantile ν ⌊l * n⌋₊ / gaussQuantile ν n) ⟨hb.1, hb.2⟩
    rw [div_mul_cancel₀ _ hn.1.ne'] at this
    rwa [Real.dist_eq]
  have hsq : Tendsto (fun n : ℕ => Real.sqrt (((⌊l * n⌋₊ : ℕ) : ℝ) / n *
      (truncSecondMoment ν (gaussQuantile ν ⌊l * n⌋₊) /
        truncSecondMoment ν (gaussQuantile ν n)))) atTop (𝓝 (Real.sqrt (l * 1))) :=
    (hmn.mul hq).sqrt
  rw [mul_one] at hsq
  rw [← Real.sqrt_eq_rpow]
  refine hsq.congr' ?_
  filter_upwards [hae, hem, eventually_gt_atTop 0, hm.eventually_gt_atTop 0] with n hn hmem hn0 hm0
  obtain ⟨hgn, hgne⟩ := hn
  obtain ⟨hgm, hgme⟩ := hmem
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  have hmR : (0 : ℝ) < ((⌊l * n⌋₊ : ℕ) : ℝ) := by exact_mod_cast hm0
  have hKn : truncSecondMoment ν (gaussQuantile ν n) ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hgne
    exact absurd hgne (pow_pos hgn 2).ne'
  have hsq' : (gaussQuantile ν ⌊l * n⌋₊ / gaussQuantile ν n) ^ 2 =
      ((⌊l * n⌋₊ : ℕ) : ℝ) / n * (truncSecondMoment ν (gaussQuantile ν ⌊l * n⌋₊) /
        truncSecondMoment ν (gaussQuantile ν n)) := by
    rw [div_pow, hgme, hgne]
    field_simp
  rw [← hsq', Real.sqrt_sq (div_nonneg hgm.le hgn.le)]


/-- **(C3-a)** If `K = truncSecondMoment ν` is slowly varying and unbounded, then eventually
`g_n = gaussQuantile ν n` is positive and the crossing is an equality:
`g_n² = n K(g_n)` (`K` is right continuous, being constant on `[k, k+1)`). -/
theorem gaussQuantile_sq_eventually (hK : SlowlyVarying (truncSecondMoment ν))
    (hKinf : Tendsto (truncSecondMoment ν) atTop atTop) :
    ∀ᶠ n : ℕ in atTop, 0 < gaussQuantile ν n ∧
      gaussQuantile ν n ^ 2 = n * truncSecondMoment ν (gaussQuantile ν n) :=
  gauss_eventually hK hKinf

/-- **(C3-b)** `g_n → ∞`, and hence `K(g_n) → ∞`. -/
theorem gaussQuantile_tendsto_atTop (hK : SlowlyVarying (truncSecondMoment ν))
    (hKinf : Tendsto (truncSecondMoment ν) atTop atTop) :
    Tendsto (fun n : ℕ => gaussQuantile ν n) atTop atTop :=
  gauss_tendsto_atTop' hK hKinf

theorem truncSecondMoment_gaussQuantile_tendsto_atTop
    (hK : SlowlyVarying (truncSecondMoment ν))
    (hKinf : Tendsto (truncSecondMoment ν) atTop atTop) :
    Tendsto (fun n : ℕ => truncSecondMoment ν (gaussQuantile ν n)) atTop atTop :=
  hKinf.comp (gauss_tendsto_atTop' hK hKinf)

/-- **(C3-c)** The Gaussian crossing sequence is regularly varying of index `1/2`:
`g_{⌊l n⌋} / g_n → l^{1/2}`. -/
theorem gaussQuantile_floor_div (hK : SlowlyVarying (truncSecondMoment ν))
    (hKinf : Tendsto (truncSecondMoment ν) atTop atTop) {l : ℝ} (hl : 0 < l) :
    Tendsto (fun n : ℕ => gaussQuantile ν ⌊l * n⌋₊ / gaussQuantile ν n) atTop
      (𝓝 (l ^ (1 / 2 : ℝ))) :=
  gauss_ratio hK hKinf hl

omit [IsProbabilityMeasure ν] in
private theorem norming_eq_aux (hinf : ¬ Integrable (fun z : ℤ => (z : ℝ) ^ 2) ν) (n : ℕ) :
    norming ν 2 n = Real.sqrt (n * truncSecondMoment ν (gaussQuantile ν n) / 2) := by
  simp only [norming, hinf, ite_false, lt_irrefl]

/-- **(C3-d)** Eventually `a_n = norming ν 2 n = g_n / √2` (since `g_n² = n K(g_n)`). -/
theorem norming_two_eventually_eq (hK : SlowlyVarying (truncSecondMoment ν))
    (hKinf : Tendsto (truncSecondMoment ν) atTop atTop) :
    ∀ᶠ n : ℕ in atTop, norming ν 2 n = gaussQuantile ν n / Real.sqrt 2 := by
  filter_upwards [gauss_eventually hK hKinf] with n hn
  rw [norming_eq_aux (not_integrable_of_tendsto_atTop hKinf), ← hn.2,
    Real.sqrt_div (sq_nonneg _), Real.sqrt_sq hn.1.le]

/-- **(C3-e)** The norming of the Gaussian branch is regularly varying of index `1/2`:
`a_{⌊l n⌋} / a_n → l^{1/2}`, for `a_n = norming ν 2 n = √(n K(g_n) / 2)`. -/
theorem norming_two_floor_div (hK : SlowlyVarying (truncSecondMoment ν))
    (hKinf : Tendsto (truncSecondMoment ν) atTop atTop) {l : ℝ} (hl : 0 < l) :
    Tendsto (fun n : ℕ => norming ν 2 ⌊l * n⌋₊ / norming ν 2 n) atTop
      (𝓝 (l ^ (1 / 2 : ℝ))) := by
  have hm : Tendsto (fun n : ℕ => ⌊l * n⌋₊) atTop atTop := tendsto_nat_floor_mul_atTop l hl
  refine (gauss_ratio hK hKinf hl).congr' ?_
  filter_upwards [norming_two_eventually_eq hK hKinf,
      hm.eventually (norming_two_eventually_eq hK hKinf),
    gauss_eventually hK hKinf] with n hn hmn hg
  rw [hn, hmn]
  have : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.2 (by norm_num)).ne'
  field_simp

end C3

end BGW.StableTrees.Attraction.GaussianBranch
