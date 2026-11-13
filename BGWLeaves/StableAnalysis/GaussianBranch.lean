module

public import BGWLeaves.StableAnalysis.MonotoneDensity
public import BGWLeaves.StableAnalysis.QuantileInversion
public import BGWLeaves.StableAnalysis.Defs
import Mathlib.MeasureTheory.Integral.Layercake

/-!
# The Gaussian branch (index `θ = 2`) of the stable analysis

Let `ν` be a probability law on `ℤ` with `ν {z < -1} = 0`, finite mean and infinite second moment,
`T(x) = ν {z > x}` and `K = truncSecondMoment ν`.

* (B3-a) `T` regularly varying of index `-2` implies that `K` is slowly varying and unbounded.
* If `K` is slowly varying and unbounded then `g_n = gaussQuantile ν n` satisfies
  `g_n² = n K(g_n)` eventually, `g_{⌊l n⌋} / g_n → l^{1/2}`, and the norming `a_n = norming ν 2 n`
  satisfies `a_{⌊l n⌋} / a_n → l^{1/2}`.
* (B3-b) If `K` is slowly varying and unbounded, then the integrated tail
  `∫₀ˣ ∫_u^∞ T ~ K(x)/2`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set intervalIntegral
open scoped Topology ENNReal

namespace BGWLeaves.StableAnalysis.GaussianBranch

open BGWLeaves.StableAnalysis BGWLeaves.StableAnalysis.MonotoneDensity BGW.StableTrees

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
    ((continuous_id.mul continuous_const).intervalIntegrable _ _) (tail_intervalIntegrable hanti _ _)
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
theorem truncSecondMoment_floor (x : ℝ) : truncSecondMoment ν x = truncSecondMoment ν (⌊x⌋ : ℝ) := by
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
    refine tendsto_atTop_mono' atTop ?_ ((tendsto_atTop_add_const_right atTop (-c0) hKinf).atTop_div_const (two_pos))
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


/-! ## 4. The Gaussian crossing sequence -/

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
  have h := (K_div_sq_tendsto hK).eventually (gt_mem_nhds (show (0 : ℝ) < 1 / (n : ℝ) by positivity))
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
  filter_upwards [(tendsto_one_div_atTop_nhds_zero_nat : Tendsto (fun n : ℕ => 1 / (n : ℝ)) atTop (𝓝 0)).eventually (gt_mem_nhds hr)]
    with n hn
  exact ⟨hz0.le, hn.le⟩

omit [IsProbabilityMeasure ν] in
private theorem exists_big (hKinf : Tendsto (truncSecondMoment ν) atTop atTop) (A : ℝ) :
    ∃ z : ℝ, max A 1 ≤ z ∧ 0 < truncSecondMoment ν z :=
  ((eventually_ge_atTop (max A 1)).and (hKinf.eventually_gt_atTop 0)).exists

/-- The crossing identity: if the crossing set is nonempty, `g_n² = n K(g_n)`. -/
private theorem gauss_eq (hK : SlowlyVarying (truncSecondMoment ν)) {n : ℕ} (hn : 0 < n)
    (hne : (gaussSet ν n).Nonempty) :
    0 < gaussQuantile ν n ∧ gaussQuantile ν n ^ 2 = n * truncSecondMoment ν (gaussQuantile ν n) := by
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


/-- If `K = truncSecondMoment ν` is slowly varying and unbounded, then eventually
`g_n = gaussQuantile ν n` is positive and the crossing is an equality:
`g_n² = n K(g_n)` (`K` is right continuous, being constant on `[k, k+1)`). -/
theorem gaussQuantile_sq_eventually (hK : SlowlyVarying (truncSecondMoment ν))
    (hKinf : Tendsto (truncSecondMoment ν) atTop atTop) :
    ∀ᶠ n : ℕ in atTop, 0 < gaussQuantile ν n ∧
      gaussQuantile ν n ^ 2 = n * truncSecondMoment ν (gaussQuantile ν n) :=
  gauss_eventually hK hKinf

/-- `g_n → ∞`, and hence `K(g_n) → ∞`. -/
theorem gaussQuantile_tendsto_atTop (hK : SlowlyVarying (truncSecondMoment ν))
    (hKinf : Tendsto (truncSecondMoment ν) atTop atTop) :
    Tendsto (fun n : ℕ => gaussQuantile ν n) atTop atTop :=
  gauss_tendsto_atTop' hK hKinf

theorem truncSecondMoment_gaussQuantile_tendsto_atTop
    (hK : SlowlyVarying (truncSecondMoment ν))
    (hKinf : Tendsto (truncSecondMoment ν) atTop atTop) :
    Tendsto (fun n : ℕ => truncSecondMoment ν (gaussQuantile ν n)) atTop atTop :=
  hKinf.comp (gauss_tendsto_atTop' hK hKinf)

/-- The Gaussian crossing sequence is regularly varying of index `1/2`:
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

/-- Eventually `a_n = norming ν 2 n = g_n / √2` (since `g_n² = n K(g_n)`). -/
theorem norming_two_eventually_eq (hK : SlowlyVarying (truncSecondMoment ν))
    (hKinf : Tendsto (truncSecondMoment ν) atTop atTop) :
    ∀ᶠ n : ℕ in atTop, norming ν 2 n = gaussQuantile ν n / Real.sqrt 2 := by
  filter_upwards [gauss_eventually hK hKinf] with n hn
  rw [norming_eq_aux (not_integrable_of_tendsto_atTop hKinf), ← hn.2,
    Real.sqrt_div (sq_nonneg _), Real.sqrt_sq hn.1.le]

/-- The norming of the Gaussian branch is regularly varying of index `1/2`:
`a_{⌊l n⌋} / a_n → l^{1/2}`, for `a_n = norming ν 2 n = √(n K(g_n) / 2)`. -/
theorem norming_two_floor_div (hK : SlowlyVarying (truncSecondMoment ν))
    (hKinf : Tendsto (truncSecondMoment ν) atTop atTop) {l : ℝ} (hl : 0 < l) :
    Tendsto (fun n : ℕ => norming ν 2 ⌊l * n⌋₊ / norming ν 2 n) atTop
      (𝓝 (l ^ (1 / 2 : ℝ))) := by
  have hm : Tendsto (fun n : ℕ => ⌊l * n⌋₊) atTop atTop := tendsto_nat_floor_mul_atTop l hl
  refine (gauss_ratio hK hKinf hl).congr' ?_
  filter_upwards [norming_two_eventually_eq hK hKinf, hm.eventually (norming_two_eventually_eq hK hKinf),
    gauss_eventually hK hKinf] with n hn hmn hg
  rw [hn, hmn]
  have : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.2 (by norm_num)).ne'
  field_simp

end C3


/-! ## 5. (B3-b) The integrated tail -/

section B3b

private theorem psi_integral {x : ℝ} (hx : 0 ≤ x) (z : ℝ) :
    ∫ u in (0 : ℝ)..x, max (z - u) 0 =
      if z ≤ 0 then 0 else if z ≤ x then z ^ 2 / 2 else x * z - x ^ 2 / 2 := by
  have hcont : Continuous (fun u : ℝ => max (z - u) 0) :=
    (continuous_const.sub continuous_id).max continuous_const
  have hlin : ∀ a b : ℝ, ∫ u in a..b, (z - u) = z * (b - a) - (b ^ 2 - a ^ 2) / 2 := by
    intro a b
    rw [intervalIntegral.integral_sub (by simp) (by simp)]
    simp [integral_id]
    ring
  split_ifs with h1 h2
  · rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ))]
    · simp
    · intro u hu
      rw [uIcc_of_le hx] at hu
      exact max_eq_right (by linarith [hu.1])
  · have hz : 0 ≤ z := by linarith
    rw [← intervalIntegral.integral_add_adjacent_intervals (b := z)
      (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _)]
    have e1 : ∫ u in (0 : ℝ)..z, max (z - u) 0 = z ^ 2 / 2 := by
      rw [intervalIntegral.integral_congr (g := fun u => z - u), hlin]
      · ring
      · intro u hu
        rw [uIcc_of_le hz] at hu
        exact max_eq_left (by linarith [hu.2])
    have e2 : ∫ u in z..x, max (z - u) 0 = 0 := by
      rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ))]
      · simp
      · intro u hu
        rw [uIcc_of_le (by linarith)] at hu
        exact max_eq_right (by linarith [hu.1])
    rw [e1, e2, add_zero]
  · push Not at h1 h2
    rw [intervalIntegral.integral_congr (g := fun u => z - u), hlin]
    · ring
    · intro u hu
      rw [uIcc_of_le hx] at hu
      exact max_eq_left (by linarith [hu.2])


variable {ν : Measure ℤ} [IsProbabilityMeasure ν]

omit [IsProbabilityMeasure ν] in
private theorem excess_fubini (hint : Integrable (fun z : ℤ => (z : ℝ)) ν) {x : ℝ} (hx : 0 ≤ x) :
    ∫ u in (0 : ℝ)..x, ∫ z, max ((z : ℝ) - u) 0 ∂ν =
      ∫ z, (∫ u in (0 : ℝ)..x, max ((z : ℝ) - u) 0) ∂ν := by
  have hcast : Measurable (fun z : ℤ => (z : ℝ)) := Measurable.of_discrete
  have hfm : Measurable (Function.uncurry (fun (u : ℝ) (z : ℤ) => max ((z : ℝ) - u) 0)) :=
    ((hcast.comp measurable_snd).sub measurable_fst).max measurable_const
  have hfin : IsFiniteMeasure (volume.restrict (uIoc (0 : ℝ) x)) := by
    rw [uIoc_of_le hx]; infer_instance
  have hg : Integrable (fun p : ℝ × ℤ => |(p.2 : ℝ)|) ((volume.restrict (uIoc (0 : ℝ) x)).prod ν) :=
    (hint.abs.comp_snd (volume.restrict (uIoc (0 : ℝ) x)))
  have hint2 : Integrable (Function.uncurry (fun (u : ℝ) (z : ℤ) => max ((z : ℝ) - u) 0))
      ((volume.restrict (uIoc (0 : ℝ) x)).prod ν) := by
    refine hg.mono' hfm.aestronglyMeasurable ?_
    have hms : MeasurableSet {p : ℝ × ℤ |
        ‖Function.uncurry (fun (u : ℝ) (z : ℤ) => max ((z : ℝ) - u) 0) p‖ ≤ |(p.2 : ℝ)|} :=
      measurableSet_le hfm.norm (continuous_abs.measurable.comp (hcast.comp measurable_snd))
    rw [Measure.ae_prod_iff_ae_ae hms]
    rw [uIoc_of_le hx]
    refine (ae_restrict_iff' measurableSet_Ioc).mpr (ae_of_all _ (fun u hu => ae_of_all _ (fun z => ?_)))
    simp only [Function.uncurry]
    rw [Real.norm_of_nonneg (le_max_right _ _)]
    refine max_le ?_ (abs_nonneg _)
    linarith [le_abs_self (z : ℝ), hu.1]
  exact intervalIntegral_integral_swap hint2


private theorem excess_decomp (hneg : ν {z : ℤ | z < -1} = 0)
    (hint : Integrable (fun z : ℤ => (z : ℝ)) ν) {x : ℝ} (hx : 1 ≤ x) :
    ∫ u in (0 : ℝ)..x, ∫ z, max ((z : ℝ) - u) 0 ∂ν =
      truncSecondMoment ν x / 2 - ν.real {(-1 : ℤ)} / 2 +
        ∫ z in {z : ℤ | x < (z : ℝ)}, ((x * (z : ℝ) - x ^ 2 / 2)) ∂ν := by
  have hx0 : 0 ≤ x := by linarith
  rw [excess_fubini hint hx0]
  have hnull : ∀ᵐ z ∂ν, ¬ z < -1 := by
    rw [ae_iff]; simpa using hneg
  set a : ℤ → ℝ := ({z : ℤ | |(z : ℝ)| ≤ x}).indicator (fun z => (z : ℝ) ^ 2) with ha
  set b : ℤ → ℝ := ({z : ℤ | x < (z : ℝ)}).indicator (fun z => x * (z : ℝ) - x ^ 2 / 2) with hb
  set c : ℤ → ℝ := ({(-1 : ℤ)} : Set ℤ).indicator (fun _ => (1 : ℝ)) with hc
  have hpt : ∀ᵐ z : ℤ ∂ν, (∫ u in (0 : ℝ)..x, max ((z : ℝ) - u) 0) = a z / 2 - c z / 2 + b z := by
    filter_upwards [hnull] with z hz
    have hz' : (-1 : ℤ) ≤ z := not_lt.mp hz
    rw [psi_integral hx0]
    obtain rfl | rfl | h1 : z = -1 ∨ z = 0 ∨ 1 ≤ z := by omega
    · simp [ha, hb, hc, Set.indicator_apply, hx]
      intro h; linarith
    · simp [ha, hb, hc, Set.indicator_apply]
      intro h; linarith
    · have hz1 : (1 : ℝ) ≤ z := by exact_mod_cast h1
      have hne : ¬ (z = -1) := by omega
      have hza : |(z : ℝ)| = z := abs_of_nonneg (by linarith)
      have hc0 : ¬ ((z : ℝ) ≤ 0) := by linarith
      simp only [hc0, ↓reduceIte]
      by_cases hzx : (z : ℝ) ≤ x
      · simp only [hzx, ↓reduceIte]
        simp [ha, hb, hc, hza, hzx, not_lt.mpr hzx, hne]
      · simp only [hzx, ↓reduceIte]
        push Not at hzx
        simp [ha, hb, hc, hza, hzx, not_le.mpr hzx, hne]
  have hbd : ∀ z : ℤ, ‖a z‖ ≤ x ^ 2 := by
    intro z
    simp only [ha, Set.indicator_apply, Set.mem_ofPred_eq]
    split_ifs with h
    · rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      nlinarith [abs_nonneg (z : ℝ), sq_abs (z : ℝ)]
    · simp; positivity
  have hia : Integrable a ν :=
    Integrable.of_bound (Measurable.of_discrete).aestronglyMeasurable (x ^ 2) (ae_of_all _ hbd)
  have hib : Integrable b ν :=
    ((hint.const_mul x).sub (integrable_const (x ^ 2 / 2))).indicator MeasurableSet.of_discrete
  have hic : Integrable c ν := (integrable_const _).indicator MeasurableSet.of_discrete
  have hi1 : Integrable (fun z => a z / 2 - c z / 2) ν := (hia.div_const 2).sub (hic.div_const 2)
  have hi2 : Integrable (fun z => a z / 2) ν := hia.div_const 2
  have hi3 : Integrable (fun z => c z / 2) ν := hic.div_const 2
  rw [integral_congr_ae hpt, integral_add hi1 hib, integral_sub hi2 hi3,
    MeasureTheory.integral_div, MeasureTheory.integral_div]
  have e1 : ∫ z, a z ∂ν = truncSecondMoment ν x := by
    rw [ha, MeasureTheory.integral_indicator MeasurableSet.of_discrete]; rfl
  have e2 : ∫ z, b z ∂ν = ∫ z in {z : ℤ | x < (z : ℝ)}, (x * (z : ℝ) - x ^ 2 / 2) ∂ν := by
    rw [hb, MeasureTheory.integral_indicator MeasurableSet.of_discrete]
  have e3 : ∫ z, c z ∂ν = ν.real {(-1 : ℤ)} := by
    rw [hc, integral_indicator_const _ MeasurableSet.of_discrete, smul_eq_mul, mul_one]
  rw [e1, e2, e3]


/-- `∫_{z > x} z dν`. -/
private noncomputable def meanAbove (ν : Measure ℤ) (x : ℝ) : ℝ :=
  ∫ z in {z : ℤ | x < (z : ℝ)}, (z : ℝ) ∂ν

omit [IsProbabilityMeasure ν] in
private theorem meanAbove_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ meanAbove ν x := by
  unfold meanAbove
  refine setIntegral_nonneg MeasurableSet.of_discrete (fun z hz => ?_)
  have : x < (z : ℝ) := hz
  linarith

/-- One dyadic step: `x · E[Z; Z > x] ≤ K(2x) - K(x) + x · E[Z; Z > 2x]` for `x ≥ 1`. -/
private theorem meanAbove_step (hint : Integrable (fun z : ℤ => (z : ℝ)) ν) {x : ℝ} (hx : 1 ≤ x) :
    x * meanAbove ν x ≤ truncSecondMoment ν (2 * x) - truncSecondMoment ν x +
      x * meanAbove ν (2 * x) := by
  have hx0 : 0 < x := by linarith
  set A : Set ℤ := {z : ℤ | x < (z : ℝ) ∧ (z : ℝ) ≤ 2 * x} with hA
  set B : Set ℤ := {z : ℤ | 2 * x < (z : ℝ)} with hB
  set S1 : Set ℤ := {z : ℤ | |(z : ℝ)| ≤ x} with hS1
  set S2 : Set ℤ := {z : ℤ | |(z : ℝ)| ≤ 2 * x} with hS2
  have hsplit : {z : ℤ | x < (z : ℝ)} = A ∪ B := by
    ext z
    simp only [hA, hB, Set.mem_union, Set.mem_ofPred_eq]
    constructor
    · intro h
      rcases le_or_gt (z : ℝ) (2 * x) with h2 | h2
      · exact Or.inl ⟨h, h2⟩
      · exact Or.inr h2
    · rintro (h | h)
      · exact h.1
      · linarith
  have hdisj : Disjoint A B := by
    rw [Set.disjoint_left]
    intro z hzA hzB
    have h1 : (z : ℝ) ≤ 2 * x := hzA.2
    have h2 : 2 * x < (z : ℝ) := hzB
    linarith
  have hAS2 : A ⊆ S2 := by
    intro z hz
    have h1 : x < (z : ℝ) := hz.1
    have h2 : (z : ℝ) ≤ 2 * x := hz.2
    show |(z : ℝ)| ≤ 2 * x
    rw [abs_of_pos (by linarith)]; exact h2
  have hdisj2 : Disjoint S1 A := by
    rw [Set.disjoint_left]
    intro z hz1 hzA
    have h1 : |(z : ℝ)| ≤ x := hz1
    have h2 : x < (z : ℝ) := hzA.1
    linarith [le_abs_self (z : ℝ)]
  have hS1S2 : S1 ⊆ S2 := fun z hz => le_trans (show |(z : ℝ)| ≤ x from hz) (by linarith)
  have hint1 : IntegrableOn (fun z : ℤ => (z : ℝ) ^ 2) S1 ν := integrableOn_sq_trunc hx0.le
  have hint2 : IntegrableOn (fun z : ℤ => (z : ℝ) ^ 2) S2 ν := integrableOn_sq_trunc (by linarith)
  have hintA : IntegrableOn (fun z : ℤ => (z : ℝ) ^ 2) A ν := hint2.mono_set hAS2
  -- the mass on `A`
  have hmassA : x * ∫ z in A, (z : ℝ) ∂ν ≤ truncSecondMoment ν (2 * x) - truncSecondMoment ν x := by
    have h1 : x * ∫ z in A, (z : ℝ) ∂ν ≤ ∫ z in A, (z : ℝ) ^ 2 ∂ν := by
      rw [← MeasureTheory.integral_const_mul]
      refine setIntegral_mono_on ((hint.const_mul x).integrableOn) hintA MeasurableSet.of_discrete
        (fun z hz => ?_)
      have h1 : x < (z : ℝ) := hz.1
      nlinarith
    have h2 : (∫ z in S1, (z : ℝ) ^ 2 ∂ν) + ∫ z in A, (z : ℝ) ^ 2 ∂ν ≤
        ∫ z in S2, (z : ℝ) ^ 2 ∂ν := by
      rw [← setIntegral_union hdisj2 MeasurableSet.of_discrete hint1 hintA]
      exact setIntegral_mono_set hint2 (ae_of_all _ fun z => sq_nonneg (z : ℝ))
        (ae_of_all _ (Set.union_subset hS1S2 hAS2))
    have e1 : truncSecondMoment ν x = ∫ z in S1, (z : ℝ) ^ 2 ∂ν := rfl
    have e2 : truncSecondMoment ν (2 * x) = ∫ z in S2, (z : ℝ) ^ 2 ∂ν := rfl
    linarith
  unfold meanAbove
  rw [hsplit, setIntegral_union hdisj MeasurableSet.of_discrete hint.integrableOn hint.integrableOn,
    mul_add]
  have : {z : ℤ | 2 * x < (z : ℝ)} = B := rfl
  rw [this]
  linarith


private theorem meanAbove_iter (hint : Integrable (fun z : ℤ => (z : ℝ)) ν) (k : ℕ) :
    ∀ x : ℝ, 1 ≤ x → x * meanAbove ν x ≤
      ∑ j ∈ Finset.range k, (1 / 2 : ℝ) ^ j *
        (truncSecondMoment ν (2 ^ (j + 1) * x) - truncSecondMoment ν (2 ^ j * x)) +
      x * meanAbove ν (2 ^ k * x) := by
  induction k with
  | zero => intro x hx; simp
  | succ k ih =>
    intro x hx
    have h1 := meanAbove_step hint hx
    have h2 := ih (2 * x) (by linarith)
    simp only [show ∀ j : ℕ, (2 : ℝ) ^ (j + 1) * (2 * x) = 2 ^ (j + 1 + 1) * x from
      fun j => by ring, show ∀ j : ℕ, (2 : ℝ) ^ j * (2 * x) = 2 ^ (j + 1) * x from
      fun j => by ring] at h2
    rw [Finset.sum_range_succ']
    have e : ∑ j ∈ Finset.range k, (1 / 2 : ℝ) ^ (j + 1) *
        (truncSecondMoment ν (2 ^ (j + 1 + 1) * x) - truncSecondMoment ν (2 ^ (j + 1) * x)) =
        (1 / 2) * ∑ j ∈ Finset.range k, (1 / 2 : ℝ) ^ j *
          (truncSecondMoment ν (2 ^ (j + 1 + 1) * x) - truncSecondMoment ν (2 ^ (j + 1) * x)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [pow_succ]; ring
    rw [e]
    simp only [pow_zero, zero_add, pow_one, one_mul]
    linarith

omit [IsProbabilityMeasure ν] in
private theorem meanAbove_tendsto_zero (hint : Integrable (fun z : ℤ => (z : ℝ)) ν) {y : ℝ}
    (hy : 0 < y) : Tendsto (fun k : ℕ => meanAbove ν (2 ^ k * y)) atTop (𝓝 0) := by
  have hF : ∀ k : ℕ, meanAbove ν (2 ^ k * y) =
      ∫ z, ({z : ℤ | 2 ^ k * y < (z : ℝ)}).indicator (fun z : ℤ => (z : ℝ)) z ∂ν := by
    intro k
    unfold meanAbove
    rw [MeasureTheory.integral_indicator MeasurableSet.of_discrete]
  simp_rw [hF]
  have h := tendsto_integral_of_dominated_convergence (μ := ν)
    (F := fun (k : ℕ) (z : ℤ) => ({z : ℤ | 2 ^ k * y < (z : ℝ)}).indicator (fun z : ℤ => (z : ℝ)) z)
    (f := fun _ => (0 : ℝ)) (bound := fun z : ℤ => |(z : ℝ)|)
    (fun k => (measurable_of_countable _).aestronglyMeasurable) hint.abs
    (fun k => ae_of_all _ fun z => by
      by_cases hz : z ∈ {z : ℤ | 2 ^ k * y < (z : ℝ)}
      · rw [Set.indicator_of_mem hz]; simp
      · rw [Set.indicator_of_notMem hz]; simp)
    (ae_of_all _ fun z => by
      have hlim : Tendsto (fun k : ℕ => (2 : ℝ) ^ k * y) atTop atTop :=
        (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).atTop_mul_const hy
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [hlim.eventually_ge_atTop (z : ℝ)] with k hk
      rw [Set.indicator_of_notMem (by simpa using hk)])
  simpa using h

private theorem potter_dyadic (hK : SlowlyVarying (truncSecondMoment ν))
    (hKinf : Tendsto (truncSecondMoment ν) atTop atTop) :
    ∃ C : ℝ, 0 < C ∧ ∃ X : ℝ, 1 ≤ X ∧ ∀ x : ℝ, X ≤ x → ∀ j : ℕ,
      truncSecondMoment ν (2 ^ j * x) ≤ C * (3 / 2 : ℝ) ^ j * truncSecondMoment ν x := by
  obtain ⟨C, hC, X, hX1, hX⟩ := potter_real hK hKinf (ε := 1 / 2) (by norm_num)
  refine ⟨C, hC, X, hX1, fun x hx j => ?_⟩
  have h := hX x hx (2 ^ j) (one_le_pow₀ (by norm_num))
  refine h.trans ?_
  have hs : ((2 : ℝ) ^ j) ^ (1 / 2 : ℝ) ≤ (3 / 2) ^ j := by
    rw [← Real.sqrt_eq_rpow]
    refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
    rw [← pow_mul, mul_comm, pow_mul]
    exact pow_le_pow_left₀ (by norm_num) (by norm_num) j
  have hK0 := truncSecondMoment_nonneg' (ν := ν) x
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hs hC.le) hK0


private theorem geom_three_quarters (k : ℕ) : ∑ j ∈ Finset.range k, (3 / 4 : ℝ) ^ j ≤ 4 := by
  rw [geom_sum_eq (by norm_num : (3 / 4 : ℝ) ≠ 1) k]
  have h : (0 : ℝ) ≤ (3 / 4) ^ k := by positivity
  rw [div_le_iff_of_neg (by norm_num)]
  linarith

/-- A priori bound `y E[Z; Z > y] ≤ C₁ K(y)` for `K` slowly varying. -/
private theorem meanAbove_apriori (hint : Integrable (fun z : ℤ => (z : ℝ)) ν)
    (hK : SlowlyVarying (truncSecondMoment ν))
    (hKinf : Tendsto (truncSecondMoment ν) atTop atTop) :
    ∃ C₁ : ℝ, ∃ X₁ : ℝ, 1 ≤ X₁ ∧ ∀ y : ℝ, X₁ ≤ y →
      y * meanAbove ν y ≤ C₁ * truncSecondMoment ν y := by
  obtain ⟨C, hC, X, hX1, hX⟩ := potter_dyadic hK hKinf
  refine ⟨6 * C, X, hX1, fun y hy => ?_⟩
  have hy1 : 1 ≤ y := hX1.trans hy
  have hy0 : 0 < y := by linarith
  have hK0 := truncSecondMoment_nonneg' (ν := ν) y
  have hbound : ∀ k : ℕ, y * meanAbove ν y ≤ 6 * C * truncSecondMoment ν y +
      y * meanAbove ν (2 ^ k * y) := by
    intro k
    refine (meanAbove_iter hint k y hy1).trans ?_
    have hsum : ∑ j ∈ Finset.range k, (1 / 2 : ℝ) ^ j *
        (truncSecondMoment ν (2 ^ (j + 1) * y) - truncSecondMoment ν (2 ^ j * y)) ≤
        ∑ j ∈ Finset.range k, (3 * C / 2 * truncSecondMoment ν y) * (3 / 4 : ℝ) ^ j := by
      refine Finset.sum_le_sum (fun j _ => ?_)
      have h1 := hX y hy (j + 1)
      have h2 := truncSecondMoment_nonneg' (ν := ν) (2 ^ j * y)
      have h3 : (1 / 2 : ℝ) ^ j * ((3 / 2 : ℝ) ^ (j + 1)) = 3 / 2 * (3 / 4 : ℝ) ^ j := by
        rw [pow_succ, show (3 / 4 : ℝ) = 1 / 2 * (3 / 2) by norm_num, mul_pow]; ring
      calc (1 / 2 : ℝ) ^ j * (truncSecondMoment ν (2 ^ (j + 1) * y) - truncSecondMoment ν (2 ^ j * y))
          ≤ (1 / 2 : ℝ) ^ j * (C * (3 / 2 : ℝ) ^ (j + 1) * truncSecondMoment ν y) :=
            mul_le_mul_of_nonneg_left (by linarith) (by positivity)
        _ = (3 * C / 2 * truncSecondMoment ν y) * (3 / 4 : ℝ) ^ j := by
            rw [← mul_assoc, mul_comm ((1 / 2 : ℝ) ^ j), mul_assoc C, ← mul_assoc C]
            calc _ = C * ((1 / 2 : ℝ) ^ j * (3 / 2 : ℝ) ^ (j + 1)) * truncSecondMoment ν y := by ring
              _ = _ := by rw [h3]; ring
    rw [← Finset.mul_sum] at hsum
    have := geom_three_quarters k
    have h4 : 3 * C / 2 * truncSecondMoment ν y * ∑ j ∈ Finset.range k, (3 / 4 : ℝ) ^ j ≤
        3 * C / 2 * truncSecondMoment ν y * 4 :=
      mul_le_mul_of_nonneg_left this (by positivity)
    linarith
  have hlim : Tendsto (fun k : ℕ => 6 * C * truncSecondMoment ν y + y * meanAbove ν (2 ^ k * y))
      atTop (𝓝 (6 * C * truncSecondMoment ν y + y * 0)) :=
    tendsto_const_nhds.add ((meanAbove_tendsto_zero hint hy0).const_mul y)
  rw [mul_zero, add_zero] at hlim
  exact ge_of_tendsto' hlim hbound

/-- `x E[Z; Z > x] = o(K(x))` if `K` is slowly varying and unbounded (`ν` of finite mean). -/
private theorem meanAbove_isLittleO (hint : Integrable (fun z : ℤ => (z : ℝ)) ν)
    (hK : SlowlyVarying (truncSecondMoment ν))
    (hKinf : Tendsto (truncSecondMoment ν) atTop atTop) :
    Tendsto (fun x : ℝ => x * meanAbove ν x / truncSecondMoment ν x) atTop (𝓝 0) := by
  obtain ⟨C, hC, X, hX1, hX⟩ := potter_dyadic hK hKinf
  obtain ⟨C₁, X₁, hX₁1, hX₁⟩ := meanAbove_apriori hint hK hKinf
  rw [Metric.tendsto_nhds]
  intro ε hε
  -- choose `J`
  have hC1 : 0 ≤ |C₁| * C := by positivity
  obtain ⟨J, hJ⟩ := ((tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 3 / 4)
    (by norm_num : (3 / 4 : ℝ) < 1)).const_mul (|C₁| * C)).eventually
    (gt_mem_nhds (show (|C₁| * C) * 0 < ε / 2 by simpa using half_pos hε)) |>.exists
  have hJ' : |C₁| * C * (3 / 4 : ℝ) ^ J < ε / 2 := hJ
  have hS : Tendsto (fun x : ℝ => ∑ j ∈ Finset.range J, (1 / 2 : ℝ) ^ j *
      (truncSecondMoment ν (2 ^ (j + 1) * x) / truncSecondMoment ν x -
        truncSecondMoment ν (2 ^ j * x) / truncSecondMoment ν x)) atTop (𝓝 0) := by
    have := tendsto_finsetSum (Finset.range J) (fun j _ =>
      (((hK (2 ^ (j + 1)) (by positivity)).sub (hK (2 ^ j) (by positivity))).const_mul
        ((1 / 2 : ℝ) ^ j)))
    simpa using this
  filter_upwards [hS.eventually (gt_mem_nhds (half_pos hε)), eventually_ge_atTop (max X X₁),
    hKinf.eventually_gt_atTop 0] with x hSx hx hKx
  have hxX : X ≤ x := (le_max_left _ _).trans hx
  have hxX₁ : X₁ ≤ x := (le_max_right _ _).trans hx
  have hx1 : 1 ≤ x := hX1.trans hxX
  have hR0 : 0 ≤ x * meanAbove ν x := mul_nonneg (by linarith) (meanAbove_nonneg (by linarith))
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (div_nonneg hR0 hKx.le), div_lt_iff₀ hKx]
  have hit := meanAbove_iter hint J x hx1
  -- the remainder term
  set y := 2 ^ J * x with hy
  have hxy : x ≤ y := by
    have : (1 : ℝ) ≤ 2 ^ J := one_le_pow₀ (by norm_num)
    nlinarith
  have hrem : x * meanAbove ν y ≤ |C₁| * C * (3 / 4 : ℝ) ^ J * truncSecondMoment ν x := by
    have h1 := hX₁ y (hxX₁.trans hxy)
    have h2' : (1 / 2 : ℝ) ^ J * y = x := by
      rw [hy, ← mul_assoc, ← mul_pow]; norm_num
    have h2 : x * meanAbove ν y = (1 / 2 : ℝ) ^ J * (y * meanAbove ν y) := by
      rw [← mul_assoc, h2']
    have h3 := hX x hxX J
    have hy0 : 0 ≤ truncSecondMoment ν y := truncSecondMoment_nonneg' _
    have h4 : (1 / 2 : ℝ) ^ J * (3 / 2 : ℝ) ^ J = (3 / 4 : ℝ) ^ J := by
      rw [← mul_pow]; norm_num
    rw [h2]
    calc (1 / 2 : ℝ) ^ J * (y * meanAbove ν y)
        ≤ (1 / 2 : ℝ) ^ J * (C₁ * truncSecondMoment ν y) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ ≤ (1 / 2 : ℝ) ^ J * (|C₁| * truncSecondMoment ν y) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (le_abs_self _) hy0) (by positivity)
      _ ≤ (1 / 2 : ℝ) ^ J * (|C₁| * (C * (3 / 2 : ℝ) ^ J * truncSecondMoment ν x)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (by rw [hy]; exact h3)
            (abs_nonneg _)) (by positivity)
      _ = |C₁| * C * ((1 / 2 : ℝ) ^ J * (3 / 2 : ℝ) ^ J) * truncSecondMoment ν x := by ring
      _ = _ := by rw [h4]
  have hsumeq : ∑ j ∈ Finset.range J, (1 / 2 : ℝ) ^ j *
      (truncSecondMoment ν (2 ^ (j + 1) * x) - truncSecondMoment ν (2 ^ j * x)) =
      truncSecondMoment ν x * ∑ j ∈ Finset.range J, (1 / 2 : ℝ) ^ j *
      (truncSecondMoment ν (2 ^ (j + 1) * x) / truncSecondMoment ν x -
        truncSecondMoment ν (2 ^ j * x) / truncSecondMoment ν x) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    field_simp
  rw [hsumeq] at hit
  have hfin : x * meanAbove ν x ≤ truncSecondMoment ν x * (∑ j ∈ Finset.range J, (1 / 2 : ℝ) ^ j *
      (truncSecondMoment ν (2 ^ (j + 1) * x) / truncSecondMoment ν x -
        truncSecondMoment ν (2 ^ j * x) / truncSecondMoment ν x)) +
      |C₁| * C * (3 / 4 : ℝ) ^ J * truncSecondMoment ν x := by linarith
  nlinarith


/-- **(B3-b)** Let `ν` be a probability law on `ℤ` with `ν {z < -1} = 0` and finite mean, such that
`K = truncSecondMoment ν` is slowly varying and unbounded.  Then the integrated tail
`J(x) = ∫₀ˣ E[(Z - u)⁺] du` (`E[(Z-u)⁺] = ∫_u^∞ ν{z > v} dv`, see
`integral_max_sub_eq_integral_tail`) satisfies `J(x) / (K(x)/2) → 1`.

Use: for the Laplace transform `ℓ(s) = E e^{-s Z}` one has the exact identity
`ℓ(s) - 1 + m s = s² ∫₀^∞ e^{-su} E[(Z-u)⁺] du + (explicit atom at -1)`, so (via the
Laplace–Karamata Abelian theorem applied to `U = J`) `ℓ(s) - 1 + m s ~ s² J(1/s) ~ s² K(1/s) / 2`
as `s → 0+`. -/
theorem integratedTail_div_tendsto (hneg : ν {z : ℤ | z < -1} = 0)
    (hint : Integrable (fun z : ℤ => (z : ℝ)) ν)
    (hK : SlowlyVarying (truncSecondMoment ν))
    (hKinf : Tendsto (truncSecondMoment ν) atTop atTop) :
    Tendsto (fun x : ℝ => (∫ u in (0 : ℝ)..x, ∫ z, max ((z : ℝ) - u) 0 ∂ν) /
      (truncSecondMoment ν x / 2)) atTop (𝓝 1) := by
  set D : ℝ → ℝ := fun x => ∫ z in {z : ℤ | x < (z : ℝ)}, ((x * (z : ℝ) - x ^ 2 / 2)) ∂ν with hD
  have hD0 : ∀ x : ℝ, 1 ≤ x → 0 ≤ D x := by
    intro x hx
    refine setIntegral_nonneg MeasurableSet.of_discrete (fun z hz => ?_)
    have : x < (z : ℝ) := hz
    nlinarith
  have hDR : ∀ x : ℝ, 1 ≤ x → D x ≤ x * meanAbove ν x := by
    intro x hx
    unfold meanAbove
    rw [← MeasureTheory.integral_const_mul]
    refine setIntegral_mono_on (((hint.const_mul x).sub (integrable_const (x ^ 2 / 2))).integrableOn)
      ((hint.const_mul x).integrableOn) MeasurableSet.of_discrete (fun z hz => ?_)
    have : x ^ 2 / 2 ≥ 0 := by positivity
    linarith
  have hDK : Tendsto (fun x : ℝ => D x / truncSecondMoment ν x) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      (meanAbove_isLittleO hint hK hKinf) ?_ ?_
    · filter_upwards [eventually_ge_atTop (1 : ℝ), hKinf.eventually_gt_atTop 0] with x hx hKx
      exact div_nonneg (hD0 x hx) hKx.le
    · filter_upwards [eventually_ge_atTop (1 : ℝ), hKinf.eventually_gt_atTop 0] with x hx hKx
      exact div_le_div_of_nonneg_right (hDR x hx) hKx.le
  have hlim : Tendsto (fun x : ℝ => 1 - ν.real {(-1 : ℤ)} / truncSecondMoment ν x +
      2 * (D x / truncSecondMoment ν x)) atTop (𝓝 (1 - 0 + 2 * 0)) :=
    (tendsto_const_nhds.sub (tendsto_const_nhds.div_atTop hKinf)).add (hDK.const_mul 2)
  rw [sub_zero, mul_zero, add_zero] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ), hKinf.eventually_gt_atTop 0] with x hx hKx
  rw [excess_decomp hneg hint hx]
  have := hKx.ne'
  simp only [hD]
  field_simp

theorem integratedTail_isEquivalent (hneg : ν {z : ℤ | z < -1} = 0)
    (hint : Integrable (fun z : ℤ => (z : ℝ)) ν)
    (hK : SlowlyVarying (truncSecondMoment ν))
    (hKinf : Tendsto (truncSecondMoment ν) atTop atTop) :
    Asymptotics.IsEquivalent atTop
      (fun x : ℝ => ∫ u in (0 : ℝ)..x, ∫ z, max ((z : ℝ) - u) 0 ∂ν)
      (fun x : ℝ => truncSecondMoment ν x / 2) :=
  Asymptotics.isEquivalent_of_tendsto_one (integratedTail_div_tendsto hneg hint hK hKinf)

/-- The excess `E[(Z-u)⁺]` equals the integrated tail `∫_u^∞ ν{z > v} dv`. -/
theorem integral_max_sub_eq_integral_tail (hint : Integrable (fun z : ℤ => (z : ℝ)) ν) (u : ℝ) :
    ∫ z, max ((z : ℝ) - u) 0 ∂ν = ∫ v in Ioi u, ν.real {z : ℤ | v < (z : ℝ)} := by
  have hf : Integrable (fun z : ℤ => max ((z : ℝ) - u) 0) ν := by
    refine Integrable.mono' (g := fun z : ℤ => |(z : ℝ)| + |u|)
      (hint.abs.add (integrable_const |u|))
      (measurable_of_countable _).aestronglyMeasurable (ae_of_all _ fun z => ?_)
    show ‖max ((z : ℝ) - u) 0‖ ≤ |(z : ℝ)| + |u|
    rw [Real.norm_of_nonneg (le_max_right _ _)]
    refine max_le ?_ (by positivity)
    linarith [abs_nonneg (z : ℝ), abs_nonneg u, neg_abs_le u, le_abs_self (z : ℝ)]
  rw [Integrable.integral_eq_integral_meas_lt hf (ae_of_all _ fun z => le_max_right _ _)]
  have h1 : ∫ t in Ioi (0 : ℝ), ν.real {z : ℤ | t < max ((z : ℝ) - u) 0} =
      ∫ t in Ioi (0 : ℝ), ν.real {z : ℤ | u + t < (z : ℝ)} := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    have ht' : 0 < t := ht
    congr 2
    ext z
    simp only [lt_max_iff]
    constructor
    · rintro (h | h)
      · linarith
      · linarith
    · intro h; left; linarith
  rw [h1]
  set g : ℝ → ℝ := fun v => ν.real {z : ℤ | v < (z : ℝ)} with hg
  have h2 : ∫ t in Ioi (0 : ℝ), g (u + t) = ∫ v in Ioi u, g v := by
    rw [← MeasureTheory.integral_indicator measurableSet_Ioi,
      ← MeasureTheory.integral_indicator measurableSet_Ioi]
    rw [← integral_add_left_eq_self (μ := volume) ((Ioi u).indicator g) u]
    refine integral_congr_ae (ae_of_all _ fun t => ?_)
    show _ = (Ioi u).indicator g (u + t)
    by_cases ht : 0 < t
    · rw [Set.indicator_of_mem (show t ∈ Ioi (0 : ℝ) from ht),
        Set.indicator_of_mem (show u + t ∈ Ioi u by simp [ht])]
    · rw [Set.indicator_of_notMem (show t ∉ Ioi (0 : ℝ) from ht),
        Set.indicator_of_notMem (show u + t ∉ Ioi u by simp [not_lt.1 ht])]
  exact h2

end B3b

end BGWLeaves.StableAnalysis.GaussianBranch
