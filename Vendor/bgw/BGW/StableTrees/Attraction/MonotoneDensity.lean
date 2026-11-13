/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.Attraction.SlowVariation

/-!
# Monotone density theorem

If `f ≥ 0` is antitone on `(0, ∞)` and `U(x) = ∫₀ˣ f` is regularly varying at infinity of index
`ρ`, then `x f(x) / U(x) → ρ`.  (The index `ρ ∈ [0,1)` of the application is not needed.)
Ported from `BGWLeaves/StableAnalysis/MonotoneDensity.lean` of the author's arXiv:1110.2163v4
formalization (local snapshot of 6 November 2026).
-/

@[expose] public section

open Filter MeasureTheory Set intervalIntegral
open scoped Topology ENNReal

namespace BGW.StableTrees.Attraction.MonotoneDensity

/-- `U` is regularly varying of index `ρ` at infinity. -/
def IsRegVaryAtTop (U : ℝ → ℝ) (ρ : ℝ) : Prop :=
  ∀ c : ℝ, 0 < c → Tendsto (fun x : ℝ => U (c * x) / U x) atTop (𝓝 (c ^ ρ))

section Part1

variable {f : ℝ → ℝ}

private theorem sandwich (hanti : AntitoneOn f (Ioi 0)) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (b - a) * f b ≤ ∫ t in a..b, f t ∧ ∫ t in a..b, f t ≤ (b - a) * f a := by
  have hsub : uIcc a b ⊆ Ioi 0 := by
    rw [uIcc_of_le hab]
    exact fun t ht => lt_of_lt_of_le ha ht.1
  have hint : IntervalIntegrable f volume a b := (hanti.mono hsub).intervalIntegrable
  constructor
  · have := intervalIntegral.integral_mono_on hab (intervalIntegrable_const (c := f b)) hint
      (fun t ht => hanti (show 0 < t from lt_of_lt_of_le ha ht.1)
        (show 0 < b from lt_of_lt_of_le ha hab) ht.2)
    simpa [mul_comm] using this
  · have := intervalIntegral.integral_mono_on hab hint (intervalIntegrable_const (c := f a))
      (fun t ht => hanti (show 0 < a from ha) (show 0 < t from lt_of_lt_of_le ha ht.1) ht.1)
    simpa [mul_comm] using this

private theorem integral_nonneg_zero (hnn : ∀ x, 0 < x → 0 ≤ f x) {x : ℝ} (hx : 0 < x) :
    0 ≤ ∫ t in (0 : ℝ)..x, f t := by
  rw [intervalIntegral.integral_of_le hx.le]
  exact setIntegral_nonneg measurableSet_Ioc (fun t ht => hnn t ht.1)

/-- The slope `(d ^ ρ - 1) / (d - 1)` tends to `ρ` as `d → 1`, `d ≠ 1`. -/
private theorem tendsto_slope_rpow (ρ : ℝ) :
    Tendsto (fun d : ℝ => (d ^ ρ - 1) / (d - 1)) (𝓝[≠] 1) (𝓝 ρ) := by
  have h := (Real.hasDerivAt_rpow_const (x := 1) (p := ρ) (Or.inl one_ne_zero))
  have h2 := (hasDerivAt_iff_tendsto_slope.mp h)
  simp only [Real.one_rpow, mul_one] at h2
  refine h2.congr (fun d => ?_)
  simp [slope_def_field]

theorem monotone_density (hnn : ∀ x, 0 < x → 0 ≤ f x) (hanti : AntitoneOn f (Ioi 0)) {ρ : ℝ}
    (hU : IsRegVaryAtTop (fun x => ∫ t in (0 : ℝ)..x, f t) ρ) :
    Tendsto (fun x : ℝ => x * f x / ∫ t in (0 : ℝ)..x, f t) atTop (𝓝 ρ) := by
  set U : ℝ → ℝ := fun x => ∫ t in (0 : ℝ)..x, f t with hUdef
  -- eventual nonvanishing of `U`, hence integrability
  have h1 : ∀ᶠ x : ℝ in atTop, U x ≠ 0 := by
    have := (hU 1 one_pos).eventually (isOpen_ne.mem_nhds (show ((1 : ℝ) ^ ρ) ≠ 0 by simp))
    filter_upwards [this] with x hx h0
    apply hx
    simp [h0]
  obtain ⟨X0, hX0⟩ := eventually_atTop.mp h1
  have hint : ∀ x, X0 ≤ x → IntervalIntegrable f volume 0 x := by
    intro x hx
    by_contra hni
    exact hX0 x hx (intervalIntegral.integral_undef hni)
  have hpos : ∀ x, max X0 1 ≤ x → 0 < U x := by
    intro x hx
    have hx0 : 0 < x := lt_of_lt_of_le one_pos ((le_max_right _ _).trans hx)
    exact lt_of_le_of_ne (integral_nonneg_zero hnn hx0)
      (hX0 x ((le_max_left _ _).trans hx)).symm
  -- sandwich for a fixed `c > 1`
  have key : ∀ c : ℝ, 1 < c → ∀ᶠ x : ℝ in atTop,
      (U (c * x) / U x - 1) / (c - 1) ≤ x * f x / U x ∧
      x * f x / U x ≤ (1 - U (c⁻¹ * x) / U x) / (1 - c⁻¹) := by
    intro c hc
    have hc0 : 0 < c := by linarith
    filter_upwards [eventually_ge_atTop (max (max X0 1) (c * max X0 1))] with x hx
    have hx1 : max X0 1 ≤ x := (le_max_left _ _).trans hx
    have hx2 : c * max X0 1 ≤ x := (le_max_right _ _).trans hx
    have hxX : X0 ≤ x := (le_max_left _ _).trans hx1
    have hx0 : 0 < x := lt_of_lt_of_le one_pos ((le_max_right _ _).trans hx1)
    have hUx : 0 < U x := hpos x hx1
    have hcx : x ≤ c * x := by nlinarith
    have hcxX : X0 ≤ c * x := hxX.trans hcx
    have hcx0 : 0 < c * x := by nlinarith
    have hxc : max X0 1 ≤ c⁻¹ * x := by
      rw [inv_mul_eq_div, le_div_iff₀ hc0]; linarith
    have hxcX : X0 ≤ c⁻¹ * x := (le_max_left _ _).trans hxc
    have hxc0 : 0 < c⁻¹ * x := lt_of_lt_of_le one_pos ((le_max_right _ _).trans hxc)
    have hxcx : c⁻¹ * x ≤ x := by
      have : c⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hc.le
      nlinarith
    have hA : U (c * x) - U x = ∫ t in x..(c * x), f t :=
      (intervalIntegral.integral_interval_sub_left (hint _ hcxX) (hint _ hxX))
    have hB : U x - U (c⁻¹ * x) = ∫ t in (c⁻¹ * x)..x, f t :=
      (intervalIntegral.integral_interval_sub_left (hint _ hxX) (hint _ hxcX))
    have s1 := (sandwich hanti hx0 hcx).2
    have s2 := (sandwich hanti hxc0 hxcx).1
    rw [← hA] at s1
    rw [← hB] at s2
    have hc1 : 0 < c - 1 := by linarith
    have hc2 : 0 < 1 - c⁻¹ := by
      have : c⁻¹ < 1 := inv_lt_one_of_one_lt₀ hc
      linarith
    constructor
    · rw [div_le_div_iff₀ hc1 hUx, sub_mul, div_mul_cancel₀ _ hUx.ne']
      have : (c * x - x) * f x = (c - 1) * (x * f x) := by ring
      nlinarith
    · rw [div_le_div_iff₀ hUx hc2, sub_mul, div_mul_cancel₀ _ hUx.ne']
      have : (x - c⁻¹ * x) * f x = (1 - c⁻¹) * (x * f x) := by ring
      nlinarith
  -- conclude
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hS := tendsto_slope_rpow ρ
  have hS1 : ∀ᶠ d : ℝ in 𝓝[≠] 1, dist ((d ^ ρ - 1) / (d - 1)) ρ < ε :=
    (Metric.tendsto_nhds.mp hS) ε hε
  have hinv : Tendsto (fun c : ℝ => c⁻¹) (𝓝[>] (1 : ℝ)) (𝓝[≠] (1 : ℝ)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have : Tendsto (fun c : ℝ => c⁻¹) (𝓝 (1 : ℝ)) (𝓝 ((1 : ℝ)⁻¹)) :=
        (continuousAt_inv₀ one_ne_zero).tendsto
      simpa using this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with c hc
      exact (inv_lt_one_of_one_lt₀ hc).ne
  have hc : ∀ᶠ c : ℝ in 𝓝[>] 1, 1 < c ∧ dist ((c ^ ρ - 1) / (c - 1)) ρ < ε ∧
      dist (((c⁻¹) ^ ρ - 1) / (c⁻¹ - 1)) ρ < ε := by
    have h2 := hinv.eventually hS1
    have h1 : ∀ᶠ c : ℝ in 𝓝[>] 1, dist ((c ^ ρ - 1) / (c - 1)) ρ < ε :=
      (nhdsWithin_mono _ (fun x hx => ne_of_gt hx)) hS1
    filter_upwards [self_mem_nhdsWithin, h1, h2] with c hc1 hc2 hc3
    exact ⟨hc1, hc2, hc3⟩
  obtain ⟨c, hc1, hc2, hc3⟩ := hc.exists
  have hc0 : 0 < c := by linarith
  have hB : Tendsto (fun x : ℝ => (U (c * x) / U x - 1) / (c - 1)) atTop
      (𝓝 ((c ^ ρ - 1) / (c - 1))) := ((hU c hc0).sub_const 1).div_const _
  have hA : Tendsto (fun x : ℝ => (1 - U (c⁻¹ * x) / U x) / (1 - c⁻¹)) atTop
      (𝓝 ((1 - (c⁻¹) ^ ρ) / (1 - c⁻¹))) :=
    (((hU c⁻¹ (inv_pos.mpr hc0)).const_sub 1)).div_const _
  have hAeq : (1 - (c⁻¹) ^ ρ) / (1 - c⁻¹) = ((c⁻¹) ^ ρ - 1) / (c⁻¹ - 1) := by
    rw [← neg_sub, ← neg_sub (c⁻¹ : ℝ), neg_div_neg_eq]
  rw [hAeq] at hA
  rw [Real.dist_eq, abs_lt] at hc2 hc3
  have e1 := hB.eventually (lt_mem_nhds (show ρ - ε < (c ^ ρ - 1) / (c - 1) by linarith [hc2.1]))
  have e2 := hA.eventually (gt_mem_nhds (show ((c⁻¹) ^ ρ - 1) / (c⁻¹ - 1) < ρ + ε by
    linarith [hc3.2]))
  filter_upwards [key c hc1, e1, e2] with x hk h1' h2'
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith [hk.1, hk.2]

end Part1

section Karamata

open BGW.StableTrees

private theorem regVary_eventually_ne {U : ℝ → ℝ} {ρ : ℝ} (hU : IsRegVaryAtTop U ρ) :
    ∀ᶠ x : ℝ in atTop, U x ≠ 0 := by
  have := (hU 1 one_pos).eventually (isOpen_ne.mem_nhds (show ((1 : ℝ) ^ ρ) ≠ 0 by simp))
  filter_upwards [this] with x hx h0
  apply hx
  simp [h0]

variable {T : ℝ → ℝ} {θ : ℝ}

private theorem regVary_eventually_pos {ρ : ℝ} (hT0 : ∀ x, 0 ≤ T x) (hT : IsRegVaryAtTop T ρ) :
    ∀ᶠ x : ℝ in atTop, 0 < T x := by
  filter_upwards [regVary_eventually_ne hT] with x hx
  exact lt_of_le_of_ne (hT0 x) hx.symm

private theorem exists_dyadic_step (hT0 : ∀ x, 0 ≤ T x) (hT : IsRegVaryAtTop T (-θ)) {β : ℝ}
    (hβ : θ < β) :
    ∃ A : ℝ, 0 < A ∧ ∀ y : ℝ, A ≤ y → T (y / 2) ≤ (2 : ℝ) ^ β * T y := by
  have h := hT (1 / 2) (by norm_num)
  have hval : ((1 : ℝ) / 2) ^ (-θ) = (2 : ℝ) ^ θ := by
    rw [one_div, Real.inv_rpow (by norm_num), Real.rpow_neg (by norm_num), inv_inv]
  rw [hval] at h
  have hlt : (2 : ℝ) ^ θ < (2 : ℝ) ^ β := Real.rpow_lt_rpow_of_exponent_lt (by norm_num) hβ
  have e1 := h.eventually (gt_mem_nhds hlt)
  have e2 := regVary_eventually_pos hT0 hT
  obtain ⟨A, hA⟩ := eventually_atTop.mp (e1.and e2)
  refine ⟨max A 1, lt_of_lt_of_le one_pos (le_max_right _ _), fun y hy => ?_⟩
  obtain ⟨h1, h2⟩ := hA y ((le_max_left _ _).trans hy)
  have : T (1 / 2 * y) = T (y / 2) := by congr 1; ring
  rw [this, div_lt_iff₀ h2] at h1
  exact h1.le

private theorem dyadic_iter {A q : ℝ} (hA0 : 0 ≤ A) (hq : 0 ≤ q)
    (hstep : ∀ y : ℝ, A ≤ y → T (y / 2) ≤ q * T y) :
    ∀ k : ℕ, ∀ y : ℝ, A * 2 ^ k ≤ y → T (y / 2 ^ k) ≤ q ^ k * T y := by
  intro k
  induction k with
  | zero => intro y _; simp
  | succ k ih =>
    intro y hy
    have h2k : (0 : ℝ) < 2 ^ k := by positivity
    have hy' : A * 2 ^ k ≤ y := by
      have : (2 : ℝ) ^ k ≤ 2 ^ (k + 1) := pow_le_pow_right₀ (by norm_num) (Nat.le_succ k)
      exact (mul_le_mul_of_nonneg_left this hA0).trans hy
    have hAy : A ≤ y / 2 ^ k := by rw [le_div_iff₀ h2k]; exact hy'
    have h1 := hstep _ hAy
    calc T (y / 2 ^ (k + 1)) = T (y / 2 ^ k / 2) := by congr 1; rw [pow_succ]; field_simp
      _ ≤ q * T (y / 2 ^ k) := h1
      _ ≤ q * (q ^ k * T y) := mul_le_mul_of_nonneg_left (ih y hy') hq
      _ = q ^ (k + 1) * T y := by ring

/-- Potter-type bound for an antitone function with a dyadic step bound. -/
private theorem potter_dyadic (hanti : Antitone T) (hT0 : ∀ x, 0 ≤ T x) {A β : ℝ} (hA : 0 < A)
    (hβ : 0 ≤ β) (hstep : ∀ y : ℝ, A ≤ y → T (y / 2) ≤ (2 : ℝ) ^ β * T y) :
    ∀ x t : ℝ, 0 < t → t ≤ 1 → 2 * A ≤ x * t →
      T (x * t) ≤ (2 : ℝ) ^ β * t ^ (-β) * T x := by
  intro x t ht ht1 hxt
  have hxt0 : 0 < x * t := by linarith
  have hx : 0 < x := by
    by_contra h
    push Not at h
    nlinarith
  obtain ⟨n, hn1, hn2⟩ := exists_nat_pow_near_of_lt_one ht ht1 (show (0 : ℝ) < 1 / 2 by norm_num)
    (show (1 / 2 : ℝ) < 1 by norm_num)
  rw [one_div_pow] at hn1 hn2
  have h2n : (0 : ℝ) < 2 ^ n := by positivity
  have h2n1 : (0 : ℝ) < 2 ^ (n + 1) := by positivity
  have hxn : x * t ≤ x / 2 ^ n := by
    rw [div_eq_mul_one_div]
    exact mul_le_mul_of_nonneg_left hn2 hx.le
  have hAx : A * 2 ^ (n + 1) ≤ x := by
    have : 2 * A ≤ x / 2 ^ n := hxt.trans hxn
    rw [le_div_iff₀ h2n] at this
    rw [pow_succ]
    linarith
  have hlow : x / 2 ^ (n + 1) ≤ x * t := by
    rw [div_eq_mul_one_div]
    exact mul_le_mul_of_nonneg_left hn1.le hx.le
  have h1 : T (x * t) ≤ T (x / 2 ^ (n + 1)) := hanti hlow
  have h2 := dyadic_iter hA.le (by positivity) hstep (n + 1) x hAx
  have hpow : ((2 : ℝ) ^ β) ^ n = ((2 : ℝ) ^ n) ^ β := by
    rw [← Real.rpow_natCast ((2 : ℝ) ^ β) n, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
      ← Real.rpow_natCast (2 : ℝ) n, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), mul_comm]
  have hle : (2 : ℝ) ^ n ≤ t⁻¹ := by
    rw [le_inv_comm₀ h2n ht]
    simpa [one_div] using hn2
  have hq : ((2 : ℝ) ^ β) ^ (n + 1) ≤ (2 : ℝ) ^ β * t ^ (-β) := by
    rw [pow_succ', hpow]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    calc ((2 : ℝ) ^ n) ^ β ≤ (t⁻¹) ^ β := Real.rpow_le_rpow h2n.le hle hβ
      _ = t ^ (-β) := by rw [Real.inv_rpow ht.le, Real.rpow_neg ht.le]
  exact h1.trans (h2.trans (mul_le_mul_of_nonneg_right hq (hT0 x)))

private theorem sq_mul_tendsto_atTop (hT0 : ∀ x, 0 ≤ T x) (hanti : Antitone T)
    (hθ2 : θ < 2) (hT : IsRegVaryAtTop T (-θ)) :
    Tendsto (fun x : ℝ => x ^ 2 * T x) atTop atTop := by
  have hTmeas : Measurable T := hanti.measurable
  have hpos : ∀ᶠ x : ℝ in atTop, 0 < T x := regVary_eventually_pos hT0 hT
  have hL : SlowlyVarying (fun x : ℝ => x ^ θ * T x) := by
    intro a ha
    have h2 := (hT a ha).const_mul (a ^ θ)
    have e : a ^ θ * a ^ (-θ) = 1 := by rw [← Real.rpow_add ha]; simp
    rw [e] at h2
    refine h2.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ), hpos] with x hx hTx
    have hxθ : 0 < x ^ θ := Real.rpow_pos_of_pos hx θ
    have hTax : 0 < T (a * x) ∨ T (a * x) = 0 := (hT0 _).lt_or_eq.imp id Eq.symm
    show a ^ θ * (T (a * x) / T x) = ((a * x) ^ θ * T (a * x)) / (x ^ θ * T x)
    rw [Real.mul_rpow ha.le hx.le]
    field_simp
  have hmeas : Measurable (fun x : ℝ => x ^ θ * T x) :=
    (measurable_id.pow_const θ).mul hTmeas
  have h := BGW.StableTrees.Attraction.SlowVariation.slow_rpow_mul_tendsto_atTop hmeas
    (fun x hx => mul_nonneg (Real.rpow_nonneg hx.le θ) (hT0 x)) hL (show 0 < 2 - θ by linarith)
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  rw [← mul_assoc, ← Real.rpow_add hx, sub_add_cancel, Real.rpow_two]

/-- Karamata's theorem for an antitone nonnegative regularly varying function. -/
theorem karamata_antitone (hT0 : ∀ x, 0 ≤ T x) (hanti : Antitone T) (hθ0 : 0 < θ)
    (hθ2 : θ < 2) (hT : IsRegVaryAtTop T (-θ)) :
    Tendsto (fun x : ℝ => (∫ u in (0 : ℝ)..x, u * T u) / (x ^ 2 * T x)) atTop
      (𝓝 (1 / (2 - θ))) := by
  set β : ℝ := (θ + 2) / 2 with hβdef
  have hβθ : θ < β := by rw [hβdef]; linarith
  have hβ0 : 0 ≤ β := by rw [hβdef]; linarith
  obtain ⟨A, hA0, hstep⟩ := exists_dyadic_step hT0 hT hβθ
  have hpot := potter_dyadic hanti hT0 hA0 hβ0 hstep
  set M : ℝ := 2 * A with hM
  have hM0 : 0 < M := by rw [hM]; linarith
  have hTmeas : Measurable T := hanti.measurable
  have hpos : ∀ᶠ x : ℝ in atTop, 0 < T x := regVary_eventually_pos hT0 hT
  have hdiv : Tendsto (fun x : ℝ => x ^ 2 * T x) atTop atTop :=
    sq_mul_tendsto_atTop hT0 hanti hθ2 hT
  -- integrability
  have hintT : ∀ a b : ℝ, IntervalIntegrable (fun u => u * T u) volume a b := fun a b =>
    ((hanti.intervalIntegrable (a := a) (b := b) (μ := volume)).continuousOn_mul
      continuous_id.continuousOn : _)
  have hanti' : Antitone (fun u : ℝ => T (max u M)) := fun a b hab => hanti (max_le_max hab le_rfl)
  have hintTm : ∀ a b : ℝ, IntervalIntegrable (fun u => u * T (max u M)) volume a b := fun a b =>
    ((hanti'.intervalIntegrable (a := a) (b := b) (μ := volume)).continuousOn_mul
      continuous_id.continuousOn : _)
  -- the cutoff only changes the integral by a constant
  set D : ℝ := (∫ u in (0 : ℝ)..M, u * T u) - ∫ u in (0 : ℝ)..M, u * T (max u M) with hD
  have hcut : ∀ x : ℝ, M ≤ x → (∫ u in (0 : ℝ)..x, u * T u) =
      (∫ u in (0 : ℝ)..x, u * T (max u M)) + D := by
    intro x hx
    have e1 := (intervalIntegral.integral_add_adjacent_intervals (hintT 0 M) (hintT M x)).symm
    have e2 := (intervalIntegral.integral_add_adjacent_intervals (hintTm 0 M) (hintTm M x)).symm
    have e3 : (∫ u in M..x, u * T (max u M)) = ∫ u in M..x, u * T u := by
      refine intervalIntegral.integral_congr (fun u hu => ?_)
      rw [uIcc_of_le hx] at hu
      simp only [max_eq_left hu.1]
    rw [e1, e2, e3, hD]
    ring
  -- main limit for the cutoff function
  have hmain : Tendsto (fun x : ℝ => (∫ u in (0 : ℝ)..x, u * T (max u M)) / (x ^ 2 * T x))
      atTop (𝓝 (1 / (2 - θ))) := by
    have hG : Tendsto (fun x : ℝ => ∫ t in (0 : ℝ)..1, t * T (max (x * t) M) / T x) atTop
        (𝓝 (∫ t in (0 : ℝ)..1, t ^ (1 - θ))) := by
      refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
        (fun t => (2 : ℝ) ^ β * t ^ (1 - β)) ?_ ?_ ?_ ?_
      · refine Eventually.of_forall (fun x => ?_)
        exact ((measurable_id.mul (hTmeas.comp ((measurable_const.mul measurable_id).max
          measurable_const))).div_const _).aestronglyMeasurable
      · filter_upwards [eventually_ge_atTop M, hpos] with x hxM hxpos
        refine Eventually.of_forall (fun t ht => ?_)
        rw [uIoc_of_le zero_le_one] at ht
        obtain ⟨ht0, ht1⟩ := ht
        have hx0 : 0 < x := lt_of_lt_of_le hM0 hxM
        set s : ℝ := max t (M / x) with hs
        have hMx : M / x ≤ 1 := by rw [div_le_one hx0]; exact hxM
        have hs0 : 0 < s := lt_of_lt_of_le ht0 (le_max_left _ _)
        have hs1 : s ≤ 1 := max_le ht1 hMx
        have hxs : x * s = max (x * t) M := by
          rw [hs, mul_max_of_nonneg _ _ hx0.le]
          congr 1
          field_simp
        have hxsM : 2 * A ≤ x * s := by
          rw [hxs]; exact le_trans (by rw [hM]) (le_max_right _ _)
        have hP := hpot x s hs0 hs1 hxsM
        rw [hxs] at hP
        have hst : s ^ (-β) ≤ t ^ (-β) :=
          Real.rpow_le_rpow_of_nonpos ht0 (le_max_left _ _) (by linarith)
        have hnn : 0 ≤ t * T (max (x * t) M) / T x :=
          div_nonneg (mul_nonneg ht0.le (hT0 _)) hxpos.le
        rw [Real.norm_of_nonneg hnn, div_le_iff₀ hxpos]
        have hb : (2 : ℝ) ^ β * t ^ (1 - β) = t * ((2 : ℝ) ^ β * t ^ (-β)) := by
          rw [sub_eq_add_neg, Real.rpow_add ht0, Real.rpow_one]; ring
        rw [hb]
        have h2β : 0 ≤ (2 : ℝ) ^ β := by positivity
        calc t * T (max (x * t) M) ≤ t * ((2 : ℝ) ^ β * s ^ (-β) * T x) :=
              mul_le_mul_of_nonneg_left hP ht0.le
          _ ≤ t * ((2 : ℝ) ^ β * t ^ (-β) * T x) := by
              refine mul_le_mul_of_nonneg_left ?_ ht0.le
              exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hst h2β) (hT0 x)
          _ = t * ((2 : ℝ) ^ β * t ^ (-β)) * T x := by ring
      · exact (intervalIntegral.intervalIntegrable_rpow' (by rw [hβdef]; linarith)).const_mul _
      · refine Eventually.of_forall (fun t ht => ?_)
        rw [uIoc_of_le zero_le_one] at ht
        have ht0 : 0 < t := ht.1
        have h1 := (hT t ht0).const_mul t
        have e : t * t ^ (-θ) = t ^ (1 - θ) := by
          rw [sub_eq_add_neg, Real.rpow_add ht0, Real.rpow_one]
        rw [e] at h1
        refine h1.congr' ?_
        filter_upwards [eventually_ge_atTop (M / t)] with x hx
        have : M ≤ t * x := by rwa [div_le_iff₀ ht0, mul_comm] at hx
        rw [mul_comm x t, max_eq_left this]
        ring
    have hint1 : ∫ t in (0 : ℝ)..1, t ^ (1 - θ) = 1 / (2 - θ) := by
      rw [integral_rpow (Or.inl (by linarith)), Real.one_rpow,
        Real.zero_rpow (by linarith : 1 - θ + 1 ≠ 0)]
      congr 1 <;> ring
    rw [hint1] at hG
    refine hG.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ), hpos] with x hx hxpos
    have h1 := intervalIntegral.integral_comp_mul_left (a := 0) (b := 1)
      (fun u => u * T (max u M)) hx.ne'
    simp only [mul_zero, mul_one, smul_eq_mul] at h1
    have h2 : (∫ t in (0 : ℝ)..1, (x * t) * T (max (x * t) M)) =
        x * ∫ t in (0 : ℝ)..1, t * T (max (x * t) M) := by
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr (fun t _ => ?_)
      ring
    rw [h2] at h1
    have h3 : (∫ t in (0 : ℝ)..1, t * T (max (x * t) M)) =
        x⁻¹ ^ 2 * ∫ u in (0 : ℝ)..x, u * T (max u M) := by
      have : x * ∫ t in (0 : ℝ)..1, t * T (max (x * t) M) =
          x⁻¹ * ∫ u in (0 : ℝ)..x, u * T (max u M) := h1
      field_simp at this
      rw [← this, ← mul_assoc, ← mul_pow, inv_mul_cancel₀ hx.ne', one_pow, one_mul]
    rw [intervalIntegral.integral_div, h3]
    field_simp
  have hD' : Tendsto (fun x : ℝ => D / (x ^ 2 * T x)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hdiv
  have hsum := hmain.add hD'
  rw [add_zero] at hsum
  refine hsum.congr' ?_
  filter_upwards [eventually_ge_atTop M] with x hx
  rw [hcut x hx, add_div]

end Karamata

section LayerCake

private theorem phi_integral {x : ℝ} (hx : 0 ≤ x) (z : ℝ) :
    ∫ u in (0 : ℝ)..x, (if u < z then 2 * u else 0) =
      if z ≤ 0 then 0 else if z ≤ x then z ^ 2 else x ^ 2 := by
  have h : (fun u : ℝ => if u < z then 2 * u else 0) =
      (Iio z).indicator (fun u : ℝ => 2 * u) := by
    funext u; simp [Set.indicator_apply]
  rw [h, intervalIntegral.integral_of_le hx, setIntegral_indicator measurableSet_Iio]
  split_ifs with h1 h2
  · have : Ioc (0 : ℝ) x ∩ Iio z = ∅ := by
      ext u
      simp only [mem_inter_iff, mem_Ioc, mem_Iio, mem_empty_iff_false, iff_false, not_and]
      intro hu _; linarith [hu.1]
    rw [this]; simp
  · have : Ioc (0 : ℝ) x ∩ Iio z = Ioo 0 z := by
      ext u
      simp only [mem_inter_iff, mem_Ioc, mem_Iio, mem_Ioo]
      constructor
      · rintro ⟨⟨a, _⟩, c⟩; exact ⟨a, c⟩
      · rintro ⟨a, c⟩; exact ⟨⟨a, by linarith⟩, c⟩
    rw [this, ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by linarith)]
    rw [intervalIntegral.integral_const_mul, integral_id]; ring
  · have : Ioc (0 : ℝ) x ∩ Iio z = Ioc 0 x := by
      refine inter_eq_left.mpr (fun u hu => lt_of_le_of_lt hu.2 (by linarith))
    rw [this, ← intervalIntegral.integral_of_le hx]
    rw [intervalIntegral.integral_const_mul, integral_id]; ring

/-- Layer-cake identity for the truncated second moment of a law on `ℤ` with `ν {z < -1} = 0`:
`2 ∫₀ˣ u T(u) du = K(x) + x² T(x) - ν{-1}` for `x ≥ 1`. -/
theorem layer_cake_trunc (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (hneg : ν {z : ℤ | z < -1} = 0) {x : ℝ} (hx : 1 ≤ x) :
    2 * ∫ u in (0 : ℝ)..x, u * ν.real {z : ℤ | u < (z : ℝ)} =
      truncSecondMoment ν x + x ^ 2 * ν.real {z : ℤ | x < (z : ℝ)} - ν.real {(-1 : ℤ)} := by
  have hx0 : 0 ≤ x := by linarith
  let f : ℝ → ℤ → ℝ := fun u z => if u < (z : ℝ) then 2 * u else 0
  have hcast : Measurable (fun z : ℤ => (z : ℝ)) := Measurable.of_discrete
  have hfmeas : Measurable (Function.uncurry f) := by
    have hset : MeasurableSet {p : ℝ × ℤ | p.1 < (p.2 : ℝ)} :=
      measurableSet_lt measurable_fst (hcast.comp measurable_snd)
    exact Measurable.ite hset (measurable_const.mul measurable_fst) measurable_const
  have hint : Integrable (Function.uncurry f) ((volume.restrict (uIoc (0 : ℝ) x)).prod ν) := by
    have : IsFiniteMeasure (volume.restrict (uIoc (0 : ℝ) x)) := by
      rw [uIoc_of_le hx0]; infer_instance
    refine Integrable.of_bound hfmeas.aestronglyMeasurable (2 * x) ?_
    rw [Measure.ae_prod_iff_ae_ae (measurableSet_le hfmeas.norm measurable_const)]
    rw [uIoc_of_le hx0]
    refine (ae_restrict_iff' measurableSet_Ioc).mpr
      (ae_of_all _ (fun u hu => ae_of_all _ (fun z => ?_)))
    simp only [Function.uncurry, f]
    split_ifs
    · rw [Real.norm_eq_abs, abs_of_nonneg (by linarith [hu.1])]; linarith [hu.2]
    · simp; linarith
  have hswap := intervalIntegral_integral_swap (μ := ν) hint
  have hL : ∀ u : ℝ, ∫ z, f u z ∂ν = 2 * (u * ν.real {z : ℤ | u < (z : ℝ)}) := by
    intro u
    have : (fun z : ℤ => f u z) =
        ({z : ℤ | u < (z : ℝ)}).indicator (fun _ => 2 * u) := by
      funext z; simp [f, Set.indicator_apply]
    show ∫ z, (fun z : ℤ => f u z) z ∂ν = _
    rw [this, integral_indicator_const _ (MeasurableSet.of_discrete), smul_eq_mul]
    ring
  have hlhs : 2 * ∫ u in (0 : ℝ)..x, u * ν.real {z : ℤ | u < (z : ℝ)} =
      ∫ u in (0 : ℝ)..x, ∫ z, f u z ∂ν := by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr (fun u _ => (hL u).symm)
  rw [hlhs, hswap]
  have hnull : ∀ᵐ z ∂ν, ¬ z < -1 := by
    rw [ae_iff]; simpa using hneg
  -- identify the inner integral
  set a : ℤ → ℝ := ({z : ℤ | |(z : ℝ)| ≤ x}).indicator (fun z => (z : ℝ) ^ 2) with ha
  set b : ℤ → ℝ := ({z : ℤ | x < (z : ℝ)}).indicator (fun _ => x ^ 2) with hb
  set c : ℤ → ℝ := ({(-1 : ℤ)} : Set ℤ).indicator (fun _ => (1 : ℝ)) with hc
  have hpt : ∀ᵐ z ∂ν, ∫ u in (0 : ℝ)..x, f u z = a z + b z - c z := by
    filter_upwards [hnull] with z hz
    have hz' : (-1 : ℤ) ≤ z := not_lt.mp hz
    have hphi := phi_integral hx0 (z : ℝ)
    simp only [f]
    rw [hphi]
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
  have hib : Integrable b ν := (integrable_const _).indicator MeasurableSet.of_discrete
  have hic : Integrable c ν := (integrable_const _).indicator MeasurableSet.of_discrete
  rw [integral_congr_ae hpt,
    integral_sub (f := fun z => a z + b z) (g := c) (hia.add hib) hic,
    integral_add hia hib]
  have e1 : ∫ z, a z ∂ν = truncSecondMoment ν x := by
    rw [ha, MeasureTheory.integral_indicator MeasurableSet.of_discrete]; rfl
  have e2 : ∫ z, b z ∂ν = x ^ 2 * ν.real {z : ℤ | x < (z : ℝ)} := by
    rw [hb, integral_indicator_const _ MeasurableSet.of_discrete, smul_eq_mul, mul_comm]
  have e3 : ∫ z, c z ∂ν = ν.real {(-1 : ℤ)} := by
    rw [hc, integral_indicator_const _ MeasurableSet.of_discrete, smul_eq_mul, mul_one]
  rw [e1, e2, e3]

/-- **Truncated second moment under a regularly varying tail** (`1 < θ < 2`; in fact the proof
only uses `0 < θ < 2`).  If `ν` is a probability law on `ℤ` with `ν {z < -1} = 0` whose right tail
`T(x) = ν {z > x}` is regularly varying of index `-θ`, then `K(x) ~ θ x² T(x) / (2 - θ)`. -/
theorem truncSecondMoment_div_tendsto (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (hneg : ν {z : ℤ | z < -1} = 0) {θ : ℝ} (hθ1 : 1 < θ) (hθ2 : θ < 2)
    (hT : IsRegVaryAtTop (fun x : ℝ => ν.real {z : ℤ | x < (z : ℝ)}) (-θ)) :
    Tendsto (fun x : ℝ => truncSecondMoment ν x / (x ^ 2 * ν.real {z : ℤ | x < (z : ℝ)}))
      atTop (𝓝 (θ / (2 - θ))) := by
  set T : ℝ → ℝ := fun x => ν.real {z : ℤ | x < (z : ℝ)} with hTdef
  have hT0 : ∀ x, 0 ≤ T x := fun x => measureReal_nonneg
  have hanti : Antitone T := fun a b hab =>
    measureReal_mono (fun z hz => lt_of_le_of_lt hab hz)
  have hK := karamata_antitone hT0 hanti (by linarith) hθ2 hT
  have hdiv := sq_mul_tendsto_atTop hT0 hanti hθ2 hT
  have hpos := regVary_eventually_pos hT0 hT
  have hc : Tendsto (fun x : ℝ => ν.real {(-1 : ℤ)} / (x ^ 2 * T x)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hdiv
  have hlim := (((hK.const_mul 2).sub_const 1).add hc)
  have hval : 2 * (1 / (2 - θ)) - 1 + 0 = θ / (2 - θ) := by
    have : (2 - θ) ≠ 0 := by linarith
    field_simp
    ring
  rw [hval] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ), hpos] with x hx hxpos
  have hx0 : 0 < x := by linarith
  have hlc := layer_cake_trunc ν hneg hx
  have hne : x ^ 2 * T x ≠ 0 := by positivity
  have hKx : truncSecondMoment ν x = 2 * (∫ u in (0 : ℝ)..x, u * T u) - x ^ 2 * T x
      + ν.real {(-1 : ℤ)} := by
    have : 2 * ∫ u in (0 : ℝ)..x, u * ν.real {z : ℤ | u < (z : ℝ)} =
      2 * ∫ u in (0 : ℝ)..x, u * T u := rfl
    linarith
  show 2 * ((∫ u in (0 : ℝ)..x, u * T u) / (x ^ 2 * T x))
    - 1 + ν.real {(-1 : ℤ)} / (x ^ 2 * T x) = truncSecondMoment ν x / (x ^ 2 * T x)
  rw [hKx]
  generalize (∫ u in (0 : ℝ)..x, u * T u) = I
  generalize ν.real {(-1 : ℤ)} = c0
  generalize T x = t at hne hxpos ⊢
  have ht : t ≠ 0 := hxpos.ne'
  field_simp

/-- Same statement in the form `K(x) ~ θ x² T(x) / (2 - θ)`. -/
theorem truncSecondMoment_isEquivalent (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (hneg : ν {z : ℤ | z < -1} = 0) {θ : ℝ} (hθ1 : 1 < θ) (hθ2 : θ < 2)
    (hT : IsRegVaryAtTop (fun x : ℝ => ν.real {z : ℤ | x < (z : ℝ)}) (-θ)) :
    Asymptotics.IsEquivalent atTop (truncSecondMoment ν)
      (fun x : ℝ => θ / (2 - θ) * (x ^ 2 * ν.real {z : ℤ | x < (z : ℝ)})) := by
  have h := (truncSecondMoment_div_tendsto ν hneg hθ1 hθ2 hT).div_const (θ / (2 - θ))
  have hc : θ / (2 - θ) ≠ 0 := div_ne_zero (by linarith) (by linarith)
  rw [div_self hc] at h
  refine Asymptotics.isEquivalent_of_tendsto_one (h.congr (fun x => ?_))
  simp only [Pi.div_apply]
  rw [div_div, mul_comm]

end LayerCake

end BGW.StableTrees.Attraction.MonotoneDensity
