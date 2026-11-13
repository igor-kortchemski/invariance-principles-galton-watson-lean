/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.Attraction.MonotoneDensity
public import BGW.StableTrees.Attraction.Defs

/-!
# Tail transfer: from the offspring tail to the strict tail of the step law

Let `μ` be an offspring law with `μ[j, ∞) = j ^ (-θ) * L j` for `j ≥ 1`, `L` slowly varying.
For `ν = stepLaw μ` (the law of `K - 1`) the strict tail `T x = ν {z | x < z}` satisfies
`T x = μ[⌊x⌋₊ + 2, ∞)` for `x ≥ 0`; this module shows that `T` is regularly varying at infinity of
index `-θ` (a consequence of the uniform convergence theorem) and eventually positive.
Ported from `BGWLeaves/StableAnalysis/TailTransfer.lean` of the author's arXiv:1110.2163v4
formalization (local snapshot of 6 November 2026).
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace BGW.StableTrees.Attraction.TailTransfer

open BGW.StableTrees
open BGW.StableTrees.Attraction
open BGW.StableTrees.Attraction.MonotoneDensity
open BGW.StableTrees.Attraction.SlowVariation

/-- The index `⌊x⌋₊ + 2` as a real number. -/
noncomputable def floorShift (x : ℝ) : ℝ := ((⌊x⌋₊ + 2 : ℕ) : ℝ)

theorem floorShift_pos (x : ℝ) : 0 < floorShift x := by
  unfold floorShift; positivity

theorem le_floorShift {x : ℝ} : x + 1 ≤ floorShift x := by
  unfold floorShift
  have := Nat.lt_floor_add_one x
  push_cast
  linarith

theorem floorShift_le {x : ℝ} (hx : 0 ≤ x) : floorShift x ≤ x + 2 := by
  unfold floorShift
  have := Nat.floor_le hx
  push_cast
  linarith

theorem tendsto_floorShift_atTop : Tendsto floorShift atTop atTop := by
  refine tendsto_atTop_mono' atTop ?_ tendsto_id
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
  have := le_floorShift (x := x)
  simp only [id_eq]
  linarith

theorem tendsto_floorShift_div : Tendsto (fun x : ℝ => floorShift x / x) atTop (𝓝 1) := by
  have h0 : Tendsto (fun x : ℝ => x⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have h1 : Tendsto (fun x : ℝ => 1 + x⁻¹) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).add h0
  have h2 : Tendsto (fun x : ℝ => 1 + 2 * x⁻¹) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).add ((tendsto_const_nhds (x := (2 : ℝ))).mul h0)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' h1 h2 ?_ ?_
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    rw [le_div_iff₀ hx]
    have := le_floorShift (x := x)
    have e : (1 + x⁻¹) * x = x + 1 := by field_simp
    linarith
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    rw [div_le_iff₀ hx]
    have := floorShift_le hx.le
    have e : (1 + 2 * x⁻¹) * x = x + 2 := by field_simp
    linarith

/-- The ratio `⌊c x⌋₊ + 2` over `⌊x⌋₊ + 2` tends to `c`. -/
theorem tendsto_floorShift_ratio {c : ℝ} (hc : 0 < c) :
    Tendsto (fun x : ℝ => floorShift (c * x) / floorShift x) atTop (𝓝 c) := by
  have h1 : Tendsto (fun x : ℝ => floorShift (c * x) / (c * x)) atTop (𝓝 1) :=
    tendsto_floorShift_div.comp (tendsto_id.const_mul_atTop hc)
  have h2 := (h1.mul_const c).div tendsto_floorShift_div one_ne_zero
  simp only [one_mul, div_one] at h2
  refine h2.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  have hf := (floorShift_pos x).ne'
  have hcx : c * x ≠ 0 := by positivity
  simp only [Pi.div_apply]
  field_simp

/-- Slow variation along `y i → ∞` and a scaling `r i → c > 0`. -/
theorem slow_ratio_tendsto {L : ℝ → ℝ} (hmeas : Measurable L) (hnn : ∀ x, 0 < x → 0 ≤ L x)
    (hL : SlowlyVarying L) {ι : Type*} {l : Filter ι} {y r : ι → ℝ} {c : ℝ} (hc : 0 < c)
    (hy : Tendsto y l atTop) (hr : Tendsto r l (𝓝 c)) :
    Tendsto (fun i => L (r i * y i) / L (y i)) l (𝓝 1) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨X, hX⟩ := slow_uniform_convergence hmeas hnn hL (a := c / 2) (b := 2 * c)
    (by positivity) (by linarith) hε
  filter_upwards [hy.eventually_ge_atTop X,
    hr.eventually (Icc_mem_nhds (show c / 2 < c by linarith) (show c < 2 * c by linarith))]
    with i hi hri
  rw [Real.dist_eq]
  exact hX (y i) hi (r i) hri

/-- A nonnegative slowly varying function is eventually strictly positive. -/
theorem eventually_pos_of_slowlyVarying' {L : ℝ → ℝ} (hnn : ∀ x, 0 < x → 0 ≤ L x)
    (hL : SlowlyVarying L) : ∀ᶠ x : ℝ in atTop, 0 < L x := by
  have hratio' : ∀ᶠ x : ℝ in atTop, 1 / 2 < L (1 * x) / L x :=
    (hL 1 one_pos).eventually (lt_mem_nhds (show (1 / 2 : ℝ) < 1 by norm_num))
  filter_upwards [hratio', eventually_gt_atTop (0 : ℝ)] with x hx hxpos
  have hxne : L x ≠ 0 := by
    intro hzero
    have : L (1 * x) / L x = 0 := by simp [hzero]
    linarith
  exact lt_of_le_of_ne (hnn x hxpos) hxne.symm

/-- For `x ≥ 0`, the strict tail of the step law `K - 1` is the offspring tail at `⌊x⌋₊ + 2`. -/
theorem stepLaw_tail_eq (μ : PMF ℕ) {x : ℝ} (hx : 0 ≤ x) :
    (stepLaw μ).real {z : ℤ | x < (z : ℝ)} = (μ.toMeasure (Set.Ici (⌊x⌋₊ + 2))).toReal := by
  rw [measureReal_def, stepLaw, Measure.map_apply (measurable_of_countable _)
    (MeasurableSet.of_discrete)]
  congr 2
  ext k
  simp only [mem_preimage, mem_ofPred_eq, mem_Ici]
  push_cast
  constructor
  · intro h
    have h1 := Nat.floor_le hx
    have : ((⌊x⌋₊ : ℝ) + 1) < k := by linarith
    have h2 : ⌊x⌋₊ + 1 < k := by exact_mod_cast this
    omega
  · intro h
    have h1 := Nat.lt_floor_add_one x
    have h2 : ((⌊x⌋₊ + 2 : ℕ) : ℝ) ≤ k := by exact_mod_cast h
    push_cast at h2
    linarith

/-- The strict tail of the step law in terms of `L`, for `x ≥ 0`. -/
theorem stepLaw_tail_eq_rpow {μ : PMF ℕ} {θ : ℝ} {L : ℝ → ℝ}
    (htail : ∀ j : ℕ, 1 ≤ j → (μ.toMeasure (Set.Ici j)).toReal = (j : ℝ) ^ (-θ) * L j)
    {x : ℝ} (hx : 0 ≤ x) :
    (stepLaw μ).real {z : ℤ | x < (z : ℝ)} = floorShift x ^ (-θ) * L (floorShift x) := by
  rw [stepLaw_tail_eq μ hx, htail _ (by omega)]
  rfl

/-- **Tail transfer.** If `μ[j,∞) = j^{-θ} L(j)` for `j ≥ 1` with `L` measurable, nonnegative and
slowly varying, then the strict tail `T x = P[K - 1 > x]` is regularly varying at infinity of
index `-θ`. -/
theorem isRegVaryAtTop_stepLaw_tail {μ : PMF ℕ} {θ : ℝ} {L : ℝ → ℝ} (hmeas : Measurable L)
    (hnn : ∀ x, 0 < x → 0 ≤ L x) (hL : SlowlyVarying L)
    (htail : ∀ j : ℕ, 1 ≤ j → (μ.toMeasure (Set.Ici j)).toReal = (j : ℝ) ^ (-θ) * L j) :
    IsRegVaryAtTop (fun x : ℝ => (stepLaw μ).real {z : ℤ | x < (z : ℝ)}) (-θ) := by
  intro c hc
  have hr := tendsto_floorShift_ratio hc
  have hLr : Tendsto (fun x : ℝ => L (floorShift (c * x)) / L (floorShift x)) atTop (𝓝 1) := by
    have := slow_ratio_tendsto hmeas hnn hL (l := atTop) (y := fun x => floorShift x)
      (r := fun x => floorShift (c * x) / floorShift x) hc tendsto_floorShift_atTop hr
    refine this.congr' ?_
    filter_upwards with x
    rw [div_mul_cancel₀ _ (floorShift_pos x).ne']
  have hlim := (hr.rpow_const (p := -θ) (Or.inl hc.ne')).mul hLr
  rw [mul_one] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  have hcx : 0 ≤ c * x := by positivity
  rw [stepLaw_tail_eq_rpow htail hx.le, stepLaw_tail_eq_rpow htail hcx,
    mul_div_mul_comm, Real.div_rpow (floorShift_pos _).le (floorShift_pos _).le]

/-- The strict tail is eventually strictly positive. -/
theorem stepLaw_tail_eventually_pos {μ : PMF ℕ} {θ : ℝ} {L : ℝ → ℝ}
    (hnn : ∀ x, 0 < x → 0 ≤ L x) (hL : SlowlyVarying L)
    (htail : ∀ j : ℕ, 1 ≤ j → (μ.toMeasure (Set.Ici j)).toReal = (j : ℝ) ^ (-θ) * L j) :
    ∀ᶠ x : ℝ in atTop, 0 < (stepLaw μ).real {z : ℤ | x < (z : ℝ)} := by
  have hp := tendsto_floorShift_atTop.eventually (eventually_pos_of_slowlyVarying' hnn hL)
  filter_upwards [hp, eventually_ge_atTop (0 : ℝ)] with x hx hx0
  rw [stepLaw_tail_eq_rpow htail hx0]
  exact mul_pos (Real.rpow_pos_of_pos (floorShift_pos x) _) hx

/-- The step law carries no mass below `-1` (restated from `stepLaw_lt_neg_one`). -/
theorem stepLaw_real_lt_neg_one (μ : PMF ℕ) : (stepLaw μ).real {z : ℤ | z < -1} = 0 := by
  rw [measureReal_def, stepLaw_lt_neg_one]; rfl

end BGW.StableTrees.Attraction.TailTransfer
