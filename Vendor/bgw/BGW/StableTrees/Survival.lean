/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.SurvivalLimit
public import BGW.StableTrees.SurvivalConsequences

/-!
# Survival of critical BGW trees in the stable domain

Asymptotics of survival at the stable height scale and their extinction consequences.
-/

@[expose] public section

open MeasureTheory Filter
open scoped Topology ENNReal

namespace BGW.StableTrees.Survival

/-- The floor index `k_n = ⌊δ n / B_n⌋` satisfies `k_n B_n / n → δ`. -/
theorem tendsto_floor_scale {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ} (h : StableDomain μ θ B)
    {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun n : ℕ => (⌊δ * (n : ℝ) / B n⌋₊ : ℝ) * B n / n) atTop (𝓝 δ) := by
  have hpos : Tendsto (fun n : ℕ => B n / n) atTop (𝓝[>] 0) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨tendsto_B_div_n h, ?_⟩
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact div_pos (h.pos n hn) (by exact_mod_cast (by omega : 0 < n))
  have hnB : Tendsto (fun n : ℕ => (n : ℝ) / B n) atTop atTop := by
    apply hpos.inv_tendsto_nhdsGT_zero.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hB := (h.pos n hn).ne'
    have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
    dsimp only [Pi.inv_apply]
    field_simp
  have hx : Tendsto (fun n : ℕ => δ * (n : ℝ) / B n) atTop atTop := by
    apply hnB.const_mul_atTop hδ |>.congr'
    filter_upwards [] with n
    ring
  have hf := (tendsto_nat_floor_div_atTop (R := ℝ)).comp hx
  have hprod := hf.mul_const δ
  rw [one_mul] at hprod
  apply hprod.congr'
  filter_upwards [eventually_ge_atTop 1, hx.eventually_gt_atTop 0] with n hn hxn
  have hB := (h.pos n hn).ne'
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  dsimp only [Function.comp_def]
  field_simp

/-- The floor form `k_n = ⌊δ n / B_n⌋`. -/
theorem tendsto_survivalProb_floor {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ} (h : StableDomain μ θ B)
    {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun n : ℕ => B n * survivalProb μ ⌊δ * (n : ℝ) / B n⌋₊) atTop
      (𝓝 (csbpSurvival θ δ)) := by
  exact tendsto_survivalProb_scaled h hδ (tendsto_floor_scale h hδ)

/-- The blueprint's uniform bound. -/
theorem survival_bound {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ} (h : StableDomain μ θ B)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ C, 0 < C ∧ ∀ᶠ n in atTop, B n * survivalProb μ ⌊δ * (n : ℝ) / B n⌋₊ ≤ C := by
  exact exists_pos_eventually_le_of_tendsto (tendsto_survivalProb_floor h hδ)

/-- `⌊a B_n⌋` independent trees: expected number reaching height `k_n` tends to `a v(δ)`. -/
theorem tendsto_floor_mul_survivalProb {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ}
    (h : StableDomain μ θ B) {δ : ℝ} (hδ : 0 < δ) {k : ℕ → ℕ}
    (hk : Tendsto (fun n : ℕ => (k n : ℝ) * B n / n) atTop (𝓝 δ)) {a : ℝ} (ha : 0 ≤ a) :
    Tendsto (fun n : ℕ => (⌊a * B n⌋₊ : ℝ) * survivalProb μ (k n)) atTop
      (𝓝 (a * csbpSurvival θ δ)) := by
  exact tendsto_floor_mul_of_scaled (tendsto_B_atTop h)
    (tendsto_survivalProb_scaled h hδ hk) ha

/-- **Extinction condition** (DLG): `⌊a B_n⌋` independent trees all die before generation
`k_n` with probability tending to `exp(-a v(δ))`. -/
theorem tendsto_extinction_pow {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ} (h : StableDomain μ θ B)
    {δ : ℝ} (hδ : 0 < δ) {k : ℕ → ℕ}
    (hk : Tendsto (fun n : ℕ => (k n : ℝ) * B n / n) atTop (𝓝 δ)) {a : ℝ} (ha : 0 ≤ a) :
    Tendsto (fun n : ℕ => (1 - survivalProb μ (k n)) ^ ⌊a * B n⌋₊) atTop
      (𝓝 (Real.exp (-(a * csbpSurvival θ δ)))) := by
  exact tendsto_extinction_pow_of_scaled (tendsto_B_atTop h)
    (tendsto_survivalProb_scaled h hδ hk) (csbpSurvival_pos h.alpha_mem.1 hδ) ha

/-- Floor form of `tendsto_floor_mul_survivalProb` (the K11 union bound). -/
theorem tendsto_floor_mul_survivalProb_floor {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ}
    (h : StableDomain μ θ B) {δ : ℝ} (hδ : 0 < δ) {a : ℝ} (ha : 0 ≤ a) :
    Tendsto (fun n : ℕ => (⌊a * B n⌋₊ : ℝ) * survivalProb μ ⌊δ * (n : ℝ) / B n⌋₊) atTop
      (𝓝 (a * csbpSurvival θ δ)) := by
  exact tendsto_floor_mul_survivalProb h hδ (tendsto_floor_scale h hδ) ha

/-- Floor form of `tendsto_extinction_pow`; `a = 1` is DLG's extinction condition. -/
theorem tendsto_extinction_pow_floor {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ}
    (h : StableDomain μ θ B) {δ : ℝ} (hδ : 0 < δ) {a : ℝ} (ha : 0 ≤ a) :
    Tendsto (fun n : ℕ => (1 - survivalProb μ ⌊δ * (n : ℝ) / B n⌋₊) ^ ⌊a * B n⌋₊) atTop
      (𝓝 (Real.exp (-(a * csbpSurvival θ δ)))) := by
  exact tendsto_extinction_pow h hδ (tendsto_floor_scale h hδ) ha

end BGW.StableTrees.Survival
