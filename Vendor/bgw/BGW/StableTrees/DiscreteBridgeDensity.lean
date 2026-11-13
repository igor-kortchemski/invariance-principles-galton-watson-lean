/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.DiscreteBridgeBasic
public import BGW.StableTrees.Scalar.ForestBounds

/-!
# Uniform bounds for discrete bridge prefix densities

The scalar local upper bound and admissible endpoint lower bound, combined with
regular variation of the norming, control every prefix strictly before time one.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal Classical

namespace BGW.StableTrees.DiscreteBridge

open BGW BGW.Skorokhod BGW.Probability.RealWalk

/-- The bridge prefix density as a function of the path on `[0,a]`:
`walkProb μ (n-m) (-1-W_m) / walkProb μ n (-1)`, `m = ⌊a n⌋`, `W_m = B n * x(a)` rounded. -/
noncomputable def bridgePathDensity (μ : PMF ℕ) (B : ℕ → ℝ) (n : ℕ) (a : ℝ≥0)
    (x : D (a : ℝ) ℝ) : ℝ :=
  walkProb μ ((n - ⌊(a : ℝ) * n⌋₊ : ℕ) : ℤ) (-1 - round (endValue a x * B n)) /
    walkProb μ (n : ℤ) (-1)

/-- The remaining number of increments divided by the full size tends to `1-a`. -/
theorem bridgeRemaining_ratio (a : ℝ≥0) (ha : a ∈ Ioo (0 : ℝ≥0) 1) :
    Tendsto (fun n : ℕ => ((n - ⌊(a : ℝ) * n⌋₊ : ℕ) : ℝ) / n) atTop
      (𝓝 (1 - (a : ℝ))) := by
  have ha0 : 0 < (a : ℝ) := by exact_mod_cast ha.1
  have ha1 : (a : ℝ) < 1 := by exact_mod_cast ha.2
  have hfloorle (n : ℕ) : ⌊(a : ℝ) * n⌋₊ ≤ n := by
    apply Nat.floor_le_of_le
    nlinarith [show (0 : ℝ) ≤ n from Nat.cast_nonneg n]
  have hfloor :
      Tendsto (fun n : ℕ => (⌊(a : ℝ) * n⌋₊ : ℝ) / n) atTop (𝓝 (a : ℝ)) := by
    have ht := (tendsto_nat_floor_div_atTop.comp
      (tendsto_natCast_atTop_atTop.const_mul_atTop ha0)).mul_const (a : ℝ)
    rw [one_mul] at ht
    refine ht.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hnR : (n : ℝ) ≠ 0 := by positivity
    dsimp only [Function.comp_apply]
    field_simp [ha0.ne']
  have ht := (tendsto_const_nhds (x := (1 : ℝ))).sub hfloor
  refine ht.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnR : (n : ℝ) ≠ 0 := by positivity
  rw [Nat.cast_sub (hfloorle _)]
  field_simp

/-- **Uniform bound** of the bridge prefix density for a fixed `a < 1`
(`Scalar.exists_walkProb_le`, `Scalar.exists_lower_bound_neg_one`, regular variation of `B`). -/
theorem bridgePathDensity_le {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ} (h : StableDomain μ θ B)
    (a : ℝ≥0) (ha : a ∈ Ioo (0 : ℝ≥0) 1) :
    ∃ C : ℝ, ∀ᶠ n : ℕ in atTop, Admissible μ n → ∀ x : D (a : ℝ) ℝ,
      0 ≤ bridgePathDensity μ B n a x ∧ bridgePathDensity μ B n a x ≤ C := by
  have ha0 : 0 < (a : ℝ) := by exact_mod_cast ha.1
  have ha1 : (a : ℝ) < 1 := by exact_mod_cast ha.2
  let R : ℕ → ℕ := fun n => n - ⌊(a : ℝ) * n⌋₊
  have hRlim := bridgeRemaining_ratio a ha
  have hRpos (n : ℕ) (hn : 1 ≤ n) : 1 ≤ R n := by
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hf : ⌊(a : ℝ) * n⌋₊ < n :=
      (Nat.floor_lt (mul_nonneg a.coe_nonneg hnR.le)).mpr (by nlinarith)
    dsimp only [R]
    omega
  obtain ⟨C₀, hC₀⟩ := Scalar.exists_walkProb_le h
  obtain ⟨c, hc, hclower⟩ := Scalar.exists_lower_bound_neg_one h
  have hC₀nn : 0 ≤ C₀ := by
    have hle := (Scalar.walkProb_nonneg μ 1 0).trans (hC₀ 1 le_rfl 0)
    simpa using (le_div_iff₀ (h.pos 1 le_rfl)).mp hle
  let L : ℝ := (1 - (a : ℝ)) ^ (-(1 / θ))
  have hratio : Tendsto (fun n => B n / B (R n)) atTop (𝓝 L) :=
    Scalar.tendsto_div_of_tendsto_div h (sub_pos.mpr ha1) hRlim
  have hbound : ∀ᶠ n : ℕ in atTop, B n / B (R n) ≤ L + 1 :=
    (hratio.eventually (gt_mem_nhds (lt_add_one L))).mono fun _ hn => hn.le
  refine ⟨C₀ / c * (L + 1), ?_⟩
  filter_upwards [hbound, eventually_ge_atTop 1] with n hn hn1 hadm x
  have hp : 0 < walkProb μ n (-1) := by
    have hmass := offspringVec_countBridges_ne_zero hadm
    have heq : offspringVec μ n (countBridges n) = walkLaw μ n {-1} := by
      rw [offspringVec, Scalar.walkLaw_eq_map_offspring_sum]
      rw [Measure.map_apply (by fun_prop) (measurableSet_singleton _)]
      congr 1
      ext ω
      rw [← stepWord_mem_bridgeWords_iff]
      simp only [bridgeWords, mem_ofPred_eq, stepWord, List.length_ofFn, true_and,
        List.sum_ofFn, mem_preimage, mem_singleton_iff]
      exact ⟨fun ht => ht.2, fun hs => ⟨fun j hj => by
        obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hj
        omega, hs⟩⟩
    rw [heq] at hmass
    rw [Scalar.walkProb_coe_nat]
    exact ENNReal.toReal_pos hmass (measure_ne_top _ _)
  have hnB := h.pos n hn1
  have hRB := h.pos (R n) (hRpos n hn1)
  have hlow := hclower n hn1 hp
  have hnum := hC₀ (R n) (hRpos n hn1)
    (-1 - round (endValue a x * B n))
  have hnn := Scalar.walkProb_nonneg μ (R n) (-1 - round (endValue a x * B n))
  change 0 ≤ walkProb μ (R n) _ / walkProb μ n (-1) ∧
    walkProb μ (R n) _ / walkProb μ n (-1) ≤ _
  refine ⟨div_nonneg hnn hp.le, ?_⟩
  calc
    walkProb μ (R n) _ / walkProb μ n (-1) ≤ (C₀ / B (R n)) / (c / B n) :=
      div_le_div₀ (div_nonneg hC₀nn hRB.le) hnum (div_pos hc hnB) hlow
    _ = C₀ / c * (B n / B (R n)) := by field_simp
    _ ≤ C₀ / c * (L + 1) := mul_le_mul_of_nonneg_left hn (div_nonneg hC₀nn hc.le)

end BGW.StableTrees.DiscreteBridge
