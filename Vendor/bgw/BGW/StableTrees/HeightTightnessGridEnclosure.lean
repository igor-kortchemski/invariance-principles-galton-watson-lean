/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.HeightTightnessRise

/-!
# Enclosing short interpolation windows by a fixed grid

Three grid steps enclose a short pair of interpolation times. Short upward
variations and close grid endpoint values then control their absolute difference,
without an assumption on the largest downward jump.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal Classical
open BGW.StableTrees.DiscreteForest
namespace BGW.StableTrees.HeightTightness

/-- Three grid steps enclose a short ordered pair of interpolation times. -/
theorem forestHeightLin_short_oscillation_of_grid {ω : ℕ → ℕ} {n N q : ℕ}
    {c T δ η : ℝ} (hc : 0 ≤ c) (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 4)
    (hn : 1 ≤ (n : ℝ) * δ) (hcover : T + 1 ≤ (N : ℝ) * δ)
    (hgrid : ∀ j < N,
      |c * forestHeight ω ⌊(n : ℝ) * ((j : ℝ) * δ)⌋₊ -
        c * forestHeight ω ⌊(n : ℝ) * (((j + 1 : ℕ) : ℝ) * δ)⌋₊| ≤ η)
    (hrise : ∀ i j : ℕ, i ≤ j → j ≤ ⌊(n : ℝ) * ((N : ℝ) * δ)⌋₊ →
      j - i ≤ ⌊(n : ℝ) * (4 * δ)⌋₊ → forestHeight ω j ≤ forestHeight ω i + 2 * q)
    {s t : ℝ} (hs : s ∈ Icc (0 : ℝ) T) (ht : t ∈ Icc (0 : ℝ) T)
    (hst : s ≤ t) (hd : t - s ≤ δ) :
    |c * forestHeightLin ω ((n : ℝ) * s) -
      c * forestHeightLin ω ((n : ℝ) * t)| ≤ 3 * η + 4 * c * q := by
  have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  let k := ⌊s / δ⌋₊
  have hklo : (k : ℝ) * δ ≤ s := (le_div_iff₀ hδ).mp
    (Nat.floor_le (div_nonneg hs.1 hδ.le))
  have hkhi : s < ((k : ℝ) + 1) * δ := (div_lt_iff₀ hδ).mp
    (Nat.lt_floor_add_one (s / δ))
  have hkN : k + 3 ≤ N := by
    have hb : ((k : ℝ) + 3) * δ ≤ (N : ℝ) * δ := by nlinarith [hs.2]
    have he : (k : ℝ) + 3 ≤ N := (mul_le_mul_iff_left₀ hδ).mp hb
    exact_mod_cast he
  let p := ⌊(n : ℝ) * ((k : ℝ) * δ)⌋₊
  let r := ⌊(n : ℝ) * (((k + 3 : ℕ) : ℝ) * δ)⌋₊
  have hpS : p ≤ ⌊(n : ℝ) * s⌋₊ := Nat.floor_mono (mul_le_mul_of_nonneg_left hklo hn0)
  have hpT : p ≤ ⌊(n : ℝ) * t⌋₊ := Nat.floor_mono
    (mul_le_mul_of_nonneg_left (hklo.trans hst) hn0)
  have hrS : ⌊(n : ℝ) * s⌋₊ + 1 ≤ r := by
    apply Nat.le_floor
    have hf := Nat.floor_le (mul_nonneg hn0 hs.1)
    push_cast
    nlinarith [mul_nonneg hn0 (sub_nonneg.mpr (le_of_lt hkhi))]
  have hrT : ⌊(n : ℝ) * t⌋₊ + 1 ≤ r := by
    apply Nat.le_floor
    have hf := Nat.floor_le (mul_nonneg hn0 ht.1)
    push_cast
    nlinarith [mul_nonneg hn0 (sub_nonneg.mpr (le_of_lt hkhi)),
      mul_nonneg hn0 (sub_nonneg.mpr hd)]
  have hpr : p ≤ r := by omega
  have hrM : r ≤ ⌊(n : ℝ) * ((N : ℝ) * δ)⌋₊ := by
    apply Nat.floor_mono
    apply mul_le_mul_of_nonneg_left _ hn0
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hkN) hδ.le
  have hwidth : r - p ≤ ⌊(n : ℝ) * (4 * δ)⌋₊ := by
    apply Nat.le_floor
    rw [Nat.cast_sub hpr]
    have hpright : (p : ℝ) + 1 > (n : ℝ) * ((k : ℝ) * δ) := Nat.lt_floor_add_one _
    have hrright : (r : ℝ) ≤ (n : ℝ) * (((k + 3 : ℕ) : ℝ) * δ) :=
      Nat.floor_le (by positivity)
    push_cast at hrright
    nlinarith
  have h0 := hgrid k (by omega)
  have h1 := hgrid (k + 1) (by omega)
  have h2 := hgrid (k + 2) (by omega)
  have hend : |c * forestHeight ω p - c * forestHeight ω r| ≤ 3 * η := by
    have ht1 := abs_sub_le (c * (forestHeight ω p : ℝ))
      (c * (forestHeight ω ⌊(n : ℝ) * (((k + 1 : ℕ) : ℝ) * δ)⌋₊ : ℝ))
      (c * (forestHeight ω r : ℝ))
    have ht2 := abs_sub_le
      (c * (forestHeight ω ⌊(n : ℝ) * (((k + 1 : ℕ) : ℝ) * δ)⌋₊ : ℝ))
      (c * (forestHeight ω ⌊(n : ℝ) * (((k + 2 : ℕ) : ℝ) * δ)⌋₊ : ℝ))
      (c * (forestHeight ω r : ℝ))
    have he1 : k + 1 + 1 = k + 2 := by omega
    have he2 : k + 2 + 1 = k + 3 := by omega
    rw [he1] at h1
    rw [he2] at h2
    change |c * forestHeight ω p - c *
      forestHeight ω ⌊(n : ℝ) * (((k + 1 : ℕ) : ℝ) * δ)⌋₊| ≤ η at h0
    change |c * forestHeight ω ⌊(n : ℝ) * (((k + 2 : ℕ) : ℝ) * δ)⌋₊ -
      c * forestHeight ω r| ≤ η at h2
    linarith
  exact forestHeightLin_oscillation_le_enclosing_grid hc (mul_nonneg hn0 hs.1)
    (mul_nonneg hn0 ht.1) hpS hrS hpT hrT hend
    (fun i hpi j hij hjr => hrise i j hij (hjr.trans hrM) (by omega))

end BGW.StableTrees.HeightTightness
