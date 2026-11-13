/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.DiscreteForestPaths
import Mathlib.Tactic.Linarith

/-!
# Integer grid enclosures and linear interpolation

Long regeneration gaps control short integer rises. Close enclosing grid values
then bound all integer heights between them. Convex interpolation preserves the
same enclosure, including large downward steps.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal Classical
open BGW.StableTrees.DiscreteForest
namespace BGW.StableTrees.HeightTightness

/-- The first clock endpoint after `s` determines a gap among the first `L`. -/
theorem exists_clock_gap {r : ℕ → ℕ} (hr0 : r 0 = 0) {L M s : ℕ}
    (hL : M < r L) (hs : s ≤ M) : ∃ j < L, r j ≤ s ∧ s < r (j + 1) := by
  have he : ∃ i, s < r i := ⟨L, hs.trans_lt hL⟩
  let i := Nat.find he
  have hi : s < r i := Nat.find_spec he
  have hiL : i ≤ L := Nat.find_min' he (hs.trans_lt hL)
  have hi0 : 0 < i := by
    by_contra hn
    have hz : i = 0 := by omega
    rw [hz, hr0] at hi
    omega
  refine ⟨i - 1, by omega, ?_, ?_⟩
  · have hp := Nat.find_min he (show i - 1 < i by omega)
    omega
  · simpa only [Nat.sub_add_cancel hi0] using hi

/-- Long gaps and bounded rises within gaps control every short upward variation. -/
theorem short_rise_le_of_long_gaps {h r : ℕ → ℕ} {q L M d : ℕ}
    (hr0 : r 0 = 0) (hL : M < r L)
    (hgaps : ∀ j < L, d < r (j + 1) - r j)
    (hrise : ∀ j < L, ∀ s, r j ≤ s → ∀ t, s ≤ t → t ≤ r (j + 1) → h t ≤ h s + q)
    {s t : ℕ} (hst : s ≤ t) (ht : t ≤ M) (hd : t - s ≤ d) : h t ≤ h s + 2 * q := by
  obtain ⟨j, hj, hjs, hsnext⟩ := exists_clock_gap hr0 hL (hst.trans ht)
  by_cases htnext : t ≤ r (j + 1)
  · have hh := hrise j hj s hjs t hst htnext
    omega
  · have hjnext : j + 1 < L := by
      by_contra hh
      have he : j + 1 = L := by omega
      rw [he] at htnext
      omega
    have hgap := hgaps (j + 1) hjnext
    have htnext2 : t ≤ r (j + 1 + 1) := by omega
    have hl := hrise j hj s hjs (r (j + 1)) hsnext.le le_rfl
    have hr := hrise (j + 1) hjnext (r (j + 1)) le_rfl t (by omega) htnext2
    omega

/-- Convex combinations of values in the same interval remain in that interval. -/
theorem interpolation_mem_Icc {x y l u a : ℝ} (hx : x ∈ Icc l u) (hy : y ∈ Icc l u)
    (ha : a ∈ Icc (0 : ℝ) 1) : (1 - a) * x + a * y ∈ Icc l u := by
  constructor
  · nlinarith [mul_nonneg (by linarith [ha.2] : 0 ≤ 1 - a) (sub_nonneg.mpr hx.1),
      mul_nonneg ha.1 (sub_nonneg.mpr hy.1)]
  · nlinarith [mul_nonneg (by linarith [ha.2] : 0 ≤ 1 - a) (sub_nonneg.mpr hx.2),
      mul_nonneg ha.1 (sub_nonneg.mpr hy.2)]

/-- Linear interpolation stays within bounds valid at its two neighboring integer times. -/
theorem forestHeightLin_mem_Icc {ω : ℕ → ℕ} {c l u t : ℝ} {p r : ℕ}
    (ht : 0 ≤ t) (hp : p ≤ ⌊t⌋₊) (hr : ⌊t⌋₊ + 1 ≤ r)
    (hb : ∀ i, p ≤ i → i ≤ r → c * (forestHeight ω i : ℝ) ∈ Icc l u) :
    c * forestHeightLin ω t ∈ Icc l u := by
  have ha : t - (⌊t⌋₊ : ℝ) ∈ Icc (0 : ℝ) 1 :=
    ⟨sub_nonneg.mpr (Nat.floor_le ht), by have := Nat.lt_floor_add_one t; linarith⟩
  have he : c * forestHeightLin ω t =
      (1 - (t - ⌊t⌋₊)) * (c * forestHeight ω ⌊t⌋₊) +
        (t - ⌊t⌋₊) * (c * forestHeight ω (⌊t⌋₊ + 1)) := by
    unfold forestHeightLin
    ring
  rw [he]
  exact interpolation_mem_Icc (hb _ hp (by omega)) (hb _ (by omega) hr) ha

/-- Integer rise bounds and close enclosing grid values control interpolated oscillations. -/
theorem forestHeightLin_oscillation_le_enclosing_grid {ω : ℕ → ℕ} {c η s t : ℝ}
    {p r q : ℕ} (hc : 0 ≤ c) (hs : 0 ≤ s) (ht : 0 ≤ t)
    (hps : p ≤ ⌊s⌋₊) (hsr : ⌊s⌋₊ + 1 ≤ r)
    (hpt : p ≤ ⌊t⌋₊) (htr : ⌊t⌋₊ + 1 ≤ r)
    (hend : |c * forestHeight ω p - c * forestHeight ω r| ≤ η)
    (hrise : ∀ i, p ≤ i → ∀ j, i ≤ j → j ≤ r →
      forestHeight ω j ≤ forestHeight ω i + 2 * q) :
    |c * forestHeightLin ω s - c * forestHeightLin ω t| ≤ η + 4 * c * q := by
  have hb (i : ℕ) (hpi : p ≤ i) (hir : i ≤ r) :
      c * (forestHeight ω i : ℝ) ∈
        Icc (c * forestHeight ω r - 2 * c * q) (c * forestHeight ω p + 2 * c * q) := by
    have hl : (forestHeight ω r : ℝ) ≤ forestHeight ω i + 2 * q := by
      exact_mod_cast hrise i hpi r hir le_rfl
    have hu : (forestHeight ω i : ℝ) ≤ forestHeight ω p + 2 * q := by
      exact_mod_cast hrise p le_rfl i hpi hir
    constructor <;> nlinarith [mul_le_mul_of_nonneg_left hl hc,
      mul_le_mul_of_nonneg_left hu hc]
  have hsb := forestHeightLin_mem_Icc hs hps hsr hb
  have htb := forestHeightLin_mem_Icc ht hpt htr hb
  rw [abs_le] at hend ⊢
  constructor <;> linarith [hsb.1, hsb.2, htb.1, htb.2, hend.1, hend.2]

end BGW.StableTrees.HeightTightness
