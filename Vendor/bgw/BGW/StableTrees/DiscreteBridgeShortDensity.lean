/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.DiscreteBridgeLocalLimit

/-!
# A density bound uniform over short prefixes

All cutoffs at most one half share a single density bound. This lets small-block
maximal estimates control a shrinking initial or terminal window.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal Classical

namespace BGW.StableTrees.DiscreteBridge

open BGW BGW.Skorokhod

/-- A single positive constant bounds every bridge density with cutoff at most one half. -/
theorem bridgePathDensity_short_le {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ}
    (h : StableDomain μ θ B) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop, Admissible μ n →
      ∀ a : ℝ≥0, 0 < a → (a : ℝ) ≤ 1 / 2 → ∀ x : D (a : ℝ) ℝ,
        bridgePathDensity μ B n a x ≤ C := by
  let a₀ : ℝ≥0 := 1 / 2
  have ha₀ : a₀ ∈ Ioo (0 : ℝ≥0) 1 := by norm_num [a₀]
  let L : ℝ := (1 - (a₀ : ℝ)) ^ (-(1 / θ))
  have hL : 0 < L := Real.rpow_pos_of_pos (by norm_num [a₀]) _
  have hratio := bridgeRemaining_norming_ratio h a₀ ha₀
  have hratbound : ∀ᶠ n in atTop, B n / B (n - ⌊(a₀ : ℝ) * n⌋₊) ≤ L + 1 :=
    (hratio.eventually (gt_mem_nhds (lt_add_one L))).mono fun _ hh => hh.le
  obtain ⟨U, hU⟩ := Scalar.exists_walkProb_le h
  obtain ⟨c, hc, hclower⟩ := Scalar.exists_lower_bound_neg_one h
  have hUnn : 0 ≤ U := by
    have hle := (Scalar.walkProb_nonneg μ 1 0).trans (hU 1 le_rfl 0)
    simpa using (le_div_iff₀ (h.pos 1 le_rfl)).mp hle
  refine ⟨U / c * (L + 1) + 1, by positivity, ?_⟩
  filter_upwards [hratbound, eventually_ge_atTop 1] with n hrat hn hadm a ha haHalf x
  have _ := ha
  have hfloorhalf : ⌊(a₀ : ℝ) * n⌋₊ < n := by
    apply (Nat.floor_lt (by positivity)).mpr
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    norm_num [a₀]
    linarith
  have hfloor : ⌊(a : ℝ) * n⌋₊ ≤ ⌊(a₀ : ℝ) * n⌋₊ := by
    apply Nat.floor_mono
    exact mul_le_mul_of_nonneg_right (by simpa [a₀] using haHalf) (Nat.cast_nonneg n)
  have hR : 1 ≤ n - ⌊(a₀ : ℝ) * n⌋₊ := by omega
  have hm : 1 ≤ n - ⌊(a : ℝ) * n⌋₊ := by omega
  have hBR := h.pos _ hR
  have hBm := h.pos _ hm
  have hBn := h.pos n hn
  have hnum := hU (n - ⌊(a : ℝ) * n⌋₊) hm (-1 - round (endValue a x * B n))
  have hnorm : B (n - ⌊(a₀ : ℝ) * n⌋₊) ≤ B (n - ⌊(a : ℝ) * n⌋₊) :=
    h.monotone (Nat.sub_le_sub_left hfloor n)
  have hnum' : walkProb μ ((n - ⌊(a : ℝ) * n⌋₊ : ℕ) : ℤ)
      (-1 - round (endValue a x * B n)) ≤ U / B (n - ⌊(a₀ : ℝ) * n⌋₊) :=
    hnum.trans (div_le_div_of_nonneg_left hUnn hBR hnorm)
  have hlow := hclower n hn (walkProb_neg_one_pos hadm)
  change walkProb μ _ _ / walkProb μ n (-1) ≤ _
  calc
    _ ≤ (U / B (n - ⌊(a₀ : ℝ) * n⌋₊)) / (c / B n) :=
      div_le_div₀ (div_nonneg hUnn hBR.le) hnum' (div_pos hc hBn) hlow
    _ = U / c * (B n / B (n - ⌊(a₀ : ℝ) * n⌋₊)) := by field_simp
    _ ≤ U / c * (L + 1) := mul_le_mul_of_nonneg_left hrat (div_nonneg hUnn hc.le)
    _ ≤ U / c * (L + 1) + 1 := by linarith

end BGW.StableTrees.DiscreteBridge
