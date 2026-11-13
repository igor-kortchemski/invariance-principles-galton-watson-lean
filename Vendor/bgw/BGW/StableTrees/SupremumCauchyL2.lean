/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.SupremumCauchyBounds

/-!
# Compact square-mean Cauchy estimates

The explicit constant combines the compact Doob inequality with discount removal.

## References

* [J. Bertoin, *Lévy Processes*, Cambridge University Press, 1996, Chapter IV]
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees

/-- **Explicit compact `L²` estimate**:
`E sup_{t≤T}|O_ε-O_η|² ≤ 128 e^{2T}(D + D²)` whenever `‖u¹_ε-u¹_η‖_∞ ≤ D`,
uniformly in the initial state `0`, with integrability. -/
theorem integral_sq_compactError_le {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {ε η : ℝ} (hε : 0 < ε)
    (hη : 0 < η) {D : ℝ}
    (hD : ∀ y : ℝ, |supOccupationResolvent θ 1 ε y - supOccupationResolvent θ 1 η y| ≤ D)
    (T : ℝ≥0) :
    Integrable (fun f => (compactError ε η T f) ^ 2) (stableLocalLaw θ : Measure DLoc) ∧
      ∫ f, (compactError ε η T f) ^ 2 ∂(stableLocalLaw θ : Measure DLoc) ≤
        128 * Real.exp (2 * (T : ℝ)) * (D + D ^ 2) := by
  let H := fun f => ⨆ t : Set.Iic T, |occupationDiffMartingale θ ε η t f|
  have hi := integrable_sq_compactError θ hε hη T
  obtain ⟨hH, hb⟩ := integral_sq_sup_occupationDiffMartingale_le hθ hε hη hD T
  have hg : Integrable (fun f => 8 * Real.exp (2 * (T : ℝ)) * (H f ^ 2 + D ^ 2))
      (stableLocalLaw θ : Measure DLoc) := (hH.add (integrable_const _)).const_mul _
  have hp : ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc),
      compactError ε η T f ^ 2 ≤ 8 * Real.exp (2 * (T : ℝ)) * (H f ^ 2 + D ^ 2) := by
    filter_upwards [ae_compactError_le hθ hε hη hD] with f hf
    have he : Real.exp (2 * (T : ℝ)) = Real.exp (T : ℝ) ^ 2 := by
      rw [two_mul, Real.exp_add, pow_two]
    have hs := pow_le_pow_left₀ (compactError_nonneg hε hη T f) (hf T) 2
    have hsum : (H f + D) ^ 2 ≤ 2 * (H f ^ 2 + D ^ 2) := by
      nlinarith only [sq_nonneg (H f - D)]
    calc
      _ ≤ (2 * Real.exp (T : ℝ) * (H f + D)) ^ 2 := hs
      _ = (2 * Real.exp (T : ℝ)) ^ 2 * (H f + D) ^ 2 := mul_pow _ _ _
      _ ≤ (2 * Real.exp (T : ℝ)) ^ 2 * (2 * (H f ^ 2 + D ^ 2)) :=
        mul_le_mul_of_nonneg_left hsum (sq_nonneg _)
      _ = _ := by rw [he]; ring
  have hle := integral_mono_ae hi hg hp
  rw [integral_const_mul, integral_add hH (integrable_const _)] at hle
  simp only [integral_const, Measure.real, measure_univ, ENNReal.toReal_one,
    smul_eq_mul, one_mul] at hle
  refine ⟨hi, hle.trans ?_⟩
  have hexp : 0 ≤ Real.exp (2 * (T : ℝ)) := (Real.exp_pos _).le
  calc
    8 * Real.exp (2 * (T : ℝ)) * ((∫ f, H f ^ 2
        ∂(stableLocalLaw θ : Measure DLoc)) + D ^ 2) ≤
        8 * Real.exp (2 * (T : ℝ)) * (16 * D + D ^ 2) :=
      mul_le_mul_of_nonneg_left (by
        linarith only [hb]) (by positivity)
    _ ≤ 128 * Real.exp (2 * (T : ℝ)) * (D + D ^ 2) := by
      nlinarith only [mul_nonneg hexp (sq_nonneg D)]

/-- **Compact-time Cauchy estimate**. -/
theorem supOccupation_compact_L2_cauchy {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (T : ℝ≥0) :
    ∀ δ : ℝ, 0 < δ → ∃ a : ℝ, 0 < a ∧
      ∀ ε η : ℝ, 0 < ε → ε < a → 0 < η → η < a →
        Integrable (fun f => (compactError ε η T f) ^ 2) (stableLocalLaw θ : Measure DLoc) ∧
        (∫ f, (compactError ε η T f) ^ 2 ∂(stableLocalLaw θ : Measure DLoc)) ≤ δ := by
  intro δ hδ
  let D := min 1 (δ / (256 * Real.exp (2 * (T : ℝ))))
  have hDpos : 0 < D := lt_min zero_lt_one (by positivity)
  obtain ⟨a, ha, hb⟩ := exists_forall_abs_supOccupationResolvent_sub_le hθ hDpos
  refine ⟨a, ha, fun ε η hε hεa hη hηa => ?_⟩
  obtain ⟨hi, hle⟩ := integral_sq_compactError_le hθ hε hη (hb ε η hε hεa hη hηa) T
  refine ⟨hi, hle.trans ?_⟩
  have hD1 : D ≤ 1 := min_le_left _ _
  have hDb : D ≤ δ / (256 * Real.exp (2 * (T : ℝ))) := min_le_right _ _
  have hDD : D ^ 2 ≤ D := by nlinarith only [mul_nonneg hDpos.le (sub_nonneg.mpr hD1)]
  calc
    128 * Real.exp (2 * (T : ℝ)) * (D + D ^ 2) ≤
        256 * Real.exp (2 * (T : ℝ)) * D := by
      nlinarith only [mul_le_mul_of_nonneg_left hDD (Real.exp_pos (2 * (T : ℝ))).le]
    _ ≤ δ := by
      have hh := (le_div_iff₀ (by positivity : 0 < 256 * Real.exp (2 * (T : ℝ)))).1 hDb
      simpa only [mul_comm] using hh

end BGW.StableTrees
