/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.SupremumDrawdown
public import BGW.StableTrees.SupremumLadderRestart
public import BGW.StableTrees.SupremumPotential

/-!
# Ladder exponent algebra and Laplace functionals

Algebra of the exact ladder exponent and the boundary and ladder Laplace functionals.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees

/-- The boundary potential of the path: `∫_{(0,∞)} e^{-qt-λS_t} dM_t`, `M = supLocalTime`
(Stieltjes measure `supLocalTimeStieltjes`), in `ℝ≥0∞` (no junk). -/
noncomputable def supBoundaryPotential (θ q lam : ℝ) (f : DLoc) : ℝ≥0∞ :=
  ∫⁻ t in Ioi (0 : ℝ),
    ENNReal.ofReal (Real.exp (-q * t - lam * supRunning f t.toNNReal))
      ∂(supLocalTimeStieltjes θ f).measure

/-- The ladder Laplace transform `φ_{q,λ}(z) = E exp(-q A_z - λ B_z)`. -/
noncomputable def supLadderLaplace (θ q lam : ℝ) (z : ℝ≥0) : ℝ :=
  ∫ f, Real.exp (-q * (supLadderTime θ z f : ℝ) - lam * supLadderHeight θ z f)
    ∂(stableLocalLaw θ : Measure DLoc)

/-- `κ(q,λ) > 0` for `q > 0`, `λ ≥ 0` (both branches; diagonal `θ q^{1-1/θ} > 0`). -/
theorem supLadderExponent_pos {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {q lam : ℝ} (hq : 0 < q)
    (hlam : 0 ≤ lam) : 0 < supLadderExponent θ q lam := by
  have hθ0 : 0 < θ := zero_lt_one.trans hθ.1
  have hPhi : 0 < q ^ (1 / θ) := Real.rpow_pos_of_pos hq _
  have hroot : (q ^ (1 / θ)) ^ θ = q := by
    rw [← Real.rpow_mul hq.le, one_div_mul_cancel hθ0.ne', Real.rpow_one]
  unfold supLadderExponent
  split_ifs with he
  · exact mul_pos hθ0 (Real.rpow_pos_of_pos hq _)
  · rcases lt_or_gt_of_ne he with hl | hl
    · have hp := Real.rpow_lt_rpow hlam hl hθ0
      rw [hroot] at hp
      exact div_pos (sub_pos.mpr hp) (sub_pos.mpr hl)
    · have hp := Real.rpow_lt_rpow hPhi.le hl hθ0
      rw [hroot] at hp
      exact div_pos_of_neg_of_neg (sub_neg.mpr hp) (sub_neg.mpr hl)

/-- **`1/κ` is the mean potential** `(Φ/q) F_q(λ)`, including the diagonal
(`F_q(Φ) = 1/θ`, from `BGW.StableTrees.SupremumDrawdown`).  Pure algebra from
`integral_exp_neg_supRunning_expTime`; no ladder object enters.

Reference: Bertoin, *Lévy Processes*, Chapter VI. -/
theorem inv_supLadderExponent_eq_integral {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {q lam : ℝ}
    (hq : 0 < q) (hlam : 0 ≤ lam) :
    (supLadderExponent θ q lam)⁻¹ =
      q ^ (1 / θ) / q *
        ∫ p, Real.exp (-lam * supRunning p.1 p.2.toNNReal) ∂expClockLaw θ q := by
  have hθ0 : 0 < θ := zero_lt_one.trans hθ.1
  have hPhi : 0 < q ^ (1 / θ) := Real.rpow_pos_of_pos hq _
  by_cases he : lam = q ^ (1 / θ)
  · subst lam
    rw [supLadderExponent_diagonal, integral_exp_neg_supRunning_expTime_diag hθ hq]
    have hp : q ^ (1 - 1 / θ) = q / q ^ (1 / θ) :=
      Real.rpow_one_sub' hq.le (by
        have : 1 / θ < 1 := (div_lt_one hθ0).mpr hθ.1
        linarith)
    rw [hp]
    field_simp
  · rw [integral_exp_neg_supRunning_expTime hθ hq hlam he]
    simp only [supLadderExponent, ite_eq_right he, inv_div]
    field_simp

/-- Off the diagonal: `1/κ = (Φ-λ)/(q-λ^θ)`.

Reference: Bertoin, *Lévy Processes*, Chapter VI. -/
theorem inv_supLadderExponent_eq_of_ne {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {q lam : ℝ}
    (hq : 0 < q) (hlam : 0 ≤ lam) (hne : lam ≠ q ^ (1 / θ)) :
    (supLadderExponent θ q lam)⁻¹ = (q ^ (1 / θ) - lam) / (q - lam ^ θ) := by
  -- `hθ`, `hq` and `hlam` are part of the stated interface; the identity holds without
  -- them because division is totalized.
  have _hθ := hθ
  have _hq := hq
  have _hlam := hlam
  simp only [supLadderExponent, ite_eq_right hne, inv_div]

/-- Continuity of `κ` in `q ↓ 0` at fixed `λ ≥ 0` (to `κ(0,λ) = λ^{θ-1}`; at `λ = 0` the
value is `0`), needed to pass from `q > 0` to `q = 0`. -/
theorem tendsto_supLadderExponent_zero {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {lam : ℝ}
    (hlam : 0 ≤ lam) :
    Tendsto (fun q : ℝ => supLadderExponent θ q lam) (𝓝[>] 0)
      (𝓝 (supLadderExponent θ 0 lam)) := by
  have hθ0 : 0 < θ := zero_lt_one.trans hθ.1
  have hα : 0 < 1 / θ := one_div_pos.mpr hθ0
  by_cases hl : lam = 0
  · subst lam
    have hβ : 0 < 1 - 1 / θ := sub_pos.mpr ((div_lt_one hθ0).mpr hθ.1)
    have hp : Tendsto (fun q : ℝ => q ^ (1 - 1 / θ)) (𝓝[>] 0) (𝓝 (0 ^ (1 - 1 / θ))) :=
      (Real.continuous_rpow_const hβ.le).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    rw [supLadderExponent_zero_right hθ (le_refl 0)]
    apply hp.congr'
    filter_upwards [self_mem_nhdsWithin] with q hq
    exact (supLadderExponent_zero_right hθ hq.le).symm
  · have hp : Tendsto (fun q : ℝ => q ^ (1 / θ)) (𝓝[>] 0) (𝓝 0) := by
      simpa only [Real.zero_rpow hα.ne'] using
        (Real.continuous_rpow_const hα.le).continuousAt.tendsto.mono_left
          (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
    have hn : Tendsto (fun q : ℝ => (q - lam ^ θ) / (q ^ (1 / θ) - lam))
        (𝓝[>] 0) (𝓝 ((0 - lam ^ θ) / (0 - lam))) :=
      (tendsto_id.mono_left nhdsWithin_le_nhds |>.sub_const _).div
        (hp.sub_const lam) (by simpa using hl)
    have he : ∀ᶠ q : ℝ in 𝓝[>] 0, lam ≠ q ^ (1 / θ) := by
      have hh := hp.eventually (isOpen_compl_singleton.mem_nhds (Ne.symm hl))
      filter_upwards [hh] with q hq
      exact Ne.symm hq
    have hzero : supLadderExponent θ 0 lam = (0 - lam ^ θ) / (0 - lam) := by
      simp only [supLadderExponent, Real.zero_rpow hα.ne', ite_eq_right hl]
    rw [hzero]
    apply hn.congr'
    filter_upwards [he] with q hq
    simp only [supLadderExponent, ite_eq_right hq]

end BGW.StableTrees
