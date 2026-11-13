/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.StableProcessLaw
public import BGW.StableTrees.StableProcessJumps
import Mathlib.MeasureTheory.Measure.Portmanteau

/-!
# Spectral positivity of the stable process

The offspring-law witness of `exists_stableDomain` has no step below `-1`. Its
reciprocal-normalizer jump bound passes to the unique limiting law by the closed-set inequality
in the Portmanteau theorem (Billingsley, *Convergence of Probability Measures*, 2nd ed., 1999,
Theorem 2.1). The limit is spectrally positive; Bertoin, *Lévy Processes*, 1996, Chapter VII,
treats the mirror image (spectrally negative processes).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology

namespace BGW.StableTrees

open BGW.Skorokhod BGW.Probability.RealWalk

private theorem ae_offspring_step_ge (μ : PMF ℕ) :
    ∀ᵐ x : ℝ ∂(realOffspringStepLaw μ : Measure ℝ), -1 ≤ x := by
  change ∀ᵐ x : ℝ ∂((stepLaw μ).map (fun z : ℤ => (z : ℝ))), -1 ≤ x
  rw [ae_map_iff (measurable_of_countable _).aemeasurable measurableSet_Ici]
  change ∀ᵐ z : ℤ ∂(μ.toMeasure.map (fun k : ℕ => (k : ℤ) - 1)), -1 ≤ (z : ℝ)
  rw [ae_map_iff (measurable_of_countable _).aemeasurable
    (MeasurableSet.of_discrete)]
  exact Eventually.of_forall fun k => by
    push_cast
    linarith [Nat.cast_nonneg (α := ℝ) k]

private theorem ae_offspring_sequence_ge (μ : PMF ℕ) :
    ∀ᵐ ω : ℕ → ℝ ∂(iidLaw (realOffspringStepLaw μ) : Measure (ℕ → ℝ)),
      ∀ i, -1 ≤ ω i := by
  apply ae_all_iff.mpr
  intro i
  have hh := ae_offspring_step_ge μ
  rw [← map_coord (realOffspringStepLaw μ) i] at hh
  exact (ae_map_iff (measurable_pi_apply i).aemeasurable measurableSet_Ici).mp hh

private theorem ae_maxNegativeJump_stepPathLaw_le (μ : PMF ℕ) {T : ℝ} (hT : 0 < T)
    (B : ℕ → ℝ) (n : ℕ) (hB : 0 < B n) :
    ∀ᵐ f : D T ℝ ∂(stepPathLaw (realOffspringStepLaw μ) T B n : Measure (D T ℝ)),
      maxNegativeJump f ≤ 1 / B n := by
  rw [coe_stepPathLaw, ae_map_iff (measurable_realStepPath T n (B n)).aemeasurable
    (measurableSet_le continuous_maxNegativeJump.measurable measurable_const)]
  filter_upwards [ae_offspring_sequence_ge μ] with ω hω
  apply (maxNegativeJump_le_iff hT.le (by positivity) _).mpr
  exact leftLim_sub_realStepPath_le n hB ω hω

/-- Almost surely, simultaneously at all times `t ∈ [0,T]`, the path has no negative jump:
`f (t-) ≤ f t`. Proved through the offspring witness (steps `≥ -1`) and uniqueness, not through
the absence of fixed discontinuities. -/
theorem ae_leftLim_le_stableProcessLaw {θ T : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (hT : 0 < T) :
    ∀ᵐ f : D T ℝ ∂(stableProcessLaw θ T : Measure (D T ℝ)),
      ∀ t : Set.Icc (0 : ℝ) T, Function.leftLim f t ≤ f t := by
  obtain ⟨μ, B, hμ⟩ := exists_stableDomain hθ
  have h := hμ.isRealStableAttracted
  have hrecip : Tendsto (fun n => 1 / B n) atTop (𝓝 0) := by
    simpa only [one_div, Function.comp_def] using
      tendsto_inv_atTop_zero.comp h.tendsto_norming_atTop
  have hbound {ε : ℝ} (hε : 0 < ε) :
      ∀ᵐ f : D T ℝ ∂(stableProcessLaw θ T : Measure (D T ℝ)),
        maxNegativeJump f ≤ ε := by
    let F : Set (D T ℝ) := {f | maxNegativeJump f ≤ ε}
    have hF : IsClosed F := isClosed_le continuous_maxNegativeJump continuous_const
    have hevent : ∀ᶠ n in atTop,
        (stepPathLaw (realOffspringStepLaw μ) T B n : Measure (D T ℝ)) F = 1 := by
      filter_upwards [h.pos, hrecip.eventually_lt_const hε] with n hn he
      have hae : ∀ᵐ f : D T ℝ
          ∂(stepPathLaw (realOffspringStepLaw μ) T B n : Measure (D T ℝ)), f ∈ F := by
        filter_upwards [ae_maxNegativeJump_stepPathLaw_le μ hT B n hn] with f hf
        exact hf.trans he.le
      simpa using (ae_mem_iff_measure_eq hF.measurableSet.nullMeasurableSet).mp hae
    have hport := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto
      (h.tendsto_stepPathLaw hT) hF
    rw [Filter.limsup_congr hevent, Filter.limsup_const] at hport
    apply (ae_mem_iff_measure_eq hF.measurableSet.nullMeasurableSet).mpr
    apply le_antisymm (measure_mono (subset_univ F))
    simpa using hport
  have hall : ∀ᵐ f : D T ℝ ∂(stableProcessLaw θ T : Measure (D T ℝ)),
      ∀ n : ℕ, maxNegativeJump f ≤ 1 / (n + 1 : ℝ) :=
    ae_all_iff.mpr fun n => hbound (by positivity)
  filter_upwards [hall] with f hf
  have hzero : maxNegativeJump f ≤ 0 := by
    by_contra hh
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (lt_of_not_ge hh)
    exact (not_lt_of_ge (hf n)) hn
  intro t
  exact sub_nonpos.mp ((maxNegativeJump_le_iff hT.le le_rfl f).mp hzero t)

end BGW.StableTrees
