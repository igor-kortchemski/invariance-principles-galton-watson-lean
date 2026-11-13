module

public import BGWLeaves.GeneralAInf.BlockLocal
public import BGWLeaves.LocalEstimates.Defs
public import BGWLeaves.GeneralAFunctional.WalkStopped

/-! Signed lattice local estimates for arbitrary A-block increments.
This module supplies the analytic part of F; the stopped-walk adapter is separate.
-/

@[expose] public section
namespace BGWLeaves.GeneralAFunctional.WalkLocal
open MeasureTheory ProbabilityTheory Filter BGW BGW.StableTrees BGW.LocallyFinite
open BGWLeaves.StableAnalysis
open BGWLeaves.GeneralA MarkedWalk Regroup MarkedTime MarkedSpan
open scoped ENNReal Topology

/-- Direct lattice LLT for the block walk, retaining its one-step endpoint shift. -/
theorem block_local_shifted {μ : PMF ℕ} {θ : ℝ} {A : Set ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hDA : ∃ a, StableDomain μ θ a) (hA : μ.toMeasure A ≠ 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ j : ℤ,
      |normB μ θ ((n : ℝ) / (μ.toMeasure A).toReal) * intWalkProb (blockStep μ A) n (-1 - j) -
        (if (arithFactor μ A : ℤ) ∣ (n : ℤ) - 1 - j then
          (arithFactor μ A : ℝ) * Scalar.stableDensity θ
            ((-1 - (j : ℝ)) / normB μ θ ((n : ℝ) / (μ.toMeasure A).toReal)) else 0)| ≤ ε := by
  obtain ⟨hprob, hi, hm⟩ := GeneralAInf.BlockStable.blockStep_firstMoment hc hA
  let := hprob
  change mean (blockStep μ A) = 0 at hm
  have hattr := GeneralAInf.BlockStable.blockStep_isStableAttracted hc hne hDA hA
  have hattr' : IsStableAttracted (blockStep μ A) θ (mean (blockStep μ A))
      (fun n : ℕ => normB μ θ ((n : ℝ) / (μ.toMeasure A).toReal)) := by
    simpa only [hm, normB] using hattr
  obtain ⟨hs, hr⟩ := blockLaw_span hc hne hA
  have hmono : Monotone (fun n : ℕ => normB μ θ ((n : ℝ) / (μ.toMeasure A).toReal)) := by
    simpa only [normB] using
      GeneralAInf.BlockStable.monotone_norming_floor hc hne hDA hA
  obtain ⟨N, hN⟩ := LeafMass.YLaw.llt_lattice_abstract (blockStep μ A) hi hs (-1) hr hmono hattr' hε
  refine ⟨max N 1, fun n hn j => ?_⟩
  have he : -1 - j - (n : ℤ) * (-1) = (n : ℤ) - 1 - j := by ring
  simpa only [he, hm, mul_zero, sub_zero, Int.cast_sub, Int.cast_neg, Int.cast_one] using
    hN n (le_trans (le_max_left _ _) hn) (-1 - j)

/-- The canonical block norming diverges. -/
theorem block_norming_atTop {μ : PMF ℕ} {θ : ℝ} {A : Set ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hDA : ∃ a, StableDomain μ θ a) (hA : μ.toMeasure A ≠ 0) :
    Tendsto (fun n : ℕ => normB μ θ ((n : ℝ) / (μ.toMeasure A).toReal)) atTop atTop := by
  obtain ⟨hp, _, _⟩ := GeneralAInf.BlockStable.blockStep_firstMoment hc hA
  let := hp
  have ht := TransformConvergence.tendsto_atTop (blockStep μ A)
    (GeneralAInf.BlockStable.blockStep_isStableAttracted hc hne hDA hA)
  simpa only [normB] using ht

/-- Lattice replacement for 6.11, uniformly over all signed endpoints. -/
theorem block_local_signed {μ : PMF ℕ} {θ : ℝ} {A : Set ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hDA : ∃ a, StableDomain μ θ a) (hA : μ.toMeasure A ≠ 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ j : ℤ,
      |normB μ θ ((n : ℝ) / (μ.toMeasure A).toReal) * intWalkProb (blockStep μ A) n (-1 - j) -
        (if (arithFactor μ A : ℤ) ∣ (n : ℤ) - 1 - j then
          (arithFactor μ A : ℝ) * Scalar.stableDensity θ
            (-((j : ℝ) / normB μ θ ((n : ℝ) / (μ.toMeasure A).toReal))) else 0)| ≤ ε := by
  obtain ⟨b, hb⟩ := hDA
  let g : ℝ := arithFactor μ A
  have hg : 0 < g := by dsimp [g]; exact_mod_cast GeneralA.Arithmetic.arithFactor_pos hc hne A
  obtain ⟨δ, hδ, hd⟩ := (Metric.uniformContinuous_iff.1
    (Scalar.uniformContinuous_stableDensity hb.alpha_mem)) (ε / (2 * g)) (by positivity)
  obtain ⟨N, hN⟩ := block_local_shifted hc hne ⟨b, hb⟩ hA (half_pos hε)
  have htop := block_norming_atTop hc hne ⟨b, hb⟩ hA
  have hi : Tendsto (fun n : ℕ => 1 / normB μ θ ((n : ℝ) / (μ.toMeasure A).toReal))
      atTop (𝓝 (0 : ℝ)) := tendsto_const_nhds.div_atTop htop
  obtain ⟨M, hM⟩ := eventually_atTop.1 ((hi.eventually (eventually_lt_nhds hδ)).and
    (htop.eventually (eventually_gt_atTop 0)))
  refine ⟨max N M, fun n hn j => ?_⟩
  obtain ⟨hsmall, hpos⟩ := hM n (le_trans (le_max_right _ _) hn)
  have h := hN n (le_trans (le_max_left _ _) hn) j
  by_cases hr : (arithFactor μ A : ℤ) ∣ (n : ℤ) - 1 - j
  · rw [ite_eq_left hr] at h ⊢
    have harg : dist ((-1 - (j : ℝ)) / normB μ θ ((n : ℝ) / (μ.toMeasure A).toReal))
        (-((j : ℝ) / normB μ θ ((n : ℝ) / (μ.toMeasure A).toReal))) < δ := by
      rw [Real.dist_eq, show (-1 - (j : ℝ)) / normB μ θ ((n : ℝ) / (μ.toMeasure A).toReal) -
        (-((j : ℝ) / normB μ θ ((n : ℝ) / (μ.toMeasure A).toReal))) =
          -(1 / normB μ θ ((n : ℝ) / (μ.toMeasure A).toReal)) by ring, abs_neg,
        abs_of_pos (one_div_pos.mpr hpos)]
      exact hsmall
    have hp := hd harg
    rw [Real.dist_eq] at hp
    have hmul := mul_lt_mul_of_pos_left hp hg
    have he : g * (ε / (2 * g)) = ε / 2 := by field_simp
    rw [he] at hmul
    have hh := abs_sub_le (normB μ θ ((n : ℝ) / (μ.toMeasure A).toReal) * intWalkProb (blockStep μ A) n (-1 - j))
      (g * Scalar.stableDensity θ ((-1 - (j : ℝ)) / normB μ θ ((n : ℝ) / (μ.toMeasure A).toReal)))
      (g * Scalar.stableDensity θ (-((j : ℝ) / normB μ θ ((n : ℝ) / (μ.toMeasure A).toReal))))
    rw [← mul_sub, abs_mul, abs_of_pos hg] at hh
    linarith
  · simpa only [ite_eq_right hr] using h.trans (half_le_self hε.le)

/-- Signed stopped-walk kernel for arbitrary offspring marks. -/
noncomputable def chiA (μ : PMF ℕ) (A : Set ℕ) (n : ℕ) (j : ℤ) : ℝ≥0∞ :=
  iidWalk μ (WalkStopped.aStopEvent A n (-1 - j))

/-- F: the stopped-path adapter has no stability or nondegeneracy assumptions. -/
theorem chiA_eq_blockWalk (μ : PMF ℕ) (A : Set ℕ) {n : ℕ} (hn : 1 ≤ n) (j : ℤ) :
    chiA μ A n j = intWalk (blockStep μ A) n {-1 - j} := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  exact WalkStopped.aStopEvent_mass μ A m (-1 - j)

/-- F: the signed LLT for the original stopped walk, uniformly in every integer
endpoint, with the corrected arithmetic indicator and span factor. -/
theorem chiA_local_signed {μ : PMF ℕ} {θ : ℝ} {A : Set ℕ} (hc : IsCritical μ)
    (hne : μ 1 ≠ 1) (hDA : ∃ a, StableDomain μ θ a) (hA : μ.toMeasure A ≠ 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ j : ℤ,
      |normB μ θ ((n : ℝ) / (μ.toMeasure A).toReal) * (chiA μ A n j).toReal -
        (if (arithFactor μ A : ℤ) ∣ (n : ℤ) - 1 - j then
          (arithFactor μ A : ℝ) * Scalar.stableDensity θ
            (-((j : ℝ) / normB μ θ ((n : ℝ) / (μ.toMeasure A).toReal))) else 0)| ≤ ε := by
  obtain ⟨N, hN⟩ := block_local_signed hc hne hDA hA hε
  refine ⟨max N 1, fun n hn j => ?_⟩
  rw [chiA_eq_blockWalk μ A (le_trans (le_max_right _ _) hn)]
  exact hN n (le_trans (le_max_left _ _) hn) j

end BGWLeaves.GeneralAFunctional.WalkLocal
