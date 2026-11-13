/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.Scalar.LocalLimit

/-!
# Local bounds and scalar tightness

Both estimates are derived from `StableDomain` alone. All positive-time
bounds retain `1 ≤ m`; no condition is imposed on the normalizer at time zero.

Adapted from `PoissonDeclumping/Stable/ToolkitProof.lean` in
`igor-kortchemski/rare-subtree-patterns`, commit
`fc5ef722392b1af41e8b9d5fc45d5a521b7823dd` (Apache-2.0).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Complex Filter Set
open scoped Topology

namespace BGW.StableTrees.Scalar

variable {μ : PMF ℕ} {α : ℝ} {a : ℕ → ℝ}

/-- **Uniform local bound** (inventory B10, "the local bound following from `eq:LL`", source
lines 1140, 1161): `Ψ_m(x) ≤ C / a_m` for all `m ≥ 1` and all `x ∈ ℤ`. -/
theorem exists_walkProb_le (h : StableDomain μ α a) :
    ∃ C : ℝ, ∀ m : ℕ, 1 ≤ m → ∀ x : ℤ, walkProb μ m x ≤ C / a m := by
  obtain ⟨M, hM0, hM⟩ := exists_stableDensity_le (α := α)
  obtain ⟨N, hN⟩ := localLimit h one_pos
  set d : ℝ := (latticeSpan μ : ℝ)
  set C : ℝ := max (d * M + 1) (a (max N 1)) with hC
  refine ⟨C, fun m hm x => ?_⟩
  have ham := h.pos m hm
  rw [le_div_iff₀ ham]
  by_cases hdx : (latticeSpan μ : ℤ) ∣ x + m
  · rcases le_or_gt N m with hNm | hNm
    · have h1 := hN m hNm x hdx
      have h2 : d * stableDensity α (x / a m) ≤ d * M :=
        mul_le_mul_of_nonneg_left ((le_abs_self _).trans (hM _)) (by positivity)
      have h3 : a m * walkProb μ m x ≤ d * M + 1 := by
        have := (abs_le.1 h1).2; linarith
      calc walkProb μ m x * a m = a m * walkProb μ m x := mul_comm _ _
        _ ≤ d * M + 1 := h3
        _ ≤ C := le_max_left _ _
    · have hP : walkProb μ m x ≤ 1 := by
        rw [walkProb_coe_nat]; exact measureReal_le_one
      have hP0 : 0 ≤ walkProb μ m x := by rw [walkProb_coe_nat]; exact measureReal_nonneg
      have : a m ≤ a (max N 1) := h.monotone (le_trans hNm.le (le_max_left _ _))
      calc walkProb μ m x * a m ≤ 1 * a m := by gcongr
        _ ≤ a (max N 1) := by linarith
        _ ≤ C := le_max_right _ _
  · rw [walkProb_eq_zero_of_not_dvd h hdx, zero_mul]
    exact le_trans (by positivity) (le_max_left _ _)

/-- The bounded continuous cutoff `y ↦ min 1 (max 0 (|y| - R))`. -/
noncomputable def cutoffFn (R : ℝ) : BoundedContinuousFunction ℝ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun y => min 1 (max 0 (|y| - R)))
    (by fun_prop) 1 (fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (le_min zero_le_one (le_max_left _ _))]
      exact min_le_left _ _)

lemma cutoffFn_apply (R y : ℝ) : cutoffFn R y = min 1 (max 0 (|y| - R)) := rfl

/-- **Tightness of `S_m / a_m`** (inventory B07 in marginal form):
`sup_{m ≥ 1} P(|S_m| > K a_m) → 0` as `K → ∞`. -/
theorem tight (h : StableDomain μ α a) {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ, ∀ m : ℕ, 1 ≤ m → (walkLaw μ m).real {x : ℤ | K * a m < |(x : ℝ)|} ≤ ε := by
  obtain ⟨ν, hν, -, hconv⟩ := h.converges
  -- the limit law: `∫ cutoff_R dν → 0`
  have hνt : Tendsto (fun R : ℝ => ∫ y, cutoffFn R y ∂ν) atTop (𝓝 0) := by
    have h0 : (0 : ℝ) = ∫ y, (fun _ => (0 : ℝ)) y ∂ν := by simp
    rw [h0]
    apply tendsto_integral_filter_of_dominated_convergence (fun _ => (1 : ℝ))
    · exact Eventually.of_forall fun R => (cutoffFn R).continuous.aestronglyMeasurable
    · refine Eventually.of_forall fun R => Eventually.of_forall fun y => ?_
      rw [cutoffFn_apply, Real.norm_eq_abs, abs_of_nonneg (le_min zero_le_one (le_max_left _ _))]
      exact min_le_left _ _
    · exact integrable_const 1
    · refine Eventually.of_forall fun y => ?_
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_ge_atTop |y|] with R hR
      rw [cutoffFn_apply, max_eq_left (by linarith), min_eq_right zero_le_one]
  obtain ⟨R, hR⟩ := (hνt.eventually (gt_mem_nhds (half_pos hε))).exists_forall_of_atTop
  have hR' := hR (max R 0) (le_max_left _ _)
  set R' : ℝ := max R 0
  -- large `m`
  obtain ⟨N, hN⟩ := ((hconv (cutoffFn R')).eventually
    (gt_mem_nhds (show ∫ y, cutoffFn R' y ∂ν < ε by linarith))).exists_forall_of_atTop
  -- small `m`: each law is tight
  have hsmall : ∀ m ∈ Finset.range N, ∀ᶠ j : ℕ in atTop, 1 ≤ m →
      (walkLaw μ m).real {x : ℤ | (j : ℝ) * a m < |(x : ℝ)|} ≤ ε := by
    intro m _
    by_cases hm : 1 ≤ m
    · have ham := h.pos m hm
      have ht : Tendsto (fun j : ℕ => (walkLaw μ m).real {x : ℤ | (j : ℝ) * a m < |(x : ℝ)|})
          atTop (𝓝 0) := by
        have heq : ∀ j : ℕ, (walkLaw μ m).real {x : ℤ | (j : ℝ) * a m < |(x : ℝ)|} =
            ∫ x, {x : ℤ | (j : ℝ) * a m < |(x : ℝ)|}.indicator 1 x ∂(walkLaw μ m) :=
          fun j => (integral_indicator_one ((Set.to_countable _).measurableSet)).symm
        simp_rw [heq]
        have h0 : (0 : ℝ) = ∫ x, (fun _ => (0 : ℝ)) x ∂(walkLaw μ m) := by simp
        rw [h0]
        apply tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ))
        · exact fun j => (measurable_of_countable _).aestronglyMeasurable
        · exact integrable_const 1
        · intro j; refine Eventually.of_forall fun x => ?_
          by_cases hx : x ∈ {x : ℤ | (j : ℝ) * a m < |(x : ℝ)|}
          · simp [indicator_of_mem hx]
          · simp [indicator_of_notMem hx]
        · refine Eventually.of_forall fun x => ?_
          apply tendsto_const_nhds.congr'
          obtain ⟨J, hJ⟩ := exists_nat_ge (|(x : ℝ)| / a m)
          filter_upwards [eventually_ge_atTop J] with j hj
          have : |(x : ℝ)| ≤ j * a m := by
            rw [div_le_iff₀ ham] at hJ
            exact hJ.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hj) ham.le)
          have hx : x ∉ {x : ℤ | (j : ℝ) * a m < |(x : ℝ)|} := by
            simp only [mem_ofPred_eq, not_lt]; exact this
          simp [indicator_of_notMem hx]
      filter_upwards [ht.eventually (ge_mem_nhds hε)] with j hj _ using hj
    · exact Eventually.of_forall fun j hm' => absurd hm' hm
  obtain ⟨J, hJ⟩ := ((Finset.eventually_all (Finset.range N)).2 hsmall).exists_forall_of_atTop
  refine ⟨max (R' + 1) J, fun m hm => ?_⟩
  have ham := h.pos m hm
  rcases le_or_gt N m with hNm | hNm
  · -- large `m`: compare with the cutoff
    have h1 : (walkLaw μ m).real {x : ℤ | max (R' + 1) J * a m < |(x : ℝ)|} ≤
        ∫ y, cutoffFn R' y ∂((walkLaw μ m).map (fun z : ℤ => (z : ℝ) / a m)) := by
      set S : Set ℤ := {x : ℤ | max (R' + 1) J * a m < |(x : ℝ)|} with hS
      have hint1 : Integrable (S.indicator (1 : ℤ → ℝ)) (walkLaw μ m) :=
        Integrable.of_bound (C := 1) (measurable_of_countable _).aestronglyMeasurable
          (Eventually.of_forall fun x => by
            by_cases hx : x ∈ S
            · simp [indicator_of_mem hx]
            · simp [indicator_of_notMem hx])
      have hint2 : Integrable (fun x : ℤ => cutoffFn R' ((x : ℝ) / a m)) (walkLaw μ m) :=
        Integrable.of_bound (C := 1) (measurable_of_countable _).aestronglyMeasurable
          (Eventually.of_forall fun x => by
            rw [cutoffFn_apply, Real.norm_eq_abs,
              abs_of_nonneg (le_min zero_le_one (le_max_left _ _))]
            exact min_le_left _ _)
      rw [integral_map (measurable_of_countable _).aemeasurable
        (cutoffFn R').continuous.aestronglyMeasurable,
        ← integral_indicator_one (Set.to_countable S).measurableSet]
      apply integral_mono hint1 hint2
      intro x
      by_cases hx : x ∈ {x : ℤ | max (R' + 1) J * a m < |(x : ℝ)|}
      · rw [indicator_of_mem hx, Pi.one_apply]
        show 1 ≤ cutoffFn R' ((x : ℝ) / a m)
        rw [cutoffFn_apply]
        simp only [mem_ofPred_eq] at hx
        have : R' + 1 < |(x : ℝ) / a m| := by
          rw [abs_div, abs_of_pos ham, lt_div_iff₀ ham]
          exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right (le_max_left _ _) ham.le) hx
        rw [min_eq_left (by rw [le_max_iff]; right; linarith)]
      · rw [indicator_of_notMem hx]
        show 0 ≤ cutoffFn R' ((x : ℝ) / a m)
        rw [cutoffFn_apply]
        exact le_min zero_le_one (le_max_left _ _)
    exact h1.trans (hN m hNm).le
  · have h2 := hJ J le_rfl m (Finset.mem_range.2 hNm) hm
    refine le_trans (measureReal_mono ?_) h2
    intro x hx
    simp only [mem_ofPred_eq] at hx ⊢
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right (le_max_right _ _) ham.le) hx

end BGW.StableTrees.Scalar

