module

public import BGWLeaves.Coding.Defs
public import BGWLeaves.StableAnalysis
public import BGW.StableTrees.RealAttraction
public import BGW.StableTrees.NonmonotoneNorming

/-!
# BGW's admissible normings and the corrected norming

Proofs of the bridge between BGW's admissible normings (`IsRealStableAttracted`) and the corrected
norming `norming (stepLaw μ) θ`: `isRealStableAttracted_norming` and
`stableDomain_of_isRealStableAttracted` of `BGWLeaves.Coding`, exported in namespace
`BGWLeaves.Coding.Norming` with exactly the types stated there.

Route.  The project's `BGWLeaves.StableAnalysis.{intWalk, IsStableAttracted}` and BGW's
`BGW.StableTrees.Attraction.{intWalk, IsStableAttracted}` are two copies of the same definitions:
the walks agree by induction (`intWalk_eq`), hence the two attraction predicates are equivalent
(`isStableAttracted_toBGW`, `isStableAttracted_ofBGW`).
* `isRealStableAttracted_norming`: `locallimit_i` (with `mean_stepLaw`) gives the
  attraction with the corrected norming; BGW's public `Attraction.IsStableAttracted.isRealStableAttracted`
  concludes (`realOffspringStepLaw μ = castLaw (stepLaw μ)` by definition).
* `stableDomain_of_isRealStableAttracted`: the real attraction gives BGW's integer attraction with
  centering `0` (`isStableAttracted_of_isRealStableAttracted`, re-derived from the public
  `sumLaw_castLaw` and `integral_exp_neg_mul_stableLaw`, since BGW's version is private); then
  `locallimit_i`, `locallimit_ii` (monotonicity) and `IsStableAttracted.exists_stableDomain`
  give the domain of attraction, and `norming_isEquivalent` (inverted) the ratio.
-/

@[expose] public section

namespace BGWLeaves.Coding.Norming

open MeasureTheory ProbabilityTheory Filter BGW
open BGW.StableTrees BGW.LocallyFinite BGWLeaves.StableAnalysis BGW.Probability.RealWalk
open scoped ENNReal NNReal Topology

/-- The two copies of the `n`-fold convolution power coincide. -/
theorem intWalk_eq (ν : Measure ℤ) :
    BGWLeaves.StableAnalysis.intWalk ν = BGW.StableTrees.Attraction.intWalk ν := by
  funext n
  induction n with
  | zero => rfl
  | succ m ih =>
      simp only [BGWLeaves.StableAnalysis.intWalk, BGW.StableTrees.Attraction.intWalk, ih]

/-- The project's attraction predicate implies BGW's (same fields). -/
theorem isStableAttracted_toBGW {ν : Measure ℤ} {θ m : ℝ} {a : ℕ → ℝ}
    (h : BGWLeaves.StableAnalysis.IsStableAttracted ν θ m a) :
    BGW.StableTrees.Attraction.IsStableAttracted ν θ m a := by
  obtain ⟨h1, h2, X, hX, hL, hw⟩ := h
  rw [intWalk_eq] at hw
  exact ⟨h1, h2, X, hX, hL, hw⟩

/-- BGW's attraction predicate implies the project's (same fields). -/
theorem isStableAttracted_ofBGW {ν : Measure ℤ} {θ m : ℝ} {a : ℕ → ℝ}
    (h : BGW.StableTrees.Attraction.IsStableAttracted ν θ m a) :
    BGWLeaves.StableAnalysis.IsStableAttracted ν θ m a := by
  obtain ⟨h1, h2, X, hX, hL, hw⟩ := h
  rw [← intWalk_eq] at hw
  exact ⟨h1, h2, X, hX, hL, hw⟩

/-- A real attracted norming of `realOffspringStepLaw μ` gives BGW's integer attraction predicate with
centering `0` (re-derivation of BGW's private `isStableAttracted_of_isRealStableAttracted`). -/
theorem isStableAttracted_of_isRealStableAttracted {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ}
    (hB : IsRealStableAttracted (realOffspringStepLaw μ) θ B) :
    BGW.StableTrees.Attraction.IsStableAttracted (stepLaw μ) θ 0 B := by
  refine ⟨hB.index_mem, ?_, (stableLaw θ : Measure ℝ), inferInstance, ?_, ?_⟩
  · obtain ⟨N, hN⟩ := eventually_atTop.mp hB.pos
    exact ⟨N, hN⟩
  · intro lam hlam
    exact integral_exp_neg_mul_stableLaw hB.index_mem hlam.le
  · intro f
    have h := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hB.converges) f
    refine h.congr' ?_
    filter_upwards [] with n
    have hmap : (scaledSumLaw (realOffspringStepLaw μ) B n : Measure ℝ) =
        (BGW.StableTrees.Attraction.intWalk (stepLaw μ) n).map (fun z : ℤ => (z : ℝ) / B n) := by
      change Measure.map (fun x : ℝ => x / B n)
        (sumLaw (castLaw (stepLaw μ)) n : Measure ℝ) = _
      rw [sumLaw_castLaw, Measure.map_map (by fun_prop) (by fun_prop)]
      rfl
    rw [hmap]
    simp

set_option linter.unusedVariables false in
theorem isRealStableAttracted_norming {μ : PMF ℕ} {θ : ℝ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hDA : ∃ a, StableDomain μ θ a) :
    IsRealStableAttracted (realOffspringStepLaw μ) θ (norming (stepLaw μ) θ) := by
  obtain ⟨a, ha⟩ := hDA
  have hmean := BGWLeaves.StableAnalysis.mean_stepLaw hc
  have h0 : BGWLeaves.StableAnalysis.IsStableAttracted (stepLaw μ) θ
      (BGWLeaves.StableAnalysis.mean (stepLaw μ)) a := by
    rw [hmean]
    exact BGWLeaves.StableAnalysis.stableDomain_isStableAttracted ha
  have hcan := BGWLeaves.StableAnalysis.locallimit_i (stepLaw μ)
    (BGWLeaves.StableAnalysis.stepLaw_lt_neg_one μ)
    (BGWLeaves.StableAnalysis.integrable_stepLaw hc) ⟨a, h0⟩
  rw [hmean] at hcan
  exact BGW.StableTrees.Attraction.IsStableAttracted.isRealStableAttracted
    (isStableAttracted_toBGW hcan)

theorem stableDomain_of_isRealStableAttracted {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ}
    (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hB : IsRealStableAttracted (realOffspringStepLaw μ) θ B) :
    (∃ a, StableDomain μ θ a) ∧ Tendsto (fun n => B n / norming (stepLaw μ) θ n) atTop (𝓝 1) := by
  have hmean := BGWLeaves.StableAnalysis.mean_stepLaw hc
  have hB' : BGWLeaves.StableAnalysis.IsStableAttracted (stepLaw μ) θ
      (BGWLeaves.StableAnalysis.mean (stepLaw μ)) B := by
    rw [hmean]
    exact isStableAttracted_ofBGW (isStableAttracted_of_isRealStableAttracted hB)
  have hstep := BGWLeaves.StableAnalysis.stepLaw_lt_neg_one μ
  have hint := BGWLeaves.StableAnalysis.integrable_stepLaw hc
  have hcan := BGWLeaves.StableAnalysis.locallimit_i (stepLaw μ) hstep hint ⟨B, hB'⟩
  have hmono := (BGWLeaves.StableAnalysis.locallimit_ii (stepLaw μ) hstep hint ⟨B, hB'⟩).1
  rw [hmean] at hcan
  obtain ⟨a', -, hdom⟩ := hcan.exists_stableDomain hc hne hmono
  refine ⟨⟨a', hdom⟩, ?_⟩
  have hr := (BGWLeaves.StableAnalysis.norming_isEquivalent (stepLaw μ) hstep hint hB').inv₀
    one_ne_zero
  simpa only [inv_div, inv_one] using hr

end BGWLeaves.Coding.Norming
