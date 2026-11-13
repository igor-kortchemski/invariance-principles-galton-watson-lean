/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.Attraction.Defs
public import BGW.StableTrees.Attraction.Norming
public import BGW.StableTrees.Attraction.TailTransfer
public import BGW.StableTrees.Attraction.GaussianBranch
public import BGW.StableTrees.Attraction.CanonicalAttraction
public import BGW.StableTrees.Attraction.DomainCriterion
public import BGW.StableTrees.Attraction.QuantileAnalysis

/-!
# Bridge, tail branch

`μ[j,∞) = j^{-θ} L(j)` with `L` slowly varying gives a normalized stable domain of attraction.
The step law `ν = stepLaw μ` has a regularly varying strict tail (`TailTransfer`); for `θ < 2` the
canonical attraction D2(i) applies, for `θ = 2` either the finite variance CLT of BGW or the
Gaussian criterion D2(ii) (slow variation of the truncated second moment, B3-a).  The canonical
norming is monotone, so `IsStableAttracted.exists_stableDomain` repairs its first terms.
Ported from `BGWLeaves/StableAnalysis/StableDomainTail.lean` of the author's arXiv:1110.2163v4
formalization (local snapshot of 6 November 2026).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal

namespace BGW.StableTrees.Attraction

open BGW.StableTrees
open BGW.StableTrees.Attraction

/-- A finite second moment of the step law `K - 1` gives a finite second moment of `K`. -/
theorem memLp_offspring_of_integrable_sq {μ : PMF ℕ}
    (h : Integrable (fun z : ℤ => (z : ℝ) ^ 2) (stepLaw μ)) :
    MemLp (fun j : ℕ => (j : ℝ)) 2 μ.toMeasure := by
  have h1 : MemLp (fun z : ℤ => (z : ℝ)) 2 (stepLaw μ) :=
    (memLp_two_iff_integrable_sq (measurable_of_countable _).aestronglyMeasurable).2 h
  rw [stepLaw, memLp_map_measure_iff (measurable_of_countable _).aestronglyMeasurable
    (measurable_of_countable _).aemeasurable] at h1
  have h2 := h1.add (memLp_const (1 : ℝ))
  convert h2 using 1
  funext j
  simp

/-- **Bridge, tail branch**: `μ[j,∞) = j^{-θ}L(j)` gives a normalized domain of attraction. -/
theorem exists_stableDomain_of_tail {μ : PMF ℕ} {θ : ℝ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hθ : 1 < θ ∧ θ ≤ 2) {L : ℝ → ℝ} (hmeas : Measurable L) (hnn : ∀ x, 0 < x → 0 ≤ L x)
    (hL : SlowlyVarying L)
    (htail : ∀ j : ℕ, 1 ≤ j → (μ.toMeasure (Set.Ici j)).toReal = (j : ℝ) ^ (-θ) * L j) :
    ∃ a : ℕ → ℝ, StableDomain μ θ a := by
  have := isProbabilityMeasure_stepLaw μ
  have hstep := stepLaw_lt_neg_one μ
  have hint := integrable_stepLaw hc
  have hmean := mean_stepLaw hc
  have hT := TailTransfer.isRegVaryAtTop_stepLaw_tail hmeas hnn hL htail
  rcases lt_or_eq_of_le hθ.2 with hlt | heq
  · have hatt := CanonicalAttraction.isStableAttracted_of_regVary_tail hstep hint hθ.1 hlt hT
    have hinf := DomainCriterion.not_integrable_sq_of_index_lt_two hatt hint hlt
    have hmono := QuantileAnalysis.norming_monotone_of_infinite_variance hstep hint hinf θ hθ
    rw [hmean] at hatt
    obtain ⟨a', -, ha'⟩ := hatt.exists_stableDomain hc hne hmono
    exact ⟨a', ha'⟩
  · subst heq
    by_cases hsq : Integrable (fun z : ℤ => (z : ℝ) ^ 2) (stepLaw μ)
    · exact ⟨_, Scalar.stableDomain_of_finiteVariance hc hne
        (memLp_offspring_of_integrable_sq hsq)⟩
    · obtain ⟨hK, hKinf⟩ := GaussianBranch.truncSecondMoment_slowlyVarying_of_regVary
        (stepLaw μ) hstep hsq hT
      have hatt := CanonicalAttraction.isStableAttracted_of_slowlyVarying_moment hstep hint hK hKinf
      have hmono := QuantileAnalysis.norming_monotone_of_infinite_variance hstep hint hsq 2 hθ
      rw [hmean] at hatt
      obtain ⟨a', -, ha'⟩ := hatt.exists_stableDomain hc hne hmono
      exact ⟨a', ha'⟩

end BGW.StableTrees.Attraction
