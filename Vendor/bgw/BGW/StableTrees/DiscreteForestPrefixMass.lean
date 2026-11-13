/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.DiscreteForestPrefixUnconditioned

/-!
# Conditional prefix atoms

Dividing the unconditioned prefix-completion identities by the conditioning
masses gives the tail and exact prefix atoms and their discrete density ratio.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Classical

namespace BGW.StableTrees.DiscreteForest

/-- Every inclusive tree-size tail has positive real mass in the critical nondegenerate case. -/
theorem forestTail_pos (μ : PMF ℕ) (hc : IsCritical μ) (hne : μ 1 ≠ 1) (n : ℕ) :
    0 < forestTail μ 1 n := by
  rw [← tailMass_eq_forestTail μ hc hne n]
  exact ENNReal.toReal_pos (bienaymeLaw_sizeGeEvent_ne_zero μ hc hne n) (measure_ne_top _ _)

/-- The tail tree law is the conditional BGW measure when its tail mass is positive. -/
theorem tailTreeLaw_toMeasure (μ : PMF ℕ) (n : ℕ)
    (h : BGW.LocallyFinite.bienaymeLaw μ.toMeasure (Attraction.sizeGeEvent n) ≠ 0) :
    (tailTreeLaw μ n).toMeasure =
      (BGW.LocallyFinite.bienaymeLaw μ.toMeasure)[|Attraction.sizeGeEvent n] := by
  have heq : tailTreeLaw μ n =
      (⟨(BGW.LocallyFinite.bienaymeLaw μ.toMeasure)[|Attraction.sizeGeEvent n],
        cond_isProbabilityMeasure h⟩ : ProbabilityMeasure BGW.LocallyFinite.Tree) :=
    dite_eq_left h
  exact congrArg ProbabilityMeasure.toMeasure heq

/-- The exact tree law is the conditional BGW measure at every admissible size. -/
theorem exactTreeLaw_toMeasure (μ : PMF ℕ) (n : ℕ) (h : Admissible μ n) :
    (exactTreeLaw μ n).toMeasure =
      (BGW.LocallyFinite.bienaymeLaw μ.toMeasure)[|BGW.LocallyFinite.sizeEvent n] := by
  have heq : exactTreeLaw μ n =
      (⟨(BGW.LocallyFinite.bienaymeLaw μ.toMeasure)[|BGW.LocallyFinite.sizeEvent n],
        BGW.LocallyFinite.isProbabilityMeasure_cond_sizeEvent μ.toMeasure h⟩ :
          ProbabilityMeasure BGW.LocallyFinite.Tree) := dite_eq_left h
  exact congrArg ProbabilityMeasure.toMeasure heq

/-- Tail law of a surviving prefix: `P(prefix = a | ζ ≥ n) = ∏μ(a_i) G_j(n-m) / G_1(n)`,
with `m = |a| < n`, `j = W_m + 1`, positive denominator. -/
theorem tailPrefixMass (μ : PMF ℕ) (hc : IsCritical μ) (hne : μ 1 ≠ 1) {n m : ℕ} {a : List ℕ}
    (ham : a.length = m) (hmn : m < n) (hs : IsSurvivingPrefix a)
    (hG : 0 < forestTail μ 1 n) :
    ((tailTreeLaw μ n).toMeasure).real (prefixCylinder m a) =
      degreeWeight μ a * forestTail μ (prefixStack a) (n - m) / forestTail μ 1 n := by
  have hreal : 0 < (BGW.LocallyFinite.bienaymeLaw μ.toMeasure
      (Attraction.sizeGeEvent n)).toReal := by rwa [tailMass_eq_forestTail μ hc hne n]
  have hq := (ENNReal.toReal_pos_iff.mp hreal).1.ne'
  rw [tailTreeLaw_toMeasure μ n hq, measureReal_def,
    cond_apply' (measurableSet_prefixCylinder m a), ENNReal.toReal_mul, ENNReal.toReal_inv,
    tailMass_eq_forestTail μ hc hne n]
  change (forestTail μ 1 n)⁻¹ *
    (BGW.LocallyFinite.bienaymeLaw μ.toMeasure).real
      (Attraction.sizeGeEvent n ∩ prefixCylinder m a) = _
  rw [sizeGeEvent_prefixCylinder_real μ hc hne ham hmn hs]
  ring

/-- Exact law of a surviving prefix: `P(prefix = a | ζ = n) = ∏μ(a_i) f_j(n-m) / f_1(n)`,
at an admissible size. -/
theorem exactPrefixMass (μ : PMF ℕ) (hc : IsCritical μ) (hne : μ 1 ≠ 1) {n m : ℕ}
    {a : List ℕ} (hn : Admissible μ n) (ham : a.length = m) (hmn : m < n)
    (hs : IsSurvivingPrefix a) :
    ((exactTreeLaw μ n).toMeasure).real (prefixCylinder m a) =
      degreeWeight μ a * forestMass μ (prefixStack a) (n - m) / forestMass μ 1 n := by
  rw [exactTreeLaw_toMeasure μ n hn, measureReal_def,
    cond_apply' (measurableSet_prefixCylinder m a), ENNReal.toReal_mul, ENNReal.toReal_inv]
  change ((BGW.LocallyFinite.bienaymeLaw μ.toMeasure).real
    (BGW.LocallyFinite.sizeEvent n))⁻¹ *
    (BGW.LocallyFinite.bienaymeLaw μ.toMeasure).real
      (BGW.LocallyFinite.sizeEvent n ∩ prefixCylinder m a) = _
  rw [← forestMass_one_eq_sizeProb, sizeEvent_prefixCylinder_real μ hc hne ham hmn hs]
  ring

/-- Prefix-atom form of the RN identity: exact mass = `R_n(m,j)` times tail mass, on every
surviving prefix with positive denominators. -/
theorem exactPrefixMass_eq_prefixRN_mul (μ : PMF ℕ) (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    {n m : ℕ} {a : List ℕ} (hn : Admissible μ n) (ham : a.length = m) (hmn : m < n)
    (hs : IsSurvivingPrefix a) (hG : 0 < forestTail μ (prefixStack a) (n - m)) :
    ((exactTreeLaw μ n).toMeasure).real (prefixCylinder m a) =
      exactPrefixWeight μ n m (prefixStack a) *
        ((tailTreeLaw μ n).toMeasure).real (prefixCylinder m a) := by
  have hG1 := forestTail_pos μ hc hne n
  have hf1 : forestMass μ 1 n ≠ 0 := ne_of_gt
    ((admissible_iff_forestWeight_pos μ n).mp hn)
  rw [exactPrefixMass μ hc hne hn ham hmn hs,
    tailPrefixMass μ hc hne ham hmn hs hG1, exactPrefixWeight]
  field_simp [hf1, ne_of_gt hG, ne_of_gt hG1]

end BGW.StableTrees.DiscreteForest
