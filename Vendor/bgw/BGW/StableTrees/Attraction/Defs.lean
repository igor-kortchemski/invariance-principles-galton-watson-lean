/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.Scalar.LocalLimit
public import BGW.StableTrees.Scalar.ForestBounds
public import BGW.StableTrees.Scalar.FiniteVariance
public import BGW.StableTrees.Scalar.DensityLaw
public import BGW.StableTrees.Scalar.Normalization
public import BGW.StableTrees.RegularVariation.Potter
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Probability.ConditionalProbability
public import Mathlib.MeasureTheory.Function.Floor
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.MeasureTheory.Group.Integral

/-!
# Scalar stable analysis (M3): definitions and proved bridges

Source: arXiv:1110.2163v4, `largetrees_final.tex`, Section 1 (Proposition 1.7, Definitions 1.8,
Theorem 1.10, Lemma 1.11, Remarks 1.9 and 1.12) and Sections 3 and 6 (Lemma 3.4, Theorem 3.5,
the Gaussian convolution of Section 6).

This file contains every definition of milestone M3 and every proved lemma that does not depend on
the statements still to be proved (those are in `BGW.StableTrees.Attraction`, and the proved results
that use them are in `BGW.StableTrees.Attraction.Consequences`).  It contains no proof holes.

The paper's norming constant `Γ(1-θ)^{1/θ}` and the norming `√(n K(z_n))` are not correct as
printed; `norming` is the corrected one (`printedConstant_neg`, `printedNorming_gauss`).
Ported from `BGWLeaves/StableAnalysis/Defs.lean` of the author's arXiv:1110.2163v4
formalization (local snapshot of 6 November 2026).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal

namespace BGW.StableTrees.Attraction

open BGW.StableTrees
open BGW.LocallyFinite (bienaymeLaw sizeEvent FiniteVertices Present)

/-! ## 0. Walks with an arbitrary integer step law -/

/-- `n`-fold convolution power of a step law on `ℤ`; the empty sum is `δ₀`.
For `ν = stepLaw μ` this is `walkLaw μ` (`intWalk_stepLaw`). -/
noncomputable def intWalk (ν : Measure ℤ) : ℕ → Measure ℤ
  | 0 => Measure.dirac 0
  | m + 1 => (intWalk ν m).conv ν

theorem intWalk_stepLaw (μ : PMF ℕ) : intWalk (stepLaw μ) = walkLaw μ := by
  funext n
  induction n with
  | zero => rfl
  | succ m ih => simp only [intWalk, walkLaw, ih]

/-- `P[W_n = k]` for the walk with step law `ν`. -/
noncomputable def intWalkProb (ν : Measure ℤ) (n : ℕ) (k : ℤ) : ℝ := (intWalk ν n).real {k}

theorem intWalkProb_stepLaw (μ : PMF ℕ) (n : ℕ) (k : ℤ) :
    intWalkProb (stepLaw μ) n k = walkProb μ n k := by
  simp [intWalkProb, intWalk_stepLaw, walkProb]

/-- Mean and variance of a law on `ℤ`. -/
noncomputable def mean (ν : Measure ℤ) : ℝ := ∫ z, (z : ℝ) ∂ν

/-- The second central moment of a law on `ℤ`. -/
noncomputable def variance (ν : Measure ℤ) : ℝ := ∫ z, ((z : ℝ) - mean ν) ^ 2 ∂ν

/-- Definition 1.8: the law is lattice if its support lies in `b + dℤ` for some `d ≥ 2`.
On the countable space `ℤ`, "support contained in" is "almost surely in". -/
def IsLatticeLaw (ν : Measure ℤ) : Prop :=
  ∃ (b : ℤ) (d : ℕ), 2 ≤ d ∧ ∀ᵐ z ∂ν, (d : ℤ) ∣ z - b

/-- `d` is the span: the largest `d` with support in some `b + dℤ`, in the divisibility sense
(every admissible `d'` divides `d`); `0 < d` excludes point masses. -/
def HasSpan (ν : Measure ℤ) (d : ℕ) : Prop :=
  0 < d ∧ (∃ b : ℤ, ∀ᵐ z ∂ν, (d : ℤ) ∣ z - b) ∧
    ∀ d' : ℕ, (∃ b : ℤ, ∀ᵐ z ∂ν, (d' : ℤ) ∣ z - b) → d' ∣ d

/-- Aperiodicity of an offspring law: the support generates `ℤ` as an additive group. -/
def Aperiodic (μ : PMF ℕ) : Prop :=
  AddSubgroup.closure (((↑) : ℕ → ℤ) '' {j : ℕ | μ j ≠ 0}) = ⊤


/-- The function `x ↦ a_{⌊x⌋} / x^ρ` used in 1.10(ii) is measurable (a measurability
side-condition of 1.7 for `h`). -/
theorem measurable_floor_ratio (a : ℕ → ℝ) (ρ : ℝ) :
    Measurable (fun x : ℝ => a ⌊x⌋₊ / x ^ ρ) :=
  (measurable_from_top.comp Nat.measurable_floor).div (measurable_id.pow_const ρ)


/-! ## 2. Lattice and non-lattice laws (1.8, 1.9 `rem:non-lattice`) -/

/-- `Aperiodic μ` is `latticeSpan μ = 1` for a critical nondegenerate law. -/
theorem aperiodic_iff_latticeSpan_eq_one {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1) :
    Aperiodic μ ↔ Scalar.latticeSpan μ = 1 := by
  constructor
  · intro h
    have hle : AddSubgroup.closure (((↑) : ℕ → ℤ) '' {j : ℕ | μ j ≠ 0}) ≤
        AddSubgroup.zmultiples (Scalar.latticeSpan μ : ℤ) := by
      rw [AddSubgroup.closure_le]
      rintro _ ⟨j, hj, rfl⟩
      exact AddSubgroup.mem_zmultiples_iff.2
        (by
          obtain ⟨k, hk⟩ := Scalar.latticeSpan_dvd_of_ne_zero hc hne hj
          exact ⟨k, by rw [smul_eq_mul]; linarith⟩)
    rw [h] at hle
    have h1 : (1 : ℤ) ∈ AddSubgroup.zmultiples (Scalar.latticeSpan μ : ℤ) := hle trivial
    obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.1 h1
    have : (Scalar.latticeSpan μ : ℤ) ∣ 1 := ⟨k, by simpa [mul_comm] using hk.symm⟩
    exact_mod_cast Int.eq_one_of_dvd_one (by positivity) this
  · intro h
    have hmem := Scalar.latticeSpan_mem_span μ
    rw [h, Nat.cast_one] at hmem
    have hsub : Ideal.span (Scalar.supportDiffs μ) ≤
        AddSubgroup.toIntSubmodule (AddSubgroup.closure (((↑) : ℕ → ℤ) '' {j : ℕ | μ j ≠ 0})) := by
      rw [Ideal.span_le]
      rintro _ ⟨i, j, hi, hj, rfl⟩
      exact sub_mem (AddSubgroup.subset_closure ⟨i, hi, rfl⟩)
        (AddSubgroup.subset_closure ⟨j, hj, rfl⟩)
    have h1 := hsub hmem
    unfold Aperiodic
    rw [eq_top_iff]
    intro z _
    have : z ∈ AddSubgroup.toIntSubmodule
        (AddSubgroup.closure (((↑) : ℕ → ℤ) '' {j : ℕ | μ j ≠ 0})) := by
      have := Submodule.smul_mem _ z h1
      simpa using this
    exact this

/-- Remark 1.9: for critical, aperiodic `μ` (with `μ 1 ≠ 1`) the law `ν` of `K - 1` is
non-lattice.  Uses `μ 0 > 0`. -/
theorem nonLattice_stepLaw {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1) (hap : Aperiodic μ) :
    ¬ IsLatticeLaw (stepLaw μ) := by
  rintro ⟨b, d, hd, hae⟩
  rw [stepLaw, ae_map_iff (measurable_of_countable _).aemeasurable
    (MeasurableSet.of_discrete)] at hae
  rw [ae_iff_of_countable] at hae
  have hdvd : ∀ j : ℕ, μ j ≠ 0 → (d : ℤ) ∣ (((j : ℤ) - 1) - b) := fun j hj =>
    hae j (by simpa [PMF.toMeasure_apply_singleton μ _ (measurableSet_singleton _)] using hj)
  have h0 := hdvd 0 (hc.apply_zero_ne_zero hne)
  have hle : AddSubgroup.closure (((↑) : ℕ → ℤ) '' {j : ℕ | μ j ≠ 0}) ≤
      AddSubgroup.zmultiples (d : ℤ) := by
    rw [AddSubgroup.closure_le]
    rintro _ ⟨j, hj, rfl⟩
    have := dvd_sub (hdvd j hj) h0
    refine AddSubgroup.mem_zmultiples_iff.2 ?_
    obtain ⟨k, hk⟩ := this
    exact ⟨k, by rw [smul_eq_mul]; push_cast at hk; linarith⟩
  rw [Aperiodic] at hap
  rw [hap] at hle
  have h1 : (1 : ℤ) ∈ AddSubgroup.zmultiples (d : ℤ) := hle trivial
  obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.1 h1
  have : (d : ℤ) ∣ 1 := ⟨k, by simpa [mul_comm] using hk.symm⟩
  have := Int.eq_one_of_dvd_one (by positivity) this
  omega

/-! ## 3. The printed norming (1.10): the constant and the positive replacement -/

/-- `Γ(1-θ) < 0` for `1 < θ < 2`: the base of the printed constant `Γ(1-θ)^{1/θ}` is
negative. -/
theorem gamma_one_sub_neg {θ : ℝ} (h1 : 1 < θ) (h2 : θ < 2) : Real.Gamma (1 - θ) < 0 := by
  have hs : (1 - θ) ≠ 0 := by linarith
  have := Real.Gamma_add_one hs
  have hpos : 0 < Real.Gamma (1 - θ + 1) := Real.Gamma_pos_of_pos (by linarith)
  have hneg : 1 - θ < 0 := by linarith
  rw [this] at hpos
  exact neg_of_mul_pos_right hpos hneg.le

/-- The printed real power `Γ(1-θ)^{1/θ}`, read with Lean's `rpow` on a negative base, is
negative (`exp(..)·cos(π/θ) < 0`), so the printed formula is not a norming as written. Reading it as
`|Γ(1-θ)|^{1/θ}` gives a positive constant, which is the correct one: the norming is
`(-Γ(1-θ))^{1/θ}` times the tail quantile (`negGamma_eq`). -/
theorem printedConstant_neg {θ : ℝ} (h1 : 1 < θ) (h2 : θ < 2) :
    Real.Gamma (1 - θ) ^ (1 / θ) < 0 := by
  have hg := gamma_one_sub_neg h1 h2
  rw [Real.rpow_def_of_neg hg]
  have hθ : 0 < θ := by linarith
  have hcos : Real.cos (1 / θ * Real.pi) < 0 := by
    apply Real.cos_neg_of_pi_div_two_lt_of_lt
    · have : 1 / 2 < 1 / θ := by rw [div_lt_div_iff₀ (by norm_num) hθ]; linarith
      nlinarith [Real.pi_pos]
    · have : 1 / θ < 1 := by rw [div_lt_one hθ]; exact h1
      nlinarith [Real.pi_pos]
  exact mul_neg_of_pos_of_neg (Real.exp_pos _) hcos

/-- The positive constant: for Laplace exponent `u ^ θ` (`E exp(-u X) = exp(u^θ)`) and
`n P[W > a_n x] → (C x)^{-θ}`, the norming constant is `C^θ = θ Γ(-θ) = -Γ(1-θ)
= Γ(2-θ)/(θ-1) > 0`. -/
theorem negGamma_eq {θ : ℝ} (h1 : 1 < θ) (h2 : θ < 2) :
    -Real.Gamma (1 - θ) = θ * Real.Gamma (-θ) ∧
      -Real.Gamma (1 - θ) = Real.Gamma (2 - θ) / (θ - 1) ∧ 0 < -Real.Gamma (1 - θ) := by
  refine ⟨?_, ?_, neg_pos.2 (gamma_one_sub_neg h1 h2)⟩
  · have := Real.Gamma_add_one (s := -θ) (by linarith)
    rw [show -θ + 1 = 1 - θ by ring] at this
    rw [this]; ring
  · have := Real.Gamma_add_one (s := 1 - θ) (by linarith)
    rw [show 1 - θ + 1 = 2 - θ by ring] at this
    rw [this]
    field_simp
    ring


/-- Right tail quantile `inf {x ≥ 0 : P[W₁ > x] ≤ 1/n}` of a step law. -/
noncomputable def tailQuantile (ν : Measure ℤ) (n : ℕ) : ℝ :=
  sInf {x : ℝ | 0 ≤ x ∧ ν.real {z : ℤ | x < (z : ℝ)} ≤ 1 / n}

/-- Truncated second moment `K(x) = E[W₁² 1_{|W₁| ≤ x}]`. -/
noncomputable def truncSecondMoment (ν : Measure ℤ) (x : ℝ) : ℝ :=
  ∫ z in {z : ℤ | |(z : ℝ)| ≤ x}, (z : ℝ) ^ 2 ∂ν

/-- `sup {z ≥ 0 : K(z)/z² ≥ 1/n}` (`sSup ∅ = 0` as in the printed convention;
at `z = 0` Lean's `K 0 / 0 = 0 < 1/n`, so `0` is not in the set for `n ≥ 1`). -/
noncomputable def gaussQuantile (ν : Measure ℤ) (n : ℕ) : ℝ :=
  sSup {z : ℝ | 0 ≤ z ∧ 1 / (n : ℝ) ≤ truncSecondMoment ν z / z ^ 2}

open Classical in
/-- The **corrected** norming `a_n` of Theorem 1.10, for Laplace exponent `u ^ θ`:
`σ √(n/2)` if the variance is finite; `(-Γ(1-θ))^{1/θ} · inf{x : P[W₁>x] ≤ 1/n}` if the variance
is infinite and `θ < 2`; `√(n K(z_n) / 2)` (note the factor `1/2`) if the variance is
infinite and `θ = 2`. -/
noncomputable def norming (ν : Measure ℤ) (θ : ℝ) (n : ℕ) : ℝ :=
  if Integrable (fun z : ℤ => (z : ℝ) ^ 2) ν then Real.sqrt (variance ν) * Real.sqrt (n / 2)
  else if θ < 2 then (-Real.Gamma (1 - θ)) ^ (1 / θ) * tailQuantile ν n
  else Real.sqrt (n * truncSecondMoment ν (gaussQuantile ν n) / 2)

open Classical in
/-- The norming **as printed** (Theorem 1.10): constant `Γ(1-θ)^{1/θ}` (negative base) and
`√(n K(z_n))` (no `1/2`). Kept only to document the discrepancies. -/
noncomputable def printedNorming (ν : Measure ℤ) (θ : ℝ) (n : ℕ) : ℝ :=
  if Integrable (fun z : ℤ => (z : ℝ) ^ 2) ν then Real.sqrt (variance ν) * Real.sqrt (n / 2)
  else if θ < 2 then Real.Gamma (1 - θ) ^ (1 / θ) * tailQuantile ν n
  else Real.sqrt (n * truncSecondMoment ν (gaussQuantile ν n))

/-- In the case `σ² = ∞`, `θ = 2` the printed norming is `√2` times the corrected one.
(With `K ≡ σ²` the printed formula would give `σ√n`, not `σ√(n/2)`.) -/
theorem printedNorming_gauss (ν : Measure ℤ) (hν : ¬ Integrable (fun z : ℤ => (z : ℝ) ^ 2) ν)
    (n : ℕ) : printedNorming ν 2 n = Real.sqrt 2 * norming ν 2 n := by
  simp only [printedNorming, norming, hν, ite_false, lt_irrefl]
  rw [← Real.sqrt_mul (by norm_num)]
  congr 1
  ring

/-- Weak convergence of `(W_n - n m) / a_n` to the law `X_1` with Laplace transform
`exp(λ^θ)`; `a_n > 0` **eventually** (the explicit quantile norming vanishes at small `n`).
This is the **definition** of the domain of
attraction with centering `n m`, normalized to the spectrally positive law of 1.10.
For `ν = stepLaw μ` and `m = 0` it is `StableDomain μ θ a` without monotonicity. -/
structure IsStableAttracted (ν : Measure ℤ) (θ m : ℝ) (a : ℕ → ℝ) : Prop where
  alpha_mem : 1 < θ ∧ θ ≤ 2
  pos : ∃ N : ℕ, ∀ n : ℕ, N ≤ n → 0 < a n
  converges : ∃ X : Measure ℝ, IsProbabilityMeasure X ∧
    (∀ lam : ℝ, 0 < lam → ∫ y, Real.exp (-lam * y) ∂X = Real.exp (lam ^ θ)) ∧
    ∀ f : BoundedContinuousFunction ℝ ℝ,
      Tendsto (fun n : ℕ => ∫ x, f x ∂((intWalk ν n).map (fun z : ℤ => ((z : ℝ) - n * m) / a n)))
        atTop (𝓝 (∫ x, f x ∂X))

theorem stableDomain_isStableAttracted {μ : PMF ℕ} {α : ℝ} {a : ℕ → ℝ}
    (h : StableDomain μ α a) : IsStableAttracted (stepLaw μ) α 0 a := by
  obtain ⟨X, hX, hL, hw⟩ := h.converges
  refine ⟨h.alpha_mem, ⟨1, h.pos⟩, X, hX, hL, fun f => ?_⟩
  simpa [intWalk_stepLaw] using hw f

/-- Bridge to BGW's `StableDomain`: replace the first `N` terms by `a N` (this keeps
monotonicity and gives positivity for all `n ≥ 1`); the new sequence agrees with `a` eventually. -/
theorem IsStableAttracted.exists_stableDomain {μ : PMF ℕ} {α : ℝ} {a : ℕ → ℝ}
    (hc : IsCritical μ) (hne : μ 1 ≠ 1) (hmono : Monotone a)
    (h : IsStableAttracted (stepLaw μ) α 0 a) :
    ∃ a' : ℕ → ℝ, (∀ᶠ n in atTop, a' n = a n) ∧ StableDomain μ α a' := by
  obtain ⟨N, hN⟩ := h.pos
  refine ⟨fun n => a (max n N), ?_, ?_⟩
  · filter_upwards [eventually_ge_atTop N] with n hn
    simp [max_eq_left hn]
  · obtain ⟨X, hX, hL, hw⟩ := h.converges
    refine ⟨hc, hne, h.alpha_mem, fun m n hmn => hmono (max_le_max hmn le_rfl),
      fun n _ => hN _ (le_max_right _ _), X, hX, hL, fun f => ?_⟩
    have := hw f
    simp only [intWalk_stepLaw, mul_zero, sub_zero] at this ⊢
    refine this.congr' ?_
    filter_upwards [eventually_ge_atTop N] with n hn
    simp [max_eq_left hn]

instance isProbabilityMeasure_stepLaw (μ : PMF ℕ) : IsProbabilityMeasure (stepLaw μ) := by
  unfold stepLaw
  infer_instance

theorem stepLaw_lt_neg_one (μ : PMF ℕ) : stepLaw μ {z | z < -1} = 0 := by
  rw [stepLaw, Measure.map_apply (measurable_of_countable _) (MeasurableSet.of_discrete)]
  convert measure_empty (μ := μ.toMeasure)
  ext k
  simp
  omega

theorem integrable_offspring {μ : PMF ℕ} (hc : IsCritical μ) :
    Integrable (fun j : ℕ => (j : ℝ)) μ.toMeasure := by
  refine ⟨(measurable_of_countable _).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun j => Nat.cast_nonneg j),
    lintegral_countable']
  simp only [ENNReal.ofReal_natCast,
    PMF.toMeasure_apply_singleton μ _ (measurableSet_singleton _)]
  rw [show ∑' j : ℕ, (j : ℝ≥0∞) * μ j = 1 from hc]
  exact ENNReal.one_lt_top

theorem integrable_stepLaw {μ : PMF ℕ} (hc : IsCritical μ) :
    Integrable (fun z : ℤ => (z : ℝ)) (stepLaw μ) := by
  rw [stepLaw, integrable_map_measure (measurable_of_countable _).aestronglyMeasurable
    (measurable_of_countable _).aemeasurable]
  have h := (integrable_offspring hc).sub (integrable_const (1 : ℝ))
  simp only [Function.comp_def, Int.cast_sub, Int.cast_natCast, Int.cast_one]
  exact h

theorem mean_stepLaw {μ : PMF ℕ} (hc : IsCritical μ) : mean (stepLaw μ) = 0 := by
  rw [mean, stepLaw, integral_map (measurable_of_countable _).aemeasurable
    (measurable_of_countable _).aestronglyMeasurable]
  simp only [Int.cast_sub, Int.cast_natCast, Int.cast_one]
  rw [integral_sub (integrable_offspring hc) (integrable_const _),
    Scalar.offspring_integral_eq_one hc]
  simp

/-- **Proved bridge.**  For a critical aperiodic `μ` with `StableDomain`, the existing
`Scalar.localLimit_aperiodic` is `llt_abstract` for `ν = stepLaw μ`, `m = 0`. -/
theorem llt_stepLaw {μ : PMF ℕ} {α : ℝ} {a : ℕ → ℝ} (h : StableDomain μ α a) (hap : Aperiodic μ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ k : ℤ,
      |a n * intWalkProb (stepLaw μ) n k -
          Scalar.stableDensity α (((k : ℝ) - n * mean (stepLaw μ)) / a n)| ≤ ε := by
  have hd := (aperiodic_iff_latticeSpan_eq_one h.critical h.nondegenerate).1 hap
  obtain ⟨N, hN⟩ := Scalar.localLimit_aperiodic h hd hε
  refine ⟨N, fun n hn k => ?_⟩
  rw [intWalkProb_stepLaw, mean_stepLaw h.critical, mul_zero, sub_zero]
  exact hN n hn k

/-! ## 5. Lemma 1.11 (`lem:locallimit`) and Remark 1.12 (`rem:lattice`) -/

/-- `ζ(τ) ≥ n`, including infinite trees (they have probability zero in the critical case). -/
def sizeGeEvent (n : ℕ) : Set BGW.LocallyFinite.Tree :=
  {T | ¬ FiniteVertices T ∨ n ≤ {u | Present T u}.ncard}

/-- Kemperman at `ℓ = 1`: `n P[ζ = n] = P[W_n = -1]` for `n ≥ 1`. -/
theorem nat_mul_sizeProb {μ : PMF ℕ} {n : ℕ} (_hn : 1 ≤ n) :
    (n : ℝ) * (bienaymeLaw μ.toMeasure).real (sizeEvent n) = walkProb μ n (-1) := by
  have hF : BGW.forestWeight μ 1 n = bienaymeLaw μ.toMeasure (sizeEvent n) := by
    simpa only [PMF.toMeasure_apply_singleton μ _ (measurableSet_singleton _)] using
      BGW.LocallyFinite.forestWeight_one_eq_bienaymeLaw_sizeEvent μ.toMeasure n
  simpa [hF, measureReal_def] using Scalar.natCast_mul_forestWeight_toReal μ (ℓ := 1) (by omega) n

/-- The size law with its **exact** constant, on the admissible lattice
`d ∣ n - 1` (`d = latticeSpan μ`): `n a_n P[ζ = n] - d p₁(0) → 0`.
This covers the periodic case (`rem:lattice`) and, for `d = 1`, `lem:locallimit`. -/
theorem sizeProb_lattice_asymp {μ : PMF ℕ} {α : ℝ} {a : ℕ → ℝ} (h : StableDomain μ α a)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ((Scalar.latticeSpan μ : ℤ) ∣ (n : ℤ) - 1) →
      |(n : ℝ) * a n * (bienaymeLaw μ.toMeasure).real (sizeEvent n) -
          Scalar.latticeSpan μ * Scalar.stableDensity α 0| ≤ ε := by
  set d : ℝ := (Scalar.latticeSpan μ : ℝ) with hd
  have harg : Tendsto (fun n : ℕ => (-1 : ℝ) / a n) atTop (𝓝 0) :=
    (Scalar.tendsto_atTop h).const_div_atTop (-1)
  have hden : Tendsto (fun n : ℕ => d * Scalar.stableDensity α ((-1 : ℝ) / a n)) atTop
      (𝓝 (d * Scalar.stableDensity α 0)) :=
    ((Scalar.continuous_stableDensity h.alpha_mem).continuousAt.tendsto.comp harg).const_mul _
  obtain ⟨N₀, hN₀⟩ := Metric.tendsto_atTop.1 hden (ε / 2) (by positivity)
  obtain ⟨N₁, hN₁⟩ := Scalar.localLimit h (show 0 < ε / 2 by positivity)
  refine ⟨max (max N₀ N₁) 1, fun n hn hdvd => ?_⟩
  have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
  have hn0 : N₀ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hn1' : N₁ ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  have hLL := hN₁ n hn1' (-1) (by rwa [show (-1 : ℤ) + n = n - 1 by ring])
  simp only [Int.cast_neg, Int.cast_one] at hLL
  have hcl := hN₀ n hn0
  rw [Real.dist_eq] at hcl
  have hE : (n : ℝ) * a n * (bienaymeLaw μ.toMeasure).real (sizeEvent n) =
      a n * walkProb μ n (-1) := by
    rw [← nat_mul_sizeProb (μ := μ) hn1]; ring
  rw [hE]
  calc _ ≤ |a n * walkProb μ n (-1) - d * Scalar.stableDensity α ((-1 : ℝ) / a n)| +
        |d * Scalar.stableDensity α ((-1 : ℝ) / a n) - d * Scalar.stableDensity α 0| :=
      abs_sub_le _ _ _
    _ ≤ ε / 2 + ε / 2 := add_le_add hLL hcl.le
    _ = ε := by ring

/-- **Lemma 1.11, first half**, in terms of any `StableDomain` norming `a` (`a_n = B_n =
n^{1/θ} h(n)`): `P[ζ = n] ∼ p₁(0) / (n a_n)`, for aperiodic `μ`. -/
theorem sizeProb_asymp {μ : PMF ℕ} {α : ℝ} {a : ℕ → ℝ} (h : StableDomain μ α a)
    (hap : Aperiodic μ) :
    Tendsto (fun n : ℕ => (n : ℝ) * a n * (bienaymeLaw μ.toMeasure).real (sizeEvent n)) atTop
      (𝓝 (Scalar.stableDensity α 0)) := by
  have hd := (aperiodic_iff_latticeSpan_eq_one h.critical h.nondegenerate).1 hap
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := sizeProb_lattice_asymp h (half_pos hε)
  refine ⟨N, fun n hn => ?_⟩
  have := hN n hn (by rw [hd]; exact one_dvd _)
  rw [hd, Nat.cast_one, one_mul] at this
  rw [Real.dist_eq]
  exact lt_of_le_of_lt this (half_lt_self hε)


/-- **Remark 1.12** (both halves, in terms of `d = latticeSpan μ`, the span of `supp μ`
since `μ 0 > 0`): for large `n`, `P[ζ = n] > 0` iff `d ∣ n - 1`. -/
theorem sizeProb_pos_iff {μ : PMF ℕ} {α : ℝ} {a : ℕ → ℝ} (h : StableDomain μ α a) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (bienaymeLaw μ.toMeasure (sizeEvent n) ≠ 0 ↔ (Scalar.latticeSpan μ : ℤ) ∣ (n : ℤ) - 1) := by
  have hd : (0 : ℝ) < Scalar.latticeSpan μ := by
    exact_mod_cast Scalar.latticeSpan_pos h.critical h.nondegenerate
  have hp0 := Scalar.stableDensity_zero_pos h.alpha_mem
  obtain ⟨N, hN⟩ := sizeProb_lattice_asymp h (show 0 < (Scalar.latticeSpan μ : ℝ) *
    Scalar.stableDensity α 0 / 2 by positivity)
  refine ⟨max N 1, fun n hn => ?_⟩
  have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
  constructor
  · intro hne
    by_contra hnd
    apply hne
    have h0 : walkProb μ n (-1) = 0 :=
      Scalar.walkProb_eq_zero_of_not_dvd h (by rwa [show (-1 : ℤ) + n = n - 1 by ring])
    have := nat_mul_sizeProb (μ := μ) hn1
    rw [h0] at this
    have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn1.trans_lt' zero_lt_one |>.ne'
    have hreal : (bienaymeLaw μ.toMeasure).real (sizeEvent n) = 0 :=
      (mul_eq_zero.1 this).resolve_left hnR
    exact (measureReal_eq_zero_iff).1 hreal
  · intro hdvd hzero
    have := hN n (le_trans (le_max_left _ _) hn) hdvd
    have hreal : (bienaymeLaw μ.toMeasure).real (sizeEvent n) = 0 := by
      simp [measureReal_def, hzero]
    have hpos : 0 < (Scalar.latticeSpan μ : ℝ) * Scalar.stableDensity α 0 := mul_pos hd hp0
    rw [hreal, mul_zero, zero_sub, abs_neg, abs_of_pos hpos] at this
    linarith

/-- The aperiodic corollary of 1.12: every large `n` is admissible. -/
theorem sizeProb_ne_zero_eventually {μ : PMF ℕ} {α : ℝ} {a : ℕ → ℝ} (h : StableDomain μ α a)
    (hap : Aperiodic μ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → bienaymeLaw μ.toMeasure (sizeEvent n) ≠ 0 := by
  have hd := (aperiodic_iff_latticeSpan_eq_one h.critical h.nondegenerate).1 hap
  obtain ⟨N, hN⟩ := sizeProb_pos_iff h
  exact ⟨N, fun n hn => (hN n hn).2 (by rw [hd]; exact one_dvd _)⟩

/-! ## 6. Finite variance: reuse of `stableDomain_of_finiteVariance`, and the ratio check -/

/-- With finite variance, `norming` is `σ √(n/2)` (first branch of the definition). -/
theorem norming_of_integrable_sq {ν : Measure ℤ} (h : Integrable (fun z : ℤ => (z : ℝ) ^ 2) ν)
    (θ : ℝ) (n : ℕ) : norming ν θ n = Real.sqrt (variance ν) * Real.sqrt (n / 2) := by
  classical
  simp [norming, h]

/-- **Proved reuse.** For a critical nondegenerate law with finite variance, the corrected
norming at index `2` is exactly the sequence of `Scalar.stableDomain_of_finiteVariance`. -/
theorem stableDomain_norming_finiteVariance {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hfin : MemLp (fun j : ℕ => (j : ℝ)) 2 μ.toMeasure) :
    StableDomain μ 2 (norming (stepLaw μ) 2) := by
  have h := Scalar.stableDomain_of_finiteVariance hc hne hfin
  have hsq : Integrable (fun z : ℤ => (z : ℝ) ^ 2) (stepLaw μ) :=
    (Scalar.memLp_step_of_memLp_offspring hfin).integrable_sq
  convert h using 1
  funext n
  rw [norming_of_integrable_sq hsq, variance, mean_stepLaw hc]
  simp only [sub_zero]
  rw [Real.sqrt_div (by exact_mod_cast Nat.zero_le n)]
  ring

/-- The law of `Y = K - 1` given `K ≥ 1` (`eq:Y`), on `ℤ`: `P[Y = i] = μ(i+1)/(1-μ₀)`. -/
noncomputable def etaLaw (μ : PMF ℕ) : Measure ℤ :=
  (ProbabilityTheory.cond μ.toMeasure (Set.Ici 1)).map (fun k : ℕ => (k : ℤ) - 1)

/-- **Proved algebra**: that limit squared, `μ₀ σ'^2/σ²`, is *strictly smaller* than
`c = μ₀/(1-μ₀)` for `0 < μ₀ < 1`; so `B'_n / B_{n/μ₀} → c^{1/θ}` is false in finite variance. -/
theorem finiteVariance_ratio_sq_lt {m σ2 : ℝ} (hm0 : 0 < m) (hm1 : m < 1) (hσ : 0 < σ2) :
    m * (σ2 / (1 - m) - m / (1 - m) ^ 2) / σ2 < m / (1 - m) := by
  have h1 : 0 < 1 - m := by linarith
  have key :
      m * (σ2 / (1 - m) - m / (1 - m) ^ 2) / σ2 =
        m / (1 - m) - m ^ 2 / ((1 - m) ^ 2 * σ2) := by
    field_simp
  rw [key]
  have : 0 < m ^ 2 / ((1 - m) ^ 2 * σ2) := by positivity
  linarith

/-! ## 8. The Gaussian density -/

/-- The Gaussian `p₁` at `θ = 2`: `e^{-x²/4}/√(4π)` (line 3 of 1.3). -/
noncomputable def gaussDensity (x : ℝ) : ℝ := Real.exp (-x ^ 2 / 4) / Real.sqrt (4 * Real.pi)

/-! ## 9. Additions after audit -/

section GaussianConvolution

/-- `∫ exp(-(A u² + B u + C)) du = √(π/A) exp(B²/(4A) - C)`. -/
theorem integral_exp_neg_quadratic {A : ℝ} (hA : 0 < A) (B C : ℝ) :
    ∫ u : ℝ, Real.exp (-(A * u ^ 2 + B * u + C)) =
      Real.sqrt (Real.pi / A) * Real.exp (B ^ 2 / (4 * A) - C) := by
  have h : ∀ u : ℝ, Real.exp (-(A * u ^ 2 + B * u + C)) =
      Real.exp (-A * (u + B / (2 * A)) ^ 2) * Real.exp (B ^ 2 / (4 * A) - C) := by
    intro u
    rw [← Real.exp_add]
    congr 1
    field_simp
    ring
  simp_rw [h]
  rw [integral_mul_const, integral_add_right_eq_self (fun u : ℝ => Real.exp (-A * u ^ 2))
    (B / (2 * A)), integral_gaussian]

/-- `F₀(u) = (2π(1-μ₀))^{-1/2} exp(-μ₀² u²/(2(1-μ₀)))` (line 1849: `F₀(u) = √μ₀ F(μ₀^{3/2}u)`);
`μ₀ F₀` is the `N(0,(1-μ₀)/μ₀²)` density. -/
noncomputable def F0 (m u : ℝ) : ℝ :=
  Real.exp (-(m ^ 2 * u ^ 2) / (2 * (1 - m))) / Real.sqrt (2 * Real.pi * (1 - m))

/-- `G₀(u,x)` of line 1850 in the finite-variance case `θ = 2`, with `c = μ₀/(1-μ₀)`,
`c^{1/2}` written `√c`, `c^{3/2} = c √c`, `σ' = sp`. -/
noncomputable def G0fv (m sp x u : ℝ) : ℝ :=
  Real.sqrt (m / (1 - m)) * gaussDensity (-(Real.sqrt (m / (1 - m)) * x) -
    Real.sqrt 2 * ((m / (1 - m)) * Real.sqrt (m / (1 - m))) * u / sp)

/-- **Corrected Gaussian identity** (finite variance, line 1937-1940).  With
`r = √μ₀ σ'/σ` (`σ'^2 = σ²/(1-μ₀) - μ₀/(1-μ₀)²`), the convolution `μ₀ ∫ F₀(u) G₀(u,x) du`
equals `r p₁(r x)`.  The paper's `c^{1/2} p₁(c^{1/2} x)` is wrong: `r < c^{1/2}`
(`r_lt_sqrt_c`); at `x = j/B'_n`, `r x = j / B_{n/μ₀}` as printed, only the prefactor and the
inner scaling by `r` (not `√c`) are corrected. -/
theorem gaussian_convolution_identity {m s sp : ℝ} (hm0 : 0 < m) (hm1 : m < 1) (hs : 0 < s)
    (hsp : 0 < sp) (h : sp ^ 2 = s ^ 2 / (1 - m) - m / (1 - m) ^ 2) (x : ℝ) :
    m * ∫ u : ℝ, F0 m u * G0fv m sp x u =
      Real.sqrt m * sp / s * gaussDensity (Real.sqrt m * sp / s * x) := by
  have h1m : 0 < 1 - m := by linarith
  set c : ℝ := m / (1 - m) with hc
  have hc0 : 0 < c := div_pos hm0 h1m
  set sc : ℝ := Real.sqrt c with hsc
  have hsc2 : sc ^ 2 = c := Real.sq_sqrt hc0.le
  have hsc0 : 0 < sc := Real.sqrt_pos.2 hc0
  set β : ℝ := Real.sqrt 2 * (c * sc) / sp with hβ
  have hβ2 : β ^ 2 = 2 * c ^ 3 / sp ^ 2 := by
    rw [hβ, div_pow, mul_pow, Real.sq_sqrt (by norm_num), mul_pow, hsc2]; ring
  set A : ℝ := m ^ 2 / (2 * (1 - m)) + β ^ 2 / 4 with hA
  have hApos : 0 < A := by positivity
  set B : ℝ := sc * x * β / 2 with hB
  set C : ℝ := sc ^ 2 * x ^ 2 / 4 with hC
  set K : ℝ := sc / (Real.sqrt (2 * Real.pi * (1 - m)) * Real.sqrt (4 * Real.pi)) with hK
  have hint : ∀ u : ℝ, F0 m u * G0fv m sp x u = K * Real.exp (-(A * u ^ 2 + B * u + C)) := by
    intro u
    have e : -(A * u ^ 2 + B * u + C) =
        -(m ^ 2 * u ^ 2) / (2 * (1 - m)) + -(-(sc * x) - β * u) ^ 2 / 4 := by
      rw [hA, hB, hC]; ring
    rw [e, Real.exp_add]
    unfold F0 G0fv gaussDensity
    have hβu : Real.sqrt 2 * (c * sc) * u / sp = β * u := by rw [hβ]; ring
    rw [hβu]
    have : Real.sqrt (2 * Real.pi * (1 - m)) ≠ 0 := (Real.sqrt_pos.2 (by positivity)).ne'
    have : Real.sqrt (4 * Real.pi) ≠ 0 := (Real.sqrt_pos.2 (by positivity)).ne'
    rw [hK]
    field_simp
    have hxs : (-(Real.sqrt (m / (1 - m)) * x) - u * β) = (-(x * sc) - u * β) := by
      rw [hsc, hc]; ring
    rw [hxs]
  simp_rw [hint]
  rw [integral_const_mul, integral_exp_neg_quadratic hApos]
  set r : ℝ := Real.sqrt m * sp / s with hr
  have hs2 : s ^ 2 = (sp ^ 2 + m / (1 - m) ^ 2) * (1 - m) := by
    have : s ^ 2 / (1 - m) = sp ^ 2 + m / (1 - m) ^ 2 := by linarith
    field_simp at this ⊢
    nlinarith [this]
  have hr2 : r ^ 2 = m * sp ^ 2 / s ^ 2 := by
    rw [hr, div_pow, mul_pow, Real.sq_sqrt hm0.le]
  -- exponent identity
  have hE : B ^ 2 / (4 * A) - C = -(r * x) ^ 2 / 4 := by
    have hB2 : B ^ 2 = c * x ^ 2 * (2 * c ^ 3 / sp ^ 2) / 4 := by
      rw [hB, div_pow, mul_pow, mul_pow, hsc2, hβ2]; ring
    rw [hB2, hC, hsc2, mul_pow, hr2, hA, hβ2, hs2]
    rw [hc]
    field_simp
    ring
  -- prefactor identity
  have hP : m * K * Real.sqrt (Real.pi / A) = r / Real.sqrt (4 * Real.pi) := by
    have hsq : m * sc * Real.sqrt (Real.pi / A) / Real.sqrt (2 * Real.pi * (1 - m)) = r := by
      have hl : 0 ≤ m * sc * Real.sqrt (Real.pi / A) / Real.sqrt (2 * Real.pi * (1 - m)) := by
        positivity
      have hr0 : 0 ≤ r := by positivity
      rw [← sq_eq_sq₀ hl hr0, div_pow, mul_pow, mul_pow, hsc2, Real.sq_sqrt (by positivity),
        Real.sq_sqrt (by positivity), hr2, hA, hβ2, hs2, hc]
      field_simp
      ring
    rw [hK]
    have : Real.sqrt (2 * Real.pi * (1 - m)) ≠ 0 := (Real.sqrt_pos.2 (by positivity)).ne'
    have h4 : Real.sqrt (4 * Real.pi) ≠ 0 := (Real.sqrt_pos.2 (by positivity)).ne'
    rw [← hsq]
    field_simp
  unfold gaussDensity
  rw [hE, show m * (K * (Real.sqrt (Real.pi / A) * Real.exp (-(r * x) ^ 2 / 4))) =
    (m * K * Real.sqrt (Real.pi / A)) * Real.exp (-(r * x) ^ 2 / 4) by ring, hP]
  ring

/-- `r < √c`: the prefactor of the corrected identity is strictly smaller than the printed one. -/
theorem r_lt_sqrt_c {m s sp : ℝ} (hm0 : 0 < m) (hm1 : m < 1) (hs : 0 < s) (_hsp : 0 < sp)
    (h : sp ^ 2 = s ^ 2 / (1 - m) - m / (1 - m) ^ 2) :
    Real.sqrt m * sp / s < Real.sqrt (m / (1 - m)) := by
  have hlt := finiteVariance_ratio_sq_lt hm0 hm1 (sq_pos_of_pos hs)
  rw [← h] at hlt
  apply Real.lt_sqrt_of_sq_lt
  rw [div_pow, mul_pow, Real.sq_sqrt hm0.le]
  have : m * sp ^ 2 / s ^ 2 = m * (sp ^ 2) / s ^ 2 := rfl
  exact hlt

end GaussianConvolution

/-- The printed hypothesis `(H_θ)(ii)` made precise: finite variance **and `θ = 2`**
(BGW proves finite variance forces `θ = 2`, `Scalar.alpha_eq_two_of_finiteVariance`), or
`μ[j,∞) = j^{-θ} L(j)` with `L` slowly varying (measurable, nonnegative). -/
def HthetaTail (μ : PMF ℕ) (θ : ℝ) : Prop :=
  (θ = 2 ∧ MemLp (fun j : ℕ => (j : ℝ)) 2 μ.toMeasure) ∨
  (∃ L : ℝ → ℝ, Measurable L ∧ (∀ x, 0 < x → 0 ≤ L x) ∧ SlowlyVarying L ∧
    ∀ j : ℕ, 1 ≤ j → (μ.toMeasure (Set.Ici j)).toReal = (j : ℝ) ^ (-θ) * L j)

end BGW.StableTrees.Attraction
