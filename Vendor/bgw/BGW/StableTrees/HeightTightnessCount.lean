/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.HeightTightnessShortGaps
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Uniform tightness of the regenerated crossing count

A uniformly positive chance of a macroscopic gap contracts the Laplace transform
below one. The exponential crossing-count bound then controls the number of
crossings before any fixed scaled horizon.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal Classical
open BGW.StableTrees.DiscreteForest
namespace BGW.StableTrees.HeightTightness

/-- Splitting at a deterministic cutoff bounds the first-crossing Laplace transform. -/
theorem heightUpcrossing_laplace_le (μ : PMF ℕ) (q m n : ℕ) :
    (∫ ω, Real.exp (-((heightUpcrossingStop q ω).toNat : ℝ) / n)
      ∂(offspringSeqLaw μ).toMeasure) ≤
      Real.exp (-(m : ℝ) / n) + (1 - Real.exp (-(m : ℝ) / n)) *
        (offspringSeqLaw μ).toMeasure.real {ω | (heightUpcrossingStop q ω).toNat ≤ m} := by
  let P := (offspringSeqLaw μ).toMeasure
  let E : Set (ℕ → ℕ) := {ω | (heightUpcrossingStop q ω).toNat ≤ m}
  let r := Real.exp (-(m : ℝ) / n)
  let f : (ℕ → ℕ) → ℝ := fun ω => Real.exp (-((heightUpcrossingStop q ω).toNat : ℝ) / n)
  have ht : Measurable (fun ω => (heightUpcrossingStop q ω).toNat) :=
    (measurable_of_countable ENat.toNat).comp (measurable_heightUpcrossingStop q)
  have hE : MeasurableSet E := measurableSet_le ht measurable_const
  have hm : Measurable f := (measurable_of_countable
    (fun k : ℕ => Real.exp (-(k : ℝ) / n))).comp ht
  have hf (ω : ℕ → ℕ) : f ω ≤ 1 := Real.exp_le_one_iff.mpr
    (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg _)) (Nat.cast_nonneg n))
  have hi : Integrable f P := Integrable.of_bound hm.aestronglyMeasurable 1
    (Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact hf ω)
  have hI : Integrable (E.indicator (fun _ => 1 - r)) P := (integrable_const _).indicator hE
  have hb : ∀ ω, f ω ≤ r + E.indicator (fun _ => 1 - r) ω := by
    intro ω
    by_cases hω : ω ∈ E
    · rw [Set.indicator_of_mem hω]
      linarith [hf ω]
    · rw [Set.indicator_of_notMem hω, add_zero]
      apply Real.exp_le_exp.mpr
      have hh : (m : ℝ) ≤ (heightUpcrossingStop q ω).toNat := by
        exact_mod_cast (le_of_not_ge hω : m ≤ (heightUpcrossingStop q ω).toNat)
      exact div_le_div_of_nonneg_right (neg_le_neg hh) (Nat.cast_nonneg n)
  calc
    _ ≤ ∫ ω, r + E.indicator (fun _ => 1 - r) ω ∂P :=
      integral_mono_ae hi ((integrable_const r).add hI) (Eventually.of_forall hb)
    _ = _ := by
      rw [integral_add (integrable_const r) hI, integral_const, integral_indicator_const _ hE]
      simp only [probReal_univ, smul_eq_mul, one_mul]
      dsimp only [r, P, E]
      ring

/-- The initial regenerated gap is the finite reading of the first-upcrossing time. -/
theorem heightRegenerationGap_zero (q : ℕ) (ω : ℕ → ℕ) :
    heightRegenerationGap q 0 ω = (heightUpcrossingStop q ω).toNat := by
  have hs : shiftSeq 0 ω = ω := by funext i; simp [shiftSeq]
  simp [heightRegenerationGap, heightRegenerationStop, nextHeightUpcrossing, hs]

/-- A uniform positive chance of a macroscopic gap contracts its Laplace transform. -/
theorem exists_eventually_heightUpcrossing_laplace_le_lt_one {μ : PMF ℕ} {θ : ℝ}
    {B : ℕ → ℝ} (h : StableDomain μ θ B) {η : ℝ} (hη : 0 < η) :
    ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧ ∀ᶠ n : ℕ in atTop,
      (∫ ω, Real.exp (-((heightUpcrossingStop ⌊η * (n : ℝ) / B n⌋₊ ω).toNat : ℝ) / n)
        ∂(offspringSeqLaw μ).toMeasure) ≤ ρ := by
  obtain ⟨x, hx, hsmall⟩ := exists_pos_eventually_height_hit_probability_small h hη
    (by norm_num : (0 : ℝ) < 1 / 2)
  let r := Real.exp (-(x / 2))
  let ρ := (1 + r) / 2
  have hrpos : 0 < r := Real.exp_pos _
  have hrlt : r < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  refine ⟨ρ, by dsimp [ρ]; positivity, by dsimp [ρ]; linarith, ?_⟩
  filter_upwards [hsmall, eventually_ge_atTop 1, eventually_ge_atTop ⌈2 / x⌉₊]
      with n hn hn1 hnlarge
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn1
  have hlarge : 2 ≤ (n : ℝ) * x := (div_le_iff₀ hx).mp
    ((Nat.le_ceil (2 / x)).trans (Nat.cast_le.mpr hnlarge))
  let q := ⌊η * (n : ℝ) / B n⌋₊
  let m := ⌊(n : ℝ) * x⌋₊
  have hprob : (offspringSeqLaw μ).toMeasure.real
      {ω | (heightUpcrossingStop q ω).toNat ≤ m} ≤ 1 / 2 := by
    have he := heightRegenerationGap_probability μ h.critical h.nondegenerate q 0 m
    simp only [heightRegenerationGap_zero] at he
    exact he.trans_le hn
  have hrn : Real.exp (-(m : ℝ) / n) ≤ r := by
    apply Real.exp_le_exp.mpr
    have hf := Nat.lt_floor_add_one ((n : ℝ) * x)
    have hfrac : x / 2 ≤ (m : ℝ) / n := (le_div_iff₀ hnR).mpr (by dsimp [m]; nlinarith)
    rw [neg_div]
    exact neg_le_neg hfrac
  have hnonneg : 0 ≤ 1 - Real.exp (-(m : ℝ) / n) := by linarith
  have hb := heightUpcrossing_laplace_le μ q m n
  have hmul := mul_le_mul_of_nonneg_left hprob hnonneg
  change _ ≤ ρ
  dsimp only [ρ]
  linarith

/-- The number of regenerated upcrossings before a fixed scaled horizon is eventually tight. -/
theorem exists_eventually_heightRegenerationStop_probability_small
    {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ} (h : StableDomain μ θ B)
    {η T ε : ℝ} (hη : 0 < η) (hT : 0 ≤ T) (hε : 0 < ε) :
    ∃ L : ℕ, ∀ᶠ n : ℕ in atTop, (offspringSeqLaw μ).toMeasure.real
      {ω | heightRegenerationStop ⌊η * (n : ℝ) / B n⌋₊ L ω ≤
        (⌊(n : ℝ) * T⌋₊ : ℕ∞)} ≤ ε := by
  obtain ⟨ρ, hρ, hρ1, hb⟩ := exists_eventually_heightUpcrossing_laplace_le_lt_one h hη
  have hp := (tendsto_pow_atTop_nhds_zero_of_lt_one hρ hρ1).const_mul (Real.exp T)
  rw [mul_zero] at hp
  obtain ⟨L, hL⟩ := (hp.eventually (gt_mem_nhds hε)).exists
  refine ⟨L, ?_⟩
  filter_upwards [hb, eventually_ge_atTop 1] with n hn hn1
  have hi : 0 ≤ ∫ ω,
      Real.exp (-((heightUpcrossingStop ⌊η * (n : ℝ) / B n⌋₊ ω).toNat : ℝ) / n)
      ∂(offspringSeqLaw μ).toMeasure := integral_nonneg fun _ => (Real.exp_pos _).le
  exact (heightRegenerationStop_probability_le μ h.critical h.nondegenerate
    ⌊η * (n : ℝ) / B n⌋₊ L hn1 hT).trans
      ((mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hi hn L) (Real.exp_pos T).le).trans hL.le)

end BGW.StableTrees.HeightTightness
