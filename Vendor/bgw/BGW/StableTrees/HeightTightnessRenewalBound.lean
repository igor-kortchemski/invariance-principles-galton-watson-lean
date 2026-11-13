/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.HeightTightnessRenewal
public import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Probability.Independence.Integration

/-!
# Exponential bounds for the number of regenerated height crossings

The finite crossing time is the sum of its iid durations. Its Laplace transform
therefore factors. Exponential Markov gives a bound for the probability of `L`
crossings before a fixed scaled horizon.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal Classical
open BGW.StableTrees.DiscreteForest

namespace BGW.StableTrees.HeightTightness

/-- On a finite crossing time, the preceding gap durations add to that time. -/
theorem heightRegenerationStop_toNat_eq_sum {q L : ℕ} {ω : ℕ → ℕ}
    (hfin : heightRegenerationStop q L ω ≠ ⊤) :
    (heightRegenerationStop q L ω).toNat =
      ∑ j ∈ Finset.range L, heightRegenerationGap q j ω := by
  induction L with
  | zero => simp [heightRegenerationStop]
  | succ L ih =>
    have hle : heightRegenerationStop q L ω ≤ heightRegenerationStop q (L + 1) ω :=
      monotone_heightRegenerationStop q ω (Nat.le_succ L)
    have hpfin := ne_top_of_le_ne_top hfin hle
    have hnat : (heightRegenerationStop q L ω).toNat ≤
        (heightRegenerationStop q (L + 1) ω).toNat := by
      rw [← ENat.natCast_toNat hpfin, ← ENat.natCast_toNat hfin] at hle
      exact ENat.natCast_le_natCast.mp hle
    rw [Finset.sum_range_succ, ← ih hpfin]
    exact (Nat.add_sub_of_le hnat).symm

/-- The Laplace transform of the `L`th crossing time factors into `L` identical transforms. -/
theorem integral_exp_heightRegenerationStop (μ : PMF ℕ) (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (q L n : ℕ) :
    (∫ ω, Real.exp (-((heightRegenerationStop q L ω).toNat : ℝ) / n)
      ∂(offspringSeqLaw μ).toMeasure) =
      (∫ ω, Real.exp (-((heightUpcrossingStop q ω).toNat : ℝ) / n)
        ∂(offspringSeqLaw μ).toMeasure) ^ L := by
  let f : ℕ → ℝ := fun k => Real.exp (-(k : ℝ) / n)
  have hf : Measurable f := measurable_of_countable _
  have hind : iIndepFun (fun j : Fin L => heightRegenerationGap q j)
      (offspringSeqLaw μ).toMeasure :=
    (iIndepFun_heightRegenerationGap μ hc hne q).precomp Fin.val_injective
  have hprod := hind.integral_fun_prod_comp
    (fun j => (measurable_heightRegenerationGap q j).aemeasurable)
    (f := fun _ => f) (fun _ => hf.aestronglyMeasurable)
  have hmarg (j : Fin L) :
      (∫ ω, f (heightRegenerationGap q j ω) ∂(offspringSeqLaw μ).toMeasure) =
        ∫ ω, f (heightUpcrossingStop q ω).toNat ∂(offspringSeqLaw μ).toMeasure := by
    rw [← integral_map (measurable_heightRegenerationGap q j).aemeasurable
      hf.aestronglyMeasurable, map_heightRegenerationGap μ hc hne q j,
      integral_map (φ := fun ω => (heightUpcrossingStop q ω).toNat)
        ((measurable_of_countable ENat.toNat).comp
        (measurable_heightUpcrossingStop q)).aemeasurable hf.aestronglyMeasurable]
  simp_rw [hmarg] at hprod
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hprod
  rw [← hprod]
  apply integral_congr_ae
  filter_upwards [ae_heightRegenerationStop_ne_top μ hc hne q L] with ω hω
  dsimp only [f]
  rw [← Real.exp_sum]
  congr 1
  rw [Fin.sum_univ_eq_sum_range
    (fun j : ℕ => -(heightRegenerationGap q j ω : ℝ) / n), ← Finset.sum_div, Finset.sum_neg_distrib,
    ← Nat.cast_sum, ← heightRegenerationStop_toNat_eq_sum hω]

/-- Exponential Markov bound for the number of regenerated upcrossings before a horizon. -/
theorem heightRegenerationStop_probability_le (μ : PMF ℕ) (hc : IsCritical μ)
    (hne : μ 1 ≠ 1) (q L : ℕ) {n : ℕ} (hn : 1 ≤ n) {T : ℝ} (hT : 0 ≤ T) :
    (offspringSeqLaw μ).toMeasure.real
      {ω | heightRegenerationStop q L ω ≤ (⌊(n : ℝ) * T⌋₊ : ℕ∞)} ≤
      Real.exp T * (∫ ω, Real.exp (-((heightUpcrossingStop q ω).toNat : ℝ) / n)
        ∂(offspringSeqLaw μ).toMeasure) ^ L := by
  let P := (offspringSeqLaw μ).toMeasure
  let f : (ℕ → ℕ) → ℝ := fun ω =>
    Real.exp (-((heightRegenerationStop q L ω).toNat : ℝ) / n)
  have hm : Measurable f := (measurable_of_countable
    (fun k : ℕ∞ => Real.exp (-(k.toNat : ℝ) / n))).comp
      (measurable_heightRegenerationStop q L)
  have hi : Integrable f P := Integrable.of_bound hm.aestronglyMeasurable 1
    (Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      apply Real.exp_le_one_iff.mpr
      exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg _))
        (Nat.cast_nonneg n))
  have hf : 0 ≤ᵐ[P] f := Eventually.of_forall fun ω => (Real.exp_pos _).le
  have hs : {ω | heightRegenerationStop q L ω ≤ (⌊(n : ℝ) * T⌋₊ : ℕ∞)} ⊆
      {ω | Real.exp (-T) ≤ f ω} := by
    intro ω hω
    simp only [mem_ofPred_eq] at hω ⊢
    have hfin := ne_top_of_le_ne_top (ENat.natCast_ne_top _) hω
    have hle : (heightRegenerationStop q L ω).toNat ≤ ⌊(n : ℝ) * T⌋₊ := by
      rw [← ENat.natCast_toNat hfin] at hω
      exact ENat.natCast_le_natCast.mp hω
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    apply Real.exp_le_exp.mpr
    apply (le_div_iff₀ hnR).mpr
    have hh := (Nat.cast_le.mpr hle).trans (Nat.floor_le (mul_nonneg hnR.le hT))
    nlinarith
  have hmark := (mul_le_mul_of_nonneg_left (measureReal_mono hs)
    (Real.exp_pos (-T)).le).trans (mul_meas_ge_le_integral_of_nonneg hf hi (Real.exp (-T)))
  change Real.exp (-T) * P.real _ ≤ ∫ ω, f ω ∂P at hmark
  change Real.exp (-T) * P.real _ ≤
    ∫ ω, Real.exp (-((heightRegenerationStop q L ω).toNat : ℝ) / n)
      ∂(offspringSeqLaw μ).toMeasure at hmark
  rw [integral_exp_heightRegenerationStop μ hc hne] at hmark
  calc
    _ = Real.exp T * (Real.exp (-T) * P.real _) := by
      rw [← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_left hmark (Real.exp_pos T).le

end BGW.StableTrees.HeightTightness
