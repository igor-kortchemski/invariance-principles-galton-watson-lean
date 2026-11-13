/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.SupremumLadderTransformSemigroup
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Exponential form of the ladder Laplace semigroup

The rational-level argument for a positive monotone multiplicative function follows the
existing no-arrival Cauchy proof, with strict positivity supplied by the integral itself.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees

private lemma mul_nsmul {f : ℝ≥0 → ℝ} (f0 : f 0 = 1)
    (fmul : ∀ s t : ℝ≥0, f (s + t) = f s * f t) (n : ℕ) (t : ℝ≥0) :
    f (n • t) = f t ^ n := by
  induction n with
  | zero => simp [f0]
  | succ n ih => rw [succ_nsmul, fmul, ih, pow_succ]

private lemma eq_exp_div_nat {f : ℝ≥0 → ℝ} (hf : ∀ t, 0 ≤ f t)
    (f0 : f 0 = 1) (fmul : ∀ s t : ℝ≥0, f (s + t) = f s * f t)
    {c : ℝ} (hc : f 1 = Real.exp (-c)) (m n : ℕ) (hn : n ≠ 0) :
    f ((m : ℝ≥0) / (n : ℝ≥0)) = Real.exp (-c * ((m : ℝ) / (n : ℝ))) := by
  have hpow : f ((m : ℝ≥0) / (n : ℝ≥0)) ^ n = f 1 ^ m := by
    calc
      _ = f (n • ((m : ℝ≥0) / (n : ℝ≥0))) := (mul_nsmul f0 fmul _ _).symm
      _ = f (m : ℝ≥0) := by
        congr 1
        rw [nsmul_eq_mul']
        field_simp
      _ = f (m • (1 : ℝ≥0)) := by simp
      _ = f 1 ^ m := mul_nsmul f0 fmul _ _
  apply (pow_left_inj₀ (hf _) (Real.exp_nonneg _) hn).mp
  calc
    _ = f 1 ^ m := hpow
    _ = Real.exp (-c) ^ m := by rw [hc]
    _ = Real.exp ((m : ℝ) * (-c)) := (Real.exp_nat_mul _ _).symm
    _ = Real.exp ((n : ℝ) * (-c * ((m : ℝ) / (n : ℝ)))) := by
      congr 1
      field_simp
    _ = _ := Real.exp_nat_mul _ _

private lemma eq_exp_ratCast {f : ℝ≥0 → ℝ} (hf : ∀ t, 0 ≤ f t)
    (f0 : f 0 = 1) (fmul : ∀ s t : ℝ≥0, f (s + t) = f s * f t)
    {c : ℝ} (hc : f 1 = Real.exp (-c)) (r : ℚ) (hr : 0 ≤ (r : ℝ)) :
    f (Real.toNNReal (r : ℝ)) = Real.exp (-c * (r : ℝ)) := by
  have hrq : 0 ≤ r := by exact_mod_cast hr
  have hnum : 0 ≤ r.num := Rat.num_nonneg.2 hrq
  have hrepr : Real.toNNReal (r : ℝ) = (r.num.toNat : ℝ≥0) / (r.den : ℝ≥0) := by
    apply NNReal.eq
    simp only [NNReal.coe_div, NNReal.coe_natCast, Real.coe_toNNReal _ hr]
    rw [Rat.cast_def]
    have hnumcast : (r.num.toNat : ℝ) = r.num := by
      exact_mod_cast Int.toNat_of_nonneg hnum
    rw [hnumcast]
  rw [hrepr, eq_exp_div_nat hf f0 fmul hc r.num.toNat r.den r.den_nz]
  congr 2
  simp only [Rat.cast_def]
  have hnumcast : (r.num.toNat : ℝ) = r.num := by
    exact_mod_cast Int.toNat_of_nonneg hnum
  rw [hnumcast]

private lemma eq_exp_of_multiplicative {f : ℝ≥0 → ℝ} (hf : ∀ t, 0 ≤ f t)
    (f0 : f 0 = 1) (fmul : ∀ s t : ℝ≥0, f (s + t) = f s * f t)
    (fanti : Antitone f) (hf1pos : 0 < f 1)
    (t : ℝ≥0) : f t = Real.exp (-(t : ℝ) * (-Real.log (f 1))) := by
  let c : ℝ := -Real.log (f 1)
  have hc : f 1 = Real.exp (-c) := by
    dsimp [c]
    rw [neg_neg, Real.exp_log hf1pos]
  have hmain (x : ℝ≥0) : f x = Real.exp (-c * (x : ℝ)) := by
    rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ x) with hx | hx
    · rw [← hx, f0]
      simp
    · apply le_antisymm
      · obtain ⟨r, _hrmono, hrlt, hrlim⟩ := Real.exists_seq_rat_strictMono_tendsto (x : ℝ)
        have hpos : ∀ᶠ n : ℕ in atTop, 0 < (r n : ℝ) :=
          hrlim.eventually (Ioi_mem_nhds hx)
        have hlin : Tendsto (fun r : ℝ => -c * r) (𝓝 (x : ℝ)) (𝓝 (-c * (x : ℝ))) :=
          tendsto_const_nhds.mul tendsto_id
        have hexp := Real.continuous_exp.continuousAt.tendsto.comp hlin
        apply ge_of_tendsto (hexp.comp hrlim)
        filter_upwards [hpos] with n hn
        have hle : Real.toNNReal (r n : ℝ) ≤ x := by
          have := Real.toNNReal_le_toNNReal (hrlt n).le
          simpa using this
        exact (fanti hle).trans_eq (eq_exp_ratCast hf f0 fmul hc (r n) hn.le)
      · obtain ⟨r, _hranti, hrlt, hrlim⟩ := Real.exists_seq_rat_strictAnti_tendsto (x : ℝ)
        have hlin : Tendsto (fun r : ℝ => -c * r) (𝓝 (x : ℝ)) (𝓝 (-c * (x : ℝ))) :=
          tendsto_const_nhds.mul tendsto_id
        have hexp := Real.continuous_exp.continuousAt.tendsto.comp hlin
        apply le_of_tendsto (hexp.comp hrlim)
        filter_upwards [] with n
        have hle : x ≤ Real.toNNReal (r n : ℝ) := by
          have := Real.toNNReal_le_toNNReal (hrlt n).le
          simpa using this
        have hnpos : 0 < (r n : ℝ) := (show (0 : ℝ) < (x : ℝ) from hx).trans (hrlt n)
        exact (eq_exp_ratCast hf f0 fmul hc (r n) hnpos.le).symm.le.trans (fanti hle)
  rw [hmain]
  dsimp [c]
  ring_nf

/-- **Exponential form** (measurable multiplicative Cauchy equation, positivity from
`φ(z/2ⁿ) → 1`): there is a rate `k ≥ 0` with `φ(z) = e^{-zk}` for all `z`. -/
theorem exists_supLadderLaplace_eq_exp {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {q lam : ℝ}
    (hq : 0 ≤ q) (hlam : 0 ≤ lam) :
    ∃ k : ℝ, 0 ≤ k ∧ ∀ z : ℝ≥0, supLadderLaplace θ q lam z = Real.exp (-(z : ℝ) * k) := by
  let φ := supLadderLaplace θ q lam
  have hbounds (z : ℝ≥0) : φ z ∈ Icc (0 : ℝ) 1 := supLadderLaplace_mem_Icc hθ hq hlam z
  have hmul : ∀ y z, φ (y + z) = φ y * φ z := supLadderLaplace_add hθ hq hlam
  have hanti : Antitone φ := by
    intro y z hyz
    have he := hmul y (z - y)
    rw [add_tsub_cancel_of_le hyz] at he
    rw [he]
    exact mul_le_of_le_one_right (hbounds y).1 (hbounds _).2
  have hm : Measurable (fun f : DLoc => Real.exp
      (-q * (supLadderTime θ 1 f : ℝ) - lam * supLadderHeight θ 1 f)) :=
    ((measurable_const.mul (measurable_supLadderPair θ 1).fst).sub
      (measurable_const.mul (measurable_supLadderPair θ 1).snd)).exp
  have hb : ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc),
      ‖Real.exp (-q * (supLadderTime θ 1 f : ℝ) - lam * supLadderHeight θ 1 f)‖ ≤ 1 := by
    filter_upwards [ae_supLadderPair_path hθ] with f hf
    rw [Real.norm_of_nonneg (Real.exp_pos _).le, Real.exp_le_one_iff]
    have hA := (hf.1 1).1
    have hB := (hf.1 1).2
    change 0 ≤ (supLadderTime θ 1 f : ℝ) at hA
    change 0 ≤ supLadderHeight θ 1 f at hB
    nlinarith [mul_nonneg hq hA, mul_nonneg hlam hB]
  have hpos : 0 < φ 1 := integral_exp_pos (Integrable.of_bound hm.aestronglyMeasurable 1 hb)
  refine ⟨-Real.log (φ 1), neg_nonneg.mpr (Real.log_nonpos (hbounds 1).1 (hbounds 1).2), ?_⟩
  exact eq_exp_of_multiplicative (fun z => (hbounds z).1)
    (supLadderLaplace_zero hθ q lam) hmul hanti hpos

end BGW.StableTrees
