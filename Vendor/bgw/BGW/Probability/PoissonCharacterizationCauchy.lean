/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module
public import BGW.Probability.PoissonCharacterizationWindow
public import Mathlib.Topology.Instances.Real.Lemmas

/-! The multiplicative Cauchy equation on nonnegative reals, and the no-arrival law. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

namespace BGW.Probability

private lemma mul_nsmul {f : ℝ≥0 → ℝ} (f0 : f 0 = 1)
    (fmul : ∀ s t : ℝ≥0, f (s + t) = f s * f t) (n : ℕ) (t : ℝ≥0) :
    f (n • t) = f t ^ n := by
  induction n with
  | zero => simp [f0]
  | succ n ih => rw [succ_nsmul, fmul, ih, pow_succ]

private lemma one_ne_zero_of_tendsto {f : ℝ≥0 → ℝ} (f0 : f 0 = 1)
    (fmul : ∀ s t : ℝ≥0, f (s + t) = f s * f t)
    (hlim : Tendsto f (𝓝[>] 0) (𝓝 1)) : f 1 ≠ 0 := by
  intro hf1
  have hev : ∀ᶠ t : ℝ≥0 in 𝓝[>] 0, 1 / 2 < f t :=
    (tendsto_order.1 hlim).1 _ (by norm_num)
  have hulim0 : Tendsto (fun n : ℕ => (n + 1 : ℝ≥0)⁻¹) atTop (𝓝 0) := by
    simpa [one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ≥0))
  have hulim : Tendsto (fun n : ℕ => (n + 1 : ℝ≥0)⁻¹) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨hulim0,
      Eventually.of_forall fun n => by simp only [mem_Ioi]; positivity⟩
  obtain ⟨n, hn⟩ := (hulim.eventually hev).exists
  have hs := mul_nsmul f0 fmul (n + 1) ((n + 1 : ℝ≥0)⁻¹)
  have hnu : (n + 1) • ((n + 1 : ℝ≥0)⁻¹) = (1 : ℝ≥0) := by
    rw [nsmul_eq_mul']
    field_simp
    norm_num
  rw [hnu, hf1] at hs
  have hz : f ((n + 1 : ℝ≥0)⁻¹) = 0 := by
    have : f ((n + 1 : ℝ≥0)⁻¹) ^ (n + 1) = 0 := hs.symm
    simpa using this
  rw [hz] at hn
  norm_num at hn

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
    (fanti : Antitone f) (_hf1le : f 1 ≤ 1) (hlim : Tendsto f (𝓝[>] 0) (𝓝 1))
    (t : ℝ≥0) : f t = Real.exp (-(t : ℝ) * (-Real.log (f 1))) := by
  let c : ℝ := -Real.log (f 1)
  have hf1pos : 0 < f 1 := lt_of_le_of_ne (hf 1) (Ne.symm (one_ne_zero_of_tendsto f0 fmul hlim))
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

variable {Ω M : Type*} [MeasurableSpace Ω] [MeasurableSpace M]
variable {P : Measure Ω} [IsProbabilityMeasure P] {ξ : Ω → Measure (ℝ≥0 × M)} {A : Set M}

lemma prob_noMark_exp_exists (hξ : IsTimeSimpleLevy P ξ) (hA : IsFiniteRate P ξ A) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ t : ℝ≥0, (P {ω | ξ ω (Ioc 0 t ×ˢ A) = 0}).toReal =
      Real.exp (-(t : ℝ) * c) := by
  let f : ℝ≥0 → ℝ := fun t => (P {ω | ξ ω (Ioc 0 t ×ˢ A) = 0}).toReal
  have hf : ∀ t, 0 ≤ f t := fun t => ENNReal.toReal_nonneg
  have f0 : f 0 = 1 := by
    have hset : {ω | ξ ω (Ioc 0 0 ×ˢ A) = 0} = Set.univ := by
      ext ω
      simp
    dsimp [f]
    rw [hset]
    simp
  have fmul : ∀ s t : ℝ≥0, f (s + t) = f s * f t := by
    intro s t
    dsimp [f]
    rw [prob_noMark_mul hξ hA, ENNReal.toReal_mul]
  have fanti : Antitone f := by
    intro s t hst
    apply ENNReal.toReal_mono (measure_ne_top _ _)
    apply measure_mono
    intro ω hω
    change ξ ω (Ioc 0 t ×ˢ A) = 0 at hω
    change ξ ω (Ioc 0 s ×ˢ A) = 0
    rw [count_split _ hA.1 (zero_le : (0 : ℝ≥0) ≤ s) hst] at hω
    exact (add_eq_zero.1 hω).1
  have f1le : f 1 ≤ 1 := by
    rw [← ENNReal.toReal_one]
    exact ENNReal.toReal_mono ENNReal.one_ne_top prob_le_one
  have hlim : Tendsto f (𝓝[>] 0) (𝓝 1) := tendsto_prob_noMark_real_zero hξ hA
  refine ⟨-Real.log (f 1), neg_nonneg.2 (Real.log_nonpos (hf 1) f1le), ?_⟩
  exact eq_exp_of_multiplicative hf f0 fmul fanti f1le hlim

end BGW.Probability
