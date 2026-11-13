module

public import BGWLeaves.LeafConcentration.Defs
import Mathlib.Probability.Moments.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Leaf concentration (M4a): Chernoff-Cramér bounds (Lemma 2.2)

Provider of the frozen statements `lem_phi_i` and `lem_phi_ii` (Lemma 2.2 of arXiv:1110.2163v4)
and of the helper lemmas `chernoff_threshold_trivial` and `phiStar_lower`.

Proof of (i): for `x = p + a ∈ (p, 1)`, the Chernoff bound `measure_ge_le_exp_mul_mgf` with the
optimal tilt `t = log (x (1 - p) / (p (1 - x)))` and the Bernoulli mgf `1 - p + p e^t` gives
`exp (-n φ*(p, x))` (without the factor `2`); the lower tail is the upper tail of `1 - X`.
Proof of (ii): `log (1 + y) = y - y² / 2 + O (y³)` (`Real.abs_log_sub_add_sum_range_le`) gives
`φ*(p + x) = x² / (2 p (1 - p)) + O (x³)`.
-/

@[expose] public section

namespace BGWLeaves.LeafConcentration.Chernoff

open MeasureTheory ProbabilityTheory Filter Asymptotics
open scoped ENNReal Topology

section Bernoulli

variable {Ω : Type*} [MeasurableSpace Ω]

private lemma p_mem {P : Measure Ω} [IsProbabilityMeasure P] {p : ℝ} {Y : Ω → ℝ}
    (h1 : P {ω | Y ω = 1} = ENNReal.ofReal p) (h0 : P {ω | Y ω = 0} = ENNReal.ofReal (1 - p)) :
    0 ≤ p ∧ p ≤ 1 := by
  have a1 : ENNReal.ofReal p ≤ 1 := h1 ▸ prob_le_one
  have a0 : ENNReal.ofReal (1 - p) ≤ 1 := h0 ▸ prob_le_one
  rw [ENNReal.ofReal_le_one] at a1 a0
  constructor <;> linarith

private lemma ae_zero_or_one {P : Measure Ω} [IsProbabilityMeasure P] {p : ℝ} {Y : Ω → ℝ}
    (hY : Measurable Y) (h1 : P {ω | Y ω = 1} = ENNReal.ofReal p)
    (h0 : P {ω | Y ω = 0} = ENNReal.ofReal (1 - p)) : ∀ᵐ ω ∂P, Y ω = 0 ∨ Y ω = 1 := by
  obtain ⟨hp0, hp1⟩ := p_mem h1 h0
  have hdisj : Disjoint {ω | Y ω = 1} {ω | Y ω = 0} := by
    rw [Set.disjoint_left]
    intro ω h h'
    simp only [Set.mem_ofPred_eq] at h h'
    rw [h] at h'
    norm_num at h'
  have hm1 : MeasurableSet {ω | Y ω = 1} := hY (measurableSet_singleton 1)
  have hm0 : MeasurableSet {ω | Y ω = 0} := hY (measurableSet_singleton 0)
  have hunion : P ({ω | Y ω = 1} ∪ {ω | Y ω = 0}) = 1 := by
    rw [measure_union hdisj hm0, h1, h0, ← ENNReal.ofReal_add hp0 (by linarith)]
    simp
  have hnull : P ({ω | Y ω = 1} ∪ {ω | Y ω = 0})ᶜ = 0 :=
    (prob_compl_eq_zero_iff (hm1.union hm0)).2 hunion
  rw [ae_iff]
  refine measure_mono_null ?_ hnull
  intro ω hω
  simp only [Set.mem_ofPred_eq, not_or] at hω
  simp [hω.1, hω.2]

private lemma mgf_bern {P : Measure Ω} [IsProbabilityMeasure P] {p : ℝ} {Y : Ω → ℝ}
    (hY : Measurable Y) (h1 : P {ω | Y ω = 1} = ENNReal.ofReal p)
    (h0 : P {ω | Y ω = 0} = ENNReal.ofReal (1 - p)) (t : ℝ) :
    mgf Y P t = 1 - p + p * Real.exp t := by
  obtain ⟨hp0, hp1⟩ := p_mem h1 h0
  have hae := ae_zero_or_one hY h1 h0
  have hm1 : MeasurableSet {ω | Y ω = 1} := hY (measurableSet_singleton 1)
  have hm0 : MeasurableSet {ω | Y ω = 0} := hY (measurableSet_singleton 0)
  have hcongr : (fun ω => Real.exp (t * Y ω)) =ᵐ[P]
      fun ω => {ω | Y ω = 1}.indicator (fun _ => Real.exp t) ω +
        {ω | Y ω = 0}.indicator (fun _ => (1 : ℝ)) ω := by
    filter_upwards [hae] with ω hω
    rcases hω with h | h <;> simp [h]
  unfold mgf
  rw [integral_congr_ae hcongr,
    integral_add ((integrable_const _).indicator hm1) ((integrable_const _).indicator hm0),
    integral_indicator_const _ hm1, integral_indicator_const _ hm0, measureReal_def,
    measureReal_def, h1, h0, ENNReal.toReal_ofReal hp0, ENNReal.toReal_ofReal (by linarith)]
  simp only [smul_eq_mul]
  ring

private lemma ae_all_zero_or_one {P : Measure Ω} [IsProbabilityMeasure P] {p : ℝ}
    {X : ℕ → Ω → ℝ} (hX : ∀ i, Measurable (X i))
    (hber : ∀ i, P {ω | X i ω = 1} = ENNReal.ofReal p ∧ P {ω | X i ω = 0} = ENNReal.ofReal (1 - p)) :
    ∀ᵐ ω ∂P, ∀ k, X k ω = 0 ∨ X k ω = 1 :=
  ae_all_iff.2 fun k => ae_zero_or_one (hX k) (hber k).1 (hber k).2

omit [MeasurableSpace Ω] in
private lemma sum_bounds {X : ℕ → Ω → ℝ} {ω : Ω} (h : ∀ k, X k ω = 0 ∨ X k ω = 1) (n : ℕ) :
    0 ≤ ∑ k ∈ Finset.range n, X k ω ∧ ∑ k ∈ Finset.range n, X k ω ≤ n := by
  constructor
  · exact Finset.sum_nonneg fun k _ => by rcases h k with h | h <;> simp [h]
  · calc ∑ k ∈ Finset.range n, X k ω ≤ ∑ _k ∈ Finset.range n, (1 : ℝ) :=
          Finset.sum_le_sum fun k _ => by rcases h k with h | h <;> simp [h]
      _ = n := by simp

/-- The thresholds outside `[0,1]` are trivial events: the empirical mean of a Bernoulli family
lies in `[0,1]`, so `{avg > p + a}` is null as soon as `p + a ≥ 1` and `{avg < p - a}` as soon as
`a ≥ p` (so the junk values of `phiStar` outside `[0,1]` are irrelevant in `lem_phi_i`). -/
theorem chernoff_threshold_trivial {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {p : ℝ} (X : ℕ → Ω → ℝ) (hX : ∀ i, Measurable (X i))
    (hber : ∀ i, P {ω | X i ω = 1} = ENNReal.ofReal p ∧ P {ω | X i ω = 0} = ENNReal.ofReal (1 - p))
    {a : ℝ} {n : ℕ} (hn : 1 ≤ n) :
    (1 ≤ p + a → P.real {ω | p + a < (∑ k ∈ Finset.range n, X k ω) / n} = 0) ∧
      (a ≥ p → P.real {ω | (∑ k ∈ Finset.range n, X k ω) / n < p - a} = 0) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hnull := ae_iff.1 (ae_all_zero_or_one hX hber)
  constructor
  · intro h
    rw [measureReal_def, measure_mono_null (t := {ω | ¬ ∀ k, X k ω = 0 ∨ X k ω = 1}) _ hnull]
    · simp
    · intro ω hω
      simp only [Set.mem_ofPred_eq] at hω ⊢
      intro hall
      have := (sum_bounds hall n).2
      rw [lt_div_iff₀ hn'] at hω
      nlinarith
  · intro h
    rw [measureReal_def, measure_mono_null (t := {ω | ¬ ∀ k, X k ω = 0 ∨ X k ω = 1}) _ hnull]
    · simp
    · intro ω hω
      simp only [Set.mem_ofPred_eq] at hω ⊢
      intro hall
      have := (sum_bounds hall n).1
      have h2 : 0 ≤ (∑ k ∈ Finset.range n, X k ω) / n := div_nonneg this hn'.le
      linarith

/-- The upper tail with the sharp exponent, for thresholds `x ∈ (p, 1)`. -/
private lemma upper_tail {P : Measure Ω} [IsProbabilityMeasure P] {p : ℝ} (hp0 : 0 < p)
    (hp1 : p < 1) {X : ℕ → Ω → ℝ} (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X P)
    (hber : ∀ i, P {ω | X i ω = 1} = ENNReal.ofReal p ∧ P {ω | X i ω = 0} = ENNReal.ofReal (1 - p))
    {x : ℝ} (hx : p < x) (hx1 : x < 1) {n : ℕ} (hn : 1 ≤ n) :
    P.real {ω | x < (∑ k ∈ Finset.range n, X k ω) / n} ≤ Real.exp (-(n * phiStar p x)) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h1p : 0 < 1 - p := by linarith
  have h1x : 0 < 1 - x := by linarith
  have hx0 : 0 < x := by linarith
  have hqpos : 0 < x * (1 - p) / (p * (1 - x)) := by positivity
  set t := Real.log (x * (1 - p) / (p * (1 - x))) with ht
  have hq : 1 ≤ x * (1 - p) / (p * (1 - x)) := by
    rw [le_div_iff₀ (by positivity)]; nlinarith
  have ht0 : 0 ≤ t := Real.log_nonneg hq
  have het : Real.exp t = x * (1 - p) / (p * (1 - x)) := Real.exp_log hqpos
  have hae := ae_all_zero_or_one hX hber
  have hint : Integrable (fun ω => Real.exp (t * (∑ i ∈ Finset.range n, X i) ω)) P := by
    refine Integrable.of_bound (C := Real.exp (t * n)) ?_ ?_
    · have hm : Measurable (fun ω => (∑ i ∈ Finset.range n, X i) ω) := by
        simpa only [Finset.sum_apply] using Finset.measurable_sum _ fun i _ => hX i
      exact ((hm.const_mul t).exp).aestronglyMeasurable
    · filter_upwards [hae] with ω hω
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      apply Real.exp_le_exp.2
      rw [Finset.sum_apply]
      exact mul_le_mul_of_nonneg_left (sum_bounds hω n).2 ht0
  have hmgf : mgf (∑ i ∈ Finset.range n, X i) P t = (1 - p + p * Real.exp t) ^ n := by
    rw [hind.mgf_sum hX, Finset.prod_congr rfl
      (fun i _ => mgf_bern (hX i) (hber i).1 (hber i).2 t)]
    simp
  have hbase : 1 - p + p * Real.exp t = (1 - p) / (1 - x) := by
    rw [het]; field_simp; ring
  have hsub : {ω | x < (∑ k ∈ Finset.range n, X k ω) / n} ⊆
      {ω | (n : ℝ) * x ≤ (∑ i ∈ Finset.range n, X i) ω} := by
    intro ω hω
    simp only [Set.mem_ofPred_eq, Finset.sum_apply] at hω ⊢
    rw [lt_div_iff₀ hn'] at hω
    linarith
  -- the exponent
  set a := Real.log (x / p) with ha
  set b := Real.log ((1 - x) / (1 - p)) with hb
  have hta : t = a - b := by
    rw [ht, ha, hb, ← Real.log_div (by positivity) (by positivity)]
    congr 1; field_simp
  have hexp : (1 - p) / (1 - x) = Real.exp (-b) := by
    rw [Real.exp_neg, hb, Real.exp_log (by positivity), inv_div]
  calc P.real {ω | x < (∑ k ∈ Finset.range n, X k ω) / n}
      ≤ P.real {ω | (n : ℝ) * x ≤ (∑ i ∈ Finset.range n, X i) ω} :=
        measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ Real.exp (-t * (n * x)) * mgf (∑ i ∈ Finset.range n, X i) P t :=
        measure_ge_le_exp_mul_mgf _ ht0 hint
    _ = Real.exp (-(n * phiStar p x)) := by
      rw [hmgf, hbase, hexp, ← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      unfold phiStar
      rw [hta]
      ring

private lemma upper_tail_all {P : Measure Ω} [IsProbabilityMeasure P] {p : ℝ} (hp0 : 0 < p)
    (hp1 : p < 1) {X : ℕ → Ω → ℝ} (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X P)
    (hber : ∀ i, P {ω | X i ω = 1} = ENNReal.ofReal p ∧ P {ω | X i ω = 0} = ENNReal.ofReal (1 - p))
    {a : ℝ} (ha : 0 < a) {n : ℕ} (hn : 1 ≤ n) :
    P.real {ω | p + a < (∑ k ∈ Finset.range n, X k ω) / n} ≤
      2 * Real.exp (-(n * phiStar p (p + a))) := by
  by_cases h : 1 ≤ p + a
  · rw [(chernoff_threshold_trivial P X hX hber hn).1 h]
    positivity
  · push Not at h
    have := upper_tail hp0 hp1 hX hind hber (by linarith : p < p + a) h hn
    have hpos := Real.exp_pos (-(n * phiStar p (p + a)))
    linarith

/-- **Lemma 2.2(i) (`lem:phi`)**: Chernoff-Cramér bounds, both tails, for `n` iid Bernoulli(`p`)
variables `X_0, …, X_{n-1}` on an arbitrary probability space `(Ω, P)`, `0 < p < 1` (the paper's
`p = μ₀`).  The sums are indexed by `Finset.range n` (the paper's `X_1, …, X_n` shifted to start at
`0`, so that `X i ω = 1{ω i = 0}` applies to the walk directly).  For every `a > 0` and `n ≥ 1`
(arbitrary, no restriction to `[0,1]`):
`P[(1/n) ∑ X_k > p + a] ≤ 2 exp(-n φ*(p + a))` and `P[(1/n) ∑ X_k < p - a] ≤ 2 exp(-n φ*(p - a))`.
When `p + a ≥ 1` (resp. `a ≥ p`) the event is null (the empirical mean lies in `[0,1]` almost
surely), so the bound is trivial, and the junk values of `phiStar` outside `[0,1]` play no role.
The factor `2` is the printed one. -/
theorem lem_phi_i {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (X : ℕ → Ω → ℝ) (hX : ∀ i, Measurable (X i))
    (hind : iIndepFun X P)
    (hber : ∀ i, P {ω | X i ω = 1} = ENNReal.ofReal p ∧ P {ω | X i ω = 0} = ENNReal.ofReal (1 - p))
    {a : ℝ} (ha : 0 < a) {n : ℕ} (hn : 1 ≤ n) :
    P.real {ω | p + a < (∑ k ∈ Finset.range n, X k ω) / n} ≤
        2 * Real.exp (-(n * phiStar p (p + a))) ∧
      P.real {ω | (∑ k ∈ Finset.range n, X k ω) / n < p - a} ≤
        2 * Real.exp (-(n * phiStar p (p - a))) := by
  refine ⟨upper_tail_all hp0 hp1 hX hind hber ha hn, ?_⟩
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  -- the lower tail is the upper tail of `1 - X`
  have hX' : ∀ i, Measurable (fun ω => 1 - X i ω) := fun i => measurable_const.sub (hX i)
  have hind' : iIndepFun (fun i ω => 1 - X i ω) P :=
    hind.comp (fun _ y => 1 - y) (fun _ => measurable_const.sub measurable_id)
  have hber' : ∀ i, P {ω | 1 - X i ω = 1} = ENNReal.ofReal (1 - p) ∧
      P {ω | 1 - X i ω = 0} = ENNReal.ofReal (1 - (1 - p)) := by
    intro i
    refine ⟨?_, ?_⟩
    · rw [← (hber i).2]
      congr 1; ext ω; simp only [Set.mem_ofPred_eq]; constructor <;> intro h <;> linarith
    · rw [sub_sub_cancel, ← (hber i).1]
      congr 1; ext ω; simp only [Set.mem_ofPred_eq]; constructor <;> intro h <;> linarith
  have h := upper_tail_all (by linarith : 0 < 1 - p) (by linarith : 1 - p < 1) hX' hind' hber' ha hn
  have hset : {ω | (∑ k ∈ Finset.range n, X k ω) / n < p - a} =
      {ω | 1 - p + a < (∑ k ∈ Finset.range n, (1 - X k ω)) / n} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul, mul_one]
    rw [div_lt_iff₀ hn', lt_div_iff₀ hn']
    constructor <;> intro h <;> nlinarith
  have hphi : phiStar (1 - p) (1 - p + a) = phiStar p (p - a) := by
    unfold phiStar
    rw [show 1 - (1 - p + a) = p - a by ring, show 1 - (1 - p) = p by ring,
      show 1 - (p - a) = 1 - p + a by ring]
    ring
  rw [hset]
  rwa [hphi] at h

end Bernoulli

/-! ## Lemma 2.2(ii): expansion of the rate function -/

private lemma log_one_add_bound {y : ℝ} (hy : |y| ≤ 1 / 2) :
    |Real.log (1 + y) - (y - y ^ 2 / 2)| ≤ 2 * |y| ^ 3 := by
  have h := Real.abs_log_sub_add_sum_range_le (x := -y) (by rw [abs_neg]; linarith) 2
  have e : (∑ i ∈ Finset.range 2, (-y) ^ (i + 1) / ((i : ℝ) + 1)) + Real.log (1 - -y) =
      Real.log (1 + y) - (y - y ^ 2 / 2) := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    norm_num
    ring
  rw [e] at h
  simp only [abs_neg] at h
  refine h.trans ?_
  rw [div_le_iff₀ (by linarith), show (2 + 1 : ℕ) = 3 by norm_num]
  nlinarith [mul_nonneg (pow_nonneg (abs_nonneg y) 3) (by linarith : (0 : ℝ) ≤ 1 / 2 - |y|)]

private lemma phiStar_cubic {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    ∃ K : ℝ, ∀ x : ℝ, |x| ≤ min p (1 - p) / 2 →
      |phiStar p (p + x) - x ^ 2 / (2 * p * (1 - p))| ≤ K * |x| ^ 3 := by
  have h1p : 0 < 1 - p := by linarith
  set D : ℝ := 1 / (2 * (1 - p) ^ 2) - 1 / (2 * p ^ 2) with hD
  refine ⟨|D| + 2 / p ^ 3 + 2 / (1 - p) ^ 3, fun x hx => ?_⟩
  have hxp : |x| ≤ p / 2 := hx.trans (by have := min_le_left p (1 - p); linarith)
  have hxq : |x| ≤ (1 - p) / 2 := hx.trans (by have := min_le_right p (1 - p); linarith)
  have hx1 := abs_le.1 hxp
  have hx2 := abs_le.1 hxq
  have hu : |x / p| ≤ 1 / 2 := by
    rw [abs_div, abs_of_pos hp0, div_le_iff₀ hp0]; linarith
  have hw : |-x / (1 - p)| ≤ 1 / 2 := by
    rw [abs_div, abs_neg, abs_of_pos h1p, div_le_iff₀ h1p]; linarith
  have b1 := log_one_add_bound hu
  have b2 := log_one_add_bound hw
  set R1 := Real.log (1 + x / p) - (x / p - (x / p) ^ 2 / 2) with hR1
  set R2 := Real.log (1 + -x / (1 - p)) - (-x / (1 - p) - (-x / (1 - p)) ^ 2 / 2) with hR2
  have e1 : (p + x) / p = 1 + x / p := by field_simp
  have e2 : (1 - (p + x)) / (1 - p) = 1 + -x / (1 - p) := by field_simp; ring
  have hE : phiStar p (p + x) - x ^ 2 / (2 * p * (1 - p)) =
      x ^ 3 * D + (p + x) * R1 + (1 - (p + x)) * R2 := by
    unfold phiStar
    rw [e1, e2]
    have l1 : Real.log (1 + x / p) = R1 + (x / p - (x / p) ^ 2 / 2) := by rw [hR1]; ring
    have l2 : Real.log (1 + -x / (1 - p)) =
        R2 + (-x / (1 - p) - (-x / (1 - p)) ^ 2 / 2) := by rw [hR2]; ring
    rw [l1, l2, hD]
    field_simp
    ring
  have hpx : |p + x| ≤ 1 := by rw [abs_le]; constructor <;> linarith
  have hpx' : |1 - (p + x)| ≤ 1 := by rw [abs_le]; constructor <;> linarith
  have hu3 : |x / p| ^ 3 = |x| ^ 3 / p ^ 3 := by
    rw [abs_div, abs_of_pos hp0, div_pow]
  have hw3 : |-x / (1 - p)| ^ 3 = |x| ^ 3 / (1 - p) ^ 3 := by
    rw [abs_div, abs_neg, abs_of_pos h1p, div_pow]
  have c1 : |(p + x) * R1| ≤ 2 * (|x| ^ 3 / p ^ 3) := by
    rw [abs_mul]
    calc |p + x| * |R1| ≤ 1 * (2 * |x / p| ^ 3) :=
          mul_le_mul hpx b1 (abs_nonneg _) zero_le_one
      _ = _ := by rw [hu3]; ring
  have c2 : |(1 - (p + x)) * R2| ≤ 2 * (|x| ^ 3 / (1 - p) ^ 3) := by
    rw [abs_mul]
    calc |1 - (p + x)| * |R2| ≤ 1 * (2 * |-x / (1 - p)| ^ 3) :=
          mul_le_mul hpx' b2 (abs_nonneg _) zero_le_one
      _ = _ := by rw [hw3]; ring
  have c0 : |x ^ 3 * D| = |x| ^ 3 * |D| := by rw [abs_mul, abs_pow]
  rw [hE]
  calc |x ^ 3 * D + (p + x) * R1 + (1 - (p + x)) * R2|
      ≤ |x ^ 3 * D| + |(p + x) * R1| + |(1 - (p + x)) * R2| := abs_add_three _ _ _
    _ ≤ |x| ^ 3 * |D| + 2 * (|x| ^ 3 / p ^ 3) + 2 * (|x| ^ 3 / (1 - p) ^ 3) := by
        rw [c0]; linarith
    _ = _ := by ring

/-- **Lemma 2.2(ii) (`lem:phi`)**: `φ*(p + x) = x² / (2 p (1 - p)) + o(x²)` as `x → 0`, for
`0 < p < 1`, stated as `φ*(p + x) - x²/(2p(1-p)) = o(x²)` along `𝓝 0`. -/
theorem lem_phi_ii {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    (fun x : ℝ => phiStar p (p + x) - x ^ 2 / (2 * p * (1 - p))) =o[𝓝 0] fun x : ℝ => x ^ 2 := by
  obtain ⟨K, hK⟩ := phiStar_cubic hp0 hp1
  have hr : 0 < min p (1 - p) / 2 := by
    have : 0 < min p (1 - p) := lt_min hp0 (by linarith)
    linarith
  refine Asymptotics.IsLittleO.of_bound fun c hc => ?_
  have hcK : 0 < c / (|K| + 1) := div_pos hc (by positivity)
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (lt_min hr hcK)] with x hx
  rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hx
  have hx1 : |x| < min p (1 - p) / 2 := hx.trans_le (min_le_left _ _)
  have hx2 : |x| < c / (|K| + 1) := hx.trans_le (min_le_right _ _)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_pow]
  have h := hK x hx1.le
  have hKx : |K| * |x| ≤ c := by
    rw [lt_div_iff₀ (by positivity)] at hx2
    nlinarith [abs_nonneg x, abs_nonneg K]
  calc |phiStar p (p + x) - x ^ 2 / (2 * p * (1 - p))| ≤ K * |x| ^ 3 := h
    _ ≤ |K| * |x| ^ 3 := mul_le_mul_of_nonneg_right (le_abs_self K) (by positivity)
    _ = (|K| * |x|) * |x| ^ 2 := by ring
    _ ≤ c * |x| ^ 2 := mul_le_mul_of_nonneg_right hKx (by positivity)

private lemma phiStar_quad_lower {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ x : ℝ, |x| < ρ → x ^ 2 / (4 * p * (1 - p)) ≤ phiStar p (p + x) := by
  have h1p : 0 < 1 - p := by linarith
  have h := (lem_phi_ii hp0 hp1).def (c := 1 / (4 * p * (1 - p))) (by positivity)
  obtain ⟨ρ, hρ, hball⟩ := Metric.eventually_nhds_iff.1 h
  refine ⟨ρ, hρ, fun x hx => ?_⟩
  have h2 := hball (y := x) (by rwa [Real.dist_eq, sub_zero])
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_pow, sq_abs, abs_le] at h2
  have e : x ^ 2 / (2 * p * (1 - p)) - x ^ 2 / (4 * p * (1 - p)) =
      1 / (4 * p * (1 - p)) * x ^ 2 := by field_simp; ring
  have := h2.1
  linarith

/-- Consequence of 2.2(ii) used in the proofs of 2.5 and 2.7: for fixed `δ > 0` there are `c > 0` and
`N` such that `φ*(p ± δ n^{-1/4}) > c n^{-1/2}` for `n ≥ N`. -/
theorem phiStar_lower {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) {δ : ℝ} (hδ : 0 < δ) :
    ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      c / (n : ℝ) ^ (1 / 2 : ℝ) < phiStar p (p + δ / (n : ℝ) ^ (1 / 4 : ℝ)) ∧
        c / (n : ℝ) ^ (1 / 2 : ℝ) < phiStar p (p - δ / (n : ℝ) ^ (1 / 4 : ℝ)) := by
  have h1p : 0 < 1 - p := by linarith
  obtain ⟨ρ, hρ, hq⟩ := phiStar_quad_lower hp0 hp1
  have htend : Tendsto (fun n : ℕ => δ / (n : ℝ) ^ (1 / 4 : ℝ)) atTop (𝓝 0) :=
    Tendsto.div_atTop tendsto_const_nhds
      ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)).comp tendsto_natCast_atTop_atTop)
  have hev := (htend.eventually (Metric.ball_mem_nhds (0 : ℝ) hρ))
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hev.and (eventually_ge_atTop 1))
  refine ⟨δ ^ 2 / (8 * p * (1 - p)), by positivity, N, fun n hn => ?_⟩
  obtain ⟨hb, hn1⟩ := hN n hn
  rw [Real.dist_eq, sub_zero] at hb
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  set s := δ / (n : ℝ) ^ (1 / 4 : ℝ) with hs
  have hs2 : s ^ 2 = δ ^ 2 / (n : ℝ) ^ (1 / 2 : ℝ) := by
    have : ((n : ℝ) ^ (1 / 4 : ℝ)) ^ 2 = (n : ℝ) ^ (1 / 2 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hn0.le]
      norm_num
    rw [hs, div_pow, this]
  have hpos : 0 < (n : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hn0 _
  have key : δ ^ 2 / (8 * p * (1 - p)) / (n : ℝ) ^ (1 / 2 : ℝ) < s ^ 2 / (4 * p * (1 - p)) := by
    rw [hs2]
    have : 0 < δ ^ 2 / (n : ℝ) ^ (1 / 2 : ℝ) / (8 * p * (1 - p)) := by positivity
    have e1 : δ ^ 2 / (8 * p * (1 - p)) / (n : ℝ) ^ (1 / 2 : ℝ) =
        δ ^ 2 / (n : ℝ) ^ (1 / 2 : ℝ) / (8 * p * (1 - p)) := by field_simp
    have e2 : δ ^ 2 / (n : ℝ) ^ (1 / 2 : ℝ) / (4 * p * (1 - p)) =
        2 * (δ ^ 2 / (n : ℝ) ^ (1 / 2 : ℝ) / (8 * p * (1 - p))) := by field_simp; ring
    rw [e1, e2]; linarith
  refine ⟨key.trans_le (hq s hb), ?_⟩
  have := hq (-s) (by rwa [abs_neg])
  rw [← sub_eq_add_neg] at this
  exact key.trans_le (by simpa using this)

end BGWLeaves.LeafConcentration.Chernoff
