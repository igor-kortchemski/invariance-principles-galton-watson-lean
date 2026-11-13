module

public import BGWLeaves.Vervaat.Defs
import BGWLeaves.LeafConcentration.WalkDeviation
import Mathlib.Probability.Independence.InfinitePi

/-!
# Concentration of the mark times (6.2(i))

Proofs of the concentration of the mark times (6.2(i)).  The theorems are those stated in
`BGWLeaves.Vervaat`; they are exported in namespace `BGWLeaves.Vervaat.MarkTime` with exactly the types
stated there.

Proof of `lem_CVf2_i`: `{T_n > a} ⊆ {Λ(⌊a⌋) < n}`, `{T_n < b} ⊆ {n ≤ Λ(⌈b⌉ - 1)}` for
`a, b = n/μ₀ ± n^{3/4}` (this includes `T_n = ∞`), then the Chernoff bound `lem_phi_i` at the
scales `⌊a⌋` and `⌈b⌉ - 1` (both `≍ n/μ₀`) with the deviation `μ₀² n^{-1/4} / 4` and `phiStar_lower`.
(The printed citation of Lemma 2.5(i) is incomplete: its window is times `≤ n`, while `T_n ≈ n/μ₀`.)
-/

@[expose] public section

namespace BGWLeaves.Vervaat.MarkTime

open MeasureTheory ProbabilityTheory Filter BGW
open BGW.StableTrees BGW.LocallyFinite BGWLeaves.StableAnalysis
open scoped ENNReal Topology

/-! ## Counter and mark times -/

private theorem walkLeafCount_succ (ω : ℕ → ℕ) (n : ℕ) :
    walkLeafCount ω (n + 1) = walkLeafCount ω n + if ω n = 0 then 1 else 0 := by
  unfold walkLeafCount
  rw [Finset.card_filter, Finset.card_filter, Finset.sum_range_succ]
  by_cases h : ω n = 0 <;> simp [h]

private theorem walkLeafCount_mono (ω : ℕ → ℕ) {q k : ℕ} (h : q ≤ k) :
    walkLeafCount ω q ≤ walkLeafCount ω k := by
  unfold walkLeafCount
  exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.range_mono h))

private theorem walkLeafCount_zero (ω : ℕ → ℕ) : walkLeafCount ω 0 = 0 := by
  simp [walkLeafCount]

private theorem walkLeafCount_le (ω : ℕ → ℕ) (k : ℕ) : walkLeafCount ω k ≤ k := by
  unfold walkLeafCount
  exact (Finset.card_filter_le _ _).trans (by simp)

/-- If `n ≤ Λ(K)` the mark time `T_n` exists and is `≤ K`. -/
private theorem exists_markTime_of_le {n K : ℕ} {ω : ℕ → ℕ} (h : n ≤ walkLeafCount ω K) :
    ∃ k, k ≤ K ∧ IsMarkTime n ω k := by
  classical
  have hex : ∃ k, n ≤ walkLeafCount ω k := ⟨K, h⟩
  refine ⟨Nat.find hex, Nat.find_min' hex h, ?_⟩
  have hm := Nat.find_spec hex
  rcases hk : Nat.find hex with _ | m
  · rw [hk] at hm
    have h0 : n = 0 := by rw [walkLeafCount_zero] at hm; omega
    refine ⟨by rw [walkLeafCount_zero, h0], fun q hq => absurd hq (Nat.not_lt_zero _)⟩
  · have hlt : walkLeafCount ω m < n := by
      have := Nat.find_min hex (show m < Nat.find hex by omega)
      omega
    have hs := walkLeafCount_succ ω m
    have h1 : walkLeafCount ω (m + 1) = n := by
      rw [hk] at hm
      split_ifs at hs <;> omega
    refine ⟨h1, fun q hq => ?_⟩
    have := walkLeafCount_mono ω (show q ≤ m by omega)
    omega

theorem exists_isMarkTime_iff (n : ℕ) (ω : ℕ → ℕ) :
    (∃ k, IsMarkTime n ω k) ↔ ∃ k, walkLeafCount ω k = n := by
  constructor
  · rintro ⟨k, hk, -⟩
    exact ⟨k, hk⟩
  · rintro ⟨k, hk⟩
    obtain ⟨k', -, hk'⟩ := exists_markTime_of_le (n := n) (K := k) (ω := ω) hk.ge
    exact ⟨k', hk'⟩

theorem IsMarkTime.unique {n : ℕ} {ω : ℕ → ℕ} {k k' : ℕ} (h : IsMarkTime n ω k)
    (h' : IsMarkTime n ω k') : k = k' := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have h1 := h'.2 k hlt
    have h2 := h.1
    omega
  · have h1 := h.2 k' hlt
    have h2 := h'.1
    omega

/-! ## Bernoulli tails of the leaf counter -/

private def zeroIndicator (m : ℕ) : ℝ := if m = 0 then 1 else 0

private theorem zeroIndicator_sum (ω : ℕ → ℕ) (k : ℕ) :
    ∑ i ∈ Finset.range k, zeroIndicator (ω i) = (walkLeafCount ω k : ℝ) := by
  unfold walkLeafCount
  rw [Finset.card_filter, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : ω i = 0 <;> simp [zeroIndicator, h]

private theorem zeroIndicator_bernoulli (μ : PMF ℕ) (i : ℕ) :
    (Measure.infinitePi fun _ : ℕ => μ.toMeasure) {ω | zeroIndicator (ω i) = 1} =
        ENNReal.ofReal (μ 0).toReal ∧
      (Measure.infinitePi fun _ : ℕ => μ.toMeasure) {ω | zeroIndicator (ω i) = 0} =
        ENNReal.ofReal (1 - (μ 0).toReal) := by
  have h : (Measure.infinitePi fun _ : ℕ => μ.toMeasure) {ω | ω i = 0} = μ 0 := by
    rw [← PMF.toMeasure_apply_singleton μ 0 (measurableSet_singleton (0 : ℕ))]
    convert (measurePreserving_eval_infinitePi (fun _ : ℕ => μ.toMeasure) i).measure_preimage
      (measurableSet_singleton (0 : ℕ)).nullMeasurableSet using 1
    congr 1
  have hset1 : {ω : ℕ → ℕ | zeroIndicator (ω i) = 1} = {ω | ω i = 0} := by
    ext ω; simp [zeroIndicator]
  have hset0 : {ω : ℕ → ℕ | zeroIndicator (ω i) = 0} = {ω | ω i = 0}ᶜ := by
    ext ω; simp [zeroIndicator]
  rw [hset1, hset0, h, measure_compl (by measurability) (by finiteness), measure_univ, h]
  simp [ENNReal.ofReal_sub, ENNReal.ofReal_toReal, PMF.apply_ne_top]

/-- Both Chernoff tails of the leaf counter `Λ(K)`. -/
private theorem counter_tails (μ : PMF ℕ) {p : ℝ} (hp : (μ 0).toReal = p)
    (hp0 : 0 < p) (hp1 : p < 1)
    {a : ℝ} (ha : 0 < a) {K : ℕ} (hK : 1 ≤ K) :
    (Measure.infinitePi fun _ : ℕ => μ.toMeasure).real
        {ω | p + a < (walkLeafCount ω K : ℝ) / K} ≤
        2 * Real.exp (-(K * phiStar p (p + a))) ∧
      (Measure.infinitePi fun _ : ℕ => μ.toMeasure).real
        {ω | (walkLeafCount ω K : ℝ) / K < p - a} ≤
        2 * Real.exp (-(K * phiStar p (p - a))) := by
  subst hp
  have hX : ∀ i : ℕ, Measurable (fun ω : ℕ → ℕ => zeroIndicator (ω i)) :=
    fun i => (measurable_of_countable zeroIndicator).comp (measurable_pi_apply i)
  have hind : iIndepFun (fun i (ω : ℕ → ℕ) => zeroIndicator (ω i))
      (Measure.infinitePi fun _ : ℕ => μ.toMeasure) :=
    iIndepFun_infinitePi (fun _ => measurable_of_countable zeroIndicator)
  obtain ⟨hu, hl⟩ := LeafConcentration.Chernoff.lem_phi_i _ hp0 hp1 _ hX hind
    (zeroIndicator_bernoulli μ) ha hK
  simp only [zeroIndicator_sum] at hu hl
  exact ⟨hu, hl⟩

/-! ## Lemma 6.2(i): real algebra -/

private theorem alg_one {p s a0 : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hs : 4 ≤ s)
    (ha0 : a0 = p ^ 2 / 4 / s) : s ^ 4 ≤ (s ^ 4 / p + s ^ 3 - 1) * (p - a0) := by
  have hspos : 0 < s := by linarith
  have ha0pos : 0 < a0 := by rw [ha0]; positivity
  have hsp : s ^ 4 / p * a0 = p * s ^ 3 / 4 := by rw [ha0]; field_simp
  have hs3a : s ^ 3 * a0 = p ^ 2 * s ^ 2 / 4 := by rw [ha0]; field_simp
  have e : (s ^ 4 / p + s ^ 3 - 1) * (p - a0) =
      s ^ 4 + p * s ^ 3 - p - s ^ 4 / p * a0 - s ^ 3 * a0 + a0 := by
    field_simp; ring
  rw [e, hsp, hs3a]
  have hp2 : p ^ 2 ≤ p := by nlinarith
  have h2 : p ^ 2 * s ^ 2 ≤ p * s ^ 2 := mul_le_mul_of_nonneg_right hp2 (sq_nonneg s)
  have h3 : s ^ 2 ≤ s ^ 3 := by nlinarith [sq_nonneg s]
  have h4 : 0 < p * s ^ 3 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left h3 hp0.le]

private theorem alg_two {p s a0 : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hs : 4 ≤ s)
    (ha0 : a0 = p ^ 2 / 4 / s) : (s ^ 4 / p - s ^ 3) * (p + a0) ≤ s ^ 4 := by
  have hspos : 0 < s := by linarith
  have hsp : s ^ 4 / p * a0 = p * s ^ 3 / 4 := by rw [ha0]; field_simp
  have hs3a : s ^ 3 * a0 = p ^ 2 * s ^ 2 / 4 := by rw [ha0]; field_simp
  have e : (s ^ 4 / p - s ^ 3) * (p + a0) =
      s ^ 4 - p * s ^ 3 + s ^ 4 / p * a0 - s ^ 3 * a0 := by
    field_simp; ring
  rw [e, hsp, hs3a]
  have h4 : 0 < p * s ^ 3 := by positivity
  have h5 : 0 < p ^ 2 * s ^ 2 := by positivity
  nlinarith

private theorem alg_three {p s : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hs : 4 ≤ s) :
    2 * s ^ 3 + 2 ≤ s ^ 4 / p := by
  have hspos : 0 < s := by linarith
  rw [le_div_iff₀ hp0]
  have h3 : 1 ≤ s ^ 3 := one_le_pow₀ (by linarith)
  have h4 : 4 * s ^ 3 ≤ s ^ 4 := by nlinarith [pow_pos hspos 3]
  nlinarith [mul_pos hp0 (pow_pos hspos 3)]

/-! ## Lemma 6.2(i): the two tails at the scales `⌊a⌋` and `⌈b⌉ - 1` -/

private theorem piece_upper (μ : PMF ℕ) {p : ℝ} (hp : (μ 0).toReal = p) (hp0 : 0 < p)
    (hp1 : p < 1) {s : ℝ} {n : ℕ} (hs : 4 ≤ s) (hs4 : s ^ 4 = n) {c : ℝ} (hc : 0 < c)
    (hphi : c / s ^ 2 < phiStar p (p - p ^ 2 / 4 / s)) :
    (Measure.infinitePi fun _ : ℕ => μ.toMeasure).real
        {ω | walkLeafCount ω ⌊(n : ℝ) / p + s ^ 3⌋₊ < n} ≤
      2 * Real.exp (-(c / (2 * p) * s ^ 2)) := by
  have hspos : 0 < s := by linarith
  have hnp : (n : ℝ) / p = s ^ 4 / p := by rw [← hs4]
  have hn3 : (0 : ℝ) ≤ (n : ℝ) / p + s ^ 3 := by positivity
  have h3 : 1 ≤ s ^ 3 := one_le_pow₀ (by linarith)
  have hnn : (n : ℝ) ≤ (n : ℝ) / p := by
    rw [le_div_iff₀ hp0]; nlinarith [(by rw [← hs4]; positivity : (0 : ℝ) ≤ n)]
  have hK1lt : (n : ℝ) / p + s ^ 3 - 1 < (⌊(n : ℝ) / p + s ^ 3⌋₊ : ℕ) := by
    have := Nat.lt_floor_add_one ((n : ℝ) / p + s ^ 3)
    linarith
  have hKge : (n : ℝ) / p ≤ (⌊(n : ℝ) / p + s ^ 3⌋₊ : ℕ) := by linarith
  have hn1 : (1 : ℝ) < (n : ℝ) / p := by
    have : (256 : ℝ) ≤ n := by rw [← hs4]; nlinarith [pow_pos hspos 2]
    linarith
  generalize hK : ⌊(n : ℝ) / p + s ^ 3⌋₊ = K at hK1lt hKge
  have hKpos : 1 ≤ K := by
    have : (1 : ℝ) < K := lt_of_lt_of_le hn1 hKge
    exact_mod_cast this.le
  set a0 : ℝ := p ^ 2 / 4 / s with ha0
  have ha0pos : 0 < a0 := by positivity
  have ha0le : a0 ≤ p / 4 := by
    rw [ha0, div_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [sq_nonneg p, mul_pos hp0 hspos]
  have hpa : 0 < p - a0 := by linarith
  have hKr : (0 : ℝ) < K := by exact_mod_cast hKpos
  have key : (n : ℝ) ≤ K * (p - a0) := by
    have h1 : ((n : ℝ) / p + s ^ 3 - 1) * (p - a0) ≤ K * (p - a0) :=
      mul_le_mul_of_nonneg_right hK1lt.le hpa.le
    have h2 := alg_one hp0 hp1 hs ha0
    rw [← hnp, hs4] at h2
    linarith
  have hE : {ω | walkLeafCount ω K < n} ⊆
      {ω | (walkLeafCount ω K : ℝ) / K < p - a0} := by
    intro ω hω
    have hlt : (walkLeafCount ω K : ℝ) < n := by exact_mod_cast (show walkLeafCount ω K < n from hω)
    show (walkLeafCount ω K : ℝ) / K < p - a0
    rw [div_lt_iff₀ hKr]
    linarith
  obtain ⟨-, hlow⟩ := counter_tails μ hp hp0 hp1 ha0pos hKpos
  refine (measureReal_mono hE).trans (hlow.trans ?_)
  have hmul : (n : ℝ) / p * (c / s ^ 2) ≤ K * phiStar p (p - a0) :=
    mul_le_mul hKge hphi.le (by positivity) (by positivity)
  have e : (n : ℝ) / p * (c / s ^ 2) = c / p * s ^ 2 := by
    rw [hnp]; field_simp
  have : 0 ≤ c / p * s ^ 2 := by positivity
  have e2 : c / (2 * p) * s ^ 2 = c / p * s ^ 2 / 2 := by ring
  have hex : Real.exp (-(K * phiStar p (p - a0))) ≤ Real.exp (-(c / (2 * p) * s ^ 2)) :=
    Real.exp_le_exp.2 (neg_le_neg (by linarith))
  linarith

private theorem piece_lower (μ : PMF ℕ) {p : ℝ} (hp : (μ 0).toReal = p) (hp0 : 0 < p)
    (hp1 : p < 1) {s : ℝ} {n : ℕ} (hs : 4 ≤ s) (hs4 : s ^ 4 = n) {c : ℝ} (hc : 0 < c)
    (hphi : c / s ^ 2 < phiStar p (p + p ^ 2 / 4 / s)) :
    (Measure.infinitePi fun _ : ℕ => μ.toMeasure).real
        {ω | n ≤ walkLeafCount ω (⌈(n : ℝ) / p - s ^ 3⌉₊ - 1)} ≤
      2 * Real.exp (-(c / (2 * p) * s ^ 2)) := by
  have hspos : 0 < s := by linarith
  have hnp : (n : ℝ) / p = s ^ 4 / p := by rw [← hs4]
  have h3 : 1 ≤ s ^ 3 := one_le_pow₀ (by linarith)
  have hα := alg_three hp0 hp1 hs
  have hb0 : 0 < (n : ℝ) / p - s ^ 3 := by rw [hnp]; linarith
  have hc1 : 1 ≤ ⌈(n : ℝ) / p - s ^ 3⌉₊ :=
    Nat.one_le_iff_ne_zero.2 (by rw [Ne, Nat.ceil_eq_zero, not_le]; exact hb0)
  have hcast : ((⌈(n : ℝ) / p - s ^ 3⌉₊ - 1 : ℕ) : ℝ) = (⌈(n : ℝ) / p - s ^ 3⌉₊ : ℝ) - 1 := by
    push_cast [Nat.cast_sub hc1]; ring
  have hK2lt : ((⌈(n : ℝ) / p - s ^ 3⌉₊ - 1 : ℕ) : ℝ) < (n : ℝ) / p - s ^ 3 := by
    rw [hcast]; linarith [Nat.ceil_lt_add_one hb0.le]
  have hK2ge : (n : ℝ) / p - s ^ 3 - 1 ≤ ((⌈(n : ℝ) / p - s ^ 3⌉₊ - 1 : ℕ) : ℝ) := by
    rw [hcast]; linarith [Nat.le_ceil ((n : ℝ) / p - s ^ 3)]
  generalize hK : ⌈(n : ℝ) / p - s ^ 3⌉₊ - 1 = K at hK2lt hK2ge
  have hKge : (n : ℝ) / (2 * p) ≤ K := by
    have : (n : ℝ) / (2 * p) = (n : ℝ) / p / 2 := by field_simp
    rw [this, hnp] at *
    linarith
  have hn1 : (1 : ℝ) < (n : ℝ) / (2 * p) := by
    have : (256 : ℝ) ≤ n := by rw [← hs4]; nlinarith [pow_pos hspos 2]
    rw [lt_div_iff₀ (by positivity)]; nlinarith
  have hKpos : 1 ≤ K := by
    have : (1 : ℝ) < K := lt_of_lt_of_le hn1 hKge
    exact_mod_cast this.le
  set a0 : ℝ := p ^ 2 / 4 / s with ha0
  have ha0pos : 0 < a0 := by positivity
  have hKr : (0 : ℝ) < K := by exact_mod_cast hKpos
  have hpa : 0 < p + a0 := by linarith
  have key : (K : ℝ) * (p + a0) < n := by
    have h1 : (K : ℝ) * (p + a0) < ((n : ℝ) / p - s ^ 3) * (p + a0) :=
      mul_lt_mul_of_pos_right hK2lt hpa
    have h2 := alg_two hp0 hp1 hs ha0
    rw [← hnp, hs4] at h2
    linarith
  have hE : {ω | n ≤ walkLeafCount ω K} ⊆
      {ω | p + a0 < (walkLeafCount ω K : ℝ) / K} := by
    intro ω hω
    have hge : (n : ℝ) ≤ walkLeafCount ω K := by
      exact_mod_cast (show n ≤ walkLeafCount ω K from hω)
    show p + a0 < (walkLeafCount ω K : ℝ) / K
    rw [lt_div_iff₀ hKr]
    linarith
  obtain ⟨hup, -⟩ := counter_tails μ hp hp0 hp1 ha0pos hKpos
  refine (measureReal_mono hE).trans (hup.trans ?_)
  have hmul : (n : ℝ) / (2 * p) * (c / s ^ 2) ≤ K * phiStar p (p + a0) :=
    mul_le_mul hKge hphi.le (by positivity) (by positivity)
  have e : (n : ℝ) / (2 * p) * (c / s ^ 2) = c / (2 * p) * s ^ 2 := by
    rw [← hs4]; field_simp
  have hex : Real.exp (-(K * phiStar p (p + a0))) ≤ Real.exp (-(c / (2 * p) * s ^ 2)) :=
    Real.exp_le_exp.2 (neg_le_neg (by linarith))
  linarith

/-! ## Lemma 6.2(i) -/

private theorem lem_CVf2_i_aux (μ : PMF ℕ) (h0 : μ 0 ≠ 0) (h1 : μ 0 ≠ 1) :
    IsOe (1 / 2) fun n : ℕ =>
      ((Measure.infinitePi fun _ : ℕ => μ.toMeasure).real
        {ω | (¬ ∃ k, IsMarkTime n ω k) ∨
          ∃ k, IsMarkTime n ω k ∧
            1 / (n : ℝ) ^ (1 / 4 : ℝ) < |(k : ℝ) / n - 1 / (μ 0).toReal|}) := by
  have hp0 : 0 < (μ 0).toReal := ENNReal.toReal_pos h0 (μ.apply_ne_top 0)
  have hp1 : (μ 0).toReal < 1 := by
    have hlt : μ 0 < 1 := lt_of_le_of_ne (PMF.coe_le_one μ 0) h1
    simpa using (ENNReal.toReal_lt_toReal (μ.apply_ne_top 0) ENNReal.one_ne_top).2 hlt
  generalize hpdef : (μ 0).toReal = p at hp0 hp1 ⊢
  have hδ : 0 < p ^ 2 / 4 := by positivity
  obtain ⟨c, hc, N, hN⟩ := LeafConcentration.Chernoff.phiStar_lower hp0 hp1 hδ
  apply LeafConcentration.WalkDeviation.isOe_of_eventually_bound (by norm_num)
    (fun _ => measureReal_le_one) (C := 4) (c := c / (2 * p)) (by norm_num) (by positivity)
  filter_upwards [eventually_ge_atTop (max N 256)] with n hn
  have hnN : N ≤ n := (le_max_left _ _).trans hn
  have hn256 : 256 ≤ n := (le_max_right _ _).trans hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  obtain ⟨hphiU, hphiL⟩ := hN n hnN
  generalize hs : (n : ℝ) ^ (1 / 4 : ℝ) = s at hphiU hphiL
  have hspos : 0 < s := by rw [← hs]; exact Real.rpow_pos_of_pos hn0 _
  have hs4 : s ^ 4 = n := by
    rw [← hs, ← Real.rpow_natCast, ← Real.rpow_mul hn0.le]; norm_num
  have hroot : (n : ℝ) ^ (1 / 2 : ℝ) = s ^ 2 := by
    rw [← hs, ← Real.rpow_natCast, ← Real.rpow_mul hn0.le]; norm_num
  have hs4' : (4 : ℝ) ≤ s := by
    by_contra hlt
    rw [not_le] at hlt
    have : s ^ 4 < 4 ^ 4 := by gcongr
    have h256 : (256 : ℝ) ≤ n := by exact_mod_cast hn256
    nlinarith
  rw [hroot] at hphiU hphiL
  have hU := piece_upper μ hpdef hp0 hp1 hs4' hs4 hc hphiL
  have hL := piece_lower μ hpdef hp0 hp1 hs4' hs4 hc hphiU
  have hbad : {ω | (¬ ∃ k, IsMarkTime n ω k) ∨
      ∃ k, IsMarkTime n ω k ∧ 1 / s < |(k : ℝ) / n - 1 / p|} ⊆
      {ω | walkLeafCount ω ⌊(n : ℝ) / p + s ^ 3⌋₊ < n} ∪
        {ω | n ≤ walkLeafCount ω (⌈(n : ℝ) / p - s ^ 3⌉₊ - 1)} := by
    intro ω hω
    rcases hω with hno | ⟨k, hk, hdev⟩
    · left
      by_contra hcon
      exact hno (by
        obtain ⟨k', -, hk'⟩ := exists_markTime_of_le (n := n)
          (K := ⌊(n : ℝ) / p + s ^ 3⌋₊) (ω := ω) (not_lt.1 hcon)
        exact ⟨k', hk'⟩)
    · have hnk : (k : ℝ) / n - 1 / p = ((k : ℝ) - n / p) / n := by field_simp
      have h1s : 1 / s * n = s ^ 3 := by rw [← hs4]; field_simp
      rw [hnk, abs_div, abs_of_pos hn0, lt_div_iff₀ hn0, h1s] at hdev
      rcases lt_abs.1 hdev with h | h
      · left
        have hk1 : ⌊(n : ℝ) / p + s ^ 3⌋₊ < k := by
          exact (Nat.floor_lt (by positivity)).2 (by linarith)
        exact hk.2 _ hk1
      · right
        have hk2 : k < ⌈(n : ℝ) / p - s ^ 3⌉₊ := by
          apply Nat.lt_ceil.2
          linarith
        have hkle : k ≤ ⌈(n : ℝ) / p - s ^ 3⌉₊ - 1 := by omega
        have h1 := walkLeafCount_mono ω hkle
        have h2 : walkLeafCount ω k = n := hk.1
        show n ≤ walkLeafCount ω (⌈(n : ℝ) / p - s ^ 3⌉₊ - 1)
        omega
  rw [hroot]
  calc _ ≤ _ := measureReal_mono hbad
    _ ≤ _ := measureReal_union_le _ _
    _ ≤ _ := by rw [neg_mul]; linarith

theorem lem_CVf2_i (μ : PMF ℕ) (h0 : μ 0 ≠ 0) (h1 : μ 0 ≠ 1) :
    IsOe (1 / 2) fun n : ℕ =>
      ((Measure.infinitePi fun _ : ℕ => μ.toMeasure).real
        {ω | (¬ ∃ k, IsMarkTime n ω k) ∨
          ∃ k, IsMarkTime n ω k ∧
            1 / (n : ℝ) ^ (1 / 4 : ℝ) < |(k : ℝ) / n - 1 / (μ 0).toReal|}) :=
  lem_CVf2_i_aux μ h0 h1

/-- `T_n < ∞` for all `n` almost surely. -/
theorem ae_exists_markTime (μ : PMF ℕ) (h0 : μ 0 ≠ 0) :
    ∀ᵐ ω ∂(Measure.infinitePi fun _ : ℕ => μ.toMeasure), ∀ n : ℕ, ∃ k, IsMarkTime n ω k := by
  by_cases h1 : μ 0 = 1
  · have hsupp : μ.support = {0} := (PMF.apply_eq_one_iff μ 0).1 h1
    have hi : ∀ i : ℕ, ∀ᵐ ω ∂(Measure.infinitePi fun _ : ℕ => μ.toMeasure), ω i = 0 := by
      intro i
      have hmp := measurePreserving_eval_infinitePi (fun _ : ℕ => μ.toMeasure) i
      have : μ.toMeasure ({0}ᶜ : Set ℕ) = 0 := by
        rw [PMF.toMeasure_apply_eq_zero_iff _ (measurableSet_singleton 0).compl, hsupp]
        exact disjoint_compl_right
      have h2 : ∀ᵐ x ∂μ.toMeasure, x = 0 := by
        rw [ae_iff]
        exact this
      exact hmp.quasiMeasurePreserving.ae h2
    filter_upwards [ae_all_iff.2 hi] with ω hω n
    rw [exists_isMarkTime_iff]
    refine ⟨n, ?_⟩
    unfold walkLeafCount
    simp [hω]
  · have hao := lem_CVf2_i_aux μ h0 h1
    obtain ⟨C, c, hC, hc, hb⟩ := hao
    rw [ae_all_iff]
    intro n
    set P := Measure.infinitePi fun _ : ℕ => μ.toMeasure with hP
    have hle : ∀ m : ℕ, n ≤ m → P.real {ω | ¬ ∃ k, IsMarkTime n ω k} ≤
        C * Real.exp (-c * (m : ℝ) ^ (1 / 2 : ℝ)) := by
      intro m hm
      refine le_trans (measureReal_mono ?_) (hb m)
      intro ω hω
      left
      intro ⟨k, hk⟩
      apply hω
      obtain ⟨k', -, hk'⟩ := exists_markTime_of_le (n := n) (K := k) (ω := ω)
        (by have := hk.1; omega)
      exact ⟨k', hk'⟩
    have htend : Tendsto (fun m : ℕ => C * Real.exp (-c * (m : ℝ) ^ (1 / 2 : ℝ))) atTop (𝓝 0) := by
      have h1 : Tendsto (fun m : ℕ => (m : ℝ) ^ (1 / 2 : ℝ)) atTop atTop :=
        (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp tendsto_natCast_atTop_atTop
      have h2 := (h1.const_mul_atTop_of_neg (by linarith : -c < 0))
      have h3 := Real.tendsto_exp_atBot.comp h2
      simpa using h3.const_mul C
    have hz : P.real {ω | ¬ ∃ k, IsMarkTime n ω k} ≤ 0 :=
      ge_of_tendsto htend (eventually_atTop.2 ⟨n, hle⟩)
    have hz' : P {ω | ¬ ∃ k, IsMarkTime n ω k} = 0 :=
      (measureReal_eq_zero_iff).1 (le_antisymm hz measureReal_nonneg)
    rw [ae_iff]
    simpa using hz'

end BGWLeaves.Vervaat.MarkTime
