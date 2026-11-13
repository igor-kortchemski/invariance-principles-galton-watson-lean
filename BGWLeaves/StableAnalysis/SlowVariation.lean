module

public import BGWLeaves.StableAnalysis.Defs
public import Mathlib.MeasureTheory.Function.Egorov

@[expose] public section

open Filter MeasureTheory Set
open scoped Topology ENNReal

namespace BGWLeaves.StableAnalysis.SlowVariation

open BGW.StableTrees

variable {L : ℝ → ℝ}

/-- A nonnegative slowly varying function is eventually strictly positive.
The `a = 1` ratio limit rules out eventual zeros. -/
private theorem eventually_pos_of_slowlyVarying (hnn : ∀ x, 0 < x → 0 ≤ L x)
    (hL : SlowlyVarying L) : ∀ᶠ x : ℝ in atTop, 0 < L x := by
  have hratio := hL 1 one_pos
  have hhalf : (1 / 2 : ℝ) < 1 := by norm_num
  have hratio' : ∀ᶠ x : ℝ in atTop, 1 / 2 < L (1 * x) / L x :=
    hratio.eventually (lt_mem_nhds hhalf)
  filter_upwards [hratio', eventually_gt_atTop (0 : ℝ)] with x hx hxpos
  have hxne : L x ≠ 0 := by
    intro hzero
    have : L (1 * x) / L x = 0 := by simp [hzero]
    linarith
  exact lt_of_le_of_ne (hnn x hxpos) hxne.symm

/-- Two exceptional sets of measure at most `1/4` cannot cover a unit interval,
even after translating one of them. -/
private theorem exists_outside_small_sets (s t : Set ℝ)
    (hs : volume s ≤ ENNReal.ofReal (1 / 4 : ℝ)) (ht : volume t ≤ ENNReal.ofReal (1 / 4 : ℝ)) (u : ℝ) :
    ∃ v ∈ Icc (0 : ℝ) 1, v + u ∉ s ∧ v ∉ t := by
  by_contra h
  have hsub : Icc (0 : ℝ) 1 ⊆ ((fun v => v + u) ⁻¹' s) ∪ t := by
    intro v hv
    by_contra hv'
    exact h ⟨v, hv, by simpa only [mem_union, mem_preimage, not_or] using hv'⟩
  have hb := (measure_mono (μ := volume) hsub).trans (measure_union_le _ _)
  rw [measure_preimage_add_right] at hb
  have hc := hb.trans (add_le_add hs ht)
  rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)] at hc
  norm_num at hc

/-- The sequential Egorov step in the measurable uniform convergence theorem.
The shifts may vary arbitrarily in a bounded interval. -/
private theorem additive_slow_sequence {g : ℝ → ℝ} (hg : Measurable g)
    (hslow : ∀ u : ℝ, Tendsto (fun t => g (t + u) - g t) atTop (𝓝 0))
    {a b : ℕ → ℝ} (ha : Tendsto a atTop atTop) {K : ℝ} (_hK : 0 ≤ K)
    (hb : ∀ n, |b n| ≤ K) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, |g (a n + b n) - g (a n)| < ε := by
  have hab : Tendsto (fun n => a n + b n) atTop atTop := by
    refine tendsto_atTop_mono (fun n => ?_)
      (tendsto_atTop_add_const_right atTop (-K) ha)
    have := (abs_le.mp (hb n)).1
    linarith
  let f : ℕ → ℝ → ℝ := fun n v => g (a n + v) - g (a n)
  let k : ℕ → ℝ → ℝ := fun n v => g (a n + b n + v) - g (a n + b n)
  have hf : ∀ n, StronglyMeasurable (f n) := fun n =>
    ((hg.comp (measurable_const.add measurable_id)).sub measurable_const).stronglyMeasurable
  have hk : ∀ n, StronglyMeasurable (k n) := fun n =>
    ((hg.comp (measurable_const.add measurable_id)).sub measurable_const).stronglyMeasurable
  obtain ⟨s, _, _, hs, hfs⟩ := tendstoUniformlyOn_of_ae_tendsto
    (μ := volume) hf stronglyMeasurable_const
    (s := Icc (-K) (K + 1)) measurableSet_Icc (by simp)
    (ae_of_all _ (fun v _ => (hslow v).comp ha)) (show (0 : ℝ≥0∞) < ENNReal.ofReal (1 / 4 : ℝ) by norm_num)
  obtain ⟨t, _, _, ht, hkt⟩ := tendstoUniformlyOn_of_ae_tendsto
    (μ := volume) hk stronglyMeasurable_const
    (s := Icc (0 : ℝ) 1) measurableSet_Icc (by simp)
    (ae_of_all _ (fun v _ => (hslow v).comp hab)) (show (0 : ℝ≥0∞) < ENNReal.ofReal (1 / 4 : ℝ) by norm_num)
  have hfs' := Metric.tendstoUniformlyOn_iff.mp hfs (ε / 2) (by positivity)
  have hkt' := Metric.tendstoUniformlyOn_iff.mp hkt (ε / 2) (by positivity)
  filter_upwards [hfs', hkt'] with n hn hn'
  obtain ⟨v, hv, hvs, hvt⟩ := exists_outside_small_sets s t hs ht (b n)
  have hvb : v + b n ∈ Icc (-K) (K + 1) := by
    have := abs_le.mp (hb n)
    constructor <;> linarith [hv.1, hv.2]
  have h1 := hn (v + b n) ⟨hvb, hvs⟩
  have h2 := hn' v ⟨hv, hvt⟩
  simp only [f, k, Real.dist_eq, zero_sub, abs_neg] at h1 h2
  have heq : g (a n + b n) - g (a n) =
      (g (a n + (v + b n)) - g (a n)) -
      (g (a n + b n + v) - g (a n + b n)) := by
    rw [show a n + (v + b n) = a n + b n + v by ring]
    ring
  rw [heq]
  exact (abs_sub _ _).trans_lt (by linarith)

/-- Measurable additive Uniform Convergence Theorem, on every bounded interval
of shifts. No local boundedness or continuity of `g` is assumed. -/
theorem additive_uniform_convergence {g : ℝ → ℝ} (hg : Measurable g)
    (hslow : ∀ u : ℝ, Tendsto (fun t => g (t + u) - g t) atTop (𝓝 0))
    {K : ℝ} (hK : 0 ≤ K) {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℝ, ∀ t : ℝ, T ≤ t → ∀ u : ℝ, |u| ≤ K →
      |g (t + u) - g t| < ε := by
  classical
  by_contra h
  push Not at h
  have hex : ∀ n : ℕ, ∃ t : ℝ, (n : ℝ) ≤ t ∧
      ∃ u : ℝ, |u| ≤ K ∧ ε ≤ |g (t + u) - g t| := fun n => h n
  choose a ha b hb hbad using hex
  have hatop : Tendsto a atTop atTop :=
    tendsto_atTop_mono ha tendsto_natCast_atTop_atTop
  have he := additive_slow_sequence hg hslow hatop hK hb hε
  obtain ⟨n, hn⟩ := he.exists
  exact (not_lt_of_ge (hbad n)) hn

/-- Logarithmic change of variables turns ratio slow variation into additive
slow variation. -/
private theorem log_exp_slowlyVarying (hnn : ∀ x, 0 < x → 0 ≤ L x)
    (hL : SlowlyVarying L) (u : ℝ) :
    Tendsto (fun t => Real.log (L (Real.exp (t + u))) - Real.log (L (Real.exp t)))
      atTop (𝓝 0) := by
  have hp := eventually_pos_of_slowlyVarying hnn hL
  have h1 := Real.tendsto_exp_atTop.eventually hp
  have h2 := (Real.tendsto_exp_atTop.comp
    (tendsto_atTop_add_const_right atTop u tendsto_id)).eventually hp
  have hr := (hL (Real.exp u) (Real.exp_pos u)).comp Real.tendsto_exp_atTop
  have hl := (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp hr
  simp only [Real.log_one] at hl
  apply hl.congr'
  filter_upwards [h1, h2] with t ht ht'
  change 0 < L (Real.exp (t + u)) at ht'
  change Real.log (L (Real.exp u * Real.exp t) / L (Real.exp t)) = _
  rw [show Real.exp u * Real.exp t = Real.exp (t + u) by rw [← Real.exp_add]; congr 1; ring,
    Real.log_div ht'.ne' ht.ne']

/-- Uniform convergence of logarithmic ratios on bounded logarithmic scales. -/
theorem slow_uniform_log (hmeas : Measurable L) (hnn : ∀ x, 0 < x → 0 ≤ L x)
    (hL : SlowlyVarying L) {K : ℝ} (hK : 0 ≤ K) {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℝ, ∀ t : ℝ, T ≤ t → ∀ u : ℝ, |u| ≤ K →
      |Real.log (L (Real.exp (t + u))) - Real.log (L (Real.exp t))| < ε :=
  additive_uniform_convergence
    (Real.measurable_log.comp (hmeas.comp Real.measurable_exp))
    (log_exp_slowlyVarying hnn hL) hK hε

/-- Chaining unit increments gives a linear bound for every nonnegative shift. -/
private theorem additive_linear_bound {g : ℝ → ℝ} {T δ : ℝ} (hδ : 0 ≤ δ)
    (hunit : ∀ t : ℝ, T ≤ t → ∀ v : ℝ, 0 ≤ v → v ≤ 1 →
      |g (t + v) - g t| ≤ δ) {t u : ℝ} (ht : T ≤ t) (hu : 0 ≤ u) :
    |g (t + u) - g t| ≤ δ * (u + 1) := by
  have hn : ∀ n : ℕ, |g (t + n) - g t| ≤ (n : ℝ) * δ := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hs := hunit (t + n) (ht.trans (le_add_of_nonneg_right (Nat.cast_nonneg n))) 1 (by norm_num) le_rfl
      have heq : g (t + (n + 1 : ℕ)) - g t =
          (g (t + n + 1) - g (t + n)) + (g (t + n) - g t) := by
        push_cast
        rw [show t + ((n : ℝ) + 1) = t + n + 1 by ring]
        ring
      rw [heq]
      have hab := abs_add_le (g (t + n + 1) - g (t + n)) (g (t + n) - g t)
      push_cast
      linarith
  have hfl : (⌊u⌋₊ : ℝ) ≤ u := Nat.floor_le hu
  have hfr : u - (⌊u⌋₊ : ℝ) ≤ 1 := by linarith [Nat.lt_floor_add_one u]
  have hs := hunit (t + (⌊u⌋₊ : ℝ)) (ht.trans (le_add_of_nonneg_right (Nat.cast_nonneg ⌊u⌋₊)))
    (u - (⌊u⌋₊ : ℝ)) (by linarith) hfr
  have heq : g (t + u) - g t =
      (g (t + (⌊u⌋₊ : ℝ) + (u - (⌊u⌋₊ : ℝ))) - g (t + (⌊u⌋₊ : ℝ))) +
      (g (t + (⌊u⌋₊ : ℝ)) - g t) := by
    rw [show t + (⌊u⌋₊ : ℝ) + (u - (⌊u⌋₊ : ℝ)) = t + u by ring]
    ring
  rw [heq]
  have hab := abs_add_le (g (t + (⌊u⌋₊ : ℝ) + (u - (⌊u⌋₊ : ℝ))) - g (t + (⌊u⌋₊ : ℝ)))
    (g (t + (⌊u⌋₊ : ℝ)) - g t)
  have hnat := hn ⌊u⌋₊
  nlinarith

/-- Multiplicative UCT: ratio convergence is uniform on each compact interval
of positive scaling factors. -/
theorem slow_uniform_convergence (hmeas : Measurable L)
    (hnn : ∀ x, 0 < x → 0 ≤ L x) (hL : SlowlyVarying L)
    {a b : ℝ} (ha : 0 < a) (_hab : a ≤ b) {ε : ℝ} (hε : 0 < ε) :
    ∃ X : ℝ, ∀ x : ℝ, X ≤ x → ∀ r : ℝ, r ∈ Icc a b →
      |L (r * x) / L x - 1| < ε := by
  obtain ⟨δ, hδ, he⟩ := Metric.continuousAt_iff.mp
    (Real.continuous_exp.continuousAt (x := (0 : ℝ))) ε hε
  let K := max |Real.log a| |Real.log b|
  have hK : 0 ≤ K := (abs_nonneg _).trans (le_max_left _ _)
  obtain ⟨T, hT⟩ := slow_uniform_log hmeas hnn hL hK hδ
  obtain ⟨B, hB⟩ := eventually_atTop.1
    (Real.tendsto_exp_atTop.eventually (eventually_pos_of_slowlyVarying hnn hL))
  let S := max T (B + K)
  refine ⟨Real.exp S, ?_⟩
  intro x hx r hr
  have hx0 : 0 < x := (Real.exp_pos S).trans_le hx
  have ht : S ≤ Real.log x := (Real.le_log_iff_exp_le hx0).2 hx
  have hr0 : 0 < r := ha.trans_le hr.1
  have hrlog : |Real.log r| ≤ K := by
    apply abs_le.2
    constructor
    · have hl := Real.log_le_log ha hr.1
      have hk : |Real.log a| ≤ K := le_max_left _ _
      linarith [neg_abs_le (Real.log a)]
    · have hl := Real.log_le_log hr0 hr.2
      exact hl.trans ((le_abs_self _).trans (le_max_right _ _))
  have hlogs := hT (Real.log x) ((le_max_left _ _).trans ht) (Real.log r) hrlog
  have hp : 0 < L x := by
    simpa only [Real.exp_log hx0] using hB (Real.log x)
      (by have := le_max_right T (B + K); linarith)
  have hpr : 0 < L (r * x) := by
    have htB : B ≤ Real.log x + Real.log r := by
      have := le_max_right T (B + K)
      have := (abs_le.1 hrlog).1
      linarith
    simpa only [Real.exp_add, Real.exp_log hx0, Real.exp_log hr0, mul_comm]
      using hB (Real.log x + Real.log r) htB
  have he' := he (show dist
      (Real.log (L (Real.exp (Real.log x + Real.log r))) -
        Real.log (L (Real.exp (Real.log x)))) 0 < δ by
      simpa only [Real.dist_eq, sub_zero] using hlogs)
  simpa only [Real.exp_zero, Real.exp_add, Real.exp_log hx0, Real.exp_log hr0,
    mul_comm x r, Real.exp_sub, Real.exp_log hp, Real.exp_log hpr,
    Real.dist_eq] using he'

/-- A logarithmic Potter estimate, before exponentiating. -/
private theorem slow_log_potter (hmeas : Measurable L)
    (hnn : ∀ x, 0 < x → 0 ≤ L x) (hL : SlowlyVarying L) {δ : ℝ} (hδ : 0 < δ) :
    ∃ T : ℝ, 0 ≤ T ∧ (∀ t : ℝ, T ≤ t → 0 < L (Real.exp t)) ∧
      ∀ t : ℝ, T ≤ t → ∀ u : ℝ, 0 ≤ u →
        |Real.log (L (Real.exp (t + u))) - Real.log (L (Real.exp t))| ≤ δ * (u + 1) := by
  obtain ⟨A, hA⟩ := slow_uniform_log hmeas hnn hL (K := 1) (by norm_num) hδ
  obtain ⟨B, hB⟩ := eventually_atTop.1
    (Real.tendsto_exp_atTop.eventually (eventually_pos_of_slowlyVarying hnn hL))
  let T := max 0 (max A B)
  refine ⟨T, le_max_left _ _, fun t ht => hB t ((le_max_right A B).trans
    ((le_max_right 0 (max A B)).trans ht)), ?_⟩
  intro t ht u hu
  exact additive_linear_bound (g := fun s => Real.log (L (Real.exp s))) (T := T) hδ.le (fun s hs v hv hv' =>
    (hA s ((le_max_left A B).trans ((le_max_right 0 (max A B)).trans hs))
      v (by rwa [abs_of_nonneg hv])).le) ht hu

/-- Potter bounds with a single constant and threshold for all large integer
base points and all real scaling factors at least one. -/
theorem slow_potter_nat (hmeas : Measurable L) (hnn : ∀ x, 0 < x → 0 ≤ L x)
    (hL : SlowlyVarying L) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 1 < C ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ x : ℝ, 1 ≤ x →
      1 / C * x ^ (-ε) ≤ L (n * x) / L n ∧ L (n * x) / L n ≤ C * x ^ ε := by
  obtain ⟨T, _, hp, hT⟩ := slow_log_potter hmeas hnn hL hε
  obtain ⟨N, hN⟩ := exists_nat_ge (Real.exp T)
  refine ⟨Real.exp ε, by simpa using Real.exp_lt_exp.2 hε, N, ?_⟩
  intro n hn x hx
  have hnT : Real.exp T ≤ (n : ℝ) := hN.trans (by exact_mod_cast hn)
  have hn0 : 0 < (n : ℝ) := (Real.exp_pos T).trans_le hnT
  have hx0 : 0 < x := by linarith
  have ht : T ≤ Real.log n := (Real.le_log_iff_exp_le hn0).2 hnT
  have hu : 0 ≤ Real.log x := Real.log_nonneg hx
  have hposn : 0 < L n := by simpa only [Real.exp_log hn0] using hp (Real.log n) ht
  have hposnx : 0 < L (n * x) := by
    simpa only [Real.exp_add, Real.exp_log hn0, Real.exp_log hx0] using
      hp (Real.log n + Real.log x) (by linarith)
  have hh := hT (Real.log n) ht (Real.log x) hu
  simp only [Real.exp_add, Real.exp_log hn0, Real.exp_log hx0] at hh
  have heq : L (n * x) / L n = Real.exp (Real.log (L (n * x)) - Real.log (L n)) := by
    rw [Real.exp_sub, Real.exp_log hposnx, Real.exp_log hposn]
  rw [heq]
  constructor
  · have hlow := Real.exp_le_exp.2 (abs_le.1 hh).1
    convert hlow using 1
    rw [Real.rpow_def_of_pos hx0, one_div, ← Real.exp_neg, ← Real.exp_add]
    congr 1
    ring
  · have hhigh := Real.exp_le_exp.2 (abs_le.1 hh).2
    convert hhigh using 1
    rw [Real.rpow_def_of_pos hx0, ← Real.exp_add]
    congr 1
    ring

/-- The positive power dominates every measurable slowly varying function. -/
theorem slow_rpow_mul_tendsto_atTop (hmeas : Measurable L) (hnn : ∀ x, 0 < x → 0 ≤ L x)
    (hL : SlowlyVarying L) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun x : ℝ => x ^ ε * L x) atTop atTop := by
  obtain ⟨T, _, hp, hT⟩ := slow_log_potter hmeas hnn hL
    (show 0 < ε / 2 by positivity)
  let g : ℝ → ℝ := fun t => Real.log (L (Real.exp t))
  have hbound : ∀ t : ℝ, T ≤ t →
      |g t - g T| ≤ ε / 2 * (t - T + 1) := by
    intro t ht
    have hb := hT T le_rfl (t - T) (by linarith)
    simpa only [show T + (t - T) = t by ring] using hb
  have he : Tendsto (fun t => ε * t + g t) atTop atTop := by
    apply tendsto_atTop_mono' atTop (f₁ := fun t =>
      ε / 2 * t + (g T + ε / 2 * (T - 1)))
    · filter_upwards [eventually_ge_atTop T] with t ht
      have hb := (abs_le.1 (hbound t ht)).1
      nlinarith
    · exact tendsto_atTop_add_const_right atTop _
        (tendsto_id.const_mul_atTop (by positivity))
  have hr := (Real.tendsto_exp_atTop.comp he).comp Real.tendsto_log_atTop
  apply hr.congr'
  filter_upwards [eventually_ge_atTop (Real.exp T)] with x hx
  have hx0 := (Real.exp_pos T).trans_le hx
  have ht : T ≤ Real.log x := (Real.le_log_iff_exp_le hx0).2 hx
  have hpx : 0 < L x := by simpa only [Real.exp_log hx0] using hp (Real.log x) ht
  change Real.exp (ε * Real.log x + Real.log (L (Real.exp (Real.log x)))) = _
  rw [Real.exp_log hx0, Real.exp_add, Real.exp_log hpx, Real.rpow_def_of_pos hx0]
  rw [mul_comm ε]

/-- Every negative power times a measurable slowly varying function tends to zero. -/
theorem slow_rpow_neg_mul_tendsto_zero (hmeas : Measurable L)
    (hnn : ∀ x, 0 < x → 0 ≤ L x) (hL : SlowlyVarying L) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun x : ℝ => x ^ (-ε) * L x) atTop (𝓝 0) := by
  obtain ⟨T, _, hp, hT⟩ := slow_log_potter hmeas hnn hL
    (show 0 < ε / 2 by positivity)
  let g : ℝ → ℝ := fun t => Real.log (L (Real.exp t))
  have hbound : ∀ t : ℝ, T ≤ t →
      |g t - g T| ≤ ε / 2 * (t - T + 1) := by
    intro t ht
    have hb := hT T le_rfl (t - T) (by linarith)
    simpa only [show T + (t - T) = t by ring] using hb
  have he : Tendsto (fun t => -ε * t + g t) atTop atBot := by
    apply tendsto_atBot_mono' atTop (f₁ := fun t =>
      (-ε / 2) * t + (g T + ε / 2 * (1 - T)))
    · filter_upwards [eventually_ge_atTop T] with t ht
      have hb := (abs_le.1 (hbound t ht)).2
      nlinarith
    · exact tendsto_atBot_add_const_right atTop _
        ((tendsto_const_mul_atBot_of_neg (show -ε / 2 < 0 by linarith)).2 tendsto_id)
  have hr := (Real.tendsto_exp_atBot.comp he).comp Real.tendsto_log_atTop
  apply hr.congr'
  filter_upwards [eventually_ge_atTop (Real.exp T)] with x hx
  have hx0 := (Real.exp_pos T).trans_le hx
  have ht : T ≤ Real.log x := (Real.le_log_iff_exp_le hx0).2 hx
  have hpx : 0 < L x := by simpa only [Real.exp_log hx0] using hp (Real.log x) ht
  change Real.exp (-ε * Real.log x + Real.log (L (Real.exp (Real.log x)))) = _
  rw [Real.exp_log hx0, Real.exp_add, Real.exp_log hpx, Real.rpow_def_of_pos hx0]
  rw [mul_comm (-ε)]

end BGWLeaves.StableAnalysis.SlowVariation

