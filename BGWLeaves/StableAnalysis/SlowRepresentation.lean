module

public import BGWLeaves.StableAnalysis.SlowVariation

/-!
# Bingham representation of slowly varying functions

Bingham–Goldie–Teugels, Theorem 1.3.1, in the eventual form frozen in
`BGWLeaves.StableAnalysis.slow_representation` (the printed text has `∫₁ˣ` for all `x ≥ 0`;
the corrected eventual form is formalized, see `MANUSCRIPT_RECOMMENDATIONS.md`, R5).
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped Topology Interval

namespace BGWLeaves.StableAnalysis.SlowRepresentation

open BGW.StableTrees BGWLeaves.StableAnalysis

variable {L : ℝ → ℝ}

/-- A measurable function bounded on a bounded interval is interval integrable there. -/
private theorem intervalIntegrable_of_bound {f : ℝ → ℝ} (hf : Measurable f) {a b M : ℝ}
    (h : ∀ x ∈ Ι a b, |f x| ≤ M) : IntervalIntegrable f volume a b := by
  rw [intervalIntegrable_iff]
  refine Measure.integrableOn_of_bounded (M := M) ?_ hf.aestronglyMeasurable ?_
  · rw [Set.uIoc, Real.volume_Ioc]
    exact ENNReal.ofReal_ne_top
  · rw [ae_restrict_iff' measurableSet_uIoc]
    exact ae_of_all _ (fun x hx => by simpa using h x hx)

/-! ### The representation implies slow variation -/

private theorem slow_of_representation {c e : ℝ → ℝ} {cinf X : ℝ} (hcinf : 0 < cinf)
    (hX : 1 ≤ X) (he : Measurable e) (hc : Tendsto c atTop (𝓝 cinf))
    (he0 : Tendsto e atTop (𝓝 0)) (hb : ∀ x, X ≤ x → |e x| ≤ 1)
    (hL : ∀ x, X ≤ x → L x = c x * Real.exp (∫ u in X..x, e u / u)) :
    SlowlyVarying L := by
  intro r hr
  have hX0 : 0 < X := by linarith
  have hint : ∀ a b, X ≤ a → X ≤ b → IntervalIntegrable (fun u => e u / u) volume a b := by
    intro a b ha hb'
    refine intervalIntegrable_of_bound (he.div measurable_id) (M := 1 / X) ?_
    intro u hu
    have hu' : X ≤ u := (le_min ha hb').trans hu.1.le
    have hu0 : 0 < u := by linarith
    show |e u / u| ≤ 1 / X
    rw [abs_div, abs_of_pos hu0]
    exact div_le_div₀ zero_le_one (hb u hu') hX0 hu'
  set m : ℝ := min 1 r with hm
  have hm0 : 0 < m := lt_min one_pos hr
  have hm1 : m ≤ 1 := min_le_left _ _
  have hmr : m ≤ r := min_le_right _ _
  -- the integral over `[x, r x]` tends to zero
  have hI : Tendsto (fun x : ℝ => ∫ u in x..r * x, e u / u) atTop (𝓝 0) := by
    rw [Metric.tendsto_atTop]
    intro ε' hε'
    set K : ℝ := |r - 1| / m with hK
    have hK0 : 0 ≤ K := by positivity
    have hε : 0 < ε' / (K + 1) := by positivity
    obtain ⟨M, hM⟩ := Metric.tendsto_atTop.1 he0 (ε' / (K + 1)) hε
    refine ⟨max (M / m) (X / m), fun x hx => ?_⟩
    have hx1 : M / m ≤ x := (le_max_left _ _).trans hx
    have hx2 : X / m ≤ x := (le_max_right _ _).trans hx
    have hmxM : M ≤ m * x := by rwa [div_le_iff₀ hm0, mul_comm] at hx1
    have hmxX : X ≤ m * x := by rwa [div_le_iff₀ hm0, mul_comm] at hx2
    have hx0 : 0 < x := by
      have : 0 < X / m := by positivity
      linarith
    have hbound : ∀ u ∈ Ι x (r * x), ‖e u / u‖ ≤ ε' / (K + 1) / (m * x) := by
      intro u hu
      have hmin : m * x ≤ min x (r * x) := by
        apply le_min
        · nlinarith
        · nlinarith
      have hu1 : m * x ≤ u := hmin.trans hu.1.le
      have hu0 : 0 < u := lt_of_lt_of_le (by positivity) hu1
      have h1 := hM u (hmxM.trans hu1)
      rw [Real.dist_eq, sub_zero] at h1
      rw [Real.norm_eq_abs, abs_div, abs_of_pos hu0]
      exact div_le_div₀ hε.le h1.le (by positivity) hu1
    have hn := intervalIntegral.norm_integral_le_of_norm_le_const hbound
    have hrx : |r * x - x| = |r - 1| * x := by
      rw [show r * x - x = (r - 1) * x by ring, abs_mul, abs_of_pos hx0]
    rw [hrx] at hn
    have hcalc : ε' / (K + 1) / (m * x) * (|r - 1| * x) = ε' / (K + 1) * K := by
      rw [hK]; field_simp
    rw [hcalc] at hn
    rw [Real.dist_eq, sub_zero]
    calc |∫ u in x..r * x, e u / u| = ‖∫ u in x..r * x, e u / u‖ := (Real.norm_eq_abs _).symm
      _ ≤ ε' / (K + 1) * K := hn
      _ < ε' := by
        have : ε' / (K + 1) * K = ε' - ε' / (K + 1) := by field_simp; ring
        rw [this]; linarith
  have hcr : Tendsto (fun x : ℝ => c (r * x)) atTop (𝓝 cinf) :=
    hc.comp (tendsto_id.const_mul_atTop hr)
  have hlim : Tendsto (fun x : ℝ => c (r * x) / c x * Real.exp (∫ u in x..r * x, e u / u))
      atTop (𝓝 1) := by
    have := (hcr.div hc hcinf.ne').mul ((Real.continuous_exp.tendsto 0).comp hI)
    simpa [div_self hcinf.ne'] using this
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop (X / m)] with x hx
  have hmx : X ≤ m * x := by rwa [div_le_iff₀ hm0, mul_comm] at hx
  have hx0 : 0 < x := by
    have : 0 < X / m := by positivity
    linarith
  have hxX : X ≤ x := by nlinarith
  have hrxX : X ≤ r * x := by nlinarith
  have hsub : (∫ u in X..r * x, e u / u) - (∫ u in X..x, e u / u) = ∫ u in x..r * x, e u / u :=
    intervalIntegral.integral_interval_sub_left (hint X (r * x) le_rfl hrxX) (hint X x le_rfl hxX)
  rw [hL x hxX, hL (r * x) hrxX, mul_div_mul_comm, ← Real.exp_sub, hsub]

/-! ### Slow variation implies the representation -/

/-- A nonnegative slowly varying function is eventually strictly positive. -/
private theorem eventually_pos_of_slowlyVarying (hnn : ∀ x, 0 < x → 0 ≤ L x)
    (hL : SlowlyVarying L) : ∀ᶠ x : ℝ in atTop, 0 < L x := by
  have hratio := hL 1 one_pos
  have hratio' : ∀ᶠ x : ℝ in atTop, 1 / 2 < L (1 * x) / L x :=
    hratio.eventually (lt_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1))
  filter_upwards [hratio', eventually_gt_atTop (0 : ℝ)] with x hx hxpos
  have hxne : L x ≠ 0 := by
    intro hzero
    have : L (1 * x) / L x = 0 := by simp [hzero]
    linarith
  exact lt_of_le_of_ne (hnn x hxpos) hxne.symm

section Smoothing

variable {g : ℝ → ℝ}

/-- The window average `t ↦ ∫_t^{t+1} g` of a measurable function is measurable. -/
private theorem measurable_window (hg : Measurable g) :
    Measurable (fun t : ℝ => ∫ s in t..t + 1, g s) := by
  have h : (fun t : ℝ => ∫ s in t..t + 1, g s) =
      fun t => ∫ s, g (t + s) ∂(volume.restrict (Ioc (0 : ℝ) 1)) := by
    funext t
    rw [← intervalIntegral.integral_of_le zero_le_one,
      intervalIntegral.integral_comp_add_left g t]
    simp
  rw [h]
  have : StronglyMeasurable (fun p : ℝ × ℝ => g (p.1 + p.2)) :=
    (hg.comp (measurable_fst.add measurable_snd)).stronglyMeasurable
  exact (this.integral_prod_right' (ν := volume.restrict (Ioc (0 : ℝ) 1))).measurable

/-- Local integrability of `g` beyond a threshold where unit increments are bounded. -/
private theorem intervalIntegrable_ge (hg : Measurable g) {T : ℝ}
    (hT : ∀ t, T ≤ t → ∀ u, |u| ≤ 1 → |g (t + u) - g t| < 1) :
    ∀ a b, T ≤ a → T ≤ b → IntervalIntegrable g volume a b := by
  have hn : ∀ n : ℕ, IntervalIntegrable g volume T (T + n) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hTn : T ≤ T + n := le_add_of_nonneg_right (Nat.cast_nonneg n)
      have hstep : IntervalIntegrable g volume (T + n) (T + n + 1) := by
        refine intervalIntegrable_of_bound hg (M := |g (T + n)| + 1) ?_
        intro s hs
        rw [Set.uIoc_of_le (by linarith)] at hs
        have h1 := hT (T + n) hTn (s - (T + n))
          (by rw [abs_le]; constructor <;> linarith [hs.1, hs.2])
        rw [show T + n + (s - (T + n)) = s by ring] at h1
        have h2 := abs_sub_abs_le_abs_sub (g s) (g (T + n))
        linarith
      have := ih.trans hstep
      rwa [show T + ((n + 1 : ℕ) : ℝ) = T + n + 1 by push_cast; ring]
  intro a b ha hb
  obtain ⟨n, hn'⟩ := exists_nat_ge (max a b - T)
  have hTn : T ≤ T + n := le_add_of_nonneg_right (Nat.cast_nonneg n)
  refine (hn n).mono_set ?_
  rw [Set.uIcc_of_le hTn]
  refine Set.uIcc_subset_Icc ⟨ha, ?_⟩ ⟨hb, ?_⟩
  · linarith [le_max_left a b]
  · linarith [le_max_right a b]

/-- The window average differs from `g` by a vanishing amount. -/
private theorem tendsto_sub_window
    (hU : ∀ ε : ℝ, 0 < ε → ∃ T, ∀ t, T ≤ t → ∀ u, |u| ≤ 1 → |g (t + u) - g t| < ε)
    {T : ℝ} (hint : ∀ a b, T ≤ a → T ≤ b → IntervalIntegrable g volume a b) :
    Tendsto (fun t => g t - ∫ s in t..t + 1, g s) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨T1, hT1⟩ := hU (ε / 2) (by positivity)
  refine ⟨max T T1, fun t ht => ?_⟩
  have htT : T ≤ t := (le_max_left _ _).trans ht
  have htT1 : T1 ≤ t := (le_max_right _ _).trans ht
  have h1 : IntervalIntegrable g volume t (t + 1) := hint t (t + 1) htT (by linarith)
  have h2 : ∫ s in t..t + 1, (g s - g t) = (∫ s in t..t + 1, g s) - g t := by
    rw [intervalIntegral.integral_sub h1 intervalIntegrable_const]; simp
  have h3 : ‖∫ s in t..t + 1, (g s - g t)‖ ≤ ε / 2 * |t + 1 - t| :=
    intervalIntegral.norm_integral_le_of_norm_le_const (fun s hs => by
      rw [Set.uIoc_of_le (by linarith)] at hs
      have := hT1 t htT1 (s - t) (by rw [abs_le]; constructor <;> linarith [hs.1, hs.2])
      rw [show t + (s - t) = s by ring] at this
      exact this.le)
  rw [h2, show |t + 1 - t| = 1 by simp, Real.norm_eq_abs, abs_sub_comm] at h3
  rw [Real.dist_eq, sub_zero]
  linarith

/-- The window average has increment `g (s + 1) - g s`. -/
private theorem window_sub (T : ℝ)
    (hint : ∀ a b, T ≤ a → T ≤ b → IntervalIntegrable g volume a b) {t : ℝ} (ht : T ≤ t) :
    (∫ s in t..t + 1, g s) - (∫ s in T..T + 1, g s) = ∫ s in T..t, (g (s + 1) - g s) := by
  have hshift : IntervalIntegrable (fun s => g (s + 1)) volume T t := by
    have := (hint (T + 1) (t + 1) (by linarith) (by linarith)).comp_add_right 1
    simpa using this
  rw [intervalIntegral.integral_sub hshift (hint T t le_rfl ht),
    intervalIntegral.integral_comp_add_right g 1]
  have ha := intervalIntegral.integral_add_adjacent_intervals
    (hint T (T + 1) le_rfl (by linarith)) (hint (T + 1) (t + 1) (by linarith) (by linarith))
  have hb := intervalIntegral.integral_add_adjacent_intervals
    (hint T t le_rfl ht) (hint t (t + 1) ht (by linarith))
  linarith

end Smoothing

/-- Substitution `u = exp s`. -/
private theorem integral_exp_subst (F : ℝ → ℝ) {T t : ℝ} (h : T ≤ t) :
    ∫ u in Real.exp T..Real.exp t, F u / u = ∫ s in T..t, F (Real.exp s) := by
  rw [intervalIntegral.integral_of_le (Real.exp_le_exp.2 h), intervalIntegral.integral_of_le h]
  have himg : Real.exp '' Ioc T t = Ioc (Real.exp T) (Real.exp t) := by
    ext y
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact ⟨Real.exp_lt_exp.2 hs.1, Real.exp_le_exp.2 hs.2⟩
    · rintro ⟨h1, h2⟩
      have hy : 0 < y := lt_trans (Real.exp_pos T) h1
      refine ⟨Real.log y, ⟨?_, ?_⟩, Real.exp_log hy⟩
      · exact (Real.lt_log_iff_exp_lt hy).2 h1
      · exact (Real.log_le_iff_le_exp hy).2 h2
  rw [← himg, integral_image_eq_integral_abs_deriv_smul measurableSet_Ioc (f' := Real.exp)
    (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt) Real.exp_injective.injOn]
  refine setIntegral_congr_fun measurableSet_Ioc (fun s _ => ?_)
  have := (Real.exp_pos s).ne'
  simp only [abs_of_pos (Real.exp_pos s), smul_eq_mul]
  field_simp

private theorem representation_of_slow (hmeas : Measurable L) (hnn : ∀ x, 0 < x → 0 ≤ L x)
    (hL : SlowlyVarying L) :
    ∃ (c e : ℝ → ℝ) (cinf X : ℝ), 0 < cinf ∧ 1 ≤ X ∧ Measurable c ∧ Measurable e ∧
      Tendsto c atTop (𝓝 cinf) ∧ Tendsto e atTop (𝓝 0) ∧ (∀ x, X ≤ x → |e x| ≤ 1) ∧
      ∀ x, X ≤ x → L x = c x * Real.exp (∫ u in X..x, e u / u) := by
  obtain ⟨g, hg⟩ : ∃ g : ℝ → ℝ, g = fun t => Real.log (L (Real.exp t)) := ⟨_, rfl⟩
  have hgm : Measurable g := by
    rw [hg]; exact Real.measurable_log.comp (hmeas.comp Real.measurable_exp)
  have hU : ∀ ε : ℝ, 0 < ε → ∃ T, ∀ t, T ≤ t → ∀ u, |u| ≤ 1 → |g (t + u) - g t| < ε := by
    intro ε hε
    rw [hg]
    exact SlowVariation.slow_uniform_log hmeas hnn hL zero_le_one hε
  obtain ⟨B, hB⟩ := eventually_atTop.1
    (Real.tendsto_exp_atTop.eventually (eventually_pos_of_slowlyVarying hnn hL))
  obtain ⟨A, hA⟩ := hU 1 one_pos
  set T0 : ℝ := max 0 (max A B) with hT0
  have hT0A : A ≤ T0 := (le_max_left A B).trans (le_max_right _ _)
  have hT0B : B ≤ T0 := (le_max_right A B).trans (le_max_right _ _)
  have hT0nn : 0 ≤ T0 := le_max_left _ _
  have hint := intervalIntegrable_ge hgm (T := T0) (fun t ht => hA t (hT0A.trans ht))
  have hwin := tendsto_sub_window hU hint
  have hstep : Tendsto (fun t => g (t + 1) - g t) atTop (𝓝 0) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨T, hT⟩ := hU ε hε
    refine ⟨T, fun t ht => ?_⟩
    rw [Real.dist_eq, sub_zero]
    exact hT t ht 1 (by simp)
  refine ⟨fun x => Real.exp ((∫ s in T0..T0 + 1, g s) +
      (g (Real.log x) - ∫ s in Real.log x..Real.log x + 1, g s)),
    fun u => g (Real.log u + 1) - g (Real.log u),
    Real.exp (∫ s in T0..T0 + 1, g s), Real.exp T0, Real.exp_pos _,
    Real.one_le_exp hT0nn, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Real.measurable_exp.comp (measurable_const.add
      ((hgm.comp Real.measurable_log).sub ((measurable_window hgm).comp Real.measurable_log)))
  · exact (hgm.comp (Real.measurable_log.add_const 1)).sub (hgm.comp Real.measurable_log)
  · have h1 := hwin.comp Real.tendsto_log_atTop
    have h2 := (Real.continuous_exp.tendsto
      ((∫ s in T0..T0 + 1, g s) + 0)).comp (tendsto_const_nhds.add h1)
    rw [add_zero] at h2
    exact h2
  · exact hstep.comp Real.tendsto_log_atTop
  · intro x hx
    have hx0 : 0 < x := (Real.exp_pos T0).trans_le hx
    have ht : T0 ≤ Real.log x := (Real.le_log_iff_exp_le hx0).2 hx
    exact (hA _ (hT0A.trans ht) 1 (by simp)).le
  · intro x hx
    have hx0 : 0 < x := (Real.exp_pos T0).trans_le hx
    have ht : T0 ≤ Real.log x := (Real.le_log_iff_exp_le hx0).2 hx
    have hsub := integral_exp_subst (fun u => g (Real.log u + 1) - g (Real.log u)) ht
    simp only [Real.log_exp] at hsub
    rw [Real.exp_log hx0] at hsub
    rw [hsub, ← window_sub T0 hint ht, ← Real.exp_add]
    have hpos : 0 < L x := by
      have := hB (Real.log x) (hT0B.trans ht)
      rwa [Real.exp_log hx0] at this
    have hgx : g (Real.log x) = Real.log (L x) := by rw [hg]; simp only [Real.exp_log hx0]
    rw [show (∫ s in T0..T0 + 1, g s) + (g (Real.log x) - ∫ s in Real.log x..Real.log x + 1, g s)
      + ((∫ s in Real.log x..Real.log x + 1, g s) - ∫ s in T0..T0 + 1, g s) = g (Real.log x) by ring,
      hgx, Real.exp_log hpos]

/-- Bingham's representation theorem (Bingham–Goldie–Teugels, Theorem 1.3.1), in the eventual
form: a measurable nonnegative `L` is slowly varying iff `L x = c x * exp (∫_X^x e u / u du)`
for `x ≥ X`, with `c → cinf ∈ (0, ∞)` and `e → 0`.  The printed statement is for all `x ≥ 0`;
the corrected eventual form is the one formalized (`MANUSCRIPT_RECOMMENDATIONS.md`, R5). -/
theorem slow_representation (hmeas : Measurable L) (hnn : ∀ x, 0 < x → 0 ≤ L x) :
    SlowlyVarying L ↔
      ∃ (c e : ℝ → ℝ) (cinf X : ℝ), 0 < cinf ∧ 1 ≤ X ∧ Measurable c ∧ Measurable e ∧
        Tendsto c atTop (𝓝 cinf) ∧ Tendsto e atTop (𝓝 0) ∧ (∀ x, X ≤ x → |e x| ≤ 1) ∧
        ∀ x, X ≤ x → L x = c x * Real.exp (∫ u in X..x, e u / u) :=
  ⟨representation_of_slow hmeas hnn, fun ⟨_, _, _, _, hcinf, hX, _, he, hc, he0, hb, hL⟩ =>
    slow_of_representation hcinf hX he hc he0 hb hL⟩

end BGWLeaves.StableAnalysis.SlowRepresentation
