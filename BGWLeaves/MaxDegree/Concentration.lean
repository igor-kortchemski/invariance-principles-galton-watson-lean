module

public import BGWLeaves.MaxDegree.Defs
public import BGWLeaves.Conditioning
public import BGWLeaves.LocalEstimates
import BGWLeaves.Vervaat
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Independence.Integration
import Mathlib.MeasureTheory.Function.AEMeasurableSequence

/-!
# M9 provider `Concentration`

Density bounds and tightness of the midpoint of the bridge (discrete replacement of `eq:trucsuperutile`):
`chi_sup_bound`, `chi_zero_lower`, `wald_second_moment`, `bridge_midpoint_tight`.  The theorems are the registered holes of
`BGWLeaves.MaxDegree`; they are exported in namespace `BGWLeaves.MaxDegree.Concentration` with exactly the types of the
statements file.

Proof outline.
* `chi_zero_lower`: M7 `chi_zero_asymp` and `B_n = σ √(⌊n⌋/2)` (finite variance).
* `chi_sup_bound`: M7 `chi_window` (localization to `|k - n/μ₀| ≤ εn`), M7 `bN_bounded` (which bounds
  `B'_n P[W'_{k-n} = x]` uniformly on the window), `B'_n = σ' √(n/2)`, and the total mass `∑_q binomProb = 1/μ₀`
  of the negative binomial (`hasSum_choose_mul_geometric_of_norm_lt_one`).
* `wald_second_moment`: Wald's second identity.  `Z_k = 1{Λ(k) < m} (ω_k - 1)` are orthogonal in `L²` (independence of
  the first `k` coordinates and `ω_k`, `iIndepFun_infinitePi`), `E Z_k² = σ² P[Λ(k) < m]`, `∑_k P[Λ(k) < m] = m/μ₀` (Wald's
  first identity for `Λ`, bounded convergence), and the `L²` limit of the partial sums is `W_{T_m}` (Fatou).
* `bridge_midpoint_tight`: the strong Markov property `lem_absolueC2_k` (M6) with `f = 1{|W_{T_m}| ≥ α√n}`,
  `chi_sup_bound`, `chi_zero_lower`, Chebyshev and `wald_second_moment`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter BGW
open BGW.StableTrees BGW.LocallyFinite BGWLeaves.StableAnalysis BGWLeaves
open scoped ENNReal NNReal Topology

local notation "𝐏w[" μ "]" => Measure.infinitePi (fun _ : ℕ => μ)

namespace BGWLeaves.MaxDegree.Concentration

/-- Finite variance in the form of `HypH.finiteVariance`, from the form `Integrable (z^2) (stepLaw μ)` used by the
principles. -/
theorem memLp_of_integrable_sq_stepLaw {μ : PMF ℕ}
    (hfin : Integrable (fun z : ℤ => (z : ℝ) ^ 2) (stepLaw μ)) :
    MemLp (fun j : ℕ => (j : ℝ)) 2 μ.toMeasure := by
  have hf : Measurable (fun j : ℕ => (j : ℤ) - 1) := measurable_of_countable _
  have h1 : Integrable (fun j : ℕ => (((j : ℤ) - 1 : ℤ) : ℝ) ^ 2) μ.toMeasure := by
    unfold stepLaw at hfin
    exact (integrable_map_measure (measurable_of_countable _).aestronglyMeasurable
      hf.aemeasurable).1 hfin
  have h2 : Integrable (fun j : ℕ => 2 * (((j : ℤ) - 1 : ℤ) : ℝ) ^ 2 + 2) μ.toMeasure :=
    (h1.const_mul 2).add (integrable_const _)
  refine (memLp_two_iff_integrable_sq (measurable_of_countable _).aestronglyMeasurable).2 ?_
  refine h2.mono' (measurable_of_countable _).aestronglyMeasurable (Eventually.of_forall fun j => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  push_cast
  nlinarith [sq_nonneg ((j : ℝ) - 2)]

/-- The part of the hypothesis `𝓗` used by the providers `Concentration`, `Bridge` and `Principles`: critical,
nondegenerate, aperiodic, finite variance (no condition on the radius of convergence).  It is obtainable from the
hypotheses `hc hne hap hfin` of the principles (`HypW.of_integrable_sq`), and from `HypH` (`HypH.toW`). -/
structure HypW (μ : PMF ℕ) : Prop where
  critical : IsCritical μ
  nondegenerate : μ 1 ≠ 1
  aperiodic : Aperiodic μ
  finiteVariance : MemLp (fun j : ℕ => (j : ℝ)) 2 μ.toMeasure

theorem HypW.integrable_sq {μ : PMF ℕ} (h : HypW μ) :
    Integrable (fun z : ℤ => (z : ℝ) ^ 2) (stepLaw μ) :=
  (Scalar.memLp_step_of_memLp_offspring h.finiteVariance).integrable_sq

theorem HypW.stableDomain {μ : PMF ℕ} (h : HypW μ) : ∃ a : ℕ → ℝ, StableDomain μ 2 a :=
  ⟨_, Scalar.stableDomain_of_finiteVariance h.critical h.nondegenerate h.finiteVariance⟩

theorem HypW.of_integrable_sq {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1) (hap : Aperiodic μ)
    (hfin : Integrable (fun z : ℤ => (z : ℝ) ^ 2) (stepLaw μ)) : HypW μ :=
  ⟨hc, hne, hap, memLp_of_integrable_sq_stepLaw hfin⟩

theorem _root_.BGWLeaves.HypH.toW {μ : PMF ℕ} (h : HypH μ) : HypW μ :=
  ⟨h.critical, h.nondegenerate, h.aperiodic, h.finiteVariance⟩




/-- total mass of the negative binomial -/
private theorem binomProb_hasSum {m : ℝ} (hm0 : 0 < m) (hm1 : m < 1) {n : ℕ} (hn : 1 ≤ n) :
    HasSum (fun q : ℕ => binomProb m (n - 1 + q) (n - 1)) (1 / m) := by
  have hr : ‖1 - m‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (by linarith)]; linarith
  have h := hasSum_choose_mul_geometric_of_norm_lt_one (𝕜 := ℝ) (n - 1) hr
  have h2 := h.mul_left (m ^ (n - 1))
  have e : (1 - (1 - m)) = m := by ring
  rw [e, show n - 1 + 1 = n by omega] at h2
  convert h2 using 1
  · funext q
    unfold binomProb
    rw [show n - 1 + q - (n - 1) = q by omega, add_comm (n - 1) q]
    ring
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    field_simp
    ring

private theorem binomProb_nonneg {m : ℝ} (hm0 : 0 ≤ m) (hm1 : m ≤ 1) (p n : ℕ) : 0 ≤ binomProb m p n := by
  unfold binomProb
  have : 0 ≤ 1 - m := by linarith
  positivity

private theorem binom_window_le {m : ℝ} (hm0 : 0 < m) (hm1 : m < 1) {n : ℕ} (hn : 1 ≤ n) (S : Finset ℕ)
    (hS : ∀ k ∈ S, n ≤ k) :
    ∑ k ∈ S, binomProb m (k - 1) (n - 1) ≤ 1 / m := by
  have hs := binomProb_hasSum hm0 hm1 hn
  have hnn : ∀ q, 0 ≤ binomProb m (n - 1 + q) (n - 1) := fun q => binomProb_nonneg hm0.le hm1.le _ _
  have himg : ∑ k ∈ S, binomProb m (k - 1) (n - 1) =
      ∑ q ∈ S.image (fun k => k - n), binomProb m (n - 1 + q) (n - 1) := by
    rw [Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro k hk
      have := hS k hk
      congr 2
      omega
    · intro a ha b hb hab
      have := hS a ha
      have := hS b hb
      simp only at hab
      omega
  rw [himg]
  calc _ ≤ ∑' q, binomProb m (n - 1 + q) (n - 1) := hs.summable.sum_le_tsum _ (fun q _ => hnn q)
    _ = 1 / m := hs.tsum_eq


private theorem chi_le_one (μ : PMF ℕ) (n : ℕ) (j : ℤ) : (chi μ n j).toReal ≤ 1 := by
  have : IsProbabilityMeasure (iidWalk μ) := by unfold iidWalk; infer_instance
  exact measureReal_le_one (μ := iidWalk μ) (s := walkStopEvent n (-1 - j))

theorem mu0_bounds {μ : PMF ℕ} (h : HypW μ) : 0 < (μ 0).toReal ∧ (μ 0).toReal < 1 := by
  have h0 := h.critical.apply_zero_ne_zero h.nondegenerate
  have h1 := mu0_ne_one h.critical h.nondegenerate
  refine ⟨ENNReal.toReal_pos h0 (μ.apply_ne_top 0), ?_⟩
  have hle : (μ 0).toReal ≤ 1 := by
    have := ENNReal.toReal_mono ENNReal.one_ne_top (PMF.coe_le_one μ 0)
    simpa using this
  refine lt_of_le_of_ne hle fun heq => h1 ?_
  have := (ENNReal.toReal_eq_toReal_iff' (μ.apply_ne_top 0) ENNReal.one_ne_top).1 (by simpa using heq)
  exact this

private theorem etaNorming_form {μ : PMF ℕ} (h : HypW μ) (hnl : ¬ IsLatticeLaw (etaLaw μ)) :
    ∃ s : ℝ, 0 < s ∧ ∀ n : ℕ, norming (etaLaw μ) 2 n = s * Real.sqrt (n / 2) := by
  have hint := integrable_sq_etaLaw h.critical h.nondegenerate h.integrable_sq
  have hS := hS_of_nonLattice h.critical h.nondegenerate hnl
  obtain ⟨hattr, -, -⟩ := etaLaw_norming h.critical h.nondegenerate hS h.stableDomain
  obtain ⟨Np, hp⟩ := hattr.pos
  refine ⟨Real.sqrt (variance (etaLaw μ)), ?_, fun n => norming_of_integrable_sq hint 2 n⟩
  have := hp Np le_rfl
  rw [norming_of_integrable_sq hint] at this
  rcases (Real.sqrt_nonneg (variance (etaLaw μ))).lt_or_eq with h1 | h1
  · exact h1
  · rw [← h1] at this; simp at this

theorem chi_sup_boundW {μ : PMF ℕ} (h : HypW μ) (hnl : ¬ IsLatticeLaw (etaLaw μ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n → ∀ j : ℤ, (chi μ n j).toReal ≤ C / Real.sqrt n := by
  have hc := h.critical
  have hne := h.nondegenerate
  have hap := h.aperiodic
  have hDA := h.stableDomain
  obtain ⟨hm, hm1⟩ := mu0_bounds h
  set m0 := (μ 0).toReal with hm0
  set ε : ℝ := (1 - m0) / (4 * m0) with hε
  have hε0 : 0 < ε := by rw [hε]; have : 0 < 1 - m0 := by linarith
                         positivity
  have hε1 : ε < (1 - m0) / (2 * m0) := by
    rw [hε]; have : 0 < 1 - m0 := by linarith
    apply div_lt_div_of_pos_left this (by positivity) (by linarith)
  have hε2 : ε ≤ 1 / m0 - 1 := by
    have : 1 / m0 - 1 = (1 - m0) / m0 := by field_simp
    rw [this, hε]
    have : 0 < 1 - m0 := by linarith
    apply div_le_div_of_nonneg_left this.le hm (by linarith)
  obtain ⟨Cw, cw, hCw, hcw, hwin⟩ := chi_window hc hne hap hDA hnl hε0 (by linarith)
  obtain ⟨Cb, Nb, hb⟩ := bN_bounded hc hne hap hDA hnl hε0 hε1
  obtain ⟨s, hs, hform⟩ := etaNorming_form h hnl
  let N1 : ℕ := max 1 Nb
  have key : ∀ n : ℕ, N1 ≤ n → ∀ j : ℤ,
      (chi μ n j).toReal ≤ |Cb| / (s * Real.sqrt (n / 2)) + Cw * Real.exp (-cw * (n : ℝ) ^ (1 / 2 : ℝ)) := by
    intro n hn j
    have hn1 : 1 ≤ n := le_trans (le_max_left _ _) hn
    have hnb : Nb ≤ n := le_trans (le_max_right _ _) hn
    have hnr : (0 : ℝ) < n := by exact_mod_cast hn1
    have hsq : 0 < Real.sqrt n := Real.sqrt_pos.2 hnr
    have hB : 0 < norming (etaLaw μ) 2 n := by rw [hform]; positivity
    have hw := hwin n hn1 j
    set S := Finset.Icc (⌈(n : ℝ) / m0 - ε * n⌉.toNat) ⌊(n : ℝ) / m0 + ε * n⌋₊ with hSdef
    have hSmem : ∀ k ∈ S, ((n : ℝ) / m0 - ε * n ≤ k ∧ (k : ℝ) ≤ (n : ℝ) / m0 + ε * n) := by
      intro k hk
      rw [hSdef, Finset.mem_Icc, Int.ceil_toNat] at hk
      exact ⟨Nat.ceil_le.1 hk.1, Nat.le_floor_iff (by positivity) |>.1 hk.2⟩
    have hSn : ∀ k ∈ S, n ≤ k := by
      intro k hk
      have := (hSmem k hk).1
      have h2 : (n : ℝ) ≤ n / m0 - ε * n := by
        have : (n : ℝ) / m0 = (1 / m0) * n := by ring
        rw [this]; nlinarith
      exact_mod_cast h2.trans this
    have hterm : ∀ k ∈ S, intWalkProb (etaLaw μ) (k - n) ((n : ℤ) - 1 - j) ≤ |Cb| / norming (etaLaw μ) 2 n := by
      intro k hk
      obtain ⟨hk1, hk2⟩ := hSmem k hk
      set u : ℝ := ((k : ℝ) - n / m0) / Real.sqrt n with hu
      have hus : u * Real.sqrt n = (k : ℝ) - n / m0 := by rw [hu]; field_simp
      have hua : |u| ≤ ε * Real.sqrt n := by
        have hnn : (n : ℝ) = Real.sqrt n * Real.sqrt n := (Real.mul_self_sqrt hnr.le).symm
        rw [hu, abs_div, abs_of_pos hsq, div_le_iff₀ hsq]
        have : ε * Real.sqrt n * Real.sqrt n = ε * n := by rw [mul_assoc, ← hnn]
        rw [this]
        exact abs_le.2 ⟨by linarith, by linarith⟩
      have hrN : rN μ n u = k := by
        unfold rN
        rw [hus]
        have : (n : ℝ) / m0 + ((k : ℝ) - n / m0) = k := by ring
        rw [this]; exact Nat.floor_natCast k
      have hbd := hb n hnb u hua (j + 1)
      unfold bN at hbd
      rw [hrN, show (n : ℤ) - (j + 1) = (n : ℤ) - 1 - j by ring, abs_mul, abs_of_pos hB] at hbd
      rw [le_div_iff₀ hB]
      have h1 : intWalkProb (etaLaw μ) (k - n) ((n : ℤ) - 1 - j) * norming (etaLaw μ) 2 n ≤
          |intWalkProb (etaLaw μ) (k - n) ((n : ℤ) - 1 - j)| * norming (etaLaw μ) 2 n :=
        mul_le_mul_of_nonneg_right (le_abs_self _) hB.le
      linarith [le_abs_self Cb]
    have hsum : m0 * ∑ k ∈ S, binomProb m0 (k - 1) (n - 1) * intWalkProb (etaLaw μ) (k - n) ((n : ℤ) - 1 - j) ≤
        |Cb| / norming (etaLaw μ) 2 n := by
      have hbn : ∀ k ∈ S, 0 ≤ binomProb m0 (k - 1) (n - 1) := fun k _ => binomProb_nonneg hm.le hm1.le _ _
      calc m0 * ∑ k ∈ S, binomProb m0 (k - 1) (n - 1) * intWalkProb (etaLaw μ) (k - n) ((n : ℤ) - 1 - j)
          ≤ m0 * ∑ k ∈ S, binomProb m0 (k - 1) (n - 1) * (|Cb| / norming (etaLaw μ) 2 n) :=
            mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun k hk =>
              mul_le_mul_of_nonneg_left (hterm k hk) (hbn k hk)) hm.le
        _ = m0 * ((∑ k ∈ S, binomProb m0 (k - 1) (n - 1)) * (|Cb| / norming (etaLaw μ) 2 n)) := by
            rw [Finset.sum_mul]
        _ ≤ m0 * ((1 / m0) * (|Cb| / norming (etaLaw μ) 2 n)) := by
            apply mul_le_mul_of_nonneg_left _ hm.le
            exact mul_le_mul_of_nonneg_right (binom_window_le hm hm1 hn1 S hSn) (by positivity)
        _ = |Cb| / norming (etaLaw μ) 2 n := by field_simp
    rw [hform] at hsum
    have := (abs_le.1 hw).2
    linarith
  have hexp : ∀ n : ℕ, 1 ≤ n → Cw * Real.exp (-cw * (n : ℝ) ^ (1 / 2 : ℝ)) ≤ (Cw / cw) / Real.sqrt n := by
    intro n hn1
    have hnr : (0 : ℝ) < n := by exact_mod_cast hn1
    have hsq : 0 < Real.sqrt n := Real.sqrt_pos.2 hnr
    have hx : 0 < cw * Real.sqrt n := by positivity
    have h1 : Real.exp (-cw * (n : ℝ) ^ (1 / 2 : ℝ)) ≤ 1 / (cw * Real.sqrt n) := by
      rw [← Real.sqrt_eq_rpow, show -cw * Real.sqrt n = -(cw * Real.sqrt n) by ring, Real.exp_neg,
        ← one_div]
      apply one_div_le_one_div_of_le hx
      linarith [Real.add_one_le_exp (cw * Real.sqrt n)]
    calc Cw * Real.exp (-cw * (n : ℝ) ^ (1 / 2 : ℝ)) ≤ Cw * (1 / (cw * Real.sqrt n)) :=
          mul_le_mul_of_nonneg_left h1 hCw.le
      _ = (Cw / cw) / Real.sqrt n := by field_simp
  refine ⟨|Cb| * Real.sqrt 2 / s + Cw / cw + Real.sqrt (N1 : ℝ) + 1, by positivity, fun n hn j => ?_⟩
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hsq : 0 < Real.sqrt n := Real.sqrt_pos.2 hnr
  by_cases hN : N1 ≤ n
  · have h1 := key n hN j
    have h2 := hexp n hn
    have h3 : |Cb| / (s * Real.sqrt (n / 2)) = (|Cb| * Real.sqrt 2 / s) / Real.sqrt n := by
      rw [Real.sqrt_div hnr.le]
      have : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
      field_simp
    rw [h3] at h1
    have h4 : (|Cb| * Real.sqrt 2 / s) / Real.sqrt n + (Cw / cw) / Real.sqrt n ≤
        (|Cb| * Real.sqrt 2 / s + Cw / cw + Real.sqrt (N1 : ℝ) + 1) / Real.sqrt n := by
      rw [← add_div]
      apply div_le_div_of_nonneg_right _ hsq.le
      have := Real.sqrt_nonneg (N1 : ℝ)
      linarith
    linarith
  · rw [not_le] at hN
    have h1 := chi_le_one μ n j
    have hle : Real.sqrt n ≤ Real.sqrt (N1 : ℝ) := Real.sqrt_le_sqrt (by exact_mod_cast hN.le)
    have h5 : 1 ≤ (|Cb| * Real.sqrt 2 / s + Cw / cw + Real.sqrt (N1 : ℝ) + 1) / Real.sqrt n := by
      rw [le_div_iff₀ hsq]
      have : 0 ≤ |Cb| * Real.sqrt 2 / s + Cw / cw := by positivity
      linarith
    linarith



theorem chi_zero_lowerW {μ : PMF ℕ} (h : HypW μ) (hnl : ¬ IsLatticeLaw (etaLaw μ)) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop, c / Real.sqrt n ≤ (chi μ n 0).toReal := by
  have hm : 0 < (μ 0).toReal := ENNReal.toReal_pos (h.critical.apply_zero_ne_zero h.nondegenerate) (μ.apply_ne_top 0)
  have hlim := chi_zero_asymp h.critical h.nondegenerate h.aperiodic h.stableDomain hnl
  have hp : 0 < Scalar.stableDensity 2 0 :=
    Scalar.stableDensity_zero_pos ⟨by norm_num, le_rfl⟩
  set p := Scalar.stableDensity 2 0 with hpdef
  set σ := Real.sqrt (variance (stepLaw μ)) with hσ
  have hB : ∀ x : ℝ, normB μ 2 x = σ * Real.sqrt (⌊x⌋₊ / 2) := by
    intro x
    unfold normB
    rw [norming_of_integrable_sq h.integrable_sq]
  -- eventually the ratio is ≥ 1/2
  have hev : ∀ᶠ n : ℕ in atTop, 1 / 2 ≤ normB μ 2 ((n : ℝ) / (μ 0).toReal) * (chi μ n 0).toReal / p :=
    hlim.eventually (le_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1))
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  have hσpos : 0 < σ := by
    rcases (Real.sqrt_nonneg (variance (stepLaw μ))).lt_or_eq with h1 | h1
    · exact h1
    · exfalso
      have := hN N le_rfl
      rw [hB, show σ = 0 from h1.symm] at this
      simp at this
      linarith
  refine ⟨p * Real.sqrt (2 * (μ 0).toReal) / (2 * σ), by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop N, eventually_gt_atTop 0] with n hn hn0
  have h1 := hN n hn
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn0
  have hchi0 : 0 ≤ (chi μ n 0).toReal := ENNReal.toReal_nonneg
  -- B ≤ σ √(n/(2 μ₀))
  have hBle : normB μ 2 ((n : ℝ) / (μ 0).toReal) ≤ σ * Real.sqrt (n / (2 * (μ 0).toReal)) := by
    rw [hB]
    apply mul_le_mul_of_nonneg_left _ hσpos.le
    apply Real.sqrt_le_sqrt
    have := Nat.floor_le (show 0 ≤ (n : ℝ) / (μ 0).toReal by positivity)
    calc (⌊(n : ℝ) / (μ 0).toReal⌋₊ : ℝ) / 2 ≤ ((n : ℝ) / (μ 0).toReal) / 2 := by linarith
      _ = n / (2 * (μ 0).toReal) := by field_simp
  have hq : 0 < Real.sqrt (n / (2 * (μ 0).toReal)) := Real.sqrt_pos.2 (by positivity)
  have h2 : p / 2 ≤ normB μ 2 ((n : ℝ) / (μ 0).toReal) * (chi μ n 0).toReal := by
    have := (le_div_iff₀ hp).1 h1
    linarith
  have h3 : p / 2 ≤ σ * Real.sqrt (n / (2 * (μ 0).toReal)) * (chi μ n 0).toReal :=
    h2.trans (mul_le_mul_of_nonneg_right hBle hchi0)
  have hs : Real.sqrt (n / (2 * (μ 0).toReal)) = Real.sqrt n / Real.sqrt (2 * (μ 0).toReal) := by
    rw [Real.sqrt_div (by positivity)]
  have hsn : 0 < Real.sqrt n := Real.sqrt_pos.2 hnr
  have hs2 : 0 < Real.sqrt (2 * (μ 0).toReal) := Real.sqrt_pos.2 (by positivity)
  rw [hs] at h3
  rw [div_le_iff₀ hsn]
  have : p * Real.sqrt (2 * (μ 0).toReal) / (2 * σ) ≤ (chi μ n 0).toReal * Real.sqrt n := by
    rw [div_le_iff₀ (by positivity)]
    have e : σ * (Real.sqrt n / Real.sqrt (2 * (μ 0).toReal)) * (chi μ n 0).toReal =
        σ * ((chi μ n 0).toReal * Real.sqrt n) / Real.sqrt (2 * (μ 0).toReal) := by ring
    rw [e, le_div_iff₀ hs2] at h3
    nlinarith
  exact this



/-! ## Wald -/

def pref (m : ℕ) (ω : ℕ → ℕ) : Fin m → ℕ := fun i => ω i

def extendZ (m : ℕ) (x : Fin m → ℕ) : ℕ → ℕ := fun i => if h : i < m then x ⟨i, h⟩ else 0

theorem measurable_pref (m : ℕ) : Measurable (pref m) :=
  measurable_pi_iff.2 fun _ => measurable_pi_apply _

theorem measurable_shiftSeq (m : ℕ) : Measurable (shiftSeq m) :=
  measurable_pi_iff.2 fun _ => measurable_pi_apply _

theorem extendZ_pref_agree (m : ℕ) (ω : ℕ → ℕ) : ∀ i < m, ω i = extendZ m (pref m ω) i := by
  intro i hi
  simp [extendZ, pref, hi]

theorem dep_comp {α : Type*} (l : ℕ) (F : (ℕ → ℕ) → α)
    (hF : ∀ ω ω' : ℕ → ℕ, (∀ i < l, ω i = ω' i) → F ω = F ω') :
    F = fun ω => F (extendZ l (pref l ω)) :=
  funext fun ω => hF _ _ (extendZ_pref_agree l ω)

theorem indep_pref_shift (μ : PMF ℕ) (m : ℕ) :
    IndepFun (pref m) (shiftSeq m) (iidWalk μ) := by
  have hI : iIndepFun (fun (i : ℕ) (ω : ℕ → ℕ) => ω i) (iidWalk μ) :=
    iIndepFun_infinitePi (P := fun _ : ℕ => μ.toMeasure) (X := fun _ x => x) (fun _ => measurable_id)
  have h := hI.indepFun_set (Set.Iio m) (Set.Ici m)
    (Set.disjoint_left.2 fun x hx hx' => by simp only [Set.mem_Iio, Set.mem_Ici] at hx hx'; omega) (fun i => measurable_pi_apply i)
  have h2 := h.comp (φ := fun (s : Set.Iio m → ℕ) (i : Fin m) => s ⟨i, i.2⟩)
    (ψ := fun (s : Set.Ici m → ℕ) (i : ℕ) => s ⟨m + i, by simp⟩)
    (measurable_pi_iff.2 fun _ => measurable_pi_apply _)
    (measurable_pi_iff.2 fun _ => measurable_pi_apply _)
  exact h2

theorem map_shift (μ : PMF ℕ) (m : ℕ) : (iidWalk μ).map (shiftSeq m) = iidWalk μ := by
  have := Measure.map_infinitePi_infinitePi_of_inj (P := fun _ : ℕ => μ.toMeasure)
    (f := fun i : ℕ => m + i) (add_right_injective m)
  exact this

private theorem integral_shift (μ : PMF ℕ) (m : ℕ) {h : (ℕ → ℕ) → ℝ} (hh : Measurable h) :
    ∫ ω, h (shiftSeq m ω) ∂iidWalk μ = ∫ ω, h ω ∂iidWalk μ := by
  rw [← integral_map (measurable_shiftSeq m).aemeasurable, map_shift]
  exact hh.aestronglyMeasurable

private theorem integral_pref_shift (μ : PMF ℕ) (k : ℕ) (g : (Fin k → ℕ) → ℝ) {h : (ℕ → ℕ) → ℝ}
    (hh : Measurable h) :
    ∫ ω, g (pref k ω) * h (shiftSeq k ω) ∂iidWalk μ =
      (∫ ω, g (pref k ω) ∂iidWalk μ) * ∫ ω, h ω ∂iidWalk μ := by
  rw [(indep_pref_shift μ k).integral_fun_comp_mul_comp (measurable_pref k).aemeasurable
    (measurable_shiftSeq k).aemeasurable (measurable_of_countable g).aestronglyMeasurable
    (hh.aestronglyMeasurable)]
  rw [integral_shift μ k hh]


theorem wlc_zero (ω : ℕ → ℕ) : walkLeafCount ω 0 = 0 := by
  simp [walkLeafCount]

theorem wlc_succ (ω : ℕ → ℕ) (n : ℕ) :
    walkLeafCount ω (n + 1) = walkLeafCount ω n + if ω n = 0 then 1 else 0 := by
  unfold walkLeafCount
  rw [Finset.card_filter, Finset.card_filter, Finset.sum_range_succ]
  by_cases h : ω n = 0 <;> simp [h]

theorem wlc_congr {ω ω' : ℕ → ℕ} {q : ℕ} (h : ∀ i < q, ω i = ω' i) :
    walkLeafCount ω q = walkLeafCount ω' q := by
  induction q with
  | zero => simp [wlc_zero]
  | succ q ih =>
    rw [wlc_succ, wlc_succ, ih (fun i hi => h i (by omega)), h q (by omega)]

theorem wlc_mono (ω : ℕ → ℕ) {a b : ℕ} (h : a ≤ b) : walkLeafCount ω a ≤ walkLeafCount ω b := by
  induction b, h using Nat.le_induction with
  | base => exact le_rfl
  | succ b _ ih => rw [wlc_succ]; omega

/-- `ξ j = j - 1`, the step. -/
private noncomputable def X0 (s : ℕ → ℕ) : ℝ := (((s 0 : ℤ) - 1 : ℤ) : ℝ)

private noncomputable def Xk (k : ℕ) (ω : ℕ → ℕ) : ℝ := X0 (shiftSeq k ω)

private noncomputable def Ind (m k : ℕ) (ω : ℕ → ℕ) : ℝ := if walkLeafCount ω k < m then 1 else 0

private noncomputable def Zk (m k : ℕ) (ω : ℕ → ℕ) : ℝ := Ind m k ω * Xk k ω

private theorem Ind_dep (m k : ℕ) {ω ω' : ℕ → ℕ} (h : ∀ i < k, ω i = ω' i) : Ind m k ω = Ind m k ω' := by
  unfold Ind; rw [wlc_congr h]

private theorem measurable_X0 : Measurable X0 := by
  unfold X0
  exact (measurable_of_countable (fun j : ℤ => (j : ℝ))).comp
    ((measurable_of_countable (fun n : ℕ => (n : ℤ) - 1)).comp (measurable_pi_apply 0))

private theorem measurable_Xk (k : ℕ) : Measurable (Xk k) := measurable_X0.comp (measurable_shiftSeq k)

private theorem measurable_Ind (m k : ℕ) : Measurable (Ind m k) := by
  rw [dep_comp k (Ind m k) (fun _ _ h => Ind_dep m k h)]
  exact (measurable_of_countable (fun y : Fin k → ℕ => Ind m k (extendZ k y))).comp (measurable_pref k)

private theorem measurable_Zk (m k : ℕ) : Measurable (Zk m k) := (measurable_Ind m k).mul (measurable_Xk k)

private theorem Ind_sq (m k : ℕ) (ω : ℕ → ℕ) : Ind m k ω * Ind m k ω = Ind m k ω := by
  unfold Ind; split_ifs <;> simp

private theorem Ind_nonneg (m k : ℕ) (ω : ℕ → ℕ) : 0 ≤ Ind m k ω := by
  unfold Ind; split_ifs <;> norm_num

private theorem Ind_le_one (m k : ℕ) (ω : ℕ → ℕ) : Ind m k ω ≤ 1 := by
  unfold Ind; split_ifs <;> norm_num

private theorem measurable_c0 : Measurable (fun ω : ℕ → ℕ => (ω 0 : ℤ) - 1) :=
  (measurable_of_countable (fun k : ℕ => (k : ℤ) - 1)).comp (measurable_pi_apply 0)

private theorem law_step (μ : PMF ℕ) :
    (iidWalk μ).map (fun ω : ℕ → ℕ => (ω 0 : ℤ) - 1) = stepLaw μ := by
  have h1 : (iidWalk μ).map (fun ω : ℕ → ℕ => ω 0) = μ.toMeasure :=
    Measure.infinitePi_map_eval (fun _ : ℕ => μ.toMeasure) 0
  have := Measure.map_map (μ := iidWalk μ) (measurable_of_countable (fun k : ℕ => (k : ℤ) - 1))
    (measurable_pi_apply (0 : ℕ))
  unfold stepLaw
  rw [← h1]
  exact this.symm

private theorem X0_memLp {μ : PMF ℕ} (h : HypW μ) : MemLp X0 2 (iidWalk μ) := by
  have h1 := Scalar.memLp_step_of_memLp_offspring h.finiteVariance
  rw [← law_step μ, memLp_map_measure_iff (measurable_of_countable _).aestronglyMeasurable
    measurable_c0.aemeasurable] at h1
  exact h1

private theorem X0_integral {μ : PMF ℕ} (h : HypW μ) : ∫ ω, X0 ω ∂iidWalk μ = 0 := by
  have := integral_map (μ := iidWalk μ) (φ := fun ω : ℕ → ℕ => (ω 0 : ℤ) - 1) (f := fun z : ℤ => (z : ℝ))
    measurable_c0.aemeasurable (measurable_of_countable _).aestronglyMeasurable
  rw [law_step] at this
  have hm := mean_stepLaw h.critical
  unfold mean at hm
  rw [← hm, this]
  rfl

private theorem X0_sq_integral {μ : PMF ℕ} (h : HypW μ) :
    ∫ ω, X0 ω ^ 2 ∂iidWalk μ = StableAnalysis.variance (stepLaw μ) := by
  have := integral_map (μ := iidWalk μ) (φ := fun ω : ℕ → ℕ => (ω 0 : ℤ) - 1) (f := fun z : ℤ => (z : ℝ) ^ 2)
    measurable_c0.aemeasurable (measurable_of_countable _).aestronglyMeasurable
  rw [law_step] at this
  unfold StableAnalysis.variance
  rw [mean_stepLaw h.critical]
  simp only [sub_zero]
  rw [this]
  rfl


private theorem Xk_eq (k : ℕ) (ω : ℕ → ℕ) : Xk k ω = (((ω k : ℤ) - 1 : ℤ) : ℝ) := by
  simp [Xk, X0, shiftSeq]

private theorem Zk_dep (m : ℕ) {k l : ℕ} (hkl : k < l) {ω ω' : ℕ → ℕ} (h : ∀ i < l, ω i = ω' i) :
    Zk m k ω = Zk m k ω' := by
  unfold Zk
  rw [Ind_dep m k (fun i hi => h i (by omega)), Xk_eq, Xk_eq, h k hkl]

private theorem Ind_dep' (m : ℕ) {k l : ℕ} (hkl : k ≤ l) {ω ω' : ℕ → ℕ} (h : ∀ i < l, ω i = ω' i) :
    Ind m k ω = Ind m k ω' := Ind_dep m k (fun i hi => h i (by omega))

private noncomputable def pK (μ : PMF ℕ) (m k : ℕ) : ℝ := ∫ ω, Ind m k ω ∂iidWalk μ

private theorem pK_nonneg (μ : PMF ℕ) (m k : ℕ) : 0 ≤ pK μ m k :=
  integral_nonneg (fun ω => Ind_nonneg m k ω)

private theorem Zk_orth {μ : PMF ℕ} (h : HypW μ) (m : ℕ) {k l : ℕ} (hkl : k < l) :
    ∫ ω, Zk m k ω * Zk m l ω ∂iidWalk μ = 0 := by
  set G : (ℕ → ℕ) → ℝ := fun ω => Zk m k ω * Ind m l ω with hG
  have hGd : ∀ ω ω' : ℕ → ℕ, (∀ i < l, ω i = ω' i) → G ω = G ω' := by
    intro ω ω' hh
    simp only [hG]
    rw [Zk_dep m hkl hh, Ind_dep' m le_rfl hh]
  have hGe : G = fun ω => G (extendZ l (pref l ω)) := dep_comp l G hGd
  have e : ∀ ω, Zk m k ω * Zk m l ω = G (extendZ l (pref l ω)) * X0 (shiftSeq l ω) := by
    intro ω
    rw [← congrFun hGe ω]
    simp only [hG, Zk, Xk]
    ring
  simp_rw [e]
  rw [integral_pref_shift μ l (fun y => G (extendZ l y)) measurable_X0, X0_integral h, mul_zero]

private theorem Zk_sq {μ : PMF ℕ} (h : HypW μ) (m k : ℕ) :
    ∫ ω, Zk m k ω * Zk m k ω ∂iidWalk μ = pK μ m k * StableAnalysis.variance (stepLaw μ) := by
  have hd : Ind m k = fun ω => Ind m k (extendZ k (pref k ω)) :=
    dep_comp k (Ind m k) (fun _ _ hh => Ind_dep m k hh)
  have e : ∀ ω, Zk m k ω * Zk m k ω = Ind m k (extendZ k (pref k ω)) * (fun s => X0 s ^ 2) (shiftSeq k ω) := by
    intro ω
    rw [← congrFun hd ω]
    simp only [Zk, Xk]
    have := Ind_sq m k ω
    calc Ind m k ω * X0 (shiftSeq k ω) * (Ind m k ω * X0 (shiftSeq k ω))
        = (Ind m k ω * Ind m k ω) * X0 (shiftSeq k ω) ^ 2 := by ring
      _ = _ := by rw [this]
  simp_rw [e]
  rw [integral_pref_shift μ k (fun y => Ind m k (extendZ k y)) ((measurable_X0).pow_const 2),
    X0_sq_integral h]
  congr 1
  unfold pK
  exact (congrArg (fun f : (ℕ → ℕ) → ℝ => ∫ ω, f ω ∂iidWalk μ) hd).symm

private theorem Xk_memLp {μ : PMF ℕ} (h : HypW μ) (k : ℕ) : MemLp (Xk k) 2 (iidWalk μ) :=
  (X0_memLp h).comp_measurePreserving ⟨measurable_shiftSeq k, map_shift μ k⟩

private theorem Zk_memLp {μ : PMF ℕ} (h : HypW μ) (m k : ℕ) : MemLp (Zk m k) 2 (iidWalk μ) := by
  refine (Xk_memLp h k).of_le (measurable_Zk m k).aestronglyMeasurable (Filter.Eventually.of_forall fun ω => ?_)
  unfold Zk
  rw [norm_mul]
  have h1 : ‖Ind m k ω‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (Ind_nonneg m k ω)]; exact Ind_le_one m k ω
  calc ‖Ind m k ω‖ * ‖Xk k ω‖ ≤ 1 * ‖Xk k ω‖ := mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
    _ = ‖Xk k ω‖ := one_mul _

private theorem sum_Zk_sq {μ : PMF ℕ} (h : HypW μ) (m : ℕ) (I : Finset ℕ) :
    ∫ ω, (∑ k ∈ I, Zk m k ω) ^ 2 ∂iidWalk μ =
      StableAnalysis.variance (stepLaw μ) * ∑ k ∈ I, pK μ m k := by
  have hint : ∀ k l : ℕ, Integrable (fun ω => Zk m k ω * Zk m l ω) (iidWalk μ) := fun k l =>
    (Zk_memLp h m k).integrable_mul (Zk_memLp h m l)
  have hcc : ∀ k l : ℕ, ∫ ω, Zk m k ω * Zk m l ω ∂iidWalk μ =
      if k = l then pK μ m k * StableAnalysis.variance (stepLaw μ) else 0 := by
    intro k l
    rcases lt_trichotomy k l with hlt | heq | hgt
    · simp only [hlt.ne, ite_false]; exact Zk_orth h m hlt
    · subst heq; simp only [ite_true]; exact Zk_sq h m k
    · simp only [hgt.ne', ite_false]
      simp_rw [mul_comm (Zk m k _)]
      exact Zk_orth h m hgt
  have e : ∀ ω, (∑ k ∈ I, Zk m k ω) ^ 2 = ∑ k ∈ I, ∑ l ∈ I, Zk m k ω * Zk m l ω := by
    intro ω; rw [sq, Finset.sum_mul_sum]
  simp_rw [e]
  rw [integral_finsetSum _ (fun k _ => integrable_finsetSum _ (fun l _ => hint k l))]
  simp_rw [integral_finsetSum _ (fun l _ => hint _ l), hcc]
  simp only [Finset.sum_ite_eq]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  simp [hk, mul_comm]


private noncomputable def Ek (k : ℕ) (ω : ℕ → ℕ) : ℝ := if ω k = 0 then 1 else 0

private theorem measurable_Ek (k : ℕ) : Measurable (Ek k) := by
  have : Ek k = (fun x : ℕ => if x = 0 then (1 : ℝ) else 0) ∘ (fun ω : ℕ → ℕ => ω k) := rfl
  rw [this]
  exact (measurable_of_countable _).comp (measurable_pi_apply k)

private theorem Ek_eq (k : ℕ) (ω : ℕ → ℕ) :
    Ek k ω = (fun s : ℕ → ℕ => if s 0 = 0 then (1 : ℝ) else 0) (shiftSeq k ω) := by
  simp [Ek, shiftSeq]

private theorem integral_E0 (μ : PMF ℕ) :
    ∫ ω, (fun s : ℕ → ℕ => if s 0 = 0 then (1 : ℝ) else 0) ω ∂iidWalk μ = (μ 0).toReal := by
  have h1 : (iidWalk μ).map (fun ω : ℕ → ℕ => ω 0) = μ.toMeasure :=
    Measure.infinitePi_map_eval (fun _ : ℕ => μ.toMeasure) 0
  have := integral_map (μ := iidWalk μ) (φ := fun ω : ℕ → ℕ => ω 0)
    (f := fun x : ℕ => if x = 0 then (1 : ℝ) else 0) (measurable_pi_apply 0).aemeasurable
    (measurable_of_countable _).aestronglyMeasurable
  rw [h1] at this
  have e : (fun x : ℕ => if x = 0 then (1 : ℝ) else 0) = Set.indicator {0} (fun _ => (1 : ℝ)) := by
    funext x; by_cases hx : x = 0 <;> simp [hx]
  rw [e] at this
  show ∫ ω, (fun x : ℕ => if x = 0 then (1 : ℝ) else 0) (ω 0) ∂iidWalk μ = _
  rw [← this, integral_indicator (measurableSet_singleton 0)]
  simp [Measure.real, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton 0)]

private theorem integral_Ind_Ek (μ : PMF ℕ) (m k : ℕ) :
    ∫ ω, Ind m k ω * Ek k ω ∂iidWalk μ = pK μ m k * (μ 0).toReal := by
  have hd : Ind m k = fun ω => Ind m k (extendZ k (pref k ω)) :=
    dep_comp k (Ind m k) (fun _ _ hh => Ind_dep m k hh)
  have e : ∀ ω, Ind m k ω * Ek k ω = Ind m k (extendZ k (pref k ω)) *
      (fun s : ℕ → ℕ => if s 0 = 0 then (1 : ℝ) else 0) (shiftSeq k ω) := by
    intro ω
    rw [← congrFun hd ω, Ek_eq]
  have hm : Measurable (fun s : ℕ → ℕ => if s 0 = 0 then (1 : ℝ) else 0) :=
    (measurable_of_countable (fun x : ℕ => if x = 0 then (1 : ℝ) else 0)).comp (measurable_pi_apply 0)
  have h := integral_pref_shift μ k (fun y => Ind m k (extendZ k y)) hm
  rw [integral_E0] at h
  rw [show (fun ω => Ind m k ω * Ek k ω) = fun ω => Ind m k (extendZ k (pref k ω)) *
      (fun s : ℕ → ℕ => if s 0 = 0 then (1 : ℝ) else 0) (shiftSeq k ω) from funext e, h]
  congr 1
  unfold pK
  exact (congrArg (fun f : (ℕ → ℕ) → ℝ => ∫ ω, f ω ∂iidWalk μ) hd).symm


private theorem min_count (m N : ℕ) (ω : ℕ → ℕ) :
    ((min (walkLeafCount ω N) m : ℕ) : ℝ) = ∑ k ∈ Finset.range N, Ind m k ω * Ek k ω := by
  induction N with
  | zero => simp [wlc_zero]
  | succ N ih =>
    rw [Finset.sum_range_succ, ← ih, wlc_succ]
    unfold Ind Ek
    by_cases h1 : walkLeafCount ω N < m <;> by_cases h2 : ω N = 0 <;> simp only [h1, h2, ite_true, ite_false, mul_one, mul_zero, add_zero] <;> norm_cast <;> omega

private theorem pK_hasSum {μ : PMF ℕ} (h : HypW μ) (m : ℕ) :
    HasSum (pK μ m) ((m : ℝ) / (μ 0).toReal) := by
  have hm : 0 < (μ 0).toReal :=
    ENNReal.toReal_pos (h.critical.apply_zero_ne_zero h.nondegenerate) (μ.apply_ne_top 0)
  have hint : ∀ k : ℕ, Integrable (fun ω => Ind m k ω * Ek k ω) (iidWalk μ) := by
    intro k
    refine Integrable.of_bound ((measurable_Ind m k).mul (measurable_Ek k)).aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun ω => ?_)
    unfold Ind Ek
    split_ifs <;> simp
  have hpart : ∀ N : ℕ, ∑ k ∈ Finset.range N, pK μ m k =
      (∫ ω, ((min (walkLeafCount ω N) m : ℕ) : ℝ) ∂iidWalk μ) / (μ 0).toReal := by
    intro N
    simp_rw [min_count m N]
    rw [integral_finsetSum _ (fun k _ => hint k), Finset.sum_div]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [integral_Ind_Ek]
    field_simp
  have hlim : Tendsto (fun N : ℕ => ∫ ω, ((min (walkLeafCount ω N) m : ℕ) : ℝ) ∂iidWalk μ) atTop (𝓝 (m : ℝ)) := by
    have hmeas : ∀ N : ℕ, AEStronglyMeasurable (fun ω => ((min (walkLeafCount ω N) m : ℕ) : ℝ)) (iidWalk μ) := by
      intro N
      simp_rw [min_count m N]
      exact (Finset.measurable_sum _ (fun k _ => (measurable_Ind m k).mul (measurable_Ek k))).aestronglyMeasurable
    have := tendsto_integral_of_dominated_convergence (μ := iidWalk μ) (f := fun _ => (m : ℝ)) (fun _ => (m : ℝ)) hmeas
      (integrable_const _) (fun N => Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
        exact_mod_cast min_le_right _ _)
      (by
        filter_upwards [BGWLeaves.ae_exists_markTime μ (h.critical.apply_zero_ne_zero h.nondegenerate)] with ω hω
        obtain ⟨k, hk⟩ := hω m
        apply tendsto_const_nhds.congr'
        filter_upwards [eventually_ge_atTop k] with N hN
        have := wlc_mono ω hN
        rw [hk.1] at this
        simp [min_eq_right this])
    simpa using this
  rw [hasSum_iff_tendsto_nat_of_nonneg (pK_nonneg μ m)]
  simp_rw [hpart]
  exact hlim.div_const _


private theorem l2_limit {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (S : ℕ → Ω → ℝ) (f : Ω → ℝ) (a : ℕ → ℝ) (A : ℝ)
    (hSm : ∀ N, Measurable (S N))
    (hconv : ∀ᵐ ω ∂P, Tendsto (fun N => S N ω) atTop (𝓝 (f ω)))
    (hint : ∀ N N', N ≤ N' → Integrable (fun ω => (S N' ω - S N ω) ^ 2) P)
    (hval : ∀ N N', N ≤ N' → ∫ ω, (S N' ω - S N ω) ^ 2 ∂P = a N' - a N)
    (hint0 : ∀ N, Integrable (fun ω => (S N ω) ^ 2) P)
    (hval0 : ∀ N, ∫ ω, (S N ω) ^ 2 ∂P = a N)
    (ha : Tendsto a atTop (𝓝 A)) :
    Integrable (fun ω => (f ω) ^ 2) P ∧ ∫ ω, (f ω) ^ 2 ∂P = A := by
  have hfm : AEMeasurable f P := aemeasurable_of_tendsto_metrizable_ae (atTop : Filter ℕ) (fun N => (hSm N).aemeasurable) hconv
  -- Step A: Fatou
  have stepA : ∀ N : ℕ, ∫⁻ ω, ENNReal.ofReal ((f ω - S N ω) ^ 2) ∂P ≤ ENNReal.ofReal (A - a N) := by
    intro N
    let g : ℕ → Ω → ℝ≥0∞ := fun N' ω => ENNReal.ofReal ((S (N + N') ω - S N ω) ^ 2)
    have hgm : ∀ N', AEMeasurable (g N') P := fun N' =>
      (((hSm (N + N')).sub (hSm N)).pow_const 2).ennreal_ofReal.aemeasurable
    have h1 := lintegral_liminf_le' (u := (atTop : Filter ℕ)) hgm
    have hlimg : ∀ᵐ ω ∂P, liminf (fun N' => g N' ω) atTop = ENNReal.ofReal ((f ω - S N ω) ^ 2) := by
      filter_upwards [hconv] with ω hω
      have h2 : Tendsto (fun N' : ℕ => S (N + N') ω) atTop (𝓝 (f ω)) :=
        hω.comp (tendsto_atTop_mono (fun n => Nat.le_add_left n N) tendsto_id)
      have h3 : Tendsto (fun N' : ℕ => g N' ω) atTop (𝓝 (ENNReal.ofReal ((f ω - S N ω) ^ 2))) :=
        (ENNReal.continuous_ofReal.tendsto _).comp (((h2.sub_const (S N ω)).pow 2))
      exact h3.liminf_eq
    have hlint : ∀ N', ∫⁻ ω, g N' ω ∂P = ENNReal.ofReal (a (N + N') - a N) := by
      intro N'
      rw [← hval N (N + N') (Nat.le_add_right N N'), ofReal_integral_eq_lintegral_ofReal (hint N (N + N') (Nat.le_add_right N N'))
        (Filter.Eventually.of_forall fun ω => sq_nonneg _)]
    have hlim2 : Tendsto (fun N' : ℕ => ∫⁻ ω, g N' ω ∂P) atTop (𝓝 (ENNReal.ofReal (A - a N))) := by
      simp_rw [hlint]
      have h4 : Tendsto (fun N' : ℕ => a (N + N')) atTop (𝓝 A) :=
        ha.comp (tendsto_atTop_mono (fun n => Nat.le_add_left n N) tendsto_id)
      exact (ENNReal.continuous_ofReal.tendsto _).comp (h4.sub_const (a N))
    calc ∫⁻ ω, ENNReal.ofReal ((f ω - S N ω) ^ 2) ∂P = ∫⁻ ω, liminf (fun N' => g N' ω) atTop ∂P :=
          lintegral_congr_ae (hlimg.mono fun ω h => h.symm)
      _ ≤ liminf (fun N' => ∫⁻ ω, g N' ω ∂P) atTop := h1
      _ = ENNReal.ofReal (A - a N) := hlim2.liminf_eq
  have hmono : ∀ N, a N ≤ A := by
    intro N
    refine ge_of_tendsto ha (eventually_atTop.2 ⟨N, fun N' hN' => ?_⟩)
    have h1 := hval N N' hN'
    have : 0 ≤ ∫ ω, (S N' ω - S N ω) ^ 2 ∂P := integral_nonneg (fun ω => sq_nonneg _)
    linarith
  -- Step B: integrability and bounds
  have hvm : ∀ N, AEStronglyMeasurable (fun ω => (f ω - S N ω) ^ 2) P := fun N =>
    ((hfm.sub (hSm N).aemeasurable).pow_const 2).aestronglyMeasurable
  have stepB : ∀ N, Integrable (fun ω => (f ω - S N ω) ^ 2) P ∧ ∫ ω, (f ω - S N ω) ^ 2 ∂P ≤ A - a N := by
    intro N
    have hfin : ∫⁻ ω, ENNReal.ofReal ((f ω - S N ω) ^ 2) ∂P ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.ofReal_ne_top (stepA N)
    have hi := (lintegral_ofReal_ne_top_iff_integrable (hvm N) (Filter.Eventually.of_forall fun ω => sq_nonneg _)).1 hfin
    refine ⟨hi, ?_⟩
    have := stepA N
    rw [← ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall fun ω => sq_nonneg _)] at this
    have hA : 0 ≤ A - a N := sub_nonneg.2 (hmono N)
    exact (ENNReal.ofReal_le_ofReal_iff hA).1 this
  have hfsq : Integrable (fun ω => (f ω) ^ 2) P := by
    have h0 := (stepB 0).1
    refine Integrable.mono' (g := fun ω => 2 * (S 0 ω) ^ 2 + 2 * (f ω - S 0 ω) ^ 2)
      (((hint0 0).const_mul 2).add (h0.const_mul 2))
      ((hfm.pow_const 2).aestronglyMeasurable) (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    nlinarith [sq_nonneg (S 0 ω - (f ω - S 0 ω))]
  refine ⟨hfsq, ?_⟩
  set L := ∫ ω, (f ω) ^ 2 ∂P with hL
  have hL0 : 0 ≤ L := integral_nonneg (fun ω => sq_nonneg _)
  have haN : ∀ N, 0 ≤ a N := fun N => by rw [← hval0 N]; exact integral_nonneg (fun ω => sq_nonneg _)
  have hA0 : 0 ≤ A := ge_of_tendsto' ha haN
  have hI : ∀ δ : ℝ, 0 < δ → ∀ N, L ≤ (1 + δ) * a N + (1 + 1 / δ) * (A - a N) := by
    intro δ hδ N
    have hv := stepB N
    calc L ≤ ∫ ω, ((1 + δ) * (S N ω) ^ 2 + (1 + 1 / δ) * (f ω - S N ω) ^ 2) ∂P := by
          apply integral_mono hfsq (((hint0 N).const_mul _).add (hv.1.const_mul _))
          intro ω
          have e : (f ω) ^ 2 = (S N ω + (f ω - S N ω)) ^ 2 := by ring
          simp only [Pi.add_apply]
          rw [e]
          have : 2 * (S N ω * (f ω - S N ω)) ≤ δ * (S N ω) ^ 2 + 1 / δ * (f ω - S N ω) ^ 2 := by
            have h1 := sq_nonneg (δ * S N ω - (f ω - S N ω))
            have : 1 / δ * (f ω - S N ω) ^ 2 = (f ω - S N ω) ^ 2 / δ := by ring
            rw [this, ← sub_nonneg]
            have h2 : δ * (S N ω) ^ 2 + (f ω - S N ω) ^ 2 / δ - 2 * (S N ω * (f ω - S N ω)) =
                (δ * S N ω - (f ω - S N ω)) ^ 2 / δ := by field_simp; ring
            rw [h2]; positivity
          nlinarith
      _ = (1 + δ) * a N + (1 + 1 / δ) * ∫ ω, (f ω - S N ω) ^ 2 ∂P := by
          rw [integral_add ((hint0 N).const_mul _) (hv.1.const_mul _), integral_const_mul, integral_const_mul, hval0]
      _ ≤ (1 + δ) * a N + (1 + 1 / δ) * (A - a N) := by
          have : 0 ≤ 1 + 1 / δ := by positivity
          nlinarith [hv.2]
  have hII : ∀ δ : ℝ, 0 < δ → ∀ N, a N ≤ (1 + δ) * L + (1 + 1 / δ) * (A - a N) := by
    intro δ hδ N
    have hv := stepB N
    calc a N = ∫ ω, (S N ω) ^ 2 ∂P := (hval0 N).symm
      _ ≤ ∫ ω, ((1 + δ) * (f ω) ^ 2 + (1 + 1 / δ) * (f ω - S N ω) ^ 2) ∂P := by
          apply integral_mono (hint0 N) ((hfsq.const_mul _).add (hv.1.const_mul _))
          intro ω
          have e : S N ω = f ω - (f ω - S N ω) := by ring
          simp only [Pi.add_apply]
          rw [e]
          have : -(2 * (f ω * (f ω - S N ω))) ≤ δ * (f ω) ^ 2 + 1 / δ * (f ω - S N ω) ^ 2 := by
            have : 1 / δ * (f ω - S N ω) ^ 2 = (f ω - S N ω) ^ 2 / δ := by ring
            rw [this, ← sub_nonneg]
            have h2 : δ * (f ω) ^ 2 + (f ω - S N ω) ^ 2 / δ - -(2 * (f ω * (f ω - S N ω))) =
                (δ * f ω + (f ω - S N ω)) ^ 2 / δ := by field_simp; ring
            rw [h2]; positivity
          nlinarith
      _ = (1 + δ) * L + (1 + 1 / δ) * ∫ ω, (f ω - S N ω) ^ 2 ∂P := by
          rw [integral_add (hfsq.const_mul _) (hv.1.const_mul _), integral_const_mul, integral_const_mul]
      _ ≤ (1 + δ) * L + (1 + 1 / δ) * (A - a N) := by
          have : 0 ≤ 1 + 1 / δ := by positivity
          nlinarith [hv.2]
  have hlim : ∀ δ : ℝ, 0 < δ → Tendsto (fun N => (1 + δ) * a N + (1 + 1 / δ) * (A - a N)) atTop (𝓝 ((1 + δ) * A)) := by
    intro δ hδ
    have : Tendsto (fun N => (1 + 1 / δ) * (A - a N)) atTop (𝓝 ((1 + 1 / δ) * (A - A))) :=
      (tendsto_const_nhds.sub ha).const_mul _
    simpa using (ha.const_mul (1 + δ)).add this
  have hlim2 : ∀ δ : ℝ, 0 < δ → Tendsto (fun N => (1 + δ) * L + (1 + 1 / δ) * (A - a N)) atTop (𝓝 ((1 + δ) * L)) := by
    intro δ hδ
    have : Tendsto (fun N => (1 + 1 / δ) * (A - a N)) atTop (𝓝 ((1 + 1 / δ) * (A - A))) :=
      (tendsto_const_nhds.sub ha).const_mul _
    simpa using (tendsto_const_nhds (x := (1 + δ) * L)).add this
  have h1 : ∀ δ : ℝ, 0 < δ → L ≤ (1 + δ) * A := fun δ hδ =>
    ge_of_tendsto (hlim δ hδ) (Filter.Eventually.of_forall (hI δ hδ))
  have h2 : ∀ δ : ℝ, 0 < δ → A ≤ (1 + δ) * L := fun δ hδ =>
    le_of_tendsto_of_tendsto ha (hlim2 δ hδ) (Filter.Eventually.of_forall (hII δ hδ))
  apply le_antisymm
  · apply le_of_forall_pos_le_add
    intro ε hε
    have := h1 (ε / (A + 1)) (by positivity)
    have e : (1 + ε / (A + 1)) * A = A + ε * (A / (A + 1)) := by field_simp
    have : ε * (A / (A + 1)) ≤ ε := by
      have : A / (A + 1) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
      nlinarith
    linarith
  · apply le_of_forall_pos_le_add
    intro ε hε
    have := h2 (ε / (L + 1)) (by positivity)
    have e : (1 + ε / (L + 1)) * L = L + ε * (L / (L + 1)) := by field_simp
    have : ε * (L / (L + 1)) ≤ ε := by
      have : L / (L + 1) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
      nlinarith
    linarith


theorem walkAtMark_eq {m k : ℕ} {ω : ℕ → ℕ} (hk : IsMarkTime m ω k) : walkAtMark m ω = walkSum ω k := by
  have hex : ∃ k, IsMarkTime m ω k := ⟨k, hk⟩
  unfold walkAtMark
  simp only [hex, ↓reduceDIte]
  have := BGWLeaves.IsMarkTime.unique (Classical.choose_spec hex) hk
  rw [this]

private theorem S_eq {m k N : ℕ} {ω : ℕ → ℕ} (hk : IsMarkTime m ω k) (hN : k ≤ N) :
    ∑ i ∈ Finset.range N, Zk m i ω = ((walkAtMark m ω : ℤ) : ℝ) := by
  rw [walkAtMark_eq hk]
  have h1 : ∀ i ∈ Finset.range N, i ∉ Finset.range k → Zk m i ω = 0 := by
    intro i _ hi
    have hik : k ≤ i := not_lt.1 (fun h => hi (Finset.mem_range.2 h))
    have : m ≤ walkLeafCount ω i := by
      have := wlc_mono ω hik
      rw [hk.1] at this
      exact this
    simp [Zk, Ind, not_lt.2 this]
  rw [← Finset.sum_subset (Finset.range_mono hN) h1]
  unfold walkSum
  push_cast
  apply Finset.sum_congr rfl
  intro i hi
  have : walkLeafCount ω i < m := hk.2 i (Finset.mem_range.1 hi)
  simp [Zk, Ind, this, Xk_eq]

private theorem sumZ_memLp {μ : PMF ℕ} (h : HypW μ) (m : ℕ) (I : Finset ℕ) :
    MemLp (fun ω => ∑ k ∈ I, Zk m k ω) 2 (iidWalk μ) :=
  memLp_finsetSum I (fun k _ => Zk_memLp h m k)

private theorem wald_core {μ : PMF ℕ} (h : HypW μ) (m : ℕ) :
    Integrable (fun ω => ((walkAtMark m ω : ℤ) : ℝ) ^ 2) (iidWalk μ) ∧
    ∫ ω, ((walkAtMark m ω : ℤ) : ℝ) ^ 2 ∂(iidWalk μ) =
      StableAnalysis.variance (stepLaw μ) * (m : ℝ) / (μ 0).toReal := by
  have hm : 0 < (μ 0).toReal :=
    ENNReal.toReal_pos (h.critical.apply_zero_ne_zero h.nondegenerate) (μ.apply_ne_top 0)
  set σ2 := StableAnalysis.variance (stepLaw μ) with hσ2
  have hP : IsProbabilityMeasure (iidWalk μ) := by unfold iidWalk; infer_instance
  have key := l2_limit (iidWalk μ) (fun N ω => ∑ k ∈ Finset.range N, Zk m k ω)
    (fun ω => ((walkAtMark m ω : ℤ) : ℝ)) (fun N => σ2 * ∑ k ∈ Finset.range N, pK μ m k)
    (σ2 * ((m : ℝ) / (μ 0).toReal))
    (fun N => Finset.measurable_sum _ (fun k _ => measurable_Zk m k))
    (by
      filter_upwards [BGWLeaves.ae_exists_markTime μ (h.critical.apply_zero_ne_zero h.nondegenerate)] with ω hω
      obtain ⟨k, hk⟩ := hω m
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_ge_atTop k] with N hN
      exact (S_eq hk hN).symm)
    (fun N N' hNN' => by
      have e : ∀ ω, (∑ k ∈ Finset.range N', Zk m k ω) - ∑ k ∈ Finset.range N, Zk m k ω =
          ∑ k ∈ Finset.Ico N N', Zk m k ω := fun ω => (Finset.sum_Ico_eq_sub _ hNN').symm
      simp_rw [e]
      exact (sumZ_memLp h m _).integrable_sq)
    (fun N N' hNN' => by
      have e : ∀ ω, (∑ k ∈ Finset.range N', Zk m k ω) - ∑ k ∈ Finset.range N, Zk m k ω =
          ∑ k ∈ Finset.Ico N N', Zk m k ω := fun ω => (Finset.sum_Ico_eq_sub _ hNN').symm
      simp_rw [e]
      rw [sum_Zk_sq h m, Finset.sum_Ico_eq_sub _ hNN']
      ring)
    (fun N => (sumZ_memLp h m _).integrable_sq)
    (fun N => sum_Zk_sq h m _)
    (((pK_hasSum h m).tendsto_sum_nat).const_mul σ2)
  refine ⟨key.1, ?_⟩
  rw [key.2]
  ring

theorem wald_second_momentW {μ : PMF ℕ} (h : HypW μ) (m : ℕ) :
    ∫ ω, ((walkAtMark m ω : ℤ) : ℝ) ^ 2 ∂(Measure.infinitePi (fun _ : ℕ => μ.toMeasure)) =
      StableAnalysis.variance (stepLaw μ) * (m : ℝ) / (μ 0).toReal :=
  (wald_core h m).2


/-! ## Midpoint tightness -/

theorem isMarkTime_walkLeafTime {n : ℕ} {ω : ℕ → ℕ} {m : ℕ} (h : IsMarkTime n ω m) :
    walkLeafTime ω n = (m : ℕ∞) := by
  unfold walkLeafTime
  apply le_antisymm
  · exact iInf₂_le m h.1
  · refine le_iInf₂ fun q hq => ?_
    have : m ≤ q := by
      by_contra hlt
      have := h.2 q (not_le.1 hlt)
      omega
    exact_mod_cast this

theorem walkLeafTime_ne_top_iff {n : ℕ} {ω : ℕ → ℕ} :
    walkLeafTime ω n ≠ ⊤ ↔ ∃ m, IsMarkTime n ω m := by
  constructor
  · intro h
    by_contra hne
    apply h
    have : ¬ ∃ m, walkLeafCount ω m = n := by
      rw [← BGWLeaves.exists_isMarkTime_iff]; exact hne
    unfold walkLeafTime
    simp only [iInf_eq_top]
    intro m hm
    exact absurd ⟨m, hm⟩ this
  · rintro ⟨m, hm⟩
    rw [isMarkTime_walkLeafTime hm]
    exact ENat.natCast_ne_top m

theorem bridgeAtMark_eq (n : ℕ) : bridgeAtMark n = walkStopEvent n (-1) := by
  ext ω
  constructor
  · rintro ⟨k, hk, hs⟩
    refine ⟨by rw [isMarkTime_walkLeafTime hk]; exact ENat.natCast_ne_top _, ?_⟩
    simpa only [walkStopPos, isMarkTime_walkLeafTime hk, ENat.toNat_natCast] using hs
  · rintro ⟨hne, hs⟩
    obtain ⟨k, hk⟩ := walkLeafTime_ne_top_iff.1 hne
    refine ⟨k, hk, ?_⟩
    simpa only [walkStopPos, isMarkTime_walkLeafTime hk, ENat.toNat_natCast] using hs

theorem walkSum_congr {ω ω' : ℕ → ℕ} {q : ℕ} (h : ∀ i < q, ω i = ω' i) :
    walkSum ω q = walkSum ω' q := by
  unfold walkSum
  exact Finset.sum_congr rfl fun i hi => by rw [h i (Finset.mem_range.1 hi)]

theorem isMarkTime_congr {k m : ℕ} {ω ω' : ℕ → ℕ} (h : ∀ i < m, ω i = ω' i) :
    IsMarkTime k ω m ↔ IsMarkTime k ω' m := by
  unfold IsMarkTime
  rw [wlc_congr h]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun q hq => by rw [← wlc_congr (fun i hi => h i (by omega))]; exact h2 q hq⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun q hq => by rw [wlc_congr (fun i hi => h i (by omega))]; exact h2 q hq⟩

/-- the midpoint event -/
def midEvent (k : ℕ) (t : ℝ) : Set (ℕ → ℕ) :=
  {ω | ∃ k', IsMarkTime k ω k' ∧ t ≤ |(walkSum ω k' : ℝ)|}

theorem measurableSet_midEvent (k : ℕ) (t : ℝ) : MeasurableSet (midEvent k t) := by
  have : midEvent k t = ⋃ k' : ℕ, {ω | IsMarkTime k ω k' ∧ t ≤ |(walkSum ω k' : ℝ)|} := by
    ext ω; simp [midEvent]
  rw [this]
  refine MeasurableSet.iUnion fun k' => ?_
  have hd : ∀ ω ω' : ℕ → ℕ, (∀ i < k', ω i = ω' i) →
      ((IsMarkTime k ω k' ∧ t ≤ |(walkSum ω k' : ℝ)|) ↔ (IsMarkTime k ω' k' ∧ t ≤ |(walkSum ω' k' : ℝ)|)) := by
    intro ω ω' hh
    rw [isMarkTime_congr hh, walkSum_congr hh]
  have hS : {ω : ℕ → ℕ | IsMarkTime k ω k' ∧ t ≤ |(walkSum ω k' : ℝ)|} =
      pref k' ⁻¹' {y | IsMarkTime k (extendZ k' y) k' ∧ t ≤ |(walkSum (extendZ k' y) k' : ℝ)|} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_preimage]
    exact hd _ _ (extendZ_pref_agree k' ω)
  rw [hS]
  exact measurable_pref k' (Set.to_countable _).measurableSet

theorem getLastD_stopPath (ω : ℕ → ℕ) (k : ℕ) :
    (walkStopPath ω k).getLastD 0 = walkStopPos ω k := by
  unfold walkStopPath walkStopPos
  rw [List.range_succ, List.map_append]
  simp

private theorem indicator_stopPath {k : ℕ} {t : ℝ} (ht : 0 < t) (ω : ℕ → ℕ) :
    (if t ≤ |(((walkStopPath ω k).getLastD 0 : ℤ) : ℝ)| then (1 : ℝ≥0∞) else 0) =
      (midEvent k t).indicator 1 ω := by
  rw [getLastD_stopPath]
  by_cases hex : ∃ k', IsMarkTime k ω k'
  · obtain ⟨k', hk'⟩ := hex
    have hpos : walkStopPos ω k = walkSum ω k' := by
      simp only [walkStopPos, isMarkTime_walkLeafTime hk', ENat.toNat_natCast]
    rw [hpos]
    by_cases hle : t ≤ |(walkSum ω k' : ℝ)|
    · have : ω ∈ midEvent k t := ⟨k', hk', hle⟩
      simp [hle, this]
    · have : ω ∉ midEvent k t := by
        rintro ⟨k'', hk'', hle'⟩
        have := BGWLeaves.IsMarkTime.unique hk' hk''
        subst this
        exact hle hle'
      simp [hle, this]
  · have hnot : ω ∉ midEvent k t := fun ⟨k', hk', _⟩ => hex ⟨k', hk'⟩
    have htop : walkLeafTime ω k = ⊤ := by
      by_contra hne
      exact hex (walkLeafTime_ne_top_iff.1 hne)
    have h0 : walkStopPos ω k = 0 := by simp [walkStopPos, htop, walkSum]
    rw [h0]
    simp [hnot, not_le.2 ht]

private theorem walkAtMark_mem {k : ℕ} {t : ℝ} {ω : ℕ → ℕ} (hω : ω ∈ midEvent k t) :
    t ^ 2 ≤ ((walkAtMark k ω : ℤ) : ℝ) ^ 2 ∨ t < 0 := by
  obtain ⟨k', hk', hle⟩ := hω
  rw [walkAtMark_eq hk']
  by_cases ht : t < 0
  · exact Or.inr ht
  · left
    rw [not_lt] at ht
    exact (sq_le_sq₀ ht (abs_nonneg _)).2 hle |>.trans_eq (sq_abs _)

private theorem midpoint_bound {μ : PMF ℕ} (h : HypW μ) {C1 c : ℝ} (hC1 : 0 < C1) (hc : 0 < c)
    (hsup : ∀ n : ℕ, 1 ≤ n → ∀ j : ℤ, (chi μ n j).toReal ≤ C1 / Real.sqrt n)
    {n k : ℕ} (hkn : k < n) (hlow : c / Real.sqrt n ≤ (chi μ n 0).toReal) {α : ℝ} (hα : 0 < α) :
    ((𝐏w[μ.toMeasure])[|bridgeAtMark n]).real (midEvent k (α * Real.sqrt n)) ≤
      (C1 / Real.sqrt ((n - k : ℕ) : ℝ)) / (c / Real.sqrt n) *
        (StableAnalysis.variance (stepLaw μ) * (k : ℝ) / (μ 0).toReal / (α ^ 2 * n)) := by
  have h0 : μ 0 ≠ 0 := h.critical.apply_zero_ne_zero h.nondegenerate
  have hnr : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hsq : 0 < Real.sqrt n := Real.sqrt_pos.2 hnr
  have hkn' : 0 < ((n - k : ℕ) : ℝ) := by exact_mod_cast (show 0 < n - k by omega)
  have hsq' : 0 < Real.sqrt ((n - k : ℕ) : ℝ) := Real.sqrt_pos.2 hkn'
  set t : ℝ := α * Real.sqrt n with ht
  have htpos : 0 < t := by positivity
  set E := midEvent k t with hE
  have : IsProbabilityMeasure (iidWalk μ) := by unfold iidWalk; infer_instance
  -- Markov
  have hmark : (iidWalk μ).real E ≤ StableAnalysis.variance (stepLaw μ) * (k : ℝ) / (μ 0).toReal / (α ^ 2 * n) := by
    have hw := wald_core h k
    have hm := mul_meas_ge_le_integral_of_nonneg (μ := iidWalk μ)
      (f := fun ω => ((walkAtMark k ω : ℤ) : ℝ) ^ 2) (Filter.Eventually.of_forall fun ω => sq_nonneg _) hw.1 (α ^ 2 * n)
    rw [hw.2] at hm
    have hsub : (iidWalk μ).real E ≤ (iidWalk μ).real {ω | α ^ 2 * n ≤ ((walkAtMark k ω : ℤ) : ℝ) ^ 2} := by
      apply measureReal_mono _ (measure_ne_top _ _)
      intro ω hω
      rcases walkAtMark_mem hω with h1 | h1
      · have : t ^ 2 = α ^ 2 * n := by
          rw [ht, mul_pow, Real.sq_sqrt hnr.le]
        simpa only [Set.mem_ofPred_eq, this] using h1
      · exact absurd h1 (not_lt.2 htpos.le)
    rw [le_div_iff₀ (by positivity)]
    calc (iidWalk μ).real E * (α ^ 2 * n) ≤ (iidWalk μ).real {ω | α ^ 2 * n ≤ ((walkAtMark k ω : ℤ) : ℝ) ^ 2} * (α ^ 2 * n) :=
          mul_le_mul_of_nonneg_right hsub (by positivity)
      _ = (α ^ 2 * n) * (iidWalk μ).real {ω | α ^ 2 * n ≤ ((walkAtMark k ω : ℤ) : ℝ) ^ 2} := by ring
      _ ≤ _ := hm
  rw [bridgeAtMark_eq]
  have hkey : ∫⁻ ω, (midEvent k t).indicator 1 ω ∂((iidWalk μ)[|walkStopEvent n (-1)]) =
      ∫⁻ ω, (midEvent k t).indicator 1 ω * (chi μ (n - k) (walkStopPos ω k) / chi μ n 0) ∂iidWalk μ := by
    have := BGWLeaves.lem_absolueC2_k h0 hkn
      (fun l : List ℤ => if t ≤ |((l.getLastD 0 : ℤ) : ℝ)| then (1 : ℝ≥0∞) else 0)
    simpa only [indicator_stopPath htpos] using this
  rw [lintegral_indicator_one (measurableSet_midEvent k t)] at hkey
  set K : ℝ≥0∞ := ENNReal.ofReal (C1 / Real.sqrt ((n - k : ℕ) : ℝ)) / ENNReal.ofReal (c / Real.sqrt n) with hK
  have hKne : K ≠ ⊤ := ENNReal.div_ne_top ENNReal.ofReal_ne_top
    (ENNReal.ofReal_pos.2 (by positivity)).ne'
  have hratio : ∀ ω, chi μ (n - k) (walkStopPos ω k) / chi μ n 0 ≤ K := by
    intro ω
    apply ENNReal.div_le_div
    · rw [ENNReal.le_ofReal_iff_toReal_le (chi_ne_top _ _ _) (by positivity)]
      exact hsup (n - k) (by omega) _
    · rw [ENNReal.ofReal_le_iff_le_toReal (chi_ne_top _ _ _)]
      exact hlow
  have h1 : ((iidWalk μ)[|walkStopEvent n (-1)]) E ≤ (iidWalk μ) E * K := by
    rw [hkey]
    calc ∫⁻ ω, E.indicator 1 ω * (chi μ (n - k) (walkStopPos ω k) / chi μ n 0) ∂iidWalk μ
        ≤ ∫⁻ ω, E.indicator 1 ω * K ∂iidWalk μ := lintegral_mono fun ω => mul_le_mul' le_rfl (hratio ω)
      _ = (∫⁻ ω, E.indicator 1 ω ∂iidWalk μ) * K := lintegral_mul_const' _ _ hKne
      _ = (iidWalk μ) E * K := by rw [lintegral_indicator_one (measurableSet_midEvent k t)]
  have h2 : (((iidWalk μ)[|walkStopEvent n (-1)]) E).toReal ≤ (iidWalk μ).real E * K.toReal := by
    calc _ ≤ ((iidWalk μ) E * K).toReal := ENNReal.toReal_mono (ENNReal.mul_ne_top (measure_ne_top _ _) hKne) h1
      _ = _ := by rw [ENNReal.toReal_mul]; rfl
  have hKr : K.toReal = (C1 / Real.sqrt ((n - k : ℕ) : ℝ)) / (c / Real.sqrt n) := by
    rw [hK, ENNReal.toReal_div, ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_ofReal (by positivity)]
  rw [hKr] at h2
  show (((iidWalk μ)[|walkStopEvent n (-1)]) E).toReal ≤ _
  calc _ ≤ _ := h2
    _ = (C1 / Real.sqrt ((n - k : ℕ) : ℝ)) / (c / Real.sqrt n) * (iidWalk μ).real E := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hmark (by positivity)

theorem bridge_midpoint_tightW {μ : PMF ℕ} (h : HypW μ) (hnl : ¬ IsLatticeLaw (etaLaw μ))
    {m : ℕ → ℕ} (hm : ∀ n, n / 2 ≤ m n ∧ m n ≤ (n + 1) / 2) :
    ∀ ε : ℝ, 0 < ε → ∃ α : ℝ, 0 < α ∧ ∀ᶠ n : ℕ in atTop,
      ((𝐏w[μ.toMeasure])[|bridgeAtMark n]).real
        {ω | ∃ k, IsMarkTime (m n) ω k ∧ α * Real.sqrt n ≤ |(walkSum ω k : ℝ)|} < ε := by
  intro ε hε
  obtain ⟨C1, hC1, hsup⟩ := chi_sup_boundW h hnl
  obtain ⟨c, hc, hlow⟩ := chi_zero_lowerW h hnl
  obtain ⟨N0, hN0⟩ := eventually_atTop.1 hlow
  have hm0 : 0 < (μ 0).toReal :=
    ENNReal.toReal_pos (h.critical.apply_zero_ne_zero h.nondegenerate) (μ.apply_ne_top 0)
  set σ2 := StableAnalysis.variance (stepLaw μ) with hσ2def
  have hσ2 : 0 ≤ σ2 := integral_nonneg (fun z => sq_nonneg _)
  set B : ℝ := C1 * Real.sqrt 3 * σ2 / (c * (μ 0).toReal) with hBdef
  have hB : 0 ≤ B := by positivity
  have hα : 0 < Real.sqrt (2 * (B + 1) / ε) := Real.sqrt_pos.2 (by positivity)
  refine ⟨Real.sqrt (2 * (B + 1) / ε), hα, ?_⟩
  filter_upwards [eventually_ge_atTop (max N0 3)] with n hn
  have hn3 : 3 ≤ n := le_trans (le_max_right _ _) hn
  have hnN0 : N0 ≤ n := le_trans (le_max_left _ _) hn
  have hk := hm n
  have hkn : m n < n := by omega
  have hb := midpoint_bound h hC1 hc hsup hkn (hN0 n hnN0) hα
  set α := Real.sqrt (2 * (B + 1) / ε) with hαdef
  have hα2 : α ^ 2 = 2 * (B + 1) / ε := Real.sq_sqrt (by positivity)
  have hnr : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hsq : 0 < Real.sqrt n := Real.sqrt_pos.2 hnr
  have hnk : (n : ℝ) ≤ 3 * ((n - m n : ℕ) : ℝ) := by exact_mod_cast (show n ≤ 3 * (n - m n) by omega)
  have hkpos : 0 < ((n - m n : ℕ) : ℝ) := by exact_mod_cast (show 0 < n - m n by omega)
  have hsq' : 0 < Real.sqrt ((n - m n : ℕ) : ℝ) := Real.sqrt_pos.2 hkpos
  have hr : Real.sqrt n ≤ Real.sqrt 3 * Real.sqrt ((n - m n : ℕ) : ℝ) := by
    rw [← Real.sqrt_mul (by norm_num)]
    exact Real.sqrt_le_sqrt hnk
  have hK : (C1 / Real.sqrt ((n - m n : ℕ) : ℝ)) / (c / Real.sqrt n) ≤ C1 * Real.sqrt 3 / c := by
    rw [div_div_div_eq, div_le_div_iff₀ (by positivity) hc]
    have : C1 * Real.sqrt n * c ≤ C1 * (Real.sqrt 3 * Real.sqrt ((n - m n : ℕ) : ℝ)) * c := by
      apply mul_le_mul_of_nonneg_right _ hc.le
      exact mul_le_mul_of_nonneg_left hr hC1.le
    nlinarith
  have hmn : (m n : ℝ) ≤ n := by exact_mod_cast hkn.le
  have hD : σ2 * (m n : ℝ) / (μ 0).toReal / (α ^ 2 * n) ≤ σ2 / (μ 0).toReal / α ^ 2 := by
    have hpos : 0 < α ^ 2 * n := by positivity
    calc σ2 * (m n : ℝ) / (μ 0).toReal / (α ^ 2 * n) = (σ2 / (μ 0).toReal * (m n : ℝ)) / (α ^ 2 * n) := by ring
      _ ≤ (σ2 / (μ 0).toReal * (n : ℝ)) / (α ^ 2 * n) :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hmn (by positivity)) hpos.le
      _ = σ2 / (μ 0).toReal / α ^ 2 := by field_simp
  have hfin : (C1 / Real.sqrt ((n - m n : ℕ) : ℝ)) / (c / Real.sqrt n) *
      (σ2 * (m n : ℝ) / (μ 0).toReal / (α ^ 2 * n)) ≤ B / α ^ 2 := by
    have e : B / α ^ 2 = C1 * Real.sqrt 3 / c * (σ2 / (μ 0).toReal / α ^ 2) := by
      rw [hBdef]; field_simp
    rw [e]
    exact mul_le_mul hK hD (by positivity) (by positivity)
  have hlt : B / α ^ 2 < ε := by
    rw [hα2, div_div_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith
  exact lt_of_le_of_lt (hb.trans hfin) hlt

/-! ## The frozen exports (types with `h : HypH μ`) -/

theorem chi_sup_bound {μ : PMF ℕ} (h : HypH μ) (hnl : ¬ IsLatticeLaw (etaLaw μ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n → ∀ j : ℤ, (chi μ n j).toReal ≤ C / Real.sqrt n :=
  chi_sup_boundW h.toW hnl

theorem chi_zero_lower {μ : PMF ℕ} (h : HypH μ) (hnl : ¬ IsLatticeLaw (etaLaw μ)) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop, c / Real.sqrt n ≤ (chi μ n 0).toReal :=
  chi_zero_lowerW h.toW hnl

theorem wald_second_moment {μ : PMF ℕ} (h : HypH μ) (m : ℕ) :
    ∫ ω, ((walkAtMark m ω : ℤ) : ℝ) ^ 2 ∂(Measure.infinitePi (fun _ : ℕ => μ.toMeasure)) =
      StableAnalysis.variance (stepLaw μ) * (m : ℝ) / (μ 0).toReal :=
  wald_second_momentW h.toW m

theorem bridge_midpoint_tight {μ : PMF ℕ} (h : HypH μ) (hnl : ¬ IsLatticeLaw (etaLaw μ))
    {m : ℕ → ℕ} (hm : ∀ n, n / 2 ≤ m n ∧ m n ≤ (n + 1) / 2) :
    ∀ ε : ℝ, 0 < ε → ∃ α : ℝ, 0 < α ∧ ∀ᶠ n : ℕ in atTop,
      ((𝐏w[μ.toMeasure])[|bridgeAtMark n]).real
        {ω | ∃ k, IsMarkTime (m n) ω k ∧ α * Real.sqrt n ≤ |(walkSum ω k : ℝ)|} < ε :=
  bridge_midpoint_tightW h.toW hnl hm

end BGWLeaves.MaxDegree.Concentration
