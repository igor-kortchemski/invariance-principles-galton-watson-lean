module

public import BGWLeaves.Conditioning.Defs
import BGWLeaves.LeafMass.Arithmetic
import BGWLeaves.StableAnalysis.TransformConvergence
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Inputs of Proposition 4.4(ii): size and leaf tails

Proved inputs of Proposition 4.4(ii): `sizeGe_poly_lower`, `sizeWindow_small`,
`norming_leafCutoff_ratio`, `leafTail_asymp`, and `leafGe_sizeGe_ratio`, with the
types stated in `BGWLeaves.Conditioning`. The assembly `prop_passage_ii` is in `PassageII`.

The private Karamata helpers are adapted from the module `StableAnalysis.SizeTail`.
The lattice specialization cancels the local factor `g`; the leaf-event
series identity and interpolation between neighboring lattice thresholds give the
sharp leaf tail at every integer threshold.

-/

@[expose] public section

namespace BGWLeaves.Conditioning.LeafTail

open MeasureTheory ProbabilityTheory Filter Asymptotics BGW
open BGW.StableTrees BGW.LocallyFinite BGWLeaves.StableAnalysis
open scoped ENNReal Topology

/-- A positive power dominates the slowly varying part of any stable norming. -/
private theorem norming_power_small {μ : PMF ℕ} {θ : ℝ} {a : ℕ → ℝ}
    (ha : StableDomain μ θ a) {η : ℝ} (hη : 0 < η) :
    Tendsto (fun n : ℕ => a n * (n : ℝ) ^ (-(1 / θ) - η)) atTop (𝓝 0) := by
  have hslow : SlowlyVarying (fun x : ℝ => |a ⌊x⌋₊ / x ^ (1 / θ)|) := by
    intro c hc
    simpa only [← abs_div, abs_one] using ((Scalar.slowlyVarying ha) c hc).abs
  have hs := slow_rpow_neg_mul_tendsto_zero
    (continuous_abs.measurable.comp (measurable_floor_ratio a (1 / θ)))
    (fun _ _ => abs_nonneg _) hslow hη
  apply (hs.comp tendsto_natCast_atTop_atTop).congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  simp only [Function.comp_apply, Nat.floor_natCast]
  rw [abs_of_nonneg (div_nonneg (ha.pos n hn).le (Real.rpow_nonneg hnpos.le _))]
  rw [Real.rpow_sub hnpos]
  simp only [Real.rpow_neg hnpos.le]
  ring

/-- Polynomial lower bound for the size tail, with the exponent of `sizeGe_poly_lower`. -/
theorem sizeGe_poly_lower {μ : PMF ℕ} {θ : ℝ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hap : Aperiodic μ) (hDA : ∃ a, StableDomain μ θ a) {η : ℝ} (hη : 0 < η) :
    ∃ c₃ : ℝ, 0 < c₃ ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      c₃ * (n : ℝ) ^ (-(1 / θ) - η) ≤ (bienaymeLaw μ.toMeasure).real (sizeGeEvent n) := by
  have _ := hc
  have _ := hne
  obtain ⟨a, ha⟩ := hDA
  have hL : 0 < θ * Scalar.stableDensity θ 0 :=
    mul_pos (by linarith [ha.alpha_mem.1]) (Scalar.stableDensity_zero_pos ha.alpha_mem)
  refine ⟨θ * Scalar.stableDensity θ 0 / 2, half_pos hL, ?_⟩
  have hlo := (sizeTail_asymp ha hap).eventually
    (eventually_gt_nhds (show θ * Scalar.stableDensity θ 0 / 2 <
      θ * Scalar.stableDensity θ 0 by linarith))
  have hsmall := (norming_power_small ha hη).eventually
    (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num))
  apply eventually_atTop.1
  filter_upwards [hlo, hsmall, eventually_ge_atTop 1] with n hn hs hn1
  have hp := Real.rpow_pos_of_pos (show (0 : ℝ) < n by exact_mod_cast hn1)
    (-(1 / θ) - η)
  have hP : 0 ≤ (bienaymeLaw μ.toMeasure).real (sizeGeEvent n) := measureReal_nonneg
  nlinarith

/-- The real cutoff, divided by its index, tends to the leaf frequency. -/
private theorem realCutoff_ratio (μ : PMF ℕ) :
    Tendsto (fun n : ℕ => ((μ 0).toReal * n - (n : ℝ) ^ (3 / 4 : ℝ)) / n)
      atTop (𝓝 (μ 0).toReal) := by
  have ht : Tendsto (fun n : ℕ => (μ 0).toReal - (n : ℝ) ^ (-(1 / 4 : ℝ)))
      atTop (𝓝 ((μ 0).toReal - 0)) := tendsto_const_nhds.sub
    ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 4)).comp
      tendsto_natCast_atTop_atTop)
  simp only [sub_zero] at ht
  apply ht.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  rw [sub_div, mul_div_cancel_right₀ _ hnpos.ne', ← Real.rpow_sub_one hnpos.ne']
  norm_num

private theorem leafCutoff_ratio {μ : PMF ℕ} (h0 : 0 < (μ 0).toReal) :
    Tendsto (fun n : ℕ => (leafCutoff μ n : ℝ) / n) atTop (𝓝 (μ 0).toReal) := by
  have hr := realCutoff_ratio μ
  have hpos := hr.eventually (eventually_gt_nhds h0)
  have hu := hr.add tendsto_one_div_atTop_nhds_zero_nat
  rw [add_zero] at hu
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hr hu
  · filter_upwards [eventually_ge_atTop 1] with n hn
    exact div_le_div_of_nonneg_right (Nat.le_ceil _) (Nat.cast_nonneg n)
  · filter_upwards [hpos, eventually_ge_atTop 1] with n hn hn1
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
    have he : 0 ≤ (μ 0).toReal * n - (n : ℝ) ^ (3 / 4 : ℝ) :=
      ((div_pos_iff_of_pos_right hnpos).1 hn).le
    rw [← add_div]
    exact div_le_div_of_nonneg_right (Nat.ceil_lt_add_one he).le hnpos.le

/-- Regular variation of the canonical norming at the leaf cutoff. -/
theorem norming_leafCutoff_ratio {μ : PMF ℕ} {θ : ℝ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hDA : ∃ a, StableDomain μ θ a) :
    Tendsto (fun n : ℕ => norming (stepLaw μ) θ (leafCutoff μ n) / norming (stepLaw μ) θ n)
      atTop (𝓝 ((μ 0).toReal ^ (1 / θ))) := by
  obtain ⟨a, ha⟩ := hDA
  have := isProbabilityMeasure_stepLaw μ
  have hcan := locallimit_i (stepLaw μ) (stepLaw_lt_neg_one μ) (integrable_stepLaw hc)
    ⟨a, by rw [mean_stepLaw hc]; exact stableDomain_isStableAttracted ha⟩
  have h0 : 0 < (μ 0).toReal :=
    ENNReal.toReal_pos (LeafMass.Arithmetic.mu_zero_ne_zero hc hne) (μ.apply_ne_top 0)
  exact TransformConvergence.tendsto_div_of_tendsto_div' (stepLaw μ) hcan hcan h0
    (leafCutoff_ratio h0)


/-- The reciprocal slowly varying factor also loses to every positive power. -/
private theorem inverse_norming_power_small {μ : PMF ℕ} {θ : ℝ} {a : ℕ → ℝ}
    (ha : StableDomain μ θ a) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => (n : ℝ) ^ (1 / θ - ε) / a n) atTop (𝓝 0) := by
  have hslow : SlowlyVarying (fun x : ℝ => |a ⌊x⌋₊ / x ^ (1 / θ)|) := by
    intro c hc
    simpa only [← abs_div, abs_one] using ((Scalar.slowlyVarying ha) c hc).abs
  have hinv : SlowlyVarying (fun x : ℝ => |a ⌊x⌋₊ / x ^ (1 / θ)|⁻¹) := by
    intro c hc
    simpa only [div_eq_mul_inv, mul_inv_rev, inv_inv, inv_one, mul_comm] using
      ((hslow c hc).inv₀ one_ne_zero)
  have hs := slow_rpow_neg_mul_tendsto_zero
    ((continuous_abs.measurable.comp (measurable_floor_ratio a (1 / θ))).inv)
    (fun _ _ => inv_nonneg.2 (abs_nonneg _)) hinv hε
  apply (hs.comp tendsto_natCast_atTop_atTop).congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  change (n : ℝ) ^ (-ε) * |a ⌊(n : ℝ)⌋₊ / (n : ℝ) ^ (1 / θ)|⁻¹ = _
  rw [Nat.floor_natCast, abs_of_nonneg (div_nonneg (ha.pos n hn).le (Real.rpow_nonneg hnpos.le _)),
    inv_div, Real.rpow_sub hnpos, Real.rpow_neg hnpos.le]
  ring

/-- A window of width `D n^(3/4)` contains at most that width plus one integer sizes. -/
private theorem sizeWindow_bound {μ : PMF ℕ} {μ0 s K : ℝ} (hμ0 : 0 < μ0)
    (hs : 0 < s) (hK : 0 ≤ K) {N : ℕ}
    (hp : ∀ p : ℕ, N ≤ p → (bienaymeLaw μ.toMeasure).real (sizeEvent p) ≤
      K * (p : ℝ) ^ (-s)) :
    ∀ᶠ n : ℕ in atTop, (bienaymeLaw μ.toMeasure).real (sizeWindow μ0 n) ≤
      ((1 / μ0 + 1) + 1) * K * (2 : ℝ) ^ s * (n : ℝ) ^ (3 / 4 - s) := by
  let D := 1 / μ0 + 1
  have hD : 0 < D := by dsimp [D]; positivity
  have hwidth := ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 4)).comp
    tendsto_natCast_atTop_atTop).const_mul D
  rw [mul_zero] at hwidth
  have he := hwidth.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  filter_upwards [he, eventually_ge_atTop (max (2 * N) 1)] with n hn hnN
  have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hnN
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hpow : (n : ℝ) ^ (3 / 4 : ℝ) / n = (n : ℝ) ^ (-(1 / 4 : ℝ)) := by
    rw [← Real.rpow_sub_one hn0.ne']; norm_num
  have hw : D * (n : ℝ) ^ (3 / 4 : ℝ) ≤ (n : ℝ) / 2 := by
    have hh : D * ((n : ℝ) ^ (3 / 4 : ℝ) / n) < 1 / 2 := by rwa [hpow]
    rw [← mul_div_assoc] at hh
    have := (div_lt_iff₀ hn0).1 hh
    linarith
  let l : ℕ := ⌈(n : ℝ) - D * (n : ℝ) ^ (3 / 4 : ℝ)⌉₊
  have hl : l ≤ n := by
    apply Nat.ceil_le.2
    nlinarith [Real.rpow_nonneg hn0.le (3 / 4 : ℝ)]
  have hlR : (n : ℝ) - D * (n : ℝ) ^ (3 / 4 : ℝ) ≤ l := Nat.le_ceil _
  have hcard : ((Finset.Icc l n).card : ℝ) ≤ (D + 1) * (n : ℝ) ^ (3 / 4 : ℝ) := by
    rw [Nat.card_Icc, Nat.cast_sub (by omega : l ≤ n + 1), Nat.cast_add, Nat.cast_one]
    have hpow1 : (1 : ℝ) ≤ (n : ℝ) ^ (3 / 4 : ℝ) :=
      Real.one_le_rpow (by exact_mod_cast hn1) (by norm_num)
    nlinarith
  have hsub : sizeWindow μ0 n ⊆ ⋃ p ∈ Finset.Icc l n, sizeEvent p := by
    rintro T ⟨p, hp, hpl, hpn⟩
    exact Set.mem_iUnion.2 ⟨p, Set.mem_iUnion.2 ⟨Finset.mem_Icc.2
      ⟨Nat.ceil_le.2 (by simpa [D] using hpl), hpn⟩, hp⟩⟩
  have hterm : ∀ p ∈ Finset.Icc l n,
      (bienaymeLaw μ.toMeasure).real (sizeEvent p) ≤
        K * ((2 : ℝ) ^ s * (n : ℝ) ^ (-s)) := by
    intro p hp'
    obtain ⟨hpl, hpn⟩ := Finset.mem_Icc.1 hp'
    have hpR : (n : ℝ) / 2 ≤ p := by
      have : (l : ℝ) ≤ p := by exact_mod_cast hpl
      linarith
    have hpN : N ≤ p := by
      have : 2 * N ≤ n := le_trans (le_max_left _ _) hnN
      have : (2 : ℝ) * N ≤ n := by exact_mod_cast this
      have : (N : ℝ) ≤ p := by linarith
      exact_mod_cast this
    refine (hp p hpN).trans (mul_le_mul_of_nonneg_left ?_ hK)
    calc (p : ℝ) ^ (-s) ≤ ((n : ℝ) / 2) ^ (-s) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) hpR (by linarith)
      _ = (2 : ℝ) ^ s * (n : ℝ) ^ (-s) := by
        rw [Real.div_rpow hn0.le (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
        simp only [div_inv_eq_mul]; ring
  calc
    (bienaymeLaw μ.toMeasure).real (sizeWindow μ0 n) ≤
        (bienaymeLaw μ.toMeasure).real (⋃ p ∈ Finset.Icc l n, sizeEvent p) :=
      measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ ∑ p ∈ Finset.Icc l n, (bienaymeLaw μ.toMeasure).real (sizeEvent p) :=
      measureReal_biUnion_finset_le _ _
    _ ≤ ((Finset.Icc l n).card : ℝ) * (K * ((2 : ℝ) ^ s * (n : ℝ) ^ (-s))) := by
      simpa using Finset.sum_le_sum hterm
    _ ≤ ((D + 1) * (n : ℝ) ^ (3 / 4 : ℝ)) *
        (K * ((2 : ℝ) ^ s * (n : ℝ) ^ (-s))) := by
      exact mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = _ := by
      dsimp [D]
      rw [Real.rpow_sub hn0, Real.rpow_neg hn0.le]
      ring

/-- The size window is negligible with the polynomial weight of `sizeWindow_small`. -/
theorem sizeWindow_small {μ : PMF ℕ} {θ : ℝ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hap : Aperiodic μ) (hDA : ∃ a, StableDomain μ θ a) {η : ℝ} (hη0 : 0 < η) (hη1 : η < 1 / 4) :
    Tendsto (fun n : ℕ => (n : ℝ) ^ (1 / θ + η) *
      (bienaymeLaw μ.toMeasure).real (sizeWindow (μ 0).toReal n)) atTop (𝓝 0) := by
  obtain ⟨a, ha⟩ := hDA
  let ε : ℝ := (1 / 4 - η) / 2
  have hε : 0 < ε := by dsimp [ε]; linarith
  let s : ℝ := 1 + 1 / θ - ε
  have hθ : 0 < θ := by linarith [ha.alpha_mem.1]
  have hs : 0 < s := by
    have hr : 0 < 1 / θ := by positivity
    dsimp [s, ε]
    linarith
  have hpoint := (sizeProb_asymp ha hap).mul (inverse_norming_power_small ha hε)
  rw [mul_zero] at hpoint
  have hpoint' : Tendsto (fun n : ℕ => (n : ℝ) ^ s *
      (bienaymeLaw μ.toMeasure).real (sizeEvent n)) atTop (𝓝 0) := by
    apply hpoint.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have han := (ha.pos n hn).ne'
    dsimp [s]
    simp only [Real.rpow_sub hn0, Real.rpow_add hn0, Real.rpow_one]
    field_simp
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hpoint'.eventually
    (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)))
  have hbound : ∀ p : ℕ, max N 1 ≤ p →
      (bienaymeLaw μ.toMeasure).real (sizeEvent p) ≤ 1 * (p : ℝ) ^ (-s) := by
    intro p hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (le_trans (le_max_right _ _) hp)
    have hh := hN p (le_trans (le_max_left _ _) hp)
    rw [Real.rpow_neg hp0.le, one_mul]
    simpa only [one_div] using
      ((le_div_iff₀ (Real.rpow_pos_of_pos hp0 s)).2
        (show (bienaymeLaw μ.toMeasure).real (sizeEvent p) * (p : ℝ) ^ s ≤ 1 by nlinarith [hh]))
  have h0 : 0 < (μ 0).toReal :=
    ENNReal.toReal_pos (LeafMass.Arithmetic.mu_zero_ne_zero hc hne) (μ.apply_ne_top 0)
  have hw := sizeWindow_bound h0 hs (by norm_num : (0 : ℝ) ≤ 1) hbound
  let C : ℝ := ((1 / (μ 0).toReal + 1) + 1) * (2 : ℝ) ^ s
  have hneg : 0 < -(1 / θ + η + (3 / 4 - s)) := by dsimp [s, ε]; linarith
  have ht := ((tendsto_rpow_neg_atTop hneg).comp tendsto_natCast_atTop_atTop).const_mul C
  rw [mul_zero] at ht
  apply squeeze_zero' (Eventually.of_forall (fun n => mul_nonneg (Real.rpow_nonneg (by positivity) _)
    measureReal_nonneg)) (g := fun n : ℕ => C * (n : ℝ) ^ (1 / θ + η + (3 / 4 - s))) ?_
    (by simpa only [neg_neg, Function.comp_apply] using ht)
  filter_upwards [hw, eventually_ge_atTop 1] with n hn hn1
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hh := mul_le_mul_of_nonneg_left hn (Real.rpow_nonneg (Nat.cast_nonneg n) (1 / θ + η))
  convert hh using 1
  simp only [C, mul_one, Real.rpow_add hn0]
  ring

/-! Private Karamata machinery, adapted from `StableAnalysis.SizeTail`. -/

open Set Finset

private theorem powerBlock_integral_bounds {ρ : ℝ} (hρ : 0 < ρ)
    {n : ℕ} (hn : 1 ≤ n) :
    (∫ x in (n : ℝ)..(2 * n : ℕ), x ^ (-1 - ρ)) ≤
        ∑ q ∈ Finset.Ico n (2 * n), (q : ℝ) ^ (-1 - ρ) ∧
      ∑ q ∈ Finset.Ico n (2 * n), ((q + 1 : ℕ) : ℝ) ^ (-1 - ρ) ≤
        ∫ x in (n : ℝ)..(2 * n : ℕ), x ^ (-1 - ρ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have h2n : n ≤ 2 * n := by omega
  have hant : AntitoneOn (fun x : ℝ => x ^ (-1 - ρ)) (Set.Icc (n : ℝ) (2 * n : ℕ)) := by
    intro x hx y hy hxy
    apply Real.rpow_le_rpow_of_nonpos (lt_of_lt_of_le hnR hx.1) hxy
    linarith
  have hint : IntegrableOn (fun x : ℝ => x ^ (-1 - ρ)) (Set.Icc (n : ℝ) (2 * n : ℕ)) :=
    hant.integrableOn_isCompact isCompact_Icc
  constructor
  · exact hant.integral_le_sum_Ico h2n
  · exact hant.sum_le_integral_Ico h2n

private theorem powerBlock_sum_bounds {ρ : ℝ} (hρ : 0 < ρ)
    {n : ℕ} (hn : 1 ≤ n) :
    (∫ x in (n : ℝ)..(2 * n : ℕ), x ^ (-1 - ρ)) ≤
        ∑ q ∈ Finset.Ico n (2 * n), (q : ℝ) ^ (-1 - ρ) ∧
      ∑ q ∈ Finset.Ico n (2 * n), (q : ℝ) ^ (-1 - ρ) ≤
        (∫ x in (n : ℝ)..(2 * n : ℕ), x ^ (-1 - ρ)) + (n : ℝ) ^ (-1 - ρ) := by
  have h2n : n ≤ 2 * n := by omega
  obtain ⟨hleft, hright⟩ := powerBlock_integral_bounds hρ hn
  let g : ℕ → ℝ := fun q => (q : ℝ) ^ (-1 - ρ)
  have htel : (∑ q ∈ Finset.Ico n (2 * n), (g (q + 1) - g q)) =
      g (2 * n) - g n := by
    rw [Finset.sum_Ico_eq_sub _ h2n, Finset.sum_range_sub, Finset.sum_range_sub]
    simp [g]
  have hshift : (∑ q ∈ Finset.Ico n (2 * n), g (q + 1)) -
      (∑ q ∈ Finset.Ico n (2 * n), g q) = g (2 * n) - g n := by
    calc _ = ∑ q ∈ Finset.Ico n (2 * n), (g (q + 1) - g q) := by rw [Finset.sum_sub_distrib]
      _ = _ := htel
  have hsum : (∑ q ∈ Finset.Ico n (2 * n), g q) =
      (∑ q ∈ Finset.Ico n (2 * n), g (q + 1)) + g n - g (2 * n) := by
    linarith
  have hnonneg : 0 ≤ g (2 * n) := by positivity
  constructor
  · simpa [g] using hleft
  · have hr : (∑ q ∈ Finset.Ico n (2 * n), g (q + 1)) ≤
        ∫ x in (n : ℝ)..(2 * n : ℕ), x ^ (-1 - ρ) := by
      simpa [g] using hright
    rw [hsum]
    linarith

private theorem powerBlock_sum_tendsto {ρ : ℝ} (hρ : 0 < ρ) :
    Tendsto (fun n : ℕ => (n : ℝ) ^ ρ *
      ∑ q ∈ Finset.Ico n (2 * n), (q : ℝ) ^ (-1 - ρ)) atTop
      (𝓝 ((1 - (2 : ℝ) ^ (-ρ)) / ρ)) := by
  let c : ℝ := (1 - (2 : ℝ) ^ (-ρ)) / ρ
  have hlo : ∀ n : ℕ, 1 ≤ n → c ≤ (n : ℝ) ^ ρ *
      ∑ q ∈ Finset.Ico n (2 * n), (q : ℝ) ^ (-1 - ρ) := by
    intro n hn
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hn2n : (n : ℝ) ≤ 2 * n := by nlinarith
    have hnot0 : (0 : ℝ) ∉ Set.uIcc (n : ℝ) (2 * n : ℝ) := by
      rw [Set.uIcc_of_le hn2n]
      simp only [Set.mem_Icc, not_and_or]
      exact Or.inl (by linarith)
    have hInt := integral_rpow (a := (n : ℝ)) (b := (2 * n : ℝ))
      (r := -1 - ρ) (Or.inr ⟨by linarith, hnot0⟩)
    have hInt' : (∫ x in (n : ℝ)..(2 * n : ℝ), x ^ (-1 - ρ)) =
        (n : ℝ) ^ (-ρ) * c := by
      rw [hInt, show -1 - ρ + 1 = -ρ by ring,
        Real.mul_rpow (by norm_num) hnR.le]
      dsimp [c]
      ring
    have hmul : (n : ℝ) ^ ρ * (n : ℝ) ^ (-ρ) = 1 := by
      rw [← Real.rpow_add hnR, show ρ + -ρ = 0 by ring, Real.rpow_zero]
    have hScaled : (n : ℝ) ^ ρ *
        (∫ x in (n : ℝ)..(2 * n : ℝ), x ^ (-1 - ρ)) = c := by
      rw [hInt', ← mul_assoc, hmul, one_mul]
    have hEndpoints : ((2 * n : ℕ) : ℝ) = (2 : ℝ) * n := by norm_cast
    have hIntEq : (∫ x in (n : ℝ)..(2 * n : ℝ), x ^ (-1 - ρ)) =
        ∫ x in (n : ℝ)..(2 * n : ℕ), x ^ (-1 - ρ) := by rw [hEndpoints]
    have hScaledNat : (n : ℝ) ^ ρ *
        (∫ x in (n : ℝ)..(2 * n : ℕ), x ^ (-1 - ρ)) = c := by
      rw [← hIntEq, hScaled]
    have hB := powerBlock_sum_bounds hρ hn
    have hmulnonneg : 0 ≤ (n : ℝ) ^ ρ := Real.rpow_nonneg (by positivity) _
    calc c = (n : ℝ) ^ ρ *
          (∫ x in (n : ℝ)..(2 * n : ℕ), x ^ (-1 - ρ)) := hScaledNat.symm
      _ ≤ (n : ℝ) ^ ρ * ∑ q ∈ Finset.Ico n (2 * n), (q : ℝ) ^ (-1 - ρ) :=
        mul_le_mul_of_nonneg_left hB.1 hmulnonneg
  have hup : ∀ n : ℕ, 1 ≤ n → (n : ℝ) ^ ρ *
      ∑ q ∈ Finset.Ico n (2 * n), (q : ℝ) ^ (-1 - ρ) ≤ c + 1 / n := by
    intro n hn
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hn2n : (n : ℝ) ≤ 2 * n := by nlinarith
    have hnot0 : (0 : ℝ) ∉ Set.uIcc (n : ℝ) (2 * n : ℝ) := by
      rw [Set.uIcc_of_le hn2n]
      simp only [Set.mem_Icc, not_and_or]
      exact Or.inl (by linarith)
    have hInt := integral_rpow (a := (n : ℝ)) (b := (2 * n : ℝ))
      (r := -1 - ρ) (Or.inr ⟨by linarith, hnot0⟩)
    have hInt' : (∫ x in (n : ℝ)..(2 * n : ℝ), x ^ (-1 - ρ)) =
        (n : ℝ) ^ (-ρ) * c := by
      rw [hInt, show -1 - ρ + 1 = -ρ by ring,
        Real.mul_rpow (by norm_num) hnR.le]
      dsimp [c]
      ring
    have hmul : (n : ℝ) ^ ρ * (n : ℝ) ^ (-ρ) = 1 := by
      rw [← Real.rpow_add hnR, show ρ + -ρ = 0 by ring, Real.rpow_zero]
    have herr : (n : ℝ) ^ ρ * (n : ℝ) ^ (-1 - ρ) = 1 / n := by
      rw [← Real.rpow_add hnR, show ρ + (-1 - ρ) = -1 by ring,
        Real.rpow_neg hnR.le, Real.rpow_one]
      simp
    have hScaled : (n : ℝ) ^ ρ *
        (∫ x in (n : ℝ)..(2 * n : ℝ), x ^ (-1 - ρ)) = c := by
      rw [hInt', ← mul_assoc, hmul, one_mul]
    have hEndpoints : ((2 * n : ℕ) : ℝ) = (2 : ℝ) * n := by norm_cast
    have hIntEq : (∫ x in (n : ℝ)..(2 * n : ℝ), x ^ (-1 - ρ)) =
        ∫ x in (n : ℝ)..(2 * n : ℕ), x ^ (-1 - ρ) := by rw [hEndpoints]
    have hScaledNat : (n : ℝ) ^ ρ *
        (∫ x in (n : ℝ)..(2 * n : ℕ), x ^ (-1 - ρ)) = c := by
      rw [← hIntEq, hScaled]
    have hB := powerBlock_sum_bounds hρ hn
    have hmulnonneg : 0 ≤ (n : ℝ) ^ ρ := Real.rpow_nonneg (by positivity) _
    calc (n : ℝ) ^ ρ * ∑ q ∈ Finset.Ico n (2 * n), (q : ℝ) ^ (-1 - ρ)
        ≤ (n : ℝ) ^ ρ *
          ((∫ x in (n : ℝ)..(2 * n : ℕ), x ^ (-1 - ρ)) + (n : ℝ) ^ (-1 - ρ)) :=
          mul_le_mul_of_nonneg_left hB.2 hmulnonneg
      _ = c + 1 / n := by rw [mul_add, hScaledNat, herr]
  have hlow : ∀ᶠ n : ℕ in atTop, c ≤ (n : ℝ) ^ ρ *
      ∑ q ∈ Finset.Ico n (2 * n), (q : ℝ) ^ (-1 - ρ) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact hlo n hn
  have hhigh : ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ ρ *
      ∑ q ∈ Finset.Ico n (2 * n), (q : ℝ) ^ (-1 - ρ) ≤ c + 1 / n := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact hup n hn
  have hupper : Tendsto (fun n : ℕ => c + 1 / (n : ℝ)) atTop (𝓝 c) := by
    have hzero : Tendsto (fun n : ℕ => (1 : ℝ) / n) atTop (𝓝 0) :=
      tendsto_one_div_atTop_nhds_zero_nat
    have hconst : Tendsto (fun _ : ℕ => c) atTop (𝓝 c) := tendsto_const_nhds
    have h := hconst.add hzero
    simpa using h
  simpa [c] using
    (tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper hlow hhigh)

private theorem powerTerm_cancel {ρ : ℝ} {n q : ℕ} (hn : 0 < n) (hq : 0 < q) :
    (n : ℝ) ^ ρ * (q : ℝ) ^ (-1 - ρ) *
      ((q : ℝ) * ((q : ℝ) / n) ^ ρ) = 1 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  rw [Real.div_rpow hqR.le hnR.le, show -1 - ρ = -1 + -ρ by ring,
    Real.rpow_add hqR, Real.rpow_neg hqR.le, Real.rpow_one]
  field_simp
  rw [← Real.rpow_add hqR, show -ρ + ρ = 0 by ring, Real.rpow_zero]

private theorem inverseBlock_tendsto {ρ : ℝ} {a : ℕ → ℝ}
    (hρ : 0 < ρ) (hrv : RegularlyVaryingSeq ρ a) (hmono : Monotone a)
    (hpos : ∀ n : ℕ, 1 ≤ n → 0 < a n) :
    Tendsto (fun n : ℕ => a n *
      ∑ q ∈ Finset.Ico n (2 * n), 1 / ((q : ℝ) * a q)) atTop
      (𝓝 ((1 - (2 : ℝ) ^ (-ρ)) / ρ)) := by
  let P : ℕ → ℝ := fun n =>
    ∑ q ∈ Finset.Ico n (2 * n), (n : ℝ) ^ ρ * (q : ℝ) ^ (-1 - ρ)
  let B : ℕ → ℝ := fun n =>
    a n * ∑ q ∈ Finset.Ico n (2 * n), 1 / ((q : ℝ) * a q)
  let R : ℕ → ℝ := fun n => B n / P n
  have hP : Tendsto P atTop (𝓝 ((1 - (2 : ℝ) ^ (-ρ)) / ρ)) := by
    have h := powerBlock_sum_tendsto hρ
    simpa [P, Finset.mul_sum] using h
  have hPpos : ∀ n : ℕ, 1 ≤ n → 0 < P n := by
    intro n hn
    have hnpos : 0 < n := by omega
    have hsum : 0 < ∑ q ∈ Finset.Ico n (2 * n),
        (n : ℝ) ^ ρ * (q : ℝ) ^ (-1 - ρ) := by
      apply Finset.sum_pos'
      · intro q hq
        have hqmem := Finset.mem_Ico.mp hq
        have hqpos : 0 < q := by omega
        positivity
      · refine ⟨n, Finset.mem_Ico.mpr ⟨le_rfl, by omega⟩, ?_⟩
        have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
        have hpow : 0 < (n : ℝ) ^ ρ := Real.rpow_pos_of_pos hnR _
        have hterm : 0 < (n : ℝ) ^ (-1 - ρ) := Real.rpow_pos_of_pos hnR _
        exact mul_pos hpow hterm
    dsimp [P]
    exact hsum
  have hR : Tendsto R atTop (𝓝 1) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    let δ : ℝ := min (ε / 4) (1 / 2)
    have hδ : 0 < δ := lt_min (by linarith) (by norm_num)
    have hδ1 : δ < 1 := by dsimp [δ]; have := min_le_right (ε / 4) (1 / 2); linarith
    have hδsmall : 2 * δ < ε := by
      dsimp [δ]
      have := min_le_left (ε / 4) (1 / 2)
      linarith
    obtain ⟨N, hN⟩ := eventually_atTop.1
      (hrv.eventually_ratio_bounds hmono hpos hρ.le hδ)
    refine ⟨max N 1, fun n hn => ?_⟩
    have hnN : N ≤ n := le_trans (le_max_left _ _) hn
    have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
    have hnpos : 0 < n := by omega
    have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
    have haN : 0 < a n := hpos n hn1
    have hpN : 0 < P n := hPpos n hn1
    have hloc := hN n hnN
    have hlowBlock : (1 / (1 + δ)) * P n ≤ B n := by
      dsimp [P, B]
      rw [Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_le_sum
      intro q hq
      have hqn : n ≤ q := (Finset.mem_Ico.mp hq).1
      have hq2 : q ≤ 2 * n := (Finset.mem_Ico.mp hq).2.le
      have hqpos : 0 < q := by omega
      have hqR : (0 : ℝ) < q := by exact_mod_cast hqpos
      have haq : 0 < a q := hpos q (by omega)
      have hx : 0 < ((q : ℝ) / n) ^ ρ := by positivity
      obtain ⟨hUpper, _⟩ := hloc q hqn hq2
      have hcancel := powerTerm_cancel (ρ := ρ) hnpos hqpos
      have hden : 0 < 1 + δ := by linarith
      have hkernel : 0 < (q : ℝ) * a q := mul_pos hqR haq
      have hdiv : ((n : ℝ) ^ ρ * (q : ℝ) ^ (-1 - ρ)) / (1 + δ) ≤
          a n / ((q : ℝ) * a q) := by
        rw [div_le_div_iff₀ hden hkernel]
        calc (n : ℝ) ^ ρ * (q : ℝ) ^ (-1 - ρ) * ((q : ℝ) * a q)
            = ((n : ℝ) ^ ρ * (q : ℝ) ^ (-1 - ρ)) * (q * a q) := by ring
        _ ≤ ((n : ℝ) ^ ρ * (q : ℝ) ^ (-1 - ρ)) *
            (q * ((1 + δ) * ((q : ℝ) / n) ^ ρ * a n)) := by
              exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hUpper hqR.le)
                (by positivity)
        _ = a n * (1 + δ) := by
              calc _ = (1 + δ) * a n * ((n : ℝ) ^ ρ * (q : ℝ) ^ (-1 - ρ) *
                  (q * ((q : ℝ) / n) ^ ρ)) := by ring
                _ = (1 + δ) * a n := by rw [hcancel]; ring
                _ = a n * (1 + δ) := by ring
      simpa [div_eq_mul_inv, one_div, mul_comm] using hdiv
    have hhighBlock : B n ≤ (1 / (1 - δ)) * P n := by
      dsimp [P, B]
      rw [Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_le_sum
      intro q hq
      have hqn : n ≤ q := (Finset.mem_Ico.mp hq).1
      have hq2 : q ≤ 2 * n := (Finset.mem_Ico.mp hq).2.le
      have hqpos : 0 < q := by omega
      have hqR : (0 : ℝ) < q := by exact_mod_cast hqpos
      have haq : 0 < a q := hpos q (by omega)
      have hx : 0 < ((q : ℝ) / n) ^ ρ := by positivity
      obtain ⟨_, hLower⟩ := hloc q hqn hq2
      have hcancel := powerTerm_cancel (ρ := ρ) hnpos hqpos
      have hden : 0 < 1 - δ := by linarith
      have hkernel : 0 < (q : ℝ) * a q := mul_pos hqR haq
      have hdiv : a n / ((q : ℝ) * a q) ≤
          ((n : ℝ) ^ ρ * (q : ℝ) ^ (-1 - ρ)) / (1 - δ) := by
        rw [div_le_div_iff₀ hkernel hden]
        calc a n * (1 - δ) = (1 - δ) * a n *
              ((n : ℝ) ^ ρ * (q : ℝ) ^ (-1 - ρ) *
                ((q : ℝ) * ((q : ℝ) / n) ^ ρ)) := by
                  rw [hcancel]
                  ring
          _ = ((n : ℝ) ^ ρ * (q : ℝ) ^ (-1 - ρ) * q) *
                ((1 - δ) * ((q : ℝ) / n) ^ ρ * a n) := by ring
          _ ≤ ((n : ℝ) ^ ρ * (q : ℝ) ^ (-1 - ρ) * q) * a q :=
                mul_le_mul_of_nonneg_left hLower (by positivity)
          _ = (n : ℝ) ^ ρ * (q : ℝ) ^ (-1 - ρ) * ((q : ℝ) * a q) := by ring
      simpa [div_eq_mul_inv, one_div, mul_comm] using hdiv
    have hRlo : 1 - δ ≤ R n := by
      have hcoeff : 1 - δ ≤ 1 / (1 + δ) := by
        rw [le_div_iff₀ (by linarith)]
        nlinarith [sq_nonneg δ]
      dsimp [R]
      exact le_trans hcoeff ((le_div_iff₀ hpN).2 hlowBlock)
    have hRhi : R n ≤ 1 + 2 * δ := by
      have hcoeff : 1 / (1 - δ) ≤ 1 + 2 * δ := by
        rw [div_le_iff₀ (by linarith)]
        have hδhalf : δ ≤ 1 / 2 := by dsimp [δ]; exact min_le_right _ _
        have hmul : 0 ≤ δ * (1 - 2 * δ) := mul_nonneg (le_of_lt hδ) (by linarith)
        nlinarith
      dsimp [R]
      exact le_trans ((div_le_iff₀ hpN).2 hhighBlock) hcoeff
    rw [Real.dist_eq]
    have habs : |R n - 1| ≤ 2 * δ := by
      rw [abs_le]
      constructor <;> linarith
    exact lt_of_le_of_lt habs hδsmall
  have hmul := hR.mul hP
  have hcongr : (fun n : ℕ => R n * P n) =ᶠ[atTop] B := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hnpos := hPpos n hn
    dsimp [R]
    field_simp [hnpos.ne']
  have hB : Tendsto B atTop
      (𝓝 ((1 - (2 : ℝ) ^ (-ρ)) / ρ)) := by
    have hmul' : Tendsto (fun n : ℕ => R n * P n) atTop
        (𝓝 ((1 - (2 : ℝ) ^ (-ρ)) / ρ)) := by simpa using hmul
    exact hmul'.congr' hcongr
  simpa [B] using hB

private noncomputable def inverseKernel {a : ℕ → ℝ} (q : ℕ) : ℝ :=
  1 / ((q : ℝ) * a q)

private noncomputable def inverseKernelTail {a : ℕ → ℝ} (n : ℕ) : ℝ :=
  ∑' k : ℕ, inverseKernel (a := a) (n + k)

private theorem inverseKernelTail_split {a : ℕ → ℝ}
    (hs : Summable (inverseKernel (a := a))) (n : ℕ) :
    inverseKernelTail (a := a) n =
      (∑ q ∈ Finset.Ico n (2 * n), inverseKernel (a := a) q) +
        inverseKernelTail (a := a) (2 * n) := by
  have hshift : Summable (fun k : ℕ => inverseKernel (a := a) (n + k)) :=
    by simpa [Nat.add_comm] using (summable_nat_add_iff n).2 hs
  have hsplit := hshift.sum_add_tsum_nat_add n
  have hfinite : (∑ k ∈ Finset.range n, inverseKernel (a := a) (n + k)) =
      ∑ q ∈ Finset.Ico n (2 * n), inverseKernel (a := a) q := by
    rw [Finset.range_eq_Ico]
    conv_lhs => arg 2; ext k; rw [Nat.add_comm n k]
    rw [Finset.sum_Ico_add' (inverseKernel (a := a)) 0 n (c := n)]
    simp [two_mul]
  have htail : (∑' k : ℕ, inverseKernel (a := a) (n + (k + n))) =
      inverseKernelTail (a := a) (2 * n) := by
    congr 1
    funext k
    congr 1
    omega
  calc
    inverseKernelTail (a := a) n =
        (∑ k ∈ Finset.range n, inverseKernel (a := a) (n + k)) +
          (∑' k : ℕ, inverseKernel (a := a) (n + (k + n))) := hsplit.symm
    _ = (∑ q ∈ Finset.Ico n (2 * n), inverseKernel (a := a) q) +
          inverseKernelTail (a := a) (2 * n) := by rw [hfinite, htail]

private theorem inverseKernelTail_shift_eq {a : ℕ → ℝ} (n : ℕ) :
    inverseKernelTail (a := a) (n + 1) =
      ∑' q : ℕ, (Set.Ioi n).indicator (inverseKernel (a := a)) q := by
  let e : ℕ ≃ {q : ℕ // q ∈ Set.Ioi n} :=
    { toFun := fun k => ⟨n + 1 + k, by simp; omega⟩
      invFun := fun q => q.1 - (n + 1)
      left_inv := by intro k; simp
      right_inv := by
        intro q
        apply Subtype.ext
        have hqmem : n < q.1 := q.2
        have hq : n + 1 ≤ q.1 := by omega
        change n + 1 + (q.1 - (n + 1)) = q.1
        exact Nat.add_sub_of_le hq }
  calc
    inverseKernelTail (a := a) (n + 1) =
        ∑' k : ℕ, inverseKernel (a := a) ((n + 1) + k) := rfl
    _ = ∑' q : {q : ℕ // q ∈ Set.Ioi n}, inverseKernel (a := a) q.1 := by
      simpa [e, Nat.add_assoc] using (e.tsum_eq (fun q : {q : ℕ // q ∈ Set.Ioi n} =>
        inverseKernel (a := a) q.1))
    _ = ∑' q : ℕ, (Set.Ioi n).indicator (inverseKernel (a := a)) q :=
      tsum_subtype (Set.Ioi n) (inverseKernel (a := a))

private theorem inverseKernelTail_bound {ρ : ℝ} {a : ℕ → ℝ}
    (hρ : 0 < ρ) (hrv : RegularlyVaryingSeq ρ a) (hmono : Monotone a)
    (hpos : ∀ n : ℕ, 1 ≤ n → 0 < a n) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      a n * inverseKernelTail (a := a) n ≤ C + 1 := by
  obtain ⟨C, hC, hbound⟩ := hrv.karamata_tail_tsum hmono hpos hρ
  refine ⟨C, hC, fun n hn => ?_⟩
  have hshift := inverseKernelTail_shift_eq (a := a) n
  have htail : inverseKernelTail (a := a) (n + 1) ≤ C / a n := by
    calc inverseKernelTail (a := a) (n + 1) =
          ∑' q : ℕ, (Set.Ioi n).indicator (inverseKernel (a := a)) q := hshift
      _ = ∑' q : ℕ, (Set.Ioi n).indicator (fun q => 1 / ((q : ℝ) * a q)) q := by
          congr 1
      _ ≤ C / a n := hbound n hn
  have hsum := hrv.summable_inv_mul hmono hpos hρ
  have hshiftSum : Summable (fun k : ℕ => inverseKernel (a := a) (n + k)) :=
    by simpa [inverseKernel, Nat.add_comm] using (summable_nat_add_iff n).2 hsum
  have hdecomp : inverseKernelTail (a := a) n =
      inverseKernel (a := a) n + inverseKernelTail (a := a) (n + 1) := by
    dsimp [inverseKernelTail]
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      hshiftSum.sum_add_tsum_nat_add 1 |>.symm
  have han : 0 < a n := hpos n hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hfirst : a n * inverseKernel (a := a) n = 1 / n := by
    dsimp [inverseKernel]
    field_simp
  have hmulTail : a n * inverseKernelTail (a := a) (n + 1) ≤ C := by
    calc a n * inverseKernelTail (a := a) (n + 1)
        ≤ a n * (C / a n) := mul_le_mul_of_nonneg_left htail han.le
      _ = C := by field_simp
  have hle : a n * inverseKernelTail (a := a) n ≤ 1 / n + C := by
    rw [hdecomp, mul_add, hfirst]
    exact add_le_add_right hmulTail _
  have hone : (1 : ℝ) / n ≤ 1 := by
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    simpa using one_div_le_one_div_of_le (show (0 : ℝ) < 1 by norm_num) hn1
  calc a n * inverseKernelTail (a := a) n
      ≤ 1 / n + C := hle
    _ ≤ C + 1 := by linarith

-- A bounded affine recurrence with a strict contraction determines its limit.
private theorem limsup_le_of_dyadic_recursion
    {F B R : ℕ → ℝ} {c r : ℝ}
    (hb : atTop.IsBoundedUnder (· ≤ ·) F)
    (hl : atTop.IsBoundedUnder (· ≥ ·) F)
    (hB : Tendsto B atTop (𝓝 c)) (hR : Tendsto R atTop (𝓝 r))
    (hr : r < 1) (hRpos : ∀ᶠ n in atTop, 0 ≤ R n)
    (heq : ∀ᶠ n in atTop, F n = B n + R n * F (2 * n)) :
    limsup F atTop ≤ c / (1 - r) := by
  let U := limsup F atTop
  have hdouble : Tendsto (fun n : ℕ => 2 * n) atTop atTop :=
    tendsto_atTop_mono (fun n => show id n ≤ 2 * n by dsimp; omega) tendsto_id
  have hbound (δ : ℝ) (hδ : 0 < δ) : U ≤ c + r * (U + δ) := by
    have hupper : ∀ᶠ n in atTop, F (2 * n) ≤ U + δ :=
      (hdouble.eventually (eventually_lt_of_limsup_lt (by dsimp [U]; linarith) hb)).mono
        (fun _ h => h.le)
    have hcomp : ∀ᶠ n in atTop, F n ≤ B n + R n * (U + δ) := by
      filter_upwards [heq, hupper, hRpos] with n hn hu hp
      rw [hn]
      exact add_le_add_right (mul_le_mul_of_nonneg_left hu hp) _
    have ht := hB.add (hR.mul_const (U + δ))
    exact (limsup_le_limsup hcomp hl.isCoboundedUnder_le ht.isBoundedUnder_le).trans_eq
      ht.limsup_eq
  have hU : U ≤ c + r * U := by
    have ht : Tendsto (fun n : ℕ => c + r * (U + 1 / (n : ℝ))) atTop
        (𝓝 (c + r * U)) := by
      simpa using (tendsto_const_nhds.add
        ((tendsto_const_nhds.add tendsto_one_div_atTop_nhds_zero_nat).const_mul r))
    apply ge_of_tendsto ht
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    exact hbound _ (by positivity)
  apply (le_div_iff₀ (by linarith : 0 < 1 - r)).2
  dsimp [U] at hU ⊢
  nlinarith

private theorem tendsto_of_dyadic_recursion
    {F B R : ℕ → ℝ} {L r : ℝ}
    (hb : atTop.IsBoundedUnder (· ≤ ·) F)
    (hl : atTop.IsBoundedUnder (· ≥ ·) F)
    (hB : Tendsto B atTop (𝓝 ((1 - r) * L))) (hR : Tendsto R atTop (𝓝 r))
    (hr : r < 1) (hRpos : ∀ᶠ n in atTop, 0 ≤ R n)
    (heq : ∀ᶠ n in atTop, F n = B n + R n * F (2 * n)) :
    Tendsto F atTop (𝓝 L) := by
  have hu : limsup F atTop ≤ L := by
    have := limsup_le_of_dyadic_recursion hb hl hB hR hr hRpos heq
    rwa [mul_div_cancel_left₀ _ (by linarith : 1 - r ≠ 0)] at this
  have hnegB : Tendsto (fun n => -B n) atTop (𝓝 ((1 - r) * (-L))) := by
    simpa using hB.neg
  obtain ⟨u, hu'⟩ := hb
  obtain ⟨l, hl'⟩ := hl
  have hnb : atTop.IsBoundedUnder (· ≤ ·) (fun n => -F n) :=
    ⟨-l, hl'.mono (fun _ h => neg_le_neg h)⟩
  have hnl : atTop.IsBoundedUnder (· ≥ ·) (fun n => -F n) :=
    ⟨-u, hu'.mono (fun _ h => neg_le_neg h)⟩
  have hnrec : ∀ᶠ n in atTop, -F n = -B n + R n * (-F (2 * n)) := by
    filter_upwards [heq] with n hn
    rw [hn]; ring
  have hn := limsup_le_of_dyadic_recursion hnb hnl hnegB hR hr hRpos hnrec
  rw [mul_div_cancel_left₀ _ (by linarith : 1 - r ≠ 0)] at hn
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := eventually_atTop.1
    ((eventually_lt_of_limsup_lt (lt_of_le_of_lt hu (show L < L + ε by linarith))
        ⟨u, hu'⟩).and
      (eventually_lt_of_limsup_lt (lt_of_le_of_lt hn (show -L < -L + ε by linarith)) hnb))
  refine ⟨N, fun n h => ?_⟩
  obtain ⟨h1, h2⟩ := hN n h
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

-- Sharp Karamata: the dyadic block tends to (1 - r) / ρ, the tail is bounded,
-- and its recurrence has multiplier a n / a (2 * n) → r = 2 ^ (-ρ) < 1.
private theorem inverseKernelTail_tendsto {ρ : ℝ} {a : ℕ → ℝ}
    (hρ : 0 < ρ) (hrv : RegularlyVaryingSeq ρ a) (hmono : Monotone a)
    (hpos : ∀ n : ℕ, 1 ≤ n → 0 < a n) :
    Tendsto (fun n : ℕ => a n * inverseKernelTail (a := a) n) atTop (𝓝 (1 / ρ)) := by
  let F : ℕ → ℝ := fun n => a n * inverseKernelTail (a := a) n
  let B : ℕ → ℝ := fun n => a n *
    ∑ q ∈ Finset.Ico n (2 * n), inverseKernel (a := a) q
  let R : ℕ → ℝ := fun n => a n / a (2 * n)
  let r : ℝ := (2 : ℝ) ^ (-ρ)
  have hr : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hR : Tendsto R atTop (𝓝 r) := by
    have ht := (hrv 2 (by norm_num)).inv₀ (ne_of_gt (Real.rpow_pos_of_pos (by norm_num) ρ))
    have hf (n : ℕ) : ⌊(2 : ℝ) * n⌋₊ = 2 * n := by
      rw [show (2 : ℝ) * n = ((2 * n : ℕ) : ℝ) by push_cast; rfl, Nat.floor_natCast]
    simpa [R, r, Real.rpow_neg, hf] using ht
  obtain ⟨C, hC, hbound⟩ := inverseKernelTail_bound hρ hrv hmono hpos
  have hb : atTop.IsBoundedUnder (· ≤ ·) F := by
    refine ⟨C + 1, ?_⟩
    change ∀ᶠ n in atTop, F n ≤ C + 1
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact hbound n hn
  have hl : atTop.IsBoundedUnder (· ≥ ·) F := by
    refine ⟨0, ?_⟩
    change ∀ᶠ n in atTop, 0 ≤ F n
    filter_upwards [eventually_ge_atTop 1] with n hn
    apply mul_nonneg (hpos n hn).le
    apply tsum_nonneg
    intro k
    dsimp [inverseKernel]
    exact one_div_nonneg.mpr (mul_nonneg (by positivity) (hpos _ (by omega)).le)
  apply tendsto_of_dyadic_recursion hb hl (r := r)
  · simpa [B, inverseKernel, r, div_eq_mul_inv] using inverseBlock_tendsto hρ hrv hmono hpos
  · exact hR
  · exact hr
  · filter_upwards [eventually_ge_atTop 1] with n hn
    exact div_nonneg (hpos n hn).le (hpos _ (by omega)).le
  · have hs : Summable (inverseKernel (a := a)) := hrv.summable_inv_mul hmono hpos hρ
    filter_upwards [eventually_ge_atTop 1] with n hn
    have ha : a (2 * n) ≠ 0 := (hpos _ (by omega)).ne'
    dsimp [F, B, R]
    rw [inverseKernelTail_split hs n, mul_add]
    have hc : a n / a (2 * n) * (a (2 * n) * inverseKernelTail (a := a) (2 * n)) =
        a n * inverseKernelTail (a := a) (2 * n) := by field_simp
    rw [hc]
    simp only [inverseKernel, one_div, mul_inv_rev]

private theorem weighted_tail_tendsto {ρ c : ℝ} {a p : ℕ → ℝ}
    (hρ : 0 < ρ) (hrv : RegularlyVaryingSeq ρ a) (hmono : Monotone a)
    (hpos : ∀ n : ℕ, 1 ≤ n → 0 < a n) (hp : Summable p)
    (hpoint : Tendsto (fun n : ℕ => (n : ℝ) * a n * p n) atTop (𝓝 c)) :
    Tendsto (fun n : ℕ => a n * ∑' k : ℕ, p (n + k)) atTop (𝓝 (c * (1 / ρ))) := by
  have hk : Summable (inverseKernel (a := a)) := hrv.summable_inv_mul hmono hpos hρ
  have ht := (inverseKernelTail_tendsto hρ hrv hmono hpos).const_mul c
  obtain ⟨C, hC, hbound⟩ := inverseKernelTail_bound hρ hrv hmono hpos
  rw [Metric.tendsto_atTop]
  intro ε hε
  let δ : ℝ := ε / (2 * (C + 1))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδmul : δ * (C + 1) = ε / 2 := by dsimp [δ]; field_simp
  obtain ⟨N₁, hN₁⟩ := Metric.tendsto_atTop.1 hpoint δ hδ
  obtain ⟨N₂, hN₂⟩ := Metric.tendsto_atTop.1 ht (ε / 2) (by positivity)
  refine ⟨max (max N₁ N₂) 1, fun n hn => ?_⟩
  have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
  have hnN₁ : N₁ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hnN₂ : N₂ ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  have han : 0 < a n := hpos _ hn1
  have hks : Summable (fun k => inverseKernel (a := a) (n + k)) := by
    simpa [Nat.add_comm] using (summable_nat_add_iff n).2 hk
  have hps : Summable (fun k => p (n + k)) := by
    simpa [Nat.add_comm] using (summable_nat_add_iff n).2 hp
  have hterm (k : ℕ) : ‖p (n + k) - c * inverseKernel (a := a) (n + k)‖ ≤
      δ * inverseKernel (a := a) (n + k) := by
    let q := n + k
    have hq : 1 ≤ q := by dsimp [q]; omega
    have hqR : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
    have haq : 0 < a q := hpos q hq
    have hkp : 0 ≤ inverseKernel (a := a) q := by dsimp [inverseKernel]; positivity
    have hid : p q - c * inverseKernel (a := a) q =
        ((q : ℝ) * a q * p q - c) * inverseKernel (a := a) q := by
      dsimp [inverseKernel]
      field_simp
    have hclose : |(q : ℝ) * a q * p q - c| ≤ δ := by
      exact (show dist ((q : ℝ) * a q * p q) c < δ from hN₁ q (by dsimp [q]; omega)).le
    rw [Real.norm_eq_abs, hid, abs_mul, abs_of_nonneg hkp]
    exact mul_le_mul_of_nonneg_right hclose hkp
  have he := (hps.hasSum.sub (hks.hasSum.mul_left c)).norm_le_of_bounded
    (hks.hasSum.mul_left δ) hterm
  have he' : |(∑' k : ℕ, p (n + k)) - c * inverseKernelTail (a := a) n| ≤
      δ * inverseKernelTail (a := a) n := by
    simpa only [Real.norm_eq_abs, inverseKernelTail] using he
  have hscaled : |a n * (∑' k : ℕ, p (n + k)) -
      c * (a n * inverseKernelTail (a := a) n)| ≤ ε / 2 := by
    calc _ = |a n * ((∑' k : ℕ, p (n + k)) - c * inverseKernelTail (a := a) n)| := by
            congr 1
            ring
      _ = a n * |(∑' k : ℕ, p (n + k)) - c * inverseKernelTail (a := a) n| := by
            rw [abs_mul, abs_of_pos han]
      _ ≤ a n * (δ * inverseKernelTail (a := a) n) := mul_le_mul_of_nonneg_left he' han.le
      _ = δ * (a n * inverseKernelTail (a := a) n) := by ring
      _ ≤ δ * (C + 1) := mul_le_mul_of_nonneg_left (hbound n hn1) hδ.le
      _ = ε / 2 := hδmul
  have hclose := hN₂ n hnN₂
  rw [Real.dist_eq] at hclose ⊢
  calc _ ≤ |a n * (∑' k : ℕ, p (n + k)) - c * (a n * inverseKernelTail (a := a) n)| +
        |c * (a n * inverseKernelTail (a := a) n) - c * (1 / ρ)| := abs_sub_le _ _ _
    _ < ε := by linarith


/-- On the lattice `g ℕ + 1`, the local factor `g` cancels when passing to the
lattice index. This is the analytic part of the leaf-tail transfer; identifying
the series with the leaf event and treating arbitrary thresholds remain separate. -/
private theorem lattice_weighted_tail_tendsto {ρ c : ℝ} {a p : ℕ → ℝ} {g : ℕ}
    (hg : 0 < g) (hρ : 0 < ρ)
    (hrv : RegularlyVaryingSeq ρ (fun n => a (g * n)))
    (hmono : Monotone (fun n => a (g * n)))
    (hpos : ∀ n : ℕ, 1 ≤ n → 0 < a (g * n))
    (hp : Summable (fun n => p (g * n + 1)))
    (hpoint : Tendsto (fun n : ℕ => ((g * n : ℕ) : ℝ) * a (g * n) * p (g * n + 1))
      atTop (𝓝 ((g : ℝ) * c))) :
    Tendsto (fun n : ℕ => a (g * n) * ∑' k : ℕ, p (g * (n + k) + 1))
      atTop (𝓝 (c * (1 / ρ))) := by
  have hgR : (g : ℝ) ≠ 0 := by exact_mod_cast hg.ne'
  have ht := hpoint.div_const (g : ℝ)
  rw [mul_div_cancel_left₀ c hgR] at ht
  have ht' : Tendsto (fun n : ℕ => (n : ℝ) * a (g * n) * p (g * n + 1))
      atTop (𝓝 c) := by
    apply ht.congr fun n => ?_
    push_cast
    field_simp
  exact weighted_tail_tendsto hρ hrv hmono hpos hp ht'

private theorem leafCountEvent_measurable (m : ℕ) : MeasurableSet (leafCountEvent m) := by
  have he : leafCountEvent m = PlaneTree.toLocallyFinite '' {t | t.degreeCount 0 = m} := by
    ext T
    simp [leafCountEvent, finiteTreeEvent, Set.mem_image, and_comm]
  rw [he]
  exact (Set.to_countable _ |>.image _).measurableSet

private theorem leafCountEvents_disjoint (n : ℕ) :
    Pairwise (fun i j : ℕ => Disjoint (leafCountEvent (n + i)) (leafCountEvent (n + j))) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  rintro T ⟨t, ht, hti⟩ ⟨u, hu, huj⟩
  have htu : t = u := PlaneTree.toLocallyFinite_injective (ht.trans hu.symm)
  subst u
  exact hij (by omega)

private theorem leafGe_real_eq_tsum (μ : PMF ℕ) (n : ℕ) :
    (bienaymeLaw μ.toMeasure).real (leafGeEvent n) = ∑' k : ℕ, leafProb μ (n + k) := by
  have he : leafGeEvent n = ⋃ k : ℕ, leafCountEvent (n + k) := by
    ext T
    constructor
    · rintro ⟨t, ht, htn⟩
      exact Set.mem_iUnion.2 ⟨t.degreeCount 0 - n, t, ht, by omega⟩
    · intro h
      obtain ⟨k, t, ht, htk⟩ := Set.mem_iUnion.1 h
      exact ⟨t, ht, by omega⟩
  rw [he, measureReal_def, measure_iUnion (leafCountEvents_disjoint n)
    (fun k => leafCountEvent_measurable _), ENNReal.tsum_toReal_eq (fun _ => measure_ne_top _ _)]
  rfl

private theorem leafGe_lattice_series {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (n : ℕ) :
    (bienaymeLaw μ.toMeasure).real (leafGeEvent (arithFactor μ {0} * n + 1)) =
      ∑' k : ℕ, leafProb μ (arithFactor μ {0} * (n + k) + 1) := by
  let g := arithFactor μ {0}
  have hg : 0 < g := by
    change 0 < arithFactor μ {0}
    rw [LeafMass.Arithmetic.arithFactor_zero_eq_setGcd hc hne]
    exact lt_of_lt_of_le Nat.zero_lt_one
      (LeafMass.Arithmetic.arithFactor_isGreatest_of_two_le
        (LeafMass.Arithmetic.exists_two_le hc hne)).1.1
  rw [leafGe_real_eq_tsum]
  have hi : Function.Injective (fun k : ℕ => g * k) := mul_right_injective₀ hg.ne'
  have hs : Function.support (fun k : ℕ => leafProb μ (g * n + 1 + k)) ⊆
      Set.range (fun k : ℕ => g * k) := by
    intro k hk
    have hd : g ∣ g * n + k := by
      by_contra hd
      have hz := leafProb_eq_zero_of_not_dvd hc hne hd
      exact hk (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hz)
    have hdk : g ∣ k := (Nat.dvd_add_iff_right (dvd_mul_right g n)).2 hd
    obtain ⟨q, hq⟩ := hdk
    exact ⟨q, hq.symm⟩
  have hsum := hi.tsum_eq hs
  calc
    (∑' k : ℕ, leafProb μ (g * n + 1 + k)) =
        ∑' k : ℕ, leafProb μ (g * n + 1 + g * k) := hsum.symm
    _ = _ := by
      congr 1
      funext k
      simp only [g, Nat.mul_add, Nat.add_assoc, Nat.add_comm]

private theorem stableDomain_mul_regular {μ : PMF ℕ} {θ : ℝ} {a : ℕ → ℝ}
    (ha : StableDomain μ θ a) {g : ℕ} (hg : 0 < g) :
    RegularlyVaryingSeq (1 / θ) (fun n => a (g * n)) := by
  have := isProbabilityMeasure_stepLaw μ
  have hat := stableDomain_isStableAttracted ha
  have hgR : (0 : ℝ) < g := by exact_mod_cast hg
  intro c hc
  have hcfl := (tendsto_nat_floor_mul_div_atTop (R := ℝ) hc.le).comp
    tendsto_natCast_atTop_atTop
  have hnum : Tendsto (fun n : ℕ => ((g * ⌊c * n⌋₊ : ℕ) : ℝ) / n)
      atTop (𝓝 ((g : ℝ) * c)) := by
    simpa only [Nat.cast_mul, mul_div_assoc, Function.comp_apply] using hcfl.const_mul (g : ℝ)
  have hden : Tendsto (fun n : ℕ => ((g * n : ℕ) : ℝ) / n) atTop (𝓝 (g : ℝ)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ne_atTop 0] with n hn
    simp [Nat.cast_mul, Nat.cast_ne_zero.2 hn]
  have hn := TransformConvergence.tendsto_div_of_tendsto_div' (stepLaw μ) hat hat
    (mul_pos hgR hc) hnum
  have hd := TransformConvergence.tendsto_div_of_tendsto_div' (stepLaw μ) hat hat hgR hden
  have hlim : ((g : ℝ) * c) ^ (1 / θ) / (g : ℝ) ^ (1 / θ) = c ^ (1 / θ) := by
    rw [Real.mul_rpow hgR.le hc.le, mul_div_cancel_left₀ _ (Real.rpow_pos_of_pos hgR _).ne']
  rw [← hlim]
  apply (hn.div hd (Real.rpow_pos_of_pos hgR _).ne').congr'
  filter_upwards [eventually_ge_atTop 1] with n hn1
  exact div_div_div_cancel_right₀ (ha.pos n hn1).ne' _ _

private theorem leafTail_lattice {μ : PMF ℕ} {θ : ℝ} {a : ℕ → ℝ}
    (hc : IsCritical μ) (hne : μ 1 ≠ 1) (hap : Aperiodic μ)
    (ha : StableDomain μ θ a)
    (heq : ∀ᶠ n in atTop, a n = norming (stepLaw μ) θ n) :
    Tendsto (fun n : ℕ => a (arithFactor μ {0} * n) *
      (bienaymeLaw μ.toMeasure).real (leafGeEvent (arithFactor μ {0} * n + 1))) atTop
      (𝓝 (θ * (μ 0).toReal ^ (1 / θ) * Scalar.stableDensity θ 0)) := by
  let g := arithFactor μ {0}
  have hg : 0 < g := by
    change 0 < arithFactor μ {0}
    rw [LeafMass.Arithmetic.arithFactor_zero_eq_setGcd hc hne]
    exact lt_of_lt_of_le Nat.zero_lt_one
      (LeafMass.Arithmetic.arithFactor_isGreatest_of_two_le
        (LeafMass.Arithmetic.exists_two_le hc hne)).1.1
  have hgtop : Tendsto (fun n : ℕ => g * n) atTop atTop :=
    tendsto_atTop_mono (fun n => Nat.le_mul_of_pos_left n hg) tendsto_id
  have hfilter : Tendsto (fun n : ℕ => g * n)
      atTop (atTop ⊓ 𝓟 {n : ℕ | arithFactor μ {0} ∣ n}) :=
    tendsto_inf.2 ⟨hgtop, tendsto_principal.2 (Eventually.of_forall fun n => dvd_mul_right g n)⟩
  have hpoint := (ltn_ii_tendsto hc hne hap ⟨a, ha⟩).comp hfilter
  have hpoint' : Tendsto (fun n : ℕ => ((g * n : ℕ) : ℝ) * a (g * n) *
      leafProb μ (g * n + 1)) atTop
      (𝓝 ((g : ℝ) * ((μ 0).toReal ^ (1 / θ) * Scalar.stableDensity θ 0))) := by
    rw [mul_comm (g : ℝ)]
    apply hpoint.congr'
    filter_upwards [hgtop.eventually heq] with n hn
    simp only [Function.comp_apply, hn]
  have hpall : Summable (leafProb μ) := by
    change Summable (fun q : ℕ => (bienaymeLaw μ.toMeasure).real (leafCountEvent q))
    have hd := leafCountEvents_disjoint 0
    exact
      (summable_measure_toReal leafCountEvent_measurable (by simpa only [zero_add] using hd)
        (μ := bienaymeLaw μ.toMeasure))
  have hp : Summable (fun n : ℕ => leafProb μ (g * n + 1)) :=
    hpall.comp_injective (fun i j hij => (mul_right_injective₀ hg.ne') (Nat.add_right_cancel hij))
  have ht := lattice_weighted_tail_tendsto hg (by have := ha.alpha_mem.1; positivity)
    (stableDomain_mul_regular ha hg)
    (ha.monotone.comp (fun i j hij => Nat.mul_le_mul_left g hij))
    (fun n hn => ha.pos _ (by have : 1 ≤ g := hg; nlinarith)) hp hpoint'
  have hseries (n : ℕ) : (∑' k : ℕ, leafProb μ (g * (n + k) + 1)) =
      (bienaymeLaw μ.toMeasure).real (leafGeEvent (g * n + 1)) :=
    (leafGe_lattice_series hc hne n).symm
  simp_rw [hseries] at ht
  rw [one_div_one_div] at ht
  have hL : ((μ 0).toReal ^ (1 / θ) * Scalar.stableDensity θ 0) * θ =
      θ * (μ 0).toReal ^ (1 / θ) * Scalar.stableDensity θ 0 := by ring
  rw [hL] at ht
  exact ht

private theorem index_ratio_of_bounded_error {u : ℕ → ℕ} {C : ℝ}
    (hb : ∀ᶠ n : ℕ in atTop, (n : ℝ) - C ≤ u n ∧ (u n : ℝ) ≤ n + C) :
    Tendsto (fun n : ℕ => (u n : ℝ) / n) atTop (𝓝 1) := by
  have hz : Tendsto (fun n : ℕ => C / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat C
  have hlo : Tendsto (fun n : ℕ => 1 - C / (n : ℝ)) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.sub hz
  have hhi : Tendsto (fun n : ℕ => 1 + C / (n : ℝ)) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.add hz
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi
  · filter_upwards [hb, eventually_ge_atTop 1] with n hn hn1
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
    have he : 1 - C / (n : ℝ) = ((n : ℝ) - C) / n := by field_simp
    rw [he]
    exact div_le_div_of_nonneg_right hn.1 hn0.le
  · filter_upwards [hb, eventually_ge_atTop 1] with n hn hn1
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
    have he : 1 + C / (n : ℝ) = ((n : ℝ) + C) / n := by field_simp
    rw [he]
    exact div_le_div_of_nonneg_right hn.2 hn0.le

private theorem lattice_limit_change_index {μ : PMF ℕ} {θ : ℝ} {a F : ℕ → ℝ}
    (ha : StableDomain μ θ a) {g : ℕ} (hg : 0 < g) {L : ℝ}
    (hlat : Tendsto (fun n : ℕ => a (g * n) * F (g * n + 1)) atTop (𝓝 L))
    {u : ℕ → ℕ} (hu : Tendsto u atTop atTop)
    (hr : Tendsto (fun n : ℕ => ((g * u n : ℕ) : ℝ) / n) atTop (𝓝 1)) :
    Tendsto (fun n : ℕ => a n * F (g * u n + 1)) atTop (𝓝 L) := by
  have := isProbabilityMeasure_stepLaw μ
  have hat := stableDomain_isStableAttracted ha
  have har := TransformConvergence.tendsto_div_of_tendsto_div' (stepLaw μ) hat hat zero_lt_one hr
  rw [Real.one_rpow] at har
  have ht := (har.inv₀ one_ne_zero).mul (hlat.comp hu)
  rw [inv_one, one_mul] at ht
  apply ht.congr'
  filter_upwards [hu.eventually (eventually_ge_atTop 1)] with n hn
  have hap : a (g * u n) ≠ 0 := (ha.pos _ (by have : 1 ≤ g := hg; nlinarith)).ne'
  simp only [Function.comp_apply, inv_div]
  field_simp

private theorem lattice_tail_interpolation {μ : PMF ℕ} {θ : ℝ} {a F : ℕ → ℝ}
    (ha : StableDomain μ θ a) (hF : Antitone F) {g : ℕ} (hg : 0 < g) {L : ℝ}
    (hlat : Tendsto (fun n : ℕ => a (g * n) * F (g * n + 1)) atTop (𝓝 L)) :
    Tendsto (fun n : ℕ => a n * F n) atTop (𝓝 L) := by
  have hq : Tendsto (fun n : ℕ => n / g) atTop atTop := by
    apply tendsto_atTop.2
    intro N
    filter_upwards [eventually_ge_atTop (N * g)] with n hn
    exact (Nat.le_div_iff_mul_le hg).2 hn
  have hp : Tendsto (fun n : ℕ => n / g + 1) atTop atTop :=
    (tendsto_add_atTop_nat 1).comp hq
  have hm : Tendsto (fun n : ℕ => n / g - 1) atTop atTop :=
    (tendsto_sub_atTop_nat 1).comp hq
  have hrp : Tendsto (fun n : ℕ => ((g * (n / g + 1) : ℕ) : ℝ) / n) atTop (𝓝 1) := by
    apply index_ratio_of_bounded_error (C := 2 * g)
    apply Eventually.of_forall
    intro n
    have he : (g : ℝ) * (n / g : ℕ) + (n % g : ℕ) = n := by
      exact_mod_cast Nat.div_add_mod n g
    have hmod : ((n % g : ℕ) : ℝ) < g := by exact_mod_cast Nat.mod_lt n hg
    simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    constructor <;> nlinarith [(Nat.cast_nonneg (n % g) : (0 : ℝ) ≤ (n % g : ℕ))]
  have hrm : Tendsto (fun n : ℕ => ((g * (n / g - 1) : ℕ) : ℝ) / n) atTop (𝓝 1) := by
    apply index_ratio_of_bounded_error (C := 2 * g)
    filter_upwards [hq.eventually (eventually_ge_atTop 1)] with n hn
    have he : (g : ℝ) * (n / g : ℕ) + (n % g : ℕ) = n := by
      exact_mod_cast Nat.div_add_mod n g
    have hmod : ((n % g : ℕ) : ℝ) < g := by exact_mod_cast Nat.mod_lt n hg
    simp only [Nat.cast_mul, Nat.cast_sub hn, Nat.cast_one]
    constructor <;> nlinarith [(Nat.cast_nonneg (n % g) : (0 : ℝ) ≤ (n % g : ℕ))]
  have hlo := lattice_limit_change_index ha hg hlat hp hrp
  have hhi := lattice_limit_change_index ha hg hlat hm hrm
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi
  · filter_upwards [eventually_ge_atTop 1] with n hn
    apply mul_le_mul_of_nonneg_left _ (ha.pos n hn).le
    apply hF
    have he := Nat.div_add_mod n g
    have hr := Nat.mod_lt n hg
    simp only [Nat.mul_add, Nat.mul_one]
    omega
  · filter_upwards [eventually_ge_atTop 1, hq.eventually (eventually_ge_atTop 1)] with n hn hnq
    apply mul_le_mul_of_nonneg_left _ (ha.pos n hn).le
    apply hF
    have he := Nat.div_add_mod n g
    have hx : g * (n / g - 1) + g = g * (n / g) := by
      calc
        g * (n / g - 1) + g = g * (n / g - 1) + g * 1 := by rw [Nat.mul_one]
        _ = g * (n / g - 1 + 1) := (Nat.mul_add _ _ _).symm
        _ = g * (n / g) := by rw [Nat.sub_add_cancel hnq]
    omega

/-- The sharp leaf tail, including the cancellation of the arithmetic factor. -/
theorem leafTail_asymp {μ : PMF ℕ} {θ : ℝ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hap : Aperiodic μ) (hDA : ∃ a, StableDomain μ θ a) :
    Tendsto (fun m : ℕ => norming (stepLaw μ) θ m *
      (bienaymeLaw μ.toMeasure).real (leafGeEvent m)) atTop
      (𝓝 (θ * (μ 0).toReal ^ (1 / θ) * Scalar.stableDensity θ 0)) := by
  obtain ⟨b, hb⟩ := hDA
  have := isProbabilityMeasure_stepLaw μ
  have hcan := locallimit_i (stepLaw μ) (stepLaw_lt_neg_one μ) (integrable_stepLaw hc)
    ⟨b, by rw [mean_stepLaw hc]; exact stableDomain_isStableAttracted hb⟩
  have hmono := (locallimit_ii (stepLaw μ) (stepLaw_lt_neg_one μ) (integrable_stepLaw hc)
    ⟨b, by rw [mean_stepLaw hc]; exact stableDomain_isStableAttracted hb⟩).1
  rw [mean_stepLaw hc] at hcan
  obtain ⟨a, heq, ha⟩ := hcan.exists_stableDomain hc hne hmono
  have hg : 0 < arithFactor μ {0} := by
    rw [LeafMass.Arithmetic.arithFactor_zero_eq_setGcd hc hne]
    exact lt_of_lt_of_le Nat.zero_lt_one
      (LeafMass.Arithmetic.arithFactor_isGreatest_of_two_le
        (LeafMass.Arithmetic.exists_two_le hc hne)).1.1
  have hF : Antitone (fun n : ℕ => (bienaymeLaw μ.toMeasure).real (leafGeEvent n)) := by
    intro n m hnm
    apply measureReal_mono _ (measure_ne_top _ _)
    rintro T ⟨t, ht, htm⟩
    exact ⟨t, ht, hnm.trans htm⟩
  have ht := lattice_tail_interpolation ha hF hg (leafTail_lattice hc hne hap ha heq)
  exact ht.congr' (heq.mono fun n hn => by rw [hn])

/-- The leaf tail at the cutoff and the size tail have the same asymptotic. -/
theorem leafGe_sizeGe_ratio {μ : PMF ℕ} {θ : ℝ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hap : Aperiodic μ) (hDA : ∃ a, StableDomain μ θ a) :
    Tendsto (fun n : ℕ => (bienaymeLaw μ.toMeasure).real (leafGeEvent (leafCutoff μ n)) /
      (bienaymeLaw μ.toMeasure).real (sizeGeEvent n)) atTop (𝓝 1) := by
  obtain ⟨a, ha⟩ := hDA
  have := isProbabilityMeasure_stepLaw μ
  have h0 : 0 < (μ 0).toReal :=
    ENNReal.toReal_pos (LeafMass.Arithmetic.mu_zero_ne_zero hc hne) (μ.apply_ne_top 0)
  have hθ : 0 < θ := by linarith [ha.alpha_mem.1]
  have hD : θ * Scalar.stableDensity θ 0 ≠ 0 :=
    (mul_pos hθ (Scalar.stableDensity_zero_pos ha.alpha_mem)).ne'
  have hR : (μ 0).toReal ^ (1 / θ) ≠ 0 := (Real.rpow_pos_of_pos h0 _).ne'
  have hcut : Tendsto (leafCutoff μ) atTop atTop := by
    have ht := Filter.Tendsto.pos_mul_atTop h0 (leafCutoff_ratio h0) tendsto_natCast_atTop_atTop
    have ht' : Tendsto (fun n : ℕ => (leafCutoff μ n : ℝ)) atTop atTop := by
      apply ht.congr'
      filter_upwards [eventually_ne_atTop 0] with n hn
      exact div_mul_cancel₀ _ (by exact_mod_cast hn)
    exact tendsto_natCast_atTop_iff.1 ht'
  have ht := ((leafTail_asymp hc hne hap ⟨a, ha⟩).comp hcut).div
    ((norming_leafCutoff_ratio hc hne ⟨a, ha⟩).mul (lem_locallimit hc hne hap ⟨a, ha⟩).2)
    (mul_ne_zero hR hD)
  have hlim : (θ * (μ 0).toReal ^ (1 / θ) * Scalar.stableDensity θ 0) /
      ((μ 0).toReal ^ (1 / θ) * (θ * Scalar.stableDensity θ 0)) = 1 := by
    rw [show θ * (μ 0).toReal ^ (1 / θ) * Scalar.stableDensity θ 0 =
      (μ 0).toReal ^ (1 / θ) * (θ * Scalar.stableDensity θ 0) by ring,
      div_self (mul_ne_zero hR hD)]
  rw [hlim] at ht
  have hcan := locallimit_i (stepLaw μ) (stepLaw_lt_neg_one μ) (integrable_stepLaw hc)
    ⟨a, by rw [mean_stepLaw hc]; exact stableDomain_isStableAttracted ha⟩
  have hpos : ∀ᶠ n in atTop, 0 < norming (stepLaw μ) θ n := eventually_atTop.2 hcan.pos
  apply ht.congr'
  filter_upwards [hpos, hcut.eventually hpos] with n hn hcn
  change (norming (stepLaw μ) θ (leafCutoff μ n) *
    (bienaymeLaw μ.toMeasure).real (leafGeEvent (leafCutoff μ n))) /
    ((norming (stepLaw μ) θ (leafCutoff μ n) / norming (stepLaw μ) θ n) *
      (norming (stepLaw μ) θ n * (bienaymeLaw μ.toMeasure).real (sizeGeEvent n))) = _
  have hd : (norming (stepLaw μ) θ (leafCutoff μ n) / norming (stepLaw μ) θ n) *
      (norming (stepLaw μ) θ n * (bienaymeLaw μ.toMeasure).real (sizeGeEvent n)) =
      norming (stepLaw μ) θ (leafCutoff μ n) * (bienaymeLaw μ.toMeasure).real (sizeGeEvent n) := by
    field_simp [hn.ne']
  rw [hd]
  exact mul_div_mul_left _ _ hcn.ne'

end BGWLeaves.Conditioning.LeafTail
