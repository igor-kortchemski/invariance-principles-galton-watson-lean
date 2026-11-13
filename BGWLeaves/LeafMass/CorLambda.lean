module

public import BGWLeaves.LeafMass.Defs
public import BGWLeaves.LeafMass.LeafLocalLimit
public import BGWLeaves.LeafMass.Arithmetic
public import BGWLeaves.LeafConcentration
public import BGWLeaves.LeafConcentration.OeLemmas

/-!
# Corollary 3.3 (`cor:Lambda`): leaf-conditioned concentration

Proof of the paper: `{λ = n} ⊂ {ζ ≥ n}`, Corollary 2.6 (`cor_GD2mieux`) and the polynomial lower bound
`P[λ = n] ≥ n^{-A}` coming from Theorem 3.1(ii) (`ltn_ii_tendsto`, `B_n = h(n) n^{1/θ}`).
-/

@[expose] public section

namespace BGWLeaves.LeafMass.CorLambda

open MeasureTheory ProbabilityTheory Filter Asymptotics BGW BGW.StableTrees BGW.LocallyFinite
open BGWLeaves.StableAnalysis
open scoped ENNReal Topology

private theorem finiteTreeEvent_measurable (Q : PlaneTree → Prop) :
    MeasurableSet (finiteTreeEvent Q) := by
  have h : finiteTreeEvent Q = PlaneTree.toLocallyFinite '' {t | Q t} := by
    ext T; simp [finiteTreeEvent, Set.mem_image, and_comm]
  rw [h]
  exact (Set.to_countable _ |>.image _).measurableSet

private theorem leafCountEvent_subset_sizeGe (n : ℕ) : leafCountEvent n ⊆ sizeGeEvent n := by
  rintro T ⟨t, rfl, ht⟩
  right
  rw [ncard_present_toLocallyFinite]
  have : t.degreeCount 0 ≤ t.size := by
    unfold PlaneTree.degreeCount
    rw [← PlaneTree.length_degrees]
    exact List.count_le_length
  have ht' : t.degreeCount 0 = n := ht
  omega

private theorem cond_real_eq_div (P : Measure Tree) [IsFiniteMeasure P]
    {s A : Set Tree} (hs : MeasurableSet s) :
    (P[|s]).real A = P.real (s ∩ A) / P.real s := by
  simp only [measureReal_def, cond_apply hs, ENNReal.toReal_mul, ENNReal.toReal_inv,
    div_eq_mul_inv, mul_comm]

/-- `P[λ = n, D] ≤ P[D | ζ ≥ n]`. -/
private theorem inter_le_cond_sizeGe (μ : PMF ℕ) (n : ℕ) {D : Set Tree} (hD : MeasurableSet D) :
    (bienaymeLaw μ.toMeasure).real (leafCountEvent n ∩ D) ≤
      ((bienaymeLaw μ.toMeasure)[|sizeGeEvent n]).real D := by
  set P := bienaymeLaw μ.toMeasure with hP
  have h1 : P (leafCountEvent n ∩ D) ≤ P (sizeGeEvent n ∩ D) :=
    measure_mono (Set.inter_subset_inter_left _ (leafCountEvent_subset_sizeGe n))
  have h2 : P (sizeGeEvent n ∩ D) ≤ (P[|sizeGeEvent n]) D := by
    by_cases hz : P (sizeGeEvent n) = 0
    · have : P (sizeGeEvent n ∩ D) = 0 := measure_mono_null Set.inter_subset_left hz
      simp [this]
    · rw [cond_apply' hD P]
      calc P (sizeGeEvent n ∩ D) = 1 * P (sizeGeEvent n ∩ D) := (one_mul _).symm
        _ ≤ (P (sizeGeEvent n))⁻¹ * P (sizeGeEvent n ∩ D) := by
          gcongr
          exact ENNReal.one_le_inv.2 prob_le_one
  exact ENNReal.toReal_mono (measure_ne_top _ _) (h1.trans h2)

private theorem cond_leaf_le (μ : PMF ℕ) (n : ℕ) (Q : PlaneTree → Prop) :
    (((bienaymeLaw μ.toMeasure)[|leafCountEvent n]).real (finiteTreeEvent Q)) ≤
      (((bienaymeLaw μ.toMeasure)[|sizeGeEvent n]).real (finiteTreeEvent Q)) / leafProb μ n := by
  have hE : MeasurableSet (leafCountEvent n) :=
    finiteTreeEvent_measurable fun t => t.degreeCount 0 = n
  rw [cond_real_eq_div _ hE]
  exact div_le_div_of_nonneg_right (inter_le_cond_sizeGe μ n (finiteTreeEvent_measurable Q))
    measureReal_nonneg

/-- The polynomial lower bound `P[λ = n] ≥ n^{-A}`, for `n - 1` large in the multiples of `g`. -/
private theorem leafProb_poly_lower {μ : PMF ℕ} {θ : ℝ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hap : Aperiodic μ) (hDA : ∃ a, StableDomain μ θ a) :
    ∃ (A : ℝ) (N : ℕ), ∀ n : ℕ, N ≤ n → 1 ≤ n → arithFactor μ {0} ∣ n - 1 →
      (n : ℝ) ^ (-A) ≤ leafProb μ n := by
  obtain ⟨a, ha⟩ := hDA
  have hθ := (stableDomain_isStableAttracted ha).alpha_mem
  have hθ1 : 1 < θ := hθ.1
  have hq : 0 < (μ 0).toReal :=
    ENNReal.toReal_pos (Arithmetic.mu_zero_ne_zero hc hne) (μ.apply_ne_top 0)
  have hg : 0 < arithFactor μ {0} := by
    rw [Arithmetic.arithFactor_zero_eq_setGcd hc hne]
    exact lt_of_lt_of_le Nat.zero_lt_one
      (Arithmetic.arithFactor_isGreatest_of_two_le (Arithmetic.exists_two_le hc hne)).1.1
  set L := (μ 0).toReal ^ (1 / θ) * Scalar.stableDensity θ 0 * (arithFactor μ {0} : ℝ) with hLdef
  have hL : 0 < L := mul_pos (mul_pos (Real.rpow_pos_of_pos hq _)
    (Scalar.stableDensity_zero_pos hθ)) (by exact_mod_cast hg)
  -- the local limit theorem
  have hlim := LeafLocalLimit.ltn_ii_tendsto hc hne hap ⟨a, ha⟩
  have hev1 := hlim.eventually (lt_mem_nhds (half_lt_self hL))
  rw [eventually_inf_principal] at hev1
  -- the slowly varying function is `≤ n` eventually
  have hSV : SlowlyVarying (hSlow μ θ) := hSlow_slowlyVarying hc ⟨a, ha⟩
  have hSVabs : SlowlyVarying (fun x : ℝ => |hSlow μ θ x|) := by
    intro c hc'
    simpa only [← abs_div, abs_one] using (hSV c hc').abs
  have hmeas : Measurable (fun x : ℝ => |hSlow μ θ x|) :=
    continuous_abs.measurable.comp (measurable_floor_ratio (norming (stepLaw μ) θ) (1 / θ))
  have hs := slow_rpow_neg_mul_tendsto_zero hmeas (fun _ _ => abs_nonneg _) hSVabs
    (ε := 1) zero_lt_one
  have hs' := (hs.comp tendsto_natCast_atTop_atTop).eventually (eventually_lt_nhds (zero_lt_one' ℝ))
  -- choose the threshold
  obtain ⟨N0, hN0⟩ := eventually_atTop.1 (hev1.and (hs'.and (eventually_ge_atTop 1)))
  set q : ℝ := 2 + 1 / θ with hqdef
  have hq0 : 0 ≤ q := by rw [hqdef]; have : 0 < 1 / θ := by positivity
                         linarith
  obtain ⟨N1, hN1⟩ := exists_nat_gt (2 / L)
  refine ⟨q + 1, max N0 N1 + 1, fun n hn hn1 hdvd => ?_⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hdvd' : arithFactor μ {0} ∣ m := by simpa using hdvd
  have hm0 : N0 ≤ m := by omega
  have hm1 : N1 ≤ m := by omega
  obtain ⟨hlt, hsm, hm1'⟩ := hN0 m hm0
  have hlt := hlt hdvd'
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm1'
  -- B_m = hSlow m * m^(1/θ)
  have hB : norming (stepLaw μ) θ m = hSlow μ θ m * (m : ℝ) ^ (1 / θ) := by
    have : (m : ℝ) ^ (1 / θ) ≠ 0 := (Real.rpow_pos_of_pos hmpos _).ne'
    simp only [hSlow, Nat.floor_natCast]
    field_simp
  have hsm' : |hSlow μ θ m| < m := by
    have h := hsm
    simp only [Function.comp_apply, Real.rpow_neg_one] at h
    rw [inv_mul_lt_iff₀ hmpos] at h
    simpa using h
  have hBle : norming (stepLaw μ) θ m ≤ (m : ℝ) * (m : ℝ) ^ (1 / θ) := by
    rw [hB]
    exact mul_le_mul_of_nonneg_right ((le_abs_self _).trans hsm'.le)
      (Real.rpow_nonneg hmpos.le _)
  have hlp : 0 ≤ leafProb μ (m + 1) := measureReal_nonneg
  have hmain : L / 2 < (m : ℝ) * ((m : ℝ) * (m : ℝ) ^ (1 / θ)) * leafProb μ (m + 1) := by
    refine lt_of_lt_of_le hlt ?_
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hBle hmpos.le) hlp
  have hmq : (m : ℝ) * ((m : ℝ) * (m : ℝ) ^ (1 / θ)) = (m : ℝ) ^ q := by
    rw [hqdef, Real.rpow_add hmpos]
    have : (m : ℝ) ^ (2 : ℝ) = (m : ℝ) * m := by
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; ring
    rw [this]; ring
  rw [hmq] at hmain
  -- compare
  have hmq0 : 0 < (m : ℝ) ^ q := Real.rpow_pos_of_pos hmpos _
  have hN1' : 2 / L < ((m : ℝ) + 1) := by
    have : (N1 : ℝ) ≤ m := by exact_mod_cast hm1
    linarith
  have hmp1 : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by positivity
  push_cast at hmp1 ⊢
  have hle : (m : ℝ) ^ q ≤ ((m : ℝ) + 1) ^ q :=
    Real.rpow_le_rpow hmpos.le (by linarith) hq0
  have hrw : ((m : ℝ) + 1) ^ (-(q + 1)) = (((m : ℝ) + 1) ^ q * ((m : ℝ) + 1))⁻¹ := by
    rw [Real.rpow_neg hmp1.le, Real.rpow_add hmp1, Real.rpow_one]
  rw [hrw]
  have h2L : 2 / L * (L / 2) = 1 := by field_simp
  have hbig : (m : ℝ) ^ q * (2 / L) ≤ ((m : ℝ) + 1) ^ q * ((m : ℝ) + 1) := by
    exact mul_le_mul hle hN1'.le (by positivity) (by positivity)
  -- (m+1)^q (m+1) ≥ m^q * 2/L
  have : (((m : ℝ) + 1) ^ q * ((m : ℝ) + 1))⁻¹ ≤ (L / 2) / (m : ℝ) ^ q := by
    rw [inv_eq_one_div, div_le_div_iff₀ (by positivity) hmq0]
    have hL2 : 0 < L / 2 := by positivity
    calc 1 * (m : ℝ) ^ q = (L / 2) * ((m : ℝ) ^ q * (2 / L)) := by field_simp
      _ ≤ (L / 2) * (((m : ℝ) + 1) ^ q * ((m : ℝ) + 1)) :=
          mul_le_mul_of_nonneg_left hbig hL2.le
  refine this.trans ?_
  rw [div_le_iff₀ hmq0]
  linarith [hmain]

/-- `IsOeOn` from an eventual bound along `S`, for sequences bounded by `1`. -/
private theorem isOeOn_of_eventually_bound {S : Set ℕ} {ε : ℝ} (hε : 0 < ε) {x : ℕ → ℝ}
    (hx : ∀ n, x n ≤ 1) {C c : ℝ} (hC : 0 < C) (hc : 0 < c) {N : ℕ}
    (h : ∀ n ∈ S, N ≤ n → x n ≤ C * Real.exp (-c * (n : ℝ) ^ ε)) : IsOeOn S ε x := by
  refine ⟨C + Real.exp (c * (N : ℝ) ^ ε), c, by positivity, hc, fun n hn => ?_⟩
  by_cases hnN : N ≤ n
  · exact (h n hn hnN).trans (mul_le_mul_of_nonneg_right
      (by linarith [Real.exp_pos (c * (N : ℝ) ^ ε)]) (Real.exp_pos _).le)
  · have hpow : (n : ℝ) ^ ε ≤ (N : ℝ) ^ ε :=
      Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast (Nat.le_of_lt (not_le.1 hnN))) hε.le
    have h1 : 1 ≤ Real.exp (c * (N : ℝ) ^ ε) * Real.exp (-c * (n : ℝ) ^ ε) := by
      rw [← Real.exp_add]
      apply Real.one_le_exp
      nlinarith
    calc x n ≤ 1 := hx n
      _ ≤ Real.exp (c * (N : ℝ) ^ ε) * Real.exp (-c * (n : ℝ) ^ ε) := h1
      _ ≤ _ := by
        rw [add_mul]
        nlinarith [mul_pos hC (Real.exp_pos (-c * (n : ℝ) ^ ε))]

private theorem cond_real_le_one' (P : Measure Tree) [IsFiniteMeasure P] (s A : Set Tree) :
    (P[|s]).real A ≤ 1 := by
  by_cases hs : P s = 0
  · simp [cond_eq_zero_of_meas_eq_zero hs]
  · have := cond_isProbabilityMeasure (μ := P) hs
    exact measureReal_le_one

/-- **Corollary 3.3**, arithmetic form (statement of `BGWLeaves.LeafMass.cor_Lambda_arith`). -/
theorem cor_Lambda_arith {μ : PMF ℕ} {θ : ℝ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hap : Aperiodic μ) (hDA : ∃ a, StableDomain μ θ a) {η δ : ℝ}
    (hη0 : 0 < η) (hη1 : η < 1) (hδ : 0 < δ) :
    IsOeOn {n : ℕ | 1 ≤ n ∧ arithFactor μ {0} ∣ n - 1} (1 / 2) fun n : ℕ =>
      (((bienaymeLaw μ.toMeasure)[|leafCountEvent n]).real
        (finiteTreeEvent fun t =>
          ENNReal.ofReal (δ / (n : ℝ) ^ (1 / 4 : ℝ)) ≤
            supDev η (treeLeafDev (μ 0).toReal t (t.size : ℝ)))) := by
  obtain ⟨A, N, hlow⟩ := leafProb_poly_lower hc hne hap hDA
  have hGD := BGWLeaves.cor_GD2mieux hc hne hap ⟨hDA.choose, hDA.choose_spec⟩ hη0 hη1 hδ
  obtain ⟨C, c, hC, hcp, hb⟩ :=
    BGWLeaves.LeafConcentration.OeLemmas.IsOe.poly_mul (by norm_num) hGD A
  refine isOeOn_of_eventually_bound (N := N) (by norm_num)
    (fun n => cond_real_le_one' _ _ _) hC hcp ?_
  rintro n ⟨hn1, hdvd⟩ hnN
  refine (cond_leaf_le μ n _).trans ?_
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hlow' := hlow n hnN hn1 hdvd
  have hpos : 0 < (n : ℝ) ^ (-A) := Real.rpow_pos_of_pos hn0 _
  calc _ ≤ ((((bienaymeLaw μ.toMeasure)[|sizeGeEvent n]).real
        (finiteTreeEvent fun t =>
          ENNReal.ofReal (δ / (n : ℝ) ^ (1 / 4 : ℝ)) ≤
            supDev η (treeLeafDev (μ 0).toReal t (t.size : ℝ))))) / (n : ℝ) ^ (-A) :=
        div_le_div_of_nonneg_left measureReal_nonneg hpos hlow'
    _ = (n : ℝ) ^ A * _ := by
        simp only [Real.rpow_neg hn0.le, div_eq_mul_inv, inv_inv]; ring
    _ ≤ _ := hb n

/-- **Corollary 3.3** for all `n` (statement of `BGWLeaves.LeafMass.cor_Lambda_isOe`). -/
theorem cor_Lambda_isOe {μ : PMF ℕ} {θ : ℝ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hap : Aperiodic μ) (hDA : ∃ a, StableDomain μ θ a) {η δ : ℝ}
    (hη0 : 0 < η) (hη1 : η < 1) (hδ : 0 < δ) :
    IsOe (1 / 2) fun n : ℕ =>
      (((bienaymeLaw μ.toMeasure)[|leafCountEvent n]).real
        (finiteTreeEvent fun t =>
          ENNReal.ofReal (δ / (n : ℝ) ^ (1 / 4 : ℝ)) ≤
            supDev η (treeLeafDev (μ 0).toReal t (t.size : ℝ)))) := by
  obtain ⟨C, c, hC, hcp, hb⟩ := cor_Lambda_arith hc hne hap hDA hη0 hη1 hδ
  refine ⟨C, c, hC, hcp, fun n => ?_⟩
  by_cases hS : 1 ≤ n ∧ arithFactor μ {0} ∣ n - 1
  · exact hb n hS
  · have hlp : leafProb μ n = 0 := by
      by_cases hn : n = 0
      · subst hn
        have hemp : leafCountEvent 0 = ∅ := by
          ext T
          constructor
          · rintro ⟨t, rfl, ht⟩
            have hc0 : t.degrees.count 0 = 0 := ht
            have hnm : (0 : ℕ) ∉ t.degrees := List.count_eq_zero.1 hc0
            have hall : ∀ i ∈ t.degrees, 1 ≤ i := fun i hi =>
              Nat.one_le_iff_ne_zero.2 (fun h => hnm (h ▸ hi))
            have h1 := List.length_le_sum_of_one_le _ hall
            have h2 := PlaneTree.sum_degrees_add_one t
            have h3 := PlaneTree.length_degrees t
            omega
          · intro h; exact h.elim
        simp [leafProb, hemp]
      · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
        have hnd : ¬ arithFactor μ {0} ∣ m := fun h => hS ⟨by omega, by simpa using h⟩
        exact Arithmetic.leafProb_eq_zero_of_not_dvd hc hne hnd
    have hnull : (bienaymeLaw μ.toMeasure) (leafCountEvent n) = 0 :=
      (measureReal_eq_zero_iff (measure_ne_top _ _)).1 hlp
    beta_reduce
    rw [cond_eq_zero_of_meas_eq_zero hnull]
    simp only [measureReal_def, Measure.coe_zero, Pi.zero_apply, ENNReal.toReal_zero]
    positivity

end BGWLeaves.LeafMass.CorLambda
