module

public import BGWLeaves.Conditioning.Defs
import BGWLeaves.Conditioning.LeafTail
import BGWLeaves.LeafMass.Arithmetic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# M6 provider `PassageProof`

Proved providers of Lemma 4.3, its two deviation estimates and one-tree form,
the averaging formula `integral_cond_sizeGe`, and Proposition 4.4(i).
The constants in Lemma 4.3 are uniform in both the bounded test and the number of trees.
All exports have exactly the frozen types in `BGWLeaves.Conditioning`.
-/

@[expose] public section

namespace BGWLeaves.Conditioning.PassageProof

open MeasureTheory ProbabilityTheory Filter Asymptotics BGW
open BGW.StableTrees BGW.LocallyFinite BGWLeaves.StableAnalysis
open scoped ENNReal Topology

private theorem bounded_integrable {α : Type*} [MeasurableSpace α] (P : Measure α)
    [IsFiniteMeasure P] {M : ℝ} {U : α → ℝ} (hU : IsBoundedTest M U) : Integrable U P := by
  apply (integrable_const M).mono' hU.1.aestronglyMeasurable
  exact ae_of_all _ fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (hU.2 x).1]
    exact (hU.2 x).2

private theorem cond_integral_real {α : Type*} [MeasurableSpace α] (P : Measure α)
    (s : Set α) (U : α → ℝ) :
    ∫ x, U x ∂(P[|s]) = (P.real s)⁻¹ * ∫ x in s, U x ∂P := by
  simp only [ProbabilityTheory.cond, integral_smul_measure, ENNReal.toReal_inv, Measure.real, smul_eq_mul]

private theorem mass_mul_cond_integral {α : Type*} [MeasurableSpace α] (P : Measure α)
    [IsFiniteMeasure P] (s : Set α) (U : α → ℝ) :
    P.real s * (∫ x, U x ∂(P[|s])) = ∫ x in s, U x ∂P := by
  rw [cond_integral_real]
  by_cases hs : P s = 0
  · have hr : P.restrict s = 0 := Measure.restrict_eq_zero.2 hs
    simp [Measure.real, hs, hr]
  · have hr : P.real s ≠ 0 := ENNReal.toReal_ne_zero.mpr ⟨hs, measure_ne_top _ _⟩
    field_simp

private theorem sizeEvents_disjoint (n : ℕ) :
    Pairwise (fun i j : ℕ => Disjoint (sizeEvent (n + i)) (sizeEvent (n + j))) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro T hi hj
  exact hij (by have := hi.2; have := hj.2; omega)

private theorem sizeGe_ae_union {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1) (n : ℕ) :
    sizeGeEvent n =ᵐ[bienaymeLaw μ.toMeasure] ⋃ k : ℕ, sizeEvent (n + k) := by
  have hm : ∫⁻ k : ℕ, (k : ℝ≥0∞) ∂μ.toMeasure ≤ 1 := by
    rw [lintegral_countable']
    simpa only [PMF.toMeasure_apply_singleton μ _ (measurableSet_singleton _)] using hc.le
  have hne' : μ.toMeasure {1} ≠ 1 := by
    simpa only [PMF.toMeasure_apply_singleton μ _ (measurableSet_singleton _)] using hne
  have hae := ae_finiteVertices_bienaymeLaw μ.toMeasure hm hne'
  filter_upwards [hae] with T hT
  apply propext
  simp only [Set.mem_iUnion, sizeGeEvent, Set.mem_ofPred_eq, sizeEvent, hT,
    not_true_eq_false, false_or, true_and]
  constructor
  · intro hn
    exact ⟨{u | Present T u}.ncard - n, by omega⟩
  · rintro ⟨k, hk⟩
    omega

/-- The conditional size-tail law is the probability-weighted mixture of the size laws. -/
theorem integral_cond_sizeGe {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1) {M : ℝ}
    {U : LocallyFinite.Tree → ℝ} (hU : IsBoundedTest M U) (n : ℕ) :
    ∫ τ, U τ ∂((bienaymeLaw μ.toMeasure)[|sizeGeEvent n]) =
      ((bienaymeLaw μ.toMeasure).real (sizeGeEvent n))⁻¹ *
        ∑' k : ℕ, (bienaymeLaw μ.toMeasure).real (sizeEvent (n + k)) *
          ∫ τ, U τ ∂((bienaymeLaw μ.toMeasure)[|sizeEvent (n + k)]) := by
  rw [cond_integral_real, setIntegral_congr_set (sizeGe_ae_union hc hne n),
    integral_iUnion (fun k => measurableSet_sizeEvent _) (sizeEvents_disjoint n)
      ((bounded_integrable _ hU).mono_measure Measure.restrict_le_self)]
  simp_rw [mass_mul_cond_integral]

private theorem real_union_bound {α : Type*} [MeasurableSpace α] (P : Measure α)
    [IsFiniteMeasure P] {s : Set α} {H : ℕ → Set α} {x : ℕ → ℝ}
    (hsub : s ⊆ ⋃ k, H k) (hx0 : ∀ k, 0 ≤ x k) (hx : Summable x)
    (hH : ∀ k, P.real (H k) ≤ x k) : P.real s ≤ ∑' k, x k := by
  have hb : P s ≤ ENNReal.ofReal (∑' k, x k) := by
    rw [ENNReal.ofReal_tsum_of_nonneg hx0 hx]
    apply (measure_mono hsub).trans ((measure_iUnion_le _).trans ?_)
    apply ENNReal.tsum_le_tsum
    intro k
    rw [← ofReal_measureReal (measure_ne_top P (H k))]
    exact ENNReal.ofReal_le_ofReal (hH k)
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hb).trans_eq
    (ENNReal.toReal_ofReal (tsum_nonneg hx0))

private theorem real_pow_three_quarters {p : ℕ} (hp : 1 ≤ p) :
    (1 / (p : ℝ) ^ (1 / 4 : ℝ)) * p = (p : ℝ) ^ (3 / 4 : ℝ) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  calc (1 / (p : ℝ) ^ (1 / 4 : ℝ)) * p = p / (p : ℝ) ^ (1 / 4 : ℝ) := by ring
    _ = (p : ℝ) ^ (1 - 1 / 4 : ℝ) := by rw [Real.rpow_sub hp0, Real.rpow_one]
    _ = _ := by norm_num

/-- The lower leaf deviation, summed over every size above the threshold. -/
theorem passage_est_lambda_small {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ n j : ℕ, 1 ≤ j → j ≤ n →
      (forestLaw μ j).real {F | ∃ p m : ℕ, F ∈ forestEvent j p m ∧ n ≤ p ∧
        (m : ℝ) < (μ 0).toReal * p - (p : ℝ) ^ (3 / 4 : ℝ)} ≤ C * Real.exp (-c * (n : ℝ) ^ (1 / 2 : ℝ)) := by
  have h0 := LeafMass.Arithmetic.mu_zero_ne_zero hc hne
  have h1 := LeafMass.Arithmetic.mu_zero_ne_one hc hne
  obtain ⟨C, c, hC, hc0, hb⟩ := lem_GdesDev2_i μ h0 h1 (δ := 1) zero_lt_one
  let x : ℕ → ℝ := fun p => C * Real.exp (-c * (p : ℝ) ^ (1 / 2 : ℝ))
  have hx0 : ∀ p, 0 ≤ x p := fun p => by dsimp [x]; positivity
  have hxoe : IsOe (1 / 2) x := ⟨C, c, hC, hc0, fun p => le_rfl⟩
  obtain ⟨hx, C', c', hC', hc', htail⟩ := IsOe.tail (by norm_num) hx0 hxoe
  refine ⟨C', c', hC', hc', fun n j hj hjn => ?_⟩
  let H : ℕ → Set (Fin j → LocallyFinite.Tree) := fun k =>
    {F | ∃ m : ℕ, F ∈ forestEvent j (n + k) m ∧
      1 / ((n + k : ℕ) : ℝ) ^ (1 / 4 : ℝ) < |(m : ℝ) / (n + k : ℕ) - (μ 0).toReal|}
  have hsub : {F | ∃ p m : ℕ, F ∈ forestEvent j p m ∧ n ≤ p ∧
      (m : ℝ) < (μ 0).toReal * p - (p : ℝ) ^ (3 / 4 : ℝ)} ⊆ ⋃ k, H k := by
    rintro F ⟨p, m, hF, hnp, hm⟩
    have hp1 : 1 ≤ p := hj.trans (hjn.trans hnp)
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp1
    have hdev : (m : ℝ) / p < (μ 0).toReal - 1 / (p : ℝ) ^ (1 / 4 : ℝ) := by
      rw [div_lt_iff₀ hp0, sub_mul, real_pow_three_quarters hp1]
      exact hm
    have hh : 1 / (p : ℝ) ^ (1 / 4 : ℝ) < |(m : ℝ) / p - (μ 0).toReal| := by
      have hpos : 0 < 1 / (p : ℝ) ^ (1 / 4 : ℝ) := by positivity
      have hneg : (m : ℝ) / p - (μ 0).toReal < 0 := by linarith
      rw [abs_of_neg hneg]
      linarith
    apply Set.mem_iUnion.2
    refine ⟨p - n, ?_⟩
    dsimp [H]
    rw [Nat.add_sub_of_le hnp]
    exact ⟨m, hF, hh⟩
  have hxs : Summable (fun k => x (n + k)) := by
    simpa [Nat.add_comm] using (summable_nat_add_iff n).2 hx
  refine (real_union_bound (forestLaw μ j) hsub (fun k => hx0 _) hxs ?_).trans (htail n)
  intro k
  exact hb (n + k) j hj (hjn.trans (Nat.le_add_right n k))

private theorem leaf_degree_pos (t : PlaneTree) : 1 ≤ t.degreeCount 0 := by
  by_contra hn
  have hz : t.degreeCount 0 = 0 := by omega
  have hnot : 0 ∉ t.degrees := List.count_eq_zero.1 hz
  have hsum := List.length_le_sum_of_one_le t.degrees (fun i hi => by
    have hne : i ≠ 0 := fun h => hnot (h ▸ hi)
    omega)
  rw [PlaneTree.length_degrees] at hsum
  have := t.sum_degrees_add_one
  omega

private theorem forest_leaves_ge_components {j p m : ℕ} {F : Fin j → LocallyFinite.Tree}
    (hF : F ∈ forestEvent j p m) : j ≤ m := by
  obtain ⟨ts, hp, hm, rfl⟩ := hF
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun i _ => leaf_degree_pos (ts i))
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
    Nat.mul_one, hm] using hh

private theorem uniform_extend {x : ℕ → ℕ → ℝ}
    (hx : ∀ n j : ℕ, 1 ≤ j → j ≤ n → x j n ≤ 1) {C c : ℝ} (hC : 0 < C) (hc : 0 < c)
    (h : ∀ᶠ n : ℕ in atTop, ∀ j : ℕ, 1 ≤ j → j ≤ n →
      x j n ≤ C * Real.exp (-c * (n : ℝ) ^ (1 / 2 : ℝ))) : IsOeUniform (1 / 2) x := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 h
  refine ⟨C + Real.exp (c * (N : ℝ) ^ (1 / 2 : ℝ)), c, by positivity, hc, fun n j hj hjn => ?_⟩
  by_cases hn : N ≤ n
  · exact (hN n hn j hj hjn).trans (mul_le_mul_of_nonneg_right
      (by linarith [Real.exp_pos (c * (N : ℝ) ^ (1 / 2 : ℝ))]) (Real.exp_pos _).le)
  · have hpow : (n : ℝ) ^ (1 / 2 : ℝ) ≤ (N : ℝ) ^ (1 / 2 : ℝ) :=
      Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast (Nat.le_of_lt (not_le.1 hn))) (by norm_num)
    have he : 1 ≤ Real.exp (c * (N : ℝ) ^ (1 / 2 : ℝ)) * Real.exp (-c * (n : ℝ) ^ (1 / 2 : ℝ)) := by
      rw [← Real.exp_add, Real.one_le_exp_iff]
      nlinarith
    exact (hx n j hj hjn).trans (he.trans (by nlinarith [Real.exp_pos (-c * (n : ℝ) ^ (1 / 2 : ℝ))]))

private theorem cutoff_linear_lower {μ : PMF ℕ} (h0 : 0 < (μ 0).toReal) :
    ∀ᶠ n : ℕ in atTop, ((μ 0).toReal / 2) * n ≤ (leafCutoff μ n : ℝ) := by
  have ht := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 4)).comp
    tendsto_natCast_atTop_atTop
  filter_upwards [ht.eventually (eventually_lt_nhds (half_pos h0)), eventually_ge_atTop 1] with n hn hn1
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have heq : (n : ℝ) ^ (-(1 / 4 : ℝ)) = 1 / (n : ℝ) ^ (1 / 4 : ℝ) := by
    simp only [Real.rpow_neg hn0.le, one_div]
  have hw : (n : ℝ) ^ (3 / 4 : ℝ) ≤ ((μ 0).toReal / 2) * n := by
    rw [← real_pow_three_quarters hn1]
    apply mul_le_mul_of_nonneg_right _ hn0.le
    rw [← heq]
    exact hn.le
  have hh := Nat.le_ceil ((μ 0).toReal * n - (n : ℝ) ^ (3 / 4 : ℝ))
  change (μ 0).toReal / 2 * n ≤ ⌈(μ 0).toReal * n - (n : ℝ) ^ (3 / 4 : ℝ)⌉₊
  linarith

/-- The size deviation, summed over all leaf counts above the cutoff. -/
theorem passage_est_size_dev {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ n j : ℕ, 1 ≤ j → j ≤ n →
      (forestLaw μ j).real {F | ∃ p m : ℕ, F ∈ forestEvent j p m ∧ p < n ∧
        (μ 0).toReal * n - (n : ℝ) ^ (3 / 4 : ℝ) ≤ m ∧
        (p : ℝ) ^ (3 / 4 : ℝ) < |(p : ℝ) - m / (μ 0).toReal|} ≤
          C * Real.exp (-c * (n : ℝ) ^ (1 / 2 : ℝ)) := by
  have h0 := LeafMass.Arithmetic.mu_zero_ne_zero hc hne
  have h1 := LeafMass.Arithmetic.mu_zero_ne_one hc hne
  have h0R : 0 < (μ 0).toReal := ENNReal.toReal_pos h0 (μ.apply_ne_top 0)
  obtain ⟨C, c, hC, hc0, hb⟩ := lem_GdesDev2_ii μ h0 h1
  let x : ℕ → ℝ := fun m => C * Real.exp (-c * (m : ℝ) ^ (1 / 2 : ℝ))
  have hx0 : ∀ m, 0 ≤ x m := fun m => by dsimp [x]; positivity
  have hxoe : IsOe (1 / 2) x := ⟨C, c, hC, hc0, fun m => le_rfl⟩
  obtain ⟨hx, C', c', hC', hc', htail⟩ := IsOe.tail (by norm_num) hx0 hxoe
  apply uniform_extend (fun n j _ _ => measureReal_le_one) hC'
    (mul_pos hc' (Real.rpow_pos_of_pos (half_pos h0R) (1 / 2 : ℝ)))
  filter_upwards [cutoff_linear_lower h0R] with n hn
  intro j hj hjn
  let H : ℕ → Set (Fin j → LocallyFinite.Tree) := fun k =>
    {F | ∃ p : ℕ, F ∈ forestEvent j p (leafCutoff μ n + k) ∧
      (p : ℝ) ^ (3 / 4 : ℝ) < |(p : ℝ) - ((leafCutoff μ n + k : ℕ) : ℝ) / (μ 0).toReal|}
  have hsub : {F : Fin j → LocallyFinite.Tree | ∃ p m : ℕ, F ∈ forestEvent j p m ∧ p < n ∧
      (μ 0).toReal * n - (n : ℝ) ^ (3 / 4 : ℝ) ≤ m ∧
      (p : ℝ) ^ (3 / 4 : ℝ) < |(p : ℝ) - m / (μ 0).toReal|} ⊆ ⋃ k, H k := by
    rintro F ⟨p, m, hF, hpn, hmn, hd⟩
    have hcut : leafCutoff μ n ≤ m := Nat.ceil_le.2 hmn
    refine Set.mem_iUnion.2 ⟨m - leafCutoff μ n, ?_⟩
    dsimp [H]
    rw [Nat.add_sub_of_le hcut]
    exact ⟨p, hF, hd⟩
  have hxs : Summable (fun k => x (leafCutoff μ n + k)) := by
    simpa [Nat.add_comm] using (summable_nat_add_iff (leafCutoff μ n)).2 hx
  have hH : ∀ k, (forestLaw μ j).real (H k) ≤ x (leafCutoff μ n + k) := by
    intro k
    by_cases hjm : j ≤ leafCutoff μ n + k
    · exact hb _ j hj hjm
    · have he : H k = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.2
        rintro F ⟨p, hF, hd⟩
        exact hjm (forest_leaves_ge_components hF)
      rw [he, measureReal_empty]
      exact hx0 _
  have hr : ((μ 0).toReal / 2) ^ (1 / 2 : ℝ) * (n : ℝ) ^ (1 / 2 : ℝ) ≤
      (leafCutoff μ n : ℝ) ^ (1 / 2 : ℝ) := by
    rw [← Real.mul_rpow (half_pos h0R).le (Nat.cast_nonneg n)]
    exact Real.rpow_le_rpow (by positivity) hn (by norm_num)
  refine ((real_union_bound (forestLaw μ j) hsub (fun k => hx0 _) hxs hH).trans (htail _)).trans ?_
  apply mul_le_mul_of_nonneg_left _ hC'.le
  apply Real.exp_le_exp.2
  nlinarith

private theorem sizeGe_real_series {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1) (n : ℕ) :
    (bienaymeLaw μ.toMeasure).real (sizeGeEvent n) =
      ∑' k : ℕ, (bienaymeLaw μ.toMeasure).real (sizeEvent (n + k)) := by
  rw [measureReal_congr (sizeGe_ae_union hc hne n), Measure.real,
    measure_iUnion (sizeEvents_disjoint n) (fun k => measurableSet_sizeEvent _),
    ENNReal.tsum_toReal_eq (fun _ => measure_ne_top _ _)]
  rfl

/-- Convergence under exact sizes passes to convergence under a size-tail condition. -/
theorem prop_passage_i {μ : PMF ℕ} {θ : ℝ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hap : Aperiodic μ) (hDA : ∃ a, StableDomain μ θ a) {M : ℝ} {U : LocallyFinite.Tree → ℝ}
    (hU : IsBoundedTest M U) {L : ℝ}
    (h : Tendsto (fun n : ℕ => ∫ τ, U τ ∂((bienaymeLaw μ.toMeasure)[|sizeEvent n])) atTop (𝓝 L)) :
    Tendsto (fun n : ℕ => ∫ τ, U τ ∂((bienaymeLaw μ.toMeasure)[|sizeGeEvent n])) atTop (𝓝 L) := by
  obtain ⟨c, hc0, N0, hN0⟩ := LeafTail.sizeGe_poly_lower hc hne hap hDA (η := 1) zero_lt_one
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N1, hN1⟩ := Metric.tendsto_atTop.1 h (ε / 2) (half_pos hε)
  refine ⟨max (max N0 N1) 1, fun n hn => ?_⟩
  have hn0 : N0 ≤ n := (le_max_left _ _).trans ((le_max_left _ _).trans hn)
  have hn1 : N1 ≤ n := (le_max_right _ _).trans ((le_max_left _ _).trans hn)
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (le_trans (le_max_right _ _) hn)
  let P := bienaymeLaw μ.toMeasure
  let p : ℝ := P.real (sizeGeEvent n)
  let w : ℕ → ℝ := fun k => P.real (sizeEvent (n + k))
  let A : ℕ → ℝ := fun k => ∫ τ, U τ ∂(P[|sizeEvent (n + k)])
  have hp : 0 < p := lt_of_lt_of_le
    (mul_pos hc0 (Real.rpow_pos_of_pos hnpos _)) (hN0 n hn0)
  have hw0 : ∀ k, 0 ≤ w k := fun k => measureReal_nonneg
  have hws : Summable w := summable_measure_toReal (fun k => measurableSet_sizeEvent _)
    (sizeEvents_disjoint n)
  have hsumw : ∑' k, w k = p := (sizeGe_real_series hc hne n).symm
  have hwA : Summable (fun k => w k * A k) := by
    simp only [w, A, mass_mul_cond_integral]
    exact (hasSum_integral_iUnion (fun k => measurableSet_sizeEvent _) (sizeEvents_disjoint n)
      ((bounded_integrable P hU).mono_measure Measure.restrict_le_self)).summable
  have hb : ∀ k, ‖w k * A k - w k * L‖ ≤ (ε / 2) * w k := by
    intro k
    have hh := hN1 (n + k) (hn1.trans (Nat.le_add_right _ _))
    rw [Real.dist_eq] at hh
    rw [← mul_sub, norm_mul, Real.norm_eq_abs, abs_of_nonneg (hw0 k), Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_left hh.le (hw0 k)).trans_eq (mul_comm _ _)
  have he := (hwA.hasSum.sub (hws.hasSum.mul_right L)).norm_le_of_bounded
    (hws.hasSum.mul_left (ε / 2)) hb
  rw [hsumw, Real.norm_eq_abs] at he
  rw [Real.dist_eq, integral_cond_sizeGe hc hne hU n]
  change |p⁻¹ * (∑' k, w k * A k) - L| < ε
  calc
    |p⁻¹ * (∑' k, w k * A k) - L| = p⁻¹ * |(∑' k, w k * A k) - p * L| := by
      calc
        |p⁻¹ * (∑' k, w k * A k) - L| = |p⁻¹ * ((∑' k, w k * A k) - p * L)| := by
          congr 1
          field_simp
        _ = _ := by rw [abs_mul, abs_of_pos (inv_pos.2 hp)]
    _ ≤ p⁻¹ * ((ε / 2) * p) := mul_le_mul_of_nonneg_left he (inv_nonneg.2 hp.le)
    _ = ε / 2 := by field_simp
    _ < ε := half_lt_self hε

/-- Below the size threshold, the cutoff and the absence of size deviation force the window. -/
private theorem in_size_window_of_no_deviation {μ0 : ℝ} (h0 : 0 < μ0) {n p m : ℕ}
    (hpn : p < n) (hm : μ0 * n - (n : ℝ) ^ (3 / 4 : ℝ) ≤ m)
    (hd : |(p : ℝ) - m / μ0| ≤ (p : ℝ) ^ (3 / 4 : ℝ)) :
    (n : ℝ) - (1 / μ0 + 1) * (n : ℝ) ^ (3 / 4 : ℝ) ≤ p := by
  have hpow : (p : ℝ) ^ (3 / 4 : ℝ) ≤ (n : ℝ) ^ (3 / 4 : ℝ) :=
    Real.rpow_le_rpow (Nat.cast_nonneg p) (by exact_mod_cast hpn.le) (by norm_num)
  have hd' := (abs_le.1 hd).1
  have hm' : (n : ℝ) - (n : ℝ) ^ (3 / 4 : ℝ) / μ0 ≤ m / μ0 := by
    apply (le_div_iff₀ h0).2
    have hh : ((n : ℝ) - (n : ℝ) ^ (3 / 4 : ℝ) / μ0) * μ0 =
        μ0 * n - (n : ℝ) ^ (3 / 4 : ℝ) := by field_simp
    rwa [hh]
  have he : (1 / μ0 + 1) * (n : ℝ) ^ (3 / 4 : ℝ) =
      (n : ℝ) ^ (3 / 4 : ℝ) / μ0 + (n : ℝ) ^ (3 / 4 : ℝ) := by ring
  rw [he]
  linarith

open scoped symmDiff

private def finiteSizeGeEvent (j n : ℕ) : Set (Fin j → LocallyFinite.Tree) :=
  {F | ∃ p m : ℕ, F ∈ forestEvent j p m ∧ n ≤ p}

private theorem finite_forest_measurable {j : ℕ} {s : Set (Fin j → LocallyFinite.Tree)}
    (hs : ∀ F ∈ s, ∃ ts : Fin j → PlaneTree, F = fun i => (ts i).toLocallyFinite) :
    MeasurableSet s := by
  apply Set.Countable.measurableSet
  apply (Set.countable_range (fun ts : Fin j → PlaneTree => fun i => (ts i).toLocallyFinite)).mono
  rintro F hF
  obtain ⟨ts, rfl⟩ := hs F hF
  exact Set.mem_range_self _

private theorem finiteSizeGe_measurable (j n : ℕ) : MeasurableSet (finiteSizeGeEvent j n) := by
  apply finite_forest_measurable
  rintro F ⟨p, m, ⟨ts, hp, hm, hF⟩, hn⟩
  exact ⟨ts, hF⟩

private theorem forestLeafGe_measurable (j n : ℕ) : MeasurableSet (forestLeafGeEvent j n) := by
  apply finite_forest_measurable
  rintro F ⟨p, m, hn, ts, hp, hm, hF⟩
  exact ⟨ts, hF⟩

private theorem forestSizeGe_ae_finite {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (j n : ℕ) : forestSizeGeEvent j n =ᵐ[forestLaw μ j] finiteSizeGeEvent j n := by
  have hm : ∫⁻ k : ℕ, (k : ℝ≥0∞) ∂μ.toMeasure ≤ 1 := by
    rw [lintegral_countable']
    simpa only [PMF.toMeasure_apply_singleton μ _ (measurableSet_singleton _)] using hc.le
  have hne' : μ.toMeasure {1} ≠ 1 := by
    simpa only [PMF.toMeasure_apply_singleton μ _ (measurableSet_singleton _)] using hne
  have hfin := ae_finiteVertices_bienaymeLaw μ.toMeasure hm hne'
  have hF : ∀ᵐ F ∂forestLaw μ j, ∀ i, FiniteVertices (F i) := by
    apply ae_all_iff.2
    intro i
    exact (Measure.tendsto_eval_ae_ae (i := i)).eventually hfin
  filter_upwards [hF] with F hF
  apply propext
  constructor
  · rintro (hinf | ⟨p, ⟨ts, hp, heq⟩, hn⟩)
    · obtain ⟨i, hi⟩ := hinf
      exact (hi (hF i)).elim
    · exact ⟨p, ∑ i, (ts i).degreeCount 0, ⟨ts, hp, rfl, heq⟩, hn⟩
  · rintro ⟨p, m, ⟨ts, hp, hm, heq⟩, hn⟩
    exact Or.inr ⟨p, ⟨ts, hp, heq⟩, hn⟩

private theorem alpha_comparison {μ0 : ℝ} {n p : ℕ} (hn : 1 ≤ n) (hnp : n ≤ p)
    (hsmall : (n : ℝ) ^ (-(1 / 4 : ℝ)) ≤ μ0) :
    μ0 * n - (n : ℝ) ^ (3 / 4 : ℝ) ≤ μ0 * p - (p : ℝ) ^ (3 / 4 : ℝ) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hp : 1 ≤ p := hn.trans hnp
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  have hre (k : ℕ) (hk : 1 ≤ k) : (k : ℝ) ^ (3 / 4 : ℝ) =
      (k : ℝ) ^ (-(1 / 4 : ℝ)) * k := by
    rw [Real.rpow_neg (Nat.cast_nonneg k), ← one_div]
    exact (real_pow_three_quarters hk).symm
  have hpow := Real.rpow_le_rpow_of_nonpos hn0 (show (n : ℝ) ≤ p by exact_mod_cast hnp)
    (by norm_num : -(1 / 4 : ℝ) ≤ 0)
  rw [hre n hn, hre p hp]
  nlinarith [(mul_le_mul_of_nonneg_left (show (n : ℝ) ≤ p by exact_mod_cast hnp)
    (sub_nonneg.2 hsmall)), mul_le_mul_of_nonneg_right hpow hp0.le]

private theorem abs_integral_restrict_diff {α : Type*} [MeasurableSpace α] (P : Measure α)
    [IsFiniteMeasure P] {s t : Set α} (hs : MeasurableSet s) (ht : MeasurableSet t)
    {M : ℝ} {U : α → ℝ} (hU : IsBoundedTest M U) :
    |(∫ x in s, U x ∂P) - ∫ x in t, U x ∂P| ≤ M * P.real (s ∆ t) := by
  classical
  let f : α → ℝ := fun x => s.indicator U x - t.indicator U x
  have hi := bounded_integrable P hU
  rw [← integral_indicator hs, ← integral_indicator ht, ← integral_sub (hi.indicator hs) (hi.indicator ht)]
  have hzero : (s ∆ t).indicator f = f := by
    funext x
    by_cases hx : x ∈ s <;> by_cases hy : x ∈ t <;>
      simp [f, hx, hy, Set.mem_symmDiff]
  have he : (∫ x, f x ∂P) = ∫ x in s ∆ t, f x ∂P := by
    calc (∫ x, f x ∂P) = ∫ x, (s ∆ t).indicator f x ∂P := by rw [hzero]
      _ = _ := integral_indicator (hs.symmDiff ht)
  change |∫ x, f x ∂P| ≤ _
  rw [he]
  have hb : ∀ x ∈ s ∆ t, ‖f x‖ ≤ M := by
    intro x hx
    have hu0 := (hU.2 x).1
    have huM := (hU.2 x).2
    have hM : 0 ≤ M := hu0.trans huM
    by_cases hxs : x ∈ s <;> by_cases hxt : x ∈ t <;>
      simp [f, hxs, hxt, Real.norm_eq_abs, abs_of_nonneg hu0, huM, hM]
  simpa only [Real.norm_eq_abs, mul_comm] using
    (norm_setIntegral_le_of_norm_le_const (measure_lt_top P _) hb)

/-- Lemma 4.3, with constants uniform over both the forest size and the bounded test. -/
theorem lemma_passage {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ n j : ℕ, 1 ≤ j → j ≤ n →
      ∀ (M : ℝ) (U : (Fin j → LocallyFinite.Tree) → ℝ), IsBoundedTest M U →
        |(∫ F in forestSizeGeEvent j n, U F ∂forestLaw μ j) -
            ∫ F in forestLeafGeEvent j (leafCutoff μ n), U F ∂forestLaw μ j| ≤
          M * ((forestLaw μ j).real (forestSizeWindow (μ 0).toReal j n) +
            C * Real.exp (-c * (n : ℝ) ^ (1 / 2 : ℝ))) := by
  have h0 : 0 < (μ 0).toReal :=
    ENNReal.toReal_pos (LeafMass.Arithmetic.mu_zero_ne_zero hc hne) (μ.apply_ne_top 0)
  obtain ⟨C1, c1, hC1, hc1, hb1⟩ := passage_est_lambda_small hc hne
  obtain ⟨C2, c2, hC2, hc2, hb2⟩ := passage_est_size_dev hc hne
  let q : ℕ → ℕ → ℝ := fun j n =>
    (forestLaw μ j).real (finiteSizeGeEvent j n ∆ forestLeafGeEvent j (leafCutoff μ n)) -
      (forestLaw μ j).real (forestSizeWindow (μ 0).toReal j n)
  have hq : IsOeUniform (1 / 2) q := by
    apply uniform_extend (fun n j _ _ => by
      dsimp [q]
      linarith [show (forestLaw μ j).real
        (finiteSizeGeEvent j n ∆ forestLeafGeEvent j (leafCutoff μ n)) ≤ 1 from measureReal_le_one,
        show 0 ≤ (forestLaw μ j).real (forestSizeWindow (μ 0).toReal j n) from measureReal_nonneg])
      (add_pos hC1 hC2) (lt_min hc1 hc2)
    have ht := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 4)).comp tendsto_natCast_atTop_atTop
    filter_upwards [ht.eventually (eventually_lt_nhds h0), eventually_ge_atTop 1] with n hn hn1
    intro j hj hjn
    let E1 : Set (Fin j → LocallyFinite.Tree) := {F | ∃ p m : ℕ, F ∈ forestEvent j p m ∧ n ≤ p ∧
      (m : ℝ) < (μ 0).toReal * p - (p : ℝ) ^ (3 / 4 : ℝ)}
    let E2 : Set (Fin j → LocallyFinite.Tree) := {F | ∃ p m : ℕ, F ∈ forestEvent j p m ∧ p < n ∧
      (μ 0).toReal * n - (n : ℝ) ^ (3 / 4 : ℝ) ≤ m ∧
      (p : ℝ) ^ (3 / 4 : ℝ) < |(p : ℝ) - m / (μ 0).toReal|}
    have hsub : finiteSizeGeEvent j n ∆ forestLeafGeEvent j (leafCutoff μ n) ⊆
        forestSizeWindow (μ 0).toReal j n ∪ (E1 ∪ E2) := by
      intro F hF
      rcases hF with ⟨hs, hnt⟩ | ⟨ht, hns⟩
      · obtain ⟨p, m, hp, hnp⟩ := hs
        have hmc : ¬ leafCutoff μ n ≤ m := fun hm => hnt ⟨p, m, hm, hp⟩
        have hm : (m : ℝ) < (μ 0).toReal * n - (n : ℝ) ^ (3 / 4 : ℝ) :=
          Nat.lt_ceil.1 (lt_of_not_ge hmc)
        exact Or.inr (Or.inl ⟨p, m, hp, hnp,
          hm.trans_le (alpha_comparison hn1 hnp hn.le)⟩)
      · obtain ⟨p, m, hmc, hp⟩ := ht
        have hpn : p < n := by
          by_contra hpn
          exact hns ⟨p, m, hp, Nat.le_of_not_gt hpn⟩
        have hm : (μ 0).toReal * n - (n : ℝ) ^ (3 / 4 : ℝ) ≤ m := (Nat.ceil_le).1 hmc
        by_cases hd : (p : ℝ) ^ (3 / 4 : ℝ) < |(p : ℝ) - m / (μ 0).toReal|
        · exact Or.inr (Or.inr ⟨p, m, hp, hpn, hm, hd⟩)
        · have hw := in_size_window_of_no_deviation h0 hpn hm (le_of_not_gt hd)
          obtain ⟨ts, hps, hms, hts⟩ := hp
          exact Or.inl ⟨p, ⟨ts, hps, hts⟩, hw, hpn.le⟩
    have hP : (forestLaw μ j).real (finiteSizeGeEvent j n ∆ forestLeafGeEvent j (leafCutoff μ n)) ≤
        (forestLaw μ j).real (forestSizeWindow (μ 0).toReal j n) +
          ((forestLaw μ j).real E1 + (forestLaw μ j).real E2) := by
      exact (measureReal_mono hsub (measure_ne_top _ _)).trans
        ((measureReal_union_le _ _).trans (add_le_add le_rfl (measureReal_union_le E1 E2)))
    have he1 : C1 * Real.exp (-c1 * (n : ℝ) ^ (1 / 2 : ℝ)) ≤
        C1 * Real.exp (-min c1 c2 * (n : ℝ) ^ (1 / 2 : ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ hC1.le
      apply Real.exp_le_exp.2
      nlinarith [min_le_left c1 c2, Real.rpow_nonneg (Nat.cast_nonneg n) (1 / 2 : ℝ)]
    have he2 : C2 * Real.exp (-c2 * (n : ℝ) ^ (1 / 2 : ℝ)) ≤
        C2 * Real.exp (-min c1 c2 * (n : ℝ) ^ (1 / 2 : ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ hC2.le
      apply Real.exp_le_exp.2
      nlinarith [min_le_right c1 c2, Real.rpow_nonneg (Nat.cast_nonneg n) (1 / 2 : ℝ)]
    have hb1' := hb1 n j hj hjn
    have hb2' := hb2 n j hj hjn
    dsimp [q, E1, E2] at *
    nlinarith
  obtain ⟨C, c, hC, hc0, hq⟩ := hq
  refine ⟨C, c, hC, hc0, fun n j hj hjn M U hU => ?_⟩
  rw [setIntegral_congr_set (forestSizeGe_ae_finite hc hne j n)]
  have hM : 0 ≤ M := (hU.2 (fun _ => PlaneTree.leaf.toLocallyFinite)).1.trans (hU.2 (fun _ => PlaneTree.leaf.toLocallyFinite)).2
  refine (abs_integral_restrict_diff (forestLaw μ j) (finiteSizeGe_measurable j n)
    (forestLeafGe_measurable j _) hU).trans (mul_le_mul_of_nonneg_left ?_ hM)
  have hh := hq n j hj hjn
  dsimp [q] at hh
  linarith

private theorem forestEvent_one_iff (F : Fin 1 → LocallyFinite.Tree) (p m : ℕ) :
    F ∈ forestEvent 1 p m ↔ ∃ t : PlaneTree,
      t.toLocallyFinite = F 0 ∧ t.size = p ∧ t.degreeCount 0 = m := by
  constructor
  · rintro ⟨ts, hp, hm, hF⟩
    exact ⟨ts 0, (congrFun hF 0).symm, by simpa using hp, by simpa using hm⟩
  · rintro ⟨t, ht, hp, hm⟩
    refine ⟨fun _ => t, by simpa using hp, by simpa using hm, ?_⟩
    funext i
    have hi : i = 0 := Subsingleton.elim _ _
    simpa only [hi] using ht.symm

private theorem forestSizeEvent_one_iff (F : Fin 1 → LocallyFinite.Tree) (p : ℕ) :
    F ∈ forestSizeEvent 1 p ↔ F 0 ∈ sizeEvent p := by
  constructor
  · rintro ⟨ts, hp, hF⟩
    have ht : (ts 0).toLocallyFinite = F 0 := (congrFun hF 0).symm
    rw [← ht]
    exact ⟨(ts 0).finiteVertices_toLocallyFinite,
      by rw [ncard_present_toLocallyFinite]; simpa using hp⟩
  · rintro ⟨hfin, hp⟩
    obtain ⟨t, ht⟩ := (exists_toLocallyFinite_iff (F 0)).2 hfin
    refine ⟨fun _ => t, ?_, ?_⟩
    · simpa only [Fin.sum_univ_one] using
        (show t.size = p by rw [← ht, ncard_present_toLocallyFinite] at hp; exact hp)
    · funext i
      have hi : i = 0 := Subsingleton.elim _ _
      simpa only [hi] using ht.symm

private theorem forestSizeGe_one (n : ℕ) :
    forestSizeGeEvent 1 n = (fun F : Fin 1 → LocallyFinite.Tree => F 0) ⁻¹' sizeGeEvent n := by
  ext F
  change ((∃ i, ¬ FiniteVertices (F i)) ∨ ∃ p, F ∈ forestSizeEvent 1 p ∧ n ≤ p) ↔
    (¬ FiniteVertices (F 0) ∨ n ≤ {u | Present (F 0) u}.ncard)
  simp_rw [forestSizeEvent_one_iff]
  constructor
  · rintro (⟨i, hi⟩ | ⟨p, ⟨hfin, hp⟩, hn⟩)
    · have hi0 : i = 0 := Subsingleton.elim _ _
      exact Or.inl (hi0 ▸ hi)
    · exact Or.inr (by omega)
  · rintro (hi | hn)
    · exact Or.inl ⟨0, hi⟩
    · by_cases hfin : FiniteVertices (F 0)
      · exact Or.inr ⟨_, ⟨hfin, rfl⟩, hn⟩
      · exact Or.inl ⟨0, hfin⟩

private theorem forestLeafGe_one (m : ℕ) :
    forestLeafGeEvent 1 m = (fun F : Fin 1 → LocallyFinite.Tree => F 0) ⁻¹' leafGeEvent m := by
  ext F
  constructor
  · rintro ⟨p, q, hmq, hF⟩
    obtain ⟨t, ht, hp, hq⟩ := (forestEvent_one_iff F p q).1 hF
    exact ⟨t, ht, by omega⟩
  · rintro ⟨t, ht, hm⟩
    exact ⟨t.size, t.degreeCount 0, hm, (forestEvent_one_iff F _ _).2 ⟨t, ht, rfl, rfl⟩⟩

private theorem forestSizeWindow_one (μ0 : ℝ) (n : ℕ) :
    forestSizeWindow μ0 1 n = (fun F : Fin 1 → LocallyFinite.Tree => F 0) ⁻¹' sizeWindow μ0 n := by
  ext F
  simp only [forestSizeWindow, sizeWindow, Set.mem_ofPred_eq, Set.mem_preimage,
    forestSizeEvent_one_iff]

/-- The one-tree form of the uniform passage estimate. -/
theorem lemma_passage_tree {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ n : ℕ, 1 ≤ n →
      ∀ (M : ℝ) (U : LocallyFinite.Tree → ℝ), IsBoundedTest M U →
        |(∫ τ in sizeGeEvent n, U τ ∂bienaymeLaw μ.toMeasure) -
            ∫ τ in leafGeEvent (leafCutoff μ n), U τ ∂bienaymeLaw μ.toMeasure| ≤
          M * ((bienaymeLaw μ.toMeasure).real (sizeWindow (μ 0).toReal n) +
            C * Real.exp (-c * (n : ℝ) ^ (1 / 2 : ℝ))) := by
  obtain ⟨C, c, hC, hc0, hb⟩ := lemma_passage hc hne
  refine ⟨C, c, hC, hc0, fun n hn M U hU => ?_⟩
  let e := MeasurableEquiv.funUnique (Fin 1) LocallyFinite.Tree
  have hmap : (forestLaw μ 1).map e = bienaymeLaw μ.toMeasure :=
    (measurePreserving_funUnique (bienaymeLaw μ.toMeasure) (Fin 1)).map_eq
  have hInt (s : Set LocallyFinite.Tree) :
      (∫ τ in s, U τ ∂bienaymeLaw μ.toMeasure) =
        ∫ F in e ⁻¹' s, U (e F) ∂forestLaw μ 1 := by
    rw [← hmap, setIntegral_map_equiv]
  have hmass (s : Set LocallyFinite.Tree) :
      (bienaymeLaw μ.toMeasure).real s = (forestLaw μ 1).real (e ⁻¹' s) := by
    rw [Measure.real, ← hmap, e.map_apply]
    rfl
  have htest : IsBoundedTest M (fun F : Fin 1 → LocallyFinite.Tree => U (e F)) :=
    ⟨hU.1.comp e.measurable, fun F => hU.2 (e F)⟩
  have hh := hb n 1 (by omega) hn M (fun F => U (e F)) htest
  rw [hInt, hInt, hmass]
  have he : (e : (Fin 1 → LocallyFinite.Tree) → LocallyFinite.Tree) = fun F => F 0 := by
    funext F
    exact congrArg F (Subsingleton.elim _ _)
  simpa only [forestSizeGe_one, forestLeafGe_one, forestSizeWindow_one, he] using hh

end BGWLeaves.Conditioning.PassageProof
