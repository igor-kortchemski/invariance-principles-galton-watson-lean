/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module
public import BGW.Probability.PoissonCharacterizationCounts
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Complex.Basic
import BGW.Probability.PoissonCharacterizationLimit
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! Joint complex generating functions of disjoint measurable subsets of a finite-rate box.

On each grid cell, the generating function agrees with its linear count expression when the
containing cell has at most one arrival. The integrated remainder is controlled by the mean count
minus the probability of a nonempty cell. Stationarity and the exponential no-arrival law make
the sum of these remainders vanish as the grid is refined. Intersecting cells with the tested sets
allows arbitrary box endpoints without an additional time partition. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal BigOperators

namespace BGW.Probability

/-- Products of powers of numbers in the complex unit disk stay in that disk. -/
private lemma norm_count_pgf_le_one {ι : Type*} (s : Finset ι) (z : ι → ℂ) (N : ι → ℕ)
    (hz : ∀ i ∈ s, ‖z i‖ ≤ 1) : ‖∏ i ∈ s, z i ^ N i‖ ≤ 1 := by
  rw [Complex.norm_prod]
  apply Finset.prod_le_one₀ (fun _ _ => norm_nonneg _)
  intro i hi
  rw [norm_pow]
  exact pow_le_one₀ (norm_nonneg _) (hz i hi)

private lemma count_pgf_eq_linear {ι : Type*} (s : Finset ι) (z : ι → ℂ) (N : ι → ℕ)
    (hN : ∑ i ∈ s, N i ≤ 1) :
    ∏ i ∈ s, z i ^ N i = 1 + ∑ i ∈ s, (N i : ℂ) * (z i - 1) := by
  classical
  by_cases he : ∃ i ∈ s, N i ≠ 0
  · obtain ⟨i, hi, hni⟩ := he
    have hs := Finset.sum_le_one_iff.1 hN
    have hni1 : N i = 1 := (hs i i hi hi hni hni).2
    have hzero (j : ι) (hj : j ∈ s) (hji : j ≠ i) : N j = 0 := by
      by_contra hn
      exact hji (hs j i hj hi hn hni).1
    rw [Finset.prod_eq_single i, Finset.sum_eq_single i]
    · simp [hni1]
    · intro j hj hji
      simp [hzero j hj hji]
    · exact fun h => (h hi).elim
    · intro j hj hji
      simp [hzero j hj hji]
    · exact fun h => (h hi).elim
  · push Not at he
    have hp : ∏ i ∈ s, z i ^ N i = 1 := Finset.prod_eq_one fun i hi => by
      rw [he i hi, pow_zero]
    have hs : ∑ i ∈ s, (N i : ℂ) * (z i - 1) = 0 := Finset.sum_eq_zero fun i hi => by
      rw [he i hi]
      simp
    rw [hp, hs, add_zero]

/-- The linear generating-function remainder is controlled by arrivals beyond the first. -/
private lemma norm_count_pgf_remainder {ι : Type*} (s : Finset ι) (z : ι → ℂ) (N : ι → ℕ)
    (hz : ∀ i ∈ s, ‖z i‖ ≤ 1) (n : ℕ) (hN : ∑ i ∈ s, N i ≤ n) :
    ‖(∏ i ∈ s, z i ^ N i) - (1 + ∑ i ∈ s, (N i : ℂ) * (z i - 1))‖ ≤
      6 * ((n : ℝ) - if n = 0 then 0 else 1) := by
  by_cases hn : n ≤ 1
  · rw [count_pgf_eq_linear s z N (hN.trans hn), sub_self, norm_zero]
    rcases n with _ | n
    · norm_num
    · have : n = 0 := by omega
      subst n
      norm_num
  · have hn2 : 2 ≤ n := by omega
    have hsum : ‖∑ i ∈ s, (N i : ℂ) * (z i - 1)‖ ≤ 2 * (n : ℝ) := by
      calc
        _ ≤ ∑ i ∈ s, ‖(N i : ℂ) * (z i - 1)‖ := norm_sum_le _ _
        _ ≤ ∑ i ∈ s, (N i : ℝ) * 2 := by
          apply Finset.sum_le_sum
          intro i hi
          rw [Complex.norm_mul, Complex.norm_natCast]
          gcongr
          exact (norm_sub_le _ _).trans (by
            simpa only [norm_one, one_add_one_eq_two] using add_le_add_left (hz i hi) 1)
        _ = 2 * ((∑ i ∈ s, N i : ℕ) : ℝ) := by
          push_cast
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          ring
        _ ≤ _ := by exact_mod_cast Nat.mul_le_mul_left 2 hN
    calc
      _ ≤ ‖∏ i ∈ s, z i ^ N i‖ + ‖1 + ∑ i ∈ s, (N i : ℂ) * (z i - 1)‖ :=
        norm_sub_le _ _
      _ ≤ 1 + (1 + 2 * (n : ℝ)) := add_le_add (norm_count_pgf_le_one s z N hz)
        ((norm_add_le _ _).trans (by simpa only [norm_one] using add_le_add_right hsum 1))
      _ ≤ _ := by
        have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn2
        rw [ite_eq_right (by omega : n ≠ 0)]
        linarith

/-- Products of contractions differ by at most the sum of the differences of their factors. -/
private lemma norm_prod_sub_prod_le_sum {ι : Type*} (s : Finset ι) (f g : ι → ℂ)
    (hf : ∀ i ∈ s, ‖f i‖ ≤ 1) (hg : ∀ i ∈ s, ‖g i‖ ≤ 1) :
    ‖(∏ i ∈ s, f i) - ∏ i ∈ s, g i‖ ≤ ∑ i ∈ s, ‖f i - g i‖ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.sum_insert ha]
    have hprod : ‖∏ i ∈ s, g i‖ ≤ 1 := by
      simpa using norm_count_pgf_le_one s g (fun _ => 1) (fun i hi => hg i (by simp [hi]))
    calc
      _ = ‖f a * ((∏ i ∈ s, f i) - ∏ i ∈ s, g i) +
          (f a - g a) * ∏ i ∈ s, g i‖ := by congr 1; ring
      _ ≤ ‖f a‖ * ‖(∏ i ∈ s, f i) - ∏ i ∈ s, g i‖ +
          ‖f a - g a‖ * ‖∏ i ∈ s, g i‖ := by
        rw [← Complex.norm_mul, ← Complex.norm_mul]
        exact norm_add_le _ _
      _ ≤ 1 * (∑ i ∈ s, ‖f i - g i‖) + ‖f a - g a‖ * 1 := by
        gcongr
        · exact hf a (by simp)
        · exact ih (fun i hi => hf i (by simp [hi])) (fun i hi => hg i (by simp [hi]))
      _ = _ := by ring

end BGW.Probability

namespace BGW.Probability

variable {Ω M : Type*} [MeasurableSpace Ω] [MeasurableSpace M]
variable {P : Measure Ω} [IsProbabilityMeasure P] {ξ : Ω → Measure (ℝ≥0 × M)} {A : Set M}

omit [IsProbabilityMeasure P] in
/-- A finite union of finite-rate mark sets has finite rate. -/
lemma isFiniteRate_iUnion {k : ℕ} (A : Fin k → Set M) (hA : ∀ i, IsFiniteRate P ξ (A i)) :
    IsFiniteRate P ξ (⋃ i, A i) := by
  refine ⟨MeasurableSet.iUnion (fun i => (hA i).1), fun t => ?_⟩
  filter_upwards [ae_all_iff.2 (fun i => (hA i).2 t)] with ω hω
  have hs : Ioc 0 t ×ˢ (⋃ i, A i) = ⋃ i, Ioc 0 t ×ˢ A i := by ext p; simp
  rw [hs]
  apply (measure_iUnion_le _).trans_lt
  rw [tsum_fintype]
  exact ENNReal.sum_lt_top.2 fun i _ => hω i

/-- Counts of disjoint measurable subsets are bounded by the count of a containing set. -/
private lemma sum_counts_le {k : ℕ} (μ : Measure (ℝ≥0 × M)) (B : Fin k → Set (ℝ≥0 × M))
    (hB : ∀ i, MeasurableSet (B i)) (hdisj : Pairwise (Function.onFun Disjoint B))
    {D : Set (ℝ≥0 × M)} (hsub : ∀ i, B i ⊆ D) : ∑ i, μ (B i) ≤ μ D := by
  calc
    _ = μ (⋃ i, B i) := by rw [measure_iUnion hdisj hB, tsum_fintype]
    _ ≤ _ := measure_mono (iUnion_subset hsub)

/-- Intersecting a grid with a measurable subset still partitions that subset. -/
private lemma sum_grid_inter_counts (μ : Measure (ℝ≥0 × M)) (hA : MeasurableSet A)
    (T : ℝ≥0) {n : ℕ} (hn : n ≠ 0) {B : Set (ℝ≥0 × M)}
    (hB : MeasurableSet B) (hsub : B ⊆ Ioc 0 T ×ˢ A) :
    ∑ i : Fin n, μ (B ∩ gridBox T n i A) = μ B := by
  have he := sum_grid_counts hA (μ.restrict B) T hn
  have hc (i : Fin n) : (μ.restrict B) (gridBox T n i A) =
      μ (B ∩ gridBox T n i A) := by
    rw [Measure.restrict_apply' hB, inter_comm]
  rw [Measure.restrict_apply' hB, inter_eq_right.2 hsub] at he
  simpa only [hc] using he

omit [IsProbabilityMeasure P] in
/-- A measurable subset of a finite-rate box has finite count almost surely. -/
private lemma ae_finite_count_subset (hA : IsFiniteRate P ξ A) {T : ℝ≥0}
    {B : Set (ℝ≥0 × M)} (hsub : B ⊆ Ioc 0 T ×ˢ A) :
    ∀ᵐ ω ∂P, ξ ω B < ⊤ :=
  (hA.2 T).mono fun _ hω => (measure_mono hsub).trans_lt hω

/-- A measurable subset of a finite-rate box has finite expected count. -/
private lemma lintegral_count_subset_lt_top (hξ : IsTimeSimpleLevy P ξ) (hA : IsFiniteRate P ξ A)
    {T : ℝ≥0} {B : Set (ℝ≥0 × M)} (hsub : B ⊆ Ioc 0 T ×ˢ A) :
    ∫⁻ ω, ξ ω B ∂P < ⊤ := by
  apply (lintegral_mono (fun _ => measure_mono hsub)).trans_lt
  rw [lintegral_count_window hξ hA (zero_le : (0 : ℝ≥0) ≤ T)]
  exact ENNReal.mul_lt_top ENNReal.coe_lt_top (markRate_lt_top hξ hA)

/-- Natural-number counts of measurable subsets of finite-rate boxes are integrable. -/
private lemma integrable_natCount_subset (hξ : IsTimeSimpleLevy P ξ) (hA : IsFiniteRate P ξ A)
    {T : ℝ≥0} {B : Set (ℝ≥0 × M)} (hB : MeasurableSet B) (hsub : B ⊆ Ioc 0 T ×ˢ A) :
    Integrable (fun ω => (natCount (ξ ω) B : ℝ)) P := by
  have hm := measurable_count hξ.measurable hB
  have he := ae_natCount_cast hξ hB (ae_finite_count_subset hA hsub)
  apply (integrable_toReal_of_lintegral_ne_top hm.aemeasurable
    (lintegral_count_subset_lt_top hξ hA hsub).ne).congr
  filter_upwards [he] with ω hω
  simpa only [ENNReal.toReal_natCast] using congrArg ENNReal.toReal hω.symm

omit [IsProbabilityMeasure P] in
/-- Expected natural-number counts agree with the extended nonnegative expected counts. -/
lemma integral_natCount_subset (hξ : IsTimeSimpleLevy P ξ) (hA : IsFiniteRate P ξ A)
    {T : ℝ≥0} {B : Set (ℝ≥0 × M)} (hB : MeasurableSet B) (hsub : B ⊆ Ioc 0 T ×ˢ A) :
    ∫ ω, (natCount (ξ ω) B : ℝ) ∂P = (∫⁻ ω, ξ ω B ∂P).toReal := by
  rw [← integral_toReal (measurable_count hξ.measurable hB).aemeasurable
    (ae_finite_count_subset hA hsub)]
  apply integral_congr_ae
  filter_upwards [ae_natCount_cast hξ hB (ae_finite_count_subset hA hsub)] with ω hω
  simpa only [ENNReal.toReal_natCast] using congrArg ENNReal.toReal hω

end BGW.Probability

namespace BGW.Probability

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- Generating functions of measurable natural-number vectors are measurable. -/
private lemma measurable_count_pgf {k : ℕ} (N : Fin k → Ω → ℕ) (hN : ∀ i, Measurable (N i))
    (z : Fin k → ℂ) : Measurable (fun ω => ∏ i, z i ^ N i ω) := by
  apply Finset.measurable_prod
  intro i _
  exact (Measurable.of_discrete : Measurable (fun n : ℕ => z i ^ n)).comp (hN i)

/-- Generating functions in the complex unit polydisk are integrable. -/
private lemma integrable_count_pgf {k : ℕ} (N : Fin k → Ω → ℕ) (hN : ∀ i, Measurable (N i))
    (z : Fin k → ℂ) (hz : ∀ i, ‖z i‖ ≤ 1) :
    Integrable (fun ω => ∏ i, z i ^ N i ω) P :=
  Integrable.of_bound (measurable_count_pgf N hN z).aestronglyMeasurable 1
    (Eventually.of_forall fun ω => norm_count_pgf_le_one _ z (fun i => N i ω) (fun i _ => hz i))

/-- The mean generating-function remainder is bounded by the expected number of extra arrivals. -/
private lemma norm_integral_count_pgf_remainder {k : ℕ} (N : Fin k → Ω → ℕ)
    (hN : ∀ i, Measurable (N i)) (hNi : ∀ i, Integrable (fun ω => (N i ω : ℝ)) P)
    (U : Ω → ℕ) (hU : Measurable U) (hUi : Integrable (fun ω => (U ω : ℝ)) P)
    (hNU : ∀ᵐ ω ∂P, ∑ i, N i ω ≤ U ω) (z : Fin k → ℂ) (hz : ∀ i, ‖z i‖ ≤ 1) :
    ‖(∫ ω, ∏ i, z i ^ N i ω ∂P) -
        (1 + ∑ i, ((∫ ω, (N i ω : ℝ) ∂P : ℝ) : ℂ) * (z i - 1))‖ ≤
      6 * ((∫ ω, (U ω : ℝ) ∂P) - P.real {ω | U ω ≠ 0}) := by
  have hc (i : Fin k) : Integrable (fun ω => (N i ω : ℂ) * (z i - 1)) P := by
    exact (hNi i).ofReal.mul_const _
  have hlin : Integrable (fun ω => (1 : ℂ) + ∑ i, (N i ω : ℂ) * (z i - 1)) P :=
    integrable_const 1 |>.add (integrable_finsetSum _ (fun i _ => hc i))
  have hlin_eq : (∫ ω, (1 : ℂ) + ∑ i, (N i ω : ℂ) * (z i - 1) ∂P) =
      1 + ∑ i, ((∫ ω, (N i ω : ℝ) ∂P : ℝ) : ℂ) * (z i - 1) := by
    rw [integral_add (integrable_const 1) (integrable_finsetSum _ (fun i _ => hc i)),
      integral_const, probReal_univ, one_smul, integral_finsetSum _ (fun i _ => hc i)]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    rw [integral_mul_const]
    congr 1
    simpa only [Complex.ofReal_natCast] using
      (integral_complex_ofReal (μ := P) (f := fun ω => (N i ω : ℝ)))
  have hE : MeasurableSet {ω | U ω ≠ 0} :=
    (measurableSet_eq_fun hU measurable_const).compl
  have hI : Integrable ({ω | U ω ≠ 0}.indicator (fun _ => (1 : ℝ))) P :=
    (integrable_const 1).indicator hE
  have hbound : Integrable (fun ω => 6 * ((U ω : ℝ) - if U ω = 0 then 0 else 1)) P := by
    convert (hUi.sub hI).const_mul 6 using 1
    funext ω
    dsimp only [Pi.sub_apply]
    by_cases hh : U ω = 0 <;> simp [hh]
  rw [← hlin_eq, ← integral_sub (integrable_count_pgf N hN z hz) hlin]
  calc
    _ ≤ ∫ ω, ‖(∏ i, z i ^ N i ω) -
        (1 + ∑ i, (N i ω : ℂ) * (z i - 1))‖ ∂P := norm_integral_le_integral_norm _
    _ ≤ ∫ ω, 6 * ((U ω : ℝ) - if U ω = 0 then 0 else 1) ∂P := by
      apply integral_mono_ae ((integrable_count_pgf N hN z hz).sub hlin).norm hbound
      filter_upwards [hNU] with ω hω
      exact norm_count_pgf_remainder _ z (fun i => N i ω) (fun i _ => hz i) (U ω) hω
    _ = _ := by
      rw [integral_const_mul, integral_sub hUi]
      · congr 2
        rw [← integral_indicator_one hE]
        apply integral_congr_ae
        exact Eventually.of_forall fun ω => by by_cases hh : U ω = 0 <;> simp [hh]
      · convert hI using 1
        funext ω
        by_cases hh : U ω = 0 <;> simp [hh]

end BGW.Probability

namespace BGW.Probability

/-- The norm of a generating-function exponent is bounded by twice its total intensity. -/
private lemma norm_count_exponent_le {k : ℕ} (m : Fin k → ℝ) (hm : ∀ i, 0 ≤ m i)
    (z : Fin k → ℂ) (hz : ∀ i, ‖z i‖ ≤ 1) :
    ‖∑ i, (m i : ℂ) * (z i - 1)‖ ≤ 2 * ∑ i, m i := by
  calc
    _ ≤ ∑ i, ‖(m i : ℂ) * (z i - 1)‖ := norm_sum_le _ _
    _ ≤ ∑ i, m i * 2 := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hm i)]
      have hs : ‖z i - 1‖ ≤ 2 := (norm_sub_le _ _).trans (by
        simpa only [norm_one, one_add_one_eq_two] using add_le_add_left (hz i) 1)
      exact mul_le_mul_of_nonneg_left hs (hm i)
    _ = _ := by rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring

/-- Generating-function exponents in the unit polydisk have nonpositive real part. -/
private lemma norm_exp_count_exponent_le_one {k : ℕ} (m : Fin k → ℝ) (hm : ∀ i, 0 ≤ m i)
    (z : Fin k → ℂ) (hz : ∀ i, ‖z i‖ ≤ 1) :
    ‖Complex.exp (∑ i, (m i : ℂ) * (z i - 1))‖ ≤ 1 := by
  rw [Complex.norm_exp, Real.exp_le_one_iff]
  simp only [Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.sub_re,
    Complex.one_re, Complex.ofReal_im, zero_mul, sub_zero]
  exact Finset.sum_nonpos fun i _ =>
    mul_nonpos_of_nonneg_of_nonpos (hm i) (sub_nonpos.2 ((Complex.re_le_norm _).trans (hz i)))

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- The mean generating function in the unit polydisk has norm at most one. -/
private lemma norm_integral_count_pgf_le_one {k : ℕ} (N : Fin k → Ω → ℕ)
    (hN : ∀ i, Measurable (N i)) (z : Fin k → ℂ) (hz : ∀ i, ‖z i‖ ≤ 1) :
    ‖∫ ω, ∏ i, z i ^ N i ω ∂P‖ ≤ 1 := by
  calc
    _ ≤ ∫ ω, ‖∏ i, z i ^ N i ω‖ ∂P := norm_integral_le_integral_norm _
    _ ≤ ∫ _ω, (1 : ℝ) ∂P := by
      apply integral_mono (integrable_count_pgf N hN z hz).norm (integrable_const 1)
      intro ω
      exact norm_count_pgf_le_one _ z (fun i => N i ω) (fun i _ => hz i)
    _ = _ := by simp

/-- The transform in a small cell differs from its exponential approximation by two remainders. -/
private lemma norm_integral_count_pgf_sub_exp_le {k : ℕ} (N : Fin k → Ω → ℕ)
    (hN : ∀ i, Measurable (N i)) (hNi : ∀ i, Integrable (fun ω => (N i ω : ℝ)) P)
    (U : Ω → ℕ) (hU : Measurable U) (hUi : Integrable (fun ω => (U ω : ℝ)) P)
    (hNU : ∀ᵐ ω ∂P, ∑ i, N i ω ≤ U ω) (z : Fin k → ℂ) (hz : ∀ i, ‖z i‖ ≤ 1)
    (b : ℝ) (hb : 2 * b ≤ 1) (hmean : ∑ i, (∫ ω, (N i ω : ℝ) ∂P) ≤ b) :
    ‖(∫ ω, ∏ i, z i ^ N i ω ∂P) -
        Complex.exp (∑ i, ((∫ ω, (N i ω : ℝ) ∂P : ℝ) : ℂ) * (z i - 1))‖ ≤
      6 * ((∫ ω, (U ω : ℝ) ∂P) - P.real {ω | U ω ≠ 0}) + (2 * b) ^ 2 := by
  let m : Fin k → ℝ := fun i => ∫ ω, (N i ω : ℝ) ∂P
  have hm (i : Fin k) : 0 ≤ m i := integral_nonneg fun _ => Nat.cast_nonneg _
  let q : ℂ := ∑ i, (m i : ℂ) * (z i - 1)
  have hq : ‖q‖ ≤ 2 * b := (norm_count_exponent_le m hm z hz).trans (by gcongr)
  have he : ‖(1 + q) - Complex.exp q‖ ≤ (2 * b) ^ 2 := by
    calc
      _ = ‖Complex.exp q - 1 - q‖ := by rw [← norm_neg]; congr 1; ring
      _ ≤ ‖q‖ ^ 2 := Complex.norm_exp_sub_one_sub_id_le (hq.trans hb)
      _ ≤ _ := by gcongr
  exact (norm_sub_le_norm_sub_add_norm_sub _ (1 + q) _).trans
    (add_le_add (norm_integral_count_pgf_remainder N hN hNi U hU hUi hNU z hz) he)

end BGW.Probability

namespace BGW.Probability

variable {Ω M : Type*} [MeasurableSpace Ω] [MeasurableSpace M]
variable {P : Measure Ω} [IsProbabilityMeasure P] {ξ : Ω → Measure (ℝ≥0 × M)} {A : Set M}

omit [MeasurableSpace M] in
/-- Each cell of a uniform grid lies in its full time window. -/
private lemma gridBox_subset_window (T : ℝ≥0) {n : ℕ} (hn : n ≠ 0) (i : Fin n) :
    gridBox T n i A ⊆ Ioc 0 T ×ˢ A := by
  apply Set.prod_mono _ Subset.rfl
  intro x hx
  exact ⟨(zero_le : (0 : ℝ≥0) ≤ pointGridTime T n i).trans_lt hx.1,
    hx.2.trans (by simpa [pointGridTime_end T hn] using
      pointGridTime_monotone T hn (show i + 1 ≤ n by omega))⟩

omit [IsProbabilityMeasure P] in
/-- Natural counts of grid intersections add to the count of a measurable subset. -/
private lemma ae_sum_grid_natCount (hξ : IsTimeSimpleLevy P ξ) (hA : IsFiniteRate P ξ A)
    (T : ℝ≥0) {n : ℕ} (hn : n ≠ 0) {B : Set (ℝ≥0 × M)}
    (hB : MeasurableSet B) (hsub : B ⊆ Ioc 0 T ×ˢ A) :
    ∀ᵐ ω ∂P, ∑ i : Fin n, natCount (ξ ω) (B ∩ gridBox T n i A) = natCount (ξ ω) B := by
  have hi : ∀ᵐ ω ∂P, ∀ i : Fin n,
      (natCount (ξ ω) (B ∩ gridBox T n i A) : ℝ≥0∞) = ξ ω (B ∩ gridBox T n i A) :=
    ae_all_iff.2 fun i => ae_natCount_cast hξ (hB.inter (measurable_box hA.1))
      (ae_finite_count_subset hA (inter_subset_left.trans hsub))
  filter_upwards [hi, ae_natCount_cast hξ hB (ae_finite_count_subset hA hsub)] with ω hi hω
  apply Nat.cast_injective (R := ℝ≥0∞)
  rw [Nat.cast_sum, hω]
  simp only [hi]
  exact sum_grid_inter_counts (ξ ω) hA.1 T hn hB hsub

omit [IsProbabilityMeasure P] in
/-- Counts of disjoint measurable subsets are bounded in `ℕ` by a containing finite count. -/
private lemma ae_sum_natCount_le {k : ℕ} (hξ : IsTimeSimpleLevy P ξ) (hA : IsFiniteRate P ξ A)
    {T : ℝ≥0} (B : Fin k → Set (ℝ≥0 × M)) (hB : ∀ j, MeasurableSet (B j))
    (hd : Pairwise (Function.onFun Disjoint B)) {D : Set (ℝ≥0 × M)}
    (hD : MeasurableSet D) (hsubD : D ⊆ Ioc 0 T ×ˢ A) (hsub : ∀ j, B j ⊆ D) :
    ∀ᵐ ω ∂P, ∑ j, natCount (ξ ω) (B j) ≤ natCount (ξ ω) D := by
  have hi : ∀ᵐ ω ∂P, ∀ j,
      (natCount (ξ ω) (B j) : ℝ≥0∞) = ξ ω (B j) :=
    ae_all_iff.2 fun j => ae_natCount_cast hξ (hB j)
      (ae_finite_count_subset hA ((hsub j).trans hsubD))
  filter_upwards [hi, ae_natCount_cast hξ hD (ae_finite_count_subset hA hsubD)] with ω hi hω
  have hs := sum_counts_le (ξ ω) B hB hd hsub
  simpa only [← hi, ← hω, ← Nat.cast_sum, Nat.cast_le] using hs

/-- The real expected counts of grid intersections add to the full expected count. -/
private lemma sum_integral_grid_natCount (hξ : IsTimeSimpleLevy P ξ) (hA : IsFiniteRate P ξ A)
    (T : ℝ≥0) {n : ℕ} (hn : n ≠ 0) {B : Set (ℝ≥0 × M)}
    (hB : MeasurableSet B) (hsub : B ⊆ Ioc 0 T ×ˢ A) :
    ∑ i : Fin n, (∫ ω, (natCount (ξ ω) (B ∩ gridBox T n i A) : ℝ) ∂P) =
      ∫ ω, (natCount (ξ ω) B : ℝ) ∂P := by
  rw [← integral_finsetSum (Finset.univ : Finset (Fin n))
    (f := fun i ω => (natCount (ξ ω) (B ∩ gridBox T n i A) : ℝ))
    (fun i _ => integrable_natCount_subset hξ hA
      (hB.inter (measurable_box hA.1)) (inter_subset_left.trans hsub))]
  apply integral_congr_ae
  filter_upwards [ae_sum_grid_natCount hξ hA T hn hB hsub] with ω hω
  exact_mod_cast hω

omit [IsProbabilityMeasure P] in
/-- The mean generating function factors exactly over a grid, including clipped boxes. -/
private lemma integral_pgf_eq_prod_grid {k : ℕ} (hξ : IsTimeSimpleLevy P ξ)
    (hA : IsFiniteRate P ξ A) (T : ℝ≥0) {n : ℕ} (hn : n ≠ 0)
    (B : Fin k → Set (ℝ≥0 × M)) (hB : ∀ j, MeasurableSet (B j))
    (hsub : ∀ j, B j ⊆ Ioc 0 T ×ˢ A) (z : Fin k → ℂ) :
    (∫ ω, ∏ j, z j ^ natCount (ξ ω) (B j) ∂P) =
      ∏ i : Fin n, ∫ ω, ∏ j, z j ^ natCount (ξ ω) (B j ∩ gridBox T n i A) ∂P := by
  let t : Fin (n + 1) → ℝ≥0 := fun i => pointGridTime T n i
  have ht : Monotone t := fun i j hij => pointGridTime_monotone T hn (by exact_mod_cast hij)
  let X : Fin n → Ω → Measure (ℝ≥0 × M) :=
    fun i ω => windowRestrict (t i.castSucc) (t i.succ) (ξ ω)
  let f : Fin n → Measure (ℝ≥0 × M) → ℂ :=
    fun i μ => ∏ j, z j ^ natCount μ (B j ∩ gridBox T n i A)
  have hf (i : Fin n) : Measurable (f i) :=
    measurable_count_pgf _ (fun j => measurable_natCount measurable_id
      ((hB j).inter (measurable_box hA.1))) z
  have heval (i : Fin n) (ω : Ω) : f i (X i ω) =
      ∏ j, z j ^ natCount (ξ ω) (B j ∩ gridBox T n i A) := by
    apply Finset.prod_congr rfl
    intro j _
    congr 1
    unfold natCount
    congr 2
    dsimp [X, t, windowRestrict]
    rw [Measure.restrict_apply' (measurableSet_Ioc.prod MeasurableSet.univ)]
    congr 1
    apply inter_eq_left.2
    intro p hp
    exact ⟨hp.2.1, mem_univ _⟩
  have hi := (hξ.indep n t ht).integral_fun_prod_comp
    (fun i => (measurable_windowRestrict hξ.measurable _ _).aemeasurable)
    (fun i => (hf i).aestronglyMeasurable)
  change (∫ ω, ∏ i, f i (X i ω) ∂P) = ∏ i, ∫ ω, f i (X i ω) ∂P at hi
  simp only [heval] at hi
  rw [← hi]
  apply integral_congr_ae
  have ha : ∀ᵐ ω ∂P, ∀ j,
      ∑ i : Fin n, natCount (ξ ω) (B j ∩ gridBox T n i A) = natCount (ξ ω) (B j) :=
    ae_all_iff.2 fun j => ae_sum_grid_natCount hξ hA T hn (hB j) (hsub j)
  filter_upwards [ha] with ω hω
  rw [Finset.prod_comm]
  apply Finset.prod_congr rfl
  intro j _
  rw [Finset.prod_pow_eq_pow_sum, hω j]

end BGW.Probability

namespace BGW.Probability

variable {Ω M : Type*} [MeasurableSpace Ω] [MeasurableSpace M]
variable {P : Measure Ω} [IsProbabilityMeasure P] {ξ : Ω → Measure (ℝ≥0 × M)} {A : Set M}

/-- The expected count in a grid cell is the window intensity divided by the grid size. -/
private lemma integral_grid_natCount (hξ : IsTimeSimpleLevy P ξ) (hA : IsFiniteRate P ξ A)
    (T : ℝ≥0) {n : ℕ} (hn : n ≠ 0) (i : Fin n) :
    ∫ ω, (natCount (ξ ω) (gridBox T n i A) : ℝ) ∂P =
      (T : ℝ) * (markRate P ξ A).toReal / n := by
  rw [integral_natCount_subset hξ hA (B := gridBox T n i A) (measurable_box hA.1)
    (gridBox_subset_window T hn i)]
  simp only [gridBox]
  rw [lintegral_count_window hξ hA (pointGridTime_monotone T hn (Nat.le_succ i)),
    pointGridTime_width T hn]
  simp only [ENNReal.toReal_mul, ENNReal.coe_toReal, NNReal.coe_div, NNReal.coe_natCast]
  ring

/-- Natural and extended counts have the same empty-set event almost surely. -/
private lemma prob_grid_natCount_ne_zero (hξ : IsTimeSimpleLevy P ξ) (hA : IsFiniteRate P ξ A)
    (T : ℝ≥0) {n : ℕ} (hn : n ≠ 0) (i : Fin n) :
    P.real {ω | natCount (ξ ω) (gridBox T n i A) ≠ 0} =
      1 - Real.exp (-((T : ℝ) * (markRate P ξ A).toReal) / n) := by
  have he : {ω | natCount (ξ ω) (gridBox T n i A) ≠ 0} =ᵐ[P]
      {ω | ξ ω (gridBox T n i A) ≠ 0} := by
    filter_upwards [ae_natCount_cast hξ (B := gridBox T n i A) (measurable_box hA.1)
      (ae_finite_count_subset hA (gridBox_subset_window T hn i))] with ω hω
    apply propext
    rw [← hω]
    norm_cast
  rw [measureReal_def, measure_congr he]
  change P.real {ω | ξ ω (gridBox T n i A) ≠ 0} = _
  rw [probReal_ne_zero hξ hA (B := gridBox T n i A) (measurable_box hA.1)]
  have hc (t : ℝ≥0) : (P {ω | ξ ω (Ioc 0 t ×ˢ A) = 0}).toReal =
      Real.exp (-(t : ℝ) * (markRate P ξ A).toReal) := by
    rw [prob_noMark_window hξ hA, ENNReal.toReal_ofReal (Real.exp_nonneg _), neg_mul]
  rw [prob_noMark_grid hξ hA T hn hc]
  congr 2
  ring

end BGW.Probability

namespace BGW.Probability

variable {Ω M : Type*} [MeasurableSpace Ω] [MeasurableSpace M]
variable {P : Measure Ω} [IsProbabilityMeasure P] {ξ : Ω → Measure (ℝ≥0 × M)} {A : Set M}

/-- Joint complex generating functions of disjoint finite-intensity subsets factor exponentially. -/
lemma integral_complex_pgf_subsets {k : ℕ} (hξ : IsTimeSimpleLevy P ξ)
    (hA : IsFiniteRate P ξ A) (T : ℝ≥0) (B : Fin k → Set (ℝ≥0 × M))
    (hB : ∀ j, MeasurableSet (B j)) (hsub : ∀ j, B j ⊆ Ioc 0 T ×ˢ A)
    (hd : Pairwise (Function.onFun Disjoint B)) (z : Fin k → ℂ) (hz : ∀ j, ‖z j‖ ≤ 1) :
    (∫ ω, ∏ j, z j ^ natCount (ξ ω) (B j) ∂P) =
      Complex.exp (∑ j, ((∫ ω, (natCount (ξ ω) (B j) : ℝ) ∂P : ℝ) : ℂ) * (z j - 1)) := by
  let a : ℝ := (T : ℝ) * (markRate P ξ A).toReal
  have ha : 0 ≤ a := mul_nonneg T.coe_nonneg ENNReal.toReal_nonneg
  have he : Tendsto (fun n : ℕ =>
      6 * (a - n * (1 - Real.exp (-a / n))) + 4 * a ^ 2 / n) atTop (𝓝 0) := by
    have h₁ := ((tendsto_grid_mean a).const_sub a).const_mul 6
    have h₂ := (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (4 * a ^ 2)
    simpa [div_eq_mul_inv] using h₁.add h₂
  have hb : Tendsto (fun n : ℕ => 2 * (a / n)) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv, mul_assoc] using
      (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (2 * a)
  have hbound : ‖(∫ ω, ∏ j, z j ^ natCount (ξ ω) (B j) ∂P) -
      Complex.exp (∑ j, ((∫ ω, (natCount (ξ ω) (B j) : ℝ) ∂P : ℝ) : ℂ) * (z j - 1))‖ ≤ 0 := by
    apply ge_of_tendsto he
    filter_upwards [eventually_ge_atTop 1, hb.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))]
      with n hn hsmall
    have hn0 : n ≠ 0 := by omega
    let N : Fin n → Fin k → Ω → ℕ :=
      fun i j ω => natCount (ξ ω) (B j ∩ gridBox T n i A)
    let U : Fin n → Ω → ℕ := fun i ω => natCount (ξ ω) (gridBox T n i A)
    have hNm (i : Fin n) (j : Fin k) : Measurable (N i j) :=
      measurable_natCount hξ.measurable ((hB j).inter (measurable_box hA.1))
    have hNi (i : Fin n) (j : Fin k) : Integrable (fun ω => (N i j ω : ℝ)) P :=
      integrable_natCount_subset hξ hA ((hB j).inter (measurable_box hA.1))
        (inter_subset_left.trans (hsub j))
    have hUm (i : Fin n) : Measurable (U i) :=
      measurable_natCount hξ.measurable (measurable_box hA.1)
    have hUi (i : Fin n) : Integrable (fun ω => (U i ω : ℝ)) P :=
      integrable_natCount_subset hξ hA (measurable_box hA.1) (gridBox_subset_window T hn0 i)
    have hNU (i : Fin n) : ∀ᵐ ω ∂P, ∑ j, N i j ω ≤ U i ω := by
      apply ae_sum_natCount_le hξ hA (fun j => B j ∩ gridBox T n i A)
        (fun j => (hB j).inter (measurable_box hA.1))
      · intro j l hjl
        exact (hd hjl).mono inter_subset_left inter_subset_left
      · exact measurable_box hA.1
      · exact gridBox_subset_window T hn0 i
      · exact fun _ => inter_subset_right
    have hmean (i : Fin n) : ∑ j, (∫ ω, (N i j ω : ℝ) ∂P) ≤ a / n := by
      rw [← integral_finsetSum _ (fun j _ => hNi i j)]
      rw [← integral_grid_natCount hξ hA T hn0 i]
      apply integral_mono_ae (integrable_finsetSum _ (fun j _ => hNi i j)) (hUi i)
      filter_upwards [hNU i] with ω hω
      exact_mod_cast hω
    let m : Fin n → Fin k → ℝ := fun i j => ∫ ω, (N i j ω : ℝ) ∂P
    have hm (i : Fin n) (j : Fin k) : 0 ≤ m i j := integral_nonneg fun _ => Nat.cast_nonneg _
    have hsum (j : Fin k) : ∑ i, m i j = ∫ ω, (natCount (ξ ω) (B j) : ℝ) ∂P :=
      sum_integral_grid_natCount hξ hA T hn0 (hB j) (hsub j)
    have hexp : (∏ i : Fin n, Complex.exp (∑ j, (m i j : ℂ) * (z j - 1))) =
        Complex.exp (∑ j, ((∫ ω, (natCount (ξ ω) (B j) : ℝ) ∂P : ℝ) : ℂ) * (z j - 1)) := by
      rw [← Complex.exp_sum, Finset.sum_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      rw [← Finset.sum_mul, ← Complex.ofReal_sum, hsum]
    rw [integral_pgf_eq_prod_grid hξ hA T hn0 B hB hsub z, ← hexp]
    calc
      _ ≤ ∑ i : Fin n, ‖(∫ ω, ∏ j, z j ^ N i j ω ∂P) -
          Complex.exp (∑ j, (m i j : ℂ) * (z j - 1))‖ := by
        apply norm_prod_sub_prod_le_sum
        · exact fun i _ => norm_integral_count_pgf_le_one (N i) (hNm i) z hz
        · exact fun i _ => norm_exp_count_exponent_le_one (m i) (hm i) z hz
      _ ≤ ∑ _i : Fin n, (6 * (a / n - (1 - Real.exp (-a / n))) + (2 * (a / n)) ^ 2) := by
        apply Finset.sum_le_sum
        intro i _
        have hcell := norm_integral_count_pgf_sub_exp_le (N i) (hNm i) (hNi i)
          (U i) (hUm i) (hUi i) (hNU i) z hz (a / n) hsmall.le (hmean i)
        simpa only [U, integral_grid_natCount hξ hA T hn0 i,
          prob_grid_natCount_ne_zero hξ hA T hn0 i] using hcell
      _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn0
        field_simp
        ring
  exact sub_eq_zero.1 (norm_eq_zero.1 (le_antisymm hbound (norm_nonneg _)))

end BGW.Probability
