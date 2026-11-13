/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module
public import BGW.Probability.DoobL2ResolventAux
import BGW.Probability.DoobL2ResolventMoment
public import Mathlib.Probability.Martingale.OptionalStopping
public import Mathlib.MeasureTheory.Integral.MeanInequalities
public import Mathlib.Data.Finset.Sort
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Probability.Martingale.Basic
public import Mathlib.Probability.ConditionalExpectation
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! # Doob `L²` maximal inequalities and signed resolvent moments

* Doob's `L²` maximal inequality `E max_{k ≤ n} Y_k² ≤ 4 E Y_n²` for nonnegative submartingales
  (`lintegral_sq_sup_le_four_mul_of_submartingale`), for real martingales in `ℝ≥0∞` and real form
  (`lintegral_sq_sup_enorm_le_four_mul_of_martingale`, `integral_sq_sup_le_four_mul_of_martingale`),
  and over a compact time interval for right-continuous `ℝ≥0`-indexed martingales
  (`lintegral_sq_sup_Icc_le_four_mul_of_martingale`). All `ℝ≥0∞` forms need no integrability.
* For a process `Z` and bounded `k`, `V` with `E[∫_s^∞ e^{-t} k(Z_t) dt | F_s] = e^{-s} V(Z_s)`
  (`ResolventMarkov`): the martingale `∫_0^t e^{-s} k(Z_s) ds + e^{-t} V(Z_t)`
  (`martingale_discounted_resolvent`) and the second-moment identity
  `E B² = 2 E ∫_0^∞ e^{-2t} k(Z_t) V(Z_t) dt` for `B = ∫_0^∞ e^{-t} k(Z_t) dt`
  (`integral_sq_discountedOccupation`), with the bound `integral_sq_discountedOccupation_le`.

## References

* J. L. Doob, *Stochastic Processes*, Wiley, 1953, Chapter VII.
* O. Kallenberg, *Foundations of Modern Probability*, 2nd ed., Springer, 2002, Chapters 7 and 19.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open Finset

namespace BGW.Probability

section DoobL2

variable {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω} [IsFiniteMeasure μ]

/-- **Doob `L²` maximal inequality, nonnegative submartingale, finite grid.** -/
theorem lintegral_sq_sup_le_four_mul_of_submartingale {ℱ : Filtration ℕ m} {Y : ℕ → Ω → ℝ}
    (hY : Submartingale Y ℱ μ) (hnn : ∀ k ω, 0 ≤ Y k ω) (n : ℕ) :
    ∫⁻ ω, ((Finset.range (n + 1)).sup fun k => ENNReal.ofReal (Y k ω)) ^ 2 ∂μ ≤
      4 * ∫⁻ ω, ENNReal.ofReal (Y n ω) ^ 2 ∂μ := by
  let R : Ω → ℝ := fun ω => (Finset.range (n + 1)).sup'
    Finset.nonempty_range_add_one fun k => Y k ω
  have hR : Measurable R := measurable_range_sup'' fun n _ =>
    (hY.stronglyMeasurable n).measurable.le (ℱ.le n)
  have hRnn (ω : Ω) : 0 ≤ R ω := by
    change 0 ≤ (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one fun k => Y k ω
    exact (hnn 0 ω).trans (Finset.le_sup' (fun k => Y k ω)
      (Finset.mem_range.2 (show 0 < n + 1 by omega)))
  have htail (t : ℝ) (ht : 0 < t) : ENNReal.ofReal t * μ {ω | t ≤ R ω} ≤
      ∫⁻ ω in {ω | t ≤ R ω}, ENNReal.ofReal (Y n ω) ∂μ := by
    have h := maximal_ineq hY (fun k => hnn k) (ε := t.toNNReal) n
    rw [Real.coe_toNNReal _ (le_of_lt ht)] at h
    rw [ofReal_integral_eq_lintegral_ofReal (hY.integrable n).integrableOn] at h
    · exact h
    · exact Eventually.of_forall (fun _ => hnn n _)
  have hbase : ∫⁻ ω, ENNReal.ofReal (R ω) ^ 2 ∂μ ≤
      2 * ∫⁻ ω, ENNReal.ofReal (R ω) * ENNReal.ofReal (Y n ω) ∂μ :=
    lintegral_sq_le_two_mul_of_tail hR
      ((hY.stronglyMeasurable n).mono (ℱ.le n)).measurable hRnn htail
  by_cases hD : (∫⁻ ω, ENNReal.ofReal (Y n ω) ^ 2 ∂μ) = ∞
  · rw [hD]
    simp
  have hYn2 : MemLp (Y n) 2 μ := by
    apply (memLp_two_iff_integrable_sq
      ((hY.stronglyMeasurable n).mono (ℱ.le n)).aestronglyMeasurable).2
    refine ⟨((hY.stronglyMeasurable n).mono (ℱ.le n)).aestronglyMeasurable.pow 2, ?_⟩
    rw [hasFiniteIntegral_iff_enorm]
    apply lt_of_eq_of_lt _ (lt_top_iff_ne_top.2 hD)
    apply lintegral_congr
    intro ω
    rw [← ofReal_norm]
    simp [Real.norm_eq_abs,
      ← ENNReal.ofReal_pow (hnn n ω)]
  have hYk2 {k : ℕ} (hk : k ≤ n) : MemLp (Y k) 2 μ := by
    apply (hYn2.condExp (m := ℱ k) (by norm_num)).mono'
      ((hY.stronglyMeasurable k).mono (ℱ.le k)).aestronglyMeasurable
    filter_upwards [hY.ae_le_condExp hk] with ω hω
    rw [Real.norm_eq_abs, abs_of_nonneg (hnn k ω)]
    exact hω
  have hsum : MemLp (fun ω => ∑ k ∈ Finset.range (n + 1), Y k ω) 2 μ :=
    memLp_finsetSum _ (fun k hk => hYk2 (Nat.le_of_lt_succ (Finset.mem_range.1 hk)))
  have hR2 : MemLp R 2 μ := by
    apply hsum.mono' hR.aestronglyMeasurable
    apply Eventually.of_forall
    intro ω
    rw [Real.norm_eq_abs, abs_of_nonneg (hRnn ω)]
    apply Finset.sup'_le
    intro k hk
    exact Finset.single_le_sum (fun j _ => hnn j ω) hk
  have hC : (∫⁻ ω, ENNReal.ofReal (R ω) ^ 2 ∂μ) ≠ ∞ := by
    have h := hR2.integrable_sq.hasFiniteIntegral
    rw [hasFiniteIntegral_iff_enorm] at h
    apply ne_of_lt
    apply lt_of_eq_of_lt _ h
    apply lintegral_congr
    intro ω
    rw [← ofReal_norm]
    simp [Real.norm_eq_abs,
      ← ENNReal.ofReal_pow (hRnn ω)]
  have hh := ENNReal.lintegral_mul_le_Lp_mul_Lq μ Real.HolderConjugate.two_two
    (f := fun ω => ENNReal.ofReal (R ω)) (g := fun ω => ENNReal.ofReal (Y n ω))
    hR.ennreal_ofReal.aemeasurable
    ((hY.stronglyMeasurable n).mono (ℱ.le n)).measurable.ennreal_ofReal.aemeasurable
  have hchain : (∫⁻ ω, ENNReal.ofReal (R ω) ^ 2 ∂μ) ≤
      2 * ((∫⁻ ω, ENNReal.ofReal (R ω) ^ 2 ∂μ) ^ (1 / (2 : ℝ)) *
        (∫⁻ ω, ENNReal.ofReal (Y n ω) ^ 2 ∂μ) ^ (1 / (2 : ℝ))) := by
    apply hbase.trans
    gcongr
    convert hh using 2 <;> norm_num
  have hrhs : (2 : ℝ≥0∞) * ((∫⁻ ω, ENNReal.ofReal (R ω) ^ 2 ∂μ) ^ (1 / (2 : ℝ)) *
      (∫⁻ ω, ENNReal.ofReal (Y n ω) ^ 2 ∂μ) ^ (1 / (2 : ℝ))) ≠ ∞ := by
    exact ENNReal.mul_ne_top (by norm_num)
      (ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by positivity) hC)
        (ENNReal.rpow_ne_top_of_nonneg (by positivity) hD))
  have hr := ENNReal.toReal_mono hrhs hchain
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofNat, ← ENNReal.toReal_rpow] at hr
  rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow] at hr
  have hreal : (∫⁻ ω, ENNReal.ofReal (R ω) ^ 2 ∂μ).toReal ≤
      4 * (∫⁻ ω, ENNReal.ofReal (Y n ω) ^ 2 ∂μ).toReal := by
    have hs := mul_self_le_mul_self (by positivity : (0 : ℝ) ≤
      (∫⁻ ω, ENNReal.ofReal (R ω) ^ 2 ∂μ).toReal) hr
    have hcn : 0 ≤ (∫⁻ ω, ENNReal.ofReal (R ω) ^ 2 ∂μ).toReal :=
      ENNReal.toReal_nonneg
    have hdn : 0 ≤ (∫⁻ ω, ENNReal.ofReal (Y n ω) ^ 2 ∂μ).toReal :=
      ENNReal.toReal_nonneg
    have hcs := Real.sq_sqrt hcn
    have hds := Real.sq_sqrt hdn
    by_cases hc : (∫⁻ ω, ENNReal.ofReal (R ω) ^ 2 ∂μ).toReal = 0
    · rw [hc]
      positivity
    · have hcpos : 0 < (∫⁻ ω, ENNReal.ofReal (R ω) ^ 2 ∂μ).toReal :=
        lt_of_le_of_ne hcn (Ne.symm hc)
      nlinarith
  have hfinal : (∫⁻ ω, ENNReal.ofReal (R ω) ^ 2 ∂μ) ≤
      4 * ∫⁻ ω, ENNReal.ofReal (Y n ω) ^ 2 ∂μ := by
    apply (ENNReal.toReal_le_toReal hC (ENNReal.mul_ne_top (by norm_num) hD)).1
    simpa using hreal
  convert hfinal using 1
  apply lintegral_congr
  intro ω
  congr 1
  rw [← Finset.sup'_eq_sup Finset.nonempty_range_add_one]
  exact (Finset.apply_sup'_eq_sup'_comp Finset.nonempty_range_add_one
    ENNReal.ofReal (fun x y => ENNReal.ofReal_max x y)).symm


/-- **Doob `L²` maximal inequality for a real martingale, finite grid.** -/
theorem lintegral_sq_sup_enorm_le_four_mul_of_martingale {ℱ : Filtration ℕ m} {M : ℕ → Ω → ℝ}
    (hM : Martingale M ℱ μ) (n : ℕ) :
    ∫⁻ ω, ((Finset.range (n + 1)).sup fun k => ‖M k ω‖ₑ) ^ 2 ∂μ ≤
      4 * ∫⁻ ω, ‖M n ω‖ₑ ^ 2 ∂μ := by
  have habs : Submartingale (fun k ω => |M k ω|) ℱ μ := by
    refine ⟨?_, ?_, fun k => (hM.integrable k).abs⟩
    · intro k
      simpa only [Real.norm_eq_abs] using
        continuous_norm.comp_stronglyMeasurable (hM.stronglyMeasurable k)
    · intro i j hij
      filter_upwards [hM.2 i j hij, abs_condExp_ae_le_condExp_abs (m := ℱ i) (M j)]
        with ω heq hle
      rw [← heq]
      exact hle
  have h := lintegral_sq_sup_le_four_mul_of_submartingale habs
    (fun _ _ => abs_nonneg _) n
  simpa only [← ofReal_norm, Real.norm_eq_abs] using h



/-- Doob's inequality on an arbitrary finite set with a prescribed upper endpoint. -/
theorem lintegral_sq_sup_finset_le_four_mul_of_martingale {ℱ : Filtration ℝ≥0 m} {M : ℝ≥0 → Ω → ℝ}
    (hM : Martingale M ℱ μ) (T : ℝ≥0) (s : Finset ℝ≥0) (hT : T ∈ s)
    (hmax : ∀ t ∈ s, t ≤ T) :
    ∫⁻ ω, (s.sup fun t => ‖M t ω‖ₑ) ^ 2 ∂μ ≤
      4 * ∫⁻ ω, ‖M T ω‖ₑ ^ 2 ∂μ := by
  let N := s.card
  let τ : ℕ → ℝ≥0 := fun i => if hi : i < N then
    s.orderEmbOfFin rfl ⟨i, hi⟩ else T
  have hτmem (i : ℕ) (hi : i < N) : τ i ∈ s := by
    simp only [τ, dite_eq_left hi]
    exact s.orderEmbOfFin_mem rfl ⟨i, hi⟩
  have hτmono : Monotone τ := by
    intro i j hij
    by_cases hj : j < N
    · have hi : i < N := hij.trans_lt hj
      simp only [τ, dite_eq_left hi, dite_eq_left hj]
      exact (s.orderEmbOfFin rfl).monotone (show (⟨i, hi⟩ : Fin N) ≤ ⟨j, hj⟩ from hij)
    · have hj' : τ j = T := dite_eq_right hj
      rw [hj']
      by_cases hi : i < N
      · exact hmax (τ i) (hτmem i hi)
      · simp only [τ, dite_eq_right hi]
        exact le_rfl
  let 𝒢 : Filtration ℕ m :=
    ⟨fun i => ℱ (τ i), fun i j hij => ℱ.mono (hτmono hij), fun i => ℱ.le (τ i)⟩
  have hmart : Martingale (fun i => M (τ i)) 𝒢 μ := by
    refine ⟨fun i => hM.stronglyMeasurable (τ i), fun i j hij => ?_⟩
    exact hM.2 (τ i) (τ j) (hτmono hij)
  have h := lintegral_sq_sup_enorm_le_four_mul_of_martingale hmart N
  have hτN : τ N = T := dite_eq_right (lt_irrefl N)
  rw [hτN] at h
  apply le_of_eq_of_le _ h
  congr 1
  funext ω
  congr 1
  apply le_antisymm
  swap
  · apply Finset.sup_le
    intro k hk
    by_cases hkN : k < N
    · exact Finset.le_sup (f := fun t => ‖M t ω‖ₑ) (hτmem k hkN)
    · have hk0 : k = N := by
        have hklt := Finset.mem_range.1 hk
        omega
      subst k
      rw [hτN]
      exact Finset.le_sup (f := fun t => ‖M t ω‖ₑ) hT
  · apply Finset.sup_le
    intro t ht
    let i : Fin N := (s.orderIsoOfFin rfl).symm ⟨t, ht⟩
    have hi : (i : ℕ) < N := i.isLt
    have hτ : τ (i : ℕ) = t := by
      simp only [τ, dite_eq_left hi]
      exact congrArg Subtype.val ((s.orderIsoOfFin rfl).apply_symm_apply ⟨t, ht⟩)
    rw [← hτ]
    exact Finset.le_sup (f := fun k => ‖M (τ k) ω‖ₑ)
      (Finset.mem_range.2 (Nat.lt_succ_of_lt hi))

/-- Real-valued form when `M n ∈ L²`: `E max_{k ≤ n} M_k² ≤ 4 E M_n²`. -/
theorem integral_sq_sup_le_four_mul_of_martingale {ℱ : Filtration ℕ m} {M : ℕ → Ω → ℝ}
    (hM : Martingale M ℱ μ) (n : ℕ) (h2 : MemLp (M n) 2 μ) :
    Integrable (fun ω => ((Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
        fun k => |M k ω|) ^ 2) μ ∧
      ∫ ω, ((Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
        fun k => |M k ω|) ^ 2 ∂μ ≤
        4 * ∫ ω, (M n ω) ^ 2 ∂μ := by
  let A : Ω → ℝ := fun ω => (Finset.range (n + 1)).sup'
    Finset.nonempty_range_add_one fun k => |M k ω|
  have hA : Measurable A := measurable_range_sup'' fun k _ =>
    by simpa only [Real.norm_eq_abs] using
      ((hM.stronglyMeasurable k).measurable.le (ℱ.le k)).norm
  have hAnn (ω : Ω) : 0 ≤ A ω := by
    change 0 ≤ (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one fun k => |M k ω|
    exact (abs_nonneg _).trans (Finset.le_sup' (fun k => |M k ω|)
      (Finset.mem_range.2 (show 0 < n + 1 by omega)))
  have hMk2 {k : ℕ} (hk : k ≤ n) : MemLp (fun ω => |M k ω|) 2 μ := by
    apply (h2.abs.condExp (m := ℱ k) (by norm_num)).mono'
      (by simpa only [Real.norm_eq_abs] using (hM.integrable k).aestronglyMeasurable.norm)
    filter_upwards [hM.2 k n hk, abs_condExp_ae_le_condExp_abs (m := ℱ k) (M n)]
      with ω heq hle
    simp only [Real.norm_eq_abs, abs_abs]
    rw [← heq]
    exact hle
  have hsum : MemLp (fun ω => ∑ k ∈ Finset.range (n + 1), |M k ω|) 2 μ :=
    memLp_finsetSum _ (fun k hk => hMk2 (Nat.le_of_lt_succ (Finset.mem_range.1 hk)))
  have hA2 : MemLp A 2 μ := by
    apply hsum.mono' hA.aestronglyMeasurable
    apply Eventually.of_forall
    intro ω
    rw [Real.norm_eq_abs, abs_of_nonneg (hAnn ω)]
    apply Finset.sup'_le (f := fun k => |M k ω|)
    intro k hk
    exact Finset.single_le_sum (f := fun k => |M k ω|)
      (fun j _ => abs_nonneg _) hk
  have hD : (∫⁻ ω, ‖M n ω‖ₑ ^ 2 ∂μ) ≠ ∞ := by
    have h := h2.integrable_sq.hasFiniteIntegral
    rw [hasFiniteIntegral_iff_enorm] at h
    simpa only [enorm_pow] using h.ne
  have hmax := lintegral_sq_sup_enorm_le_four_mul_of_martingale hM n
  have hsup (ω : Ω) : (Finset.range (n + 1)).sup (fun k => ‖M k ω‖ₑ) = ‖A ω‖ₑ := by
    rw [← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg (hAnn ω)]
    change _ = ENNReal.ofReal ((Finset.range (n + 1)).sup'
      Finset.nonempty_range_add_one fun k => |M k ω|)
    rw [Finset.apply_sup'_eq_sup'_comp Finset.nonempty_range_add_one
      ENNReal.ofReal (fun x y => ENNReal.ofReal_max x y)]
    simp only [Finset.sup'_eq_sup Finset.nonempty_range_add_one, Function.comp_apply,
      ← ofReal_norm, Real.norm_eq_abs]
  simp_rw [hsup] at hmax
  have hIntA : ∫ ω, A ω ^ 2 ∂μ = (∫⁻ ω, ‖A ω‖ₑ ^ 2 ∂μ).toReal := by
    rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall (fun _ => sq_nonneg _))
      (hA.aestronglyMeasurable.pow 2)]
    congr 1
    apply lintegral_congr
    intro ω
    rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _) 2, Real.norm_eq_abs, sq_abs]
  have hIntM : ∫ ω, M n ω ^ 2 ∂μ = (∫⁻ ω, ‖M n ω‖ₑ ^ 2 ∂μ).toReal := by
    rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall (fun _ => sq_nonneg _))
      ((hM.integrable n).aestronglyMeasurable.pow 2)]
    congr 1
    apply lintegral_congr
    intro ω
    rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _) 2, Real.norm_eq_abs, sq_abs]
  refine ⟨hA2.integrable_sq, ?_⟩
  change (∫ ω, A ω ^ 2 ∂μ) ≤ 4 * ∫ ω, M n ω ^ 2 ∂μ
  have hreal := ENNReal.toReal_mono (ENNReal.mul_ne_top (by norm_num) hD) hmax
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofNat] at hreal
  rwa [hIntA, hIntM]


/-- **Compact-time Doob `L²`, right-continuous martingale.**
For an `ℝ≥0`-indexed martingale whose
paths are right-continuous (every `ω`), `E sup_{t ≤ T} |M_t|² ≤ 4 E |M_T|²`;
the supremum is a
countable one (rationals and `T`), hence measurable. -/
theorem lintegral_sq_sup_Icc_le_four_mul_of_martingale {ℱ : Filtration ℝ≥0 m} {M : ℝ≥0 → Ω → ℝ}
    (hM : Martingale M ℱ μ) (hrc : ∀ ω t, ContinuousWithinAt (fun s => M s ω) (Ici t) t)
    (T : ℝ≥0) :
    ∫⁻ ω, (⨆ t ∈ Icc (0 : ℝ≥0) T, ‖M t ω‖ₑ) ^ 2 ∂μ ≤
      4 * ∫⁻ ω, ‖M T ω‖ₑ ^ 2 ∂μ := by
  let Q : Set ℝ≥0 := Set.range (fun q : ℚ => Real.toNNReal (q : ℝ)) ∪ {T}
  let D : Set ℝ≥0 := Icc 0 T ∩ Q
  let tT : D := ⟨T, ⟨by simp, by simp [Q]⟩⟩
  have hQ : Q.Countable := (countable_range _).union (countable_singleton T)
  have hD : D.Countable := hQ.mono inter_subset_right
  let _ : Countable D := hD.to_subtype
  have hsupD (ω : Ω) : (⨆ t ∈ Icc (0 : ℝ≥0) T, ‖M t ω‖ₑ) =
      ⨆ d : D, ‖M d.1 ω‖ₑ := by
    apply le_antisymm
    · refine iSup_le fun t => iSup_le fun ht => ?_
      by_cases htT : t = T
      · subst t
        exact le_iSup_of_le tT (le_refl _)
      obtain ⟨q, hqanti, hqt, hqtop⟩ := Real.exists_seq_rat_strictAnti_tendsto (t : ℝ)
      let u : ℕ → ℝ≥0 := fun n => min (Real.toNNReal (q n : ℝ)) T
      have hq0 (n : ℕ) : 0 ≤ (q n : ℝ) := (hqt n).le.trans' t.coe_nonneg
      have huD (n : ℕ) : u n ∈ D := by
        have h0q : 0 ≤ Real.toNNReal (q n : ℝ) := by positivity
        refine ⟨⟨le_min h0q T.2, min_le_right _ _⟩, ?_⟩
        by_cases hqT : Real.toNNReal (q n : ℝ) ≤ T
        · refine Or.inl ?_
          simp only [u, min_eq_left hqT]
          exact ⟨q n, rfl⟩
        · refine Or.inr ?_
          simp only [u, min_eq_right (le_of_not_ge hqT)]
          exact rfl
      have hut (n : ℕ) : t ≤ u n := by
        apply le_min _ ht.2
        exact NNReal.le_toNNReal_of_coe_le (hqt n).le
      have hucoe (n : ℕ) : (u n : ℝ) = min (q n : ℝ) (T : ℝ) := by
        simp [u, Real.coe_toNNReal _ (hq0 n)]
      have hutop : Tendsto u atTop (𝓝 t) := by
        rw [← NNReal.tendsto_coe]
        simp only [hucoe]
        convert hqtop.min (tendsto_const_nhds (x := (T : ℝ))) using 1
        have htTR : (t : ℝ) ≤ (T : ℝ) := by exact_mod_cast ht.2
        rw [min_eq_left htTR]
      have hutop' : Tendsto u atTop (nhdsWithin t (Ici t)) :=
        tendsto_nhdsWithin_iff.2 ⟨hutop, Eventually.of_forall hut⟩
      have hm := (hrc ω t).tendsto.comp hutop'
      have he : Tendsto (fun n => ‖M (u n) ω‖ₑ) atTop (𝓝 ‖M t ω‖ₑ) :=
        (continuous_enorm.tendsto _).comp hm
      apply le_of_tendsto he
      exact Eventually.of_forall fun n => le_iSup_of_le ⟨u n, huD n⟩ (le_refl _)
    · refine iSup_le fun d => ?_
      exact le_iSup_of_le d.1 (le_iSup_of_le d.2.1 (le_refl _))
  let F := {s : Finset D // tT ∈ s}
  let B : F → Ω → ℝ≥0∞ := fun s ω => s.1.sup fun d => ‖M d.1 ω‖ₑ
  have hFB (ω : Ω) : (⨆ d : D, ‖M d.1 ω‖ₑ) = ⨆ s : F, B s ω := by
    rw [iSup_eq_iSup_finset]
    apply le_antisymm
    · refine iSup_le fun s => ?_
      let s' : F := ⟨insert tT s, Finset.mem_insert_self _ _⟩
      apply le_iSup_of_le s'
      simpa only [B, Finset.sup_eq_iSup] using
        Finset.sup_mono (f := fun d : D => ‖M d.1 ω‖ₑ) (Finset.subset_insert _ _)
    · refine iSup_le fun s => ?_
      change (s.1.sup fun d : D => ‖M d.1 ω‖ₑ) ≤
        ⨆ t : Finset D, ⨆ d : D, ⨆ _ : d ∈ t, ‖M d.1 ω‖ₑ
      apply Finset.sup_le
      intro d hd
      exact le_iSup_of_le {d} (le_iSup_of_le d
        (le_iSup_of_le (Finset.mem_singleton_self d) (le_refl _)))
  have hpow (ω : Ω) : (⨆ s : F, B s ω) ^ 2 = ⨆ s : F, (B s ω) ^ 2 := by
    apply le_antisymm
    · rw [pow_two, ENNReal.iSup_mul]
      refine iSup_le fun s => ?_
      rw [ENNReal.mul_iSup]
      refine iSup_le fun u => ?_
      let v : F := ⟨s.1 ∪ u.1, Finset.mem_union_left _ s.2⟩
      calc
        B s ω * B u ω ≤ B v ω * B v ω := by
          apply mul_le_mul' <;> apply Finset.sup_mono
          · exact Finset.subset_union_left
          · exact Finset.subset_union_right
        _ = B v ω ^ 2 := (pow_two _).symm
        _ ≤ ⨆ s : F, B s ω ^ 2 := le_iSup_of_le v (le_refl _)
    · refine iSup_le fun s => ?_
      exact pow_le_pow_left' (le_iSup (fun u : F => B u ω) s) 2
  have hmeas_sup (s : Finset D) : Measurable (fun ω => s.sup fun d => ‖M d.1 ω‖ₑ) := by
    classical
    induction s using Finset.induction_on with
    | empty => simp
    | @insert d s hd ih =>
      simp only [Finset.sup_insert]
      exact ((hM.stronglyMeasurable d.1).measurable.le (ℱ.le d.1)).enorm.sup ih
  have hdir : Directed (· ≤ ·) (fun s ω => (B s ω) ^ 2) := by
    intro s u
    let v : F := ⟨s.1 ∪ u.1, Finset.mem_union_left _ s.2⟩
    refine ⟨v, ?_, ?_⟩ <;> intro ω <;> dsimp only <;> gcongr
    · exact Finset.sup_mono Finset.subset_union_left
    · exact Finset.sup_mono Finset.subset_union_right
  have hbound (s : F) : (∫⁻ ω, (B s ω) ^ 2 ∂μ) ≤
      4 * ∫⁻ ω, ‖M T ω‖ₑ ^ 2 ∂μ := by
    have hTmem : T ∈ s.1.image Subtype.val := Finset.mem_image.2 ⟨tT, s.2, rfl⟩
    have hmax : ∀ t ∈ s.1.image Subtype.val, t ≤ T := by
      intro t ht
      obtain ⟨d, hd, rfl⟩ := Finset.mem_image.1 ht
      exact d.2.1.2
    have h := lintegral_sq_sup_finset_le_four_mul_of_martingale hM T
      (s.1.image Subtype.val) hTmem hmax
    simpa only [B, Finset.sup_image, Function.comp_def] using h
  calc
    _ = ∫⁻ ω, ⨆ s : F, (B s ω) ^ 2 ∂μ := by
      apply lintegral_congr
      intro ω
      rw [hsupD, hFB, hpow]
    _ = ⨆ s : F, ∫⁻ ω, (B s ω) ^ 2 ∂μ := by
      apply lintegral_iSup_directed
      · intro s
        exact ((hmeas_sup s.1).pow_const 2).aemeasurable
      · exact hdir
    _ ≤ _ := iSup_le hbound

end DoobL2

section ResolventMoments

variable {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {E : Type*} [MeasurableSpace E]

/-- The discounted occupation `B = ∫_0^∞ e^{-t} k(Z_t) dt`. -/
noncomputable def discountedOccupation (Z : ℝ≥0 → Ω → E) (k : E → ℝ) (ω : Ω) : ℝ :=
  ∫ t in Ioi (0 : ℝ), Real.exp (-t) * k (Z t.toNNReal ω)

/-- **Resolvent Markov hypothesis**: given `F_s`, the discounted future of `k(Z)` after `s` is
`e^{-s} V(Z_s)`. -/
def ResolventMarkov (ℱ : Filtration ℝ≥0 m) (μ : Measure Ω) (Z : ℝ≥0 → Ω → E)
    (k V : E → ℝ) :
    Prop :=
  ∀ s : ℝ≥0, μ[fun ω => ∫ t in Ioi (s : ℝ),
    Real.exp (-t) * k (Z t.toNNReal ω) | ℱ s] =ᵐ[μ]
    fun ω => Real.exp (-(s : ℝ)) * V (Z s ω)

private lemma integrable_exp_occupation_prod {Z : ℝ≥0 → Ω → E} {k : E → ℝ}
    (hZ : Measurable fun p : ℝ≥0 × Ω => Z p.1 p.2) (hk : Measurable k)
    (hkb : ∃ C, ∀ e, |k e| ≤ C) {ν : Measure ℝ}
    (hexp : Integrable (fun t => Real.exp (-t)) ν) :
    Integrable (fun p : ℝ × Ω => Real.exp (-p.1) * k (Z p.1.toNNReal p.2)) (ν.prod μ) := by
  obtain ⟨C, hC⟩ := hkb
  let D := max C 0
  have hD : 0 ≤ D := le_max_right _ _
  have hkD (e : E) : |k e| ≤ D := (hC e).trans (le_max_left _ _)
  have hkZ : Measurable (fun p : ℝ × Ω => k (Z p.1.toNNReal p.2)) :=
    hk.comp (hZ.comp ((measurable_real_toNNReal.comp measurable_fst).prodMk measurable_snd))
  have hf : Measurable (fun p : ℝ × Ω => Real.exp (-p.1) * k (Z p.1.toNNReal p.2)) := by
    fun_prop
  have hdom : Integrable (fun p : ℝ × Ω => D * Real.exp (-p.1)) (ν.prod μ) := by
    simpa using (hexp.const_mul D).mul_prod (integrable_const (1 : ℝ))
  apply hdom.mono' hf.aestronglyMeasurable
  filter_upwards with p
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  calc
    Real.exp (-p.1) * |k (Z p.1.toNNReal p.2)| ≤ Real.exp (-p.1) * D :=
      mul_le_mul_of_nonneg_left (hkD _) (Real.exp_pos _).le
    _ = D * Real.exp (-p.1) := mul_comm _ _

private lemma integrable_exp_occupation {Z : ℝ≥0 → Ω → E} {k : E → ℝ}
    (hZ : Measurable fun p : ℝ≥0 × Ω => Z p.1 p.2) (hk : Measurable k)
    (hkb : ∃ C, ∀ e, |k e| ≤ C) (a : ℝ) (ω : Ω) :
    IntegrableOn (fun t => Real.exp (-t) * k (Z t.toNNReal ω)) (Ioi a) := by
  obtain ⟨C, hC⟩ := hkb
  let D := max C 0
  have hD : 0 ≤ D := le_max_right _ _
  have hkD (e : E) : |k e| ≤ D := (hC e).trans (le_max_left _ _)
  have hkZ : Measurable (fun t : ℝ => k (Z t.toNNReal ω)) :=
    hk.comp (hZ.comp (measurable_real_toNNReal.prodMk measurable_const))
  have hf : Measurable (fun t : ℝ => Real.exp (-t) * k (Z t.toNNReal ω)) := by
    fun_prop
  apply ((integrableOn_exp_neg_Ioi a).const_mul D).mono' hf.aestronglyMeasurable
  filter_upwards with t
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  calc
    Real.exp (-t) * |k (Z t.toNNReal ω)| ≤ Real.exp (-t) * D :=
      mul_le_mul_of_nonneg_left (hkD _) (Real.exp_pos _).le
    _ = D * Real.exp (-t) := mul_comm _ _

omit [MeasurableSpace E] in
private lemma stronglyMeasurable_occupation_past {ℱ : Filtration ℝ≥0 m}
    {Z : ℝ≥0 → Ω → E} {k : E → ℝ}
    (hprogk : IsStronglyProgressive ℱ fun t ω => k (Z t ω)) (t : ℝ≥0) :
    StronglyMeasurable[ℱ t] (fun ω =>
      ∫ s in Ioc (0 : ℝ) t, Real.exp (-s) * k (Z s.toNNReal ω)) := by
  let τ : ℝ → ℝ≥0 := fun s => min s.toNNReal t
  have hτ : Measurable[Real.measurableSpace.prod (ℱ t)] (fun p : ℝ × Ω =>
      (⟨τ p.1, min_le_right _ _⟩ : Set.Iic t)) := by
    apply Measurable.subtype_mk
    exact (measurable_real_toNNReal.comp measurable_fst).min measurable_const
  have hpk : StronglyMeasurable[Real.measurableSpace.prod (ℱ t)]
      (fun p : ℝ × Ω => k (Z (τ p.1) p.2)) := by
    have hsnd : @Measurable (ℝ × Ω) Ω (Real.measurableSpace.prod (ℱ t)) (ℱ t)
        (fun p => p.2) := measurable_snd
    exact (hprogk t).comp_measurable (hτ.prodMk hsnd)
  have hexp : StronglyMeasurable[Real.measurableSpace.prod (ℱ t)]
      (fun p : ℝ × Ω => Real.exp (-p.1)) :=
    (Real.measurable_exp.comp (measurable_neg.comp measurable_fst)).stronglyMeasurable
  have hmul : StronglyMeasurable[Real.measurableSpace.prod (ℱ t)]
      (fun p : ℝ × Ω => Real.exp (-p.1) * k (Z (τ p.1) p.2)) := hexp.mul hpk
  have hi := @StronglyMeasurable.integral_prod_left' ℝ Ω ℝ Real.measurableSpace (ℱ t)
    (volume.restrict (Ioc (0 : ℝ) (t : ℝ))) _ _ _
    (fun p : ℝ × Ω => Real.exp (-p.1) * k (Z (τ p.1) p.2)) hmul
  have heq : (fun ω => ∫ s in Ioc (0 : ℝ) (t : ℝ),
      Real.exp (-s) * k (Z (τ s) ω)) =
      (fun ω => ∫ s in Ioc (0 : ℝ) t, Real.exp (-s) * k (Z s.toNNReal ω)) := by
    funext ω
    apply setIntegral_congr_fun measurableSet_Ioc
    intro s hs
    have hst : s.toNNReal ≤ t := by
      simpa only [Real.toNNReal_coe] using Real.toNNReal_le_toNNReal hs.2
    simp only [τ, min_eq_left hst]
  rw [← heq]
  exact hi

/-- **Explicit martingale.** Under the resolvent Markov hypothesis,
`J_t = ∫_0^t e^{-s}k(Z_s)ds + e^{-t}V(Z_t)` is a martingale. -/
theorem martingale_discounted_resolvent {ℱ : Filtration ℝ≥0 m} {Z : ℝ≥0 → Ω → E}
    {k V : E → ℝ}
    (hZ : Measurable fun p : ℝ≥0 × Ω => Z p.1 p.2) (hk : Measurable k) (hV : Measurable V)
    (hkb : ∃ C, ∀ e, |k e| ≤ C) (hVb : ∃ C, ∀ e, |V e| ≤ C)
    (hprogk : IsStronglyProgressive ℱ fun t ω => k (Z t ω))
    (hprogV : IsStronglyProgressive ℱ fun t ω => V (Z t ω))
    (hM : ResolventMarkov ℱ μ Z k V) :
    Martingale (fun (t : ℝ≥0) ω =>
      (∫ s in Ioc (0 : ℝ) t, Real.exp (-s) * k (Z s.toNNReal ω)) +
        Real.exp (-(t : ℝ)) * V (Z t ω)) ℱ μ := by
  -- `hV` and `hVb` belong to the interface shared with the second-moment theorems; the
  -- martingale property itself only uses the conditional expectation identity `hM`.
  have _hV : Measurable V := hV
  have _hVb : ∃ C, ∀ e, |V e| ≤ C := hVb
  have hjoint (a : ℝ) : Integrable
      (fun p : ℝ × Ω => Real.exp (-p.1) * k (Z p.1.toNNReal p.2))
      ((volume.restrict (Ioi a)).prod μ) :=
    integrable_exp_occupation_prod hZ hk hkb (integrableOn_exp_neg_Ioi a)
  have hB : Integrable (discountedOccupation Z k) μ := by
    exact (hjoint 0).integral_prod_right
  have hpast (t : ℝ≥0) : Integrable (fun ω =>
      ∫ s in Ioc (0 : ℝ) t, Real.exp (-s) * k (Z s.toNNReal ω)) μ := by
    exact (integrable_exp_occupation_prod hZ hk hkb
      ((integrableOn_exp_neg_Ioi 0).mono_set Ioc_subset_Ioi_self)).integral_prod_right
  have hfuture (t : ℝ≥0) : Integrable (fun ω =>
      ∫ s in Ioi (t : ℝ), Real.exp (-s) * k (Z s.toNNReal ω)) μ :=
    (hjoint (t : ℝ)).integral_prod_right
  have hsplit (t : ℝ≥0) (ω : Ω) : discountedOccupation Z k ω =
      (∫ s in Ioc (0 : ℝ) t, Real.exp (-s) * k (Z s.toNNReal ω)) +
        ∫ s in Ioi (t : ℝ), Real.exp (-s) * k (Z s.toNNReal ω) := by
    rw [discountedOccupation, ← Ioc_union_Ioi_eq_Ioi (show (0 : ℝ) ≤ t by positivity)]
    apply setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
    · exact (integrable_exp_occupation hZ hk hkb 0 ω).mono_set Ioc_subset_Ioi_self
    · exact integrable_exp_occupation hZ hk hkb (t : ℝ) ω
  have hcond (t : ℝ≥0) : μ[discountedOccupation Z k | ℱ t] =ᵐ[μ] fun ω =>
      (∫ s in Ioc (0 : ℝ) t, Real.exp (-s) * k (Z s.toNNReal ω)) +
        Real.exp (-(t : ℝ)) * V (Z t ω) := by
    have hBeq : discountedOccupation Z k = fun ω =>
        (∫ s in Ioc (0 : ℝ) t, Real.exp (-s) * k (Z s.toNNReal ω)) +
          ∫ s in Ioi (t : ℝ), Real.exp (-s) * k (Z s.toNNReal ω) := by
      funext ω
      exact hsplit t ω
    rw [hBeq]
    calc
      _ =ᵐ[μ] μ[fun ω => ∫ s in Ioc (0 : ℝ) t,
          Real.exp (-s) * k (Z s.toNNReal ω) | ℱ t] +
          μ[fun ω => ∫ s in Ioi (t : ℝ), Real.exp (-s) * k (Z s.toNNReal ω) | ℱ t] :=
        condExp_add (hpast t) (hfuture t) _
      _ =ᵐ[μ] _ := by
        filter_upwards [hM t] with ω hω
        simp only [Pi.add_apply]
        rw [condExp_of_stronglyMeasurable (ℱ.le t)
          (stronglyMeasurable_occupation_past hprogk t) (hpast t), hω]
  have hadapt : StronglyAdapted ℱ (fun (t : ℝ≥0) ω =>
      (∫ s in Ioc (0 : ℝ) t, Real.exp (-s) * k (Z s.toNNReal ω)) +
        Real.exp (-(t : ℝ)) * V (Z t ω)) := by
    intro t
    exact (stronglyMeasurable_occupation_past hprogk t).add
      ((hprogV.stronglyAdapted t).const_mul (Real.exp (-(t : ℝ))))
  exact (martingale_condExp (discountedOccupation Z k) ℱ μ).congr hadapt hcond



/-- **Signed second-moment identity**: `E B² = 2 E ∫_0^∞ e^{-2t} k(Z_t) V(Z_t) dt`, with
`B = discountedOccupation Z k`; both sides finite. -/
theorem integral_sq_discountedOccupation {ℱ : Filtration ℝ≥0 m} {Z : ℝ≥0 → Ω → E} {k V : E → ℝ}
    (hZ : Measurable fun p : ℝ≥0 × Ω => Z p.1 p.2) (hk : Measurable k) (hV : Measurable V)
    (hkb : ∃ C, ∀ e, |k e| ≤ C) (hVb : ∃ C, ∀ e, |V e| ≤ C)
    (hprogk : IsStronglyProgressive ℱ fun t ω => k (Z t ω))
    (hprogV : IsStronglyProgressive ℱ fun t ω => V (Z t ω)) (hM : ResolventMarkov ℱ μ Z k V) :
    ∫ ω, (discountedOccupation Z k ω) ^ 2 ∂μ =
      2 * ∫ ω, (∫ t in Ioi (0 : ℝ),
        Real.exp (-2 * t) * (k (Z t.toNNReal ω) * V (Z t.toNNReal ω))) ∂μ := by
  obtain ⟨C₀, hC₀⟩ := hkb
  obtain ⟨D₀, hD₀⟩ := hVb
  let C := max C₀ 0
  let D := max D₀ 0
  have hC : ∀ e, |k e| ≤ C := fun e => (hC₀ e).trans (le_max_left _ _)
  have hD : ∀ e, |V e| ≤ D := fun e => (hD₀ e).trans (le_max_left _ _)
  have hC0 : 0 ≤ C := le_max_right _ _
  have _hprogV := hprogV
  let F : ℝ × Ω → ℝ := fun p => k (Z p.1.toNNReal p.2)
  let T : ℝ × Ω → ℝ := fun p =>
    ∫ t in Ioi (p.1.toNNReal : ℝ), Real.exp (-t) * k (Z t.toNNReal p.2)
  have hF : Measurable F :=
    hk.comp (hZ.comp ((measurable_real_toNNReal.comp measurable_fst).prodMk measurable_snd))
  have hVZ : Measurable (fun p : ℝ × Ω => V (Z p.1.toNNReal p.2)) :=
    hV.comp (hZ.comp ((measurable_real_toNNReal.comp measurable_fst).prodMk measurable_snd))
  have hf : Measurable (fun p : ℝ × Ω => Real.exp (-p.1) * F p) := by fun_prop
  have hT : Measurable T := by
    exact (measurable_integral_tail hf).comp
      ((measurable_real_toNNReal.coe_nnreal_real.comp measurable_fst).prodMk measurable_snd)
  have hTb (p : ℝ × Ω) : |T p| ≤ C := by
    have hb := norm_integral_le_of_norm_le
      ((integrableOn_exp_neg_Ioi (p.1.toNNReal : ℝ)).const_mul C)
      (Eventually.of_forall (fun t => show
        ‖Real.exp (-t) * k (Z t.toNNReal p.2)‖ ≤ C * Real.exp (-t) by
        rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
        exact (mul_le_mul_of_nonneg_left (hC _) (Real.exp_pos _).le).trans_eq
          (mul_comm _ _)))
    rw [integral_const_mul, integral_exp_neg_Ioi] at hb
    change |T p| ≤ C
    exact hb.trans ((mul_le_mul_of_nonneg_left
      (Real.exp_le_one_iff.2 (neg_nonpos.2 p.1.toNNReal.coe_nonneg)) hC0).trans_eq
        (mul_one C))
  have hFT : ∀ p, |F p * T p| ≤ C * C := fun p => by
    rw [abs_mul]
    exact mul_le_mul (hC _) (hTb p) (abs_nonneg _) hC0
  have hG : Integrable (fun p : ℝ × Ω => Real.exp (-p.1) * (F p * T p))
      ((volume.restrict (Ioi 0)).prod μ) := by
    simpa only [neg_one_mul] using
      integrable_exp_mul_bounded_prod (μ := μ)
        (F := fun p => F p * T p) (by fun_prop) (by norm_num : (-1 : ℝ) < 0) hFT
  have hR : Integrable (fun p : ℝ × Ω =>
      Real.exp (-2 * p.1) * (F p * V (Z p.1.toNNReal p.2)))
      ((volume.restrict (Ioi 0)).prod μ) :=
    integrable_exp_mul_bounded_prod
      (F := fun p => F p * V (Z p.1.toNNReal p.2)) (by fun_prop) (by norm_num : (-2 : ℝ) < 0)
      (fun p => by
        rw [abs_mul]
        exact mul_le_mul (hC _) (hD _) (abs_nonneg _) hC0)
  have hpath (ω : Ω) : discountedOccupation Z k ω ^ 2 =
      2 * ∫ s in Ioi (0 : ℝ), Real.exp (-s) * (F (s, ω) * T (s, ω)) := by
    have hs := integral_sq_eq_two_mul_tail (integrable_exp_occupation hZ hk ⟨C, hC⟩ 0 ω)
    change _ = 2 * _ at hs
    rw [discountedOccupation, hs]
    congr 1
    apply setIntegral_congr_fun measurableSet_Ioi
    intro s hs
    dsimp only
    rw [Measure.restrict_restrict_of_subset (Ioi_subset_Ioi hs.le)]
    simp only [T, F, Real.coe_toNNReal _ hs.le]
    ring
  have htime (s : ℝ) (hs : 0 < s) :
      (∫ ω, Real.exp (-s) * (F (s, ω) * T (s, ω)) ∂μ) =
      ∫ ω, Real.exp (-2 * s) * (F (s, ω) * V (Z s.toNNReal ω)) ∂μ := by
    have hfuture : Integrable (fun ω => T (s, ω)) μ :=
      (integrable_exp_occupation_prod hZ hk ⟨C, hC⟩
        (integrableOn_exp_neg_Ioi (s.toNNReal : ℝ))).integral_prod_right
    have hprod : Integrable ((fun ω => Real.exp (-s) * F (s, ω)) *
        (fun ω => T (s, ω))) μ := by
      have hm : Measurable (fun ω => Real.exp (-s) * F (s, ω) * T (s, ω)) := by
        exact ((hf.comp (measurable_const.prodMk measurable_id)).mul
          (hT.comp (measurable_const.prodMk measurable_id)))
      apply (integrable_const (Real.exp (-s) * (C * C))).mono' hm.aestronglyMeasurable
      filter_upwards with ω
      change ‖Real.exp (-s) * F (s, ω) * T (s, ω)‖ ≤ Real.exp (-s) * (C * C)
      simpa only [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), mul_assoc]
        using mul_le_mul_of_nonneg_left (hFT (s, ω)) (Real.exp_pos (-s)).le
    have hpull := condExp_mul_of_stronglyMeasurable_left
      ((hprogk.stronglyAdapted s.toNNReal).const_mul (Real.exp (-s))) hprod hfuture
    calc
      _ = ∫ ω, (μ[(fun ω => Real.exp (-s) * F (s, ω)) *
          (fun ω => T (s, ω)) | ℱ s.toNNReal]) ω ∂μ := by
        rw [integral_condExp (ℱ.le _)]
        simp only [Pi.mul_apply, mul_assoc]
      _ = _ := by
        apply integral_congr_ae
        filter_upwards [hpull, hM s.toNNReal] with ω hp hm
        rw [hp]
        simp only [Pi.mul_apply]
        change Real.exp (-s) * F (s, ω) *
          (μ[fun ω => T (s, ω) | ℱ s.toNNReal]) ω = _
        rw [hm]
        rw [Real.coe_toNNReal _ hs.le]
        rw [show -2 * s = -s + -s by ring, Real.exp_add]
        ring
  calc
    _ = 2 * ∫ ω, (∫ s in Ioi (0 : ℝ),
        Real.exp (-s) * (F (s, ω) * T (s, ω))) ∂μ := by
      simp_rw [hpath, integral_const_mul]
    _ = 2 * ∫ s in Ioi (0 : ℝ),
        (∫ ω, Real.exp (-s) * (F (s, ω) * T (s, ω)) ∂μ) := by
      congr 1
      exact (integral_integral_swap
        (f := fun s ω => Real.exp (-s) * (F (s, ω) * T (s, ω))) hG).symm
    _ = 2 * ∫ s in Ioi (0 : ℝ),
        (∫ ω, Real.exp (-2 * s) * (F (s, ω) * V (Z s.toNNReal ω)) ∂μ) := by
      congr 1
      exact setIntegral_congr_fun measurableSet_Ioi htime
    _ = _ := by
      exact congrArg (fun x : ℝ => 2 * x) (integral_integral_swap
        (f := fun s ω => Real.exp (-2 * s) * (F (s, ω) * V (Z s.toNNReal ω))) hR)


/-- **Cheap bound**: if `|V| ≤ D` then `E B² ≤ 2 D E ∫_0^∞ e^{-2t}|k(Z_t)| dt`. -/
theorem integral_sq_discountedOccupation_le {ℱ : Filtration ℝ≥0 m} {Z : ℝ≥0 → Ω → E}
    {k V : E → ℝ} (hZ : Measurable fun p : ℝ≥0 × Ω => Z p.1 p.2) (hk : Measurable k)
    (hV : Measurable V) (hkb : ∃ C, ∀ e, |k e| ≤ C) {D : ℝ} (hD : ∀ e, |V e| ≤ D)
    (hprogk : IsStronglyProgressive ℱ fun t ω => k (Z t ω))
    (hprogV : IsStronglyProgressive ℱ fun t ω => V (Z t ω)) (hM : ResolventMarkov ℱ μ Z k V) :
    ∫ ω, (discountedOccupation Z k ω) ^ 2 ∂μ ≤
      2 * D * ∫ ω, (∫ t in Ioi (0 : ℝ), Real.exp (-2 * t) * |k (Z t.toNNReal ω)|) ∂μ := by
  rw [integral_sq_discountedOccupation hZ hk hV hkb ⟨D, hD⟩ hprogk hprogV hM]
  obtain ⟨C₀, hC₀⟩ := hkb
  let C := max C₀ 0
  have hC : ∀ e, |k e| ≤ C := fun e => (hC₀ e).trans (le_max_left _ _)
  have hC0 : 0 ≤ C := le_max_right _ _
  have hkZ : Measurable (fun p : ℝ × Ω => k (Z p.1.toNNReal p.2)) :=
    hk.comp (hZ.comp ((measurable_real_toNNReal.comp measurable_fst).prodMk measurable_snd))
  have hVZ : Measurable (fun p : ℝ × Ω => V (Z p.1.toNNReal p.2)) :=
    hV.comp (hZ.comp ((measurable_real_toNNReal.comp measurable_fst).prodMk measurable_snd))
  have hA : Integrable (fun p : ℝ × Ω => Real.exp (-2 * p.1) * |k (Z p.1.toNNReal p.2)|)
      ((volume.restrict (Ioi 0)).prod μ) :=
    integrable_exp_mul_bounded_prod
      (F := fun p => |k (Z p.1.toNNReal p.2)|)
      (by simpa only [Real.norm_eq_abs] using hkZ.norm) (by norm_num : (-2 : ℝ) < 0)
      (fun p => by simpa only [abs_abs] using hC (Z p.1.toNNReal p.2))
  have hR : Integrable (fun p : ℝ × Ω =>
      Real.exp (-2 * p.1) * (k (Z p.1.toNNReal p.2) * V (Z p.1.toNNReal p.2)))
      ((volume.restrict (Ioi 0)).prod μ) :=
    integrable_exp_mul_bounded_prod
      (F := fun p => k (Z p.1.toNNReal p.2) * V (Z p.1.toNNReal p.2)) (by fun_prop)
      (by norm_num : (-2 : ℝ) < 0)
      (fun p => by
        rw [abs_mul]
        exact mul_le_mul (hC _) ((hD _).trans (le_abs_self D)) (abs_nonneg _) hC0)
  have hle : (∫ ω, (∫ t in Ioi (0 : ℝ), Real.exp (-2 * t) *
      (k (Z t.toNNReal ω) * V (Z t.toNNReal ω))) ∂μ) ≤
      D * ∫ ω, (∫ t in Ioi (0 : ℝ), Real.exp (-2 * t) * |k (Z t.toNNReal ω)|) ∂μ := by
    rw [← integral_const_mul]
    apply integral_mono_ae hR.integral_prod_right (hA.integral_prod_right.const_mul D)
    filter_upwards [hR.prod_left_ae, hA.prod_left_ae] with ω hRω hAω
    rw [← integral_const_mul]
    apply integral_mono hRω (hAω.const_mul D)
    intro t
    calc
      _ ≤ Real.exp (-2 * t) * (|k (Z t.toNNReal ω)| * D) := by
        apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
        exact (le_abs_self _).trans ((abs_mul _ _).le.trans
          (mul_le_mul_of_nonneg_left (hD _) (abs_nonneg _)))
      _ = _ := by ring
  exact (mul_le_mul_of_nonneg_left hle (by norm_num : (0 : ℝ) ≤ 2)).trans_eq
    (by ring)


end ResolventMoments

end BGW.Probability
