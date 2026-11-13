/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.Scalar.ForestWalkBridge
public import BGW.StableTrees.Scalar.Bounds
public import BGW.StableTrees.RegularVariation.Karamata
public import BGW.LocallyFinite.Atoms
public import BGW.LocallyFinite.Normalization

/-!
# Local and bridge-weighted tail bounds for finite forest sizes

The total forest weight is proved from the existing finite-tree weights and
the Bienaymé law. For every offspring PMF it is at most one. The local and
tail bounds then follow from `StableDomain`, the scalar local limit theorem,
Kemperman's identity, and regular variation. No extra estimate package is
assumed, and positivity of the normalizer is used only at positive times.
The lower size bound and the normalized bridge bound retain explicit
admissibility; periodic offspring laws are allowed.

Adapted from `PoissonDeclumping/Bienayme/Basic.lean` and
`PoissonDeclumping/Bridge/ForestEstimates.lean` in
`igor-kortchemski/rare-subtree-patterns`, commit
`fc5ef722392b1af41e8b9d5fc45d5a521b7823dd` (Apache-2.0). The source uses
tuples of its own finite trees; here all sums use the existing
`BGW.forestWeight` on lists of `BGW.PlaneTree`. The lower endpoint bound
adapts the finite-minimum argument of `PoissonDeclumping/Setup/Toolkit.lean`
directly to the proved lattice local limit theorem, without a toolkit hypothesis.
-/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace BGW.StableTrees.Scalar

variable {μ : PMF ℕ} {α : ℝ} {a : ℕ → ℝ}

private theorem tsum_pi_fin_prod {β : Type*} : ∀ (k : ℕ) (g : Fin k → β → ℝ≥0∞),
    ∑' f : Fin k → β, ∏ i, g i (f i) = ∏ i, ∑' b, g i b
  | 0, g => by simp
  | k + 1, g => by
    rw [← (Fin.consEquiv fun _ : Fin (k + 1) => β).tsum_eq]
    simp only [Fin.consEquiv, Equiv.coe_fn_mk, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
    rw [ENNReal.tsum_prod']
    simp only [ENNReal.tsum_mul_left]
    rw [tsum_pi_fin_prod k (fun i => g i.succ), ENNReal.tsum_mul_right]

/-- Summing over sizes gives the product of the total weights of the component trees. -/
theorem tsum_forestWeight (p : ℕ → ℝ≥0∞) (ℓ : ℕ) :
    (∑' n, BGW.forestWeight p ℓ n) =
      (∑' t : BGW.PlaneTree, BGW.PlaneTree.weight p t) ^ ℓ := by
  unfold BGW.forestWeight
  rw [ENNReal.tsum_comm]
  calc
    (∑' ts : BGW.PlaneForest, ∑' n,
        if ts.length = ℓ ∧ BGW.PlaneForest.size ts = n
        then (ts.map (BGW.PlaneTree.weight p)).prod else 0) =
        ∑' ts : BGW.PlaneForest,
          if ts.length = ℓ then (ts.map (BGW.PlaneTree.weight p)).prod else 0 := by
      refine tsum_congr fun ts => ?_
      by_cases hlen : ts.length = ℓ
      · simp only [hlen, true_and, ite_true]
        rw [tsum_eq_single (BGW.PlaneForest.size ts)
          (fun n hn => ite_eq_right (Ne.symm hn))]
        simp
      · simp [hlen]
    _ = (∑' t : BGW.PlaneTree, BGW.PlaneTree.weight p t) ^ ℓ := by
      rw [← List.equivSigmaTuple.symm.tsum_eq, ENNReal.tsum_sigma', tsum_eq_single ℓ]
      · simp only [List.equivSigmaTuple_symm_apply, List.length_ofFn, ite_true,
          List.map_ofFn, List.prod_ofFn]
        change (∑' f : Fin ℓ → BGW.PlaneTree, ∏ i, BGW.PlaneTree.weight p (f i)) = _
        rw [tsum_pi_fin_prod]
        simp
      · intro j hj
        simp [List.equivSigmaTuple_symm_apply, hj]

/-- The empty forest has zero vertices and weight one. -/
theorem forestWeight_zero_left (p : ℕ → ℝ≥0∞) (n : ℕ) :
    BGW.forestWeight p 0 n = if n = 0 then 1 else 0 := by
  unfold BGW.forestWeight
  rw [tsum_eq_single ([] : BGW.PlaneForest)]
  · simp [BGW.PlaneForest.size, eq_comm]
  · intro ts hts
    have hlen : ts.length ≠ 0 := fun h => hts (List.length_eq_zero_iff.mp h)
    simp [hlen]

/-- For every offspring law, the finite forests have total weight at most one. -/
theorem tsum_forestWeight_le_one (μ : PMF ℕ) (ℓ : ℕ) :
    ∑' n, BGW.forestWeight μ ℓ n ≤ 1 := by
  rw [tsum_forestWeight]
  apply pow_le_one₀ zero_le
  simpa only [PMF.toMeasure_apply_singleton μ _ (measurableSet_singleton _)] using
    BGW.LocallyFinite.tsum_weight_le_one μ.toMeasure

/-- For a critical law other than the point mass at one, finite forests have total mass one. -/
theorem tsum_forestWeight_eq_one (hc : IsCritical μ) (hne : μ 1 ≠ 1) (ℓ : ℕ) :
    ∑' n, BGW.forestWeight μ ℓ n = 1 := by
  have hm : ∫⁻ k : ℕ, (k : ℝ≥0∞) ∂μ.toMeasure = 1 := by
    rw [lintegral_countable']
    simpa only [IsCritical,
      PMF.toMeasure_apply_singleton μ _ (measurableSet_singleton _)] using hc
  have hne' : μ.toMeasure {1} ≠ 1 := by
    simpa only [PMF.toMeasure_apply_singleton μ _ (measurableSet_singleton _)] using hne
  have ht : (∑' t : BGW.PlaneTree, BGW.PlaneTree.weight μ t) = 1 := by
    simpa only [PMF.toMeasure_apply_singleton μ _ (measurableSet_singleton _)] using
      BGW.LocallyFinite.tsum_weight_eq_one μ.toMeasure hm.le hne'
  rw [tsum_forestWeight, ht, one_pow]

theorem forestWeight_le_one (μ : PMF ℕ) (ℓ n : ℕ) : BGW.forestWeight μ ℓ n ≤ 1 :=
  (ENNReal.le_tsum n).trans (tsum_forestWeight_le_one μ ℓ)

theorem forestWeight_ne_top (μ : PMF ℕ) (ℓ n : ℕ) : BGW.forestWeight μ ℓ n ≠ ∞ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (forestWeight_le_one μ ℓ n)

theorem summable_forestWeight_toReal (μ : PMF ℕ) (ℓ : ℕ) :
    Summable (fun n => (BGW.forestWeight μ ℓ n).toReal) :=
  ENNReal.summable_toReal (ne_top_of_le_ne_top ENNReal.one_ne_top
    (tsum_forestWeight_le_one μ ℓ))

/-- The local forest-size bound, uniform in the number of components and positive size. -/
theorem forestWeight_toReal_le (h : StableDomain μ α a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ℓ q : ℕ, 1 ≤ q →
      (BGW.forestWeight μ ℓ q).toReal ≤ C * ℓ / (q * a q) := by
  obtain ⟨C, hC⟩ := exists_walkProb_le h
  refine ⟨max C 0, le_max_right _ _, fun ℓ q hq => ?_⟩
  have haq : 0 < a q := h.pos q hq
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  rcases Nat.eq_zero_or_pos ℓ with rfl | hℓ
  · rw [forestWeight_zero_left, ite_eq_right (by omega)]
    simp
  · rw [forestWeight_toReal_eq μ hℓ hq]
    have h1 : walkProb μ q (-ℓ) ≤ max C 0 / a q :=
      (hC q hq _).trans (by gcongr; exact le_max_left _ _)
    calc (ℓ : ℝ) / q * walkProb μ q (-ℓ) ≤ ℓ / q * (max C 0 / a q) := by gcongr
      _ = max C 0 * ℓ / (q * a q) := by field_simp

/-- The forest-size tail bound, with no restriction on the number of components. -/
theorem forest_tail_le (h : StableDomain μ α a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ℓ m : ℕ, 1 ≤ m →
      ∑' q, (Set.Ioi m).indicator (fun q => (BGW.forestWeight μ ℓ q).toReal) q ≤
        C * ℓ / a m := by
  obtain ⟨C₀, hC₀, hloc⟩ := forestWeight_toReal_le h
  have hρ : 0 < 1 / α := one_div_pos.2 (by linarith [h.alpha_mem.1])
  obtain ⟨K, hK, hKt⟩ :=
    (regularlyVaryingSeq h).karamata_tail_tsum h.monotone h.pos hρ
  have hsum := (regularlyVaryingSeq h).summable_inv_mul h.monotone h.pos hρ
  refine ⟨C₀ * K, by positivity, fun ℓ m hm => ?_⟩
  have ham : 0 < a m := h.pos m hm
  have hle : ∀ q, (Set.Ioi m).indicator (fun q => (BGW.forestWeight μ ℓ q).toReal) q ≤
      (C₀ * ℓ) * (Set.Ioi m).indicator (fun q : ℕ => 1 / ((q : ℝ) * a q)) q := by
    intro q
    by_cases hq : q ∈ Set.Ioi m
    · rw [Set.indicator_of_mem hq, Set.indicator_of_mem hq]
      have hq1 : 1 ≤ q := by have := Set.mem_Ioi.1 hq; omega
      calc (BGW.forestWeight μ ℓ q).toReal ≤ C₀ * ℓ / (q * a q) := hloc ℓ q hq1
        _ = C₀ * ℓ * (1 / (q * a q)) := by ring
    · rw [Set.indicator_of_notMem hq, Set.indicator_of_notMem hq, mul_zero]
  have hs2 : Summable fun q => (C₀ * ℓ) *
      (Set.Ioi m).indicator (fun q : ℕ => 1 / ((q : ℝ) * a q)) q :=
    (hsum.indicator _).mul_left _
  have hs1 : Summable fun q =>
      (Set.Ioi m).indicator (fun q => (BGW.forestWeight μ ℓ q).toReal) q :=
    (summable_forestWeight_toReal μ ℓ).indicator _
  calc ∑' q, (Set.Ioi m).indicator (fun q => (BGW.forestWeight μ ℓ q).toReal) q
      ≤ ∑' q, (C₀ * ℓ) * (Set.Ioi m).indicator (fun q : ℕ => 1 / ((q : ℝ) * a q)) q :=
        hs1.tsum_le_tsum hle hs2
    _ = (C₀ * ℓ) * ∑' q, (Set.Ioi m).indicator (fun q : ℕ => 1 / ((q : ℝ) * a q)) q :=
        tsum_mul_left
    _ ≤ (C₀ * ℓ) * (K / a m) := by gcongr; exact hKt m hm
    _ = C₀ * K * ℓ / a m := by ring


/-- Negative times have zero walk mass. -/
theorem walkProb_of_neg (μ : PMF ℕ) {m : ℤ} (hm : m < 0) (i : ℤ) :
    walkProb μ m i = 0 := by
  rw [walkProb, ite_eq_right (by omega)]

theorem walkProb_nonneg (μ : PMF ℕ) (m i : ℤ) : 0 ≤ walkProb μ m i := by
  unfold walkProb
  split_ifs
  · exact measureReal_nonneg
  · exact le_rfl

theorem walkProb_le_one (μ : PMF ℕ) (m i : ℤ) : walkProb μ m i ≤ 1 := by
  unfold walkProb
  split_ifs
  · exact measureReal_le_one
  · exact zero_le_one

/-- The supremum of the walk's point masses, also defined at negative times. -/
noncomputable def supWalk (μ : PMF ℕ) (m : ℤ) : ℝ := ⨆ x : ℤ, walkProb μ m x

theorem bddAbove_range_walkProb (μ : PMF ℕ) (m : ℤ) :
    BddAbove (Set.range (walkProb μ m)) :=
  ⟨1, by rintro _ ⟨x, rfl⟩; exact walkProb_le_one μ m x⟩

theorem walkProb_le_supWalk (μ : PMF ℕ) (m x : ℤ) :
    walkProb μ m x ≤ supWalk μ m :=
  le_ciSup (bddAbove_range_walkProb μ m) x

theorem supWalk_nonneg (μ : PMF ℕ) (m : ℤ) : 0 ≤ supWalk μ m :=
  (walkProb_nonneg μ m 0).trans (walkProb_le_supWalk μ m 0)

theorem supWalk_le_one (μ : PMF ℕ) (m : ℤ) : supWalk μ m ≤ 1 :=
  ciSup_le fun x => walkProb_le_one μ m x

theorem supWalk_of_neg (μ : PMF ℕ) {m : ℤ} (hm : m < 0) : supWalk μ m = 0 := by
  simp [supWalk, walkProb_of_neg μ hm]

/-- The local bound for the supremum of the point masses. -/
theorem exists_supWalk_le (h : StableDomain μ α a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ m : ℕ, 1 ≤ m → supWalk μ m ≤ C / a m := by
  obtain ⟨C, hC⟩ := exists_walkProb_le h
  refine ⟨max C 0, le_max_right _ _, fun m hm => ciSup_le fun x => ?_⟩
  exact (hC m hm x).trans (by gcongr; exacts [(h.pos m hm).le, le_max_left _ _])

/-- The local bound at comparable positive times. -/
theorem exists_supWalk_le_of_le_two_mul (h : StableDomain μ α a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n m : ℕ, 1 ≤ n → 1 ≤ m → n ≤ 2 * m →
      supWalk μ m ≤ C / a n := by
  obtain ⟨C₀, hC₀⟩ := exists_walkProb_le h
  have hρ : 0 ≤ 1 / α := (one_div_pos.2 (by linarith [h.alpha_mem.1])).le
  obtain ⟨C₁, hC₁pos, hC₁⟩ :=
    (regularlyVaryingSeq h).exists_le_mul_of_le_mul h.monotone h.pos hρ 2
  refine ⟨max C₀ 0 * C₁, by positivity, fun n m hn hm hnm => ciSup_le fun x => ?_⟩
  have ham : 0 < a m := h.pos m hm
  have han : 0 < a n := h.pos n hn
  have h1 : a n ≤ C₁ * a m := hC₁ m n hm (by exact_mod_cast hnm)
  calc walkProb μ m x ≤ C₀ / a m := hC₀ m hm x
    _ ≤ max C₀ 0 / a m := by gcongr; exact le_max_left _ _
    _ = max C₀ 0 * C₁ / (C₁ * a m) := by field_simp
    _ ≤ max C₀ 0 * C₁ / a n := by gcongr

/-- The bridge-weighted forest tail in numerator form. Negative remaining times
contribute zero, and the zero-time term is handled without using `a 0`. -/
theorem forest_weighted_tail_sup_le (hT : StableDomain μ α a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ℓ m N : ℕ, 1 ≤ m → 2 * m ≤ N →
      ∑' q, (Set.Ioi m).indicator
        (fun q => (BGW.forestWeight μ ℓ q).toReal * supWalk μ ((N : ℤ) - q)) q ≤
        C * ℓ / (a m * a N) := by
  have hρ : 0 < 1 / α := one_div_pos.2 (by linarith [hT.alpha_mem.1])
  have hρ1 : 1 / α < 1 := (div_lt_one (by linarith [hT.alpha_mem.1])).2 hT.alpha_mem.1
  obtain ⟨C₀, hC₀, hloc⟩ := forestWeight_toReal_le hT
  obtain ⟨C₁, hC₁, hsup2⟩ := exists_supWalk_le_of_le_two_mul hT
  obtain ⟨S₀, hS₀, hsup⟩ := exists_supWalk_le hT
  obtain ⟨C₂, hC₂, htail⟩ := forest_tail_le hT
  obtain ⟨C₃, hC₃, hcomp⟩ := (regularlyVaryingSeq hT).exists_le_mul_of_le_mul hT.monotone hT.pos
    hρ.le 2
  obtain ⟨C₄, hC₄, hkar⟩ := (regularlyVaryingSeq hT).karamata_sum hT.monotone hT.pos hρ.le
    hρ1
  obtain ⟨C₅, hC₅, hlin⟩ := (regularlyVaryingSeq hT).exists_le_mul hT.monotone hT.pos hρ.le
    hρ1
  set K : ℝ := 2 * C₀ * C₃ with hKdef
  have hK : 0 ≤ K := by positivity
  refine ⟨C₁ * C₂ + K * C₅ + K * S₀ * C₄, by positivity, fun ℓ m N hm hmN => ?_⟩
  have hN1 : 1 ≤ N := by omega
  have ham : 0 < a m := hT.pos m hm
  have haN : 0 < a N := hT.pos N hN1
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN1
  have hamN : a m ≤ a N := hT.monotone (by omega)
  have hℓ : (0 : ℝ) ≤ ℓ := Nat.cast_nonneg ℓ
  -- the comparison function `g h ≥ sup_x Ψ_h`
  set g : ℕ → ℝ := fun h => if h = 0 then 1 else S₀ / a h with hgdef
  have hg0 : ∀ h, 0 ≤ g h := by
    intro h
    simp only [hgdef]
    split_ifs with hh
    · exact zero_le_one
    · exact div_nonneg hS₀ (hT.pos h (by omega)).le
  have hsupg : ∀ h : ℕ, supWalk μ h ≤ g h := by
    intro h
    simp only [hgdef]
    split_ifs with hh
    · exact supWalk_le_one μ _
    · exact hsup h (by omega)
  set F : ℕ → ℝ := (Set.Ioi m).indicator (fun q => (BGW.forestWeight μ ℓ q).toReal) with hFdef
  set B : ℕ → ℝ := fun q => if q ≤ N then g (N - q) else 0 with hBdef
  have hF0 : ∀ q, 0 ≤ F q := fun q => Set.indicator_nonneg (fun q _ => ENNReal.toReal_nonneg) q
  have hB0 : ∀ q, 0 ≤ B q := by
    intro q
    simp only [hBdef]
    split_ifs
    · exact hg0 _
    · exact le_rfl
  have hFs : Summable F := (summable_forestWeight_toReal μ ℓ).indicator _
  have hBs : Summable B := by
    refine summable_of_ne_finset_zero (s := Finset.range (N + 1)) fun q hq => ?_
    simp only [hBdef]
    rw [ite_eq_right]
    intro hqN
    exact absurd (Finset.mem_range.2 (by omega)) hq
  -- termwise domination
  have hterm : ∀ q, (Set.Ioi m).indicator
      (fun q => (BGW.forestWeight μ ℓ q).toReal * supWalk μ ((N : ℤ) - q)) q ≤
      C₁ / a N * F q + K * ℓ / (N * a N) * B q := by
    intro q
    have hr1 : 0 ≤ C₁ / a N * F q := mul_nonneg (by positivity) (hF0 q)
    have hr2 : 0 ≤ K * ℓ / (N * a N) * B q := mul_nonneg (by positivity) (hB0 q)
    by_cases hq : q ∈ Set.Ioi m
    · rw [Set.indicator_of_mem hq]
      have hqm : m < q := hq
      have hq1 : 1 ≤ q := by omega
      have hfq0 : 0 ≤ (BGW.forestWeight μ ℓ q).toReal := ENNReal.toReal_nonneg
      rcases le_or_gt q N with hqN | hqN
      · have hcast : (N : ℤ) - q = ((N - q : ℕ) : ℤ) := by push_cast [hqN]; ring
        rw [hcast]
        rcases le_or_gt (2 * q) N with h2q | h2q
        · -- `q ≤ N / 2`: `sup_x Ψ_{N-q} ≤ C₁ / a_N`
          have hs := hsup2 N (N - q) hN1 (by omega) (by omega)
          have hFq : F q = (BGW.forestWeight μ ℓ q).toReal := by
            rw [hFdef, Set.indicator_of_mem hq]
          calc (BGW.forestWeight μ ℓ q).toReal * supWalk μ ((N - q : ℕ) : ℤ)
              ≤ (BGW.forestWeight μ ℓ q).toReal * (C₁ / a N) := by gcongr
            _ = C₁ / a N * F q := by rw [hFq]; ring
            _ ≤ _ := le_add_of_nonneg_right hr2
        · -- `N / 2 < q ≤ N`
          have haq : 0 < a q := hT.pos q hq1
          have hqR : (0 : ℝ) < q := by exact_mod_cast hq1
          have hNq : a N ≤ C₃ * a q := hcomp q N hq1 (by exact_mod_cast h2q.le)
          have hf : (BGW.forestWeight μ ℓ q).toReal ≤ K * ℓ / (N * a N) := by
            calc (BGW.forestWeight μ ℓ q).toReal ≤ C₀ * ℓ / (q * a q) := hloc ℓ q hq1
              _ ≤ K * ℓ / (N * a N) := by
                rw [div_le_div_iff₀ (by positivity) (by positivity), hKdef]
                have h2 : (N : ℝ) ≤ 2 * q := by exact_mod_cast h2q.le
                have : (N : ℝ) * a N ≤ 2 * q * (C₃ * a q) :=
                  mul_le_mul h2 hNq haN.le (by positivity)
                nlinarith [mul_le_mul_of_nonneg_left this (show 0 ≤ C₀ * ℓ by positivity)]
          have hBq : B q = g (N - q) := by simp only [hBdef]; rw [ite_eq_left hqN]
          calc (BGW.forestWeight μ ℓ q).toReal * supWalk μ ((N - q : ℕ) : ℤ)
              ≤ K * ℓ / (N * a N) * g (N - q) :=
                mul_le_mul hf (hsupg _) (supWalk_nonneg μ _) (by positivity)
            _ = K * ℓ / (N * a N) * B q := by rw [hBq]
            _ ≤ _ := le_add_of_nonneg_left hr1
      · rw [supWalk_of_neg μ (by omega), mul_zero]
        exact add_nonneg hr1 hr2
    · rw [Set.indicator_of_notMem hq]
      exact add_nonneg hr1 hr2
  -- the two sums
  have hsumB : ∑' q, B q ≤ 1 + S₀ * C₄ * N / a N := by
    rw [tsum_eq_sum (s := Finset.range (N + 1)) fun q hq => by
      simp only [hBdef]
      rw [ite_eq_right]
      intro hqN
      exact absurd (Finset.mem_range.2 (by omega)) hq]
    have h1 : ∑ q ∈ Finset.range (N + 1), B q = ∑ h ∈ Finset.range (N + 1), g h := by
      rw [← Finset.sum_range_reflect]
      refine Finset.sum_congr rfl fun q hq => ?_
      have hq' := Finset.mem_range.1 hq
      simp only [hBdef]
      rw [ite_eq_left (by omega)]
      congr 1
      omega
    rw [h1, Finset.sum_range_succ', Finset.range_eq_Ico]
    have h2 : ∑ h ∈ Finset.Ico 0 N, g (h + 1) = ∑ h ∈ Finset.Icc 1 N, S₀ / a h := by
      rw [Finset.sum_Ico_add' (c := 1), zero_add, Finset.Ico_add_one_right_eq_Icc]
      refine Finset.sum_congr rfl fun h hh => ?_
      have := (Finset.mem_Icc.1 hh).1
      simp only [hgdef]
      rw [ite_eq_right (by omega)]
    have h3 : ∑ h ∈ Finset.Icc 1 N, S₀ / a h = S₀ * ∑ h ∈ Finset.Icc 1 N, 1 / a h := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun h _ => by ring
    rw [h2, h3]
    have hg00 : g 0 = 1 := by simp [hgdef]
    rw [hg00]
    have := hkar N
    have h4 : S₀ * ∑ h ∈ Finset.Icc 1 N, 1 / a h ≤ S₀ * (C₄ * N / a N) :=
      mul_le_mul_of_nonneg_left this hS₀
    calc S₀ * ∑ h ∈ Finset.Icc 1 N, 1 / a h + 1 ≤ S₀ * (C₄ * N / a N) + 1 := by linarith
      _ = 1 + S₀ * C₄ * N / a N := by ring
  have hsumF : ∑' q, F q ≤ C₂ * ℓ / a m := htail ℓ m hm
  have hs_lhs : Summable fun q => (Set.Ioi m).indicator
      (fun q => (BGW.forestWeight μ ℓ q).toReal * supWalk μ ((N : ℤ) - q)) q := by
    refine Summable.of_nonneg_of_le (fun q => ?_) hterm ((hFs.mul_left _).add (hBs.mul_left _))
    exact Set.indicator_nonneg (fun q _ => mul_nonneg ENNReal.toReal_nonneg
      (supWalk_nonneg μ _)) q
  calc ∑' q, (Set.Ioi m).indicator
        (fun q => (BGW.forestWeight μ ℓ q).toReal * supWalk μ ((N : ℤ) - q)) q
      ≤ ∑' q, (C₁ / a N * F q + K * ℓ / (N * a N) * B q) :=
        hs_lhs.tsum_le_tsum hterm ((hFs.mul_left _).add (hBs.mul_left _))
    _ = C₁ / a N * ∑' q, F q + K * ℓ / (N * a N) * ∑' q, B q := by
        rw [(hFs.mul_left _).tsum_add (hBs.mul_left _), tsum_mul_left, tsum_mul_left]
    _ ≤ C₁ / a N * (C₂ * ℓ / a m) + K * ℓ / (N * a N) * (1 + S₀ * C₄ * N / a N) := by
        gcongr
    _ ≤ (C₁ * C₂ + K * C₅ + K * S₀ * C₄) * ℓ / (a m * a N) := by
        have hlinN : a m ≤ C₅ * N := hamN.trans (hlin N hN1)
        have e1 : C₁ / a N * (C₂ * ℓ / a m) = C₁ * C₂ * ℓ / (a m * a N) := by
          field_simp
        have e2 : K * ℓ / (N * a N) * 1 ≤ K * C₅ * ℓ / (a m * a N) := by
          rw [mul_one, div_le_div_iff₀ (by positivity) (by positivity)]
          have : K * ℓ * (a m * a N) ≤ K * ℓ * (C₅ * N * a N) := by gcongr
          nlinarith
        have e3 : K * ℓ / (N * a N) * (S₀ * C₄ * N / a N) ≤ K * S₀ * C₄ * ℓ / (a m * a N) := by
          have : K * ℓ / (N * a N) * (S₀ * C₄ * N / a N) = K * S₀ * C₄ * ℓ / (a N * a N) := by
            field_simp
          rw [this]
          gcongr
        calc C₁ / a N * (C₂ * ℓ / a m) + K * ℓ / (N * a N) * (1 + S₀ * C₄ * N / a N)
            = C₁ / a N * (C₂ * ℓ / a m) + K * ℓ / (N * a N) * 1 +
              K * ℓ / (N * a N) * (S₀ * C₄ * N / a N) := by ring
          _ ≤ C₁ * C₂ * ℓ / (a m * a N) + K * C₅ * ℓ / (a m * a N) +
              K * S₀ * C₄ * ℓ / (a m * a N) := by rw [e1]; gcongr
          _ = _ := by ring


private theorem exists_pos_le_of_finset (s : Finset ℕ) (f : ℕ → ℝ)
    (hf : ∀ n ∈ s, 0 < f n) :
    ∃ c : ℝ, 0 < c ∧ ∀ n ∈ s, c ≤ f n := by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · exact ⟨1, one_pos, by simp⟩
  · exact ⟨s.inf' hs f, (Finset.lt_inf'_iff hs).2 hf,
      fun n hn => Finset.inf'_le f hn⟩

/-- A lower bound at every positive time where the endpoint `-1` has positive mass.
The lattice local limit theorem handles large times; a finite minimum handles the rest. -/
theorem exists_lower_bound_neg_one (h : StableDomain μ α a) :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 1 ≤ n → 0 < walkProb μ n (-1) →
      c / a n ≤ walkProb μ n (-1) := by
  classical
  set L : ℝ := (latticeSpan μ : ℝ) * stableDensity α 0 with hLdef
  have hd : (0 : ℝ) < latticeSpan μ := by
    exact_mod_cast latticeSpan_pos h.critical h.nondegenerate
  have hL : 0 < L := mul_pos hd (stableDensity_zero_pos h.alpha_mem)
  have harg : Tendsto (fun n => (-1 : ℝ) / a n) atTop (𝓝 0) :=
    (tendsto_atTop h).const_div_atTop (-1)
  have hden : Tendsto
      (fun n => (latticeSpan μ : ℝ) * stableDensity α ((-1 : ℝ) / a n))
      atTop (𝓝 L) :=
    ((continuous_stableDensity h.alpha_mem).continuousAt.tendsto.comp harg).const_mul _
  obtain ⟨N₀, hN₀⟩ := Metric.tendsto_atTop.1 hden (L / 4) (by positivity)
  obtain ⟨N₁, hN₁⟩ := localLimit h (show 0 < L / 4 by positivity)
  set N : ℕ := max N₀ N₁ with hNdef
  obtain ⟨c₀, hc₀, hc₀le⟩ := exists_pos_le_of_finset
    ((Finset.range N).filter fun n => 1 ≤ n ∧ 0 < walkProb μ n (-1))
    (fun n => a n * walkProb μ n (-1)) (by
      intro n hn
      simp only [Finset.mem_filter, Finset.mem_range] at hn
      exact mul_pos (h.pos n hn.2.1) hn.2.2)
  refine ⟨min (L / 2) c₀, lt_min (half_pos hL) hc₀, fun n hn hpos => ?_⟩
  have han := h.pos n hn
  rw [div_le_iff₀ han]
  rcases lt_or_ge n N with hnN | hnN
  · have h1 := hc₀le n (by simp [hnN, hn, hpos])
    have h2 := min_le_right (L / 2) c₀
    nlinarith
  · have hcompat : (latticeSpan μ : ℤ) ∣ (-1 : ℤ) + n := by
      by_contra hc
      rw [walkProb_eq_zero_of_not_dvd h hc] at hpos
      exact (lt_irrefl 0) hpos
    have hll := hN₁ n ((le_max_right N₀ N₁).trans hnN) (-1) hcompat
    have hclose := hN₀ n ((le_max_left N₀ N₁).trans hnN)
    rw [Real.dist_eq] at hclose
    have hlo := (abs_le.1 hll).1
    have hdenlo := (abs_lt.1 hclose).1
    have hmin := min_le_left (L / 2) c₀
    norm_num only [Int.cast_neg, Int.cast_one] at hlo
    nlinarith

/-- The size law is bounded above and below by `1 / (n * a n)` at its admissible sizes. -/
theorem tree_size_asymp (h : StableDomain μ α a) :
    ∃ c C : ℝ, 0 < c ∧ 0 ≤ C ∧ ∀ n : ℕ, 1 ≤ n →
      BGW.LocallyFinite.bienaymeLaw μ.toMeasure (BGW.LocallyFinite.sizeEvent n) ≠ 0 →
      c / (n * a n) ≤
          (BGW.LocallyFinite.bienaymeLaw μ.toMeasure).real (BGW.LocallyFinite.sizeEvent n) ∧
        (BGW.LocallyFinite.bienaymeLaw μ.toMeasure).real (BGW.LocallyFinite.sizeEvent n) ≤
          C / (n * a n) := by
  obtain ⟨c, hc, hlow⟩ := exists_lower_bound_neg_one h
  obtain ⟨C, hC, hupp⟩ := forestWeight_toReal_le h
  refine ⟨c, C, hc, hC, fun n hn hadm => ?_⟩
  have han : 0 < a n := h.pos n hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hF : BGW.forestWeight μ 1 n =
      BGW.LocallyFinite.bienaymeLaw μ.toMeasure (BGW.LocallyFinite.sizeEvent n) := by
    simpa only [PMF.toMeasure_apply_singleton μ _ (measurableSet_singleton _)] using
      BGW.LocallyFinite.forestWeight_one_eq_bienaymeLaw_sizeEvent μ.toMeasure n
  have hD : (n : ℝ) *
      (BGW.LocallyFinite.bienaymeLaw μ.toMeasure).real (BGW.LocallyFinite.sizeEvent n) =
      walkProb μ n (-1) := by
    simpa [hF, measureReal_def] using
      natCast_mul_forestWeight_toReal μ (ℓ := 1) (by omega) n
  have hp : 0 <
      (BGW.LocallyFinite.bienaymeLaw μ.toMeasure).real (BGW.LocallyFinite.sizeEvent n) :=
    ENNReal.toReal_pos hadm (by finiteness)
  have hψ : 0 < walkProb μ n (-1) := by
    rw [← hD]
    exact mul_pos hnR hp
  constructor
  · have hl := hlow n hn hψ
    rw [← hD, div_le_iff₀ han] at hl
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  · have hu := hupp 1 n hn
    simpa [hF, measureReal_def] using hu

/-- The normalized bridge-weighted tail at admissible endpoint times.
The explicit positivity premise retains the lattice restriction. -/
theorem forest_weighted_tail_sup_div_le (h : StableDomain μ α a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ℓ m N : ℕ, 1 ≤ m → 2 * m ≤ N →
      0 < walkProb μ N (-1) →
      (∑' q, (Set.Ioi m).indicator
        (fun q => (BGW.forestWeight μ ℓ q).toReal * supWalk μ ((N : ℤ) - q)) q) /
        walkProb μ N (-1) ≤ C * ℓ / a m := by
  obtain ⟨C, hC, hbound⟩ := forest_weighted_tail_sup_le h
  obtain ⟨c, hc, hlow⟩ := exists_lower_bound_neg_one h
  refine ⟨C / c, by positivity, fun ℓ m N hm hmN hψ => ?_⟩
  have hN : 1 ≤ N := by omega
  have haN : 0 < a N := h.pos N hN
  have ham : 0 < a m := h.pos m hm
  have hinv : (walkProb μ N (-1))⁻¹ ≤ a N / c := by
    rw [inv_le_comm₀ hψ (by positivity), inv_div]
    exact hlow N hN hψ
  have h0 : 0 ≤ ∑' q, (Set.Ioi m).indicator
      (fun q => (BGW.forestWeight μ ℓ q).toReal * supWalk μ ((N : ℤ) - q)) q :=
    tsum_nonneg fun q => Set.indicator_nonneg (fun q _ =>
      mul_nonneg ENNReal.toReal_nonneg (supWalk_nonneg μ _)) q
  rw [div_eq_mul_inv, mul_comm]
  calc (walkProb μ N (-1))⁻¹ * _ ≤ a N / c * (C * ℓ / (a m * a N)) :=
        mul_le_mul hinv (hbound ℓ m N hm hmN) h0 (by positivity)
    _ = C / c * ℓ / a m := by field_simp

end BGW.StableTrees.Scalar
