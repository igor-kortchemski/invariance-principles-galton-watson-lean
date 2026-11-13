/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module
public import BGW.StableTrees.WalkPassage
import Mathlib.Analysis.BoxIntegral.UnitPartition

/-! # Riemann sums on arithmetic progressions

Riemann sums over residue classes, used in the proof of Kendall's identity.

References: (D. G. Kendall, Some problems in the theory of dams, J. Roy. Statist. Soc. Ser. B 19
(1957), 207–212; A. A. Borovkov, *Stochastic Processes in Queueing Theory*, Springer, 1976; J.
Bertoin, *Lévy Processes*, Cambridge University Press, 1996, Chapter VII, Corollary 3).
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal BigOperators
open BGW.Probability.RealWalk

namespace BGW.StableTrees

private lemma exists_residue_cell {d ℓ n : ℕ} (hd : 0 < d) (hn : 0 < n) {t : ℝ}
    (ht : 0 ≤ t) : ∃ k : ℕ, (d : ℤ) ∣ (k : ℤ) - ℓ ∧
      t ∈ Ioc ((k : ℝ) / n - d / n) ((k : ℝ) / n) := by
  have _hd := hd  -- keeps the hypothesis used (unused-variable linter)
  let z : ℤ := ⌈((n : ℝ) * t - ℓ) / d⌉
  let kz : ℤ := ℓ + d * z
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hzlo : ((n : ℝ) * t - ℓ) / d ≤ (z : ℝ) := Int.le_ceil _
  have hzhi : (z : ℝ) < ((n : ℝ) * t - ℓ) / d + 1 := Int.ceil_lt_add_one _
  have hlo : t ≤ (kz : ℝ) / n := by
    dsimp [kz]
    rw [Int.cast_add, Int.cast_mul, Int.cast_natCast, Int.cast_natCast]
    rw [le_div_iff₀ hnR]
    rw [div_le_iff₀ hdR] at hzlo
    nlinarith
  have hhi : (kz : ℝ) / n < t + d / n := by
    dsimp [kz]
    rw [Int.cast_add, Int.cast_mul, Int.cast_natCast, Int.cast_natCast]
    rw [div_lt_iff₀ hnR]
    have hzmul := mul_lt_mul_of_pos_right hzhi hdR
    rw [add_mul, div_mul_cancel₀ _ hdR.ne'] at hzmul
    have hrewrite : (t + (d : ℝ) / n) * n = t * n + d := by
      field_simp
    rw [hrewrite]
    nlinarith
  have hkz : 0 ≤ kz := by
    by_contra H
    have hkz' : kz < 0 := lt_of_not_ge H
    have hkzR : (kz : ℝ) < 0 := by exact_mod_cast hkz'
    have : (kz : ℝ) / n < 0 := div_neg_of_neg_of_pos hkzR hnR
    linarith
  let k : ℕ := kz.toNat
  have hk : (k : ℤ) = kz := Int.toNat_of_nonneg hkz
  refine ⟨k, ?_, ?_⟩
  · rw [hk]
    exact ⟨z, by dsimp [kz]; ring⟩
  · have hkR : (k : ℝ) = (kz : ℝ) := by exact_mod_cast hk
    rw [hkR]
    exact ⟨by linarith [hhi], hlo⟩

private lemma progression_cells_disjoint {d : ℕ} (hd : 0 < d) (ℓ n : ℕ) :
    Pairwise (Function.onFun Disjoint (fun k : ℕ =>
      if (d : ℤ) ∣ (k : ℤ) - ℓ then
        Ioc ((k : ℝ) / n - d / n) ((k : ℝ) / n) else (∅ : Set ℝ))) := by
  have _hd := hd  -- keeps the hypothesis used (unused-variable linter)
  intro i j hij
  wlog hlt : i < j generalizing i j
  · exact (this hij.symm (lt_of_le_of_ne (le_of_not_gt hlt) hij.symm)).symm
  simp only [Function.onFun]
  split_ifs with hi hj
  · have hdiv : (d : ℤ) ∣ (j : ℤ) - i := by
      obtain ⟨c, hc⟩ := hi
      obtain ⟨e, he⟩ := hj
      exact ⟨e - c, by linear_combination he - hc⟩
    have hpos : 0 < (j : ℤ) - i := by
      have : (i : ℤ) < j := by exact_mod_cast hlt
      linarith
    have hle : (d : ℤ) ≤ (j : ℤ) - i := Int.le_of_dvd hpos hdiv
    have hleR : (d : ℝ) ≤ (j : ℝ) - i := by exact_mod_cast hle
    rw [Set.disjoint_left]
    intro t hti htj
    have hnNat : 0 < n := by
      by_contra H
      have hn0 : n = 0 := Nat.eq_zero_of_not_pos H
      subst n
      norm_num at hti
    have hn : 0 < (n : ℝ) := by exact_mod_cast hnNat
    have hid : (i : ℝ) + d ≤ j := by linarith
    have hgrid : (i : ℝ) / n ≤ (j : ℝ) / n - d / n := by
      rw [le_sub_iff_add_le, ← add_div]
      exact (div_le_div_iff_of_pos_right hn).2 hid
    linarith [hti.2, htj.1]
  all_goals simp

/-- **Arithmetic-progression Riemann sum** (the lattice factor cancels): for continuous `g` with
compact support inside `(0, ∞)`, `d ≥ 1`, and any integers `ℓ n`,
`(d/n) Σ_{k ≥ 0, d ∣ k - ℓ n} g(k/n) → ∫ g`. -/
theorem tendsto_progression_riemann_sum {d : ℕ} (hd : 0 < d) (ℓ : ℕ → ℕ) {g : ℝ → ℝ}
    (hg : Continuous g) (hsupp : HasCompactSupport g) (hpos : tsupport g ⊆ Ioi 0) :
    Tendsto (fun n : ℕ => ∑' k : ℕ,
        if (d : ℤ) ∣ (k : ℤ) - ℓ n then (d : ℝ) / n * g ((k : ℝ) / n) else 0)
      atTop (𝓝 (∫ s, g s)) := by
  have hgint : Integrable g := hg.integrable_of_hasCompactSupport hsupp
  have hzero : ∀ t, t ≤ 0 → g t = 0 := by
    intro t ht
    apply image_eq_zero_of_notMem_tsupport
    intro hmem
    exact (not_le_of_gt (hpos hmem)) ht
  have hu : UniformContinuous g :=
    hg.uniformContinuous_of_tendsto_cocompact hsupp.is_zero_at_infty
  obtain ⟨R₀, hR₀⟩ := hsupp.exists_bound_of_continuousOn continuousOn_id
  let R := max R₀ 0
  have hRnonneg : 0 ≤ R := le_max_right _ _
  have hR (t : ℝ) (ht : t ∈ tsupport g) : |t| ≤ R :=
    (hR₀ t ht).trans (le_max_left _ _)
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  let η := ε / (d * R + d + 4)
  have hη : 0 < η := div_pos hε (by
    have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
    nlinarith [mul_nonneg hdR.le hRnonneg])
  obtain ⟨δ, hδ, huc⟩ := Metric.uniformContinuous_iff.1 hu η hη
  have hde : ∀ᶠ n : ℕ in atTop, (d : ℝ) / n < δ ∧ (d : ℝ) / n < 1 ∧ 1 ≤ n := by
    have htop : Tendsto (fun n : ℕ => (d : ℝ) / n) atTop (𝓝 0) :=
      tendsto_const_div_atTop_nhds_zero_nat (d : ℝ)
    filter_upwards [htop.eventually (gt_mem_nhds hδ), htop.eventually (gt_mem_nhds zero_lt_one),
      eventually_ge_atTop 1] with n h1 h2 h3
    exact ⟨h1, h2, h3⟩
  obtain ⟨J, hJ⟩ := eventually_atTop.1 hde
  refine ⟨J, fun n hnN => ?_⟩
  have hn := hJ n hnN
  have hnpos : 0 < n := hn.2.2
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hnpos
  let N := ⌈(n : ℝ) * R + d⌉₊
  let E : ℕ → Set ℝ := fun k => if (d : ℤ) ∣ (k : ℤ) - ℓ n then
    Ioc ((k : ℝ) / n - d / n) ((k : ℝ) / n) else ∅
  let F : ℕ → ℝ := fun k => if (d : ℤ) ∣ (k : ℤ) - ℓ n then
    (d : ℝ) / n * g ((k : ℝ) / n) else 0
  let I : ℕ → ℝ := fun k => ∫ t in E k, g t
  let M : ℕ → ℝ := fun k => if k ≤ N then η * ((d : ℝ) / n) else 0
  have hcut {k : ℕ} (hk : N < k) : F k = 0 ∧ I k = 0 := by
    have hN : (n : ℝ) * R + d ≤ (N : ℝ) := Nat.le_ceil _
    have hkR : (n : ℝ) * R + d < (k : ℝ) :=
      hN.trans_lt (by exact_mod_cast hk)
    have hlower : R < (k : ℝ) / n - d / n := by
      have hkdiv := (div_lt_div_iff_of_pos_right hnR).2 hkR
      rw [add_div, show (n : ℝ) * R / n = R by field_simp] at hkdiv
      exact (lt_sub_iff_add_lt).2 hkdiv
    have hgzero {t : ℝ} (ht : R < t) : g t = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      intro hmem
      have := hR t hmem
      have htpos : 0 < t := hRnonneg.trans_lt ht
      rw [abs_of_pos htpos] at this
      linarith
    have hmesh : 0 ≤ (d : ℝ) / n := by positivity
    have hksample : R + (d : ℝ) / n < (k : ℝ) / n := (lt_sub_iff_add_lt).1 hlower
    have hsample : g ((k : ℝ) / n) = 0 := hgzero ((le_add_of_nonneg_right hmesh).trans_lt hksample)
    constructor
    · dsimp [F]
      simp [hsample]
    · dsimp [I, E]
      split_ifs
      · apply setIntegral_eq_zero_of_forall_eq_zero
        intro t ht
        exact hgzero (hlower.trans ht.1)
      · simp
  have hFs : Summable F := by
    apply summable_of_hasFiniteSupport
    apply (Set.finite_le_nat N).subset
    intro k hk
    by_contra hkn
    have := (hcut (lt_of_not_ge hkn)).1
    exact hk this
  have hMs : Summable M := by
    apply summable_of_hasFiniteSupport
    apply (Set.finite_le_nat N).subset
    intro k hk
    by_contra hkn
    have hkN : ¬k ≤ N := hkn
    simp [M, hkN] at hk
  have hm : ∀ k, MeasurableSet (E k) := by
    intro k
    dsimp [E]
    split_ifs <;> measurability
  have hdis : Pairwise (Function.onFun Disjoint E) := progression_cells_disjoint hd (ℓ n) n
  have hcover : Ioi 0 ⊆ ⋃ k, E k := by
    intro t ht
    obtain ⟨k, hk, hcell⟩ := exists_residue_cell hd hnpos ht.le
    exact Set.mem_iUnion.mpr ⟨k, by
      dsimp [E]
      split_ifs with H
      · exact hcell
      · exact (H hk).elim⟩
  have hUint : ∫ t in ⋃ k, E k, g t = ∫ t, g t := by
    rw [← integral_indicator (MeasurableSet.iUnion hm)]
    apply integral_congr_ae
    filter_upwards [] with t
    by_cases ht : t ∈ ⋃ k, E k
    · rw [Set.indicator_of_mem ht]
    · have hz : g t = 0 := by
        by_cases ht0 : t ≤ 0
        · exact hzero t ht0
        · exact absurd (hcover (lt_of_not_ge ht0)) ht
      rw [Set.indicator_of_notMem ht, hz]
  have hI : HasSum I (∫ t, g t) := by
    rw [← hUint]
    exact hasSum_integral_iUnion hm hdis hgint.integrableOn
  have hbound (k : ℕ) : ‖F k - I k‖ ≤ M k := by
    by_cases hk : k ≤ N
    · dsimp [M]
      simp only [hk, ↓reduceIte]
      dsimp [F, I, E]
      split_ifs with hdiv
      · have hlen : (k : ℝ) / n - ((k : ℝ) / n - d / n) = d / n := by ring
        have hconst : (d : ℝ) / n * g ((k : ℝ) / n) =
            ∫ _t in Ioc ((k : ℝ) / n - d / n) ((k : ℝ) / n), g ((k : ℝ) / n) := by
          rw [setIntegral_const, measureReal_def, Real.volume_Ioc, hlen,
            ENNReal.toReal_ofReal (by positivity), smul_eq_mul]
        rw [hconst, ← integral_sub
          (integrableOn_const (measure_Ioc_lt_top (μ := (volume : Measure ℝ))).ne)
          hgint.integrableOn]
        have hnorm := norm_setIntegral_le_of_norm_le_const
          (s := Ioc ((k : ℝ) / n - d / n) ((k : ℝ) / n)) (f := fun t =>
            g ((k : ℝ) / n) - g t) (C := η) (measure_Ioc_lt_top (μ := (volume : Measure ℝ)))
          (fun t ht => ?_)
        · refine hnorm.trans_eq ?_
          rw [measureReal_def, Real.volume_Ioc, hlen,
            ENNReal.toReal_ofReal (by positivity)]
        · have hdist : dist ((k : ℝ) / n) t < δ := by
            rw [Real.dist_eq]
            rw [abs_sub_lt_iff]
            constructor <;> linarith [ht.1, ht.2, hn.1]
          simpa [Real.dist_eq, abs_sub_comm] using (huc hdist).le
      · simp
        positivity
    · dsimp [M]
      simp only [hk, ↓reduceIte]
      obtain ⟨hF0, hI0⟩ := hcut (lt_of_not_ge hk)
      simp [hF0, hI0]
  have hM_eval : ∑' k, M k = (N + 1 : ℕ) * (η * ((d : ℝ) / n)) := by
    rw [tsum_eq_sum (s := Finset.range (N + 1))]
    · calc
        ∑ k ∈ Finset.range (N + 1), M k =
            ∑ _k ∈ Finset.range (N + 1), η * ((d : ℝ) / n) := by
          apply Finset.sum_congr rfl
          intro k hk
          have hkN := Nat.le_of_lt_succ (Finset.mem_range.1 hk)
          simp [M, hkN]
        _ = (N + 1 : ℕ) * (η * ((d : ℝ) / n)) := by simp
    · intro k hk
      have hkn : N < k := by
        simp only [Finset.mem_range, not_lt] at hk
        omega
      dsimp [M]
      simp [not_le.mpr hkn]
  have herr := (hFs.hasSum.sub hI).norm_le_of_bounded
    (hM_eval ▸ hMs.hasSum) hbound
  have hN_upper : ((N + 1 : ℕ) : ℝ) * ((d : ℝ) / n) ≤ d * R + d + 2 := by
    have hNlt : (N : ℝ) < (n : ℝ) * R + d + 1 :=
      Nat.ceil_lt_add_one (by positivity)
    have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
    have hm := mul_lt_mul_of_pos_right hNlt hdR
    simp only [add_mul, one_mul] at hm
    rw [show ((N + 1 : ℕ) : ℝ) * ((d : ℝ) / n) =
      (((N : ℝ) + 1) * d) / n by push_cast; ring]
    apply (div_le_iff₀ hnR).2
    have hdn : (d : ℝ) ≤ n := (div_le_one hnR).1 hn.2.1.le
    have hdd : (d : ℝ) * d ≤ n * d := mul_le_mul_of_nonneg_right hdn hdR.le
    have hlt : ((N : ℝ) + 1) * d < n * R * d + n * d + 2 * d := by
      calc
        ((N : ℝ) + 1) * d = N * d + d := by ring
        _ < n * R * d + d * d + 2 * d := by linarith
        _ ≤ n * R * d + n * d + 2 * d := by linarith
    have hle : n * R * d + n * d + 2 * d ≤ (d * R + d + 2) * n := by
      calc
        n * R * d + n * d + 2 * d ≤ n * R * d + n * d + 2 * n := by linarith
        _ = (d * R + d + 2) * n := by ring
    exact hlt.le.trans hle
  rw [Real.dist_eq]
  change |∑' k, F k - ∫ t, g t| < ε
  rw [← Real.norm_eq_abs]
  apply herr.trans_lt
  have hnonneg : 0 ≤ (N + 1 : ℕ) * (η * ((d : ℝ) / n)) := by positivity
  have hmul : ((N + 1 : ℕ) : ℝ) * (η * ((d : ℝ) / n)) ≤ η * (d * R + d + 2) := by
    calc
      ((N + 1 : ℕ) : ℝ) * (η * ((d : ℝ) / n)) =
          η * (((N + 1 : ℕ) : ℝ) * ((d : ℝ) / n)) := by ring
      _ ≤ η * (d * R + d + 2) := mul_le_mul_of_nonneg_left hN_upper hη.le
  refine hmul.trans_lt ?_
  dsimp [η]
  have hdpos : 0 < (d : ℝ) := by exact_mod_cast hd
  have hdenpos : 0 < d * R + d + 4 := by nlinarith [mul_nonneg hdpos.le hRnonneg]
  rw [div_mul_eq_mul_div]
  apply (div_lt_iff₀ hdenpos).2
  nlinarith

end BGW.StableTrees
