/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.ForestLocalLimitAsymptotics
public import BGW.StableTrees.ForestLocalLimitLocal
public import BGW.StableTrees.ForestLocalLimitTail

/-!
# Exact-prefix forest weights

Compactness combines the periodic local limit, the inclusive tail limit and the
admissible tree tail-to-mass ratio. The two lattice factors cancel.

Reference: J.-F. Le Gall, *Random trees and applications*, Probab. Surveys 2 (2005),
Section 1.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped Topology ENNReal NNReal

namespace BGW.StableTrees

/-- **Exact-prefix RN weights, uniform on accessible prefixes** (`d ∣ (n-m) - j`, where
`m = ⌊a n⌋`, `j = W_m + 1`, `ε ≤ j/B_n ≤ M`):
`R_n(m,j) - gammaA θ a (j/B_n) → 0` uniformly, along admissible `n`. -/
theorem exactPrefixWeight_uniform {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ} (h : StableDomain μ θ B)
    {a ε M η : ℝ} (ha : a ∈ Set.Ioo (0 : ℝ) 1) (hε : 0 < ε) (hεM : ε ≤ M) (hη : 0 < η) :
    ∀ᶠ n : ℕ in atTop, Admissible μ n → ∀ j : ℕ,
      ε ≤ (j : ℝ) / B n → (j : ℝ) / B n ≤ M →
      ((Scalar.latticeSpan μ : ℤ) ∣ (n : ℤ) - (⌊a * n⌋₊ : ℕ) - j) →
      |exactPrefixWeight μ n ⌊a * n⌋₊ j - gammaA θ a ((j : ℝ) / B n)| ≤ η := by
  -- `hεM` is part of the stated interface; this proof does not use it.
  have _hεM := hεM
  by_contra H
  rw [eventually_atTop] at H
  push Not at H
  choose q hq hadm j hjε hjM hdiv herr using fun n => H (n + 1)
  have hqtop : Tendsto q atTop atTop := tendsto_atTop_mono
    (fun n => (Nat.le_succ n).trans (hq n)) tendsto_id
  obtain ⟨σ, _hσ, hqσ⟩ := strictMono_subseq_of_tendsto_atTop hqtop
  have hjmem (k : ℕ) : (j (σ k) : ℝ) / B (q (σ k)) ∈ Icc ε M :=
    ⟨hjε (σ k), hjM (σ k)⟩
  obtain ⟨x, hx, φ, hφ, hxlim⟩ := isCompact_Icc.tendsto_subseq hjmem
  let Q : ℕ → ℕ := fun k => q (σ (φ k))
  let J : ℕ → ℕ := fun k => j (σ (φ k))
  let R : ℕ → ℕ := fun k => Q k - ⌊a * Q k⌋₊
  have hQmono : StrictMono Q := hqσ.comp hφ
  have hQtop := hQmono.tendsto_atTop
  have hQadm (k : ℕ) : Admissible μ (Q k) := hadm (σ (φ k))
  have hxpos : 0 < x := hε.trans_le hx.1
  have hxlim' : Tendsto (fun k => (J k : ℝ) / B (Q k)) atTop (𝓝 x) := by
    simpa only [J, Q, Function.comp_def] using hxlim
  have hfloor : Tendsto (fun n : ℕ => (⌊a * n⌋₊ : ℝ) / n) atTop (𝓝 a) := by
    have ht := (tendsto_nat_floor_div_atTop.comp
      (tendsto_natCast_atTop_atTop.const_mul_atTop ha.1)).mul_const a
    rw [one_mul] at ht
    refine ht.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hnR : (n : ℝ) ≠ 0 := by positivity
    dsimp only [Function.comp_apply]
    field_simp [ha.1.ne']
  have hfloorle (n : ℕ) : ⌊a * n⌋₊ ≤ n := by
    apply Nat.floor_le_of_le
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    nlinarith [ha.2]
  have hRlim : Tendsto (fun k => (R k : ℝ) / Q k) atTop (𝓝 (1 - a)) := by
    have ht := (tendsto_const_nhds (x := (1 : ℝ))).sub (hfloor.comp hQtop)
    refine ht.congr' ?_
    filter_upwards [hQtop.eventually (eventually_ge_atTop 1)] with k hk
    have hkR : (Q k : ℝ) ≠ 0 := by positivity
    change 1 - (⌊a * Q k⌋₊ : ℝ) / Q k = (R k : ℝ) / Q k
    dsimp only [R]
    rw [Nat.cast_sub (hfloorle _)]
    field_simp
  have htime : 0 < 1 - a := sub_pos.2 ha.2
  have hlocal := forestMass_local_seq h htime hxlim' hQtop hRlim
    (fun k => by
      dsimp only [R, Q, J]
      rw [Nat.cast_sub (hfloorle _)]
      exact hdiv (σ (φ k)))
  have hqcont : ContinuousAt (fun z : ℝ × ℝ => qKernel θ z.1 z.2) (1 - a, x) :=
    (continuousOn_qKernel h.alpha_mem).continuousAt
      ((isOpen_Ioi.preimage continuous_fst).mem_nhds htime)
  have hkern := hqcont.tendsto.comp (hRlim.prodMk_nhds hxlim')
  have hmass : Tendsto (fun k => (Q k : ℝ) * forestMass μ (J k) (R k)) atTop
      (𝓝 (Scalar.latticeSpan μ * qKernel θ (1 - a) x)) := by
    have ht := hlocal.add (hkern.const_mul (Scalar.latticeSpan μ : ℝ))
    simpa only [Function.comp_apply, sub_add_cancel, zero_add] using ht
  have htail := forestTail_limit_seq h hQmono hxpos htime hxlim' hRlim
  have hratio := tailExactRatio_tendsto h hQtop hQadm
  have hG := (sizeTailKernel_pos h.alpha_mem htime hxpos).ne'
  have hd : (Scalar.latticeSpan μ : ℝ) ≠ 0 := by
    exact_mod_cast (Scalar.latticeSpan_pos h.critical h.nondegenerate).ne'
  have hweight : Tendsto (fun k => exactPrefixWeight μ (Q k) ⌊a * Q k⌋₊ (J k))
      atTop (𝓝 (gammaA θ a x)) := by
    have ht := (hmass.div htail hG).mul hratio
    have heq : (Scalar.latticeSpan μ * qKernel θ (1 - a) x /
        sizeTailKernel θ (1 - a) x) * (θ / (Scalar.latticeSpan μ : ℝ)) =
        gammaA θ a x := by
      unfold gammaA
      field_simp
    rw [heq] at ht
    refine ht.congr' ?_
    filter_upwards [hQtop.eventually (eventually_ge_atTop 1)] with k hk
    have hQ : (Q k : ℝ) ≠ 0 := by positivity
    change ((Q k : ℝ) * forestMass μ (J k) (R k) / forestTail μ (J k) (R k)) *
      (forestTail μ 1 (Q k) / ((Q k : ℝ) * forestMass μ 1 (Q k))) =
      forestMass μ (J k) (R k) / forestTail μ (J k) (R k) *
        (forestTail μ 1 (Q k) / forestMass μ 1 (Q k))
    field_simp [hQ]
  have hgcont : ContinuousAt (fun z : ℝ × ℝ => gammaA θ z.1 z.2) (a, x) :=
    (continuousOn_gammaA h.alpha_mem).continuousAt
      ((isOpen_Iio.preimage continuous_fst).inter (isOpen_Ioi.preimage continuous_snd)
        |>.mem_nhds ⟨ha.2, hxpos⟩)
  have hgamma := hgcont.tendsto.comp (tendsto_const_nhds.prodMk_nhds hxlim')
  have ht := hweight.sub hgamma
  rw [sub_self] at ht
  obtain ⟨K, hK⟩ := Metric.tendsto_atTop.1 ht η hη
  have hs := hK K le_rfl
  rw [Real.dist_eq, sub_zero] at hs
  exact (not_lt_of_ge (herr (σ (φ K))).le) hs

end BGW.StableTrees
