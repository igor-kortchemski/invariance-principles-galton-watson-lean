/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.ForestLocalLimitDefs
import BGW.StableTrees.StableKendallLocal

/-!
# Compact uniform local limits for forest masses

Kemperman's identity and the lattice local limit theorem give the sequential limit,
including levels tending to zero. Compactness then gives the uniform assertion.

Reference: J.-F. Le Gall, *Random trees and applications*, Probab. Surveys 2 (2005),
Section 1.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace BGW.StableTrees

private theorem ratio_seq {ρ : ℝ} {a : ℕ → ℝ}
    (hrv : RegularlyVaryingSeq ρ a) (hmono : Monotone a)
    (hpos : ∀ n : ℕ, 1 ≤ n → 0 < a n) {q k : ℕ → ℕ}
    (hq : Tendsto q atTop atTop) {c : ℝ} (hc : 0 < c)
    (hk : Tendsto (fun n : ℕ => (k n : ℝ) / q n) atTop (𝓝 c)) :
    Tendsto (fun n : ℕ => a (k n) / a (q n)) atTop (𝓝 (c ^ ρ)) := by
  have hcont : Tendsto (fun x : ℝ => x ^ ρ) (𝓝 c) (𝓝 (c ^ ρ)) :=
    (Real.continuousAt_rpow_const c ρ (Or.inl hc.ne')).tendsto
  rw [tendsto_order]
  refine ⟨fun l hl => ?_, fun u hu => ?_⟩
  · have h1 : ∀ᶠ x in 𝓝[<] c, l < x ^ ρ :=
      (hcont.mono_left nhdsWithin_le_nhds).eventually (lt_mem_nhds hl)
    have h2 : ∀ᶠ x in 𝓝[<] c, 0 < x :=
      nhdsWithin_le_nhds (lt_mem_nhds hc)
    have h3 : ∀ᶠ x in 𝓝[<] c, x < c := self_mem_nhdsWithin
    obtain ⟨c', hc'l, hc'0, hc'c⟩ := (h1.and (h2.and h3)).exists
    have e1 := ((hrv c' hc'0).comp hq).eventually (lt_mem_nhds hc'l)
    have e2 := hk.eventually (lt_mem_nhds hc'c)
    filter_upwards [e1, e2, hq.eventually (eventually_ge_atTop 1)] with n h1 h2 hn1
    have han := hpos (q n) hn1
    have hnR : (0 : ℝ) < q n := by exact_mod_cast hn1
    have hfl : ⌊c' * q n⌋₊ ≤ k n := by
      apply Nat.floor_le_of_le
      have := (lt_div_iff₀ hnR).1 h2
      linarith
    calc l < a ⌊c' * q n⌋₊ / a (q n) := h1
      _ ≤ a (k n) / a (q n) := div_le_div_of_nonneg_right (hmono hfl) han.le
  · have h1 : ∀ᶠ x in 𝓝[>] c, x ^ ρ < u :=
      (hcont.mono_left nhdsWithin_le_nhds).eventually (gt_mem_nhds hu)
    have h3 : ∀ᶠ x in 𝓝[>] c, c < x := self_mem_nhdsWithin
    obtain ⟨c'', hc''u, hcc''⟩ := (h1.and h3).exists
    have hc''0 : 0 < c'' := hc.trans hcc''
    have e1 := ((hrv c'' hc''0).comp hq).eventually (gt_mem_nhds hc''u)
    have e2 := hk.eventually (gt_mem_nhds hcc'')
    filter_upwards [e1, e2, hq.eventually (eventually_ge_atTop 1)] with n h1 h2 hn1
    have han := hpos (q n) hn1
    have hnR : (0 : ℝ) < q n := by exact_mod_cast hn1
    have hfl : k n ≤ ⌊c'' * q n⌋₊ := by
      apply Nat.le_floor
      have := (div_lt_iff₀ hnR).1 h2
      linarith
    calc a (k n) / a (q n) ≤ a ⌊c'' * q n⌋₊ / a (q n) :=
          div_le_div_of_nonneg_right (hmono hfl) han.le
      _ < u := h1

/-- Sequential periodic local limit, allowing the rescaled forest level to tend to zero. -/
theorem forestMass_local_seq {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ}
    (h : StableDomain μ θ B) {x κ : ℝ} (hκ : 0 < κ) {ℓ q k : ℕ → ℕ}
    (hscale : Tendsto (fun j : ℕ => (ℓ j : ℝ) / B (q j)) atTop (𝓝 x))
    (hq : Tendsto q atTop atTop)
    (hk : Tendsto (fun j : ℕ => (k j : ℝ) / q j) atTop (𝓝 κ))
    (hdiv : ∀ j, (Scalar.latticeSpan μ : ℤ) ∣ (k j : ℤ) - ℓ j) :
    Tendsto (fun j : ℕ => (q j : ℝ) * forestMass μ (ℓ j) (k j) -
      Scalar.latticeSpan μ * qKernel θ ((k j : ℝ) / q j) ((ℓ j : ℝ) / B (q j)))
      atTop (𝓝 0) := by
  have hmtop : Tendsto k atTop atTop := by
    have h1 : Tendsto (fun j : ℕ => (k j : ℝ) / q j * q j) atTop atTop :=
      Tendsto.pos_mul_atTop hκ hk (tendsto_natCast_atTop_atTop.comp hq)
    have h2 : Tendsto (fun j : ℕ => (k j : ℝ)) atTop atTop := by
      refine h1.congr' ?_
      filter_upwards [hq.eventually (eventually_ne_atTop 0)] with j hj
      field_simp
    exact tendsto_natCast_atTop_iff.1 h2
  have hratio : Tendsto (fun j => B (q j) / B (k j)) atTop (𝓝 (κ ^ (-(1 / θ)))) :=
    by
      have hr := (ratio_seq (Scalar.regularlyVaryingSeq h) h.monotone h.pos hq hκ hk).inv₀
        (Real.rpow_pos_of_pos hκ _).ne'
      simpa only [inv_div, ← Real.rpow_neg hκ.le] using hr
  have harg : Tendsto (fun j => (ℓ j : ℝ) / B (k j)) atTop
      (𝓝 (x * κ ^ (-(1 / θ)))) := by
    have hb := hscale.mul hratio
    refine hb.congr' ?_
    filter_upwards [hq.eventually (eventually_ge_atTop 1),
      hmtop.eventually (eventually_ge_atTop 1)] with j hqj hkj
    have hBq := (h.pos (q j) hqj).ne'
    have hBk := (h.pos (k j) hkj).ne'
    field_simp
  have hden : Tendsto (fun j => B (k j) * walkProb μ (k j) (-(ℓ j : ℤ))) atTop
      (𝓝 (Scalar.latticeSpan μ * Scalar.stableDensity θ
        (-(x * κ ^ (-(1 / θ)))))) := by
    have hsmall : Tendsto (fun j => B (k j) * walkProb μ (k j) (-(ℓ j : ℤ)) -
        Scalar.latticeSpan μ * Scalar.stableDensity θ
          (((-(ℓ j : ℤ)) : ℝ) / B (k j))) atTop (𝓝 0) := by
      apply Metric.tendsto_atTop.mpr
      intro ε hε
      obtain ⟨N, hN⟩ := Scalar.localLimit h (half_pos hε)
      obtain ⟨J, hJ⟩ := eventually_atTop.1 (hmtop.eventually (eventually_ge_atTop N))
      refine ⟨J, fun j hj => ?_⟩
      have hkj := hJ j hj
      rw [Real.dist_eq, sub_zero]
      simpa only [Int.cast_neg, Int.cast_natCast] using (hN (k j) hkj (-(ℓ j : ℤ))
        (by simpa [sub_eq_add_neg, add_comm] using hdiv j)).trans_lt (half_lt_self_iff.mpr hε)
    have hdens : Tendsto (fun j => Scalar.stableDensity θ
        (((-(ℓ j : ℤ)) : ℝ) / B (k j))) atTop
        (𝓝 (Scalar.stableDensity θ (-(x * κ ^ (-(1 / θ)))))) := by
      apply (Scalar.continuous_stableDensity h.alpha_mem).continuousAt.tendsto.comp
      simpa only [Int.cast_neg, Int.cast_natCast, neg_div] using harg.neg
    have H := hsmall.add (hdens.const_mul (Scalar.latticeSpan μ : ℝ))
    simp only [zero_add] at H
    refine H.congr fun j => ?_
    ring
  have hfactor : Tendsto (fun j => (ℓ j : ℝ) /
      (((k j : ℝ) / q j) * B (k j))) atTop
      (𝓝 (x * κ ^ (-(1 / θ)) / κ)) := by
    refine (hscale.mul hratio).div hk hκ.ne' |>.congr' ?_
    filter_upwards [hq.eventually (eventually_ge_atTop 1),
      hmtop.eventually (eventually_ge_atTop 1)] with j hqj hkj
    have hBq := (h.pos (q j) hqj).ne'
    have hBk := (h.pos (k j) hkj).ne'
    have hq0 : (q j : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hqj)
    dsimp only [Function.comp_apply, Pi.div_apply]
    field_simp
  have hmass : Tendsto (fun j => (q j : ℝ) *
      forestMass μ (ℓ j) (k j)) atTop
      (𝓝 ((x * κ ^ (-(1 / θ)) / κ) * (Scalar.latticeSpan μ *
        Scalar.stableDensity θ (-(x * κ ^ (-(1 / θ))))))) := by
    refine (hfactor.mul hden).congr' ?_
    filter_upwards [hq.eventually (eventually_ge_atTop 1),
      hmtop.eventually (eventually_ge_atTop 1)] with j hqj hkj
    unfold forestMass
    rcases Nat.eq_zero_or_pos (ℓ j) with hz | hℓj
    · rw [hz, Scalar.forestWeight_zero_left, ite_eq_right (by omega)]
      simp
    rw [Scalar.forestWeight_toReal_eq μ hℓj hkj]
    have hq0 : (q j : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hqj)
    have hk0 : (k j : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hkj)
    have hBk := (h.pos (k j) hkj).ne'
    field_simp
  have hker : Tendsto (fun j => qKernel θ ((k j : ℝ) / q j)
      ((ℓ j : ℝ) / B (q j))) atTop (𝓝 (qKernel θ κ x)) := by
    have hc : ContinuousAt (fun z : ℝ × ℝ => qKernel θ z.1 z.2) (κ, x) :=
      (continuousOn_qKernel h.alpha_mem).continuousAt
        ((isOpen_Ioi.preimage continuous_fst).mem_nhds hκ)
    exact hc.tendsto.comp (hk.prodMk_nhds hscale)
  have H := hmass.sub (hker.const_mul (Scalar.latticeSpan μ : ℝ))
  convert H using 1
  simp only [qKernel, stableDensityAt]
  rw [show κ ^ (-1 / θ) * -x = -(x * κ ^ (-(1 / θ))) by rw [neg_div]; ring]
  congr 1
  field_simp
  ring

/-- **Forest local limit, compact-uniform, periodic.**  With `d = latticeSpan μ`, uniformly for
`r/n ∈ [a,b]`, `j/B_n ∈ [0,M]` and ONLY `d ∣ r - j`:
`n f_j(r) - d q_{r/n}(j/B_n) → 0` (absolute error; includes `j = 0`, where both vanish). -/
theorem forestLocalLimit_uniform {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ} (h : StableDomain μ θ B)
    {a b M : ℝ} (ha : 0 < a) (hab : a ≤ b) (hM : 0 ≤ M) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ n : ℕ in atTop, ∀ r j : ℕ, a * (n : ℝ) ≤ r → (r : ℝ) ≤ b * n → (j : ℝ) / B n ≤ M →
      ((Scalar.latticeSpan μ : ℤ) ∣ (r : ℤ) - j) →
      |(n : ℝ) * forestMass μ j r -
          Scalar.latticeSpan μ * qKernel θ ((r : ℝ) / n) ((j : ℝ) / B n)| ≤ η := by
  -- `hab` and `hM` are part of the stated interface; this proof does not use them.
  have _hab := hab
  have _hM := hM
  by_contra H
  rw [eventually_atTop] at H
  push Not at H
  choose q hq r ℓ hra hrb hℓM hdiv herr using fun n => H (n + 1)
  have hqpos (j : ℕ) : 1 ≤ q j := by have := hq j; omega
  have hqtop : Tendsto q atTop atTop := tendsto_atTop_mono
    (fun j => (Nat.le_succ j).trans (hq j)) tendsto_id
  have hrmem (j : ℕ) : (r j : ℝ) / q j ∈ Icc a b := by
    have hqR : 0 < (q j : ℝ) := by exact_mod_cast hqpos j
    exact ⟨(le_div_iff₀ hqR).2 (by simpa only [mul_comm] using hra j),
      (div_le_iff₀ hqR).2 (hrb j)⟩
  have hℓmem (j : ℕ) : (ℓ j : ℝ) / B (q j) ∈ Icc 0 M :=
    ⟨div_nonneg (Nat.cast_nonneg _) (h.pos _ (hqpos j)).le, hℓM j⟩
  obtain ⟨κ, hκ, φ, hφ, hκlim⟩ := isCompact_Icc.tendsto_subseq hrmem
  obtain ⟨x, _, ψ, hψ, hxlim⟩ := isCompact_Icc.tendsto_subseq (fun j => hℓmem (φ j))
  have hlim := forestMass_local_seq h (ha.trans_le hκ.1)
    (show Tendsto (fun j => (ℓ (φ (ψ j)) : ℝ) / B (q (φ (ψ j)))) atTop (𝓝 x) by
      simpa only [Function.comp_def] using hxlim)
    (hqtop.comp (hφ.tendsto_atTop.comp hψ.tendsto_atTop))
    (show Tendsto (fun j => (r (φ (ψ j)) : ℝ) / q (φ (ψ j))) atTop (𝓝 κ) by
      simpa only [Function.comp_def] using hκlim.comp hψ.tendsto_atTop)
    (fun j => hdiv (φ (ψ j)))
  obtain ⟨J, hJ⟩ := Metric.tendsto_atTop.1 hlim η hη
  have hsmall := hJ J le_rfl
  rw [Real.dist_eq, sub_zero] at hsmall
  exact (not_lt_of_ge (herr (φ (ψ J))).le) hsmall

end BGW.StableTrees
