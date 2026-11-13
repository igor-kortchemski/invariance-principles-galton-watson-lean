/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.DiscreteBridgeDensity
public import BGW.StableTrees.BridgePrefix

/-!
# Moving endpoint local limits for discrete bridges

The lattice local limit theorem applies to signed endpoints. The lattice factors
in the remaining-walk numerator and admissible bridge denominator cancel.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal Classical

namespace BGW.StableTrees.DiscreteBridge

open BGW BGW.Skorokhod BGW.Probability.RealWalk

/-- Every admissible size has a strictly positive bridge endpoint probability. -/
theorem walkProb_neg_one_pos {μ : PMF ℕ} {n : ℕ} (hn : Admissible μ n) :
    0 < walkProb μ n (-1) := by
  have hn1 : 1 ≤ n := by
    by_contra hn1
    have : n = 0 := by omega
    subst n
    exact hn (by simp [LocallyFinite.sizeEvent_zero])
  have hmass := (DiscreteForest.admissible_iff_forestWeight_pos μ n).mp hn
  have heq := Scalar.natCast_mul_forestWeight_toReal μ (ℓ := 1) le_rfl n
  norm_num only [Nat.cast_one, one_mul] at heq
  rw [← heq]
  exact mul_pos (show (0 : ℝ) < n by exact_mod_cast hn1) hmass

/-- A sequential local limit for arbitrary signed endpoints on the reachable lattice. -/
theorem walkLocalLimit_seq {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ} (h : StableDomain μ θ B)
    {q : ℕ → ℕ} (hq : Tendsto q atTop atTop) {z : ℕ → ℤ} {x : ℝ}
    (hz : Tendsto (fun k => (z k : ℝ) / B (q k)) atTop (𝓝 x))
    (hdiv : ∀ᶠ k in atTop, (Scalar.latticeSpan μ : ℤ) ∣ z k + q k) :
    Tendsto (fun k => B (q k) * walkProb μ (q k) (z k)) atTop
      (𝓝 (Scalar.latticeSpan μ * Scalar.stableDensity θ x)) := by
  have herr : Tendsto (fun k => B (q k) * walkProb μ (q k) (z k) -
      Scalar.latticeSpan μ * Scalar.stableDensity θ ((z k : ℝ) / B (q k))) atTop (𝓝 0) := by
    apply Metric.tendsto_atTop.mpr
    intro ε hε
    obtain ⟨N, hN⟩ := Scalar.localLimit h (half_pos hε)
    rw [← eventually_atTop]
    filter_upwards [hq.eventually (eventually_ge_atTop N), hdiv] with k hk hdk
    rw [Real.dist_eq, sub_zero]
    exact (hN (q k) hk (z k) hdk).trans_lt (half_lt_self hε)
  have hdens := ((Scalar.continuous_stableDensity h.alpha_mem).tendsto x).comp hz
  have ht := herr.add (hdens.const_mul (Scalar.latticeSpan μ : ℝ))
  simpa only [Function.comp_def, sub_add_cancel, zero_add] using ht

/-- Regular variation compares the full and remaining normings at a fixed strict prefix. -/
theorem bridgeRemaining_norming_ratio {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ}
    (h : StableDomain μ θ B) (a : ℝ≥0) (ha : a ∈ Ioo (0 : ℝ≥0) 1) :
    Tendsto (fun n : ℕ => B n / B (n - ⌊(a : ℝ) * n⌋₊)) atTop
      (𝓝 ((1 - (a : ℝ)) ^ (-(1 / θ)))) := by
  have ha1 : (a : ℝ) < 1 := by exact_mod_cast ha.2
  exact Scalar.tendsto_div_of_tendsto_div h (sub_pos.mpr ha1) (bridgeRemaining_ratio a ha)

/-- The remaining time tends to infinity along every unbounded sequence of full sizes. -/
theorem bridgeRemaining_atTop (a : ℝ≥0) (ha : a ∈ Ioo (0 : ℝ≥0) 1)
    {q : ℕ → ℕ} (hq : Tendsto q atTop atTop) :
    Tendsto (fun k => q k - ⌊(a : ℝ) * q k⌋₊) atTop atTop := by
  have ha1 : (a : ℝ) < 1 := by exact_mod_cast ha.2
  have ht := Tendsto.pos_mul_atTop (sub_pos.mpr ha1)
    ((bridgeRemaining_ratio a ha).comp hq) (tendsto_natCast_atTop_atTop.comp hq)
  suffices Tendsto (fun k => ((q k - ⌊(a : ℝ) * q k⌋₊ : ℕ) : ℝ)) atTop atTop by
    exact tendsto_natCast_atTop_iff.mp this
  refine ht.congr' ?_
  filter_upwards [hq.eventually (eventually_ge_atTop 1)] with k hk
  have hkR : (q k : ℝ) ≠ 0 := by positivity
  exact div_mul_cancel₀ _ hkR

/-- Ratio limit for signed remaining endpoints, with their lattice compatibility explicit. -/
theorem bridgeRatio_tendsto {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ} (h : StableDomain μ θ B)
    {q : ℕ → ℕ} (hqtop : Tendsto q atTop atTop) (hq : ∀ k, Admissible μ (q k))
    (a : ℝ≥0) (ha : a ∈ Ioo (0 : ℝ≥0) 1) {z : ℕ → ℤ} {x : ℝ}
    (hz : Tendsto (fun k => (z k : ℝ) / B (q k)) atTop (𝓝 x))
    (hdiv : ∀ᶠ k in atTop, (Scalar.latticeSpan μ : ℤ) ∣
      z k + (q k - ⌊(a : ℝ) * q k⌋₊ : ℕ)) :
    Tendsto (fun k => walkProb μ ((q k - ⌊(a : ℝ) * q k⌋₊ : ℕ) : ℤ) (z k) /
      walkProb μ (q k) (-1)) atTop
      (𝓝 (stableDensityAt θ (1 - (a : ℝ)) x / Scalar.stableDensity θ 0)) := by
  let R := fun k => q k - ⌊(a : ℝ) * q k⌋₊
  let L := (1 - (a : ℝ)) ^ (-(1 / θ))
  have hRtop : Tendsto R atTop atTop := bridgeRemaining_atTop a ha hqtop
  have hrat : Tendsto (fun k => B (q k) / B (R k)) atTop (𝓝 L) :=
    (bridgeRemaining_norming_ratio h a ha).comp hqtop
  have harg : Tendsto (fun k => (z k : ℝ) / B (R k)) atTop (𝓝 (x * L)) := by
    refine (hz.mul hrat).congr' ?_
    filter_upwards [hqtop.eventually (eventually_ge_atTop 1)] with k hk
    have hB := (h.pos (q k) hk).ne'
    field_simp
  have hnum := walkLocalLimit_seq h hRtop harg hdiv
  have hBtop := (Scalar.tendsto_atTop h).comp hqtop
  have harg0 : Tendsto (fun k => ((-1 : ℤ) : ℝ) / B (q k)) atTop (𝓝 0) :=
    hBtop.const_div_atTop _
  have hdiv0 : ∀ᶠ k in atTop, (Scalar.latticeSpan μ : ℤ) ∣ (-1 : ℤ) + q k := by
    apply Eventually.of_forall
    intro k
    by_contra hnot
    have hzero := Scalar.walkProb_eq_zero_of_not_dvd h hnot
    have hpos := walkProb_neg_one_pos (hq k)
    rw [hzero] at hpos
    exact (lt_irrefl 0) hpos
  have hden := walkLocalLimit_seq h hqtop harg0 hdiv0
  have hd : (Scalar.latticeSpan μ : ℝ) ≠ 0 := by
    exact_mod_cast (Scalar.latticeSpan_pos h.critical h.nondegenerate).ne'
  have hp0 := (Scalar.stableDensity_zero_pos h.alpha_mem).ne'
  have ht := (hrat.mul hnum).div hden (mul_ne_zero hd hp0)
  have heq : L * (Scalar.latticeSpan μ * Scalar.stableDensity θ (x * L)) /
      (Scalar.latticeSpan μ * Scalar.stableDensity θ 0) =
      stableDensityAt θ (1 - (a : ℝ)) x / Scalar.stableDensity θ 0 := by
    rw [stableDensityAt]
    dsimp [L]
    field_simp
  rw [heq] at ht
  refine ht.congr' ?_
  filter_upwards [hRtop.eventually (eventually_ge_atTop 1),
    hqtop.eventually (eventually_ge_atTop 1)] with k hkR hkq
  have hBR := (h.pos (R k) hkR).ne'
  have hBQ := (h.pos (q k) hkq).ne'
  change (B (q k) / B (R k) * (B (R k) * walkProb μ (R k) (z k))) /
    (B (q k) * walkProb μ (q k) (-1)) = walkProb μ (R k) (z k) / walkProb μ (q k) (-1)
  field_simp

end BGW.StableTrees.DiscreteBridge
