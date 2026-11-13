/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.ForestLocalLimitDefs
import BGW.StableTrees.ForestLocalLimitResidue

/-!
# Tree-tail asymptotics and the tail-to-exact ratio

The lattice mass asymptotic is summed with the exact residue-class Karamata
constant. The resulting tree-tail asymptotic holds along all integers.

Reference: J.-F. Le Gall, *Random trees and applications*, Probab. Surveys 2 (2005),
Section 1.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped Topology ENNReal NNReal

namespace BGW.StableTrees

/-- **Tree tail asymptotics along ALL `n`:** `B_n G_1(n) → θ p₁(0)`.  No admissibility needed. -/
theorem treeTail_asymp {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ} (h : StableDomain μ θ B) :
    Tendsto (fun n : ℕ => B n * forestTail μ 1 n) atTop (𝓝 (θ * Scalar.stableDensity θ 0)) := by
  let d : ℕ := Scalar.latticeSpan μ
  let p : ℝ := Scalar.stableDensity θ 0
  let W : ℕ → ℕ → ℝ := fun n k =>
    if n ≤ k ∧ (d : ℤ) ∣ (k : ℤ) - 1 then (d : ℝ) / ((k : ℝ) * B k) else 0
  have hd : 0 < d := Scalar.latticeSpan_pos h.critical h.nondegenerate
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have hθ : 0 < θ := by linarith [h.alpha_mem.1]
  have hρ : 0 < 1 / θ := one_div_pos.2 hθ
  have hSm : Tendsto (fun n => B n * ∑' k, W n k) atTop (𝓝 θ) := by
    have ht := regularVariation_residue_tail (Scalar.regularlyVaryingSeq h)
      h.monotone h.pos hρ hd
    simpa only [one_div_one_div] using ht
  have hsW (n : ℕ) : Summable (W n) := by
    have hs := ((Scalar.regularlyVaryingSeq h).summable_inv_mul h.monotone h.pos hρ)
      |>.mul_left (d : ℝ)
    refine (hs.indicator {k | n ≤ k ∧ (d : ℤ) ∣ (k : ℤ) - 1}).congr fun k => ?_
    by_cases hk : n ≤ k ∧ (d : ℤ) ∣ (k : ℤ) - 1
    · rw [indicator_of_mem
        (show k ∈ {k | n ≤ k ∧ (d : ℤ) ∣ (k : ℤ) - 1} from hk)]
      dsimp only [W]
      rw [ite_eq_left hk]
      ring
    · rw [indicator_of_notMem
        (show k ∉ {k | n ≤ k ∧ (d : ℤ) ∣ (k : ℤ) - 1} from hk)]
      exact (ite_eq_right hk).symm
  have hsF (n : ℕ) : Summable ((Ici n).indicator (forestMass μ 1)) :=
    (Scalar.summable_forestWeight_toReal μ 1).indicator _
  have hoff (k : ℕ) (hk : 1 ≤ k) (hdk : ¬ (d : ℤ) ∣ (k : ℤ) - 1) :
      forestMass μ 1 k = 0 := by
    rw [forestMass_one_eq_sizeProb]
    have hz : walkProb μ k (-1) = 0 :=
      Scalar.walkProb_eq_zero_of_not_dvd h (by
        simpa only [show (-1 : ℤ) + k = (k : ℤ) - 1 by ring] using hdk)
    have hh := Attraction.nat_mul_sizeProb (μ := μ) hk
    rw [hz] at hh
    exact (mul_eq_zero.1 hh).resolve_left (by exact_mod_cast (show k ≠ 0 by omega))
  apply Metric.tendsto_atTop.2
  intro η hη
  let δ : ℝ := η / (2 * (θ + 1))
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  obtain ⟨N, hN⟩ := Attraction.sizeProb_lattice_asymp h (mul_pos hδ hdR)
  have hper (n : ℕ) (hn : N ≤ n) (hn1 : 1 ≤ n) (k : ℕ) :
      |(Ici n).indicator (forestMass μ 1) k - p * W n k| ≤ δ * W n k := by
    by_cases hnk : n ≤ k
    · rw [indicator_of_mem (show k ∈ Ici n from hnk)]
      have hk1 := hn1.trans hnk
      by_cases hdk : (d : ℤ) ∣ (k : ℤ) - 1
      · dsimp only [W]
        rw [ite_eq_left ⟨hnk, hdk⟩]
        have hden : 0 < (k : ℝ) * B k := mul_pos (by exact_mod_cast hk1) (h.pos k hk1)
        have hh := hN k (hn.trans hnk) hdk
        rw [← forestMass_one_eq_sizeProb] at hh
        have heq : forestMass μ 1 k - p * ((d : ℝ) / ((k : ℝ) * B k)) =
            ((k : ℝ) * B k * forestMass μ 1 k - d * p) / ((k : ℝ) * B k) := by
          field_simp [(h.pos k hk1).ne', (show (k : ℝ) ≠ 0 by positivity)]
        rw [heq, abs_div, abs_of_pos hden]
        calc _ ≤ (δ * d) / ((k : ℝ) * B k) := div_le_div_of_nonneg_right hh hden.le
          _ = _ := by ring
      · simp [W, hdk, hoff k hk1 hdk]
    · simp [W, hnk]
  have hnear := (hSm.const_mul p).eventually (Metric.ball_mem_nhds (p * θ) (half_pos hη))
  have hbound := hSm.eventually (gt_mem_nhds (show θ < θ + 1 by linarith))
  obtain ⟨J, hJ⟩ := eventually_atTop.1 (hnear.and hbound)
  refine ⟨max (max N 1) J, fun n hn => ?_⟩
  have hnN : N ≤ n := (le_max_left N 1).trans ((le_max_left _ _).trans hn)
  have hn1 : 1 ≤ n := (le_max_right N 1).trans ((le_max_left _ _).trans hn)
  have hnJ : J ≤ n := (le_max_right _ _).trans hn
  have hlo := ((hsW n).mul_left (p - δ)).tsum_le_tsum
    (fun k => by have hh := (abs_le.1 (hper n hnN hn1 k)).1; nlinarith) (hsF n)
  have hhi := (hsF n).tsum_le_tsum
    (fun k => by have hh := (abs_le.1 (hper n hnN hn1 k)).2; nlinarith)
    ((hsW n).mul_left (p + δ))
  rw [tsum_mul_left] at hlo hhi
  change (p - δ) * ∑' k, W n k ≤ forestTail μ 1 n at hlo
  change forestTail μ 1 n ≤ (p + δ) * ∑' k, W n k at hhi
  have hlo' := mul_le_mul_of_nonneg_left hlo (h.pos n hn1).le
  have hhi' := mul_le_mul_of_nonneg_left hhi (h.pos n hn1).le
  have herr : |B n * forestTail μ 1 n - p * (B n * ∑' k, W n k)| ≤
      δ * (B n * ∑' k, W n k) := by
    rw [abs_le]
    constructor <;> nlinarith
  have hb : B n * ∑' k, W n k ≤ θ + 1 := (hJ n hnJ).2.le
  have hclose : |p * (B n * ∑' k, W n k) - θ * p| < η / 2 := by
    simpa only [Real.dist_eq, mul_comm θ p] using (hJ n hnJ).1
  rw [Real.dist_eq]
  calc _ ≤ |B n * forestTail μ 1 n - p * (B n * ∑' k, W n k)| +
        |p * (B n * ∑' k, W n k) - θ * p| := abs_sub_le _ _ _
    _ < δ * (θ + 1) + η / 2 := add_lt_add_of_le_of_lt
      (herr.trans (mul_le_mul_of_nonneg_left hb hδ.le)) hclose
    _ = η := by
      dsimp only [δ]
      field_simp [ne_of_gt (show 0 < θ + 1 by linarith)]
      ring

/-- **Tail/exact ratio along admissible sizes:** `G_1(q_k) / (q_k f_1(q_k)) → θ / d`. -/
theorem tailExactRatio_tendsto {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ} (h : StableDomain μ θ B)
    {q : ℕ → ℕ} (hqtop : Tendsto q atTop atTop) (hq : ∀ k, Admissible μ (q k)) :
    Tendsto (fun k : ℕ => forestTail μ 1 (q k) / ((q k : ℝ) * forestMass μ 1 (q k))) atTop
      (𝓝 (θ / (Scalar.latticeSpan μ : ℝ))) := by
  have hp := (Scalar.stableDensity_zero_pos h.alpha_mem).ne'
  have hd : (Scalar.latticeSpan μ : ℝ) ≠ 0 := by
    exact_mod_cast (Scalar.latticeSpan_pos h.critical h.nondegenerate).ne'
  have ht := ((treeTail_asymp h).comp hqtop).div (exactMass_tendsto h hqtop hq)
    (mul_ne_zero hd hp)
  have heq : (θ * Scalar.stableDensity θ 0) /
      (Scalar.latticeSpan μ * Scalar.stableDensity θ 0) = θ / (Scalar.latticeSpan μ : ℝ) := by
    field_simp
  rw [heq] at ht
  refine ht.congr' ?_
  filter_upwards [hqtop.eventually (eventually_ge_atTop 1)] with k hk
  have hB := (h.pos (q k) hk).ne'
  change (B (q k) * forestTail μ 1 (q k)) /
    ((q k : ℝ) * B (q k) * forestMass μ 1 (q k)) = _
  rw [mul_comm (q k : ℝ) (B (q k)), mul_assoc, mul_div_mul_left _ _ hB]

end BGW.StableTrees
