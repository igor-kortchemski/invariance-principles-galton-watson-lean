module

public import BGWLeaves.LeafConcentration.Defs
public import BGWLeaves.StableAnalysis.Consequences

@[expose] public section

namespace BGWLeaves.LeafConcentration.SizeLower

open MeasureTheory ProbabilityTheory Filter BGW BGW.StableTrees BGW.LocallyFinite
open BGWLeaves.StableAnalysis
open scoped Topology

/-- The local limit constant dominates the extra inverse power eventually. -/
theorem sizeProb_poly_lower {μ : PMF ℕ} {θ : ℝ} (_hc : IsCritical μ) (_hne : μ 1 ≠ 1)
    (hap : Aperiodic μ) (hDA : ∃ b, StableDomain μ θ b) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (n : ℝ) ^ (-(1 / θ + 2)) ≤ (bienaymeLaw μ.toMeasure).real (sizeEvent n) := by
  obtain ⟨a, ha⟩ := hDA
  have hp := Scalar.stableDensity_zero_pos ha.alpha_mem
  have hslow : SlowlyVarying (fun x : ℝ => |a ⌊x⌋₊ / x ^ (1 / θ)|) := by
    intro c hc
    simpa only [← abs_div, abs_one] using ((Scalar.slowlyVarying ha) c hc).abs
  have hs := slow_rpow_neg_mul_tendsto_zero (continuous_abs.measurable.comp (measurable_floor_ratio a (1 / θ)))
    (fun _ _ => abs_nonneg _) hslow (ε := 1) zero_lt_one
  have hs' : Tendsto (fun n : ℕ => (n : ℝ) ^ (-1 : ℝ) *
      (a n / (n : ℝ) ^ (1 / θ))) atTop (𝓝 0) := by
    apply (hs.comp tendsto_natCast_atTop_atTop).congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    simp only [Function.comp_apply, Nat.floor_natCast]
    rw [abs_of_nonneg (div_nonneg (ha.pos n hn).le (Real.rpow_nonneg (Nat.cast_nonneg n) _))]
  have hlo := (sizeProb_asymp ha hap).eventually (eventually_gt_nhds (show
      Scalar.stableDensity θ 0 / 2 < Scalar.stableDensity θ 0 by linarith))
  have hsmall := hs'.eventually (eventually_lt_nhds (show 0 < Scalar.stableDensity θ 0 / 2 by positivity))
  have hev : ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ (-(1 / θ + 2)) ≤
      (bienaymeLaw μ.toMeasure).real (sizeEvent n) := by
    filter_upwards [hlo, hsmall, eventually_ge_atTop 1] with n hn hs hn1
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
    have heq : (n : ℝ) * a n * (n : ℝ) ^ (-(1 / θ + 2)) =
        (n : ℝ) ^ (-1 : ℝ) * (a n / (n : ℝ) ^ (1 / θ)) := by
      calc
        (n : ℝ) * a n * (n : ℝ) ^ (-(1 / θ + 2)) =
            a n * ((n : ℝ) ^ (1 : ℝ) * (n : ℝ) ^ (-(1 / θ + 2))) := by
          rw [Real.rpow_one]; ring
        _ = a n * (n : ℝ) ^ (1 + -(1 / θ + 2)) := by rw [Real.rpow_add hnpos]
        _ = a n * (n : ℝ) ^ (-1 + -(1 / θ)) := by congr 2; ring
        _ = (n : ℝ) ^ (-1 : ℝ) * (a n / (n : ℝ) ^ (1 / θ)) := by
          rw [Real.rpow_add hnpos]
          simp only [Real.rpow_neg hnpos.le, div_eq_mul_inv]
          ring
    apply (mul_le_mul_iff_right₀ (mul_pos hnpos (ha.pos n hn1))).1
    rw [heq]
    exact hs.le.trans hn.le
  exact eventually_atTop.1 hev

end BGWLeaves.LeafConcentration.SizeLower
