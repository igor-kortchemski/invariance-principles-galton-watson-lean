module

public import BGWLeaves.GeneralAFunctional.Walk
public import BGWLeaves.LeafLimitsGeneral.Residue
public import BGWLeaves.LeafLimits.Bridge

/-! Admissible general-mark residues and the stopped-bridge denominator. -/

@[expose] public section
namespace BGWLeaves.GeneralAFunctional.WalkDenominator
open MeasureTheory ProbabilityTheory Filter BGW BGW.StableTrees BGW.LocallyFinite
open BGWLeaves.StableAnalysis BGWLeaves.GeneralA
open scoped ENNReal Topology

theorem admissible_dvd {μ : PMF ℕ} {A : Set ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    {n : ℕ} (ha : ZetaAAdmissible μ A n) : (arithFactor μ A : ℤ) ∣ (n : ℤ) - 1 := by
  by_contra hd
  apply ha
  exact measure_mono_null (fun _ h => h.2) (MarkedLaw.zetaA_eq_zero_of_not_dvd A hc hne n hd)

/-- The admissible stopped-walk denominator has the lattice multiplier. -/
theorem chi_zero_asymp {μ : PMF ℕ} {θ : ℝ} {A : Set ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hDA : ∃ a, StableDomain μ θ a) (hA : μ.toMeasure A ≠ 0) {q : ℕ → ℕ}
    (hqtop : Tendsto q atTop atTop) (hq : ∀ k, ZetaAAdmissible μ A (q k)) :
    Tendsto (fun k => normB μ θ ((q k : ℝ) / (μ.toMeasure A).toReal) * (WalkLocal.chiA μ A (q k) 0).toReal)
      atTop (𝓝 ((arithFactor μ A : ℝ) * Scalar.stableDensity θ 0)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨N, hN⟩ := WalkLocal.chiA_local_signed hc hne hDA hA (half_pos hε)
  filter_upwards [hqtop.eventually (eventually_ge_atTop (max N 1))] with k hk
  have hr := admissible_dvd hc hne (hq k)
  have h := hN (q k) (le_trans (le_max_left _ _) hk) 0
  simpa only [Int.cast_zero, zero_div, neg_zero, sub_zero, ite_eq_left hr, Real.dist_eq] using
    h.trans_lt (half_lt_self hε)


end BGWLeaves.GeneralAFunctional.WalkDenominator
