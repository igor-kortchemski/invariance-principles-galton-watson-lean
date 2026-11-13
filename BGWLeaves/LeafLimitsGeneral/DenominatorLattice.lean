module

public import BGWLeaves.LeafLimitsGeneral.LocalLattice
public import BGWLeaves.Coding.Defs
public import BGWLeaves.Conditioning.LeafTail

/-! Denominators on admissible leaf counts. The span factor is retained until
it cancels in the conditional-density normalization. -/

@[expose] public section
namespace BGWLeaves.LeafLimitsGeneral.DenominatorLattice
open MeasureTheory ProbabilityTheory Filter BGW BGW.StableTrees BGW.LocallyFinite
open BGWLeaves.StableAnalysis
open BGWLeaves.GeneralA
open BGWLeaves.Conditioning.Basics
open scoped ENNReal Topology

/-- An admissible positive leaf count has the tree residue. -/
theorem admissible_dvd {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    {n : ℕ} (hn : 1 ≤ n) (ha : LeafAdmissible μ n) :
    (arithFactor μ {0} : ℤ) ∣ (n : ℤ) - 1 := by
  have hp : 0 < leafProb μ n := LeafMass.Arithmetic.leafProb_pos_iff_ne_zero μ n |>.2 ha
  have hd := LeafMass.Arithmetic.leafMonoid_dvd hc hne
    ((LeafMass.Arithmetic.leafProb_pos_iff_mem_leafMonoid hc hne (n - 1)).1
      (by simpa only [Nat.sub_add_cancel hn] using hp))
  have hd' := Int.natCast_dvd_natCast.2 hd
  simpa only [Nat.cast_sub hn, Nat.cast_one] using hd'

/-- The admissible stopped-walk denominator has the lattice multiplier. -/
theorem chi_zero_asymp {μ : PMF ℕ} {θ : ℝ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hDA : ∃ a, StableDomain μ θ a) {q : ℕ → ℕ}
    (hqtop : Tendsto q atTop atTop) (hq : ∀ k, LeafAdmissible μ (q k)) :
    Tendsto (fun k => normB μ θ ((q k : ℝ) / (μ 0).toReal) * (chi μ (q k) 0).toReal)
      atTop (𝓝 ((arithFactor μ {0} : ℝ) * Scalar.stableDensity θ 0)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨N, hN⟩ := LocalLattice.lem_technic3 hc hne hDA (half_pos hε)
  filter_upwards [hqtop.eventually (eventually_ge_atTop (max N 1))] with k hk
  have hr := admissible_dvd hc hne (le_trans (le_max_right _ _) hk) (hq k)
  have h := hN (q k) (le_trans (le_max_left _ _) hk) 0
  simpa only [Int.cast_zero, zero_div, neg_zero, sub_zero, ite_eq_left hr, Real.dist_eq] using
    h.trans_lt (half_lt_self hε)

/-- The two exact block identities identify the one-tree denominator with `χ`. -/
theorem n_mul_psi_one {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    {n : ℕ} (hn : 1 ≤ n) : (n : ℝ) * (psi μ n 1).toReal = (chi μ n 0).toReal := by
  rw [LocalLattice.psi_eq_blockWalk hc hne hn (by rfl), ChiBlock.chi_eq_blockWalk μ hn]
  simp only [Nat.cast_one, one_mul, sub_zero, ENNReal.toReal_mul,
    ENNReal.toReal_inv, ENNReal.toReal_natCast]
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  field_simp

/-- The leaf-mass asymptotic along every admissible sequence, with factor `g`. -/
theorem tendsto_leaf_mass_normalized {μ : PMF ℕ} {θ : ℝ}
    (hc : IsCritical μ) (hne : μ 1 ≠ 1) (hDA : ∃ a, StableDomain μ θ a)
    {q : ℕ → ℕ} (hqtop : Tendsto q atTop atTop) (hq : ∀ k, LeafAdmissible μ (q k)) :
    Tendsto (fun k => (q k : ℝ) * normB μ θ (q k) * leafProb μ (q k)) atTop
      (𝓝 ((μ 0).toReal ^ (1 / θ) * Scalar.stableDensity θ 0 * (arithFactor μ {0} : ℝ))) := by
  have hA : μ.toMeasure ({0} : Set ℕ) ≠ 0 := by
    simpa only [PMF.toMeasure_apply_singleton μ 0 (measurableSet_singleton 0)] using hc.apply_zero_ne_zero hne
  have hr := GeneralAInf.BlockStable.norming_floor_ratio hc hne hDA hA
  have hr' : Tendsto (fun n : ℕ => normB μ θ n / normB μ θ ((n : ℝ) / (μ 0).toReal))
      atTop (𝓝 ((μ 0).toReal ^ (1 / θ))) := by
    simpa only [normB, Nat.floor_natCast, PMF.toMeasure_apply_singleton μ 0 (measurableSet_singleton 0)] using hr
  have ht := (hr'.comp hqtop).mul (chi_zero_asymp hc hne hDA hqtop hq)
  have hCpos := (LocalLattice.block_norming_atTop hc hne hDA).eventually (eventually_gt_atTop 0)
  have he : ∀ᶠ k : ℕ in atTop,
      (normB μ θ (q k) / normB μ θ ((q k : ℝ) / (μ 0).toReal)) *
        (normB μ θ ((q k : ℝ) / (μ 0).toReal) * (chi μ (q k) 0).toReal) =
        (q k : ℝ) * normB μ θ (q k) * leafProb μ (q k) := by
    filter_upwards [hqtop.eventually (eventually_ge_atTop 1), hqtop.eventually hCpos] with k hk hp
    rw [← n_mul_psi_one hc hne hk, psi_one]
    change _ = (q k : ℝ) * normB μ θ (q k) * (bienaymeLaw μ.toMeasure).real (leafCountEvent (q k))
    rw [measureReal_def]
    field_simp [hp.ne']
  convert ht.congr' he using 1; ring_nf

/-- The tail/point ratio has limiting factor `θ/g`. -/
theorem tendsto_tail_div_leaf_mass {μ : PMF ℕ} {θ : ℝ}
    (hc : IsCritical μ) (hne : μ 1 ≠ 1) (hap : Aperiodic μ)
    (hDA : ∃ a, StableDomain μ θ a) {q : ℕ → ℕ}
    (hqtop : Tendsto q atTop atTop) (hq : ∀ k, LeafAdmissible μ (q k)) :
    Tendsto (fun k => (psiStar μ (q k) 1).toReal /
      ((q k : ℝ) * (psi μ (q k) 1).toReal)) atTop
      (𝓝 (θ / (arithFactor μ {0} : ℝ))) := by
  obtain ⟨a, ha⟩ := hDA
  have hp : 0 < (μ 0).toReal := ENNReal.toReal_pos (hc.apply_zero_ne_zero hne) (μ.apply_ne_top 0)
  have hg : 0 < (arithFactor μ {0} : ℝ) := by exact_mod_cast GeneralA.Arithmetic.arithFactor_pos hc hne {0}
  have hC : 0 < (μ 0).toReal ^ (1 / θ) * Scalar.stableDensity θ 0 :=
    mul_pos (Real.rpow_pos_of_pos hp _) (Scalar.stableDensity_zero_pos ha.alpha_mem)
  have hT := (Conditioning.LeafTail.leafTail_asymp hc hne hap ⟨a, ha⟩).comp hqtop
  have hL := tendsto_leaf_mass_normalized hc hne ⟨a, ha⟩ hqtop hq
  have ht := hT.div hL (mul_pos hC hg).ne'
  have hv : (θ * (μ 0).toReal ^ (1 / θ) * Scalar.stableDensity θ 0) /
      ((μ 0).toReal ^ (1 / θ) * Scalar.stableDensity θ 0 * (arithFactor μ {0} : ℝ)) =
      θ / (arithFactor μ {0} : ℝ) := by
    calc
      _ = (θ * ((μ 0).toReal ^ (1 / θ) * Scalar.stableDensity θ 0)) /
          ((arithFactor μ {0} : ℝ) * ((μ 0).toReal ^ (1 / θ) * Scalar.stableDensity θ 0)) := by ring
      _ = _ := mul_div_mul_right _ _ hC.ne'
  rw [hv] at ht
  have hattr := locallimit_i (stepLaw μ) (stepLaw_lt_neg_one μ) (integrable_stepLaw hc)
    ⟨a, by rw [mean_stepLaw hc]; exact stableDomain_isStableAttracted ha⟩
  have hpos := (TransformConvergence.tendsto_atTop (stepLaw μ) hattr).eventually (eventually_gt_atTop 0)
  apply ht.congr'
  filter_upwards [hqtop.eventually hpos] with k hk
  rw [psiStar_one, psi_one]
  change (norming (stepLaw μ) θ (q k) * (bienaymeLaw μ.toMeasure).real (leafGeEvent (q k))) /
    ((q k : ℝ) * normB μ θ (q k) * leafProb μ (q k)) = _
  rw [normB_natCast, mul_comm (q k : ℝ), mul_assoc, mul_div_mul_left _ _ hk.ne']
  rfl

end BGWLeaves.LeafLimitsGeneral.DenominatorLattice
