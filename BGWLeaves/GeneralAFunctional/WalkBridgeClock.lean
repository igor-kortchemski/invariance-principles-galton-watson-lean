module

public import BGWLeaves.GeneralAFunctional.WalkPathDensity
public import BGWLeaves.GeneralAFunctional.WalkFCLTAll

/-! Bridge conditioning preserves clock concentration, and reweights the clocked FCLT. -/

@[expose] public section
namespace BGWLeaves.GeneralAFunctional.WalkBridgeClock
open MeasureTheory ProbabilityTheory Filter BGW BGW.StableTrees BGW.LocallyFinite
open BGWLeaves.StableAnalysis BGWLeaves.LeafLimits.Bridge
open BGWLeaves.GeneralAFunctional.WalkCyclic BGWLeaves.GeneralAFunctional.WalkVervaat
open BGWLeaves.GeneralAFunctional.WalkFCLT
open scoped ENNReal NNReal Topology

theorem bridge_real_le {μ : PMF ℕ} {A : Set ℕ} {n : ℕ} (hn : 1 ≤ n) (hadm : ZetaAAdmissible μ A n)
    (s : Set (ℕ → ℕ)) :
    (Walk.aBridgeLaw μ A n).toMeasure.real s ≤ (1 / (WalkLocal.chiA μ A n 0).toReal) * (iidWalk μ).real s := by
  have hχ : iidWalk μ (bridgeAtAMark A n) = WalkLocal.chiA μ A n 0 := by
    simp only [WalkLocal.chiA, sub_zero, WalkStopped.aStopEvent, bridgeAtAMark]
  rw [Walk.coe_aBridgeLaw hn hadm]
  simp only [Measure.real, cond_apply (measurableSet_bridgeAtAMark A n), ENNReal.toReal_mul,
    ENNReal.toReal_inv, hχ, one_div]
  exact mul_le_mul_of_nonneg_left (measureReal_mono Set.inter_subset_right) (by positivity)

theorem inv_chi_zero_poly_bound {μ : PMF ℕ} {A : Set ℕ} {θ : ℝ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (_hap : Aperiodic μ) (hDA : ∃ a, StableDomain μ θ a)
    {q : ℕ → ℕ} (hqtop : Tendsto q atTop atTop) (hq : ∀ k, ZetaAAdmissible μ A (q k)) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ k : ℕ in atTop, 1 / (WalkLocal.chiA μ A (q k) 0).toReal ≤ C * (q k : ℝ)^2 := by
  have hmass := Walk.mark_mass_ne_zero_of_admissible_sequence hc hne hqtop hq
  have hp : 0 < (μ.toMeasure A).toReal := ENNReal.toReal_pos hmass (measure_ne_top _ _)
  have hcan := isRealStableAttracted_norming hc hne hDA
  obtain ⟨C, hC, hbound⟩ := attracted_norming_poly_bound hcan
  obtain ⟨a, ha⟩ := hDA
  let density : ℝ := (arithFactor μ A : ℝ) * Scalar.stableDensity θ 0
  have hd : 0 < density := mul_pos
    (by exact_mod_cast GeneralA.Arithmetic.arithFactor_pos hc hne A)
    (Scalar.stableDensity_zero_pos ha.alpha_mem)
  have hzero := WalkDenominator.chi_zero_asymp hc hne ⟨a, ha⟩ hmass hqtop hq
  have hzero' : Tendsto (fun k => normB μ θ ((q k : ℝ) / (μ.toMeasure A).toReal) * (WalkLocal.chiA μ A (q k) 0).toReal / density) atTop (𝓝 (1 : ℝ)) := by
    have he : (arithFactor μ A : ℝ) * Scalar.stableDensity θ 0 = density := rfl
    simpa only [he, div_self hd.ne'] using hzero.div_const density
  have hlow := hzero'.eventually (lt_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1))
  have hidx : Tendsto (fun n : ℕ => ⌊(n : ℝ) / (μ.toMeasure A).toReal⌋₊) atTop atTop :=
    tendsto_nat_floor_atTop.comp (tendsto_natCast_atTop_atTop.atTop_div_const hp)
  refine ⟨2 * C / ((μ.toMeasure A).toReal^2 * density), by positivity, ?_⟩
  filter_upwards [hqtop.eventually (hidx.eventually hbound), hqtop.eventually (hidx.eventually hcan.pos), hlow] with k hn hnpos hnlow
  let n := q k
  let scale := normB μ θ ((n : ℝ) / (μ.toMeasure A).toReal)
  have hscale : 0 < scale := hnpos
  have hscalen : scale ≤ C * ((n : ℝ) / (μ.toMeasure A).toReal)^2 := by
    apply hn.trans
    apply mul_le_mul_of_nonneg_left _ hC.le
    have hi : (⌊(n : ℝ) / (μ.toMeasure A).toReal⌋₊ : ℝ) ≤ (n : ℝ) / (μ.toMeasure A).toReal :=
      Nat.floor_le (div_nonneg (Nat.cast_nonneg n) hp.le)
    nlinarith [show (0 : ℝ) ≤ (⌊(n : ℝ) / (μ.toMeasure A).toReal⌋₊ : ℝ) from Nat.cast_nonneg _]
  have hprod : density / 2 < scale * (WalkLocal.chiA μ A n 0).toReal := by
    have ht := (lt_div_iff₀ hd).mp hnlow
    change (1 / 2 : ℝ) * density < scale * (WalkLocal.chiA μ A n 0).toReal at ht
    linarith
  have hχ : 0 < (WalkLocal.chiA μ A n 0).toReal :=
    pos_of_mul_pos_right (lt_trans (half_pos hd) hprod) hscale.le
  apply (div_le_iff₀ hχ).mpr
  have heq : (2 * C / ((μ.toMeasure A).toReal^2 * density) * (n : ℝ)^2) *
      (WalkLocal.chiA μ A n 0).toReal = (2 / density) *
        (C * ((n : ℝ) / (μ.toMeasure A).toReal)^2 * (WalkLocal.chiA μ A n 0).toReal) := by
    field_simp [hp.ne', hd.ne']
  rw [heq]
  have := mul_le_mul_of_nonneg_right hscalen hχ.le
  have := mul_le_mul_of_nonneg_left this (by positivity : 0 ≤ 2 / density)
  have hunit : (2 / density) * (scale * (WalkLocal.chiA μ A n 0).toReal) > 1 := by
    rw [div_mul_eq_mul_div]
    exact (lt_div_iff₀ hd).mpr (by nlinarith [hprod])
  linarith


theorem tendsto_bridge_small_events {μ : PMF ℕ} {A : Set ℕ} {θ : ℝ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hap : Aperiodic μ) (hDA : ∃ a, StableDomain μ θ a)
    {q : ℕ → ℕ} (hqtop : Tendsto q atTop atTop) (hq : ∀ k, ZetaAAdmissible μ A (q k))
    (s : ℕ → Set (ℕ → ℕ))
    (hs : Tendsto (fun k => (q k : ℝ)^2 * (iidWalk μ).real (s k)) atTop (𝓝 0)) :
    Tendsto (fun k => (Walk.aBridgeLaw μ A (q k)).toMeasure.real (s k)) atTop (𝓝 0) := by
  obtain ⟨C, hC, hbound⟩ := inv_chi_zero_poly_bound hc hne hap hDA hqtop hq
  have ht : Tendsto (fun k => C * ((q k : ℝ)^2 * (iidWalk μ).real (s k))) atTop (𝓝 0) := by
    simpa only [mul_zero] using hs.const_mul C
  apply squeeze_zero' (Eventually.of_forall fun _ => measureReal_nonneg) _ ht
  filter_upwards [hbound, hqtop.eventually_ge_atTop 1] with k hk hk1
  calc
    _ ≤ (1 / (WalkLocal.chiA μ A (q k) 0).toReal) * (iidWalk μ).real (s k) := bridge_real_le hk1 (hq k) _
    _ ≤ (C * (q k : ℝ)^2) * (iidWalk μ).real (s k) :=
      mul_le_mul_of_nonneg_right hk measureReal_nonneg
    _ = _ := by ring

theorem tendsto_nat_of_ratio {m q : ℕ → ℕ} {c : ℝ} (hc : 0 < c)
    (hq : Tendsto q atTop atTop)
    (hm : Tendsto (fun k => (m k : ℝ) / q k) atTop (𝓝 c)) : Tendsto m atTop atTop := by
  have h1 := Tendsto.pos_mul_atTop hc hm (tendsto_natCast_atTop_atTop.comp hq)
  have h2 : Tendsto (fun k => (m k : ℝ)) atTop atTop := by
    apply h1.congr'
    filter_upwards [hq.eventually_ne_atTop 0] with k hk
    simp only [Function.comp_def]
    field_simp
  exact tendsto_natCast_atTop_iff.mp h2

noncomputable def clockBad (A : Set ℕ) (p : ℝ) (n : ℕ) : Set (ℕ → ℕ) :=
  {ω | (¬ ∃ k, IsAMarkTime A n ω k) ∨ ∃ k, IsAMarkTime A n ω k ∧
    1 / (n : ℝ) ^ (1 / 4 : ℝ) < |(k : ℝ) / n - 1 / p|}

theorem tendsto_bridge_markTime_ratio {μ : PMF ℕ} {A : Set ℕ} {θ : ℝ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hap : Aperiodic μ) (hDA : ∃ a, StableDomain μ θ a)
    {q m : ℕ → ℕ} (hqtop : Tendsto q atTop atTop) (hq : ∀ k, ZetaAAdmissible μ A (q k))
    {c : ℝ} (hc0 : 0 < c) (hm : Tendsto (fun k => (m k : ℝ) / q k) atTop (𝓝 c)) :
    ∀ ε > 0, Tendsto (fun k => (Walk.aBridgeLaw μ A (q k)).toMeasure.real
      {ω | ε < dist ((aMarkTime A (m k) ω : ℝ) / m k) (1 / (μ.toMeasure A).toReal)}) atTop (𝓝 0) := by
  have hmass := Walk.mark_mass_ne_zero_of_admissible_sequence hc hne hqtop hq
  have hmtop := tendsto_nat_of_ratio hc0 hqtop hm
  have hbad : Summable (fun n : ℕ => (n : ℝ)^2 * (iidWalk μ).real (clockBad A (μ.toMeasure A).toReal n)) := by
    have hh := LeafConcentration.OeLemmas.IsOe.poly_mul (by norm_num : (0 : ℝ) < 1/2)
      (WalkClockAll.markTime_exponential μ A hmass) (2 : ℝ)
    simpa only [Real.rpow_two, clockBad, iidWalk] using (hh.tail (by norm_num) (fun _ => by positivity)).1
  have hsmall : Tendsto (fun k => (q k : ℝ)^2 * (iidWalk μ).real (clockBad A (μ.toMeasure A).toReal (m k)))
      atTop (𝓝 0) := by
    have ht := ((hm.inv₀ hc0.ne').pow 2).mul (hbad.tendsto_atTop_zero.comp hmtop)
    simp only [mul_zero] at ht
    apply ht.congr'
    filter_upwards [hmtop.eventually_ne_atTop 0] with k hk
    simp only [Function.comp_def]
    field_simp
  have hb := tendsto_bridge_small_events hc hne hap hDA hqtop hq
    (fun k => clockBad A (μ.toMeasure A).toReal (m k)) hsmall
  have hrate : Tendsto (fun k => 1 / (m k : ℝ)^(1 / 4 : ℝ)) atTop (𝓝 0) :=
    (((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1/4)).comp
      tendsto_natCast_atTop_atTop).comp hmtop).const_div_atTop 1
  intro ε hε
  apply squeeze_zero' (Eventually.of_forall fun _ => measureReal_nonneg) _ hb
  filter_upwards [hrate.eventually (gt_mem_nhds hε)] with k hk
  refine measureReal_mono ?_ (measure_ne_top _ _)
  intro ω hω
  by_contra hnot
  have hex : ∃ T, IsAMarkTime A (m k) ω T := not_not.mp (not_or.mp hnot).1
  obtain ⟨T, hT⟩ := hex
  have hle : |(T : ℝ) / m k - 1 / (μ.toMeasure A).toReal| ≤ 1 / (m k : ℝ)^(1/4 : ℝ) :=
    le_of_not_gt (fun h => (not_or.mp hnot).2 ⟨T, hT, h⟩)
  change ε < dist ((aMarkTime A (m k) ω : ℝ) / m k) (1 / (μ.toMeasure A).toReal) at hω
  rw [aMarkTime_eq hT, Real.dist_eq] at hω
  linarith


/-- Convergence at the marked prefix clock, before the final clock perturbation. -/
theorem tendsto_leafClockPath_bridge {μ : PMF ℕ} {A : Set ℕ} {θ : ℝ} {B : ℕ → ℝ}
    (hc : IsCritical μ) (hne : μ 1 ≠ 1) (hap : Aperiodic μ)
    (hB : IsRealStableAttracted (realOffspringStepLaw μ) θ B)
    {q : ℕ → ℕ}
    (hqtop : Tendsto q atTop atTop) (hq : ∀ k, ZetaAAdmissible μ A (q k))
    {a : ℝ} (ha : 0 < a) (ha1 : a < 1) :
    Tendsto (fun k => (Walk.aBridgeLaw μ A (q k)).map (aClockPath A (μ.toMeasure A).toReal B (q k) ha))
      atTop (𝓝 ((stableBridgeLaw θ).map (Skorokhod.restrict ha1.le))) := by
  have hmass := Walk.mark_mass_ne_zero_of_admissible_sequence hc hne hqtop hq
  have hp : 0 < (μ.toMeasure A).toReal := ENNReal.toReal_pos hmass (measure_ne_top _ _)
  apply tendsto_reweighted ((WalkFCLTAll.clocked_walk_tendsto A hmass hB ha).comp hqtop)
    (fun k => WalkDensity.clockPrefixDensity μ A B (q k) ha)
    (fun f => ENNReal.ofReal (bridgePrefixWeight θ a ha.le f))
    (fun k => WalkDensity.measurable_clockPrefixDensity μ A B (q k) ha)
    (measurable_bridgePrefixWeight hB.index_mem ha.le).ennreal_ofReal
  · filter_upwards [hqtop.eventually_ge_atTop 1,
      ((tendsto_leafNormIndex hp).comp hqtop).eventually hB.pos] with k hk hBk
    exact WalkPathDensity.map_clockPath_eq_withDensity hc hne hmass hk (hq k) ha ha1 B hBk.ne'
  · rw [ProbabilityMeasure.toMeasure_map, map_restrict_stableBridgeLaw hB.index_mem ha ha1]
    rfl
  · intro f g hf
    exact WalkDensity.tendsto_clockPrefixDensity hc hne hap hB hmass hqtop hq ha ha1 hf


end BGWLeaves.GeneralAFunctional.WalkBridgeClock
