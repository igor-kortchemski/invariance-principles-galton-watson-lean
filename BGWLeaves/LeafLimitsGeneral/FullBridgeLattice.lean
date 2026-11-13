module

public import BGWLeaves.LeafLimitsGeneral.SupportLattice

/-! Full lattice bridge principle. Clock concentration, time perturbation and
terminal reversal are copied from `LeafLimits.Bridge`. Only the conditioning
bound and projected prefix density require the lattice local layer. -/

@[expose] public section
namespace BGWLeaves.LeafLimitsGeneral.FullBridgeLattice
open MeasureTheory ProbabilityTheory Filter BGW BGW.StableTrees BGW.LocallyFinite
open BGWLeaves.StableAnalysis BGWLeaves.LeafLimits.Bridge
open BGWLeaves.LeafLimits
open scoped ENNReal NNReal Topology

theorem inv_chi_zero_poly_bound {μ : PMF ℕ} {θ : ℝ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (_hap : Aperiodic μ) (hDA : ∃ a, StableDomain μ θ a)
    {q : ℕ → ℕ} (hqtop : Tendsto q atTop atTop) (hq : ∀ k, LeafAdmissible μ (q k)) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ k : ℕ in atTop, 1 / (chi μ (q k) 0).toReal ≤ C * (q k : ℝ)^2 := by
  have hp : 0 < (μ 0).toReal := ENNReal.toReal_pos (hc.apply_zero_ne_zero hne) (μ.apply_ne_top 0)
  have hcan := isRealStableAttracted_norming hc hne hDA
  obtain ⟨C, hC, hbound⟩ := attracted_norming_poly_bound hcan
  obtain ⟨a, ha⟩ := hDA
  let density : ℝ := (arithFactor μ {0} : ℝ) * Scalar.stableDensity θ 0
  have hd : 0 < density := mul_pos
    (by exact_mod_cast GeneralA.Arithmetic.arithFactor_pos hc hne {0})
    (Scalar.stableDensity_zero_pos ha.alpha_mem)
  have hzero := DenominatorLattice.chi_zero_asymp hc hne ⟨a, ha⟩ hqtop hq
  have hzero' : Tendsto (fun k => normB μ θ ((q k : ℝ) / (μ 0).toReal) * (chi μ (q k) 0).toReal / density) atTop (𝓝 (1 : ℝ)) := by
    have he : (arithFactor μ {0} : ℝ) * Scalar.stableDensity θ 0 = density := rfl
    simpa only [he, div_self hd.ne'] using hzero.div_const density
  have hlow := hzero'.eventually (lt_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1))
  have hidx : Tendsto (fun n : ℕ => ⌊(n : ℝ) / (μ 0).toReal⌋₊) atTop atTop :=
    tendsto_nat_floor_atTop.comp (tendsto_natCast_atTop_atTop.atTop_div_const hp)
  refine ⟨2 * C / ((μ 0).toReal^2 * density), by positivity, ?_⟩
  filter_upwards [hqtop.eventually (hidx.eventually hbound), hqtop.eventually (hidx.eventually hcan.pos), hlow] with k hn hnpos hnlow
  let n := q k
  let A := normB μ θ ((n : ℝ) / (μ 0).toReal)
  have hA : 0 < A := hnpos
  have hAn : A ≤ C * ((n : ℝ) / (μ 0).toReal)^2 := by
    apply hn.trans
    apply mul_le_mul_of_nonneg_left _ hC.le
    have hi : (⌊(n : ℝ) / (μ 0).toReal⌋₊ : ℝ) ≤ (n : ℝ) / (μ 0).toReal :=
      Nat.floor_le (div_nonneg (Nat.cast_nonneg n) hp.le)
    nlinarith [show (0 : ℝ) ≤ (⌊(n : ℝ) / (μ 0).toReal⌋₊ : ℝ) from Nat.cast_nonneg _]
  have hprod : density / 2 < A * (chi μ n 0).toReal := by
    have ht := (lt_div_iff₀ hd).mp hnlow
    change (1 / 2 : ℝ) * density < A * (chi μ n 0).toReal at ht
    linarith
  have hχ : 0 < (chi μ n 0).toReal :=
    pos_of_mul_pos_right (lt_trans (half_pos hd) hprod) hA.le
  apply (div_le_iff₀ hχ).mpr
  have heq : (2 * C / ((μ 0).toReal^2 * density) * (n : ℝ)^2) *
      (chi μ n 0).toReal = (2 / density) *
        (C * ((n : ℝ) / (μ 0).toReal)^2 * (chi μ n 0).toReal) := by
    field_simp [hp.ne', hd.ne']
  rw [heq]
  have := mul_le_mul_of_nonneg_right hAn hχ.le
  have := mul_le_mul_of_nonneg_left this (by positivity : 0 ≤ 2 / density)
  have hunit : (2 / density) * (A * (chi μ n 0).toReal) > 1 := by
    rw [div_mul_eq_mul_div]
    exact (lt_div_iff₀ hd).mpr (by nlinarith [hprod])
  linarith


theorem tendsto_bridge_small_events {μ : PMF ℕ} {θ : ℝ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hap : Aperiodic μ) (hDA : ∃ a, StableDomain μ θ a)
    {q : ℕ → ℕ} (hqtop : Tendsto q atTop atTop) (hq : ∀ k, LeafAdmissible μ (q k))
    (s : ℕ → Set (ℕ → ℕ))
    (hs : Tendsto (fun k => (q k : ℝ)^2 * (iidWalk μ).real (s k)) atTop (𝓝 0)) :
    Tendsto (fun k => (bridgeWalkLaw μ (q k)).toMeasure.real (s k)) atTop (𝓝 0) := by
  obtain ⟨C, hC, hbound⟩ := inv_chi_zero_poly_bound hc hne hap hDA hqtop hq
  have ht : Tendsto (fun k => C * ((q k : ℝ)^2 * (iidWalk μ).real (s k))) atTop (𝓝 0) := by
    simpa only [mul_zero] using hs.const_mul C
  apply squeeze_zero' (Eventually.of_forall fun _ => measureReal_nonneg) _ ht
  filter_upwards [hbound, hqtop.eventually_ge_atTop 1] with k hk hk1
  calc
    _ ≤ (1 / (chi μ (q k) 0).toReal) * (iidWalk μ).real (s k) := bridge_real_le hk1 (hq k) _
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

noncomputable def clockBad (p : ℝ) (n : ℕ) : Set (ℕ → ℕ) :=
  {ω | (¬ ∃ k, IsMarkTime n ω k) ∨ ∃ k, IsMarkTime n ω k ∧
    1 / (n : ℝ) ^ (1 / 4 : ℝ) < |(k : ℝ) / n - 1 / p|}

theorem tendsto_bridge_markTime_ratio {μ : PMF ℕ} {θ : ℝ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hap : Aperiodic μ) (hDA : ∃ a, StableDomain μ θ a)
    {q m : ℕ → ℕ} (hqtop : Tendsto q atTop atTop) (hq : ∀ k, LeafAdmissible μ (q k))
    {c : ℝ} (hc0 : 0 < c) (hm : Tendsto (fun k => (m k : ℝ) / q k) atTop (𝓝 c)) :
    ∀ ε > 0, Tendsto (fun k => (bridgeWalkLaw μ (q k)).toMeasure.real
      {ω | ε < dist ((markTime (m k) ω : ℝ) / m k) (1 / (μ 0).toReal)}) atTop (𝓝 0) := by
  have hmtop := tendsto_nat_of_ratio hc0 hqtop hm
  have hbad : Summable (fun n : ℕ => (n : ℝ)^2 * (iidWalk μ).real (clockBad (μ 0).toReal n)) := by
    have hh := LeafConcentration.OeLemmas.IsOe.poly_mul (by norm_num : (0 : ℝ) < 1/2)
      (lem_CVf2_i μ (hc.apply_zero_ne_zero hne) (mu0_ne_one hc hne)) (2 : ℝ)
    simpa only [Real.rpow_two, clockBad, iidWalk] using (hh.tail (by norm_num) (fun _ => by positivity)).1
  have hsmall : Tendsto (fun k => (q k : ℝ)^2 * (iidWalk μ).real (clockBad (μ 0).toReal (m k)))
      atTop (𝓝 0) := by
    have ht := ((hm.inv₀ hc0.ne').pow 2).mul (hbad.tendsto_atTop_zero.comp hmtop)
    simp only [mul_zero] at ht
    apply ht.congr'
    filter_upwards [hmtop.eventually_ne_atTop 0] with k hk
    simp only [Function.comp_def]
    field_simp
  have hb := tendsto_bridge_small_events hc hne hap hDA hqtop hq
    (fun k => clockBad (μ 0).toReal (m k)) hsmall
  have hrate : Tendsto (fun k => 1 / (m k : ℝ)^(1 / 4 : ℝ)) atTop (𝓝 0) :=
    (((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1/4)).comp
      tendsto_natCast_atTop_atTop).comp hmtop).const_div_atTop 1
  intro ε hε
  apply squeeze_zero' (Eventually.of_forall fun _ => measureReal_nonneg) _ hb
  filter_upwards [hrate.eventually (gt_mem_nhds hε)] with k hk
  refine measureReal_mono ?_ (measure_ne_top _ _)
  intro ω hω
  by_contra hnot
  have hex : ∃ T, IsMarkTime (m k) ω T := not_not.mp (not_or.mp hnot).1
  obtain ⟨T, hT⟩ := hex
  have hle : |(T : ℝ) / m k - 1 / (μ 0).toReal| ≤ 1 / (m k : ℝ)^(1/4 : ℝ) :=
    le_of_not_gt (fun h => (not_or.mp hnot).2 ⟨T, hT, h⟩)
  change ε < dist ((markTime (m k) ω : ℝ) / m k) (1 / (μ 0).toReal) at hω
  rw [markTime_eq_of_isMarkTime hT, Real.dist_eq] at hω
  linarith


/-- Convergence at the marked prefix clock, before the final clock perturbation. -/
theorem tendsto_leafClockPath_bridge {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ}
    (hc : IsCritical μ) (hne : μ 1 ≠ 1) (hap : Aperiodic μ)
    (hB : IsRealStableAttracted (realOffspringStepLaw μ) θ B)
    {q : ℕ → ℕ}
    (hqtop : Tendsto q atTop atTop) (hq : ∀ k, LeafAdmissible μ (q k))
    {a : ℝ} (ha : 0 < a) (ha1 : a < 1) :
    Tendsto (fun k => (bridgeWalkLaw μ (q k)).map (leafClockPath (μ 0).toReal B (q k) ha))
      atTop (𝓝 ((stableBridgeLaw θ).map (Skorokhod.restrict ha1.le))) := by
  have hp : 0 < (μ 0).toReal := ENNReal.toReal_pos (hc.apply_zero_ne_zero hne) (μ.apply_ne_top 0)
  apply tendsto_reweighted ((ClassicalLimits.WalkClock.lem_CVf2_ii hc hne hB ha).comp hqtop)
    (fun k => BridgeLattice.clockPrefixDensity μ B (q k) ha)
    (fun f => ENNReal.ofReal (bridgePrefixWeight θ a ha.le f))
    (fun k => BridgeLattice.measurable_clockPrefixDensity μ B (q k) ha)
    (measurable_bridgePrefixWeight hB.index_mem ha.le).ennreal_ofReal
  · filter_upwards [hqtop.eventually_ge_atTop 1,
      ((tendsto_leafNormIndex hp).comp hqtop).eventually hB.pos] with k hk hBk
    exact SupportLattice.map_leafClockPath_eq_withDensity hc hne hk (hq k) ha ha1 B hBk.ne'
  · rw [ProbabilityMeasure.toMeasure_map, map_restrict_stableBridgeLaw hB.index_mem ha ha1]
    rfl
  · intro f g hf
    exact BridgeLattice.tendsto_clockPrefixDensity hc hne hap hB hqtop hq ha ha1 hf

private def ErrorConverges {Ω E : Type*} [MeasurableSpace Ω] [PseudoMetricSpace E]
    (P : ℕ → ProbabilityMeasure Ω) (X : ℕ → Ω → E) (c : E) : Prop :=
  ∀ ε > 0, Tendsto (fun n => (P n).toMeasure.real {ω | ε < dist (X n ω) c}) atTop (𝓝 0)

private theorem error_const {Ω E : Type*} [MeasurableSpace Ω] [PseudoMetricSpace E]
    (P : ℕ → ProbabilityMeasure Ω) {x : ℕ → E} {c : E} (hx : Tendsto x atTop (𝓝 c)) :
    ErrorConverges P (fun n _ => x n) c := by
  intro ε hε
  have he : ∀ᶠ n in atTop, (P n).toMeasure.real {ω | ε < dist (x n) c} = 0 := by
    filter_upwards [hx.eventually (Metric.ball_mem_nhds c hε)] with n hn
    have hs : {ω : Ω | ε < dist (x n) c} = ∅ := by ext ω; simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]; exact not_lt_of_ge hn.le
    rw [hs, measureReal_empty]
  exact tendsto_const_nhds.congr' (he.mono fun _ h => h.symm)

private theorem error_prod {Ω E F : Type*} [MeasurableSpace Ω] [PseudoMetricSpace E] [PseudoMetricSpace F]
    {P : ℕ → ProbabilityMeasure Ω} {X : ℕ → Ω → E} {Y : ℕ → Ω → F} {x : E} {y : F}
    (hX : ErrorConverges P X x) (hY : ErrorConverges P Y y) :
    ErrorConverges P (fun n ω => (X n ω, Y n ω)) (x, y) := by
  intro ε hε
  have ht := (hX ε hε).add (hY ε hε)
  simp only [add_zero] at ht
  apply squeeze_zero (fun _ => measureReal_nonneg) _ ht
  intro n
  apply (measureReal_mono (show {ω | ε < dist (X n ω, Y n ω) (x, y)} ⊆
      {ω | ε < dist (X n ω) x} ∪ {ω | ε < dist (Y n ω) y} from ?_)).trans
    (measureReal_union_le _ _)
  intro ω hω
  change ε < max (dist (X n ω) x) (dist (Y n ω) y) at hω
  exact lt_max_iff.mp hω

private theorem error_comp {Ω E F : Type*} [MeasurableSpace Ω] [PseudoMetricSpace E] [PseudoMetricSpace F]
    {P : ℕ → ProbabilityMeasure Ω} {X : ℕ → Ω → E} {c : E}
    (hX : ErrorConverges P X c) {f : E → F} (hf : ContinuousAt f c) :
    ErrorConverges P (fun n ω => f (X n ω)) (f c) := by
  intro ε hε
  obtain ⟨δ, hδ, hlocal⟩ := Metric.continuousAt_iff.mp hf ε hε
  apply squeeze_zero (fun _ => measureReal_nonneg) _ (hX (δ / 2) (half_pos hδ))
  intro n
  refine measureReal_mono ?_
  intro ω hω
  by_contra h
  have hnear : dist (X n ω) c < δ := (not_lt.mp h).trans_lt (half_lt_self hδ)
  exact (not_lt_of_ge (hlocal hnear).le) hω

private theorem error_norming_ratio {Ω : Type*} [MeasurableSpace Ω]
    {ν : ProbabilityMeasure ℝ} {θ : ℝ} {B : ℕ → ℝ}
    (hB : IsRealStableAttracted ν θ B) {P : ℕ → ProbabilityMeasure Ω}
    {q : ℕ → ℕ} (hq : Tendsto q atTop atTop) (M : ℕ → Ω → ℕ)
    {c : ℝ} (hc : 0 < c) (hM : ErrorConverges P (fun n ω => (M n ω : ℝ) / q n) c) :
    ErrorConverges P (fun n ω => B (M n ω) / B (q n)) (c^(1 / θ)) := by
  intro ε hε
  obtain ⟨δ, hδ, hlocal⟩ := Metric.continuousAt_iff.mp
    (Real.continuousAt_rpow_const c (1 / θ) (Or.inl hc.ne')) (ε / 2) (half_pos hε)
  let d := min (c / 2) (min 1 (δ / 2))
  have hd : 0 < d := lt_min (half_pos hc) (lt_min zero_lt_one (half_pos hδ))
  obtain ⟨N, hN⟩ := hB.uniform_ratio (show 0 < c / 2 by positivity)
    (show c / 2 ≤ c + 1 by linarith) (ε / 2) (half_pos hε)
  apply squeeze_zero' (Eventually.of_forall fun _ => measureReal_nonneg) _ (hM d hd)
  filter_upwards [hq.eventually_ge_atTop N] with n hn
  refine measureReal_mono ?_
  intro ω hω
  by_contra h
  have habs : |(M n ω : ℝ) / q n - c| ≤ d := not_lt.mp h
  have hlow : c / 2 * q n ≤ (M n ω : ℝ) := by
    have h := (abs_le.mp habs).1
    have hdle : d ≤ c / 2 := min_le_left _ _
    have hq0 : (0 : ℝ) ≤ q n := Nat.cast_nonneg _
    by_cases hqzero : q n = 0
    · simp [hqzero]
    · have : (0 : ℝ) < q n := by exact_mod_cast Nat.pos_of_ne_zero hqzero
      apply (le_div_iff₀ this).mp
      linarith
  have hhigh : (M n ω : ℝ) ≤ (c + 1) * q n := by
    have h := (abs_le.mp habs).2
    have hdle : d ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
    by_cases hqzero : q n = 0
    · have : c ≤ d := by simpa [hqzero, abs_of_pos hc] using habs
      have : d ≤ c / 2 := min_le_left _ _
      linarith
    · have : (0 : ℝ) < q n := by exact_mod_cast Nat.pos_of_ne_zero hqzero
      apply (div_le_iff₀ this).mp
      linarith
  have happrox := hN (q n) hn (M n ω) hlow hhigh
  have hrpow : |((M n ω : ℝ) / q n)^(1 / θ) - c^(1 / θ)| < ε / 2 := by
    apply hlocal
    exact habs.trans_lt (lt_of_le_of_lt ((min_le_right _ _).trans (min_le_right _ _)) (half_lt_self hδ))
  change ε < |B (M n ω) / B (q n) - c^(1 / θ)| at hω
  have hh := abs_sub_le (B (M n ω) / B (q n)) (((M n ω : ℝ) / q n)^(1 / θ)) (c^(1 / θ))
  linarith


private theorem error_congr_eventually {Ω E : Type*} [MeasurableSpace Ω] [PseudoMetricSpace E]
    {P : ℕ → ProbabilityMeasure Ω} {X Y : ℕ → Ω → E} {c : E}
    (hX : ErrorConverges P X c) (hXY : ∀ᶠ n in atTop, ∀ ω, X n ω = Y n ω) :
    ErrorConverges P Y c := by
  intro ε hε
  apply (hX ε hε).congr'
  filter_upwards [hXY] with n hn
  congr 1
  ext ω
  simp only [Set.mem_ofPred_eq, hn ω]

private theorem error_mul {Ω : Type*} [MeasurableSpace Ω]
    {P : ℕ → ProbabilityMeasure Ω} {X Y : ℕ → Ω → ℝ} {x y : ℝ}
    (hX : ErrorConverges P X x) (hY : ErrorConverges P Y y) :
    ErrorConverges P (fun n ω => X n ω * Y n ω) (x * y) :=
  error_comp (f := fun z : ℝ × ℝ => z.1 * z.2) (error_prod hX hY)
    (continuous_fst.mul continuous_snd).continuousAt

private theorem error_div {Ω : Type*} [MeasurableSpace Ω]
    {P : ℕ → ProbabilityMeasure Ω} {X Y : ℕ → Ω → ℝ} {x y : ℝ}
    (hX : ErrorConverges P X x) (hY : ErrorConverges P Y y) (hy : y ≠ 0) :
    ErrorConverges P (fun n ω => X n ω / Y n ω) (x / y) :=
  error_comp (f := fun z : ℝ × ℝ => z.1 / z.2) (error_prod hX hY)
    (continuousAt_fst.div continuousAt_snd hy)

private theorem bridge_factors_error {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ}
    (hc : IsCritical μ) (hne : μ 1 ≠ 1) (hap : Aperiodic μ)
    (hB : IsRealStableAttracted (realOffspringStepLaw μ) θ B)
    {q : ℕ → ℕ}
    (hqtop : Tendsto q atTop atTop) (hq : ∀ k, LeafAdmissible μ (q k))
    {b : ℝ} (hb : 0 < b) :
    ErrorConverges (fun k => bridgeWalkLaw μ (q k))
      (fun k ω => B (leafNormIndex (μ 0).toReal (q k)) / B (markTime (q k) ω)) 1 ∧
    ErrorConverges (fun k => bridgeWalkLaw μ (q k))
      (fun k ω => b * (markTime (q k) ω : ℝ) / markTime ⌊b * q k⌋₊ ω) 1 := by
  let P := fun k => bridgeWalkLaw μ (q k)
  have hp : 0 < (μ 0).toReal := ENNReal.toReal_pos (hc.apply_zero_ne_zero hne) (μ.apply_ne_top 0)
  have hDA := (stableDomain_of_isRealStableAttracted hc hne hB).1
  have hself : Tendsto (fun k => (q k : ℝ) / q k) atTop (𝓝 (1 : ℝ)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [hqtop.eventually_ne_atTop 0] with k hk
    simp [hk]
  have hfloor : Tendsto (fun k => (⌊b * q k⌋₊ : ℝ) / q k) atTop (𝓝 b) :=
    ((tendsto_nat_floor_mul_div_atTop (R := ℝ) hb.le).comp tendsto_natCast_atTop_atTop).comp hqtop
  have hfloorTop := tendsto_nat_of_ratio hb hqtop hfloor
  have hX : ErrorConverges P (fun k ω => (markTime (q k) ω : ℝ) / q k) (1 / (μ 0).toReal) :=
    tendsto_bridge_markTime_ratio hc hne hap hDA hqtop hq zero_lt_one hself
  have hY : ErrorConverges P (fun k ω => (markTime ⌊b * q k⌋₊ ω : ℝ) / ⌊b * q k⌋₊)
      (1 / (μ 0).toReal) :=
    tendsto_bridge_markTime_ratio hc hne hap hDA hqtop hq hb hfloor
  have hY' : ErrorConverges P (fun k ω => (markTime ⌊b * q k⌋₊ ω : ℝ) / q k)
      ((1 / (μ 0).toReal) * b) := by
    apply error_congr_eventually (error_mul hY (error_const P hfloor))
    filter_upwards [hfloorTop.eventually_ne_atTop 0] with k hk
    intro ω
    exact div_mul_div_cancel₀ (by exact_mod_cast hk)
  have hR := error_norming_ratio hB hqtop (fun k => markTime (q k)) (one_div_pos.mpr hp) hX
  have hA := error_const P (hB.tendsto_norming_ratio (one_div_pos.mpr hp) hqtop
    ((leafNormIndex_ratio hp).comp hqtop))
  have hRpos : 0 < (1 / (μ 0).toReal)^(1 / θ) := Real.rpow_pos_of_pos (one_div_pos.mpr hp) _
  constructor
  · have hK := error_div hA hR hRpos.ne'
    rw [div_self hRpos.ne'] at hK
    apply error_congr_eventually hK
    filter_upwards [hqtop.eventually hB.pos] with k hk
    intro ω
    exact div_div_div_cancel_right₀ hk.ne' _ _
  · have hS := error_div (error_mul (error_const P (tendsto_const_nhds (x := b))) hX)
      hY' (mul_ne_zero (one_div_ne_zero hp.ne') hb.ne')
    have heq : b * (1 / (μ 0).toReal) / ((1 / (μ 0).toReal) * b) = 1 := by field_simp
    rw [heq] at hS
    apply error_congr_eventually hS
    filter_upwards [hqtop.eventually_ne_atTop 0] with k hk
    intro ω
    rw [← mul_div_assoc, div_div_div_cancel_right₀ (show (q k : ℝ) ≠ 0 by exact_mod_cast hk)]

theorem bridgeWalkPath_apply (B : ℕ → ℝ) (n : ℕ) (ω : ℕ → ℕ) (t : Set.Icc (0 : ℝ) 1) :
    bridgeWalkPath B n ω t =
      (walkSum ω ⌊(markTime n ω : ℝ) * (t : ℝ)⌋₊ : ℝ) / B (markTime n ω) := by
  change (((walkWord ω (markTime n ω)).take
    ⌊((walkWord ω (markTime n ω)).length : ℝ) * (t : ℝ)⌋₊).sum : ℝ) / _ = _
  have hlen : (walkWord ω (markTime n ω)).length = markTime n ω := by simp [walkWord]
  rw [hlen, BGWLeaves.Vervaat.TimeReversal.sum_take_walkWord]
  exact Nat.floor_le_of_le (mul_le_of_le_one_right (Nat.cast_nonneg _) t.2.2)

noncomputable def bridgeClockFactor (b : ℝ) (n : ℕ) (ω : ℕ → ℕ) : Set.Ioi (0 : ℝ) :=
  ⟨max (b * (markTime n ω : ℝ) / markTime ⌊b * n⌋₊ ω) (1/2),
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1/2) (le_max_right _ _)⟩

theorem measurable_bridgeClockFactor (b : ℝ) (n : ℕ) :
    Measurable (fun ω => (bridgeClockFactor b n ω : ℝ)) := by
  exact (measurable_const.mul ((measurable_of_countable (fun m : ℕ => (m : ℝ))).comp (measurable_markTime n)) |>.div
    ((measurable_of_countable (fun m : ℕ => (m : ℝ))).comp (measurable_markTime ⌊b * n⌋₊))).max measurable_const

theorem timeSpaceScale_leafClockPath_eq_restrict (p : ℝ) (B : ℕ → ℝ) (n : ℕ)
    {a b : ℝ} (ha1 : a ≤ 1) (hb : 0 < b) (ω : ℕ → ℕ)
    (hL : 0 < markTime ⌊b * n⌋₊ ω) (hB : B (leafNormIndex p n) ≠ 0)
    (hS : (1/2 : ℝ) ≤ b * (markTime n ω : ℝ) / markTime ⌊b * n⌋₊ ω)
    (hfit : (b * (markTime n ω : ℝ) / markTime ⌊b * n⌋₊ ω) * a ≤ b) :
    Skorokhod.timeSpaceScale a hb.le
      (leafClockPath p B n hb ω, B (leafNormIndex p n) / B (markTime n ω), bridgeClockFactor b n ω) =
        Skorokhod.restrict ha1 (bridgeWalkPath B n ω) := by
  apply Skorokhod.ext
  intro t
  have hraw : 0 ≤ b * (markTime n ω : ℝ) / markTime ⌊b * n⌋₊ ω := by linarith
  have hbt : b * (markTime n ω : ℝ) / markTime ⌊b * n⌋₊ ω * (t : ℝ) ≤ b :=
    (mul_le_mul_of_nonneg_left t.2.2 hraw).trans hfit
  change (B (leafNormIndex p n) / B (markTime n ω)) *
      (1 * (BGW.Probability.RealWalk.partialSum (walkIncr ω)
        ⌊(markTime ⌊b * n⌋₊ ω : ℝ) * min (1 / b *
          min (max (b * (markTime n ω : ℝ) / markTime ⌊b * n⌋₊ ω) (1/2) * (t : ℝ)) b) 1⌋₊ /
          B (leafNormIndex p n))) =
    bridgeWalkPath B n ω ⟨t, t.2.1, t.2.2.trans ha1⟩
  rw [bridgeWalkPath_apply, max_eq_left hS, min_eq_left hbt]
  have hinner : 1 / b * (b * (markTime n ω : ℝ) / markTime ⌊b * n⌋₊ ω * (t : ℝ)) ≤ 1 := by
    rw [one_div_mul_eq_div, div_le_one hb]
    exact hbt
  rw [min_eq_left hinner, one_mul, partialSum_walkIncr]
  have hclock : (markTime ⌊b * n⌋₊ ω : ℝ) *
      (1 / b * (b * (markTime n ω : ℝ) / markTime ⌊b * n⌋₊ ω * (t : ℝ))) =
        (markTime n ω : ℝ) * (t : ℝ) := by
    field_simp [hb.ne', show (markTime ⌊b * n⌋₊ ω : ℝ) ≠ 0 by exact_mod_cast hL.ne']
  rw [hclock]
  exact div_mul_div_cancel₀' hB _ _

/-- Prefix convergence on a strictly positive horizon. The marked prefix is first taken at
`b > a`; Lemma 5.7 is then used with the factor `b T_n / T_(bn)`. -/
theorem bridge_prefix_tendsto_pos {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ} (hc : IsCritical μ)
    (hne : μ 1 ≠ 1) (hap : Aperiodic μ)
    (hB : IsRealStableAttracted (realOffspringStepLaw μ) θ B)
    {q : ℕ → ℕ}
    (hqtop : Tendsto q atTop atTop) (hq : ∀ k, LeafAdmissible μ (q k))
    {a : ℝ} (ha : 0 < a) (ha1 : a < 1) :
    Tendsto (fun k => (bridgeWalkLaw μ (q k)).map
        (Skorokhod.restrict ha1.le ∘ bridgeWalkPath B (q k)))
      atTop (𝓝 ((stableBridgeLaw θ).map (Skorokhod.restrict ha1.le))) := by
  obtain ⟨b, hab, hb1⟩ := exists_between ha1
  have hb : 0 < b := ha.trans hab
  have hp : 0 < (μ 0).toReal := ENNReal.toReal_pos (hc.apply_zero_ne_zero hne) (μ.apply_ne_top 0)
  let P := fun k => bridgeWalkLaw μ (q k)
  let Z := fun k => leafClockPath (μ 0).toReal B (q k) hb
  let K := fun k ω => B (leafNormIndex (μ 0).toReal (q k)) / B (markTime (q k) ω)
  let S := fun k => bridgeClockFactor b (q k)
  let L := (stableBridgeLaw θ).map (Skorokhod.restrict hb1.le)
  let G := fun k ω => Skorokhod.timeSpaceScale a hb.le (Z k ω, K k ω, S k ω)
  have hZm : ∀ k, Measurable (Z k) := fun k => measurable_leafClockPath _ _ _ _
  have hKm : ∀ k, Measurable (K k) := fun k =>
    measurable_const.div ((measurable_of_countable B).comp (measurable_markTime (q k)))
  have hSm : ∀ k, Measurable (fun ω => (S k ω : ℝ)) := fun k => measurable_bridgeClockFactor _ _
  have hGm : ∀ k, Measurable (G k) := fun k =>
    (measurable_timeSpaceScale a hb.le).comp
      ((hZm k).prodMk ((hKm k).prodMk (hSm k).subtype_mk))
  have hZ : Tendsto (fun k => (P k).map (Z k)) atTop (𝓝 L) :=
    tendsto_leafClockPath_bridge hc hne hap hB hqtop hq hb hb1
  have hcont : ∀ᵐ f : Skorokhod.D b ℝ ∂L.toMeasure,
      ContinuousAt (f : Set.Icc (0 : ℝ) b → ℝ) ⟨a, ha.le, hab.le⟩ := by
    dsimp only [L]
    rw [ProbabilityMeasure.toMeasure_map, map_restrict_stableBridgeLaw hB.index_mem hb hb1,
      bridgePrefixLaw]
    exact (withDensity_absolutelyContinuous _ _).ae_le
      (ae_continuousAt_stableProcessLaw hB.index_mem hb ⟨a, ha.le, hab.le⟩)
  obtain ⟨hK, hraw⟩ := bridge_factors_error hc hne hap hB hqtop hq hb
  have hS : ErrorConverges P (fun k ω => (S k ω : ℝ)) 1 := by
    have ht := error_comp (f := fun x : ℝ => max x (1/2)) hraw
      (continuous_id.max continuous_const).continuousAt
    simpa only [P, S, bridgeClockFactor, max_eq_left (by norm_num : (1/2 : ℝ) ≤ 1)] using ht
  have hpert : Tendsto (fun k => (P k).map (G k)) atTop
      (𝓝 (L.map (Skorokhod.restrict hab.le))) :=
    ClassicalLimits.Perturbation.lem_CVproba ha hab P Z K S hZm hKm hSm L hZ hcont hK hS
  have htarget : L.map (Skorokhod.restrict hab.le) =
      (stableBridgeLaw θ).map (Skorokhod.restrict ha1.le) := by
    apply ProbabilityMeasure.toMeasure_injective
    dsimp only [L]
    rw [ProbabilityMeasure.toMeasure_map, ProbabilityMeasure.toMeasure_map,
      Measure.map_map (Skorokhod.measurable_restrict _) (Skorokhod.measurable_restrict _),
      ProbabilityMeasure.toMeasure_map]
    rfl
  rw [htarget] at hpert
  apply BGW.MetricMeasure.tendsto_probabilityMap_of_error_probability P
    (fun k => (Skorokhod.measurable_restrict _).comp (measurable_bridgeWalkPath B (q k)))
    hGm _ hpert
  intro ε hε
  let d := min (1/4 : ℝ) ((b - a) / (2 * a))
  have hd : 0 < d := lt_min (by norm_num) (div_pos (sub_pos.mpr hab) (by positivity))
  have hfloor : Tendsto (fun k => (⌊b * q k⌋₊ : ℝ) / q k) atTop (𝓝 b) :=
    ((tendsto_nat_floor_mul_div_atTop (R := ℝ) hb.le).comp tendsto_natCast_atTop_atTop).comp hqtop
  have hfloorTop := tendsto_nat_of_ratio hb hqtop hfloor
  apply squeeze_zero' (Eventually.of_forall fun _ => measureReal_nonneg) _ (hraw d hd)
  filter_upwards [hqtop.eventually_ge_atTop 1, hfloorTop.eventually_ge_atTop 1,
    ((tendsto_leafNormIndex hp).comp hqtop).eventually hB.pos] with k hk hkfloor hkB
  have hfinite : ∀ᵐ ω ∂(P k).toMeasure, ∃ T, IsMarkTime ⌊b * q k⌋₊ ω T := by
    dsimp only [P]
    rw [coe_bridgeWalkLaw ((iidWalk_bridgeAtMark_ne_zero_iff μ hk).mpr (hq k))]
    exact (cond_absolutelyContinuous : ((iidWalk μ)[|bridgeAtMark (q k)]) ≪ iidWalk μ).ae_le
      ((ae_exists_markTime μ (hc.apply_zero_ne_zero hne)).mono fun ω hω => hω _)
  apply ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae ?_)
  filter_upwards [hfinite] with ω hω
  intro hdist
  by_contra hbad
  have hnear : |b * (markTime (q k) ω : ℝ) / markTime ⌊b * q k⌋₊ ω - 1| ≤ d := not_lt.mp hbad
  obtain ⟨T, hT⟩ := hω
  have hle : ⌊b * q k⌋₊ ≤ markTime ⌊b * q k⌋₊ ω := by
    rw [markTime_eq_of_isMarkTime hT, ← hT.1]
    unfold walkLeafCount
    exact (Finset.card_filter_le _ _).trans (by simp)
  have hL : 0 < markTime ⌊b * q k⌋₊ ω := by omega
  have hSraw : (1/2 : ℝ) ≤ b * (markTime (q k) ω : ℝ) / markTime ⌊b * q k⌋₊ ω := by
    have hdle : d ≤ 1/4 := min_le_left _ _
    have := (abs_le.mp hnear).1
    linarith
  have hfit : (b * (markTime (q k) ω : ℝ) / markTime ⌊b * q k⌋₊ ω) * a ≤ b := by
    have hdle : d ≤ (b - a) / (2 * a) := min_le_right _ _
    have hda := (le_div_iff₀ (show 0 < 2 * a by positivity)).mp hdle
    have := (abs_le.mp hnear).2
    nlinarith
  have heq := timeSpaceScale_leafClockPath_eq_restrict (μ 0).toReal B (q k) ha1.le hb ω hL hkB.ne' hSraw hfit
  change ε < dist (Skorokhod.restrict ha1.le (bridgeWalkPath B (q k) ω)) (G k ω) at hdist
  change G k ω = Skorokhod.restrict ha1.le (bridgeWalkPath B (q k) ω) at heq
  rw [heq, dist_self] at hdist
  exact (not_lt_of_ge hε.le) hdist

private theorem bridge_prefix_tendsto_zero {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ}
    (hθ : 1 < θ ∧ θ ≤ 2) (q : ℕ → ℕ) :
    Tendsto (fun k => (bridgeWalkLaw μ (q k)).map
        (Skorokhod.restrict (show (0 : ℝ) ≤ 1 by norm_num) ∘ bridgeWalkPath B (q k)))
      atTop (𝓝 ((stableBridgeLaw θ).map (Skorokhod.restrict (show (0 : ℝ) ≤ 1 by norm_num)))) := by
  let z : Skorokhod.D 0 ℝ := Skorokhod.restrict (show (0 : ℝ) ≤ 1 by norm_num)
    (Skorokhod.stepPath [] 1)
  have hsrc (n : ℕ) (ω : ℕ → ℕ) :
      Skorokhod.restrict (show (0 : ℝ) ≤ 1 by norm_num) (bridgeWalkPath B n ω) = z := by
    apply Skorokhod.ext
    intro t
    have ht : (t : ℝ) = 0 := le_antisymm t.2.2 t.2.1
    simp [Skorokhod.restrict, bridgeWalkPath, Skorokhod.stepPath, z, ht]
  have hdst : ∀ᵐ f ∂(stableBridgeLaw θ).toMeasure,
      Skorokhod.restrict (show (0 : ℝ) ≤ 1 by norm_num) f = z := by
    filter_upwards [stableBridgeLaw_endpoints hθ] with f hf
    apply Skorokhod.ext
    intro t
    have ht : (t : ℝ) = 0 := le_antisymm t.2.2 t.2.1
    have harg : (⟨(t : ℝ), t.2.1, t.2.2.trans zero_le_one⟩ : Set.Icc (0 : ℝ) 1) =
        ⟨0, le_rfl, zero_le_one⟩ := Subtype.ext ht
    change f ⟨t, t.2.1, t.2.2.trans zero_le_one⟩ = _
    rw [harg, hf.1]
    simp [z, Skorokhod.restrict, Skorokhod.stepPath]
  have heq (k : ℕ) : (bridgeWalkLaw μ (q k)).map
      (Skorokhod.restrict (show (0 : ℝ) ≤ 1 by norm_num) ∘ bridgeWalkPath B (q k)) =
      (stableBridgeLaw θ).map (Skorokhod.restrict (show (0 : ℝ) ≤ 1 by norm_num)) := by
    apply ProbabilityMeasure.toMeasure_injective
    rw [ProbabilityMeasure.toMeasure_map, ProbabilityMeasure.toMeasure_map]
    have hs := Measure.map_congr (mβ := inferInstance) (ae_of_all (bridgeWalkLaw μ (q k)).toMeasure (hsrc (q k)))
    have ht := Measure.map_congr (mβ := inferInstance) hdst
    simp only [Function.comp_def]
    rw [hs, ht]
    simp
  exact tendsto_const_nhds.congr fun k => (heq k).symm

/-- The leaf-clock bridge converges on every strict prefix of `[0,1]`. -/
theorem bridge_prefix_tendsto {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ} (hc : IsCritical μ)
    (hne : μ 1 ≠ 1) (hap : Aperiodic μ)
    (hB : IsRealStableAttracted (realOffspringStepLaw μ) θ B)
    {q : ℕ → ℕ}
    (hqtop : Tendsto q atTop atTop) (hq : ∀ k, LeafAdmissible μ (q k))
    {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) :
    Tendsto (fun k => (bridgeWalkLaw μ (q k)).map
        (Skorokhod.restrict ha1.le ∘ bridgeWalkPath B (q k)))
      atTop (𝓝 ((stableBridgeLaw θ).map (Skorokhod.restrict ha1.le))) := by
  rcases ha0.eq_or_lt with h | h
  · subst a
    exact bridge_prefix_tendsto_zero hB.index_mem q
  · exact bridge_prefix_tendsto_pos hc hne hap hB hqtop hq h ha1

/-- The stopped leaf-clock bridge converges on the whole interval. Prefix convergence is
combined with the independent terminal-reversal provider by C11b. -/
theorem tendsto_bridgeWalkPath {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ} (hc : IsCritical μ)
    (hne : μ 1 ≠ 1) (hap : Aperiodic μ)
    (hB : IsRealStableAttracted (realOffspringStepLaw μ) θ B)
    {q : ℕ → ℕ}
    (hqtop : Tendsto q atTop atTop) (hq : ∀ k, LeafAdmissible μ (q k)) :
    Tendsto (fun k => (bridgeWalkLaw μ (q k)).map (bridgeWalkPath B (q k)))
      atTop (𝓝 (stableBridgeLaw θ)) := by
  let a : ℕ → ℝ := fun j => 1 - 1 / ((j : ℝ) + 2)
  have ha0 (j : ℕ) : 0 ≤ a j := by
    dsimp [a]
    have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    have hd : 0 < (j : ℝ) + 2 := by positivity
    exact (sub_pos.mpr ((div_lt_one hd).mpr (by linarith))).le
  have ha1 (j : ℕ) : a j < 1 := by
    dsimp [a]
    exact sub_lt_self _ (by positivity)
  have halim : Tendsto a atTop (𝓝 1) := by
    have ht := (tendsto_const_nhds (x := (1 : ℝ))).sub
      ((tendsto_atTop_add_const_right atTop (2 : ℝ)
        tendsto_natCast_atTop_atTop).const_div_atTop (1 : ℝ))
    simpa only [sub_zero] using ht
  have hpre := fun (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s < 1) =>
    bridge_prefix_tendsto hc hne hap hB hqtop hq hs0 hs1
  exact Skorokhod.tendsto_of_tendsto_restrict_of_oscillation
    (fun k => bridgeWalkLaw μ (q k))
    (fun k => measurable_bridgeWalkPath B (q k)) zero_lt_one ha0 ha1 halim
    (fun j => hpre (a j) (ha0 j) (ha1 j))
    (stableBridgeLaw_ae_continuousAt hB.index_mem ⟨1, zero_le_one, le_rfl⟩)
    (LeafLimits.BridgeTerminal.bridge_terminal_oscillation_of_half hB hqtop hq (by norm_num : (1 / 2 : ℝ) ≤ 1)
      (hpre (1 / 2) (by norm_num) (by norm_num)) ha0 ha1 halim)


end BGWLeaves.LeafLimitsGeneral.FullBridgeLattice
