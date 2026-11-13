module

public import BGWLeaves.GeneralAFunctional.WalkBridgeClock
public import BGW.StableTrees.BridgeProjectiveClose
public import BGW.StableTrees.StableBridgeClosed
public import BGW.Skorokhod.Restrict

/-! General A-marked bridge convergence on every proper initial interval. -/

@[expose] public section
namespace BGWLeaves.GeneralAFunctional.WalkPrefix
open MeasureTheory ProbabilityTheory Filter BGW BGW.StableTrees BGW.LocallyFinite
open BGWLeaves.StableAnalysis BGWLeaves.LeafLimits.Bridge
open BGWLeaves.GeneralAFunctional.WalkCyclic BGWLeaves.GeneralAFunctional.WalkVervaat
open BGWLeaves.GeneralAFunctional.WalkFCLT
open BGWLeaves.GeneralAFunctional.Walk
open scoped ENNReal NNReal Topology

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

private theorem bridge_factors_error {μ : PMF ℕ} {A : Set ℕ} {θ : ℝ} {B : ℕ → ℝ}
    (hc : IsCritical μ) (hne : μ 1 ≠ 1) (hap : Aperiodic μ)
    (hB : IsRealStableAttracted (realOffspringStepLaw μ) θ B)
    {q : ℕ → ℕ}
    (hqtop : Tendsto q atTop atTop) (hq : ∀ k, ZetaAAdmissible μ A (q k))
    {b : ℝ} (hb : 0 < b) :
    ErrorConverges (fun k => Walk.aBridgeLaw μ A (q k))
      (fun k ω => B (leafNormIndex (μ.toMeasure A).toReal (q k)) / B (aMarkTime A (q k) ω)) 1 ∧
    ErrorConverges (fun k => Walk.aBridgeLaw μ A (q k))
      (fun k ω => b * (aMarkTime A (q k) ω : ℝ) / aMarkTime A ⌊b * q k⌋₊ ω) 1 := by
  have hmass := Walk.mark_mass_ne_zero_of_admissible_sequence hc hne hqtop hq
  let P := fun k => Walk.aBridgeLaw μ A (q k)
  have hp : 0 < (μ.toMeasure A).toReal := ENNReal.toReal_pos hmass (measure_ne_top _ _)
  have hDA := (stableDomain_of_isRealStableAttracted hc hne hB).1
  have hself : Tendsto (fun k => (q k : ℝ) / q k) atTop (𝓝 (1 : ℝ)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [hqtop.eventually_ne_atTop 0] with k hk
    simp [hk]
  have hfloor : Tendsto (fun k => (⌊b * q k⌋₊ : ℝ) / q k) atTop (𝓝 b) :=
    ((tendsto_nat_floor_mul_div_atTop (R := ℝ) hb.le).comp tendsto_natCast_atTop_atTop).comp hqtop
  have hfloorTop := tendsto_nat_of_ratio hb hqtop hfloor
  have hX : ErrorConverges P (fun k ω => (aMarkTime A (q k) ω : ℝ) / q k) (1 / (μ.toMeasure A).toReal) :=
    WalkBridgeClock.tendsto_bridge_markTime_ratio hc hne hap hDA hqtop hq zero_lt_one hself
  have hY : ErrorConverges P (fun k ω => (aMarkTime A ⌊b * q k⌋₊ ω : ℝ) / ⌊b * q k⌋₊)
      (1 / (μ.toMeasure A).toReal) :=
    WalkBridgeClock.tendsto_bridge_markTime_ratio hc hne hap hDA hqtop hq hb hfloor
  have hY' : ErrorConverges P (fun k ω => (aMarkTime A ⌊b * q k⌋₊ ω : ℝ) / q k)
      ((1 / (μ.toMeasure A).toReal) * b) := by
    apply error_congr_eventually (error_mul hY (error_const P hfloor))
    filter_upwards [hfloorTop.eventually_ne_atTop 0] with k hk
    intro ω
    exact div_mul_div_cancel₀ (by exact_mod_cast hk)
  have hR := error_norming_ratio hB hqtop (fun k => aMarkTime A (q k)) (one_div_pos.mpr hp) hX
  have hA := error_const P (hB.tendsto_norming_ratio (one_div_pos.mpr hp) hqtop
    ((leafNormIndex_ratio hp).comp hqtop))
  have hRpos : 0 < (1 / (μ.toMeasure A).toReal)^(1 / θ) := Real.rpow_pos_of_pos (one_div_pos.mpr hp) _
  constructor
  · have hK := error_div hA hR hRpos.ne'
    rw [div_self hRpos.ne'] at hK
    apply error_congr_eventually hK
    filter_upwards [hqtop.eventually hB.pos] with k hk
    intro ω
    exact div_div_div_cancel_right₀ hk.ne' _ _
  · have hS := error_div (error_mul (error_const P (tendsto_const_nhds (x := b))) hX)
      hY' (mul_ne_zero (one_div_ne_zero hp.ne') hb.ne')
    have heq : b * (1 / (μ.toMeasure A).toReal) / ((1 / (μ.toMeasure A).toReal) * b) = 1 := by field_simp
    rw [heq] at hS
    apply error_congr_eventually hS
    filter_upwards [hqtop.eventually_ne_atTop 0] with k hk
    intro ω
    rw [← mul_div_assoc, div_div_div_cancel_right₀ (show (q k : ℝ) ≠ 0 by exact_mod_cast hk)]

theorem bridgeWalkPath_apply (A : Set ℕ) (B : ℕ → ℝ) (n : ℕ) (ω : ℕ → ℕ) (t : Set.Icc (0 : ℝ) 1) :
    aBridgeWalkPath A B n ω t =
      (walkSum ω ⌊(aMarkTime A n ω : ℝ) * (t : ℝ)⌋₊ : ℝ) / B (aMarkTime A n ω) := by
  change (((walkWord ω (aMarkTime A n ω)).take
    ⌊((walkWord ω (aMarkTime A n ω)).length : ℝ) * (t : ℝ)⌋₊).sum : ℝ) / _ = _
  have hlen : (walkWord ω (aMarkTime A n ω)).length = aMarkTime A n ω := by simp [walkWord]
  rw [hlen, BGWLeaves.Vervaat.TimeReversal.sum_take_walkWord]
  exact Nat.floor_le_of_le (mul_le_of_le_one_right (Nat.cast_nonneg _) t.2.2)

noncomputable def bridgeClockFactor (A : Set ℕ) (b : ℝ) (n : ℕ) (ω : ℕ → ℕ) : Set.Ioi (0 : ℝ) :=
  ⟨max (b * (aMarkTime A n ω : ℝ) / aMarkTime A ⌊b * n⌋₊ ω) (1/2),
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1/2) (le_max_right _ _)⟩

theorem measurable_bridgeClockFactor (A : Set ℕ) (b : ℝ) (n : ℕ) :
    Measurable (fun ω => (bridgeClockFactor A b n ω : ℝ)) := by
  exact (measurable_const.mul ((measurable_of_countable (fun m : ℕ => (m : ℝ))).comp (measurable_aMarkTime A n)) |>.div
    ((measurable_of_countable (fun m : ℕ => (m : ℝ))).comp (measurable_aMarkTime A ⌊b * n⌋₊))).max measurable_const

theorem timeSpaceScale_leafClockPath_eq_restrict (A : Set ℕ) (p : ℝ) (B : ℕ → ℝ) (n : ℕ)
    {a b : ℝ} (ha1 : a ≤ 1) (hb : 0 < b) (ω : ℕ → ℕ)
    (hL : 0 < aMarkTime A ⌊b * n⌋₊ ω) (hB : B (leafNormIndex p n) ≠ 0)
    (hS : (1/2 : ℝ) ≤ b * (aMarkTime A n ω : ℝ) / aMarkTime A ⌊b * n⌋₊ ω)
    (hfit : (b * (aMarkTime A n ω : ℝ) / aMarkTime A ⌊b * n⌋₊ ω) * a ≤ b) :
    Skorokhod.timeSpaceScale a hb.le
      (aClockPath A p B n hb ω, B (leafNormIndex p n) / B (aMarkTime A n ω), bridgeClockFactor A b n ω) =
        Skorokhod.restrict ha1 (aBridgeWalkPath A B n ω) := by
  apply Skorokhod.ext
  intro t
  have hraw : 0 ≤ b * (aMarkTime A n ω : ℝ) / aMarkTime A ⌊b * n⌋₊ ω := by linarith
  have hbt : b * (aMarkTime A n ω : ℝ) / aMarkTime A ⌊b * n⌋₊ ω * (t : ℝ) ≤ b :=
    (mul_le_mul_of_nonneg_left t.2.2 hraw).trans hfit
  change (B (leafNormIndex p n) / B (aMarkTime A n ω)) *
      (1 * (BGW.Probability.RealWalk.partialSum (walkIncr ω)
        ⌊(aMarkTime A ⌊b * n⌋₊ ω : ℝ) * min (1 / b *
          min (max (b * (aMarkTime A n ω : ℝ) / aMarkTime A ⌊b * n⌋₊ ω) (1/2) * (t : ℝ)) b) 1⌋₊ /
          B (leafNormIndex p n))) =
    aBridgeWalkPath A B n ω ⟨t, t.2.1, t.2.2.trans ha1⟩
  rw [bridgeWalkPath_apply A, max_eq_left hS, min_eq_left hbt]
  have hinner : 1 / b * (b * (aMarkTime A n ω : ℝ) / aMarkTime A ⌊b * n⌋₊ ω * (t : ℝ)) ≤ 1 := by
    rw [one_div_mul_eq_div, div_le_one hb]
    exact hbt
  rw [min_eq_left hinner, one_mul, partialSum_walkIncr]
  have hclock : (aMarkTime A ⌊b * n⌋₊ ω : ℝ) *
      (1 / b * (b * (aMarkTime A n ω : ℝ) / aMarkTime A ⌊b * n⌋₊ ω * (t : ℝ))) =
        (aMarkTime A n ω : ℝ) * (t : ℝ) := by
    field_simp [hb.ne', show (aMarkTime A ⌊b * n⌋₊ ω : ℝ) ≠ 0 by exact_mod_cast hL.ne']
  rw [hclock]
  exact div_mul_div_cancel₀' hB _ _

/-- Prefix convergence on a strictly positive horizon. The marked prefix is first taken at
`b > a`; Lemma 5.7 is then used with the factor `b T_n / T_(bn)`. -/
theorem bridge_prefix_tendsto_pos {μ : PMF ℕ} {A : Set ℕ} {θ : ℝ} {B : ℕ → ℝ} (hc : IsCritical μ)
    (hne : μ 1 ≠ 1) (hap : Aperiodic μ)
    (hB : IsRealStableAttracted (realOffspringStepLaw μ) θ B)
    {q : ℕ → ℕ}
    (hqtop : Tendsto q atTop atTop) (hq : ∀ k, ZetaAAdmissible μ A (q k))
    {a : ℝ} (ha : 0 < a) (ha1 : a < 1) :
    Tendsto (fun k => (Walk.aBridgeLaw μ A (q k)).map
        (Skorokhod.restrict ha1.le ∘ aBridgeWalkPath A B (q k)))
      atTop (𝓝 ((stableBridgeLaw θ).map (Skorokhod.restrict ha1.le))) := by
  classical
  have hmass := Walk.mark_mass_ne_zero_of_admissible_sequence hc hne hqtop hq
  obtain ⟨b, hab, hb1⟩ := exists_between ha1
  have hb : 0 < b := ha.trans hab
  have hp : 0 < (μ.toMeasure A).toReal := ENNReal.toReal_pos hmass (measure_ne_top _ _)
  let P := fun k => Walk.aBridgeLaw μ A (q k)
  let Z := fun k => aClockPath A (μ.toMeasure A).toReal B (q k) hb
  let K := fun k ω => B (leafNormIndex (μ.toMeasure A).toReal (q k)) / B (aMarkTime A (q k) ω)
  let S := fun k => bridgeClockFactor A b (q k)
  let L := (stableBridgeLaw θ).map (Skorokhod.restrict hb1.le)
  let G := fun k ω => Skorokhod.timeSpaceScale a hb.le (Z k ω, K k ω, S k ω)
  have hZm : ∀ k, Measurable (Z k) := fun k => measurable_aClockPath A _ _ _ _
  have hKm : ∀ k, Measurable (K k) := fun k =>
    measurable_const.div ((measurable_of_countable B).comp (measurable_aMarkTime A (q k)))
  have hSm : ∀ k, Measurable (fun ω => (S k ω : ℝ)) := fun k => measurable_bridgeClockFactor A _ _
  have hGm : ∀ k, Measurable (G k) := fun k =>
    (measurable_timeSpaceScale a hb.le).comp
      ((hZm k).prodMk ((hKm k).prodMk (hSm k).subtype_mk))
  have hZ : Tendsto (fun k => (P k).map (Z k)) atTop (𝓝 L) :=
    WalkBridgeClock.tendsto_leafClockPath_bridge hc hne hap hB hqtop hq hb hb1
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
    (fun k => (Skorokhod.measurable_restrict _).comp (measurable_aBridgeWalkPath A B (q k)))
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
  have hfinite : ∀ᵐ ω ∂(P k).toMeasure, ∃ T, IsAMarkTime A ⌊b * q k⌋₊ ω T := by
    dsimp only [P]
    rw [Walk.coe_aBridgeLaw hk (hq k)]
    exact (cond_absolutelyContinuous : ((iidWalk μ)[|bridgeAtAMark A (q k)]) ≪ iidWalk μ).ae_le
      ((WalkClock.ae_exists_aMarkTime μ A hmass).mono fun ω hω => hω _)
  apply ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae ?_)
  filter_upwards [hfinite] with ω hω
  intro hdist
  by_contra hbad
  have hnear : |b * (aMarkTime A (q k) ω : ℝ) / aMarkTime A ⌊b * q k⌋₊ ω - 1| ≤ d := not_lt.mp hbad
  obtain ⟨T, hT⟩ := hω
  have hle : ⌊b * q k⌋₊ ≤ aMarkTime A ⌊b * q k⌋₊ ω := by
    rw [aMarkTime_eq hT, ← hT.1]
    unfold walkACount
    exact (Finset.card_filter_le _ _).trans (by simp)
  have hL : 0 < aMarkTime A ⌊b * q k⌋₊ ω := by omega
  have hSraw : (1/2 : ℝ) ≤ b * (aMarkTime A (q k) ω : ℝ) / aMarkTime A ⌊b * q k⌋₊ ω := by
    have hdle : d ≤ 1/4 := min_le_left _ _
    have := (abs_le.mp hnear).1
    linarith
  have hfit : (b * (aMarkTime A (q k) ω : ℝ) / aMarkTime A ⌊b * q k⌋₊ ω) * a ≤ b := by
    have hdle : d ≤ (b - a) / (2 * a) := min_le_right _ _
    have hda := (le_div_iff₀ (show 0 < 2 * a by positivity)).mp hdle
    have := (abs_le.mp hnear).2
    nlinarith
  have heq := timeSpaceScale_leafClockPath_eq_restrict A (μ.toMeasure A).toReal B (q k) ha1.le hb ω hL hkB.ne' hSraw hfit
  change ε < dist (Skorokhod.restrict ha1.le (aBridgeWalkPath A B (q k) ω)) (G k ω) at hdist
  change G k ω = Skorokhod.restrict ha1.le (aBridgeWalkPath A B (q k) ω) at heq
  rw [heq, dist_self] at hdist
  exact (not_lt_of_ge hε.le) hdist

private theorem bridge_prefix_tendsto_zero {μ : PMF ℕ} {A : Set ℕ} {θ : ℝ} {B : ℕ → ℝ}
    (hθ : 1 < θ ∧ θ ≤ 2) (q : ℕ → ℕ) :
    Tendsto (fun k => (Walk.aBridgeLaw μ A (q k)).map
        (Skorokhod.restrict (show (0 : ℝ) ≤ 1 by norm_num) ∘ aBridgeWalkPath A B (q k)))
      atTop (𝓝 ((stableBridgeLaw θ).map (Skorokhod.restrict (show (0 : ℝ) ≤ 1 by norm_num)))) := by
  let z : Skorokhod.D 0 ℝ := Skorokhod.restrict (show (0 : ℝ) ≤ 1 by norm_num)
    (Skorokhod.stepPath [] 1)
  have hsrc (n : ℕ) (ω : ℕ → ℕ) :
      Skorokhod.restrict (show (0 : ℝ) ≤ 1 by norm_num) (aBridgeWalkPath A B n ω) = z := by
    apply Skorokhod.ext
    intro t
    have ht : (t : ℝ) = 0 := le_antisymm t.2.2 t.2.1
    simp [Skorokhod.restrict, aBridgeWalkPath, Skorokhod.stepPath, z, ht]
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
  have heq (k : ℕ) : (Walk.aBridgeLaw μ A (q k)).map
      (Skorokhod.restrict (show (0 : ℝ) ≤ 1 by norm_num) ∘ aBridgeWalkPath A B (q k)) =
      (stableBridgeLaw θ).map (Skorokhod.restrict (show (0 : ℝ) ≤ 1 by norm_num)) := by
    apply ProbabilityMeasure.toMeasure_injective
    rw [ProbabilityMeasure.toMeasure_map, ProbabilityMeasure.toMeasure_map]
    have hs := Measure.map_congr (mβ := inferInstance) (ae_of_all (Walk.aBridgeLaw μ A (q k)).toMeasure (hsrc (q k)))
    have ht := Measure.map_congr (mβ := inferInstance) hdst
    simp only [Function.comp_def]
    rw [hs, ht]
    simp
  exact tendsto_const_nhds.congr fun k => (heq k).symm

/-- The leaf-clock bridge converges on every strict prefix of `[0,1]`. -/
theorem aBridge_prefix_tendsto_core {μ : PMF ℕ} {A : Set ℕ} {θ : ℝ} {B : ℕ → ℝ} (hc : IsCritical μ)
    (hne : μ 1 ≠ 1) (hap : Aperiodic μ)
    (hB : IsRealStableAttracted (realOffspringStepLaw μ) θ B)
    {q : ℕ → ℕ}
    (hqtop : Tendsto q atTop atTop) (hq : ∀ k, ZetaAAdmissible μ A (q k))
    {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) :
    Tendsto (fun k => (Walk.aBridgeLaw μ A (q k)).map
        (Skorokhod.restrict ha1.le ∘ aBridgeWalkPath A B (q k)))
      atTop (𝓝 ((stableBridgeLaw θ).map (Skorokhod.restrict ha1.le))) := by
  rcases ha0.eq_or_lt with h | h
  · subst a
    exact bridge_prefix_tendsto_zero (A := A) hB.index_mem q
  · exact bridge_prefix_tendsto_pos hc hne hap hB hqtop hq h ha1

/-- (P_A) prefix convergence of the A-marked bridge path on `[0,a]`, `0 ≤ a < 1`. -/
theorem aBridge_prefix_tendsto {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ} {A : Set ℕ} (hA : A.Nonempty)
    (hc : IsCritical μ) (hne : μ 1 ≠ 1) (hap : Aperiodic μ)
    (hB : IsRealStableAttracted (realOffspringStepLaw μ) θ B)
    (hAfin : ¬ Integrable (fun z : ℤ => (z : ℝ) ^ 2) (stepLaw μ) → A.Finite ∨ Aᶜ.Finite)
    {q : ℕ → ℕ} (hqtop : Tendsto q atTop atTop) (hq : ∀ k, ZetaAAdmissible μ A (q k))
    {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) :
    Tendsto (fun k => (aBridgeLaw μ A (q k)).map
        (Skorokhod.restrict ha1.le ∘ aBridgeWalkPath A B (q k)))
      atTop (𝓝 ((stableBridgeLaw θ).map (Skorokhod.restrict ha1.le))) := by
  exact aBridge_prefix_tendsto_core hc hne hap hB hqtop hq ha0 ha1


end BGWLeaves.GeneralAFunctional.WalkPrefix
