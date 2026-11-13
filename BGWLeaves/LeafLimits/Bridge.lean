module

public import BGWLeaves.LeafLimits.Defs
public import BGWLeaves.LeafLimits.BridgeTerminal
public import BGW.Skorokhod.Prefix
public import BGWLeaves.Conditioning
public import BGWLeaves.LocalEstimates
public import BGWLeaves.Vervaat
public import BGWLeaves.Vervaat.TimeReversal
public import BGWLeaves.ClassicalLimits.Cited
public import BGWLeaves.ClassicalLimits.Perturbation
public import BGWLeaves.ClassicalLimits.WalkClock
public import BGW.Probability.SkorokhodRepresentation
public import BGW.Probability.Rounding
public import Mathlib.MeasureTheory.Measure.Portmanteau
public import BGWLeaves.LeafConcentration.OeLemmas

/-!
# M13 provider `Bridge`

The bridge invariance principle inside Theorem 6.1, for arbitrary admissible normings.
Lemma 6.10 gives the exact stopped-prefix density. The signed local estimate 6.11 and regular
variation identify its moving-endpoint limit; Fatou and open-set portmanteau remove the cut-offs
without atom choices, since all tilted laws are probability measures. Polynomial control of the
conditioning denominator transfers exponential clock concentration to the bridge laws.

For a target prefix `a`, Lemma 5.7 is applied first at `b > a`, with the time factor
`b T_n/T_(bn)` and a positive modification off the good event. The whole-interval result combines
these prefixes with the independent `BridgeTerminal` provider by C11b.
-/

@[expose] public section

namespace BGWLeaves.LeafLimits.Bridge

open MeasureTheory ProbabilityTheory Filter BGW
open BGW.StableTrees BGW.LocallyFinite BGWLeaves.StableAnalysis
open scoped ENNReal NNReal Topology

/-- A witness of the first mark time determines the extended-valued clock. -/
theorem walkLeafTime_eq_of_isMarkTime {n m : ℕ} {ω : ℕ → ℕ} (hm : IsMarkTime n ω m) :
    walkLeafTime ω n = (m : ℕ∞) := by
  unfold walkLeafTime
  apply le_antisymm
  · exact iInf₂_le m hm.1
  · refine le_iInf₂ fun q hq => ?_
    have hmq : m ≤ q := by
      by_contra h
      have := hm.2 q (not_le.mp h)
      omega
    exact_mod_cast hmq

/-- The natural-valued clock agrees with any witness of the first mark time. -/
theorem markTime_eq_of_isMarkTime {n m : ℕ} {ω : ℕ → ℕ} (hm : IsMarkTime n ω m) :
    markTime n ω = m := by
  simp [markTime, walkLeafTime_eq_of_isMarkTime hm]

/-- The two encodings of the stopped bridge event agree, including the finite-clock condition. -/
theorem bridgeAtMark_eq_walkStopEvent (n : ℕ) : bridgeAtMark n = walkStopEvent n (-1) := by
  ext ω
  constructor
  · rintro ⟨m, hm, hs⟩
    refine ⟨?_, ?_⟩
    · rw [walkLeafTime_eq_of_isMarkTime hm]
      exact ENat.natCast_ne_top m
    · simpa [walkStopPos, walkLeafTime_eq_of_isMarkTime hm] using hs
  · rintro ⟨hfinite, hs⟩
    have hex : ∃ m, IsMarkTime n ω m := by
      by_contra h
      apply hfinite
      have h' : ¬ ∃ m, walkLeafCount ω m = n := by
        rwa [← exists_isMarkTime_iff]
      unfold walkLeafTime
      simp only [iInf_eq_top]
      intro m hm
      exact (h' ⟨m, hm⟩).elim
    obtain ⟨m, hm⟩ := hex
    refine ⟨m, hm, ?_⟩
    simpa [walkStopPos, walkLeafTime_eq_of_isMarkTime hm] using hs

/-- Lemma 6.10 under the actual probability law used by the invariance principle. -/
theorem lintegral_bridgeWalkLaw_stopPath {μ : PMF ℕ} (h0 : μ 0 ≠ 0) {n k : ℕ}
    (hn : 1 ≤ n) (hadm : LeafAdmissible μ n) (hkn : k < n) (f : List ℤ → ℝ≥0∞) :
    ∫⁻ ω, f (walkStopPath ω k) ∂(bridgeWalkLaw μ n).toMeasure =
      ∫⁻ ω, f (walkStopPath ω k) * (chi μ (n - k) (walkStopPos ω k) / chi μ n 0)
        ∂iidWalk μ := by
  rw [coe_bridgeWalkLaw ((iidWalk_bridgeAtMark_ne_zero_iff μ hn).mpr hadm),
    bridgeAtMark_eq_walkStopEvent]
  exact lem_absolueC2_k h0 hkn f

/-- On the conditioning event, at least `n` increments have been read. -/
theorem le_markTime_of_bridgeAtMark {n : ℕ} {ω : ℕ → ℕ} (hω : ω ∈ bridgeAtMark n) :
    n ≤ markTime n ω := by
  obtain ⟨m, hm, -⟩ := hω
  rw [markTime_eq_of_isMarkTime hm, ← hm.1]
  unfold walkLeafCount
  exact (Finset.card_filter_le _ _).trans (by simp)

/-- The lower bound on the stopped clock also holds under its probability law. -/
theorem ae_le_markTime {μ : PMF ℕ} {n : ℕ} (hn : 1 ≤ n) (hadm : LeafAdmissible μ n) :
    ∀ᵐ ω ∂(bridgeWalkLaw μ n).toMeasure, n ≤ markTime n ω := by
  rw [coe_bridgeWalkLaw ((iidWalk_bridgeAtMark_ne_zero_iff μ hn).mpr hadm)]
  filter_upwards [ae_cond_mem (measurableSet_bridgeAtMark n)] with ω hω
  exact le_markTime_of_bridgeAtMark hω

/-- Altering finitely many norming values leaves the stopped path laws eventually unchanged.
The clock lower bound is used only on the conditioning event, avoiding its junk value at infinity. -/
theorem eventually_map_bridgeWalkPath_eq {μ : PMF ℕ} {B B' : ℕ → ℝ}
    (hBB' : ∀ᶠ n in atTop, B n = B' n) {q : ℕ → ℕ}
    (hqtop : Tendsto q atTop atTop) (hq : ∀ k, LeafAdmissible μ (q k)) :
    ∀ᶠ k in atTop, (bridgeWalkLaw μ (q k)).map (bridgeWalkPath B (q k)) =
      (bridgeWalkLaw μ (q k)).map (bridgeWalkPath B' (q k)) := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp hBB'
  filter_upwards [hqtop.eventually_ge_atTop (max N 1)] with k hk
  apply ProbabilityMeasure.toMeasure_injective
  rw [ProbabilityMeasure.toMeasure_map, ProbabilityMeasure.toMeasure_map]
  apply Measure.map_congr
  filter_upwards [ae_le_markTime (by omega) (hq k)] with ω hω
  unfold bridgeWalkPath
  rw [hN _ (by omega)]

/-- The terminal value is the final step `-1`, rather than zero. -/
theorem bridgeWalkPath_one {B : ℕ → ℝ} {n : ℕ} {ω : ℕ → ℕ}
    (hω : ω ∈ bridgeAtMark n) :
    bridgeWalkPath B n ω ⟨1, zero_le_one, le_rfl⟩ = -1 / B (markTime n ω) := by
  obtain ⟨m, hm, hs⟩ := hω
  rw [bridgeWalkPath, markTime_eq_of_isMarkTime hm]
  change (((walkWord ω m).take ⌊((walkWord ω m).length : ℝ) * 1⌋₊).sum : ℝ) / B m = _
  simp only [mul_one, Nat.floor_natCast, List.take_length, sum_walkWord, hs, Int.cast_neg,
    Int.cast_one]

/-- Before the last downward step, the bridge has sum zero and exactly `n-1` marks.
This is the event to which Proposition 6.8 applies; the full stopped word is not reversed. -/
theorem bridgeAtMark_last_step {n m : ℕ} {ω : ℕ → ℕ} (_hn : 1 ≤ n)
    (hm : IsMarkTime n ω (m + 1)) (hs : walkSum ω (m + 1) = -1) :
    ω m = 0 ∧ ω ∈ timeReversalEvent m (n - 1) := by
  have hcount : walkLeafCount ω (m + 1) =
      walkLeafCount ω m + if ω m = 0 then 1 else 0 := by
    unfold walkLeafCount
    rw [Finset.card_filter, Finset.card_filter, Finset.sum_range_succ]
    by_cases h : ω m = 0 <;> simp [h]
  have hmark := hm.1
  have hlt := hm.2 m (Nat.lt_succ_self m)
  have hzero : ω m = 0 := by
    by_contra h
    simp only [h, ↓reduceIte, add_zero] at hcount
    omega
  refine ⟨hzero, ?_, ?_⟩
  · have hsum : walkSum ω (m + 1) = walkSum ω m + ((ω m : ℤ) - 1) := by
      unfold walkSum
      rw [Finset.sum_range_succ]
    rw [hzero] at hsum
    omega
  · simp only [hzero, ↓reduceIte] at hcount
    omega

/-- Signed local convergence along a bounded sequence of rescaled endpoints, in the canonical
norming. This is the analytic input to the cut-off Radon–Nikodym argument. -/
theorem tendsto_scaled_chi {μ : PMF ℕ} {θ : ℝ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hap : Aperiodic μ) (hDA : ∃ a, StableDomain μ θ a)
    (hnl : ¬ IsLatticeLaw (etaLaw μ)) {q : ℕ → ℕ}
    (hqtop : Tendsto q atTop atTop) {j : ℕ → ℤ} {α x : ℝ} (hα : 0 < α)
    (hj : ∀ᶠ k in atTop, |(j k : ℝ)| ≤ α * normB μ θ (q k))
    (hx : Tendsto (fun k => (j k : ℝ) / normB μ θ ((q k : ℝ) / (μ 0).toReal))
      atTop (𝓝 x)) :
    Tendsto (fun k => normB μ θ ((q k : ℝ) / (μ 0).toReal) * (chi μ (q k) (j k)).toReal)
      atTop (𝓝 (Scalar.stableDensity θ (-x))) := by
  obtain ⟨a, ha⟩ := hDA
  have hd := ((Scalar.continuous_stableDensity ha.alpha_mem).tendsto (-x)).comp hx.neg
  have he : Tendsto (fun k =>
      normB μ θ ((q k : ℝ) / (μ 0).toReal) * (chi μ (q k) (j k)).toReal -
        Scalar.stableDensity θ (-((j k : ℝ) / normB μ θ ((q k : ℝ) / (μ 0).toReal))))
      atTop (𝓝 0) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N, hN⟩ := lem_technic3 hc hne hap ⟨a, ha⟩ hnl hα (half_pos hε)
    rw [← eventually_atTop]
    filter_upwards [hqtop.eventually_ge_atTop N, hj] with k hk hjk
    rw [Real.dist_eq, sub_zero]
    exact (hN (q k) hk (j k) hjk).trans_lt (half_lt_self hε)
  simpa only [Function.comp_def, zero_add, sub_add_cancel] using he.add hd

/-- The final downward step vanishes uniformly almost surely along admissible leaf counts.
This handles the endpoint `1` separately from the open terminal window in the reversal estimate. -/
theorem eventually_ae_bridgeWalkPath_one_lt {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ}
    (hB : IsRealStableAttracted (realOffspringStepLaw μ) θ B) {q : ℕ → ℕ}
    (hqtop : Tendsto q atTop atTop) (hq : ∀ k, LeafAdmissible μ (q k))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k in atTop, ∀ᵐ ω ∂(bridgeWalkLaw μ (q k)).toMeasure,
      |bridgeWalkPath B (q k) ω ⟨1, zero_le_one, le_rfl⟩| < ε := by
  have hlim : Tendsto (fun m => (-1 : ℝ) / B m) atTop (𝓝 0) :=
    hB.tendsto_norming_atTop.const_div_atTop (-1)
  have he : ∀ᶠ m in atTop, |(-1 : ℝ) / B m| < ε := by
    simpa only [Real.dist_eq, sub_zero] using hlim.eventually (Metric.ball_mem_nhds 0 hε)
  obtain ⟨N, hN⟩ := eventually_atTop.mp he
  filter_upwards [hqtop.eventually_ge_atTop (max N 1)] with k hk
  rw [coe_bridgeWalkLaw ((iidWalk_bridgeAtMark_ne_zero_iff μ (by omega)).mpr (hq k))]
  filter_upwards [ae_cond_mem (measurableSet_bridgeAtMark (q k))] with ω hω
  rw [bridgeWalkPath_one hω]
  exact hN _ (le_trans (by omega) (le_markTime_of_bridgeAtMark hω))

/-- Ratio form of the signed local estimate at two growing mark counts. -/
theorem tendsto_chi_ratio {μ : PMF ℕ} {θ : ℝ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hap : Aperiodic μ) (hDA : ∃ a, StableDomain μ θ a)
    (hnl : ¬ IsLatticeLaw (etaLaw μ)) {q r : ℕ → ℕ}
    (hqtop : Tendsto q atTop atTop) (hrtop : Tendsto r atTop atTop)
    {j : ℕ → ℤ} {α x c : ℝ} (hα : 0 < α) (hc0 : c ≠ 0)
    (hj : ∀ᶠ k in atTop, |(j k : ℝ)| ≤ α * normB μ θ (r k))
    (hx : Tendsto (fun k => (j k : ℝ) / normB μ θ ((r k : ℝ) / (μ 0).toReal))
      atTop (𝓝 x))
    (hratio : Tendsto (fun k => normB μ θ ((q k : ℝ) / (μ 0).toReal) /
        normB μ θ ((r k : ℝ) / (μ 0).toReal)) atTop (𝓝 c)) :
    Tendsto (fun k => (chi μ (r k) (j k)).toReal / (chi μ (q k) 0).toReal)
      atTop (𝓝 (c * (Scalar.stableDensity θ (-x) / Scalar.stableDensity θ 0))) := by
  obtain ⟨a, ha⟩ := hDA
  have hp : Scalar.stableDensity θ 0 ≠ 0 := (Scalar.stableDensity_zero_pos ha.alpha_mem).ne'
  have hnum := tendsto_scaled_chi hc hne hap ⟨a, ha⟩ hnl hrtop hα hj hx
  have hden : Tendsto (fun k => normB μ θ ((q k : ℝ) / (μ 0).toReal) *
      (chi μ (q k) 0).toReal) atTop (𝓝 (Scalar.stableDensity θ 0)) := by
    have ht := ((chi_zero_asymp hc hne hap ⟨a, ha⟩ hnl).comp hqtop).mul_const
      (Scalar.stableDensity θ 0)
    simpa only [Function.comp_def, div_mul_cancel₀ _ hp, one_mul] using ht
  have ht := hratio.mul (hnum.div hden hp)
  apply ht.congr'
  filter_upwards [hden.eventually_ne hp, hratio.eventually_ne hc0] with k hkden hkratio
  have hqB : normB μ θ ((q k : ℝ) / (μ 0).toReal) ≠ 0 :=
    (mul_ne_zero_iff.mp hkden).1
  have hrB : normB μ θ ((r k : ℝ) / (μ 0).toReal) ≠ 0 :=
    (div_ne_zero_iff.mp hkratio).2
  have hχ : (chi μ (q k) 0).toReal ≠ 0 := (mul_ne_zero_iff.mp hkden).2
  simp only [Pi.div_apply]
  field_simp [hqB, hrB, hχ]

/-- Splitting a stopped bridge at its last step yields precisely the fixed-length event
on which time reversal is valid. -/
theorem bridgeAtMark_succ_iff {n m : ℕ} {ω : ℕ → ℕ} (hn : 1 ≤ n) :
    (IsMarkTime n ω (m + 1) ∧ walkSum ω (m + 1) = -1) ↔
      (ω m = 0 ∧ ω ∈ timeReversalEvent m (n - 1)) := by
  constructor
  · rintro ⟨hm, hs⟩
    exact bridgeAtMark_last_step hn hm hs
  · rintro ⟨hzero, hs, hc⟩
    have hcount : walkLeafCount ω (m + 1) = walkLeafCount ω m + 1 := by
      unfold walkLeafCount
      rw [Finset.card_filter, Finset.card_filter, Finset.sum_range_succ]
      simp [hzero]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · omega
    · intro q hq
      have hle : walkLeafCount ω q ≤ walkLeafCount ω m := by
        unfold walkLeafCount
        exact Finset.card_le_card (Finset.filter_subset_filter _
          (Finset.range_mono (by omega)))
      omega
    · have hsum : walkSum ω (m + 1) = walkSum ω m + ((ω m : ℤ) - 1) := by
        unfold walkSum
        rw [Finset.sum_range_succ]
      simp [hsum, hs, hzero]

theorem partialSum_walkIncr (ω : ℕ → ℕ) (m : ℕ) :
    BGW.Probability.RealWalk.partialSum (walkIncr ω) m = (walkSum ω m : ℝ) := by
  simp [BGW.Probability.RealWalk.partialSum, walkIncr, walkSum, Int.cast_sum]

theorem walkStopPath_getD (ω : ℕ → ℕ) (k i : ℕ) (hi : i ≤ markTime k ω) :
    (walkStopPath ω k).getD i 0 = walkSum ω i := by
  unfold walkStopPath
  rw [List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range (show i < (walkLeafTime ω k).toNat + 1 by exact Nat.lt_succ_of_le hi)]
  rfl

theorem leafClockPath_apply_stopPath (p : ℝ) (B : ℕ → ℝ) (n : ℕ) {a : ℝ} (ha : 0 < a)
    (ω : ℕ → ℕ) (t : Set.Icc (0 : ℝ) a) :
    leafClockPath p B n ha ω t =
      (((walkStopPath ω ⌊a * n⌋₊).getD
        ⌊(leafClock ω (a * n) : ℝ) * min (1 / a * (t : ℝ)) 1⌋₊ 0 : ℤ) : ℝ) /
          B ⌊(n : ℝ) / p⌋₊ := by
  change 1 * (BGW.Probability.RealWalk.partialSum (walkIncr ω) _ / _) = _
  rw [one_mul, partialSum_walkIncr, walkStopPath_getD]
  apply Nat.floor_le_of_le
  exact mul_le_of_le_one_right (Nat.cast_nonneg _) (min_le_right _ _)

theorem leafClockPath_eq_of_walkStopPath_eq (p : ℝ) (B : ℕ → ℝ) (n : ℕ)
    {a : ℝ} (ha : 0 < a) {ω ω' : ℕ → ℕ}
    (h : walkStopPath ω ⌊a * n⌋₊ = walkStopPath ω' ⌊a * n⌋₊) :
    leafClockPath p B n ha ω = leafClockPath p B n ha ω' := by
  have hl := congrArg List.length h
  simp only [walkStopPath, List.length_map, List.length_range] at hl
  have hm : leafClock ω (a * n) = leafClock ω' (a * n) := Nat.add_right_cancel hl
  apply Skorokhod.ext
  intro t
  rw [leafClockPath_apply_stopPath, leafClockPath_apply_stopPath, h, hm]

theorem exists_leafClockPath_eq_comp_stopPath (p : ℝ) (B : ℕ → ℝ) (n : ℕ)
    {a : ℝ} (ha : 0 < a) :
    ∃ F : List ℤ → Skorokhod.D a ℝ, ∀ ω,
      F (walkStopPath ω ⌊a * n⌋₊) = leafClockPath p B n ha ω := by
  classical
  let F : List ℤ → Skorokhod.D a ℝ := fun z =>
    if hz : ∃ ω, walkStopPath ω ⌊a * n⌋₊ = z then
      leafClockPath p B n ha (Classical.choose hz)
    else leafClockPath p B n ha (fun _ => 0)
  refine ⟨F, fun ω => ?_⟩
  dsimp only [F]
  rw [dite_eq_left (show ∃ ω', walkStopPath ω' ⌊a * n⌋₊ = walkStopPath ω ⌊a * n⌋₊ from ⟨ω, rfl⟩)]
  exact leafClockPath_eq_of_walkStopPath_eq p B n ha (Classical.choose_spec (show ∃ ω', walkStopPath ω' ⌊a * n⌋₊ = walkStopPath ω ⌊a * n⌋₊ from ⟨ω, rfl⟩))

theorem lintegral_bridgeWalkLaw_leafClockPath {μ : PMF ℕ} (h0 : μ 0 ≠ 0)
    {n : ℕ} (hn : 1 ≤ n) (hadm : LeafAdmissible μ n) {a : ℝ}
    (ha : 0 < a) (ha1 : a < 1) (p : ℝ) (B : ℕ → ℝ)
    (g : Skorokhod.D a ℝ → ℝ≥0∞) :
    ∫⁻ ω, g (leafClockPath p B n ha ω) ∂(bridgeWalkLaw μ n).toMeasure =
      ∫⁻ ω, g (leafClockPath p B n ha ω) *
        (chi μ (n - ⌊a * n⌋₊) (walkStopPos ω ⌊a * n⌋₊) / chi μ n 0) ∂iidWalk μ := by
  obtain ⟨F, hF⟩ := exists_leafClockPath_eq_comp_stopPath p B n ha
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hkn : ⌊a * n⌋₊ < n := (Nat.floor_lt (by positivity)).mpr (by nlinarith)
  simpa only [Function.comp_def, hF] using lintegral_bridgeWalkLaw_stopPath h0 hn hadm hkn (g ∘ F)

theorem leafClockPath_end (p : ℝ) (B : ℕ → ℝ) (n : ℕ) {a : ℝ} (ha : 0 < a)
    (ω : ℕ → ℕ) :
    leafClockPath p B n ha ω ⟨a, ha.le, le_rfl⟩ =
      (walkStopPos ω ⌊a * n⌋₊ : ℝ) / B ⌊(n : ℝ) / p⌋₊ := by
  change 1 * (BGW.Probability.RealWalk.partialSum (walkIncr ω)
    ⌊(leafClock ω (a * n) : ℝ) * min (1 / a * a) 1⌋₊ / _) = _
  rw [one_div_mul_cancel ha.ne', min_self, mul_one, Nat.floor_natCast,
    partialSum_walkIncr, one_mul]
  rfl


/-- Nonnegative change of density preserves weak convergence when the densities converge
along convergent path sequences. Normalization of the probability laws prevents loss of mass.
Fatou and the open-set portmanteau criterion perform the cut-off removal without atom choices. -/
theorem tendsto_reweighted {S : Type*} [MetricSpace S] [PolishSpace S]
    [MeasurableSpace S] [BorelSpace S] {P R : ℕ → ProbabilityMeasure S}
    {Q L : ProbabilityMeasure S} (hP : Tendsto P atTop (𝓝 Q))
    (w : ℕ → S → ℝ≥0∞) (v : S → ℝ≥0∞)
    (hw : ∀ n, Measurable (w n)) (hv : Measurable v)
    (hR : ∀ᶠ n in atTop, (R n).toMeasure = (P n).toMeasure.withDensity (w n))
    (hL : L.toMeasure = Q.toMeasure.withDensity v)
    (hweight : ∀ (x : ℕ → S) (y : S), Tendsto x atTop (𝓝 y) →
      Tendsto (fun n => w n (x n)) atTop (𝓝 (v y))) :
    Tendsto R atTop (𝓝 L) := by
  classical
  obtain ⟨X, Y, hXm, hYm, hXlaw, hYlaw, hXY⟩ :=
    BGW.Probability.exists_tendsto_ae_of_tendsto hP
  apply MeasureTheory.tendsto_of_forall_isOpen_le_liminf_nat'
  intro G hG
  let f : ℕ → unitInterval → ℝ≥0∞ := fun n ω => G.indicator (w n) (X n ω)
  let g : unitInterval → ℝ≥0∞ := fun ω => G.indicator v (Y ω)
  have hfm (n : ℕ) : Measurable (f n) :=
    ((hw n).indicator hG.measurableSet).comp (hXm n)
  have hpoint : ∀ᵐ ω ∂(volume : Measure unitInterval),
      g ω ≤ liminf (fun n => f n ω) atTop := by
    filter_upwards [hXY] with ω hω
    by_cases hy : Y ω ∈ G
    · have he : ∀ᶠ n in atTop, X n ω ∈ G := hω.eventually (hG.mem_nhds hy)
      have ht := (hweight (fun n => X n ω) (Y ω) hω).congr'
        (he.mono fun n hn => (Set.indicator_of_mem hn (w n)).symm)
      simpa only [g, Set.indicator_of_mem hy] using ht.liminf_eq.ge
    · simp only [g, Set.indicator_of_notMem hy, zero_le]
  have hsrc : ∀ᶠ n in atTop, (∫⁻ ω, f n ω ∂(volume : Measure unitInterval)) = (R n).toMeasure G := by
    filter_upwards [hR] with n hn
    rw [hn, withDensity_apply _ hG.measurableSet, ← lintegral_indicator hG.measurableSet,
      ← hXlaw n, lintegral_map ((hw n).indicator hG.measurableSet) (hXm n)]
  have htgt : (∫⁻ ω, g ω ∂(volume : Measure unitInterval)) = L.toMeasure G := by
    rw [hL, withDensity_apply _ hG.measurableSet, ← lintegral_indicator hG.measurableSet,
      ← hYlaw, lintegral_map (hv.indicator hG.measurableSet) hYm]
  calc
    L.toMeasure G = ∫⁻ ω, g ω ∂(volume : Measure unitInterval) := htgt.symm
    _ ≤ ∫⁻ ω, liminf (fun n => f n ω) atTop ∂(volume : Measure unitInterval) :=
      lintegral_mono_ae hpoint
    _ ≤ liminf (fun n => ∫⁻ ω, f n ω ∂(volume : Measure unitInterval)) atTop :=
      lintegral_liminf_le hfm
    _ = liminf (fun n => (R n).toMeasure G) atTop := liminf_congr hsrc

noncomputable def clockPrefixDensity (μ : PMF ℕ) (B : ℕ → ℝ) (n : ℕ)
    {a : ℝ} (ha : 0 < a) (f : Skorokhod.D a ℝ) : ℝ≥0∞ :=
  chi μ (n - ⌊a * n⌋₊) (round (f ⟨a, ha.le, le_rfl⟩ * B ⌊(n : ℝ) / (μ 0).toReal⌋₊)) /
    chi μ n 0

theorem measurable_clockPrefixDensity (μ : PMF ℕ) (B : ℕ → ℝ) (n : ℕ)
    {a : ℝ} (ha : 0 < a) : Measurable (clockPrefixDensity μ B n ha) := by
  exact ((measurable_of_countable (fun j : ℤ => chi μ (n - ⌊a * n⌋₊) j)).comp
    (BGW.Probability.measurable_round.comp ((Skorokhod.measurable_eval _).mul_const _))).div_const _

theorem clockPrefixDensity_leafClockPath (μ : PMF ℕ) (B : ℕ → ℝ) (n : ℕ)
    {a : ℝ} (ha : 0 < a) (hB : B ⌊(n : ℝ) / (μ 0).toReal⌋₊ ≠ 0) (ω : ℕ → ℕ) :
    clockPrefixDensity μ B n ha (leafClockPath (μ 0).toReal B n ha ω) =
      chi μ (n - ⌊a * n⌋₊) (walkStopPos ω ⌊a * n⌋₊) / chi μ n 0 := by
  unfold clockPrefixDensity
  rw [leafClockPath_end, div_mul_cancel₀ _ hB, round_intCast]

theorem map_leafClockPath_eq_withDensity {μ : PMF ℕ} (h0 : μ 0 ≠ 0)
    {n : ℕ} (hn : 1 ≤ n) (hadm : LeafAdmissible μ n) {a : ℝ}
    (ha : 0 < a) (ha1 : a < 1) (B : ℕ → ℝ)
    (hB : B ⌊(n : ℝ) / (μ 0).toReal⌋₊ ≠ 0) :
    ((bridgeWalkLaw μ n).map (leafClockPath (μ 0).toReal B n ha)).toMeasure =
      ((walkLawPM μ).map (leafClockPath (μ 0).toReal B n ha)).toMeasure.withDensity
        (clockPrefixDensity μ B n ha) := by
  ext s hs
  have hX := measurable_leafClockPath (μ 0).toReal B n ha
  rw [ProbabilityMeasure.toMeasure_map,
    ← lintegral_indicator_one hs, lintegral_map ((measurable_one : Measurable (1 : Skorokhod.D a ℝ → ℝ≥0∞)).indicator hs) hX,
    lintegral_bridgeWalkLaw_leafClockPath h0 hn hadm ha ha1,
    withDensity_apply _ hs, ← lintegral_indicator hs, ProbabilityMeasure.toMeasure_map,
    lintegral_map ((measurable_clockPrefixDensity μ B n ha).indicator hs) hX]
  apply lintegral_congr
  intro ω
  rw [← clockPrefixDensity_leafClockPath μ B n ha hB]
  by_cases hω : leafClockPath (μ 0).toReal B n ha ω ∈ s <;>
    simp [hω]


noncomputable def leafNormIndex (p : ℝ) (n : ℕ) : ℕ := ⌊(n : ℝ) / p⌋₊

theorem tendsto_leafNormIndex {p : ℝ} (hp : 0 < p) :
    Tendsto (leafNormIndex p) atTop atTop :=
  tendsto_nat_floor_atTop.comp (tendsto_natCast_atTop_atTop.atTop_div_const hp)

theorem leafNormIndex_ratio {p : ℝ} (hp : 0 < p) :
    Tendsto (fun n : ℕ => (leafNormIndex p n : ℝ) / n) atTop (𝓝 (1 / p)) := by
  simpa only [Function.comp_def, leafNormIndex, one_div_mul_eq_div] using
    (tendsto_nat_floor_mul_div_atTop (R := ℝ) (a := 1 / p)
      (one_div_pos.mpr hp).le).comp tendsto_natCast_atTop_atTop

theorem floor_mark_le {a : ℝ} (ha : a < 1) (n : ℕ) : ⌊a * n⌋₊ ≤ n :=
  Nat.floor_le_of_le (mul_le_of_le_one_left (Nat.cast_nonneg _) ha.le)

theorem remaining_mark_ratio {a : ℝ} (ha : 0 ≤ a) (ha1 : a < 1) :
    Tendsto (fun n : ℕ => ((n - ⌊a * n⌋₊ : ℕ) : ℝ) / n) atTop (𝓝 (1 - a)) := by
  have hf := (tendsto_nat_floor_mul_div_atTop (R := ℝ) ha).comp tendsto_natCast_atTop_atTop
  have ht := (tendsto_const_nhds (x := (1 : ℝ))).sub hf
  apply ht.congr'
  filter_upwards [eventually_ne_atTop 0] with n hn
  simp only [Function.comp_def]
  rw [Nat.cast_sub (floor_mark_le ha1 n), sub_div, div_self (by exact_mod_cast hn)]

theorem tendsto_remaining_mark {a : ℝ} (ha : 0 ≤ a) (ha1 : a < 1) :
    Tendsto (fun n : ℕ => n - ⌊a * n⌋₊) atTop atTop :=
  Scalar.tendsto_natCast_of_div (sub_pos.mpr ha1) (remaining_mark_ratio ha ha1)

theorem leafNormIndex_remaining_ratio {p a : ℝ} (hp : 0 < p) (ha : 0 ≤ a) (ha1 : a < 1) :
    Tendsto (fun n : ℕ => (leafNormIndex p (n - ⌊a * n⌋₊) : ℝ) / leafNormIndex p n)
      atTop (𝓝 (1 - a)) := by
  have ht := (((leafNormIndex_ratio hp).comp (tendsto_remaining_mark ha ha1)).mul
    (remaining_mark_ratio ha ha1)).div (leafNormIndex_ratio hp) (one_div_ne_zero hp.ne')
  have hc : (1 / p * (1 - a)) / (1 / p) = 1 - a := by field_simp
  rw [hc] at ht
  apply ht.congr'
  filter_upwards [(tendsto_remaining_mark ha ha1).eventually_ne_atTop 0,
    eventually_ne_atTop 0] with n hr hn
  simp only [Function.comp_def, Pi.div_apply]
  field_simp

theorem attracted_norming_poly_bound {ν : ProbabilityMeasure ℝ} {θ : ℝ} {B : ℕ → ℝ}
    (hB : IsRealStableAttracted ν θ B) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop, B n ≤ C * (n : ℝ)^2 := by
  obtain ⟨N, hN⟩ := hB.potter_upper (ε' := 1) (A := 2) zero_lt_one (by norm_num)
  obtain ⟨Npos, hpos⟩ := eventually_atTop.mp hB.pos
  let M := max 1 (max N Npos)
  have hM1 : 1 ≤ M := le_max_left _ _
  have hMN : N ≤ M := (le_max_left _ _).trans (le_max_right _ _)
  have hBM : 0 < B M := hpos M ((le_max_right _ _).trans (le_max_right _ _))
  have hρ : 1 / θ ≤ 1 := (div_le_one (by linarith [hB.index_mem.1])).mpr hB.index_mem.1.le
  refine ⟨2 * B M, by positivity, eventually_atTop.mpr ⟨M, fun n hn => ?_⟩⟩
  have hMR : (1 : ℝ) ≤ M := by exact_mod_cast hM1
  have hratio : 1 ≤ (n : ℝ) / M := (le_div_iff₀ (by positivity)).mpr (by simpa only [one_mul] using (show (M : ℝ) ≤ n by exact_mod_cast hn))
  have hle : (n : ℝ) / M ≤ n := (div_le_iff₀ (by positivity)).mpr (by nlinarith)
  have hupper := hN M hMN n (hMN.trans hn)
  have hpow (e : ℝ) (he : e ≤ 2) : ((n : ℝ) / M)^e ≤ (n : ℝ)^2 := by
    calc
      _ ≤ ((n : ℝ) / M)^(2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hratio he
      _ = ((n : ℝ) / M)^2 := Real.rpow_two _
      _ ≤ (n : ℝ)^2 := by nlinarith [div_nonneg (Nat.cast_nonneg n) (show (0 : ℝ) ≤ M from Nat.cast_nonneg M)]
  have hmax : max (((n : ℝ) / M)^(1 / θ + 1)) (((n : ℝ) / M)^(1 / θ - 1)) ≤ (n : ℝ)^2 :=
    max_le (hpow _ (by linarith)) (hpow _ (by linarith))
  have hbound : B n / B M ≤ 2 * (n : ℝ)^2 := hupper.trans (mul_le_mul_of_nonneg_left hmax (by norm_num))
  have := (div_le_iff₀ hBM).mp hbound
  nlinarith

theorem inv_chi_zero_poly_bound {μ : PMF ℕ} {θ : ℝ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hap : Aperiodic μ) (hDA : ∃ a, StableDomain μ θ a)
    (hnl : ¬ IsLatticeLaw (etaLaw μ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop, 1 / (chi μ n 0).toReal ≤ C * (n : ℝ)^2 := by
  have hp : 0 < (μ 0).toReal := ENNReal.toReal_pos (hc.apply_zero_ne_zero hne) (μ.apply_ne_top 0)
  have hcan := isRealStableAttracted_norming hc hne hDA
  obtain ⟨C, hC, hbound⟩ := attracted_norming_poly_bound hcan
  obtain ⟨a, ha⟩ := hDA
  have hd : 0 < Scalar.stableDensity θ 0 := Scalar.stableDensity_zero_pos ha.alpha_mem
  have hlow := (chi_zero_asymp hc hne hap ⟨a, ha⟩ hnl).eventually
    (lt_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1))
  have hidx : Tendsto (fun n : ℕ => ⌊(n : ℝ) / (μ 0).toReal⌋₊) atTop atTop :=
    tendsto_nat_floor_atTop.comp (tendsto_natCast_atTop_atTop.atTop_div_const hp)
  refine ⟨2 * C / ((μ 0).toReal^2 * Scalar.stableDensity θ 0), by positivity, ?_⟩
  filter_upwards [hidx.eventually hbound, hidx.eventually hcan.pos, hlow] with n hn hnpos hnlow
  let A := normB μ θ ((n : ℝ) / (μ 0).toReal)
  have hA : 0 < A := hnpos
  have hAn : A ≤ C * ((n : ℝ) / (μ 0).toReal)^2 := by
    apply hn.trans
    apply mul_le_mul_of_nonneg_left _ hC.le
    have hi : (⌊(n : ℝ) / (μ 0).toReal⌋₊ : ℝ) ≤ (n : ℝ) / (μ 0).toReal :=
      Nat.floor_le (div_nonneg (Nat.cast_nonneg n) hp.le)
    nlinarith [show (0 : ℝ) ≤ (⌊(n : ℝ) / (μ 0).toReal⌋₊ : ℝ) from Nat.cast_nonneg _]
  have hprod : Scalar.stableDensity θ 0 / 2 < A * (chi μ n 0).toReal := by
    have ht := (lt_div_iff₀ hd).mp hnlow
    change (1 / 2 : ℝ) * Scalar.stableDensity θ 0 < A * (chi μ n 0).toReal at ht
    linarith
  have hχ : 0 < (chi μ n 0).toReal :=
    pos_of_mul_pos_right (lt_trans (half_pos hd) hprod) hA.le
  apply (div_le_iff₀ hχ).mpr
  have heq : (2 * C / ((μ 0).toReal^2 * Scalar.stableDensity θ 0) * (n : ℝ)^2) *
      (chi μ n 0).toReal = (2 / Scalar.stableDensity θ 0) *
        (C * ((n : ℝ) / (μ 0).toReal)^2 * (chi μ n 0).toReal) := by
    field_simp [hp.ne', hd.ne']
  rw [heq]
  have := mul_le_mul_of_nonneg_right hAn hχ.le
  have := mul_le_mul_of_nonneg_left this (by positivity : 0 ≤ 2 / Scalar.stableDensity θ 0)
  have hunit : (2 / Scalar.stableDensity θ 0) * (A * (chi μ n 0).toReal) > 1 := by
    rw [div_mul_eq_mul_div]
    exact (lt_div_iff₀ hd).mpr (by nlinarith [hprod])
  linarith


theorem tendsto_scaled_chi_auto {μ : PMF ℕ} {θ : ℝ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hap : Aperiodic μ) (hDA : ∃ a, StableDomain μ θ a)
    (hnl : ¬ IsLatticeLaw (etaLaw μ)) {r : ℕ → ℕ} (hrtop : Tendsto r atTop atTop)
    {j : ℕ → ℤ} {x : ℝ}
    (hx : Tendsto (fun k => (j k : ℝ) / normB μ θ ((r k : ℝ) / (μ 0).toReal))
      atTop (𝓝 x)) :
    Tendsto (fun k => normB μ θ ((r k : ℝ) / (μ 0).toReal) * (chi μ (r k) (j k)).toReal)
      atTop (𝓝 (Scalar.stableDensity θ (-x))) := by
  have hp : 0 < (μ 0).toReal := ENNReal.toReal_pos (hc.apply_zero_ne_zero hne) (μ.apply_ne_top 0)
  have hcan := isRealStableAttracted_norming hc hne hDA
  have hApos := ((tendsto_leafNormIndex hp).comp hrtop).eventually hcan.pos
  have hNpos := hrtop.eventually hcan.pos
  have hclock : Tendsto (fun n : ℕ => ((n : ℝ) / (μ 0).toReal) / n) atTop (𝓝 (1 / (μ 0).toReal)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ne_atTop 0] with n hn
    field_simp
  have hs := (normB_ratio_tendsto hc hne hap hDA (one_div_pos.mpr hp) hclock).comp hrtop
  have hb : Tendsto (fun k => (j k : ℝ) / normB μ θ (r k))
      atTop (𝓝 (x * (1 / (μ 0).toReal)^(1 / θ))) := by
    apply (hx.mul hs).congr'
    filter_upwards [hApos] with k hk
    change (j k : ℝ) / normB μ θ ((r k : ℝ) / (μ 0).toReal) *
      (normB μ θ ((r k : ℝ) / (μ 0).toReal) / normB μ θ (r k)) = _
    field_simp [show normB μ θ ((r k : ℝ) / (μ 0).toReal) ≠ 0 from ne_of_gt hk]
  let c := x * (1 / (μ 0).toReal)^(1 / θ)
  have hbnd : ∀ᶠ k in atTop, |(j k : ℝ)| ≤ (|c| + 1) * normB μ θ (r k) := by
    filter_upwards [hb.eventually (Metric.ball_mem_nhds c zero_lt_one), hNpos] with k hk hpN
    have hdist : |(j k : ℝ) / normB μ θ (r k) - c| < 1 := hk
    have hlt : |(j k : ℝ) / normB μ θ (r k)| ≤ |c| + 1 := by
      have hh := abs_sub_le ((j k : ℝ) / normB μ θ (r k)) c 0
      simp only [sub_zero] at hh
      linarith
    have hpN' : 0 < normB μ θ (r k) := by simpa only [normB_natCast] using hpN
    rw [abs_div, abs_of_pos (show 0 < normB μ θ (r k) from hpN')] at hlt
    exact (div_le_iff₀ (show 0 < normB μ θ (r k) from hpN')).mp hlt
  exact tendsto_scaled_chi hc hne hap hDA hnl hrtop (by positivity : 0 < |c| + 1) hbnd hx

theorem tendsto_clockPrefixDensity {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ}
    (hc : IsCritical μ) (hne : μ 1 ≠ 1) (hap : Aperiodic μ)
    (hB : IsRealStableAttracted (realOffspringStepLaw μ) θ B)
    (hnl : ¬ IsLatticeLaw (etaLaw μ)) {q : ℕ → ℕ}
    (hqtop : Tendsto q atTop atTop) (hq : ∀ k, LeafAdmissible μ (q k))
    {a : ℝ} (ha : 0 < a) (ha1 : a < 1)
    {f : ℕ → Skorokhod.D a ℝ} {g : Skorokhod.D a ℝ}
    (hf : Tendsto f atTop (𝓝 g)) :
    Tendsto (fun k => clockPrefixDensity μ B (q k) ha (f k)) atTop
      (𝓝 (ENNReal.ofReal (bridgePrefixWeight θ a ha.le g))) := by
  have hp : 0 < (μ 0).toReal := ENNReal.toReal_pos (hc.apply_zero_ne_zero hne) (μ.apply_ne_top 0)
  obtain ⟨hDA, hBB⟩ := stableDomain_of_isRealStableAttracted hc hne hB
  have hcan := isRealStableAttracted_norming hc hne hDA
  let N := leafNormIndex (μ 0).toReal
  let r : ℕ → ℕ := fun k => q k - ⌊a * q k⌋₊
  let j : ℕ → ℤ := fun k => round ((f k) ⟨a, ha.le, le_rfl⟩ * B (N (q k)))
  let d := (1 - a)^(1 / θ)
  have hd : 0 < d := Real.rpow_pos_of_pos (sub_pos.mpr ha1) _
  have hNtop := (tendsto_leafNormIndex hp).comp hqtop
  have hrTop : Tendsto r atTop atTop := (tendsto_remaining_mark ha.le ha1).comp hqtop
  have hNrTop := (tendsto_leafNormIndex hp).comp hrTop
  have hAr : Tendsto (fun k => normB μ θ ((r k : ℝ) / (μ 0).toReal) /
      normB μ θ ((q k : ℝ) / (μ 0).toReal)) atTop (𝓝 d) :=
    (hcan.tendsto_norming_ratio (sub_pos.mpr ha1) (tendsto_leafNormIndex hp)
      (leafNormIndex_remaining_ratio hp ha.le ha1)).comp hqtop
  have he := ((Skorokhod.lipschitzWith_one_eval_right (E := ℝ) ha.le).continuous.tendsto g).comp hf
  have hjB := BGW.Probability.round_normalized_tendsto he (hB.tendsto_norming_atTop.comp hNtop)
  have hjA : Tendsto (fun k => (j k : ℝ) / normB μ θ ((q k : ℝ) / (μ 0).toReal))
      atTop (𝓝 (g ⟨a, ha.le, le_rfl⟩)) := by
    have ht := hjB.mul (hBB.comp hNtop)
    simp only [mul_one] at ht
    apply ht.congr'
    filter_upwards [hNtop.eventually hB.pos] with k hk
    simp only [Function.comp_def, leafNormIndex] at hk
    simp only [j, N, leafNormIndex, Function.comp_def, normB]
    field_simp [hk.ne']
  have hjAr : Tendsto (fun k => (j k : ℝ) / normB μ θ ((r k : ℝ) / (μ 0).toReal))
      atTop (𝓝 (g ⟨a, ha.le, le_rfl⟩ / d)) := by
    apply (hjA.div hAr hd.ne').congr'
    filter_upwards [hNtop.eventually hcan.pos] with k hk
    change (j k : ℝ) / normB μ θ ((q k : ℝ) / (μ 0).toReal) /
      (normB μ θ ((r k : ℝ) / (μ 0).toReal) / normB μ θ ((q k : ℝ) / (μ 0).toReal)) = _
    field_simp [show normB μ θ ((q k : ℝ) / (μ 0).toReal) ≠ 0 from (by simpa only [Function.comp_def, leafNormIndex, normB] using hk.ne')]
  have hnum := tendsto_scaled_chi_auto hc hne hap hDA hnl hrTop hjAr
  have hp0 : 0 < Scalar.stableDensity θ 0 := Scalar.stableDensity_zero_pos hB.index_mem
  have hden : Tendsto (fun k => normB μ θ ((q k : ℝ) / (μ 0).toReal) * (chi μ (q k) 0).toReal)
      atTop (𝓝 (Scalar.stableDensity θ 0)) := by
    have ht := ((chi_zero_asymp hc hne hap hDA hnl).comp hqtop).mul_const (Scalar.stableDensity θ 0)
    simpa only [Function.comp_def, div_mul_cancel₀ _ hp0.ne', one_mul] using ht
  have hreal : Tendsto (fun k => (chi μ (r k) (j k)).toReal / (chi μ (q k) 0).toReal)
      atTop (𝓝 ((1 / d) * (Scalar.stableDensity θ (-(g ⟨a, ha.le, le_rfl⟩ / d)) /
        Scalar.stableDensity θ 0))) := by
    have ht := hAr.inv₀ hd.ne' |>.mul (hnum.div hden hp0.ne')
    simp only [inv_eq_one_div] at ht
    apply ht.congr'
    filter_upwards [hNtop.eventually hcan.pos, hNrTop.eventually hcan.pos, hden.eventually_ne hp0.ne'] with k hk hrk hχk
    have hQ : normB μ θ ((q k : ℝ) / (μ 0).toReal) ≠ 0 := by
      simpa only [Function.comp_def, leafNormIndex, normB] using hk.ne'
    have hR : normB μ θ ((r k : ℝ) / (μ 0).toReal) ≠ 0 := by
      simpa only [Function.comp_def, leafNormIndex, normB] using hrk.ne'
    have hχ0 := (mul_ne_zero_iff.mp hχk).2
    simp only [Pi.div_apply]
    field_simp [hQ, hR, hχ0]
  have hident : (1 / d) * (Scalar.stableDensity θ (-(g ⟨a, ha.le, le_rfl⟩ / d)) /
      Scalar.stableDensity θ 0) = bridgePrefixWeight θ a ha.le g := by
    have hpow : (1 - a)^(-1 / θ) = 1 / d := by
      rw [show -1 / θ = -(1 / θ) by ring, Real.rpow_neg (sub_pos.mpr ha1).le]
      simp only [one_div, d]
    simp only [bridgePrefixWeight, stableDensityAt, hpow]
    have harg : -(g ⟨a, ha.le, le_rfl⟩ / d) = (1 / d) * -g ⟨a, ha.le, le_rfl⟩ := by ring
    rw [harg]
    ring
  rw [hident] at hreal
  apply (ENNReal.tendsto_ofReal hreal).congr'
  filter_upwards [hqtop.eventually_ge_atTop 1] with k hk
  have hχ : chi μ (q k) 0 ≠ 0 := by
    simpa only [chi, sub_zero, ← bridgeAtMark_eq_walkStopEvent] using
      (iidWalk_bridgeAtMark_ne_zero_iff μ hk).mpr (hq k)
  have hfin : chi μ (r k) (j k) / chi μ (q k) 0 ≠ ⊤ :=
    ENNReal.div_ne_top (measure_ne_top _ _) hχ
  rw [← ENNReal.toReal_div, ENNReal.ofReal_toReal hfin]
  rfl

theorem bridge_real_le {μ : PMF ℕ} {n : ℕ} (hn : 1 ≤ n) (hadm : LeafAdmissible μ n)
    (s : Set (ℕ → ℕ)) :
    (bridgeWalkLaw μ n).toMeasure.real s ≤ (1 / (chi μ n 0).toReal) * (iidWalk μ).real s := by
  have hχ : iidWalk μ (bridgeAtMark n) = chi μ n 0 := by
    simp only [chi, sub_zero, ← bridgeAtMark_eq_walkStopEvent]
  rw [coe_bridgeWalkLaw ((iidWalk_bridgeAtMark_ne_zero_iff μ hn).mpr hadm)]
  simp only [Measure.real, cond_apply (measurableSet_bridgeAtMark n), ENNReal.toReal_mul,
    ENNReal.toReal_inv, hχ, one_div]
  exact mul_le_mul_of_nonneg_left (measureReal_mono Set.inter_subset_right) (by positivity)

theorem tendsto_bridge_small_events {μ : PMF ℕ} {θ : ℝ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hap : Aperiodic μ) (hDA : ∃ a, StableDomain μ θ a) (hnl : ¬ IsLatticeLaw (etaLaw μ))
    {q : ℕ → ℕ} (hqtop : Tendsto q atTop atTop) (hq : ∀ k, LeafAdmissible μ (q k))
    (s : ℕ → Set (ℕ → ℕ))
    (hs : Tendsto (fun k => (q k : ℝ)^2 * (iidWalk μ).real (s k)) atTop (𝓝 0)) :
    Tendsto (fun k => (bridgeWalkLaw μ (q k)).toMeasure.real (s k)) atTop (𝓝 0) := by
  obtain ⟨C, hC, hbound⟩ := inv_chi_zero_poly_bound hc hne hap hDA hnl
  have ht : Tendsto (fun k => C * ((q k : ℝ)^2 * (iidWalk μ).real (s k))) atTop (𝓝 0) := by
    simpa only [mul_zero] using hs.const_mul C
  apply squeeze_zero' (Eventually.of_forall fun _ => measureReal_nonneg) _ ht
  filter_upwards [hqtop.eventually hbound, hqtop.eventually_ge_atTop 1] with k hk hk1
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
    (hap : Aperiodic μ) (hDA : ∃ a, StableDomain μ θ a) (hnl : ¬ IsLatticeLaw (etaLaw μ))
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
  have hb := tendsto_bridge_small_events hc hne hap hDA hnl hqtop hq
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
    (hnl : ¬ IsLatticeLaw (etaLaw μ)) {q : ℕ → ℕ}
    (hqtop : Tendsto q atTop atTop) (hq : ∀ k, LeafAdmissible μ (q k))
    {a : ℝ} (ha : 0 < a) (ha1 : a < 1) :
    Tendsto (fun k => (bridgeWalkLaw μ (q k)).map (leafClockPath (μ 0).toReal B (q k) ha))
      atTop (𝓝 ((stableBridgeLaw θ).map (Skorokhod.restrict ha1.le))) := by
  have hp : 0 < (μ 0).toReal := ENNReal.toReal_pos (hc.apply_zero_ne_zero hne) (μ.apply_ne_top 0)
  apply tendsto_reweighted ((ClassicalLimits.WalkClock.lem_CVf2_ii hc hne hB ha).comp hqtop)
    (fun k => clockPrefixDensity μ B (q k) ha)
    (fun f => ENNReal.ofReal (bridgePrefixWeight θ a ha.le f))
    (fun k => measurable_clockPrefixDensity μ B (q k) ha)
    (measurable_bridgePrefixWeight hB.index_mem ha.le).ennreal_ofReal
  · filter_upwards [hqtop.eventually_ge_atTop 1,
      ((tendsto_leafNormIndex hp).comp hqtop).eventually hB.pos] with k hk hBk
    exact map_leafClockPath_eq_withDensity (hc.apply_zero_ne_zero hne) hk (hq k) ha ha1 B hBk.ne'
  · rw [ProbabilityMeasure.toMeasure_map, map_restrict_stableBridgeLaw hB.index_mem ha ha1]
    rfl
  · intro f g hf
    exact tendsto_clockPrefixDensity hc hne hap hB hnl hqtop hq ha ha1 hf

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
    (hnl : ¬ IsLatticeLaw (etaLaw μ)) {q : ℕ → ℕ}
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
    tendsto_bridge_markTime_ratio hc hne hap hDA hnl hqtop hq zero_lt_one hself
  have hY : ErrorConverges P (fun k ω => (markTime ⌊b * q k⌋₊ ω : ℝ) / ⌊b * q k⌋₊)
      (1 / (μ 0).toReal) :=
    tendsto_bridge_markTime_ratio hc hne hap hDA hnl hqtop hq hb hfloor
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
    (hnl : ¬ IsLatticeLaw (etaLaw μ)) {q : ℕ → ℕ}
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
    tendsto_leafClockPath_bridge hc hne hap hB hnl hqtop hq hb hb1
  have hcont : ∀ᵐ f : Skorokhod.D b ℝ ∂L.toMeasure,
      ContinuousAt (f : Set.Icc (0 : ℝ) b → ℝ) ⟨a, ha.le, hab.le⟩ := by
    dsimp only [L]
    rw [ProbabilityMeasure.toMeasure_map, map_restrict_stableBridgeLaw hB.index_mem hb hb1,
      bridgePrefixLaw]
    exact (withDensity_absolutelyContinuous _ _).ae_le
      (ae_continuousAt_stableProcessLaw hB.index_mem hb ⟨a, ha.le, hab.le⟩)
  obtain ⟨hK, hraw⟩ := bridge_factors_error hc hne hap hB hnl hqtop hq hb
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
    (hnl : ¬ IsLatticeLaw (etaLaw μ)) {q : ℕ → ℕ}
    (hqtop : Tendsto q atTop atTop) (hq : ∀ k, LeafAdmissible μ (q k))
    {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) :
    Tendsto (fun k => (bridgeWalkLaw μ (q k)).map
        (Skorokhod.restrict ha1.le ∘ bridgeWalkPath B (q k)))
      atTop (𝓝 ((stableBridgeLaw θ).map (Skorokhod.restrict ha1.le))) := by
  rcases ha0.eq_or_lt with h | h
  · subst a
    exact bridge_prefix_tendsto_zero hB.index_mem q
  · exact bridge_prefix_tendsto_pos hc hne hap hB hnl hqtop hq h ha1

/-- The stopped leaf-clock bridge converges on the whole interval. Prefix convergence is
combined with the independent terminal-reversal provider by C11b. -/
theorem tendsto_bridgeWalkPath {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ} (hc : IsCritical μ)
    (hne : μ 1 ≠ 1) (hap : Aperiodic μ)
    (hB : IsRealStableAttracted (realOffspringStepLaw μ) θ B)
    (hnl : ¬ IsLatticeLaw (etaLaw μ)) {q : ℕ → ℕ}
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
    bridge_prefix_tendsto hc hne hap hB hnl hqtop hq hs0 hs1
  exact Skorokhod.tendsto_of_tendsto_restrict_of_oscillation
    (fun k => bridgeWalkLaw μ (q k))
    (fun k => measurable_bridgeWalkPath B (q k)) zero_lt_one ha0 ha1 halim
    (fun j => hpre (a j) (ha0 j) (ha1 j))
    (stableBridgeLaw_ae_continuousAt hB.index_mem ⟨1, zero_le_one, le_rfl⟩)
    (BridgeTerminal.bridge_terminal_oscillation hc hne hap hB hnl hqtop hq hpre ha0 ha1 halim)

end BGWLeaves.LeafLimits.Bridge
