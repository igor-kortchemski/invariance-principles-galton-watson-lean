module

public import BGWLeaves.ClassicalLimits.Defs
public import BGWLeaves.Vervaat
public import BGWLeaves.LeafConcentration
public import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import BGWLeaves.ClassicalLimits.Perturbation
public import BGW.StableTrees.StableProcessLaw
public import BGW.StableTrees.StableProcessMarkov
public import BGW.StableTrees.StableProcessCompactness

/-!
# Lemma 6.2(ii): the walk at the leaf clock

Proof of Lemma 6.2(ii), `lem_CVf2_ii`, with exactly the type stated in `BGWLeaves.ClassicalLimits`.
The FCLT is applied along `N_n = max ⌊n/μ₀⌋ 1`, absorbing the spatial normalization into
its deterministic index. Lemma 6.2(i) and Borel–Cantelli give the strong clock law;
`Perturbation.lem_CVproba` then handles `T_{an}/(a N_n)`. Clipping at the fixed horizon
is eventually inactive almost surely and is removed by weak perturbation.
-/

@[expose] public section

namespace BGWLeaves.ClassicalLimits.WalkClock

open MeasureTheory ProbabilityTheory Filter BGW
open BGW.StableTrees
open scoped Topology ENNReal

/-- The offspring coordinates induce the canonical real iid walk law. -/
private theorem map_walkIncr (μ : PMF ℕ) :
    (walkLawPM μ).map walkIncr = BGW.Probability.RealWalk.iidLaw (realOffspringStepLaw μ) := by
  apply Subtype.ext
  change (Measure.infinitePi (fun _ : ℕ => μ.toMeasure)).map walkIncr =
    Measure.infinitePi (fun _ : ℕ =>
      ((μ.toMeasure.map (fun k : ℕ => (k : ℤ) - 1)).map (fun z : ℤ => (z : ℝ))))
  calc
    _ = Measure.infinitePi (fun _ : ℕ => μ.toMeasure.map (fun k : ℕ => (k : ℝ) - 1)) :=
      Measure.infinitePi_map_pi (μ := fun _ : ℕ => μ.toMeasure)
        (f := fun _ (k : ℕ) => (k : ℝ) - 1) (fun _ => by fun_prop)
    _ = _ := by
      congr 1
      funext i
      rw [Measure.map_map (by fun_prop) (measurable_of_countable _)]
      congr 1
      funext k
      simp

/-- FCLT on the original offspring probability space. -/
private theorem tendsto_walk_stepPath {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ}
    (hB : IsRealStableAttracted (realOffspringStepLaw μ) θ B) {T : ℝ} (hT : 0 < T) :
    Tendsto (fun n : ℕ => (walkLawPM μ).map
      (fun ω => Skorokhod.realStepPath T n (B n) (walkIncr ω))) atTop
        (𝓝 (stableProcessLaw θ T)) := by
  have heq (n : ℕ) : (walkLawPM μ).map
      (fun ω => Skorokhod.realStepPath T n (B n) (walkIncr ω)) =
        stepPathLaw (realOffspringStepLaw μ) T B n := by
    rw [stepPathLaw, ← map_walkIncr μ]
    apply Subtype.ext
    exact (Measure.map_map (Skorokhod.measurable_realStepPath T n (B n))
      measurable_walkIncr).symm
  simpa only [heq] using hB.tendsto_stepPathLaw hT

/-- A finite first mark agrees with the natural-number reading of the leaf clock. -/
private theorem clock_eq_of_mark {ω : ℕ → ℕ} {m k : ℕ} (hk : IsMarkTime m ω k) :
    (walkLeafTime ω m).toNat = k := by
  have heq : walkLeafTime ω m = (k : ℕ∞) := by
    unfold walkLeafTime
    apply le_antisymm
    · exact iInf₂_le k hk.1
    · refine le_iInf₂ fun j hj => ?_
      have hkj : k ≤ j := by
        by_contra h
        exact (ne_of_lt (hk.2 j (Nat.lt_of_not_ge h))) hj
      exact_mod_cast hkj
  rw [heq, ENat.toNat_natCast]

/-- The concentration estimate of Lemma 6.2(i) implies the strong clock law. -/
private theorem ae_tendsto_clock_ratio (μ : PMF ℕ) (h0 : μ 0 ≠ 0) (h1 : μ 0 ≠ 1) :
    ∀ᵐ ω ∂(walkLawPM μ).toMeasure,
      Tendsto (fun m : ℕ => ((walkLeafTime ω m).toNat : ℝ) / m) atTop
        (𝓝 (1 / (μ 0).toReal)) := by
  let bad : ℕ → Set (ℕ → ℕ) := fun m =>
    {ω | (¬ ∃ k, IsMarkTime m ω k) ∨ ∃ k, IsMarkTime m ω k ∧
      1 / (m : ℝ) ^ (1 / 4 : ℝ) < |(k : ℝ) / m - 1 / (μ 0).toReal|}
  have hs : Summable (fun m => (walkLawPM μ).toMeasure.real (bad m)) :=
    ((lem_CVf2_i μ h0 h1).tail (by norm_num) (fun _ => measureReal_nonneg)).1
  have hsum : (∑' m, (walkLawPM μ).toMeasure (bad m)) ≠ ⊤ := by
    simpa only [Measure.real, ENNReal.ofReal_toReal (measure_ne_top _ _)] using
      hs.tsum_ofReal_ne_top
  have hbc := ae_eventually_notMem hsum
  have hsmall : Tendsto (fun m : ℕ => 1 / (m : ℝ) ^ (1 / 4 : ℝ)) atTop (𝓝 0) := by
    exact tendsto_const_nhds.div_atTop
      ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)).comp
        tendsto_natCast_atTop_atTop)
  filter_upwards [hbc] with ω hω
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [hω, hsmall.eventually (gt_mem_nhds hε)] with m hm hεm
  have hm' : (∃ k, IsMarkTime m ω k) ∧
      ∀ k, IsMarkTime m ω k → |(k : ℝ) / m - 1 / (μ 0).toReal| ≤
        1 / (m : ℝ) ^ (1 / 4 : ℝ) := by
    have hh : (¬ ¬ ∃ k, IsMarkTime m ω k) ∧
        ¬ (∃ k, IsMarkTime m ω k ∧ 1 / (m : ℝ) ^ (1 / 4 : ℝ) <
          |(k : ℝ) / m - 1 / (μ 0).toReal|) := not_or.mp hm
    exact ⟨not_not.mp hh.1, fun k hk => le_of_not_gt (fun h => hh.2 ⟨k, hk, h⟩)⟩
  obtain ⟨k, hk⟩ := hm'.1
  rw [clock_eq_of_mark hk, Real.dist_eq]
  exact (hm'.2 k hk).trans_lt hεm

/-- Almost sure convergence gives the strict probability tails used by Slutsky. -/
private theorem error_of_ae_tendsto {Ω : Type*} [MeasurableSpace Ω]
    (P : ProbabilityMeasure Ω) (f : ℕ → Ω → ℝ) (c : ℝ)
    (hm : ∀ n, Measurable (f n))
    (ht : ∀ᵐ ω ∂P.toMeasure, Tendsto (fun n => f n ω) atTop (𝓝 c)) :
    ∀ ε > 0, Tendsto (fun n => P.toMeasure.real {ω | ε < dist (f n ω) c})
      atTop (𝓝 0) := by
  have hi : TendstoInMeasure P.toMeasure f atTop (fun _ => c) :=
    tendstoInMeasure_of_tendsto_ae (fun n => (hm n).aestronglyMeasurable) ht
  intro ε hε
  have hge : Tendsto (fun n => P.toMeasure.real {ω | ε ≤ dist (f n ω) c})
      atTop (𝓝 0) := (tendstoInMeasure_iff_measureReal_dist.mp hi) ε hε
  refine squeeze_zero (fun _ => measureReal_nonneg) ?_ hge
  intro n
  refine measureReal_mono ?_ (measure_ne_top _ _)
  intro ω hω
  change ε ≤ dist (f n ω) c
  exact le_of_lt hω

/-- On the event that the clock fits in the horizon, scaling the fixed step path is exact. -/
private theorem scale_step_eq {a : ℝ} (ha : 0 < a) {q m : ℕ} (hq : 0 < q) (hm : 0 < m)
    (hbound : (m : ℝ) / (a * q) ≤ 2) (b : ℝ) (ω : ℕ → ℝ) :
    Skorokhod.timeSpaceScale a (by positivity : 0 ≤ 2 * a)
      (Skorokhod.realStepPath (2 * a) q b ω, 1,
        ⟨(m : ℝ) / (a * q), by change 0 < (m : ℝ) / (a * q); positivity⟩) =
      Skorokhod.timeSpaceScale a zero_le_one
        (Skorokhod.realStepPath 1 m b ω, 1, ⟨1 / a, one_div_pos.mpr ha⟩) := by
  apply Skorokhod.ext
  intro t
  have hleft : (m : ℝ) / (a * q) * (t : ℝ) ≤ 2 * a :=
    mul_le_mul hbound t.2.2 t.2.1 (by norm_num)
  have hright : 1 / a * (t : ℝ) ≤ 1 := by
    rw [one_div_mul_eq_div, div_le_one ha]
    exact t.2.2
  change 1 * (BGW.Probability.RealWalk.partialSum ω
      ⌊(q : ℝ) * min ((m : ℝ) / (a * q) * (t : ℝ)) (2 * a)⌋₊ / b) =
    1 * (BGW.Probability.RealWalk.partialSum ω
      ⌊(m : ℝ) * min (1 / a * (t : ℝ)) 1⌋₊ / b)
  rw [min_eq_left hleft, min_eq_left hright]
  have heq : (q : ℝ) * ((m : ℝ) / (a * q) * (t : ℝ)) =
      (m : ℝ) * (1 / a * (t : ℝ)) := by
    have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
    field_simp [ha.ne', hqR]
  rw [heq]

/-- The deterministic indices used for the FCLT at the leaf normalization. -/
private noncomputable def clockIndex (p : ℝ) (n : ℕ) : ℕ := max ⌊(n : ℝ) / p⌋₊ 1

private theorem clockIndex_pos (p : ℝ) (n : ℕ) : 0 < clockIndex p n :=
  lt_of_lt_of_le Nat.zero_lt_one (le_max_right _ _)

private theorem clockIndex_eventually {p : ℝ} (hp : 0 < p) :
    ∀ᶠ n : ℕ in atTop, clockIndex p n = ⌊(n : ℝ) / p⌋₊ := by
  have ht : Tendsto (fun n : ℕ => ⌊(n : ℝ) / p⌋₊) atTop atTop :=
    tendsto_nat_floor_atTop.comp (tendsto_natCast_atTop_atTop.atTop_div_const hp)
  filter_upwards [ht.eventually (eventually_ge_atTop 1)] with n hn
  exact max_eq_left hn

private theorem tendsto_clockIndex {p : ℝ} (hp : 0 < p) :
    Tendsto (clockIndex p) atTop atTop := by
  have ht : Tendsto (fun n : ℕ => ⌊(n : ℝ) / p⌋₊) atTop atTop :=
    tendsto_nat_floor_atTop.comp (tendsto_natCast_atTop_atTop.atTop_div_const hp)
  exact ht.congr' ((clockIndex_eventually hp).mono fun _ h => h.symm)

private theorem clockIndex_ratio {p : ℝ} (hp : 0 < p) :
    Tendsto (fun n : ℕ => (clockIndex p n : ℝ) / n) atTop (𝓝 (1 / p)) := by
  have ht := (tendsto_nat_floor_mul_div_atTop (R := ℝ) (a := 1 / p)
    (one_div_pos.mpr hp).le).comp tendsto_natCast_atTop_atTop
  apply ht.congr'
  filter_upwards [clockIndex_eventually hp] with n hn
  change (⌊(1 / p) * (n : ℝ)⌋₊ : ℝ) / n = (clockIndex p n : ℝ) / n
  rw [hn, show (1 / p) * (n : ℝ) = (n : ℝ) / p by ring]

/-- A strictly positive modification of the random clock factor. -/
private noncomputable def clockFactor (p a : ℝ) (ha : 0 < a) (n : ℕ) (ω : ℕ → ℕ) :
    Set.Ioi (0 : ℝ) :=
  ⟨(max (leafClock ω (a * n)) 1 : ℕ) / (a * clockIndex p n),
    div_pos (by exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one (le_max_right _ _))
      (mul_pos ha (by exact_mod_cast clockIndex_pos p n))⟩

private theorem measurable_clockFactor (p a : ℝ) (ha : 0 < a) (n : ℕ) :
    Measurable (fun ω => (clockFactor p a ha n ω : ℝ)) := by
  exact (measurable_from_nat (f := fun k : ℕ => (max k 1 : ℕ) / (a * clockIndex p n))).comp
    (measurable_leafClock (a * n))

/-- The positive clock factors tend to one almost surely. -/
private theorem ae_tendsto_clockFactor (μ : PMF ℕ) (h0 : μ 0 ≠ 0) (h1 : μ 0 ≠ 1)
    {a : ℝ} (ha : 0 < a) :
    ∀ᵐ ω ∂(walkLawPM μ).toMeasure,
      Tendsto (fun n => (clockFactor (μ 0).toReal a ha n ω : ℝ)) atTop (𝓝 1) := by
  have hp : 0 < (μ 0).toReal := ENNReal.toReal_pos h0 (μ.apply_ne_top 0)
  have hm : Tendsto (fun n : ℕ => ⌊a * (n : ℝ)⌋₊) atTop atTop :=
    tendsto_nat_floor_atTop.comp (tendsto_natCast_atTop_atTop.const_mul_atTop ha)
  have hmr : Tendsto (fun n : ℕ => (⌊a * (n : ℝ)⌋₊ : ℝ) / n) atTop (𝓝 a) := by
    simpa only [Function.comp_def] using
      (tendsto_nat_floor_mul_div_atTop (R := ℝ) ha.le).comp tendsto_natCast_atTop_atTop
  filter_upwards [ae_tendsto_clock_ratio μ h0 h1] with ω hω
  have hc : Tendsto (fun n : ℕ => (leafClock ω (a * n) : ℝ) / n) atTop
      (𝓝 ((1 / (μ 0).toReal) * a)) := by
    have h := (hω.comp hm).mul hmr
    apply h.congr'
    filter_upwards [hm.eventually (eventually_ne_atTop 0)] with n hn
    dsimp [leafClock, Function.comp_def]
    rw [div_mul_div_cancel₀ (by exact_mod_cast hn)]
  have hcpos : ∀ᶠ n : ℕ in atTop, 0 < leafClock ω (a * n) := by
    filter_upwards [hc.eventually (lt_mem_nhds (mul_pos (one_div_pos.mpr hp) ha))] with n hn
    have := (pos_of_mul_pos_left (show 0 <
      (leafClock ω (a * n) : ℝ) * (n : ℝ)⁻¹ from hn) (inv_nonneg.mpr (Nat.cast_nonneg n)))
    exact_mod_cast this
  have hcmax : Tendsto (fun n : ℕ => (max (leafClock ω (a * n)) 1 : ℕ) / (n : ℝ))
      atTop (𝓝 ((1 / (μ 0).toReal) * a)) := by
    apply hc.congr'
    filter_upwards [hcpos] with n hn
    rw [max_eq_left (Nat.succ_le_iff.mpr hn)]
  have hden := (clockIndex_ratio hp).const_mul a
  have hr := hcmax.div hden (ne_of_gt (mul_pos ha (one_div_pos.mpr hp)))
  have hlimit : ((1 / (μ 0).toReal) * a) / (a * (1 / (μ 0).toReal)) = 1 := by
    rw [mul_comm, div_self (ne_of_gt (mul_pos ha (one_div_pos.mpr hp)))]
  rw [hlimit] at hr
  apply hr.congr'
  filter_upwards [eventually_ne_atTop (0 : ℕ)] with n hn
  dsimp [clockFactor]
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  field_simp [hnR]

private theorem ae_eventually_clock_pos (μ : PMF ℕ) (h0 : μ 0 ≠ 0)
    {a : ℝ} (ha : 0 < a) :
    ∀ᵐ ω ∂(walkLawPM μ).toMeasure, ∀ᶠ n : ℕ in atTop, 0 < leafClock ω (a * n) := by
  have ht : Tendsto (fun n : ℕ => ⌊a * (n : ℝ)⌋₊) atTop atTop :=
    tendsto_nat_floor_atTop.comp (tendsto_natCast_atTop_atTop.const_mul_atTop ha)
  filter_upwards [ae_exists_markTime μ h0] with ω hω
  filter_upwards [ht.eventually (eventually_ge_atTop 1)] with n hn
  obtain ⟨k, hk⟩ := hω ⌊a * (n : ℝ)⌋₊
  change 0 < (walkLeafTime ω ⌊a * (n : ℝ)⌋₊).toNat
  rw [clock_eq_of_mark hk]
  by_contra hk0
  have hkzero : k = 0 := Nat.eq_zero_of_not_pos hk0
  have hm := hk.1
  rw [hkzero] at hm
  simp only [walkLeafCount, Finset.range_zero, Finset.filter_empty, Finset.card_empty] at hm
  omega

theorem lem_CVf2_ii {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hB : IsRealStableAttracted (realOffspringStepLaw μ) θ B) {a : ℝ} (ha : 0 < a) :
    Tendsto (fun n : ℕ => (walkLawPM μ).map (leafClockPath (μ 0).toReal B n ha))
      atTop (𝓝 (stableProcessLaw θ a)) := by
  have h0 : μ 0 ≠ 0 := hc.apply_zero_ne_zero hne
  have h1 : μ 0 ≠ 1 := by
    intro heq
    have hs := (PMF.apply_eq_one_iff μ 0).mp heq
    have hz : ∀ j : ℕ, (j : ℝ≥0∞) * μ j = 0 := by
      intro j
      by_cases hj : j = 0
      · simp [hj]
      · have hj' : μ j = 0 := by
          by_contra h
          have : j ∈ μ.support := h
          rw [hs] at this
          exact hj (Set.mem_singleton_iff.mp this)
        simp [hj']
    have hc' := hc
    simp only [IsCritical, hz, tsum_zero] at hc'
    exact zero_ne_one hc'
  have hp : 0 < (μ 0).toReal := ENNReal.toReal_pos h0 (μ.apply_ne_top 0)
  let q := clockIndex (μ 0).toReal
  let Z := fun n ω => Skorokhod.realStepPath (2 * a) (q n) (B (q n)) (walkIncr ω)
  let S := clockFactor (μ 0).toReal a ha
  let G := fun n ω => Skorokhod.timeSpaceScale a (by positivity : 0 ≤ 2 * a)
    (Z n ω, (1 : ℝ), S n ω)
  have hZm : ∀ n, Measurable (Z n) := fun n =>
    (Skorokhod.measurable_realStepPath (2 * a) (q n) (B (q n))).comp measurable_walkIncr
  have hSm : ∀ n, Measurable (fun ω => (S n ω : ℝ)) :=
    measurable_clockFactor (μ 0).toReal a ha
  have hGm : ∀ n, Measurable (G n) := fun n =>
    (measurable_timeSpaceScale a (by positivity : 0 ≤ 2 * a)).comp
      ((hZm n).prodMk (measurable_const.prodMk ((hSm n).subtype_mk)))
  have hZ : Tendsto (fun n => (walkLawPM μ).map (Z n)) atTop
      (𝓝 (stableProcessLaw θ (2 * a))) :=
    (tendsto_walk_stepPath hB (by positivity)).comp (tendsto_clockIndex hp)
  have hS : ∀ ε > 0, Tendsto (fun n => (walkLawPM μ).toMeasure.real
      {ω | ε < dist (S n ω : ℝ) 1}) atTop (𝓝 0) :=
    error_of_ae_tendsto (walkLawPM μ) (fun n ω => (S n ω : ℝ)) 1 hSm
      (ae_tendsto_clockFactor μ h0 h1 ha)
  have haT : a < 2 * a := by linarith
  have hG : Tendsto (fun n => (walkLawPM μ).map (G n)) atTop
      (𝓝 (stableProcessLaw θ a)) := by
    have ht := Perturbation.lem_CVproba ha haT (fun _ => walkLawPM μ) Z
      (fun _ _ => (1 : ℝ)) S hZm (fun _ => measurable_const) hSm
      (stableProcessLaw θ (2 * a)) hZ
      (ae_continuousAt_stableProcessLaw hB.index_mem (by positivity) _)
      (by intro ε hε; simp [dist_self, not_lt.mpr hε.le]) hS
    rw [map_restrict_stableProcessLaw hB.index_mem ha haT.le] at ht
    exact ht
  have heq : ∀ᵐ ω ∂(walkLawPM μ).toMeasure, ∀ᶠ n : ℕ in atTop,
      leafClockPath (μ 0).toReal B n ha ω = G n ω := by
    filter_upwards [ae_tendsto_clockFactor μ h0 h1 ha,
      ae_eventually_clock_pos μ h0 ha] with ω hω hpos
    filter_upwards [hω.eventually (gt_mem_nhds (by norm_num : (1 : ℝ) < 2)),
      hpos, clockIndex_eventually hp] with n hn hmn hqn
    dsimp [G, Z, S]
    have hbound : (leafClock ω (a * n) : ℝ) / (a * q n) ≤ 2 := by
      simpa only [clockFactor, max_eq_left (Nat.succ_le_iff.mpr hmn)] using hn.le
    have ht := scale_step_eq ha (clockIndex_pos (μ 0).toReal n) hmn hbound
      (B (q n)) (walkIncr ω)
    simpa only [leafClockPath, clockFactor, max_eq_left (Nat.succ_le_iff.mpr hmn), q, hqn] using ht.symm
  let d := fun n ω => dist (leafClockPath (μ 0).toReal B n ha ω) (G n ω)
  have hdm : ∀ n, Measurable (d n) := fun n =>
    (measurable_leafClockPath (μ 0).toReal B n ha).dist (hGm n)
  have hd : ∀ᵐ ω ∂(walkLawPM μ).toMeasure, Tendsto (fun n => d n ω) atTop (𝓝 0) := by
    filter_upwards [heq] with ω hω
    apply tendsto_const_nhds.congr'
    filter_upwards [hω] with n hn
    simp only [d, hn, dist_self]
  have herr := error_of_ae_tendsto (walkLawPM μ) d 0 hdm hd
  apply BGW.MetricMeasure.tendsto_probabilityMap_of_error_probability
    (fun _ => walkLawPM μ) (fun n => measurable_leafClockPath (μ 0).toReal B n ha) hGm
    ?_ hG
  intro ε hε
  simpa only [Real.dist_eq, sub_zero, abs_of_nonneg dist_nonneg, d] using herr ε hε

end BGWLeaves.ClassicalLimits.WalkClock
