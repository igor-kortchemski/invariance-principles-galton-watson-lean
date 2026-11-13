module

public import BGWLeaves.LeafLimits.Defs
public import BGWLeaves.Coding.Defs
public import BGW.StableTrees.DiscreteForestTreeLaws
public import BGW.StableTrees.JointExcursion
public import BGWLeaves.ClassicalLimits
public import BGWLeaves.Conditioning
public import BGWLeaves.Coding
public import BGW.MetricMeasure.WeakPerturbation
public import BGW.StableTrees.UnitExcursionDensityTransfer
public import BGW.StableTrees.ExcursionMarkovConsequences
public import BGW.StableTrees.UnitExcursionLawBasic
public import BGW.Skorokhod.Measurable

/-!
# Stopped-tail convergence (first step of Lemma 5.8)

Source: arXiv:1110.2163v4, proof of Lemma 5.8
(`lem:absolue`, lines 1505-1530 of the LaTeX source).

Under `P_μ[· | ζ ≥ n]`, the pair of Lemma 5.8 at `r = n` (walk and height read up to the tree leaf
clock `T_{a μ₀ n}`, time change `t/a`) converges on `[0,a]` to `(X, H)` under `N(· | ζ > 1)`.

Route (the paper's): the pair `absPair` is the time-space scaling of the deterministic-clock pair
`TailPair.treePairPath B n (2a)` with time factor `S_n = T_{a μ₀ n}/(a n)` and space factors `1`,
outside the clock-deviation event of Lemma 5.6(i) (`lem_CVf_i`) and the null event of infinite trees
(`absPair_eq_timeSpaceScale`, `clock_bounds`).  Theorem 5.1 (`thm_cvW`, horizon `2a`) and Lemma 5.7
in pair form (`lem_CVproba_pair`) give the limit `(tailExcLaw θ (2a)).map (restrictPair _)`, which is
`tailExcLaw θ a` (BGW `tailExcLaw_map_restrictPair`); the discrepancy event has vanishing probability
(BGW `tendsto_probabilityMap_of_error_probability`).  The continuity hypothesis of Lemma 5.7 is the
absence of fixed jumps under `N` (`ae_continuousAt_tailExcLaw`).
-/

@[expose] public section

namespace BGWLeaves.LeafLimits.AbsolueTail

open MeasureTheory ProbabilityTheory Filter BGW
open BGW.StableTrees BGW.LocallyFinite BGWLeaves.StableAnalysis
open scoped ENNReal NNReal Topology

/-- Under `N(· | ζ > 1)` on the horizon `[0,T]`, the path is almost surely continuous at a fixed time
`a ∈ (0, T]` (no fixed jump under `N`, BGW `N_noFixedJump`). -/
theorem ae_continuousAt_tailExcLaw {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {a T : ℝ≥0} (ha : 0 < a)
    (haT : a ≤ T) :
    ∀ᵐ z : Skorokhod.D (T : ℝ) ℝ × C(Set.Icc (0 : ℝ) T, ℝ) ∂(tailExcLaw θ T).toMeasure,
      ContinuousAt (z.1 : Set.Icc (0 : ℝ) T → ℝ)
        ⟨(a : ℝ), a.coe_nonneg, NNReal.coe_le_coe.2 haT⟩ := by
  let t : Set.Icc (0 : ℝ) T := ⟨(a : ℝ), a.coe_nonneg, NNReal.coe_le_coe.2 haT⟩
  have hleft : ∀ᵐ z : Skorokhod.D (T : ℝ) ℝ × C(Set.Icc (0 : ℝ) T, ℝ)
      ∂(tailExcLaw θ T).toMeasure, Function.leftLim (z.1 : Set.Icc (0 : ℝ) T → ℝ) t = z.1 t := by
    change ∀ᵐ z ∂((tailExcursionLaw θ : Measure Excursion).map (excursionPair θ T)), _
    apply (ae_map_iff (measurable_excursionPair θ T).aemeasurable
      (measurableSet_eq_fun ((Skorokhod.measurable_leftLim_eval t).comp measurable_fst)
        ((Skorokhod.measurable_eval t).comp measurable_fst))).mpr
    rw [coe_tailExcursionLaw hθ, tailExcursionMeasure]
    apply Measure.ae_smul_measure
    have hj := ae_restrict_of_ae (s := {e : Excursion | (1 : ℝ) < (e.lifetime : ℝ)})
      (N_noFixedJump hθ a ha)
    filter_upwards [hj] with e he
    change Function.leftLim (excursionRestrict T e) t = excursionRestrict T e t
    rw [leftLim_excursionRestrict T a ha haT e]
    exact he
  filter_upwards [hleft] with z hl
  rw [continuousAt_iff_continuous_left'_right']
  refine ⟨?_, (Skorokhod.isCadlag z.1).isRightContinuous _⟩
  change Tendsto z.1 (𝓝[<] t) (𝓝 (z.1 t))
  simpa only [hl] using (Skorokhod.isCadlag z.1).tendsto_nhdsLT_leftLim t

/-- Deterministic clock bounds: if `|K/n - a| ≤ δ ≤ a/2` then `K ≥ 1`, `K ≤ 2an` and
`|K/(an) - 1| ≤ δ/a`. -/
theorem clock_bounds {a δ : ℝ} {K n : ℕ} (ha : 0 < a) (hn : 1 ≤ n) (hδ : δ ≤ a / 2)
    (hK : |(K : ℝ) / n - a| ≤ δ) :
    1 ≤ K ∧ (K : ℝ) ≤ 2 * a * n ∧ |(K : ℝ) / (a * n) - 1| ≤ δ / a := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  obtain ⟨hlo, hhi⟩ := abs_le.mp hK
  refine ⟨?_, ?_, ?_⟩
  · by_contra h
    have hK0 : K = 0 := by omega
    rw [hK0, Nat.cast_zero, zero_div, zero_sub] at hlo
    linarith
  · have h2 : (K : ℝ) / n ≤ 2 * a := by linarith
    rw [div_le_iff₀ hn'] at h2
    linarith
  · have ha' : a ≠ 0 := ha.ne'
    have hn'' : (n : ℝ) ≠ 0 := hn'.ne'
    have he : (K : ℝ) / (a * n) - 1 = ((K : ℝ) / n - a) / a := by
      field_simp
    rw [he, abs_div, abs_of_pos ha]
    exact div_le_div_of_nonneg_right hK ha.le

/-- **Pathwise identity**: when the leaf clock `K = T_{a μ₀ n}(τ)` satisfies `K ≤ 2an`, the pair of
Lemma 5.8 is the time-space scaling (time factor `s = K/(an)`, space factors `1`) of the
deterministic-clock pair `treePairPath B n (2a)`. -/
theorem absPair_eq_timeSpaceScale (μ0 : ℝ) (B : ℕ → ℝ) (n : ℕ) (a : ℝ≥0) (ha : 0 < (a : ℝ))
    (τ : LocallyFinite.Tree) (s : Set.Ioi (0 : ℝ)) (hn : 1 ≤ n)
    (hs : (s : ℝ) = (treeLeafClock τ ((a : ℝ) * μ0 * n) : ℝ) / (a * n))
    (hK : (treeLeafClock τ ((a : ℝ) * μ0 * n) : ℝ) ≤ 2 * a * n) :
    absPair μ0 B n a ha τ =
      (Skorokhod.timeSpaceScale (a : ℝ) (2 * a : ℝ≥0).coe_nonneg
          ((TailPair.treePairPath B n (2 * a) τ).1, (1 : ℝ × ℝ).1, s),
        Skorokhod.timeSpaceScaleC (a : ℝ) (2 * a : ℝ≥0).coe_nonneg
          ((TailPair.treePairPath B n (2 * a) τ).2, (1 : ℝ × ℝ).2, s)) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have ha' : (a : ℝ) ≠ 0 := ha.ne'
  have hn'' : (n : ℝ) ≠ 0 := hn'.ne'
  set K : ℕ := treeLeafClock τ ((a : ℝ) * μ0 * n) with hKdef
  have hT2 : ((2 * a : ℝ≥0) : ℝ) = 2 * (a : ℝ) := by push_cast; ring
  have hst (t : Set.Icc (0 : ℝ) a) : (s : ℝ) * t ≤ ((2 * a : ℝ≥0) : ℝ) := by
    rw [hs, hT2]
    calc (K : ℝ) / (a * n) * t ≤ (K : ℝ) / (a * n) * a :=
          mul_le_mul_of_nonneg_left t.2.2 (by positivity)
      _ = (K : ℝ) / n := by field_simp
      _ ≤ 2 * a := by rw [div_le_iff₀ hn']; linarith
  have hlin (t : Set.Icc (0 : ℝ) a) :
      (n : ℝ) * min ((s : ℝ) * t) ((2 * a : ℝ≥0) : ℝ) = (K : ℝ) * t / a := by
    rw [min_eq_left (hst t), hs]
    field_simp
  apply Prod.ext
  · apply Skorokhod.ext
    intro t
    have h1 : 1 / (a : ℝ) * t ≤ 1 := by
      rw [one_div_mul_eq_div, div_le_one ha]
      exact t.2.2
    have e : (K : ℝ) * (1 / (a : ℝ) * t) = (K : ℝ) * t / a := by ring
    change (1 : ℝ) * Skorokhod.realStepPath 1 K (B n) (PathTail.treeIncrementSeq τ) _ =
      (1 : ℝ × ℝ).1 * Skorokhod.realStepPath ((2 * a : ℝ≥0) : ℝ) n (B n)
        (PathTail.treeIncrementSeq τ) _
    rw [Skorokhod.realStepPath_apply, Skorokhod.realStepPath_apply]
    dsimp only
    rw [min_eq_left h1, hlin t, e, Prod.fst_one]
  · apply ContinuousMap.ext
    intro t
    change B n / n * TailPair.treeHeightLin τ ((K : ℝ) * t / a) =
      (1 : ℝ × ℝ).2 * TailPair.treeHeightPath B n (2 * a) τ _
    rw [TailPair.treeHeightPath, dite_eq_left (TailPair.continuous_treeHeightLin τ)]
    dsimp only [ContinuousMap.coe_mk]
    rw [hlin t, Prod.snd_one, one_mul]

/-- **Stopped-tail convergence (T)**: under `P_μ[· | ζ ≥ n]`, the pair of Lemma 5.8 at `r = n` (walk
and height read up to the tree leaf clock `T_{a μ₀ n}`, time change `t/a`, divisor `B_n`, height
amplitude `B_n/n`) converges on `[0,a]` to `(X, H)` under `N(· | ζ > 1)` (`tailExcLaw θ a`).
Theorem 5.1 (`thm_cvW`), Lemma 5.6(i) (`lem_CVf_i`) and Lemma 5.7 (`lem_CVproba_pair`). -/
theorem tail_absPair_tendsto {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ} (hc : IsCritical μ)
    (hne : μ 1 ≠ 1) (hap : Aperiodic μ)
    (hB : IsRealStableAttracted (realOffspringStepLaw μ) θ B)
    {a : ℝ≥0} (ha : a ∈ Set.Ioo (0 : ℝ≥0) 1) :
    Tendsto (fun n : ℕ => (DiscreteForest.tailTreeLaw μ n).map
        (absPair (μ 0).toReal B n a (NNReal.coe_pos.mpr ha.1)))
      atTop (𝓝 (tailExcLaw θ a)) := by
  have hDA : ∃ b, StableDomain μ θ b :=
    (BGWLeaves.stableDomain_of_isRealStableAttracted hc hne hB).1
  have hθ : 1 < θ ∧ θ ≤ 2 := by
    obtain ⟨b, hb⟩ := hDA
    exact hb.alpha_mem
  have ha0 : (0 : ℝ) < a := NNReal.coe_pos.mpr ha.1
  have ha1 : (a : ℝ) < 1 := by exact_mod_cast ha.2
  have haT : a < 2 * a := by
    calc a = 1 * a := (one_mul a).symm
      _ < 2 * a := mul_lt_mul_of_pos_right (by norm_num) ha.1
  have hT0 : (0 : ℝ≥0) < 2 * a := ha.1.trans haT
  /- The data of Lemma 5.7. -/
  let P : ℕ → ProbabilityMeasure LocallyFinite.Tree := fun n => DiscreteForest.tailTreeLaw μ n
  let K : ℕ → LocallyFinite.Tree → ℕ := fun n τ => treeLeafClock τ ((a : ℝ) * (μ 0).toReal * n)
  have hSpos (n : ℕ) (τ : LocallyFinite.Tree) :
      0 < max (K n τ : ℝ) 1 / ((a : ℝ) * max (n : ℝ) 1) :=
    div_pos (lt_max_of_lt_right one_pos) (mul_pos ha0 (lt_max_of_lt_right one_pos))
  let S : ℕ → LocallyFinite.Tree → Set.Ioi (0 : ℝ) := fun n τ => ⟨_, hSpos n τ⟩
  let Z : ℕ → LocallyFinite.Tree →
      Skorokhod.D ((2 * a : ℝ≥0) : ℝ) ℝ × C(Set.Icc (0 : ℝ) ((2 * a : ℝ≥0) : ℝ), ℝ) :=
    fun n => TailPair.treePairPath B n (2 * a)
  let Kf : ℕ → LocallyFinite.Tree → ℝ × ℝ := fun _ _ => 1
  have hZm (n : ℕ) : Measurable (Z n) := TailPair.measurable_treePairPath B n (2 * a)
  have hKm (n : ℕ) : Measurable (Kf n) := measurable_const
  have hSm (n : ℕ) : Measurable (fun τ => (S n τ : ℝ)) :=
    (measurable_from_nat (f := fun k : ℕ => max (k : ℝ) 1 / ((a : ℝ) * max (n : ℝ) 1))).comp
      (measurable_treeLeafClock _)
  have hSeq (n : ℕ) (hn : 1 ≤ n) (τ : LocallyFinite.Tree) (hK1 : 1 ≤ K n τ) :
      ((S n τ : Set.Ioi (0 : ℝ)) : ℝ) = (K n τ : ℝ) / (a * n) := by
    change max (K n τ : ℝ) 1 / ((a : ℝ) * max (n : ℝ) 1) = _
    rw [max_eq_left (by exact_mod_cast hK1), max_eq_left (by exact_mod_cast hn)]
  /- The bad events: infinite trees, and the clock-deviation event of Lemma 5.6(i). -/
  have hmin : 0 < min ((a : ℝ) / 2) ((1 - a) / 2) := lt_min (by linarith) (by linarith)
  obtain ⟨α, hα0, hα⟩ : ∃ α : ℝ, 0 < α ∧ α < min ((a : ℝ) / 2) ((1 - a) / 2) :=
    ⟨_, half_pos hmin, half_lt_self hmin⟩
  have hCV := BGWLeaves.lem_CVf_i hc hne hap hDA (a := (a : ℝ)) ⟨ha0, ha1⟩ hα
  let A : ℕ → Set LocallyFinite.Tree := fun n => finiteTreeEvent fun t =>
    ∃ b ∈ Set.Ioo ((a : ℝ) - α) ((a : ℝ) + α),
      ClockDev n b (treeLeafTime t ⌊(μ 0).toReal * b * n⌋₊)
  let Bad : ℕ → Set LocallyFinite.Tree := fun n => {τ | ¬ FiniteVertices τ} ∪ A n
  have hPeq (n : ℕ) : ((P n : ProbabilityMeasure LocallyFinite.Tree) : Measure LocallyFinite.Tree) =
      (bienaymeLaw μ.toMeasure)[|sizeGeEvent n] := by
    have h := DiscreteForest.bienaymeLaw_sizeGeEvent_ne_zero μ hc hne n
    have heq : DiscreteForest.tailTreeLaw μ n =
        (⟨(bienaymeLaw μ.toMeasure)[|Attraction.sizeGeEvent n],
          cond_isProbabilityMeasure h⟩ : ProbabilityMeasure LocallyFinite.Tree) :=
      dite_eq_left h
    exact congrArg ProbabilityMeasure.toMeasure heq
  have hm : ∫⁻ k : ℕ, (k : ℝ≥0∞) ∂μ.toMeasure ≤ 1 := by
    have h : ∫⁻ k : ℕ, (k : ℝ≥0∞) ∂μ.toMeasure = ∑' k : ℕ, (k : ℝ≥0∞) * μ k := by
      rw [lintegral_countable']
      refine tsum_congr fun k => ?_
      rw [PMF.toMeasure_apply_singleton μ k (measurableSet_singleton _)]
    rw [h]
    exact hc.le
  have hne' : μ.toMeasure {1} ≠ 1 := by
    rwa [PMF.toMeasure_apply_singleton μ 1 (measurableSet_singleton _)]
  have hInf (n : ℕ) : (P n : Measure LocallyFinite.Tree) {τ | ¬ FiniteVertices τ} = 0 := by
    rw [hPeq]
    exact cond_absolutelyContinuous
      (ae_iff.mp (ae_finiteVertices_bienaymeLaw μ.toMeasure hm hne'))
  have hBad : Tendsto (fun n => (P n : Measure LocallyFinite.Tree).real (Bad n)) atTop (𝓝 0) := by
    refine squeeze_zero (fun n => measureReal_nonneg) (fun n => ?_) hCV
    calc (P n : Measure LocallyFinite.Tree).real (Bad n)
        ≤ (P n : Measure LocallyFinite.Tree).real {τ | ¬ FiniteVertices τ} +
            (P n : Measure LocallyFinite.Tree).real (A n) := measureReal_union_le _ _
      _ = (P n : Measure LocallyFinite.Tree).real (A n) := by
          rw [measureReal_def (P n : Measure LocallyFinite.Tree) {τ | ¬ FiniteVertices τ},
            hInf n, ENNReal.toReal_zero, zero_add]
      _ = _ := by rw [hPeq]
  /- Outside the bad event, the clock is close to `a n`. -/
  have hgood (n : ℕ) (hn : 1 ≤ n) (hδn : (n : ℝ) ^ (-(1 / 4 : ℝ)) ≤ a / 2)
      (τ : LocallyFinite.Tree) (hτ : τ ∉ Bad n) :
      1 ≤ K n τ ∧ (K n τ : ℝ) ≤ 2 * a * n ∧
        |(K n τ : ℝ) / (a * n) - 1| ≤ (n : ℝ) ^ (-(1 / 4 : ℝ)) / a := by
    have hfin : FiniteVertices τ := by
      by_contra h
      exact hτ (Or.inl h)
    have hA : τ ∉ A n := fun h => hτ (Or.inr h)
    obtain ⟨t, rfl⟩ := (exists_toLocallyFinite_iff τ).mpr hfin
    have hcd : ¬ ClockDev n a (treeLeafTime t ⌊(μ 0).toReal * a * n⌋₊) := by
      intro h
      apply hA
      simp only [A, finiteTreeEvent, Set.mem_ofPred_eq]
      exact ⟨t, rfl, a, ⟨by linarith, by linarith⟩, h⟩
    simp only [ClockDev, not_or, not_lt] at hcd
    have hKeq : K n t.toLocallyFinite = (treeLeafTime t ⌊(μ 0).toReal * a * n⌋₊).toNat := by
      simp only [K, treeLeafClock, toPlaneTree_toLocallyFinite, mul_comm (a : ℝ) (μ 0).toReal]
    rw [hKeq]
    exact clock_bounds ha0 hn hδn hcd.2
  have hδ : Tendsto (fun n : ℕ => (n : ℝ) ^ (-(1 / 4 : ℝ))) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  have hδa : ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ (-(1 / 4 : ℝ)) ≤ a / 2 :=
    hδ.eventually (ge_mem_nhds (by linarith))
  /- The hypotheses of Lemma 5.7. -/
  have hK : ∀ ε > 0, Tendsto (fun n => (P n).toMeasure.real
      {τ | ε < dist (Kf n τ) 1}) atTop (𝓝 0) := by
    intro ε hε
    have he (n : ℕ) : {τ : LocallyFinite.Tree | ε < dist (Kf n τ) 1} = ∅ := by
      ext τ
      simp only [Kf, dist_self, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_lt]
      exact hε.le
    simp only [he, measureReal_empty]
    exact tendsto_const_nhds
  have hS : ∀ ε > 0, Tendsto (fun n => (P n).toMeasure.real
      {τ | ε < dist ((S n τ : ℝ)) 1}) atTop (𝓝 0) := by
    intro ε hε
    refine squeeze_zero' (Eventually.of_forall fun n => measureReal_nonneg) ?_ hBad
    have hδε : ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ (-(1 / 4 : ℝ)) < ε * a :=
      hδ.eventually (gt_mem_nhds (mul_pos hε ha0))
    filter_upwards [eventually_ge_atTop 1, hδa, hδε] with n hn hn2 hn3
    refine measureReal_mono (fun τ hτ => ?_) (measure_ne_top _ _)
    by_contra hcon
    obtain ⟨hK1, -, hK3⟩ := hgood n hn hn2 τ hcon
    rw [Set.mem_ofPred_eq, Real.dist_eq, hSeq n hn τ hK1] at hτ
    have h4 : (n : ℝ) ^ (-(1 / 4 : ℝ)) / a < ε := by
      rw [div_lt_iff₀ ha0]
      exact hn3
    linarith
  have hGm (n : ℕ) : Measurable (fun τ =>
      (Skorokhod.timeSpaceScale (a : ℝ) (2 * a).coe_nonneg ((Z n τ).1, (Kf n τ).1, S n τ),
        Skorokhod.timeSpaceScaleC (a : ℝ) (2 * a).coe_nonneg ((Z n τ).2, (Kf n τ).2, S n τ))) :=
    ((measurable_timeSpaceScale (a : ℝ) _).comp
      ((hZm n).fst.prodMk ((hKm n).fst.prodMk (hSm n).subtype_mk))).prodMk
    ((measurable_timeSpaceScaleC (a : ℝ) _).comp
      ((hZm n).snd.prodMk ((hKm n).snd.prodMk (hSm n).subtype_mk)))
  have herr : ∀ ε > 0, Tendsto (fun n => (P n : Measure LocallyFinite.Tree).real
      {τ | ε < dist (absPair (μ 0).toReal B n a (NNReal.coe_pos.mpr ha.1) τ)
        (Skorokhod.timeSpaceScale (a : ℝ) (2 * a).coe_nonneg ((Z n τ).1, (Kf n τ).1, S n τ),
          Skorokhod.timeSpaceScaleC (a : ℝ) (2 * a).coe_nonneg
            ((Z n τ).2, (Kf n τ).2, S n τ))}) atTop (𝓝 0) := by
    intro ε hε
    refine squeeze_zero' (Eventually.of_forall fun n => measureReal_nonneg) ?_ hBad
    filter_upwards [eventually_ge_atTop 1, hδa] with n hn hn2
    refine measureReal_mono (fun τ hτ => ?_) (measure_ne_top _ _)
    by_contra hcon
    obtain ⟨hK1, hK2, -⟩ := hgood n hn hn2 τ hcon
    have heq := absPair_eq_timeSpaceScale (μ 0).toReal B n a ha0 τ (S n τ) hn
      (hSeq n hn τ hK1) hK2
    rw [Set.mem_ofPred_eq] at hτ
    exact absurd (lt_of_lt_of_eq hτ (dist_eq_zero.mpr heq)) (not_lt.mpr hε.le)
  /- Lemma 5.7 applied to Theorem 5.1 on the horizon `2a`, then projectivity. -/
  have hlim := BGWLeaves.lem_CVproba_pair ha.1 haT P Z Kf S hZm hKm hSm (tailExcLaw θ (2 * a))
    (BGWLeaves.thm_cvW hc hne hB hT0) (ae_continuousAt_tailExcLaw hθ ha.1 haT.le) hK hS
  rw [tailExcLaw_map_restrictPair θ haT.le] at hlim
  exact BGW.MetricMeasure.tendsto_probabilityMap_of_error_probability P
    (fun n => measurable_absPair _ _ _ _ _) hGm herr hlim

end BGWLeaves.LeafLimits.AbsolueTail
