module

public import BGWLeaves.MaxDegree.Defs
public import BGWLeaves.Vervaat
public import BGWLeaves.MaxDegree.Bridge
public import BGWLeaves.MaxDegree.Concentration
import BGWLeaves.MaxDegree.Law
import BGWLeaves.MaxDegree.Transfer
import BGWLeaves.LeafMass
import BGWLeaves.GeneralA.Arithmetic
import BGWLeaves.StableAnalysis.DomainCriterion

/-!
# M9 provider `Principles`

Provider for the maximum-degree principles (with `hnl`) and the inputs of the case split of Theorem 7.1(ii): `maxDegree_lower_principle`, `maxDegree_upper_principle`, `HypH.not_isLatticeLaw_etaLaw_of_unbounded`, `thm_max_ii_of_bounded`, `leafProb_ne_zero_frequently`, `displayedLaw_not_isLatticeLaw_etaLaw`.  The theorems to be proved here are the registered holes of
`BGWLeaves.MaxDegree`; they are exported in namespace `BGWLeaves.MaxDegree.Principles` with exactly the types of the
statements file.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter BGW
open BGW.StableTrees BGW.LocallyFinite BGWLeaves.StableAnalysis BGWLeaves
open scoped ENNReal NNReal Topology

local notation "𝐏w[" μ "]" => Measure.infinitePi (fun _ : ℕ => μ)

namespace BGWLeaves.MaxDegree.Principles

/-! ## Two consecutive atoms: `etaLaw` is not lattice -/

/-- If `μ(k) ≠ 0` and `μ(k+1) ≠ 0` for some `k ≥ 1`, the law of `K - 1` given `K ≥ 1` has the consecutive atoms
`k - 1`, `k`, so it is not lattice. -/
theorem not_isLatticeLaw_etaLaw_of_consecutive {μ : PMF ℕ} {k : ℕ} (hk : 1 ≤ k) (h1 : μ k ≠ 0)
    (h2 : μ (k + 1) ≠ 0) : ¬ IsLatticeLaw (etaLaw μ) := by
  rintro ⟨b, d, hd, hae⟩
  have key : ∀ j : ℕ, 1 ≤ j → μ j ≠ 0 → (d : ℤ) ∣ ((j : ℤ) - 1) - b := by
    intro j hj hμ
    by_contra hnd
    have hmeas : Measurable (fun k : ℕ => (k : ℤ) - 1) := measurable_of_countable _
    have hj0 : μ.toMeasure {j} ≠ 0 := by
      rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]; exact hμ
    have hne : etaLaw μ {(j : ℤ) - 1} ≠ 0 := by
      unfold etaLaw
      rw [Measure.map_apply hmeas (measurableSet_singleton _), cond_apply measurableSet_Ici]
      refine mul_ne_zero (ENNReal.inv_ne_zero.2 (measure_ne_top _ _)) ?_
      intro h0
      apply hj0
      refine measure_mono_null ?_ h0
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst hx
      exact ⟨hj, by simp⟩
    apply hne
    refine measure_mono_null ?_ (ae_iff.1 hae)
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst hz
    exact hnd
  have a := key k hk h1
  have b' := key (k + 1) (by omega) h2
  have h3 := dvd_sub b' a
  have e : (((k + 1 : ℕ) : ℤ) - 1 - b) - ((k : ℤ) - 1 - b) = 1 := by push_cast; ring
  rw [e] at h3
  have := Int.le_of_dvd one_pos h3
  omega

/-- The displayed law of Remark 7.3 (`μ(2), μ(3) > 0`: consecutive atoms) satisfies `hnl`. -/
theorem displayedLaw_not_isLatticeLaw_etaLaw {μ : PMF ℕ} (hμ : IsDisplayedLaw μ) :
    ¬ IsLatticeLaw (etaLaw μ) := by
  have hq : 2 - Real.sqrt 2 ≠ 0 := by
    have : Real.sqrt 2 < 2 := by
      rw [Real.sqrt_lt' (by norm_num)]; norm_num
    linarith
  have h2 : μ 2 ≠ 0 := by
    rw [hμ 2]
    simp [displayedWeight]
  have h3 : μ 3 ≠ 0 := by
    rw [hμ 3]
    simp [displayedWeight]
    exact hq
  exact not_isLatticeLaw_etaLaw_of_consecutive (k := 2) (by norm_num) h2 h3

/-- `𝓗` and unbounded support give `hnl`: `μ(k) > 0` for all large `k`. -/
theorem HypH.not_isLatticeLaw_etaLaw_of_unbounded {μ : PMF ℕ} (h : HypH μ)
    (hub : ∀ K : ℕ, ∃ k : ℕ, K < k ∧ μ k ≠ 0) : ¬ IsLatticeLaw (etaLaw μ) := by
  obtain ⟨N, hN1, hN⟩ := Law.reg_E2 h (w := 2) one_lt_two
  have hpos : ∀ k : ℕ, N ≤ k → μ k ≠ 0 := by
    intro k hk hμk
    obtain ⟨j, hj, hμj⟩ := hub k
    have h1 := hN k j hk hj.le
    have hk0 : (μ k).toReal = 0 := by rw [hμk]; simp
    have hk1 : (k : ℝ) ≠ 0 := by
      have : 1 ≤ k := le_trans hN1 hk
      exact_mod_cast (by omega : k ≠ 0)
    have h2 : (μ k).toReal ^ (1 / (k : ℝ)) = 0 := by
      rw [hk0]; exact Real.zero_rpow (by simpa using hk1)
    rw [h2, mul_zero] at h1
    have hjpos : 0 < (μ j).toReal := ENNReal.toReal_pos hμj (μ.apply_ne_top j)
    have := Real.rpow_pos_of_pos hjpos (1 / (j : ℝ))
    linarith
  exact not_isLatticeLaw_etaLaw_of_consecutive (k := N) hN1 (hpos N le_rfl) (hpos (N + 1) (by omega))

/-! ## Non-null leaf counts -/

/-- `P_μ[λ = n] > 0` for infinitely many `n`. -/
theorem leafProb_ne_zero_frequently {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1) :
    ∃ᶠ n : ℕ in atTop, leafProb μ n ≠ 0 := by
  obtain ⟨N, hN⟩ := ltn_i_arith hc hne
  have hg := GeneralA.Arithmetic.arithFactor_pos hc hne {0}
  rw [Filter.frequently_atTop]
  intro a
  refine ⟨arithFactor μ {0} * (N + a) + 1, ?_, ?_⟩
  · nlinarith
  · have hge : N ≤ arithFactor μ {0} * (N + a) := by nlinarith
    exact ((hN _ hge).2 (dvd_mul_right _ _)).ne'

/-! ## Transfer of the cyclic maximum (`eq:Deltanon`), restated with the provider `Transfer` -/

theorem eqDeltanon_lt (μ : Measure ℕ) [IsProbabilityMeasure μ] {n : ℕ} (hn : 1 ≤ n) (p : ℝ) :
    ((bienaymeLaw μ)[|leafCountEvent n]) (finiteTreeEvent fun t => (maxDegree t : ℝ) < p + 1) =
      ((𝐏w[μ])[|bridgeAtMark n]) (bridgeStepsIn n {x | StepsLt p x}) := by
  have h1 : (finiteTreeEvent fun t => (maxDegree t : ℝ) < p + 1) = treeStepsIn {x | StepsLt p x} := by
    unfold treeStepsIn
    congr 1
    funext t
    exact propext (Transfer.maxDegree_lt_iff t p)
  rw [h1]
  exact Transfer.transfer_vervaat_invariant μ hn _ (fun x => stepsLt_vervaat p x)

theorem eqDeltanon_gt (μ : Measure ℕ) [IsProbabilityMeasure μ] {n : ℕ} (hn : 1 ≤ n) (q : ℝ) :
    ((bienaymeLaw μ)[|leafCountEvent n]) (finiteTreeEvent fun t => q + 1 < (maxDegree t : ℝ)) =
      ((𝐏w[μ])[|bridgeAtMark n]) (bridgeStepsIn n {x | StepsGt q x}) := by
  have h1 : (finiteTreeEvent fun t => q + 1 < (maxDegree t : ℝ)) = treeStepsIn {x | StepsGt q x} := by
    unfold treeStepsIn
    congr 1
    funext t
    exact propext (Transfer.lt_maxDegree_iff t q)
  rw [h1]
  exact Transfer.transfer_vervaat_invariant μ hn _ (fun x => stepsGt_vervaat q x)

/-! ## Bounded support -/

/-- A polynomial lower bound for the non-null leaf probabilities (sealed Theorem 3.1, finite variance). -/
theorem leafProb_poly_lower {μ : PMF ℕ} (h : HypH μ) :
    ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → leafProb μ n ≠ 0 →
      c / (n : ℝ) ^ 2 ≤ leafProb μ n := by
  have hc := h.critical
  have hne := h.nondegenerate
  have hap := h.aperiodic
  have hfin := h.integrable_sq
  have hequiv := thm_ltn_finiteVariance_arith hc hne hap hfin
  have hμ0 := Law.HypH.mu_zero_pos h
  have hg : 0 < arithFactor μ {0} := GeneralA.Arithmetic.arithFactor_pos hc hne {0}
  have hσ : 0 < variance (stepLaw μ) := by
    obtain ⟨a, ha⟩ := h.stableDomain
    exact DomainCriterion.variance_pos_of_integrable_sq (stableDomain_isStableAttracted ha)
      (integrable_stepLaw hc) hfin
  set L : ℝ := Real.sqrt ((μ 0).toReal / (2 * Real.pi * variance (stepLaw μ))) *
    (arithFactor μ {0} : ℝ) with hL
  have hLpos : 0 < L := by
    rw [hL]
    have : 0 < (μ 0).toReal / (2 * Real.pi * variance (stepLaw μ)) := by positivity
    have := Real.sqrt_pos.2 this
    positivity
  have hev := hequiv.isLittleO.def (show (0 : ℝ) < 1 / 2 by norm_num)
  rw [Filter.eventually_inf_principal] at hev
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.1 hev
  obtain ⟨N₂, hN₂⟩ := ltn_i_arith hc hne
  refine ⟨L / 2, by positivity, N₁ + N₂ + 2, fun n hn hne0 => ?_⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hpos : 0 < leafProb μ (m + 1) := lt_of_le_of_ne measureReal_nonneg (Ne.symm hne0)
  have hdvd : arithFactor μ {0} ∣ m := (hN₂ m (by omega)).1 hpos
  have h1 := hN₁ m (by omega) hdvd
  simp only [Pi.sub_apply, Real.norm_eq_abs] at h1
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (by omega : 1 ≤ m)
  have hv : 0 ≤ L * (m : ℝ) ^ (-(3 : ℝ) / 2) := by positivity
  rw [abs_of_nonneg hv] at h1
  have h2 := (abs_le.1 h1).1
  have h3 : (m : ℝ) ^ ((3 : ℝ) / 2) ≤ (m : ℝ) ^ (2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hm1 (by norm_num)
  have h4 : (m : ℝ) ^ (-(3 : ℝ) / 2) = ((m : ℝ) ^ ((3 : ℝ) / 2))⁻¹ := by
    rw [neg_div, Real.rpow_neg (Nat.cast_nonneg _)]
  have h5 : ((m : ℝ) ^ (2 : ℝ)) = (m : ℝ) ^ 2 := by exact_mod_cast Real.rpow_natCast (m : ℝ) 2
  have hmpos : (0 : ℝ) < (m : ℝ) ^ ((3 : ℝ) / 2) := Real.rpow_pos_of_pos (by linarith) _
  have h6 : 1 / ((m : ℝ) + 1) ^ 2 ≤ (m : ℝ) ^ (-(3 : ℝ) / 2) := by
    rw [h4, one_div]
    apply inv_anti₀ hmpos
    calc (m : ℝ) ^ ((3 : ℝ) / 2) ≤ (m : ℝ) ^ (2 : ℝ) := h3
      _ = (m : ℝ) ^ 2 := h5
      _ ≤ ((m : ℝ) + 1) ^ 2 := by nlinarith
  have h7 : leafProb μ (m + 1) ≥ (1 / 2) * (L * (m : ℝ) ^ (-(3 : ℝ) / 2)) := by
    linarith
  push_cast
  calc L / 2 / ((m : ℝ) + 1) ^ 2 = (L / 2) * (1 / ((m : ℝ) + 1) ^ 2) := by ring
    _ ≤ (L / 2) * (m : ℝ) ^ (-(3 : ℝ) / 2) := by gcongr
    _ ≤ _ := by linarith

/-- On the bridge, "all steps `< K - 1`" forces the first `n` coordinates to be `< K`. -/
theorem bridge_lt_le_pow (μ : PMF ℕ) (K n : ℕ) :
    (𝐏w[μ.toMeasure]) (bridgeStepsIn n {x | StepsLt ((K : ℝ) - 1) x}) ≤
      (μ.toMeasure {k : ℕ | k < K}) ^ n := by
  have hsub : bridgeStepsIn n {x | StepsLt ((K : ℝ) - 1) x} ⊆
      Set.pi (Finset.range n : Set ℕ) (fun _ => {k : ℕ | k < K}) := by
    rintro ω ⟨k, hk, -, hS⟩ i hi
    have hi' : i < n := by simpa using hi
    have hnk : n ≤ k := by
      have := hk.1
      rw [← this]
      unfold walkLeafCount
      exact (Finset.card_filter_le _ _).trans (by simp)
    have hmem : ((ω i : ℤ) - 1) ∈ walkWord ω k := by
      unfold walkWord
      rw [List.mem_map]
      exact ⟨i, List.mem_range.2 (by omega), rfl⟩
    have h1 := hS _ hmem
    have h2 : ((ω i : ℤ) : ℝ) - 1 < K - 1 := by push_cast at h1; exact h1
    have h3 : (ω i : ℝ) < K := by push_cast at h2; linarith
    exact_mod_cast h3
  calc _ ≤ (𝐏w[μ.toMeasure]) (Set.pi (Finset.range n : Set ℕ) (fun _ => {k : ℕ | k < K})) :=
        measure_mono hsub
    _ = _ := by
        have := Measure.infinitePi_pi (μ := fun _ : ℕ => μ.toMeasure) (s := Finset.range n)
          (t := fun _ => {k : ℕ | k < K}) (fun _ _ => MeasurableSet.of_discrete)
        rw [this]
        simp

/-- The bounded-support bridge estimate, in `ℝ`. -/
theorem real_cond_lt_le {μ : PMF ℕ} {K n : ℕ} (hn : 1 ≤ n) (hne : leafProb μ n ≠ 0) :
    (((bienaymeLaw μ.toMeasure)[|leafCountEvent n]).real
        (finiteTreeEvent fun t => (maxDegree t : ℝ) < ((K : ℝ) - 1) + 1)) ≤
      (μ.toMeasure {k : ℕ | k < K}).toReal ^ n / ((n : ℝ) * leafProb μ n) := by
  rw [Measure.real, eqDeltanon_lt _ hn]
  have hA : bridgeStepsIn n {x | StepsLt ((K : ℝ) - 1) x} ⊆ bridgeAtMark n :=
    fun ω ⟨k, hk, hs, _⟩ => ⟨k, hk, hs⟩
  rw [cond_apply (measurableSet_bridgeAtMark n), Set.inter_eq_right.2 hA,
    prop_vervaatdiscrete_total _ hn]
  have hpos : 0 < leafProb μ n := lt_of_le_of_ne measureReal_nonneg (Ne.symm hne)
  have hlp : leafProb μ n = (bienaymeLaw μ.toMeasure (leafCountEvent n)).toReal := rfl
  have h1 := bridge_lt_le_pow μ K n
  have hQ : ((𝐏w[μ.toMeasure]) (bridgeStepsIn n {x | StepsLt ((K : ℝ) - 1) x})).toReal ≤
      (μ.toMeasure {k : ℕ | k < K}).toReal ^ n := by
    rw [← ENNReal.toReal_pow]
    exact ENNReal.toReal_mono (ENNReal.pow_ne_top (measure_ne_top _ _)) h1
  rw [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_mul, ENNReal.toReal_natCast, ← hlp]
  rw [← div_eq_inv_mul]
  gcongr

/-- On trees, `Δ > K` has conditional probability `0` when `μ` is supported in `[0, K]`. -/
theorem real_cond_gt_eq_zero {μ : PMF ℕ} {K n : ℕ} (hb : ∀ k : ℕ, K < k → μ k = 0) (hn : 1 ≤ n) :
    ((bienaymeLaw μ.toMeasure)[|leafCountEvent n]).real
        (finiteTreeEvent fun t => ((K : ℝ) - 1) + 1 < (maxDegree t : ℝ)) = 0 := by
  rw [Measure.real, eqDeltanon_gt _ hn, cond_apply (measurableSet_bridgeAtMark n)]
  have hz : (𝐏w[μ.toMeasure]) (bridgeStepsIn n {x | StepsGt ((K : ℝ) - 1) x}) = 0 := by
    have hsub : bridgeStepsIn n {x | StepsGt ((K : ℝ) - 1) x} ⊆
        ⋃ i : ℕ, {ω : ℕ → ℕ | K < ω i} := by
      rintro ω ⟨k, hk, -, a, ha, hq⟩
      unfold walkWord at ha
      rw [List.mem_map] at ha
      obtain ⟨i, -, rfl⟩ := ha
      refine Set.mem_iUnion.2 ⟨i, ?_⟩
      have h2 : (K : ℝ) - 1 < (ω i : ℝ) - 1 := by push_cast at hq; exact hq
      have h3 : (K : ℝ) < ω i := by linarith
      exact_mod_cast h3
    refine measure_mono_null hsub (measure_iUnion_null fun i => ?_)
    have hmap := Measure.infinitePi_map_eval (fun _ : ℕ => μ.toMeasure) i
    have hm : Measurable (fun x : ℕ → ℕ => x i) := measurable_pi_apply i
    have : {ω : ℕ → ℕ | K < ω i} = (fun x : ℕ → ℕ => x i) ⁻¹' {k : ℕ | K < k} := rfl
    rw [this, ← Measure.map_apply hm MeasurableSet.of_discrete, hmap]
    rw [PMF.toMeasure_apply_eq_zero_iff _ MeasurableSet.of_discrete]
    rw [Set.disjoint_left]
    intro k hk hk'
    exact hk (hb k hk')
  have : (𝐏w[μ.toMeasure]) (bridgeAtMark n ∩ bridgeStepsIn n {x | StepsGt ((K : ℝ) - 1) x}) = 0 :=
    measure_mono_null Set.inter_subset_right hz
  rw [this]
  simp

/-- **Bounded support, elementary argument.** -/
theorem thm_max_ii_of_bounded {μ : PMF ℕ} (h : HypH μ) {K : ℕ} (hK : μ K ≠ 0)
    (hb : ∀ k : ℕ, K < k → μ k = 0) {ε : ℝ} (hε : 0 < ε) {δ : ℝ} (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → leafProb μ n ≠ 0 →
      1 - δ ≤ ((bienaymeLaw μ.toMeasure)[|leafCountEvent n]).real
        (finiteTreeEvent fun t =>
          (1 - ε) * (bigD μ n : ℝ) ≤ (maxDegree t : ℝ) ∧ (maxDegree t : ℝ) ≤ (1 + ε) * (bigD μ n : ℝ)) := by
  have hK1 : 1 ≤ K := by
    by_contra hK0
    have hK0' : K = 0 := by omega
    subst hK0'
    apply Law.mu_zero_ne_one h.critical
    have := μ.tsum_coe
    rw [tsum_eq_single 0 (fun k hk => hb k (Nat.pos_of_ne_zero hk))] at this
    exact this
  obtain ⟨c, hc, N₁, hN₁⟩ := leafProb_poly_lower h
  have hbig := Law.bigD_eq_of_bounded hK1 hK hb
  set r : ℝ := 1 - (μ K).toReal with hr
  have hμK : 0 < (μ K).toReal := ENNReal.toReal_pos hK (μ.apply_ne_top K)
  have hμK1 : (μ K).toReal ≤ 1 := by
    have := (ENNReal.toReal_le_toReal (μ.apply_ne_top K) ENNReal.one_ne_top).2 (PMF.coe_le_one μ K)
    simpa using this
  have hr0 : 0 ≤ r := by rw [hr]; linarith
  have hr1 : r < 1 := by rw [hr]; linarith
  have ha : (μ.toMeasure {k : ℕ | k < K}).toReal ≤ r := by
    have hdisj : Disjoint {k : ℕ | k < K} {K} := by
      rw [Set.disjoint_left]; intro k hk hk'; simp at hk hk'; omega
    have hu := measure_union (μ := μ.toMeasure) hdisj (measurableSet_singleton K)
    have hle : μ.toMeasure ({k : ℕ | k < K} ∪ {K}) ≤ 1 := prob_le_one
    rw [hu, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)] at hle
    have := (ENNReal.toReal_le_toReal (by
      exact ENNReal.add_ne_top.2 ⟨measure_ne_top _ _, μ.apply_ne_top K⟩) ENNReal.one_ne_top).2 hle
    rw [ENNReal.toReal_add (measure_ne_top _ _) (μ.apply_ne_top K), ENNReal.toReal_one] at this
    rw [hr]; linarith
  have ha0 : 0 ≤ (μ.toMeasure {k : ℕ | k < K}).toReal := ENNReal.toReal_nonneg
  have hlim := (tendsto_self_mul_const_pow_of_abs_lt_one (r := r)
    (by rw [abs_of_nonneg hr0]; exact hr1)).div_const c
  rw [zero_div] at hlim
  have hev : ∀ᶠ n : ℕ in atTop, (n : ℝ) * r ^ n / c < δ := hlim.eventually (gt_mem_nhds hδ)
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hev.and (hbig.and ((eventually_ge_atTop N₁).and
    (eventually_ge_atTop 1))))
  refine ⟨N, fun n hn hne => ?_⟩
  obtain ⟨hev', hbig', hN₁', hn1⟩ := hN n hn
  have key := cond_leafCount_window_ge (bienayme_leafCountEvent_ne_zero hne)
    (fun t => (maxDegree t : ℝ) < ((K : ℝ) - 1) + 1)
    (fun t => ((K : ℝ) - 1) + 1 < (maxDegree t : ℝ))
    (fun t => (1 - ε) * (bigD μ n : ℝ) ≤ (maxDegree t : ℝ) ∧
      (maxDegree t : ℝ) ≤ (1 + ε) * (bigD μ n : ℝ))
    (fun t _ => by
      simp only [hbig', sub_add_cancel]
      by_cases a : (maxDegree t : ℝ) < K
      · exact Or.inl a
      · by_cases b : (K : ℝ) < maxDegree t
        · exact Or.inr (Or.inl b)
        · refine Or.inr (Or.inr ⟨?_, ?_⟩)
          · have : (K : ℝ) ≤ maxDegree t := not_lt.1 a
            have : (0 : ℝ) ≤ K := Nat.cast_nonneg _
            nlinarith
          · have : (maxDegree t : ℝ) ≤ K := not_lt.1 b
            have : (0 : ℝ) ≤ K := Nat.cast_nonneg _
            nlinarith)
  rw [real_cond_gt_eq_zero hb hn1] at key
  have h1 := real_cond_lt_le (μ := μ) (K := K) hn1 hne
  have hpos : 0 < leafProb μ n := lt_of_le_of_ne measureReal_nonneg (Ne.symm hne)
  have hlow := hN₁ n hN₁' hne
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
  have h2 : (μ.toMeasure {k : ℕ | k < K}).toReal ^ n / ((n : ℝ) * leafProb μ n) ≤ (n : ℝ) * r ^ n / c := by
    have e1 : (μ.toMeasure {k : ℕ | k < K}).toReal ^ n ≤ r ^ n := pow_le_pow_left₀ ha0 ha n
    have e2 : c / (n : ℝ) ≤ (n : ℝ) * leafProb μ n := by
      have : c / (n : ℝ) ^ 2 * n ≤ leafProb μ n * n := by gcongr
      calc c / (n : ℝ) = c / (n : ℝ) ^ 2 * n := by field_simp
        _ ≤ leafProb μ n * n := this
        _ = _ := by ring
    calc (μ.toMeasure {k : ℕ | k < K}).toReal ^ n / ((n : ℝ) * leafProb μ n)
        ≤ r ^ n / ((n : ℝ) * leafProb μ n) := by gcongr
      _ ≤ r ^ n / (c / (n : ℝ)) := by
          apply div_le_div_of_nonneg_left (by positivity) (by positivity) e2
      _ = (n : ℝ) * r ^ n / c := by field_simp
  linarith

/-! ## The two principles: the chain, with the provider facts as explicit inputs -/

/-- The conclusion of `bridge_midpoint_tight` for the mark sequence `m`. -/
def MidTight (μ : PMF ℕ) (m : ℕ → ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ α : ℝ, 0 < α ∧ ∀ᶠ n : ℕ in atTop,
    ((𝐏w[μ.toMeasure])[|bridgeAtMark n]).real
      {ω | ∃ k, IsMarkTime (m n) ω k ∧ α * Real.sqrt n ≤ |(walkSum ω k : ℝ)|} < ε

/-- The conclusion of `eq_i_lower` for the mark sequence `m`. -/
def EqILower (μ : PMF ℕ) (m : ℕ → ℕ) : Prop :=
  ∀ α : ℝ, 0 < α → ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ p : ℝ,
    (((𝐏w[μ.toMeasure])[|bridgeAtMark n]).real (prefixStepsIn (m n) {x | StepsLt p x})) ≤
      ((𝐏w[μ.toMeasure])[|bridgeAtMark n]).real
          {ω | ∃ k, IsMarkTime (m n) ω k ∧ α * Real.sqrt n ≤ |(walkSum ω k : ℝ)|} +
        C * (1 - stepTail μ p) ^ ⌊(n : ℝ) / (4 * (μ 0).toReal)⌋₊ + C * Real.exp (-c * Real.sqrt n)

/-- The conclusion of `eq_i_upper` for the mark sequence `m`. -/
def EqIUpper (μ : PMF ℕ) (m : ℕ → ℕ) : Prop :=
  ∀ α : ℝ, 0 < α → ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ q : ℝ,
    (((𝐏w[μ.toMeasure])[|bridgeAtMark n]).real (prefixStepsIn (m n) {x | StepsGt q x})) ≤
      ((𝐏w[μ.toMeasure])[|bridgeAtMark n]).real
          {ω | ∃ k, IsMarkTime (m n) ω k ∧ α * Real.sqrt n ≤ |(walkSum ω k : ℝ)|} +
        C * (1 - (1 - stepTail μ q) ^ ⌊(n : ℝ) / (μ 0).toReal⌋₊) + C * Real.exp (-c * Real.sqrt n)

theorem bridgeStepsLt_subset_prefix' {n m : ℕ} (hmn : m ≤ n) (p : ℝ) :
    bridgeStepsIn n {x | StepsLt p x} ⊆ prefixStepsIn m {x | StepsLt p x} := by
  rintro ω ⟨k, hk, -, hS⟩
  obtain ⟨k', hk'k, hk'⟩ := Transfer.exists_isMarkTime_of_le hk hmn
  refine ⟨k', hk', ?_⟩
  have := stepsLt_take (j := k') hS
  rwa [Transfer.walkWord_take ω hk'k] at this

theorem bridgeStepsGt_subset_split' {n m : ℕ} (hmn : m ≤ n) (q : ℝ) :
    bridgeStepsIn n {x | StepsGt q x} ⊆
      prefixStepsIn m {x | StepsGt q x} ∪
        {ω | ∃ k, IsMarkTime n ω k ∧ walkSum ω k = -1 ∧ ∃ k', IsMarkTime m ω k' ∧
          StepsGt q ((walkWord ω k).drop k')} := by
  rintro ω ⟨k, hk, hs, hS⟩
  obtain ⟨k', hk'k, hk'⟩ := Transfer.exists_isMarkTime_of_le hk hmn
  rcases stepsGt_take_or_drop hS k' with h | h
  · left
    refine ⟨k', hk', ?_⟩
    rwa [Transfer.walkWord_take ω hk'k] at h
  · right
    exact ⟨k, hk, hs, k', hk', h⟩

theorem stepTail_mem_Icc (μ : PMF ℕ) (a : ℝ) : 0 ≤ 1 - stepTail μ a ∧ 1 - stepTail μ a ≤ 1 := by
  unfold stepTail
  have := isProbabilityMeasure_stepLaw μ
  constructor
  · linarith [measureReal_le_one (μ := stepLaw μ) (s := {z : ℤ | a ≤ (z : ℝ)})]
  · linarith [measureReal_nonneg (μ := stepLaw μ) (s := {z : ℤ | a ≤ (z : ℝ)})]

/-- `s^⌊x⌋ → 0` when `s^x → 0`, `0 ≤ s ≤ 1`, `x → ∞`. -/
theorem tendsto_pow_floor_zero {s x : ℕ → ℝ} (h0 : ∀ n, 0 ≤ s n) (h1 : ∀ n, s n ≤ 1)
    (hx : Tendsto x atTop atTop) (h : Tendsto (fun n => s n ^ x n) atTop (𝓝 0)) :
    Tendsto (fun n => s n ^ ⌊x n⌋₊) atTop (𝓝 0) := by
  have hsq : Tendsto (fun n => Real.sqrt (s n ^ x n)) atTop (𝓝 0) := by
    have := (Real.continuous_sqrt.tendsto 0).comp h
    rw [Real.sqrt_zero] at this
    exact this
  refine squeeze_zero' (Eventually.of_forall fun n => by have := h0 n; positivity) ?_ hsq
  filter_upwards [hx.eventually (eventually_ge_atTop 2)] with n hn
  have hxpos : 0 < x n := by linarith
  have hfl : x n / 2 ≤ (⌊x n⌋₊ : ℝ) := by
    have := Nat.lt_floor_add_one (x n); linarith
  have hfl2 : (⌊x n⌋₊ : ℝ) ≤ x n := Nat.floor_le hxpos.le
  have hq : 1 / 2 ≤ (⌊x n⌋₊ : ℝ) / x n := by
    rw [le_div_iff₀ hxpos]; linarith
  have ht0 : 0 ≤ s n ^ x n := Real.rpow_nonneg (h0 n) _
  have ht1 : s n ^ x n ≤ 1 := Real.rpow_le_one (h0 n) (h1 n) hxpos.le
  have e : s n ^ ⌊x n⌋₊ = (s n ^ x n) ^ ((⌊x n⌋₊ : ℝ) / x n) := by
    rw [← Real.rpow_mul (h0 n), mul_div_cancel₀ _ hxpos.ne', Real.rpow_natCast]
  rw [e, Real.sqrt_eq_rpow]
  exact Real.rpow_le_rpow_of_exponent_ge' ht0 ht1 (by norm_num) hq

/-- `s^⌊x⌋ → 1` when `s^x → 1`, `0 ≤ s ≤ 1`. -/
theorem tendsto_pow_floor_one {s x : ℕ → ℝ} (h0 : ∀ n, 0 ≤ s n) (h1 : ∀ n, s n ≤ 1)
    (hx : ∀ n, 0 ≤ x n) (h : Tendsto (fun n => s n ^ x n) atTop (𝓝 1)) :
    Tendsto (fun n => s n ^ ⌊x n⌋₊) atTop (𝓝 1) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le h tendsto_const_nhds (fun n => ?_) (fun n => ?_)
  · rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_ge' (h0 n) (h1 n) (by positivity) (Nat.floor_le (hx n))
  · exact pow_le_one₀ (h0 n) (h1 n)

theorem tendsto_exp_neg_sqrt {c : ℝ} (hc : 0 < c) :
    Tendsto (fun n : ℕ => Real.exp (-c * Real.sqrt n)) atTop (𝓝 0) := by
  refine Real.tendsto_exp_atBot.comp ?_
  have := (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop).const_mul_atTop_of_neg
    (show -c < 0 by linarith)
  exact this

/-- **Lower principle, chain.** -/
theorem lower_core {μ : PMF ℕ} (hμ0 : 0 < (μ 0).toReal)
    (hmid : MidTight μ (fun n => n / 2)) (hi : EqILower μ (fun n => n / 2)) {p : ℕ → ℝ}
    (hp : Tendsto (fun n : ℕ => (1 - stepTail μ (p n)) ^ ((n : ℝ) / (4 * (μ 0).toReal)))
      atTop (𝓝 0)) :
    Tendsto (fun n : ℕ =>
      (((bienaymeLaw μ.toMeasure)[|leafCountEvent n]).real
        (finiteTreeEvent fun t => (maxDegree t : ℝ) < p n + 1))) atTop (𝓝 0) := by
  rw [tendsto_order]
  refine ⟨fun a ha => Eventually.of_forall fun n => lt_of_lt_of_le ha measureReal_nonneg,
    fun b hb => ?_⟩
  obtain ⟨α, hα, hmidev⟩ := hmid (b / 3) (by linarith)
  obtain ⟨C, c, hC, hc, N₁, hN₁⟩ := hi α hα
  have hfl := tendsto_pow_floor_zero (s := fun n => 1 - stepTail μ (p n))
    (x := fun n : ℕ => (n : ℝ) / (4 * (μ 0).toReal)) (fun n => (stepTail_mem_Icc μ (p n)).1)
    (fun n => (stepTail_mem_Icc μ (p n)).2)
    (tendsto_natCast_atTop_atTop.atTop_div_const (by positivity)) hp
  have h2 : ∀ᶠ n : ℕ in atTop,
      C * (1 - stepTail μ (p n)) ^ ⌊(n : ℝ) / (4 * (μ 0).toReal)⌋₊ < b / 3 := by
    have := hfl.const_mul C
    rw [mul_zero] at this
    exact this.eventually (gt_mem_nhds (by linarith))
  have h3 : ∀ᶠ n : ℕ in atTop, C * Real.exp (-c * Real.sqrt n) < b / 3 := by
    have := (tendsto_exp_neg_sqrt hc).const_mul C
    rw [mul_zero] at this
    exact this.eventually (gt_mem_nhds (by linarith))
  filter_upwards [hmidev, h2, h3, eventually_ge_atTop (max N₁ 1)] with n h1 h2 h3 hn
  have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
  have hnN : N₁ ≤ n := le_trans (le_max_left _ _) hn
  have e1 : ((bienaymeLaw μ.toMeasure)[|leafCountEvent n]).real
      (finiteTreeEvent fun t => (maxDegree t : ℝ) < p n + 1) =
      ((𝐏w[μ.toMeasure])[|bridgeAtMark n]).real (bridgeStepsIn n {x | StepsLt (p n) x}) := by
    rw [Measure.real, Measure.real, eqDeltanon_lt _ hn1]
  have e2 : ((𝐏w[μ.toMeasure])[|bridgeAtMark n]).real (bridgeStepsIn n {x | StepsLt (p n) x}) ≤
      ((𝐏w[μ.toMeasure])[|bridgeAtMark n]).real (prefixStepsIn (n / 2) {x | StepsLt (p n) x}) :=
    measureReal_mono (bridgeStepsLt_subset_prefix' (by omega) _)
  have e3 := hN₁ n hnN (p n)
  simp only at e3
  rw [e1]
  linarith

/-- **Upper principle, chain.** -/
theorem upper_core {μ : PMF ℕ} (hμ0 : 0 < (μ 0).toReal)
    (hmid₁ : MidTight μ (fun n => n / 2)) (hmid₂ : MidTight μ (fun n => n - n / 2))
    (hi₁ : EqIUpper μ (fun n => n / 2)) (hi₂ : EqIUpper μ (fun n => n - n / 2)) {q : ℕ → ℝ}
    (hq : Tendsto (fun n : ℕ => (1 - stepTail μ (q n)) ^ ((n : ℝ) / (μ 0).toReal))
      atTop (𝓝 1)) :
    Tendsto (fun n : ℕ =>
      (((bienaymeLaw μ.toMeasure)[|leafCountEvent n]).real
        (finiteTreeEvent fun t => q n + 1 < (maxDegree t : ℝ)))) atTop (𝓝 0) := by
  rw [tendsto_order]
  refine ⟨fun a ha => Eventually.of_forall fun n => lt_of_lt_of_le ha measureReal_nonneg,
    fun b hb => ?_⟩
  obtain ⟨α₁, hα₁, hmidev₁⟩ := hmid₁ (b / 6) (by linarith)
  obtain ⟨α₂, hα₂, hmidev₂⟩ := hmid₂ (b / 6) (by linarith)
  obtain ⟨C₁, c₁, hC₁, hc₁, N₁, hN₁⟩ := hi₁ α₁ hα₁
  obtain ⟨C₂, c₂, hC₂, hc₂, N₂, hN₂⟩ := hi₂ α₂ hα₂
  have hfl := tendsto_pow_floor_one (s := fun n => 1 - stepTail μ (q n))
    (x := fun n : ℕ => (n : ℝ) / (μ 0).toReal) (fun n => (stepTail_mem_Icc μ (q n)).1)
    (fun n => (stepTail_mem_Icc μ (q n)).2) (fun n => by positivity) hq
  have hfl' : Tendsto (fun n : ℕ => 1 - (1 - stepTail μ (q n)) ^ ⌊(n : ℝ) / (μ 0).toReal⌋₊)
      atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub hfl
  have h2 : ∀ᶠ n : ℕ in atTop,
      C₁ * (1 - (1 - stepTail μ (q n)) ^ ⌊(n : ℝ) / (μ 0).toReal⌋₊) < b / 6 ∧
      C₂ * (1 - (1 - stepTail μ (q n)) ^ ⌊(n : ℝ) / (μ 0).toReal⌋₊) < b / 6 := by
    have a1 := hfl'.const_mul C₁
    have a2 := hfl'.const_mul C₂
    rw [mul_zero] at a1 a2
    exact (a1.eventually (gt_mem_nhds (by linarith))).and (a2.eventually (gt_mem_nhds (by linarith)))
  have h3 : ∀ᶠ n : ℕ in atTop, C₁ * Real.exp (-c₁ * Real.sqrt n) < b / 6 ∧
      C₂ * Real.exp (-c₂ * Real.sqrt n) < b / 6 := by
    have a1 := (tendsto_exp_neg_sqrt hc₁).const_mul C₁
    have a2 := (tendsto_exp_neg_sqrt hc₂).const_mul C₂
    rw [mul_zero] at a1 a2
    exact (a1.eventually (gt_mem_nhds (by linarith))).and (a2.eventually (gt_mem_nhds (by linarith)))
  filter_upwards [hmidev₁, hmidev₂, h2, h3, eventually_ge_atTop (max (max N₁ N₂) 2)]
    with n m1 m2 g2 g3 hn
  have hn2 : 2 ≤ n := le_trans (le_max_right _ _) hn
  have hnN₁ : N₁ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hnN₂ : N₂ ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  have e1 : ((bienaymeLaw μ.toMeasure)[|leafCountEvent n]).real
      (finiteTreeEvent fun t => q n + 1 < (maxDegree t : ℝ)) =
      ((𝐏w[μ.toMeasure])[|bridgeAtMark n]).real (bridgeStepsIn n {x | StepsGt (q n) x}) := by
    rw [Measure.real, Measure.real, eqDeltanon_gt _ (by omega)]
  have e2 := measureReal_mono (μ := (𝐏w[μ.toMeasure])[|bridgeAtMark n])
    (bridgeStepsGt_subset_split' (n := n) (m := n / 2) (by omega) (q n))
  have e3 := measureReal_union_le (μ := (𝐏w[μ.toMeasure])[|bridgeAtMark n])
    (prefixStepsIn (n / 2) {x | StepsGt (q n) x})
    {ω | ∃ k, IsMarkTime n ω k ∧ walkSum ω k = -1 ∧ ∃ k', IsMarkTime (n / 2) ω k' ∧
          StepsGt (q n) ((walkWord ω k).drop k')}
  have e4 : ((𝐏w[μ.toMeasure])[|bridgeAtMark n]).real
      {ω | ∃ k, IsMarkTime n ω k ∧ walkSum ω k = -1 ∧ ∃ k', IsMarkTime (n / 2) ω k' ∧
          StepsGt (q n) ((walkWord ω k).drop k')} =
      ((𝐏w[μ.toMeasure])[|bridgeAtMark n]).real (prefixStepsIn (n - n / 2) {x | StepsGt (q n) x}) := by
    rw [Measure.real, Measure.real,
      Bridge.bridge_reverse_half μ.toMeasure (m := n / 2) (by omega) (by omega) (q n)]
  have f1 := hN₁ n hnN₁ (q n)
  have f2 := hN₂ n hnN₂ (q n)
  simp only at f1 f2
  rw [e1]
  linarith [g2.1, g2.2, g3.1, g3.2]

theorem midTight_of_hypW {μ : PMF ℕ} (h : Concentration.HypW μ) (hnl : ¬ IsLatticeLaw (etaLaw μ)) {m : ℕ → ℕ}
    (hm : ∀ n, n / 2 ≤ m n ∧ m n ≤ (n + 1) / 2) : MidTight μ m :=
  fun ε hε => Concentration.bridge_midpoint_tightW h hnl hm ε hε

/-- The lower principle (frozen type: `hc hne hap hfin hnl`). -/
theorem maxDegree_lower_principle {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hap : Aperiodic μ) (hfin : Integrable (fun z : ℤ => (z : ℝ) ^ 2) (stepLaw μ))
    (hnl : ¬ IsLatticeLaw (etaLaw μ)) {p : ℕ → ℝ}
    (hp : Tendsto (fun n : ℕ => (1 - stepTail μ (p n)) ^ ((n : ℝ) / (4 * (μ 0).toReal)))
      atTop (𝓝 0)) :
    Tendsto (fun n : ℕ =>
      (((bienaymeLaw μ.toMeasure)[|leafCountEvent n]).real
        (finiteTreeEvent fun t => (maxDegree t : ℝ) < p n + 1))) atTop (𝓝 0) := by
  have h : Concentration.HypW μ := Concentration.HypW.of_integrable_sq hc hne hap hfin
  exact lower_core (ENNReal.toReal_pos (hc.apply_zero_ne_zero hne) (μ.apply_ne_top 0))
    (midTight_of_hypW h hnl (m := fun n => n / 2) (fun n => ⟨le_rfl, by omega⟩))
    (fun α hα => Bridge.eq_i_lowerW h hnl (m := fun n => n / 2) (fun n => ⟨le_rfl, by omega⟩) hα) hp

/-- The upper principle (frozen type: `hc hne hap hfin hnl`). -/
theorem maxDegree_upper_principle {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hap : Aperiodic μ) (hfin : Integrable (fun z : ℤ => (z : ℝ) ^ 2) (stepLaw μ))
    (hnl : ¬ IsLatticeLaw (etaLaw μ)) {q : ℕ → ℝ}
    (hq : Tendsto (fun n : ℕ => (1 - stepTail μ (q n)) ^ ((n : ℝ) / (μ 0).toReal))
      atTop (𝓝 1)) :
    Tendsto (fun n : ℕ =>
      (((bienaymeLaw μ.toMeasure)[|leafCountEvent n]).real
        (finiteTreeEvent fun t => q n + 1 < (maxDegree t : ℝ)))) atTop (𝓝 0) := by
  have h : Concentration.HypW μ := Concentration.HypW.of_integrable_sq hc hne hap hfin
  exact upper_core (ENNReal.toReal_pos (hc.apply_zero_ne_zero hne) (μ.apply_ne_top 0))
    (midTight_of_hypW h hnl (m := fun n => n / 2) (fun n => ⟨le_rfl, by omega⟩))
    (midTight_of_hypW h hnl (m := fun n => n - n / 2) (fun n => ⟨by omega, by omega⟩))
    (fun α hα => Bridge.eq_i_upperW h hnl (m := fun n => n / 2) (fun n => ⟨le_rfl, by omega⟩) hα)
    (fun α hα => Bridge.eq_i_upperW h hnl (m := fun n => n - n / 2) (fun n => ⟨by omega, by omega⟩) hα) hq

end BGWLeaves.MaxDegree.Principles
