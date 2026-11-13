module

public import BGWLeaves.MaxDegree.Defs

/-!
# Maximum degree: hypothesis `𝓗`, the tails and Lemma 7.2

Proofs for hypothesis `𝓗`, the tails and Lemma 7.2: `HypH.mu_zero_pos`, `HypH.mu_zero_lt_one`, `stepTail_eq_offTail`, `offTail_antitone`, `offTail_of_nonpos`, `offTail_one`, `tendsto_offTail`, `bigD_spec`, `eventually_bigD_spec`, `bigD_mono`, `tendsto_bigD_atTop_iff`, `bigD_eq_of_bounded`, `lem_MM`, `MM_lower_limit`, `MM_upper_limit`.  The theorems are those stated in
`BGWLeaves.MaxDegree`; they are exported in namespace `BGWLeaves.MaxDegree.Law` with exactly the types stated
there.
-/

@[expose] public section

namespace BGWLeaves.MaxDegree.Law

open MeasureTheory ProbabilityTheory Filter BGW
open BGW.StableTrees BGW.LocallyFinite BGWLeaves.StableAnalysis
open scoped ENNReal NNReal Topology

theorem mu_zero_ne_one {μ : PMF ℕ} (hc : IsCritical μ) : μ 0 ≠ 1 := by
  intro h
  have hs := (PMF.apply_eq_one_iff μ 0).1 h
  have hz : ∀ j : ℕ, (j : ℝ≥0∞) * μ j = 0 := by
    intro j
    by_cases hj : j = 0
    · simp [hj]
    · have : μ j = 0 := by
        by_contra hne
        have hmem : j ∈ μ.support := hne
        rw [hs] at hmem
        exact hj (by simpa using hmem)
      simp [this]
  have h0 : ∑' j : ℕ, (j : ℝ≥0∞) * μ j = 0 := by simp [hz]
  exact zero_ne_one (h0.symm.trans hc)

theorem HypH.mu_zero_pos {μ : PMF ℕ} (h : HypH μ) : 0 < (μ 0).toReal :=
  ENNReal.toReal_pos (h.critical.apply_zero_ne_zero h.nondegenerate) (μ.apply_ne_top 0)

theorem HypH.mu_zero_lt_one {μ : PMF ℕ} (h : HypH μ) : (μ 0).toReal < 1 := by
  have h1 : μ 0 ≠ 1 := mu_zero_ne_one h.critical
  have h2 : μ 0 ≤ 1 := PMF.coe_le_one μ 0
  have := lt_of_le_of_ne h2 h1
  simpa using (ENNReal.toReal_lt_toReal (μ.apply_ne_top 0) ENNReal.one_ne_top).2 this

theorem stepTail_eq_offTail (μ : PMF ℕ) (a : ℝ) : stepTail μ a = offTail μ (a + 1) := by
  unfold stepTail offTail stepLaw
  rw [Measure.real, Measure.map_apply (by fun_prop) (by simp)]
  congr 2
  ext k
  simp only [Set.mem_preimage, Set.mem_ofPred_eq]
  push_cast
  constructor <;> intro h <;> linarith

theorem offTail_antitone (μ : PMF ℕ) : Antitone (offTail μ) := by
  intro x y hxy
  unfold offTail
  refine ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono ?_)
  intro k hk
  exact le_trans hxy hk

theorem offTail_of_nonpos (μ : PMF ℕ) {x : ℝ} (hx : x ≤ 0) : offTail μ x = 1 := by
  unfold offTail
  have : {k : ℕ | x ≤ (k : ℝ)} = Set.univ := by
    ext k; simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
    exact le_trans hx (Nat.cast_nonneg k)
  rw [this]; simp

theorem offTail_one (μ : PMF ℕ) : offTail μ 1 = 1 - (μ 0).toReal := by
  unfold offTail
  have : {k : ℕ | (1 : ℝ) ≤ (k : ℝ)} = {0}ᶜ := by
    ext k; simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, Set.mem_singleton_iff]
    constructor
    · intro h h0; subst h0; norm_num at h
    · intro h; exact_mod_cast Nat.one_le_iff_ne_zero.2 h
  rw [this, prob_compl_eq_one_sub (measurableSet_singleton _), PMF.toMeasure_apply_singleton μ _ (measurableSet_singleton _)]
  rw [ENNReal.toReal_sub_of_le (PMF.coe_le_one μ 0) ENNReal.one_ne_top]; simp

theorem offTail_eq_zero_of_gt {μ : PMF ℕ} {K : ℕ} (hb : ∀ k : ℕ, K < k → μ k = 0) {x : ℝ}
    (hx : (K : ℝ) < x) : offTail μ x = 0 := by
  unfold offTail
  have hm : MeasurableSet {k : ℕ | x ≤ (k : ℝ)} := MeasurableSet.of_discrete
  have : μ.toMeasure {k : ℕ | x ≤ (k : ℝ)} = 0 := by
    rw [PMF.toMeasure_apply_eq_zero_iff _ hm]
    rw [Set.disjoint_left]
    intro k hk hk2
    have hk3 : x ≤ (k : ℝ) := hk2
    have : K < k := by exact_mod_cast lt_of_lt_of_le hx hk3
    exact hk (hb k this)
  rw [this]; simp

theorem offTail_pos_of_ne_zero {μ : PMF ℕ} {k : ℕ} (hk : μ k ≠ 0) : 0 < offTail μ k := by
  unfold offTail
  refine ENNReal.toReal_pos ?_ (measure_ne_top _ _)
  have hsub : ({k} : Set ℕ) ⊆ {j : ℕ | (k : ℝ) ≤ (j : ℝ)} := by
    intro j hj; rw [Set.mem_singleton_iff] at hj
    show (k : ℝ) ≤ (j : ℝ)
    rw [hj]
  intro h0
  have := measure_mono_null hsub h0
  rw [PMF.toMeasure_apply_singleton μ _ (measurableSet_singleton _)] at this
  exact hk this

theorem tendsto_offTail (μ : PMF ℕ) : Tendsto (fun k : ℕ => offTail μ k) atTop (𝓝 0) := by
  have hset : ∀ k : ℕ, {j : ℕ | (k : ℝ) ≤ (j : ℝ)} = Set.Ici k := by
    intro k; ext j; simp
  have hanti : Antitone (fun k : ℕ => (Set.Ici k : Set ℕ)) := fun a b hab => Set.Ici_subset_Ici.2 hab
  have h1 := tendsto_measure_iInter_atTop (μ := μ.toMeasure)
    (fun k => (MeasurableSet.of_discrete : MeasurableSet (Set.Ici k)).nullMeasurableSet) hanti
    ⟨0, measure_ne_top _ _⟩
  have hI : (⋂ k : ℕ, (Set.Ici k : Set ℕ)) = ∅ := by
    ext j; simp only [Set.mem_iInter, Set.mem_Ici, Set.mem_empty_iff_false, iff_false, not_forall, not_le]
    exact ⟨j + 1, Nat.lt_succ_self j⟩
  rw [hI, measure_empty] at h1
  have h2 := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h1
  simp only [offTail, hset]
  exact h2

theorem bigD_spec (μ : PMF ℕ) {n : ℕ} (hn : 1 ≤ n) (h : 1 / (n : ℝ) ≤ 1 - (μ 0).toReal) :
    IsGreatest {k : ℕ | 1 ≤ k ∧ 1 / (n : ℝ) ≤ offTail μ k} (bigD μ n) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hne : {k : ℕ | 1 ≤ k ∧ 1 / (n : ℝ) ≤ offTail μ k}.Nonempty := by
    refine ⟨1, le_rfl, ?_⟩
    have := offTail_one μ
    push_cast
    rw [this]; exact h
  have hbdd : BddAbove {k : ℕ | 1 ≤ k ∧ 1 / (n : ℝ) ≤ offTail μ k} := by
    have := (tendsto_offTail μ).eventually (gt_mem_nhds (show (0 : ℝ) < 1 / (n : ℝ) by positivity))
    obtain ⟨N, hN⟩ := eventually_atTop.1 this
    refine ⟨N, fun k hk => ?_⟩
    by_contra hlt
    push Not at hlt
    have := hN k hlt.le
    exact absurd hk.2 (not_le.2 this)
  exact ⟨Nat.sSup_mem hne hbdd, fun k hk => le_csSup hbdd hk⟩

theorem eventually_bigD_spec {μ : PMF ℕ} (h : μ 0 ≠ 1) :
    ∀ᶠ n : ℕ in atTop, IsGreatest {k : ℕ | 1 ≤ k ∧ 1 / (n : ℝ) ≤ offTail μ k} (bigD μ n) := by
  have hpos : 0 < 1 - (μ 0).toReal := by
    have h2 : μ 0 ≤ 1 := PMF.coe_le_one μ 0
    have := lt_of_le_of_ne h2 h
    have := (ENNReal.toReal_lt_toReal (μ.apply_ne_top 0) ENNReal.one_ne_top).2 this
    simpa using sub_pos.2 this
  have h1 : ∀ᶠ n : ℕ in atTop, 1 / (n : ℝ) < 1 - (μ 0).toReal :=
    (tendsto_one_div_atTop_nhds_zero_nat).eventually (gt_mem_nhds hpos)
  filter_upwards [h1, eventually_ge_atTop 1] with n hn1 hn2 using bigD_spec μ hn2 hn1.le

theorem bigD_mono {μ : PMF ℕ} (h : μ 0 ≠ 1) : ∀ᶠ n : ℕ in atTop, bigD μ n ≤ bigD μ (n + 1) := by
  filter_upwards [eventually_bigD_spec h, (eventually_atTop.2 ⟨1, fun n hn => hn⟩ : ∀ᶠ n : ℕ in atTop, 1 ≤ n),
    (tendsto_add_atTop_nat 1).eventually (eventually_bigD_spec h)] with n hn hn1 hn2
  refine hn2.2 ⟨hn.1.1, le_trans ?_ hn.1.2⟩
  have : (0 : ℝ) < n := by exact_mod_cast hn1
  push_cast
  exact one_div_le_one_div_of_le this (by linarith)

theorem tendsto_bigD_atTop_iff {μ : PMF ℕ} (h : μ 0 ≠ 1) :
    Tendsto (bigD μ) atTop atTop ↔ ∀ K : ℕ, ∃ k : ℕ, K < k ∧ μ k ≠ 0 := by
  constructor
  · intro ht K
    by_contra hcon
    push Not at hcon
    have h1 := (ht.eventually (eventually_gt_atTop K)).and ((eventually_bigD_spec h).and (eventually_ge_atTop 1))
    obtain ⟨n, hn1, hn2, hn3⟩ := h1.exists
    have hmem := hn2.1
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn3
    have := offTail_eq_zero_of_gt hcon (x := (bigD μ n : ℝ)) (by exact_mod_cast hn1)
    have h3 := hmem.2
    rw [this] at h3
    have : (0 : ℝ) < 1 / (n : ℝ) := by positivity
    linarith
  · intro hub
    rw [tendsto_atTop]
    intro K
    obtain ⟨k, hk1, hk2⟩ := hub K
    have hpos := offTail_pos_of_ne_zero hk2
    have h1 : ∀ᶠ n : ℕ in atTop, 1 / (n : ℝ) < offTail μ k :=
      (tendsto_one_div_atTop_nhds_zero_nat).eventually (gt_mem_nhds hpos)
    filter_upwards [h1, eventually_bigD_spec h] with n hn1 hn2
    exact le_trans hk1.le (hn2.2 ⟨by omega, hn1.le⟩)

theorem bigD_eq_of_bounded {μ : PMF ℕ} {K : ℕ} (hK1 : 1 ≤ K) (hK : μ K ≠ 0) (hb : ∀ k : ℕ, K < k → μ k = 0) :
    ∀ᶠ n : ℕ in atTop, bigD μ n = K := by
  have hpos := offTail_pos_of_ne_zero hK
  have h1 : ∀ᶠ n : ℕ in atTop, 1 / (n : ℝ) < offTail μ K :=
    (tendsto_one_div_atTop_nhds_zero_nat).eventually (gt_mem_nhds hpos)
  filter_upwards [h1, eventually_ge_atTop 1] with n hn1 hn2
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn2
  refine IsGreatest.csSup_eq ⟨⟨hK1, hn1.le⟩, fun k hk => ?_⟩
  by_contra hlt
  push Not at hlt
  have := offTail_eq_zero_of_gt hb (x := (k : ℝ)) (by exact_mod_cast hlt)
  have h3 := hk.2
  rw [this] at h3
  have : (0 : ℝ) < 1 / (n : ℝ) := by positivity
  linarith



theorem offTail_eq_ceil (μ : PMF ℕ) (x : ℝ) : offTail μ x = offTail μ (⌈x⌉₊ : ℝ) := by
  unfold offTail
  congr 2
  ext j
  simp only [Set.mem_ofPred_eq]
  rw [Nat.cast_le (α := ℝ)]
  exact Nat.ceil_le.symm

theorem mass_le_offTail (μ : PMF ℕ) (k : ℕ) : (μ k).toReal ≤ offTail μ k := by
  unfold offTail
  refine ENNReal.toReal_mono (measure_ne_top _ _) ?_
  have hsub : ({k} : Set ℕ) ⊆ {j : ℕ | (k : ℝ) ≤ (j : ℝ)} := by
    intro j hj; rw [Set.mem_singleton_iff] at hj
    show (k : ℝ) ≤ (j : ℝ)
    rw [hj]
  calc μ k = μ.toMeasure {k} := (PMF.toMeasure_apply_singleton μ _ (measurableSet_singleton _)).symm
    _ ≤ _ := measure_mono hsub

theorem offTail_le_one (μ : PMF ℕ) (x : ℝ) : offTail μ x ≤ 1 := by
  unfold offTail
  have := ENNReal.toReal_mono ENNReal.one_ne_top (prob_le_one (μ := μ.toMeasure) (s := {k : ℕ | x ≤ (k : ℝ)}))
  simpa using this

theorem offTail_nonneg (μ : PMF ℕ) (x : ℝ) : 0 ≤ offTail μ x := ENNReal.toReal_nonneg

theorem offTail_eq_tsum (μ : PMF ℕ) (x : ℝ) :
    offTail μ x = ∑' j : ℕ, ({k : ℕ | x ≤ (k : ℝ)}.indicator (fun j => (μ j).toReal)) j := by
  unfold offTail
  rw [PMF.toMeasure_apply _ MeasurableSet.of_discrete, ENNReal.tsum_toReal_eq]
  · congr 1; ext j
    by_cases hj : j ∈ {k : ℕ | x ≤ (k : ℝ)} <;> simp [Set.indicator, hj]
  · intro j
    by_cases hj : j ∈ {k : ℕ | x ≤ (k : ℝ)} <;> simp [Set.indicator, hj, μ.apply_ne_top]

theorem offTail_le_geom (μ : PMF ℕ) (k : ℕ) {A ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (h : ∀ j : ℕ, k ≤ j → (μ j).toReal ≤ A * ρ ^ (j - k)) : offTail μ k ≤ A / (1 - ρ) := by
  set g : ℕ → ℝ := fun j => {i : ℕ | k ≤ i}.indicator (fun j => A * ρ ^ (j - k)) j with hg
  have hA : 0 ≤ A := by
    have := h k le_rfl
    simp at this
    exact le_trans ENNReal.toReal_nonneg this
  have hgsum : Summable g := by
    rw [← summable_nat_add_iff k]
    have : (fun i => g (i + k)) = fun i => A * ρ ^ i := by
      funext i; simp [hg, Set.indicator]
    rw [this]
    exact (summable_geometric_of_lt_one hρ0 hρ1).mul_left A
  have hgtsum : ∑' j, g j = A / (1 - ρ) := by
    rw [← hgsum.sum_add_tsum_nat_add k]
    have h1 : ∑ i ∈ Finset.range k, g i = 0 := by
      apply Finset.sum_eq_zero; intro i hi
      simp [hg, Set.indicator]
      intro hki; exact absurd (Finset.mem_range.1 hi) (not_lt.2 hki)
    have : (fun i => g (i + k)) = fun i => A * ρ ^ i := by
      funext i; simp [hg, Set.indicator]
    rw [h1, this, tsum_mul_left, tsum_geometric_of_lt_one hρ0 hρ1]
    simp [div_eq_mul_inv]
  rw [offTail_eq_tsum, ← hgtsum]
  have hle : ∀ j, ({i : ℕ | (k : ℝ) ≤ (i : ℝ)}.indicator (fun j => (μ j).toReal)) j ≤ g j := by
    intro j
    by_cases hj : k ≤ j
    · have hj' : j ∈ {i : ℕ | (k : ℝ) ≤ (i : ℝ)} := by simpa using hj
      simp only [Set.indicator, hj', hg, Set.mem_ofPred_eq, ite_true]
      simpa [hj] using h j hj
    · have hj' : j ∉ {i : ℕ | (k : ℝ) ≤ (i : ℝ)} := by simpa using hj
      simp [Set.indicator, hg, hj]
  refine Summable.tsum_le_tsum hle ?_ hgsum
  refine Summable.of_nonneg_of_le (fun j => ?_) hle hgsum
  exact Set.indicator_nonneg (fun _ _ => ENNReal.toReal_nonneg) _

theorem rpow_inv_pow_self {x : ℝ} (hx : 0 ≤ x) {k : ℕ} (hk : k ≠ 0) : (x ^ (1 / (k : ℝ))) ^ k = x := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx, one_div_mul_cancel (by exact_mod_cast hk), Real.rpow_one]

theorem reg_E1 {μ : PMF ℕ} (h : HypH μ) :
    ∃ r : ℝ, 1 < r ∧ ∃ N0 : ℕ, 1 ≤ N0 ∧ ∀ k : ℕ, N0 ≤ k → (μ k).toReal ^ (1 / (k : ℝ)) ≤ 1 / r := by
  have h1 := h.radius_gt_one
  unfold genFunRadius at h1
  obtain ⟨r, hr⟩ := lt_iSup_iff.1 h1
  obtain ⟨hs, hr1⟩ := lt_iSup_iff.1 hr
  have hr1' : (1 : ℝ) < (r : ℝ) := by exact_mod_cast hr1
  have ht := hs.tendsto_atTop_zero
  obtain ⟨N1, hN1⟩ := eventually_atTop.1 (ht.eventually (gt_mem_nhds one_pos))
  refine ⟨(r : ℝ), hr1', max N1 1, le_max_right _ _, fun k hk => ?_⟩
  have hk1 : k ≠ 0 := by have := le_trans (le_max_right N1 1) hk; omega
  have hm := hN1 k (le_trans (le_max_left _ _) hk)
  have hm0 : 0 ≤ (μ k).toReal := ENNReal.toReal_nonneg
  have h2 : (μ k).toReal ≤ (1 / r) ^ k := by
    rw [div_pow, one_pow, le_div_iff₀ (by positivity)]
    exact hm.le
  have ha0 : 0 ≤ (μ k).toReal ^ (1 / (k : ℝ)) := Real.rpow_nonneg hm0 _
  refine (pow_le_pow_iff_left₀ ha0 (by positivity) hk1).1 ?_
  rw [rpow_inv_pow_self hm0 hk1]
  exact h2


theorem reg_E2 {μ : PMF ℕ} (h : HypH μ) {w : ℝ} (hw : 1 < w) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ k j : ℕ, N ≤ k → k ≤ j →
      (μ j).toReal ^ (1 / (j : ℝ)) ≤ w * (μ k).toReal ^ (1 / (k : ℝ)) := by
  rcases lt_or_eq_of_le (le_top : genFunRadius μ ≤ ⊤) with hlt | heq
  · have hlim := h.root_limit hlt
    have hR1 : (1 : ℝ) < (genFunRadius μ).toReal := by
      have := h.radius_gt_one
      have := (ENNReal.toReal_lt_toReal ENNReal.one_ne_top hlt.ne).2 this
      simpa using this
    set ρ : ℝ := ((genFunRadius μ).toReal)⁻¹ with hρ
    have hρpos : 0 < ρ := by positivity
    set s : ℝ := Real.sqrt w with hs
    have hs1 : 1 < s := by
      rw [hs, Real.lt_sqrt (by norm_num)]; simpa using hw
    have hss : s * s = w := Real.mul_self_sqrt (by linarith)
    have h1 : ∀ᶠ k : ℕ in atTop, ρ / s < (μ k).toReal ^ (1 / (k : ℝ)) :=
      hlim.eventually (lt_mem_nhds (by rw [div_lt_iff₀ (by linarith)]; nlinarith))
    have h2 : ∀ᶠ k : ℕ in atTop, (μ k).toReal ^ (1 / (k : ℝ)) < ρ * s :=
      hlim.eventually (gt_mem_nhds (by nlinarith))
    obtain ⟨N, hN⟩ := eventually_atTop.1 (h1.and (h2.and (eventually_ge_atTop 1)))
    refine ⟨max N 1, le_max_right _ _, fun k j hk hkj => ?_⟩
    have hkN : N ≤ k := le_trans (le_max_left _ _) hk
    have hjN : N ≤ j := le_trans hkN hkj
    have a1 := (hN k hkN).1
    have a2 := (hN j hjN).2.1
    calc (μ j).toReal ^ (1 / (j : ℝ)) ≤ ρ * s := a2.le
      _ = w * (ρ / s) := by rw [← hss]; field_simp
      _ ≤ w * (μ k).toReal ^ (1 / (k : ℝ)) := by
        apply mul_le_mul_of_nonneg_left a1.le (by linarith)
  · obtain ⟨N, hN⟩ := h.root_antitone heq
    refine ⟨max N 1, le_max_right _ _, fun k j hk hkj => ?_⟩
    have hkN : N ≤ k := le_trans (le_max_left _ _) hk
    have hjN : N ≤ j := le_trans hkN hkj
    have := hN hkN hjN hkj
    have h0 : 0 ≤ (μ k).toReal ^ (1 / (k : ℝ)) := Real.rpow_nonneg ENNReal.toReal_nonneg _
    calc (μ j).toReal ^ (1 / (j : ℝ)) ≤ (μ k).toReal ^ (1 / (k : ℝ)) := this
      _ ≤ w * (μ k).toReal ^ (1 / (k : ℝ)) := le_mul_of_one_le_left h0 hw.le

theorem reg_F1 {μ : PMF ℕ} {r : ℝ} (hr : 1 < r) {N0 : ℕ} (hN0 : 1 ≤ N0)
    (hE1 : ∀ k : ℕ, N0 ≤ k → (μ k).toReal ^ (1 / (k : ℝ)) ≤ 1 / r)
    (hE2 : ∀ w : ℝ, 1 < w → ∃ N : ℕ, 1 ≤ N ∧ ∀ k j : ℕ, N ≤ k → k ≤ j →
      (μ j).toReal ^ (1 / (j : ℝ)) ≤ w * (μ k).toReal ^ (1 / (k : ℝ)))
    {v : ℝ} (hv : 1 < v) :
    ∃ N : ℕ, N0 ≤ N ∧ 1 ≤ N ∧
      (∀ k j : ℕ, N ≤ k → k ≤ j →
        (μ j).toReal ^ (1 / (j : ℝ)) ≤ v * (μ k).toReal ^ (1 / (k : ℝ))) ∧
      ∀ j : ℕ, N ≤ j → offTail μ j ≤ v ^ j * (μ j).toReal := by
  set u : ℝ := Real.sqrt v with hu
  have hu1 : 1 < u := by
    rw [hu, Real.lt_sqrt (by norm_num)]; simpa using hv
  have huu : u * u = v := Real.mul_self_sqrt (by linarith)
  obtain ⟨N1, hN1, hE2u⟩ := hE2 u hu1
  obtain ⟨N3, hN3, hE2v⟩ := hE2 v hv
  have hr0 : (0 : ℝ) < r := by linarith
  have hρ0 : (0 : ℝ) ≤ 1 / r := by positivity
  have hρ1 : 1 / r < 1 := by rw [div_lt_one hr0]; exact hr
  set c0 : ℝ := 1 / (1 - 1 / r) with hc0
  obtain ⟨N2, hN2⟩ := eventually_atTop.1
    ((tendsto_pow_atTop_atTop_of_one_lt hu1).eventually_ge_atTop c0)
  refine ⟨max (max N0 N1) (max N2 N3), le_trans (le_max_left _ _) (le_trans (le_max_left _ _) le_rfl), ?_, ?_, ?_⟩
  · exact le_trans hN0 (le_trans (le_max_left _ _) (le_max_left _ _))
  · intro k j hk hkj
    exact hE2v k j (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hk) hkj
  · intro j hj
    have hjN0 : N0 ≤ j := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hj
    have hjN1 : N1 ≤ j := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hj
    have hjN2 : N2 ≤ j := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hj
    have hj1 : j ≠ 0 := by omega
    set m : ℕ → ℝ := fun i => (μ i).toReal with hm
    have hm0 : ∀ i, 0 ≤ m i := fun i => ENNReal.toReal_nonneg
    have hmj : 0 ≤ (μ j).toReal := ENNReal.toReal_nonneg
    have hgeom : offTail μ j ≤ (u ^ j * (μ j).toReal) / (1 - 1 / r) := by
      apply offTail_le_geom μ j hρ0 hρ1
      intro i hi
      have hiN0 : N0 ≤ i := le_trans hjN0 hi
      have hi1 : i ≠ 0 := by omega
      have ai := hE1 i hiN0
      have aij := hE2u j i hjN1 hi
      have ai0 : 0 ≤ (μ i).toReal ^ (1 / (i : ℝ)) := Real.rpow_nonneg ENNReal.toReal_nonneg _
      have aj0 : 0 ≤ (μ j).toReal ^ (1 / (j : ℝ)) := Real.rpow_nonneg ENNReal.toReal_nonneg _
      calc (μ i).toReal = ((μ i).toReal ^ (1 / (i : ℝ))) ^ i := (rpow_inv_pow_self ENNReal.toReal_nonneg hi1).symm
        _ = ((μ i).toReal ^ (1 / (i : ℝ))) ^ j * ((μ i).toReal ^ (1 / (i : ℝ))) ^ (i - j) := by
          rw [← pow_add]; congr 1; omega
        _ ≤ (u * (μ j).toReal ^ (1 / (j : ℝ))) ^ j * (1 / r) ^ (i - j) := by
          apply mul_le_mul (pow_le_pow_left₀ ai0 aij j) (pow_le_pow_left₀ ai0 ai _) (pow_nonneg ai0 _) (pow_nonneg (by positivity) _)
        _ = (u ^ j * (μ j).toReal) * (1 / r) ^ (i - j) := by
          rw [mul_pow, rpow_inv_pow_self ENNReal.toReal_nonneg hj1]
    calc offTail μ j ≤ (u ^ j * (μ j).toReal) / (1 - 1 / r) := hgeom
      _ = (u ^ j * (μ j).toReal) * c0 := by rw [hc0]; ring
      _ ≤ (u ^ j * (μ j).toReal) * u ^ j := by
        apply mul_le_mul_of_nonneg_left (hN2 j hjN2) (mul_nonneg (by positivity) hmj)
      _ = v ^ j * (μ j).toReal := by
        rw [← huu, mul_pow]; ring


theorem main_setup {μ : PMF ℕ} (h : HypH μ) {q : ℝ} (hq : 0 < q) :
    ∃ v : ℝ, 1 < v ∧ ∃ N : ℕ, 1 ≤ N ∧
      (∀ k j : ℕ, N ≤ k → k ≤ j →
        (μ j).toReal ^ (1 / (j : ℝ)) ≤ v * (μ k).toReal ^ (1 / (k : ℝ))) ∧
      (∀ j : ℕ, N ≤ j → offTail μ j ≤ v ^ j * (μ j).toReal) ∧
      (∀ n D : ℕ, N ≤ D → 1 ≤ n → 1 / (n : ℝ) ≤ offTail μ D → (v ^ D) ^ q ≤ (n : ℝ)) := by
  obtain ⟨r, hr, N0, hN0, hE1⟩ := reg_E1 h
  have hE2 : ∀ w : ℝ, 1 < w → ∃ N : ℕ, 1 ≤ N ∧ ∀ k j : ℕ, N ≤ k → k ≤ j →
      (μ j).toReal ^ (1 / (j : ℝ)) ≤ w * (μ k).toReal ^ (1 / (k : ℝ)) :=
    fun w hw => reg_E2 h hw
  have hr0 : 0 < r := by linarith
  set v : ℝ := r ^ (1 / (1 + q)) with hv
  have hv1 : 1 < v := Real.one_lt_rpow hr (by positivity)
  have hvr : v ^ (1 + q) = r := by
    rw [hv, ← Real.rpow_mul hr0.le, one_div_mul_cancel (by linarith), Real.rpow_one]
  obtain ⟨N, hNN0, hN1, hA, hB⟩ := reg_F1 hr hN0 hE1 hE2 hv1
  refine ⟨v, hv1, N, hN1, hA, hB, ?_⟩
  intro n D hD hn hnD
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hv0 : 0 < v := by linarith
  set W : ℝ := v ^ D with hW
  have hWpos : 0 < W := by positivity
  have h1 : 1 / (n : ℝ) ≤ W * (1 / r) ^ D := by
    calc 1 / (n : ℝ) ≤ offTail μ D := hnD
      _ ≤ v ^ D * (μ D).toReal := hB D hD
      _ ≤ v ^ D * ((μ D).toReal ^ (1 / (D : ℝ))) ^ D := by
        rw [rpow_inv_pow_self ENNReal.toReal_nonneg (by omega)]
      _ ≤ v ^ D * (1 / r) ^ D := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact pow_le_pow_left₀ (Real.rpow_nonneg ENNReal.toReal_nonneg _) (hE1 D (le_trans hNN0 hD)) D
  have hrD : r ^ D = W * W ^ q := by
    have e1 : r ^ D = W ^ (1 + q) := by
      calc r ^ D = (v ^ (1 + q)) ^ (D : ℝ) := by rw [hvr, Real.rpow_natCast]
        _ = v ^ ((1 + q) * (D : ℝ)) := by rw [← Real.rpow_mul hv0.le]
        _ = v ^ ((D : ℝ) * (1 + q)) := by rw [mul_comm]
        _ = (v ^ (D : ℝ)) ^ (1 + q) := by rw [Real.rpow_mul hv0.le]
        _ = W ^ (1 + q) := by rw [hW, Real.rpow_natCast]
    rw [e1, Real.rpow_add hWpos, Real.rpow_one]
  have hWq : 0 < W ^ q := Real.rpow_pos_of_pos hWpos q
  have h2 : 1 / (n : ℝ) ≤ 1 / W ^ q := by
    calc 1 / (n : ℝ) ≤ W * (1 / r) ^ D := h1
      _ = 1 / W ^ q := by
        rw [div_pow, one_pow, hrD]; field_simp
  exact (one_div_le_one_div hnpos hWq).1 h2


theorem main_upper {μ : PMF ℕ} (h : HypH μ) (hub : ∀ K : ℕ, ∃ k : ℕ, K < k ∧ μ k ≠ 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, offTail μ ((1 + ε) * (bigD μ n : ℝ)) ≤ (n : ℝ) ^ (-1 - ε / 3) := by
  have h0 : μ 0 ≠ 1 := mu_zero_ne_one h.critical
  set q : ℝ := 6 * (2 + ε) / ε with hq
  have hqpos : 0 < q := by positivity
  obtain ⟨v, hv1, N, hN1, hA, hB, hkey⟩ := main_setup h hqpos
  have hv0 : 0 < v := by linarith
  set D0 : ℕ := max N ⌈(3 + 2 * ε) / ε⌉₊ with hD0
  have hD : ∀ᶠ n : ℕ in atTop, D0 ≤ bigD μ n :=
    ((tendsto_bigD_atTop_iff h0).2 hub).eventually_ge_atTop D0
  filter_upwards [hD, eventually_bigD_spec h0, eventually_ge_atTop 1] with n hDn hS hn
  set D : ℕ := bigD μ n with hDdef
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hDN : N ≤ D := le_trans (le_max_left _ _) hDn
  have hDε : (3 + 2 * ε) / ε ≤ (D : ℝ) :=
    le_trans (Nat.le_ceil _) (by exact_mod_cast le_trans (le_max_right _ _) hDn)
  have hD1 : (1 : ℝ) ≤ D := by exact_mod_cast le_trans hN1 hDN
  have hεD : 3 + 2 * ε ≤ ε * D := by
    rw [div_le_iff₀ hε] at hDε; linarith
  have hDmem := hS.1
  have ht1 : offTail μ ((D + 1 : ℕ) : ℝ) < 1 / n := by
    by_contra hcon
    push Not at hcon
    have := hS.2 ⟨by omega, hcon⟩
    omega
  rw [offTail_eq_ceil]
  set k : ℕ := ⌈(1 + ε) * (D : ℝ)⌉₊ with hk
  have hk1 : (1 + ε) * (D : ℝ) ≤ k := Nat.le_ceil _
  have hk2 : (k : ℝ) < (1 + ε) * D + 1 := Nat.ceil_lt_add_one (by positivity)
  have hkD : D + 1 ≤ k := by
    have : ((D + 1 : ℕ) : ℝ) ≤ k := by push_cast; nlinarith
    exact_mod_cast this
  have hkN : N ≤ k := by omega
  set a : ℕ → ℝ := fun i => (μ i).toReal ^ (1 / (i : ℝ)) with ha
  have ha0 : ∀ i, 0 ≤ a i := fun i => Real.rpow_nonneg ENNReal.toReal_nonneg _
  have hapow : ∀ i : ℕ, i ≠ 0 → a i ^ i = (μ i).toReal := fun i hi => rpow_inv_pow_self ENNReal.toReal_nonneg hi
  have hakD : a k ≤ v * a (D + 1) := hA (D + 1) k (by omega) hkD
  have hD1pow : a (D + 1) ^ (D + 1) < 1 / n := by
    rw [hapow (D + 1) (by omega)]
    exact lt_of_le_of_lt (mass_le_offTail μ (D + 1)) ht1
  -- exponent
  have hκ : 1 + 2 * ε / 3 ≤ (k : ℝ) / ((D + 1 : ℕ) : ℝ) := by
    rw [le_div_iff₀ (by positivity)]
    push_cast
    nlinarith
  have h_ak : a (D + 1) ^ k ≤ (n : ℝ) ^ (-(1 + 2 * ε / 3)) := by
    have e1 : a (D + 1) ^ k = (a (D + 1) ^ (D + 1)) ^ ((k : ℝ) / ((D + 1 : ℕ) : ℝ)) := by
      rw [← Real.rpow_natCast (a (D + 1)) (D + 1),
        ← Real.rpow_mul (ha0 _), ← Real.rpow_natCast (a (D + 1)) k]
      congr 1
      field_simp
    rw [e1]
    have hnr : (1 / (n : ℝ)) ^ ((k : ℝ) / ((D + 1 : ℕ) : ℝ)) ≤ (1 / (n : ℝ)) ^ (1 + 2 * ε / 3) :=
      Real.rpow_le_rpow_of_exponent_ge (by positivity) (by rw [div_le_one hnpos]; exact hn1) hκ
    calc (a (D + 1) ^ (D + 1)) ^ ((k : ℝ) / ((D + 1 : ℕ) : ℝ))
        ≤ (1 / (n : ℝ)) ^ ((k : ℝ) / ((D + 1 : ℕ) : ℝ)) :=
          Real.rpow_le_rpow (pow_nonneg (ha0 _) _) hD1pow.le (by positivity)
      _ ≤ (1 / (n : ℝ)) ^ (1 + 2 * ε / 3) := hnr
      _ = (n : ℝ) ^ (-(1 + 2 * ε / 3)) := by
        rw [one_div, Real.inv_rpow hnpos.le, Real.rpow_neg hnpos.le]
  -- the factor v^k
  have hW : v ^ D ≤ (n : ℝ) ^ (1 / q) := by
    have := hkey n D hDN hn hDmem.2
    calc v ^ D = ((v ^ D) ^ q) ^ (1 / q) := by
          rw [one_div, Real.rpow_rpow_inv (by positivity) hqpos.ne']
      _ ≤ (n : ℝ) ^ (1 / q) := Real.rpow_le_rpow (by positivity) this (by positivity)
  have hvk : v ^ k ≤ (n : ℝ) ^ (ε / 6) := by
    have hkle : (k : ℝ) ≤ (2 + ε) * D := by nlinarith
    calc v ^ k = v ^ (k : ℝ) := (Real.rpow_natCast v k).symm
      _ ≤ v ^ ((2 + ε) * (D : ℝ)) := Real.rpow_le_rpow_of_exponent_le hv1.le hkle
      _ = (v ^ D) ^ (2 + ε) := by
        rw [mul_comm, Real.rpow_mul hv0.le, Real.rpow_natCast]
      _ ≤ ((n : ℝ) ^ (1 / q)) ^ (2 + ε) := Real.rpow_le_rpow (by positivity) hW (by positivity)
      _ = (n : ℝ) ^ (ε / 6) := by
        rw [← Real.rpow_mul hnpos.le]
        congr 1
        rw [hq]; field_simp
  -- assemble
  calc offTail μ (k : ℝ) ≤ v ^ k * (μ k).toReal := hB k hkN
    _ = v ^ k * a k ^ k := by rw [hapow k (by omega)]
    _ ≤ v ^ k * (v * a (D + 1)) ^ k := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact pow_le_pow_left₀ (ha0 _) hakD k
    _ = (v ^ k) ^ 2 * a (D + 1) ^ k := by rw [mul_pow]; ring
    _ ≤ ((n : ℝ) ^ (ε / 6)) ^ 2 * (n : ℝ) ^ (-(1 + 2 * ε / 3)) := by
        apply mul_le_mul (pow_le_pow_left₀ (by positivity) hvk 2) h_ak (pow_nonneg (ha0 _) _) (by positivity)
    _ = (n : ℝ) ^ (-1 - ε / 3) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hnpos.le, ← Real.rpow_add hnpos]
        congr 1
        push_cast; ring


theorem main_lower {μ : PMF ℕ} (h : HypH μ) (hub : ∀ K : ℕ, ∃ k : ℕ, K < k ∧ μ k ≠ 0)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    ∀ᶠ n : ℕ in atTop,
      (n : ℝ) ^ (-(1 / (1 + ε / 3))) ≤ offTail μ ((1 - ε) * (bigD μ n : ℝ)) := by
  have h0 : μ 0 ≠ 1 := mu_zero_ne_one h.critical
  set ω : ℝ := 1 / (1 + ε / 3) with hω
  set γ : ℝ := ω - (1 - ε) with hγ
  have hγpos : 0 < γ := by
    rw [hγ, hω, sub_pos, lt_div_iff₀ (by positivity)]; nlinarith
  set q : ℝ := 8 / γ with hq
  have hqpos : 0 < q := by positivity
  obtain ⟨v, hv1, N, hN1, hA, hB, hkey⟩ := main_setup h hqpos
  have hv0 : 0 < v := by linarith
  have hε1' : 0 < 1 - ε := by linarith
  set D0 : ℕ := max (max N ⌈(N : ℝ) / (1 - ε)⌉₊) ⌈2 / γ⌉₊ with hD0
  have hD : ∀ᶠ n : ℕ in atTop, D0 ≤ bigD μ n :=
    ((tendsto_bigD_atTop_iff h0).2 hub).eventually_ge_atTop D0
  filter_upwards [hD, eventually_bigD_spec h0, eventually_ge_atTop 1] with n hDn hS hn
  set D : ℕ := bigD μ n with hDdef
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hDN : N ≤ D := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hDn
  have hDN' : (N : ℝ) / (1 - ε) ≤ (D : ℝ) :=
    le_trans (Nat.le_ceil _) (by exact_mod_cast le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hDn)
  have hDγ : 2 / γ ≤ (D : ℝ) :=
    le_trans (Nat.le_ceil _) (by exact_mod_cast le_trans (le_max_right _ _) hDn)
  have hD1 : (1 : ℝ) ≤ D := by exact_mod_cast le_trans hN1 hDN
  have hDpos : (0 : ℝ) < D := by linarith
  have hDmem := hS.1
  rw [offTail_eq_ceil]
  set k : ℕ := ⌈(1 - ε) * (D : ℝ)⌉₊ with hk
  have hk1 : (1 - ε) * (D : ℝ) ≤ k := Nat.le_ceil _
  have hk2 : (k : ℝ) < (1 - ε) * D + 1 := Nat.ceil_lt_add_one (by positivity)
  have hkD : k ≤ D := by
    rw [hk, Nat.ceil_le]
    nlinarith
  have hNk : N ≤ k := by
    have : (N : ℝ) ≤ k := by
      rw [div_le_iff₀ hε1'] at hDN'
      nlinarith
    exact_mod_cast this
  have hk0 : k ≠ 0 := by omega
  set a : ℕ → ℝ := fun i => (μ i).toReal ^ (1 / (i : ℝ)) with ha
  have ha0 : ∀ i, 0 ≤ a i := fun i => Real.rpow_nonneg ENNReal.toReal_nonneg _
  have hapow : ∀ i : ℕ, i ≠ 0 → a i ^ i = (μ i).toReal := fun i hi => rpow_inv_pow_self ENNReal.toReal_nonneg hi
  have haD : a D ≤ v * a k := hA k D hNk hkD
  have hW : v ^ D ≤ (n : ℝ) ^ (1 / q) := by
    have := hkey n D hDN hn hDmem.2
    calc v ^ D = ((v ^ D) ^ q) ^ (1 / q) := by
          rw [one_div, Real.rpow_rpow_inv (by positivity) hqpos.ne']
      _ ≤ (n : ℝ) ^ (1 / q) := Real.rpow_le_rpow (by positivity) this (by positivity)
  have hW2 : (v ^ D) ^ 2 ≤ (n : ℝ) ^ (2 / q) := by
    calc (v ^ D) ^ 2 ≤ ((n : ℝ) ^ (1 / q)) ^ 2 := pow_le_pow_left₀ (by positivity) hW 2
      _ = (n : ℝ) ^ (2 / q) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hnpos.le]; congr 1; push_cast; ring
  -- a_k^D lower bound
  have hmD : 1 / (n : ℝ) ≤ v ^ D * (v ^ D * a k ^ D) := by
    calc 1 / (n : ℝ) ≤ offTail μ D := hDmem.2
      _ ≤ v ^ D * (μ D).toReal := hB D hDN
      _ = v ^ D * a D ^ D := by rw [hapow D (by omega)]
      _ ≤ v ^ D * (v * a k) ^ D := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact pow_le_pow_left₀ (ha0 _) haD D
      _ = v ^ D * (v ^ D * a k ^ D) := by rw [mul_pow]
  have hakD : (n : ℝ) ^ (-(1 + 2 / q)) ≤ a k ^ D := by
    have e1 : (n : ℝ) ^ (-(1 + 2 / q)) = (1 / (n : ℝ)) / (n : ℝ) ^ (2 / q) := by
      rw [Real.rpow_neg hnpos.le, Real.rpow_add hnpos, Real.rpow_one, mul_inv]
      field_simp
    rw [e1]
    have hWpos : 0 < (v ^ D) ^ 2 := by positivity
    have hnq : 0 < (n : ℝ) ^ (2 / q) := Real.rpow_pos_of_pos hnpos _
    calc (1 / (n : ℝ)) / (n : ℝ) ^ (2 / q) ≤ (1 / (n : ℝ)) / (v ^ D) ^ 2 :=
          div_le_div_of_nonneg_left (by positivity) hWpos hW2
      _ ≤ a k ^ D := by
          rw [div_le_iff₀ hWpos]
          calc 1 / (n : ℝ) ≤ v ^ D * (v ^ D * a k ^ D) := hmD
            _ = a k ^ D * (v ^ D) ^ 2 := by ring
  -- exponent
  have hκ0 : 0 ≤ (k : ℝ) / D := by positivity
  have hκ1 : (k : ℝ) / D ≤ 1 := by rw [div_le_one hDpos]; exact_mod_cast hkD
  have hκ2 : (k : ℝ) / D ≤ (1 - ε) + γ / 2 := by
    rw [div_le_iff₀ hDpos]
    have : 1 ≤ γ / 2 * D := by
      have := hDγ; rw [div_le_iff₀ hγpos] at this; nlinarith
    nlinarith
  have hexp : (1 + 2 / q) * ((k : ℝ) / D) ≤ ω := by
    have h2q : 2 / q = γ / 4 := by rw [hq]; field_simp; ring
    rw [h2q]
    have : (1 + γ / 4) * ((k : ℝ) / D) ≤ (k : ℝ) / D + γ / 4 := by nlinarith
    have hωγ : ω = (1 - ε) + γ := by rw [hγ]; ring
    nlinarith
  calc (n : ℝ) ^ (-(1 / (1 + ε / 3))) = (n : ℝ) ^ (-ω) := by rw [hω]
    _ ≤ (n : ℝ) ^ (-((1 + 2 / q) * ((k : ℝ) / D))) :=
        Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
    _ = ((n : ℝ) ^ (-(1 + 2 / q))) ^ ((k : ℝ) / D) := by
        rw [← Real.rpow_mul hnpos.le]; congr 1; ring
    _ ≤ (a k ^ D) ^ ((k : ℝ) / D) := Real.rpow_le_rpow (by positivity) hakD hκ0
    _ = a k ^ k := by
        rw [← Real.rpow_natCast (a k) D, ← Real.rpow_mul (ha0 _), ← Real.rpow_natCast (a k) k]
        congr 1
        field_simp
    _ = (μ k).toReal := hapow k hk0
    _ ≤ offTail μ (k : ℝ) := mass_le_offTail μ k


theorem main_bounded {μ : PMF ℕ} (h : HypH μ) (hub : ¬ ∀ K : ℕ, ∃ k : ℕ, K < k ∧ μ k ≠ 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      (n : ℝ) ^ (-(1 / (1 + ε / 3))) ≤ offTail μ ((1 - ε) * (bigD μ n : ℝ)) ∧
        offTail μ ((1 + ε) * (bigD μ n : ℝ)) ≤ (n : ℝ) ^ (-1 - ε / 3) := by
  have h0 : μ 0 ≠ 1 := mu_zero_ne_one h.critical
  push Not at hub
  obtain ⟨K, hK⟩ := hub
  have hne : {k : ℕ | μ k ≠ 0}.Nonempty := by
    obtain ⟨k, hk⟩ := μ.support_nonempty
    exact ⟨k, hk⟩
  have hbdd : BddAbove {k : ℕ | μ k ≠ 0} := ⟨K, fun k hk => by
    by_contra hlt; push Not at hlt; exact hk (hK k hlt)⟩
  set K' : ℕ := sSup {k : ℕ | μ k ≠ 0} with hK'
  have hK'mem : μ K' ≠ 0 := Nat.sSup_mem hne hbdd
  have hK'gt : ∀ k : ℕ, K' < k → μ k = 0 := by
    intro k hk
    by_contra hne'
    exact absurd (le_csSup hbdd hne') (not_le.2 hk)
  have hK'1 : 1 ≤ K' := by
    by_contra hlt
    have hK'0 : K' = 0 := by omega
    apply h0
    rw [PMF.apply_eq_one_iff]
    ext k
    simp only [PMF.mem_support_iff, Set.mem_singleton_iff]
    constructor
    · intro hk
      by_contra hk0
      exact hk (hK'gt k (by omega))
    · intro hk; rw [hk, ← hK'0]; exact hK'mem
  have hD := bigD_eq_of_bounded hK'1 hK'mem hK'gt
  have hmpos : 0 < (μ K').toReal := ENNReal.toReal_pos hK'mem (μ.apply_ne_top _)
  have hc : (0 : ℝ) < 1 / (1 + ε / 3) := by positivity
  have hlim : Tendsto (fun n : ℕ => (n : ℝ) ^ (-(1 / (1 + ε / 3)))) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop hc).comp tendsto_natCast_atTop_atTop
  have hsmall := hlim.eventually (gt_mem_nhds hmpos)
  filter_upwards [hD, hsmall, eventually_ge_atTop 1] with n hDn hsm hn
  rw [hDn]
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  refine ⟨?_, ?_⟩
  · calc (n : ℝ) ^ (-(1 / (1 + ε / 3))) ≤ (μ K').toReal := hsm.le
      _ ≤ offTail μ (K' : ℝ) := mass_le_offTail μ K'
      _ ≤ offTail μ ((1 - ε) * (K' : ℝ)) := by
        apply offTail_antitone
        have : (0 : ℝ) ≤ K' := Nat.cast_nonneg K'
        nlinarith
  · rw [offTail_eq_zero_of_gt hK'gt]
    · exact Real.rpow_nonneg hnpos.le _
    · have : (1 : ℝ) ≤ K' := by exact_mod_cast hK'1
      nlinarith

theorem lem_MM {μ : PMF ℕ} (h : HypH μ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      (n : ℝ) ^ (-(1 / (1 + ε / 3))) ≤ offTail μ ((1 - ε) * (bigD μ n : ℝ)) ∧
        offTail μ ((1 + ε) * (bigD μ n : ℝ)) ≤ (n : ℝ) ^ (-1 - ε / 3) := by
  by_cases hub : ∀ K : ℕ, ∃ k : ℕ, K < k ∧ μ k ≠ 0
  · have hlow : ∀ᶠ n : ℕ in atTop,
        (n : ℝ) ^ (-(1 / (1 + ε / 3))) ≤ offTail μ ((1 - ε) * (bigD μ n : ℝ)) := by
      by_cases hε1 : ε < 1
      · exact main_lower h hub hε hε1
      · filter_upwards [eventually_ge_atTop 1] with n hn
        have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
        rw [offTail_of_nonpos μ (by
          have : (0 : ℝ) ≤ (bigD μ n : ℝ) := Nat.cast_nonneg _
          nlinarith [not_lt.1 hε1])]
        exact Real.rpow_le_one_of_one_le_of_nonpos hn1 (by
          have : (0 : ℝ) < 1 / (1 + ε / 3) := by positivity
          linarith)
    filter_upwards [hlow, main_upper h hub hε] with n h1 h2 using ⟨h1, h2⟩
  · exact main_bounded h hub hε


theorem MM_upper_limit {μ : PMF ℕ} (h : HypH μ) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ =>
      (1 - stepTail μ ((1 + ε) * (bigD μ n : ℝ) - 1)) ^ ((n : ℝ) / (μ 0).toReal)) atTop (𝓝 1) := by
  have hm0 := HypH.mu_zero_pos h
  have hm1 := HypH.mu_zero_lt_one h
  have hlim : Tendsto (fun n : ℕ => (n : ℝ) ^ (-(ε / 3)) / (μ 0).toReal) atTop (𝓝 0) := by
    have := ((tendsto_rpow_neg_atTop (show 0 < ε / 3 by positivity)).comp
      tendsto_natCast_atTop_atTop).div_const (μ 0).toReal
    simpa using this
  have hlow : Tendsto (fun n : ℕ => 1 - (n : ℝ) ^ (-(ε / 3)) / (μ 0).toReal) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub hlim
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
  · filter_upwards [lem_MM h hε, eventually_ge_atTop 1] with n hMM hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hs := hMM.2
    set s : ℝ := offTail μ ((1 + ε) * (bigD μ n : ℝ)) with hsdef
    have hst : stepTail μ ((1 + ε) * (bigD μ n : ℝ) - 1) = s := by
      rw [stepTail_eq_offTail, sub_add_cancel]
    rw [hst]
    have hs0 : 0 ≤ s := offTail_nonneg _ _
    have hs1 : s ≤ 1 := offTail_le_one _ _
    have hx1 : (1 : ℝ) ≤ (n : ℝ) / (μ 0).toReal := by
      rw [le_div_iff₀ hm0]; nlinarith
    have hbern := one_add_mul_self_le_rpow_one_add (s := -s) (by linarith) hx1
    have hxs : (n : ℝ) / (μ 0).toReal * s ≤ (n : ℝ) ^ (-(ε / 3)) / (μ 0).toReal := by
      calc (n : ℝ) / (μ 0).toReal * s ≤ (n : ℝ) / (μ 0).toReal * (n : ℝ) ^ (-1 - ε / 3) :=
            mul_le_mul_of_nonneg_left hs (by positivity)
        _ = (n : ℝ) ^ (-(ε / 3)) / (μ 0).toReal := by
          have : (n : ℝ) ^ (-(ε / 3)) = (n : ℝ) * (n : ℝ) ^ (-1 - ε / 3) := by
            conv_lhs => rw [show -(ε / 3) = 1 + (-1 - ε / 3) by ring]
            rw [Real.rpow_add hnpos, Real.rpow_one]
          rw [this]; ring
    have : 1 + (n : ℝ) / (μ 0).toReal * -s = 1 - (n : ℝ) / (μ 0).toReal * s := by ring
    rw [this] at hbern
    rw [show 1 + -s = 1 - s by ring] at hbern
    linarith
  · filter_upwards [lem_MM h hε, eventually_ge_atTop 1] with n hMM hn
    have hst : stepTail μ ((1 + ε) * (bigD μ n : ℝ) - 1) = offTail μ ((1 + ε) * (bigD μ n : ℝ)) := by
      rw [stepTail_eq_offTail, sub_add_cancel]
    rw [hst]
    exact Real.rpow_le_one (by linarith [offTail_le_one μ ((1 + ε) * (bigD μ n : ℝ))])
      (by linarith [offTail_nonneg μ ((1 + ε) * (bigD μ n : ℝ))]) (by positivity)

theorem MM_lower_limit {μ : PMF ℕ} (h : HypH μ) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ =>
      (1 - stepTail μ ((1 - ε) * (bigD μ n : ℝ) - 1)) ^ ((n : ℝ) / (4 * (μ 0).toReal))) atTop (𝓝 0) := by
  have hm0 := HypH.mu_zero_pos h
  set c : ℝ := 1 / (1 + ε / 3) with hc
  have hc0 : 0 < c := by positivity
  have hc1 : c < 1 := by rw [hc, div_lt_one (by positivity)]; linarith
  have hg : Tendsto (fun n : ℕ => Real.exp (-((n : ℝ) ^ (1 - c) / (4 * (μ 0).toReal)))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => (n : ℝ) ^ (1 - c)) atTop atTop :=
      (tendsto_rpow_atTop (by linarith)).comp tendsto_natCast_atTop_atTop
    have h2 := h1.atTop_div_const (show 0 < 4 * (μ 0).toReal by positivity)
    exact Real.tendsto_exp_neg_atTop_nhds_zero.comp h2
  refine squeeze_zero' ?_ ?_ hg
  · filter_upwards [lem_MM h hε] with n hMM
    rw [stepTail_eq_offTail, sub_add_cancel]
    exact Real.rpow_nonneg (by linarith [offTail_le_one μ ((1 - ε) * (bigD μ n : ℝ))]) _
  · filter_upwards [lem_MM h hε, eventually_ge_atTop 1] with n hMM hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    rw [stepTail_eq_offTail, sub_add_cancel]
    have hL := hMM.1
    set s : ℝ := offTail μ ((1 - ε) * (bigD μ n : ℝ)) with hsdef
    set L : ℝ := (n : ℝ) ^ (-c) with hL'
    have hs1 : s ≤ 1 := offTail_le_one _ _
    have hL0 : 0 ≤ L := Real.rpow_nonneg hnpos.le _
    have hL1 : L ≤ 1 := by
      rw [hL']; exact Real.rpow_le_one_of_one_le_of_nonpos hn1 (by linarith)
    have hx0 : 0 ≤ (n : ℝ) / (4 * (μ 0).toReal) := by positivity
    calc (1 - s) ^ ((n : ℝ) / (4 * (μ 0).toReal))
        ≤ (1 - L) ^ ((n : ℝ) / (4 * (μ 0).toReal)) :=
          Real.rpow_le_rpow (by linarith) (by linarith) hx0
      _ ≤ (Real.exp (-L)) ^ ((n : ℝ) / (4 * (μ 0).toReal)) :=
          Real.rpow_le_rpow (by linarith) (by linarith [Real.add_one_le_exp (-L)]) hx0
      _ = Real.exp (-((n : ℝ) ^ (1 - c) / (4 * (μ 0).toReal))) := by
          rw [← Real.exp_mul]
          congr 1
          have : (n : ℝ) ^ (1 - c) = (n : ℝ) * L := by
            rw [hL', show 1 - c = 1 + -c by ring, Real.rpow_add hnpos, Real.rpow_one]
          rw [this]; field_simp


end BGWLeaves.MaxDegree.Law
