module

public import BGWLeaves.LeafConcentration.Defs
public import BGWLeaves.LeafConcentration.OeLemmas
public import BGWLeaves.LeafConcentration.Chernoff
import BGWLeaves.Passage
import Mathlib.Probability.Independence.InfinitePi

/-!
# Leaf concentration (M4a): forest deviations (Lemma 2.7)

Provider of the frozen statements `lem_GdesDev2_i` and `lem_GdesDev2_ii` (Lemma 2.7 of
arXiv:1110.2163v4, `lem:GdesDev2`).

Route.  By `firstHit_leaves_law` (M2b) the joint law `P_j[ζ = p, λ = n]` of a forest of `j` trees is
the probability that the walk first hits `-j` at time `p` with `n` zero steps among the first `p`;
it is therefore at most the probability that `n` of the first `p` steps are zero (no use of
`j ≤ p`, which is not needed).  The indicators `1{ω i = 0}` are iid Bernoulli(`μ₀`) under
`Measure.infinitePi`, so `lem_phi_i` (Chernoff) and `phiStar_lower` give `2 e^{-c √p}`.
(i) is a union over `m` (disjoint events `{#zeros = m}`), (ii) a union over `p` handled by
`IsOe.tail`.
-/

@[expose] public section

namespace BGWLeaves.LeafConcentration.ForestDeviation

open MeasureTheory ProbabilityTheory Filter BGW BGW.LocallyFinite
open scoped ENNReal

private noncomputable abbrev walkLaw (μ : PMF ℕ) : Measure (ℕ → ℕ) :=
  Measure.infinitePi fun _ : ℕ => μ.toMeasure

private noncomputable def zeroInd (i : ℕ) (ω : ℕ → ℕ) : ℝ := if ω i = 0 then 1 else 0

/-- Number of zero steps among the first `p`. -/
private def zcnt (p : ℕ) (ω : ℕ → ℕ) : ℕ := (Finset.univ.filter fun i : Fin p => ω i = 0).card

private lemma measurable_zeroInd (i : ℕ) : Measurable (zeroInd i) := by
  unfold zeroInd
  have : MeasurableSet {ω : ℕ → ℕ | ω i = 0} := measurableSet_eq_fun (measurable_pi_apply (i : ℕ)) measurable_const
  exact Measurable.ite this measurable_const measurable_const

private lemma sum_zeroInd (p : ℕ) (ω : ℕ → ℕ) :
    ∑ k ∈ Finset.range p, zeroInd k ω = (zcnt p ω : ℝ) := by
  unfold zcnt zeroInd
  rw [Finset.sum_range (fun k => if ω k = 0 then (1 : ℝ) else 0), Finset.card_filter]
  push_cast
  rfl

private lemma measurable_zcnt (p : ℕ) : Measurable (zcnt p) := by
  have : zcnt p = fun ω => ∑ i : Fin p, if ω i = 0 then 1 else 0 := by
    funext ω; unfold zcnt; rw [Finset.card_filter]
  rw [this]
  refine Finset.measurable_sum _ fun i _ => ?_
  have : MeasurableSet {ω : ℕ → ℕ | ω i = 0} :=
    measurableSet_eq_fun (measurable_pi_apply (i : ℕ)) measurable_const
  exact Measurable.ite this measurable_const measurable_const

private lemma zcnt_le (p : ℕ) (ω : ℕ → ℕ) : zcnt p ω ≤ p := by
  unfold zcnt
  calc _ ≤ (Finset.univ : Finset (Fin p)).card := Finset.card_filter_le _ _
    _ = p := by simp

private lemma p0_bounds {μ : PMF ℕ} (h0 : μ 0 ≠ 0) (h1 : μ 0 ≠ 1) :
    0 < (μ 0).toReal ∧ (μ 0).toReal < 1 := by
  have hle : μ 0 ≤ 1 := PMF.coe_le_one μ 0
  constructor
  · exact ENNReal.toReal_pos h0 (ne_top_of_le_ne_top ENNReal.one_ne_top hle)
  · have := ENNReal.toReal_strict_mono ENNReal.one_ne_top (lt_of_le_of_ne hle h1)
    simpa using this

private lemma indep_zeroInd (μ : PMF ℕ) : iIndepFun zeroInd (walkLaw μ) := by
  have := iIndepFun_infinitePi (P := fun _ : ℕ => μ.toMeasure)
    (X := fun _ (x : ℕ) => if x = 0 then (1 : ℝ) else 0) (fun _ => Measurable.of_discrete)
  exact this

private lemma bern_zeroInd (μ : PMF ℕ) (i : ℕ) :
    walkLaw μ {ω | zeroInd i ω = 1} = ENNReal.ofReal (μ 0).toReal ∧
      walkLaw μ {ω | zeroInd i ω = 0} = ENNReal.ofReal (1 - (μ 0).toReal) := by
  have hmap : (walkLaw μ).map (fun x : ℕ → ℕ => x i) = μ.toMeasure :=
    Measure.infinitePi_map_eval _ i
  have hm : Measurable (fun x : ℕ → ℕ => x i) := measurable_pi_apply i
  have hμ0 : μ.toMeasure {0} = μ 0 := PMF.toMeasure_apply_singleton μ 0 (measurableSet_singleton 0)
  have hne : μ 0 ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (PMF.coe_le_one μ 0)
  constructor
  · have e : {ω : ℕ → ℕ | zeroInd i ω = 1} = (fun x : ℕ → ℕ => x i) ⁻¹' {0} := by
      ext ω; simp [zeroInd]
    rw [e, ← Measure.map_apply hm (measurableSet_singleton 0), hmap, hμ0,
      ENNReal.ofReal_toReal hne]
  · have e : {ω : ℕ → ℕ | zeroInd i ω = 0} = (fun x : ℕ → ℕ => x i) ⁻¹' ({0}ᶜ) := by
      ext ω; simp [zeroInd]
    rw [e, ← Measure.map_apply hm (measurableSet_singleton 0).compl, hmap, prob_compl_eq_one_sub
      (measurableSet_singleton 0), hμ0, ENNReal.ofReal_sub _ ENNReal.toReal_nonneg,
      ENNReal.ofReal_one, ENNReal.ofReal_toReal hne]

/-- Both Chernoff tails for the proportion of zero steps among the first `p`. -/
private lemma zcnt_tails {μ : PMF ℕ} (h0 : μ 0 ≠ 0) (h1 : μ 0 ≠ 1) {a : ℝ} (ha : 0 < a)
    {p : ℕ} (hp : 1 ≤ p) :
    (walkLaw μ).real {ω | (μ 0).toReal + a < (zcnt p ω : ℝ) / p} ≤
        2 * Real.exp (-(p * phiStar (μ 0).toReal ((μ 0).toReal + a))) ∧
      (walkLaw μ).real {ω | (zcnt p ω : ℝ) / p < (μ 0).toReal - a} ≤
        2 * Real.exp (-(p * phiStar (μ 0).toReal ((μ 0).toReal - a))) := by
  obtain ⟨hp0, hp1⟩ := p0_bounds h0 h1
  have key := Chernoff.lem_phi_i (walkLaw μ) hp0 hp1 zeroInd measurable_zeroInd (indep_zeroInd μ)
    (bern_zeroInd μ) ha hp
  simpa only [sum_zeroInd] using key

private lemma forest_le_walk (μ : PMF ℕ) {j : ℕ} (hj : 1 ≤ j) (p n : ℕ) :
    (Measure.pi fun _ : Fin j => bienaymeLaw μ.toMeasure) (forestEvent j p n) ≤
      walkLaw μ {ω | zcnt p ω = n} := by
  rw [← firstHit_leaves_law μ.toMeasure hj p n]
  exact measure_mono fun ω hω => hω.2

private lemma exp_le_of_phi {c φ : ℝ} {n : ℕ} (hn : 1 ≤ n) (h : c / (n : ℝ) ^ (1 / 2 : ℝ) < φ) :
    Real.exp (-((n : ℝ) * φ)) ≤ Real.exp (-c * (n : ℝ) ^ (1 / 2 : ℝ)) := by
  apply Real.exp_le_exp.2
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hs : (0 : ℝ) < (n : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hn0 _
  have e : (n : ℝ) = (n : ℝ) ^ (1 / 2 : ℝ) * (n : ℝ) ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_add hn0]; norm_num
  rw [div_lt_iff₀ hs] at h
  have := mul_lt_mul_of_pos_right h hs
  have h3 : φ * ((n : ℝ) ^ (1 / 2 : ℝ) * (n : ℝ) ^ (1 / 2 : ℝ)) = φ * n := by rw [← e]
  nlinarith

private lemma isOeUniform_of_eventually {ε : ℝ} (hε : 0 < ε) {x : ℕ → ℕ → ℝ}
    (hx1 : ∀ j n : ℕ, 1 ≤ j → j ≤ n → x j n ≤ 1)
    (h : ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∃ N : ℕ, ∀ n j : ℕ, N ≤ n → 1 ≤ j → j ≤ n →
      x j n ≤ C * Real.exp (-c * (n : ℝ) ^ ε)) : IsOeUniform ε x := by
  obtain ⟨C, c, hC, hc, N, hN⟩ := h
  refine ⟨max C (Real.exp (c * (N : ℝ) ^ ε)), c, lt_max_of_lt_left hC, hc, fun n j hj hjn => ?_⟩
  by_cases hnN : N ≤ n
  · exact (hN n j hnN hj hjn).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)
  · have hnN := not_le.1 hnN
    have hle : (n : ℝ) ^ ε ≤ (N : ℝ) ^ ε :=
      Real.rpow_le_rpow (Nat.cast_nonneg n) (by exact_mod_cast hnN.le) hε.le
    have : 1 ≤ Real.exp (c * (N : ℝ) ^ ε) * Real.exp (-c * (n : ℝ) ^ ε) := by
      rw [← Real.exp_add]
      apply Real.one_le_exp
      nlinarith
    calc x j n ≤ 1 := hx1 j n hj hjn
      _ ≤ Real.exp (c * (N : ℝ) ^ ε) * Real.exp (-c * (n : ℝ) ^ ε) := this
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le

private lemma forest_real_le_one (μ : PMF ℕ) (j : ℕ) (s : Set (Fin j → LocallyFinite.Tree)) :
    (Measure.pi fun _ : Fin j => bienaymeLaw μ.toMeasure).real s ≤ 1 :=
  measureReal_le_one

/-- Bound for (i): `n ≥ max N 1`, uniformly in `j ≥ 1`. -/
private lemma part_i_bound {μ : PMF ℕ} (h0 : μ 0 ≠ 0) (h1 : μ 0 ≠ 1) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∃ N : ℕ, ∀ n j : ℕ, N ≤ n → 1 ≤ j →
      (Measure.pi fun _ : Fin j => bienaymeLaw μ.toMeasure).real
        {F | ∃ m : ℕ, F ∈ forestEvent j n m ∧
          δ / (n : ℝ) ^ (1 / 4 : ℝ) < |(m : ℝ) / n - (μ 0).toReal|} ≤
        C * Real.exp (-c * (n : ℝ) ^ (1 / 2 : ℝ)) := by
  obtain ⟨hp0, hp1⟩ := p0_bounds h0 h1
  obtain ⟨c, hc, N, hN⟩ := Chernoff.phiStar_lower hp0 hp1 hδ
  refine ⟨4, c, by norm_num, hc, max N 1, fun n j hn hj => ?_⟩
  have hnN : N ≤ n := (le_max_left _ _).trans hn
  have hn1 : 1 ≤ n := (le_max_right _ _).trans hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  set a : ℝ := δ / (n : ℝ) ^ (1 / 4 : ℝ) with ha
  have ha0 : 0 < a := div_pos hδ (Real.rpow_pos_of_pos hn0 _)
  set p0 := (μ 0).toReal with hp0def
  -- the deviation events
  set Dev : Set (ℕ → ℕ) := {ω | a < |(zcnt n ω : ℝ) / n - p0|} with hDev
  set T : ℕ → Set (ℕ → ℕ) := fun m => {ω | zcnt n ω = m ∧ a < |(m : ℝ) / n - p0|} with hT
  have hTmeas : ∀ m, MeasurableSet (T m) := fun m =>
    ((measurable_zcnt n) (measurableSet_singleton m)).inter (MeasurableSet.const _)
  have hTdisj : Pairwise (Function.onFun Disjoint T) := by
    intro m m' hmm'
    refine Set.disjoint_left.2 fun ω h1 h2 => hmm' ?_
    exact h1.1.symm.trans h2.1
  have hTsub : (⋃ m, T m) ⊆ Dev := by
    intro ω hω
    obtain ⟨m, hm⟩ := Set.mem_iUnion.1 hω
    obtain ⟨hz, hd⟩ := hm
    show a < |(zcnt n ω : ℝ) / n - p0|
    rw [hz]; exact hd
  have hA : (Measure.pi fun _ : Fin j => bienaymeLaw μ.toMeasure)
      {F | ∃ m : ℕ, F ∈ forestEvent j n m ∧ a < |(m : ℝ) / n - p0|} ≤ walkLaw μ Dev := by
    have hU : {F : Fin j → LocallyFinite.Tree | ∃ m : ℕ, F ∈ forestEvent j n m ∧
        a < |(m : ℝ) / n - p0|} = ⋃ m : ℕ, {F | F ∈ forestEvent j n m ∧ a < |(m : ℝ) / n - p0|} := by
      ext F; simp
    rw [hU]
    refine (measure_iUnion_le _).trans ?_
    calc ∑' m : ℕ, (Measure.pi fun _ : Fin j => bienaymeLaw μ.toMeasure)
          {F | F ∈ forestEvent j n m ∧ a < |(m : ℝ) / n - p0|}
        ≤ ∑' m : ℕ, walkLaw μ (T m) := by
          refine ENNReal.tsum_le_tsum fun m => ?_
          by_cases hd : a < |(m : ℝ) / n - p0|
          · refine le_trans (measure_mono fun F hF => hF.1) ?_
            exact (forest_le_walk μ hj n m).trans (measure_mono fun ω hω => ⟨hω, hd⟩)
          · have : {F : Fin j → LocallyFinite.Tree | F ∈ forestEvent j n m ∧
                a < |(m : ℝ) / n - p0|} = ∅ := by
              ext F; simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
              exact fun h => hd h.2
            rw [this]; simp
      _ = walkLaw μ (⋃ m, T m) := (measure_iUnion hTdisj hTmeas).symm
      _ ≤ walkLaw μ Dev := measure_mono hTsub
  -- Chernoff
  have hnp := hN n hnN
  obtain ⟨t1, t2⟩ := zcnt_tails h0 h1 ha0 hn1
  have hsub : Dev ⊆ {ω | p0 + a < (zcnt n ω : ℝ) / n} ∪ {ω | (zcnt n ω : ℝ) / n < p0 - a} := by
    intro ω hω
    rcases lt_abs.1 (show a < |(zcnt n ω : ℝ) / n - p0| from hω) with h | h
    · exact Or.inl (by simp only [Set.mem_ofPred_eq]; linarith)
    · exact Or.inr (by simp only [Set.mem_ofPred_eq]; linarith)
  have e1 := exp_le_of_phi hn1 hnp.1
  have e2 := exp_le_of_phi hn1 hnp.2
  calc (Measure.pi fun _ : Fin j => bienaymeLaw μ.toMeasure).real
        {F | ∃ m : ℕ, F ∈ forestEvent j n m ∧ a < |(m : ℝ) / n - p0|}
      ≤ (walkLaw μ).real Dev := ENNReal.toReal_mono (measure_ne_top _ _) hA
    _ ≤ (walkLaw μ).real ({ω | p0 + a < (zcnt n ω : ℝ) / n} ∪ {ω | (zcnt n ω : ℝ) / n < p0 - a}) :=
        measureReal_mono hsub
    _ ≤ _ := measureReal_union_le _ _
    _ ≤ 2 * Real.exp (-c * (n : ℝ) ^ (1 / 2 : ℝ)) + 2 * Real.exp (-c * (n : ℝ) ^ (1 / 2 : ℝ)) :=
        add_le_add (t1.trans (by linarith)) (t2.trans (by linarith))
    _ = 4 * Real.exp (-c * (n : ℝ) ^ (1 / 2 : ℝ)) := by ring

theorem lem_GdesDev2_i (μ : PMF ℕ) (h0 : μ 0 ≠ 0) (h1 : μ 0 ≠ 1) {δ : ℝ} (hδ : 0 < δ) :
    IsOeUniform (1 / 2) fun j n : ℕ =>
      ((Measure.pi fun _ : Fin j => bienaymeLaw μ.toMeasure).real
        {F | ∃ m : ℕ, F ∈ forestEvent j n m ∧
          δ / (n : ℝ) ^ (1 / 4 : ℝ) < |(m : ℝ) / n - (μ 0).toReal|}) := by
  refine isOeUniform_of_eventually (by norm_num) (fun j n _ _ => forest_real_le_one μ j _) ?_
  obtain ⟨C, c, hC, hc, N, hN⟩ := part_i_bound h0 h1 hδ
  exact ⟨C, c, hC, hc, N, fun n j hn hj _ => hN n j hn hj⟩

/-- Point bound for (ii): if `|p - n/μ₀| > p^{3/4}` and `p ≥ N` then `P[#zeros(first p) = n]`
is at most `2 e^{-c √p}`. -/
private lemma point_bound {μ : PMF ℕ} (h0 : μ 0 ≠ 0) (h1 : μ 0 ≠ 1) {c : ℝ} {N : ℕ}
    (hN : ∀ n : ℕ, N ≤ n →
      c / (n : ℝ) ^ (1 / 2 : ℝ) < phiStar (μ 0).toReal ((μ 0).toReal + (μ 0).toReal / (n : ℝ) ^ (1 / 4 : ℝ)) ∧
      c / (n : ℝ) ^ (1 / 2 : ℝ) < phiStar (μ 0).toReal ((μ 0).toReal - (μ 0).toReal / (n : ℝ) ^ (1 / 4 : ℝ)))
    {p n : ℕ} (hpN : N ≤ p) (hp1 : 1 ≤ p)
    (hS : (p : ℝ) ^ (3 / 4 : ℝ) < |(p : ℝ) - n / (μ 0).toReal|) :
    (walkLaw μ).real {ω | zcnt p ω = n} ≤ 2 * Real.exp (-c * (p : ℝ) ^ (1 / 2 : ℝ)) := by
  obtain ⟨hp0, hp1'⟩ := p0_bounds h0 h1
  set p0 := (μ 0).toReal with hp0def
  have hpos : (0 : ℝ) < p := by exact_mod_cast hp1
  set u : ℝ := (p : ℝ) ^ (1 / 4 : ℝ) with hu
  have hu0 : 0 < u := Real.rpow_pos_of_pos hpos _
  have hpu : (p : ℝ) ^ (3 / 4 : ℝ) * u = p := by
    rw [hu, ← Real.rpow_add hpos]; norm_num
  have hpu' : (p : ℝ) / u = (p : ℝ) ^ (3 / 4 : ℝ) := by
    rw [div_eq_iff hu0.ne']; exact hpu.symm
  have ha0 : 0 < p0 / u := div_pos hp0 hu0
  obtain ⟨t1, t2⟩ := zcnt_tails h0 h1 ha0 hp1
  obtain ⟨hN1, hN2⟩ := hN p hpN
  rcases lt_abs.1 hS with h | h
  · -- `p - n/p0 > p^{3/4}`: too few leaves
    have h2 : (n : ℝ) < (p0 - p0 / u) * p := by
      have : (n : ℝ) / p0 < p - (p : ℝ) ^ (3 / 4 : ℝ) := by linarith
      rw [div_lt_iff₀ hp0] at this
      have e : (p0 - p0 / u) * p = p0 * p - p0 * (p / u) := by ring
      rw [e, hpu']; nlinarith
    have h3 : (n : ℝ) / p < p0 - p0 / u := by rwa [div_lt_iff₀ hpos]
    refine le_trans (measureReal_mono ?_) (t2.trans ?_)
    · intro ω hω
      have : zcnt p ω = n := hω
      show (zcnt p ω : ℝ) / p < p0 - p0 / u
      rw [this]; exact h3
    · exact mul_le_mul_of_nonneg_left (exp_le_of_phi hp1 hN2) (by norm_num)
  · have h2 : (p0 + p0 / u) * p < (n : ℝ) := by
      have : (p : ℝ) + (p : ℝ) ^ (3 / 4 : ℝ) < (n : ℝ) / p0 := by linarith
      rw [lt_div_iff₀ hp0] at this
      have e : (p0 + p0 / u) * p = p0 * p + p0 * (p / u) := by ring
      rw [e, hpu']; nlinarith
    have h3 : p0 + p0 / u < (n : ℝ) / p := by rwa [lt_div_iff₀ hpos]
    refine le_trans (measureReal_mono ?_) (t1.trans ?_)
    · intro ω hω
      have : zcnt p ω = n := hω
      show p0 + p0 / u < (zcnt p ω : ℝ) / p
      rw [this]; exact h3
    · exact mul_le_mul_of_nonneg_left (exp_le_of_phi hp1 hN1) (by norm_num)

/-- Bound for (ii), for `n ≥ max N 1`, uniformly in `j ≥ 1`. -/
private lemma part_ii_bound {μ : PMF ℕ} (h0 : μ 0 ≠ 0) (h1 : μ 0 ≠ 1) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∃ N : ℕ, ∀ n j : ℕ, N ≤ n → 1 ≤ j →
      (Measure.pi fun _ : Fin j => bienaymeLaw μ.toMeasure).real
        {F | ∃ p : ℕ, F ∈ forestEvent j p n ∧
          (p : ℝ) ^ (3 / 4 : ℝ) < |(p : ℝ) - n / (μ 0).toReal|} ≤
        C * Real.exp (-c * (n : ℝ) ^ (1 / 2 : ℝ)) := by
  obtain ⟨hp0, hp1⟩ := p0_bounds h0 h1
  obtain ⟨c, hc, N, hN⟩ := Chernoff.phiStar_lower hp0 hp1 hp0
  set x : ℕ → ℝ := fun k => 2 * Real.exp (-c * (k : ℝ) ^ (1 / 2 : ℝ)) with hx
  have hx0 : ∀ k, 0 ≤ x k := fun k => by positivity
  have hxOe : IsOe (1 / 2) x := ⟨2, c, by norm_num, hc, fun k => le_rfl⟩
  obtain ⟨hsum, C', c', hC', hc', htail⟩ := OeLemmas.IsOe.tail (by norm_num) hx0 hxOe
  refine ⟨C', c', hC', hc', max N 1, fun n j hn hj => ?_⟩
  have hnN : N ≤ n := (le_max_left _ _).trans hn
  have hn1 : 1 ≤ n := (le_max_right _ _).trans hn
  set P := Measure.pi fun _ : Fin j => bienaymeLaw μ.toMeasure with hP
  set f : ℕ → ℝ := fun p => if n ≤ p then x p else 0 with hf
  have hf0 : ∀ p, 0 ≤ f p := fun p => by simp only [hf]; split_ifs <;> simp [hx0]
  have hfx : ∀ p, f p ≤ x p := fun p => by
    simp only [hf]; split_ifs
    · exact le_rfl
    · exact hx0 p
  have hfsum : Summable f := Summable.of_nonneg_of_le hf0 hfx hsum
  set H : ℕ → Set (Fin j → LocallyFinite.Tree) := fun p =>
    {F | F ∈ forestEvent j p n ∧ (p : ℝ) ^ (3 / 4 : ℝ) < |(p : ℝ) - n / (μ 0).toReal|} with hH
  have hHp : ∀ p, P (H p) ≤ ENNReal.ofReal (f p) := by
    intro p
    have hle : P (H p) ≤ walkLaw μ {ω | zcnt p ω = n} :=
      (measure_mono fun F hF => hF.1).trans (forest_le_walk μ hj p n)
    by_cases hnp : n ≤ p
    · by_cases hS : (p : ℝ) ^ (3 / 4 : ℝ) < |(p : ℝ) - n / (μ 0).toReal|
      · have hpN : N ≤ p := hnN.trans hnp
        have hp1' : 1 ≤ p := hn1.trans hnp
        have hb := point_bound h0 h1 (c := c) (N := N) (fun m hm => by
          obtain ⟨a, b⟩ := hN m hm
          exact ⟨by simpa using a, by simpa using b⟩) hpN hp1' hS
        calc P (H p) ≤ walkLaw μ {ω | zcnt p ω = n} := hle
          _ = ENNReal.ofReal ((walkLaw μ).real {ω | zcnt p ω = n}) :=
              (ofReal_measureReal (measure_ne_top _ _)).symm
          _ ≤ ENNReal.ofReal (f p) := by
              apply ENNReal.ofReal_le_ofReal
              rw [hf]; simp only [hnp, ↓reduceIte, hx]; exact hb
      · have : H p = ∅ := by
          ext F; simp only [hH, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
          exact fun h => hS h.2
        rw [this]; simp
    · have hlt : p < n := not_le.1 hnp
      have : {ω | zcnt p ω = n} = (∅ : Set (ℕ → ℕ)) := by
        ext ω; simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
        have := zcnt_le p ω; omega
      rw [this] at hle
      simpa [hf, hnp] using hle
  have hE : {F : Fin j → LocallyFinite.Tree | ∃ p : ℕ, F ∈ forestEvent j p n ∧
      (p : ℝ) ^ (3 / 4 : ℝ) < |(p : ℝ) - n / (μ 0).toReal|} ⊆ ⋃ p, H p := by
    intro F ⟨p, hp⟩
    exact Set.mem_iUnion.2 ⟨p, hp⟩
  have hPE : P {F | ∃ p : ℕ, F ∈ forestEvent j p n ∧
      (p : ℝ) ^ (3 / 4 : ℝ) < |(p : ℝ) - n / (μ 0).toReal|} ≤ ENNReal.ofReal (∑' p, f p) := by
    rw [ENNReal.ofReal_tsum_of_nonneg hf0 hfsum]
    exact (measure_mono hE).trans ((measure_iUnion_le _).trans (ENNReal.tsum_le_tsum hHp))
  have hS0 : 0 ≤ ∑' p, f p := tsum_nonneg hf0
  have hshift : ∑' p, f p = ∑' k : ℕ, x (n + k) := by
    rw [← hfsum.sum_add_tsum_nat_add n]
    have h1' : ∑ i ∈ Finset.range n, f i = 0 :=
      Finset.sum_eq_zero fun i hi => by
        have : ¬ n ≤ i := by have := Finset.mem_range.1 hi; omega
        simp [hf, this]
    rw [h1', zero_add]
    refine tsum_congr fun k => ?_
    simp [hf, add_comm]
  calc P.real {F | ∃ p : ℕ, F ∈ forestEvent j p n ∧
        (p : ℝ) ^ (3 / 4 : ℝ) < |(p : ℝ) - n / (μ 0).toReal|}
      ≤ (ENNReal.ofReal (∑' p, f p)).toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hPE
    _ = ∑' p, f p := ENNReal.toReal_ofReal hS0
    _ = ∑' k : ℕ, x (n + k) := hshift
    _ ≤ C' * Real.exp (-c' * (n : ℝ) ^ (1 / 2 : ℝ)) := htail n

theorem lem_GdesDev2_ii (μ : PMF ℕ) (h0 : μ 0 ≠ 0) (h1 : μ 0 ≠ 1) :
    IsOeUniform (1 / 2) fun j n : ℕ =>
      ((Measure.pi fun _ : Fin j => bienaymeLaw μ.toMeasure).real
        {F | ∃ p : ℕ, F ∈ forestEvent j p n ∧
          (p : ℝ) ^ (3 / 4 : ℝ) < |(p : ℝ) - n / (μ 0).toReal|}) := by
  refine isOeUniform_of_eventually (by norm_num) (fun j n _ _ => forest_real_le_one μ j _) ?_
  obtain ⟨C, c, hC, hc, N, hN⟩ := part_ii_bound h0 h1
  exact ⟨C, c, hC, hc, N, fun n j hn hj _ => hN n j hn hj⟩

end BGWLeaves.LeafConcentration.ForestDeviation
