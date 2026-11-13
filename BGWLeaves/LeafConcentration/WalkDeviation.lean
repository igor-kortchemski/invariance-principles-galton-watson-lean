module

public import BGWLeaves.LeafConcentration.Defs
import BGWLeaves.Passage.Atoms
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import BGWLeaves.LeafConcentration.Chernoff
public import BGWLeaves.LeafConcentration.OeLemmas

@[expose] public section

namespace BGWLeaves.LeafConcentration.WalkDeviation

open MeasureTheory ProbabilityTheory Filter BGW BGW.LocallyFinite
open scoped ENNReal Topology

/-- The DFS degree list reads the intrinsic offspring count at the corresponding address. -/
theorem childCountAt_eq_offspringAt (t : PlaneTree) {j : ℕ} (hj : j < t.size) :
    childCountAt t j =
      t.offspringAt (PlaneTree.positiveAddress (t.vertices.getD j [])) := by
  have hv : j < t.vertices.length := by simpa using hj
  have hd : j < t.degrees.length := by simpa using hj
  have h := congrArg (fun l : List (Option ℕ) => l[j]?)
    (PlaneTree.map_fringe?_vertices_rootDegree t)
  simp only [List.getElem?_map, List.getElem?_eq_getElem hv,
    List.getElem?_eq_getElem hd, Option.map_some] at h
  simp only [childCountAt, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem hv, List.getElem?_eq_getElem hd, Option.getD_some,
    PlaneTree.offspringAt_positiveAddress]
  rw [Option.some.inj h]
  rfl

private theorem increments_code (t : PlaneTree) : IsForestCode 1 t.increments := by
  obtain ⟨hge, hsum, hpre⟩ := t.isTreeExcursion_increments
  exact ⟨hge, hsum, fun i hi => by have := hpre i hi; omega⟩

private theorem tree_stopped_measurable (t : PlaneTree) :
    MeasurableSet (stoppedWordEvent 1 t.increments) := by
  rw [Passage.Atoms.stoppedWordEvent_eq_cylinder _ (increments_code t)]
  exact MeasurableSet.pi (Finset.countable_toSet _) (fun _ _ => measurableSet_singleton _)

private theorem tree_stopped_disjoint : Pairwise
    (Function.onFun Disjoint (fun t : PlaneTree => stoppedWordEvent 1 t.increments)) := by
  intro t s hts
  apply Set.disjoint_left.mpr
  intro ω ht hs
  have hlen : t.increments.length = s.increments.length := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · have hpre := hs.1.2 _ h
      rw [ht.1.1] at hpre
      omega
    · have hpre := ht.1.2 _ h
      rw [hs.1.1] at hpre
      omega
  apply hts
  apply PlaneTree.increments_injective
  apply List.ext_getElem hlen
  intro i hi hj
  exact (ht.2 i hi).symm.trans (hs.2 i hj)

/-- Equality of the finite-tree event law and the stopped-word event law. -/
theorem tree_law_eq_walk_law (μ : PMF ℕ) (Q : PlaneTree → Prop) :
    bienaymeLaw μ.toMeasure (finiteTreeEvent Q) =
      (Measure.infinitePi fun _ : ℕ => μ.toMeasure)
        {ω | ∃ t : PlaneTree, Q t ∧ ω ∈ stoppedWordEvent 1 t.increments} := by
  classical
  have htree : finiteTreeEvent Q =
      ⋃ t : {t : PlaneTree // Q t}, {t.val.toLocallyFinite} := by
    ext T
    simp only [finiteTreeEvent, Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_singleton_iff]
    constructor
    · rintro ⟨t, rfl, ht⟩
      exact ⟨⟨t, ht⟩, rfl⟩
    · rintro ⟨⟨t, ht⟩, rfl⟩
      exact ⟨t, rfl, ht⟩
  have hwalk : {ω | ∃ t : PlaneTree, Q t ∧ ω ∈ stoppedWordEvent 1 t.increments} =
      ⋃ t : {t : PlaneTree // Q t}, stoppedWordEvent 1 t.val.increments := by
    ext ω
    simp
  rw [htree, hwalk,
    measure_iUnion (fun (t s : {t : PlaneTree // Q t}) h => pairwise_disjoint_singleton_toLocallyFinite
      (fun heq => h (Subtype.ext heq))) (fun _ => measurableSet_singleton _),
    measure_iUnion (fun (t s : {t : PlaneTree // Q t}) h => tree_stopped_disjoint
      (fun heq => h (Subtype.ext heq))) (fun t => tree_stopped_measurable t.val)]
  apply tsum_congr
  intro t
  rw [bienaymeLaw_toLocallyFinite,
    Passage.Atoms.stoppedWordEvent_measure_eq_walkWeight_of_code μ.toMeasure
      t.val.increments (increments_code t.val), PlaneTree.walkWeight_increments]

/-- Extend an eventual exponential estimate across a finite initial segment. -/
theorem isOe_of_eventually_bound {ε : ℝ} (hε : 0 < ε) {x : ℕ → ℝ}
    (hx : ∀ n, x n ≤ 1) {C c : ℝ} (hC : 0 < C) (hc : 0 < c)
    (h : ∀ᶠ n : ℕ in atTop, x n ≤ C * Real.exp (-c * (n : ℝ) ^ ε)) : IsOe ε x := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 h
  refine ⟨C + Real.exp (c * (N : ℝ) ^ ε), c, by positivity, hc, fun n => ?_⟩
  by_cases hn : N ≤ n
  · exact (hN n hn).trans (mul_le_mul_of_nonneg_right (by linarith [Real.exp_pos (c * (N : ℝ) ^ ε)]) (Real.exp_pos _).le)
  · have hpow : (n : ℝ) ^ ε ≤ (N : ℝ) ^ ε :=
      Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast (Nat.le_of_lt (not_le.1 hn))) hε.le
    have he : 1 ≤ Real.exp (c * (N : ℝ) ^ ε) * Real.exp (-c * (n : ℝ) ^ ε) := by
      rw [← Real.exp_add, Real.one_le_exp_iff]
      nlinarith
    exact (hx n).trans (he.trans (by nlinarith [Real.exp_pos (-c * (n : ℝ) ^ ε)]))

private def zeroIndicator (m : ℕ) : ℝ := if m = 0 then 1 else 0

private theorem zeroIndicator_sum (ω : ℕ → ℕ) (k : ℕ) :
    ∑ i ∈ Finset.range k, zeroIndicator (ω i) = (walkLeafCount ω k : ℝ) := by
  unfold walkLeafCount
  rw [Finset.card_filter, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases h : ω i = 0 <;> simp [zeroIndicator, h]

private theorem zeroIndicator_bernoulli (μ : PMF ℕ) (i : ℕ) :
    (Measure.infinitePi fun _ : ℕ => μ.toMeasure) {ω | zeroIndicator (ω i) = 1} =
        ENNReal.ofReal (μ 0).toReal ∧
      (Measure.infinitePi fun _ : ℕ => μ.toMeasure) {ω | zeroIndicator (ω i) = 0} =
        ENNReal.ofReal (1 - (μ 0).toReal) := by
  have h : (Measure.infinitePi fun _ : ℕ => μ.toMeasure) {ω | ω i = 0} = μ 0 := by
    rw [← PMF.toMeasure_apply_singleton μ 0 (measurableSet_singleton (0 : ℕ))]
    convert (measurePreserving_eval_infinitePi (fun _ : ℕ => μ.toMeasure) i).measure_preimage
      (measurableSet_singleton (0 : ℕ)).nullMeasurableSet using 1
    congr 1
  have hset1 : {ω : ℕ → ℕ | zeroIndicator (ω i) = 1} = {ω | ω i = 0} := by
    ext ω; simp [zeroIndicator]
  have hset0 : {ω : ℕ → ℕ | zeroIndicator (ω i) = 0} = {ω | ω i = 0}ᶜ := by
    ext ω; simp [zeroIndicator]
  rw [hset1, hset0, h, measure_compl (by measurability) (by finiteness), measure_univ, h]
  simp [ENNReal.ofReal_sub, ENNReal.ofReal_toReal, PMF.apply_ne_top]

/-- The change from a real time to the next integer costs at most `1/s`. -/
private theorem prefix_fraction_shift {S s k p : ℝ} (hs : 0 < s) (hk : 0 < k)
    (hS0 : 0 ≤ S) (hSk : S ≤ k) (hsk : s ≤ k) (hks : k ≤ s + 1) :
    |S / s - p| ≤ |S / k - p| + 1 / s := by
  have hx0 : 0 ≤ S / k := div_nonneg hS0 hk.le
  have hx1 : S / k ≤ 1 := (div_le_one hk).2 hSk
  have heq : S / s - S / k = (S / k * (k - s)) / s := by field_simp
  have hd0 : 0 ≤ S / s - S / k := by rw [heq]; positivity
  have hd1 : S / s - S / k ≤ 1 / s := by
    rw [heq, div_le_div_iff_of_pos_right hs]
    nlinarith
  have h := abs_sub_le (S / s) (S / k) p
  rw [abs_of_nonneg hd0] at h
  linarith

private theorem walk_bad_subset (p η δ : ℝ) {n : ℕ} (hn : 1 ≤ n)
    (hη : 0 < η) (hδ : 0 < δ)
    (hshift : 1 / (η * n) ≤ (δ / 2) / (n : ℝ) ^ (1 / 4 : ℝ)) :
    {ω | ENNReal.ofReal (δ / (n : ℝ) ^ (1 / 4 : ℝ)) < supDev η (walkLeafDev p ω n)} ⊆
      ⋃ k ∈ Finset.Icc (⌊η * (n : ℝ)⌋₊ + 1) (n + 1),
        {ω | (δ / 2) / (n : ℝ) ^ (1 / 4 : ℝ) < |(walkLeafCount ω k : ℝ) / k - p|} := by
  intro ω hω
  obtain ⟨t, ht, hdev⟩ := (lt_supDev_iff (by positivity) _).1 hω
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hs : 0 < (n : ℝ) * t := mul_pos hn0 (hη.trans_le ht.1)
  let k := ⌊(n : ℝ) * t⌋₊ + 1
  have hsk : (n : ℝ) * t < k := by dsimp [k]; simpa only [Nat.cast_add, Nat.cast_one] using Nat.lt_floor_add_one ((n : ℝ) * t)
  have hks : (k : ℝ) ≤ (n : ℝ) * t + 1 := by
    dsimp [k]; push_cast; linarith [Nat.floor_le hs.le]
  have hk0 : (0 : ℝ) < k := hs.trans hsk
  have hk : k ∈ Finset.Icc (⌊η * (n : ℝ)⌋₊ + 1) (n + 1) := by
    simp only [Finset.mem_Icc, k]
    constructor
    · exact Nat.add_le_add_right (Nat.floor_le_floor (by nlinarith [ht.1])) 1
    · have : ⌊(n : ℝ) * t⌋₊ ≤ n := Nat.floor_le_of_le (by nlinarith [ht.2])
      omega
  have hcnt : (walkLeafCount ω k : ℝ) ≤ k := by
    exact_mod_cast (Finset.card_filter_le (Finset.range k) _).trans (by simp)
  have hnum := prefix_fraction_shift (p := p) hs hk0 (Nat.cast_nonneg _) hcnt hsk.le hks
  have hi : 1 / ((n : ℝ) * t) ≤ 1 / (η * n) :=
    one_div_le_one_div_of_le (by positivity) (by nlinarith [ht.1])
  have hbad : (δ / 2) / (n : ℝ) ^ (1 / 4 : ℝ) < |(walkLeafCount ω k : ℝ) / k - p| := by
    change δ / (n : ℝ) ^ (1 / 4 : ℝ) < |(walkLeafCount ω k : ℝ) / ((n : ℝ) * t) - p| at hdev
    have he : δ / (n : ℝ) ^ (1 / 4 : ℝ) = 2 * ((δ / 2) / (n : ℝ) ^ (1 / 4 : ℝ)) := by ring
    rw [he] at hdev
    linarith
  exact Set.mem_iUnion.2 ⟨k, Set.mem_iUnion.2 ⟨hk, hbad⟩⟩

private theorem bernoulli_prefix_tail (μ : PMF ℕ) (hp0 : 0 < (μ 0).toReal)
    (hp1 : (μ 0).toReal < 1) {a : ℝ} (ha : 0 < a) {k : ℕ} (hk : 1 ≤ k) :
    (Measure.infinitePi fun _ : ℕ => μ.toMeasure).real
      {ω | a < |(walkLeafCount ω k : ℝ) / k - (μ 0).toReal|} ≤
      2 * Real.exp (-(k * phiStar (μ 0).toReal ((μ 0).toReal + a))) +
        2 * Real.exp (-(k * phiStar (μ 0).toReal ((μ 0).toReal - a))) := by
  let P := Measure.infinitePi fun _ : ℕ => μ.toMeasure
  have hX : ∀ i : ℕ, Measurable (fun ω : ℕ → ℕ => zeroIndicator (ω i)) :=
    fun i => (measurable_of_countable zeroIndicator).comp (measurable_pi_apply i)
  have hind : iIndepFun (fun i (ω : ℕ → ℕ) => zeroIndicator (ω i)) P :=
    iIndepFun_infinitePi (fun _ => measurable_of_countable zeroIndicator)
  obtain ⟨hu, hl⟩ := Chernoff.lem_phi_i P hp0 hp1 _ hX hind
    (zeroIndicator_bernoulli μ) ha hk
  simp only [zeroIndicator_sum] at hu hl
  have hsub : {ω | a < |(walkLeafCount ω k : ℝ) / k - (μ 0).toReal|} ⊆
      {ω | (μ 0).toReal + a < (walkLeafCount ω k : ℝ) / k} ∪
        {ω | (walkLeafCount ω k : ℝ) / k < (μ 0).toReal - a} := by
    intro ω hω
    change a < |(walkLeafCount ω k : ℝ) / k - (μ 0).toReal| at hω
    rcases (lt_abs.mp hω) with h | h
    · exact Or.inl (by dsimp; linarith)
    · exact Or.inr (by dsimp; linarith)
  exact (measureReal_mono hsub).trans ((measureReal_union_le _ _).trans (add_le_add hu hl))

/-- Lemma 2.5(i): exponential concentration of all real-time walk prefixes. -/
theorem lem_GdesDev_walk (μ : PMF ℕ) (h0 : μ 0 ≠ 0) (h1 : μ 0 ≠ 1) {η δ : ℝ}
    (hη0 : 0 < η) (hη1 : η < 1) (hδ : 0 < δ) :
    IsOe (1 / 2) fun n : ℕ =>
      ((Measure.infinitePi fun _ : ℕ => μ.toMeasure).real
        {ω | ENNReal.ofReal (δ / (n : ℝ) ^ (1 / 4 : ℝ)) <
          supDev η (walkLeafDev (μ 0).toReal ω n)}) := by
  have hp0 : 0 < (μ 0).toReal := ENNReal.toReal_pos h0 (μ.apply_ne_top 0)
  have hp1 : (μ 0).toReal < 1 := by
    have hlt : μ 0 < 1 := lt_of_le_of_ne (PMF.coe_le_one μ 0) h1
    simpa using (ENNReal.toReal_lt_toReal (μ.apply_ne_top 0) ENNReal.one_ne_top).2 hlt
  obtain ⟨c, hc, N, hN⟩ := Chernoff.phiStar_lower hp0 hp1 (half_pos hδ)
  have ht : Tendsto (fun n : ℕ => (n : ℝ) ^ (1 / 4 : ℝ) / (η * n)) atTop (𝓝 0) := by
    have h0t := ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 3 / 4)).comp
      tendsto_natCast_atTop_atTop).div_const η
    have h : Tendsto (fun n : ℕ => (n : ℝ) ^ (-(3 / 4 : ℝ)) / η) atTop (𝓝 0) := by simpa using h0t
    apply h.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    change (n : ℝ) ^ (-(3 / 4 : ℝ)) / η = _
    have he : (n : ℝ) ^ (-(3 / 4 : ℝ)) = (n : ℝ) ^ (1 / 4 : ℝ) / n := by
      calc _ = (n : ℝ) ^ ((1 / 4 : ℝ) - 1) := by norm_num
           _ = _ := by rw [Real.rpow_sub hn0, Real.rpow_one]
    rw [he]
    ring
  have hshift : ∀ᶠ n : ℕ in atTop,
      1 / (η * n) ≤ (δ / 2) / (n : ℝ) ^ (1 / 4 : ℝ) := by
    filter_upwards [ht.eventually (eventually_lt_nhds (half_pos hδ)), eventually_ge_atTop 1] with n hn hn1
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
    rw [le_div_iff₀ (Real.rpow_pos_of_pos hn0 _)]
    simpa [div_eq_mul_inv, mul_comm] using hn.le
  have hb : IsOe (1 / 2) (fun n : ℕ => (n : ℝ) ^ (1 : ℝ) *
      (12 * Real.exp (-(η * c) * (n : ℝ) ^ (1 / 2 : ℝ)))) :=
    OeLemmas.IsOe.poly_mul (by norm_num)
      ⟨12, η * c, by norm_num, mul_pos hη0 hc, fun _ => le_rfl⟩ 1
  obtain ⟨C, d, hC, hd, hbd⟩ := hb
  apply isOe_of_eventually_bound (by norm_num) (fun _ => measureReal_le_one) hC hd
  filter_upwards [hshift, eventually_ge_atTop (max N 1)] with n hsh hn
  have hn1 : 1 ≤ n := (le_max_right _ _).trans hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hroot : 0 < (n : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hn0 _
  have hr : (n : ℝ) ^ (1 / 2 : ℝ) * (n : ℝ) ^ (1 / 2 : ℝ) = n := by
    rw [← Real.rpow_add hn0]; norm_num
  let I := Finset.Icc (⌊η * (n : ℝ)⌋₊ + 1) (n + 1)
  let E := fun k : ℕ => {ω : ℕ → ℕ | (δ / 2) / (n : ℝ) ^ (1 / 4 : ℝ) <
    |(walkLeafCount ω k : ℝ) / k - (μ 0).toReal|}
  have hE : ∀ k ∈ I, (Measure.infinitePi fun _ : ℕ => μ.toMeasure).real (E k) ≤
      4 * Real.exp (-(η * c) * (n : ℝ) ^ (1 / 2 : ℝ)) := by
    intro k hk
    obtain ⟨hkl, hku⟩ := Finset.mem_Icc.1 hk
    have hk1 : 1 ≤ k := by omega
    have hkη : η * (n : ℝ) ≤ k := by
      have := Nat.lt_floor_add_one (η * (n : ℝ))
      exact this.le.trans (by exact_mod_cast hkl)
    have hphi := hN n ((le_max_left _ _).trans hn)
    have hmul : η * c * (n : ℝ) ^ (1 / 2 : ℝ) ≤ (k : ℝ) * (c / (n : ℝ) ^ (1 / 2 : ℝ)) := by
      rw [← mul_div_assoc, le_div_iff₀ hroot]
      calc η * c * (n : ℝ) ^ (1 / 2 : ℝ) * (n : ℝ) ^ (1 / 2 : ℝ) = η * n * c  := by
             calc _ = (η * c) * ((n : ℝ) ^ (1 / 2 : ℝ) * (n : ℝ) ^ (1 / 2 : ℝ)) := by ring
                  _ = _ := by rw [hr]; ring
           _ ≤ k * c := mul_le_mul_of_nonneg_right hkη hc.le
    have hup := mul_le_mul_of_nonneg_left hphi.1.le (show (0 : ℝ) ≤ k by positivity)
    have hlo := mul_le_mul_of_nonneg_left hphi.2.le (show (0 : ℝ) ≤ k by positivity)
    refine (bernoulli_prefix_tail μ hp0 hp1 (by positivity) hk1).trans ?_
    have he1 := Real.exp_le_exp.2 (neg_le_neg (hmul.trans hup))
    have he2 := Real.exp_le_exp.2 (neg_le_neg (hmul.trans hlo))
    have heq : -(η * c * (n : ℝ) ^ (1 / 2 : ℝ)) = -(η * c) * (n : ℝ) ^ (1 / 2 : ℝ) := by ring
    rw [heq] at he1 he2
    linarith
  have hfloor : ⌊η * (n : ℝ)⌋₊ ≤ n := Nat.floor_le_of_le (by nlinarith)
  have hcard_exact : I.card = n + 1 - ⌊η * (n : ℝ)⌋₊ := by
    simp only [I, Nat.card_Icc]
    omega
  have hcard_sharp : (I.card : ℝ) ≤ (1 - η) * n + 2 := by
    rw [hcard_exact, Nat.cast_sub (by omega : ⌊η * (n : ℝ)⌋₊ ≤ n + 1)]
    push_cast
    have := Nat.lt_floor_add_one (η * (n : ℝ))
    nlinarith
  have hcard : I.card ≤ 3 * n := by
    have hn1r : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    have : (I.card : ℝ) ≤ 3 * n := by nlinarith
    exact_mod_cast this
  calc _ ≤ (Measure.infinitePi fun _ : ℕ => μ.toMeasure).real (⋃ k ∈ I, E k) :=
        measureReal_mono (μ := Measure.infinitePi fun _ : ℕ => μ.toMeasure) (walk_bad_subset _ _ _ hn1 hη0 hδ hsh) (measure_ne_top _ _)
    _ ≤ ∑ k ∈ I, (Measure.infinitePi fun _ : ℕ => μ.toMeasure).real (E k) :=
        measureReal_biUnion_finset_le I E
    _ ≤ ∑ _k ∈ I, 4 * Real.exp (-(η * c) * (n : ℝ) ^ (1 / 2 : ℝ)) :=
        Finset.sum_le_sum hE
    _ ≤ (n : ℝ) ^ (1 : ℝ) * (12 * Real.exp (-(η * c) * (n : ℝ) ^ (1 / 2 : ℝ))) := by
        simp only [Finset.sum_const, nsmul_eq_mul, Real.rpow_one]
        have : (I.card : ℝ) ≤ 3 * n := by exact_mod_cast hcard
        nlinarith [Real.exp_pos (-(η * c) * (n : ℝ) ^ (1 / 2 : ℝ))]
    _ ≤ C * Real.exp (-d * (n : ℝ) ^ (1 / 2 : ℝ)) := hbd n

end BGWLeaves.LeafConcentration.WalkDeviation
