module

public import BGWLeaves.LeafConcentration.Defs
import BGWLeaves.LeafConcentration.SizeLower
public import BGWLeaves.LeafConcentration.WalkDeviation
public import BGWLeaves.LeafConcentration.OeLemmas

@[expose] public section

namespace BGWLeaves.LeafConcentration.TreeDeviation

open MeasureTheory ProbabilityTheory Filter BGW BGW.StableTrees BGW.LocallyFinite
open BGWLeaves.StableAnalysis
open scoped ENNReal Topology

private theorem finiteTreeEvent_measurable (Q : PlaneTree → Prop) :
    MeasurableSet (finiteTreeEvent Q) := by
  have h : finiteTreeEvent Q = PlaneTree.toLocallyFinite '' {t | Q t} := by
    ext T; simp [finiteTreeEvent, Set.mem_image, and_comm]
  rw [h]
  exact (Set.to_countable _ |>.image _).measurableSet

private theorem finiteTreeEvent_inter_size (Q : PlaneTree → Prop) (n : ℕ) :
    sizeEvent n ∩ finiteTreeEvent Q = finiteTreeEvent (fun t => t.size = n ∧ Q t) := by
  ext T
  constructor
  · rintro ⟨hs, t, rfl, ht⟩
    exact ⟨t, rfl, (toLocallyFinite_mem_sizeEvent_iff t n).1 hs, ht⟩
  · rintro ⟨t, rfl, hs, ht⟩
    exact ⟨(toLocallyFinite_mem_sizeEvent_iff t n).2 hs, t, rfl, ht⟩

private theorem walkLeafCount_succ (ω : ℕ → ℕ) (n : ℕ) :
    walkLeafCount ω (n + 1) = walkLeafCount ω n + if ω n = 0 then 1 else 0 := by
  unfold walkLeafCount
  rw [Finset.card_filter, Finset.card_filter, Finset.sum_range_succ]
  by_cases h : ω n = 0 <;> simp [h]

private theorem abs_fraction_increment {x y s p : ℝ} (hs : 0 < s)
    (hxy : x ≤ y) (hyx : y ≤ x + 1) :
    |x / s - p| ≤ |y / s - p| + 1 / s := by
  have hd : |x / s - y / s| ≤ 1 / s := by
    rw [← sub_div, abs_div, abs_of_pos hs, div_le_div_iff_of_pos_right hs, abs_le]
    constructor <;> linarith
  have := abs_sub_le (x / s) (y / s) p
  linarith

private theorem tree_walk_pointwise (p : ℝ) (t : PlaneTree) (ω : ℕ → ℕ)
    (hω : ω ∈ stoppedWordEvent 1 t.increments) {n : ℕ} (ht : t.size = n)
    {u : ℝ} (hs : 0 < (n : ℝ) * u) (hu : u ≤ 1) :
    |treeLeafDev p t n u| ≤ |walkLeafDev p ω n u| + 1 / ((n : ℝ) * u) := by
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hsu : (n : ℝ) * u ≤ n := by nlinarith
  obtain ⟨hinside, hend, -⟩ := Lambda_translation t ω hω
  by_cases hlt : (n : ℝ) * u < n
  · have he := hinside ((n : ℝ) * u) hs.le (by simpa [ht] using hlt)
    simp only [treeLeafDev, walkLeafDev, he]
    linarith [one_div_pos.mpr hs]
  · have heq : (n : ℝ) * u = n := le_antisymm hsu (not_lt.1 hlt)
    have hcount := walkLeafCount_succ ω n
    have hcount0 : walkLeafCount ω n ≤ walkLeafCount ω (n + 1) := by omega
    have hcount1 : walkLeafCount ω (n + 1) ≤ walkLeafCount ω n + 1 := by split_ifs at hcount <;> omega
    simp only [treeLeafDev, walkLeafDev, heq, Nat.floor_natCast]
    rw [← ht, hend, ht]
    apply abs_fraction_increment (by simpa [heq] using hs)
    · exact_mod_cast hcount0
    · exact_mod_cast hcount1

private theorem tree_bad_implies_walk_bad (p η δ : ℝ) (hη : 0 < η) (hδ : 0 < δ)
    {n : ℕ} (hn : 1 ≤ n)
    (hshift : 1 / (η * n) < (δ / 2) / (n : ℝ) ^ (1 / 4 : ℝ))
    (t : PlaneTree) (ht : t.size = n) (ω : ℕ → ℕ)
    (hω : ω ∈ stoppedWordEvent 1 t.increments)
    (hbad : ENNReal.ofReal (δ / (n : ℝ) ^ (1 / 4 : ℝ)) ≤ supDev η (treeLeafDev p t n)) :
    ENNReal.ofReal ((δ / 2) / (n : ℝ) ^ (1 / 4 : ℝ)) < supDev η (walkLeafDev p ω n) := by
  by_contra hw
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hub : ∀ u ∈ Set.Icc η 1,
      |walkLeafDev p ω n u| ≤ (δ / 2) / (n : ℝ) ^ (1 / 4 : ℝ) := by
    intro u hu
    by_contra hh
    exact hw ((lt_supDev_iff (by positivity) _).2 ⟨u, hu, not_le.1 hh⟩)
  have hsup : supDev η (treeLeafDev p t n) ≤
      ENNReal.ofReal ((δ / 2) / (n : ℝ) ^ (1 / 4 : ℝ) + 1 / (η * n)) := by
    apply iSup_le
    intro u
    apply iSup_le
    intro hu
    apply ENNReal.ofReal_le_ofReal
    have hs : 0 < (n : ℝ) * u := mul_pos hn0 (hη.trans_le hu.1)
    have hpoint := tree_walk_pointwise p t ω hω ht hs hu.2
    have hi : 1 / ((n : ℝ) * u) ≤ 1 / (η * n) :=
      one_div_le_one_div_of_le (by positivity) (by nlinarith [hu.1])
    linarith [hub u hu]
  have hlt : (δ / 2) / (n : ℝ) ^ (1 / 4 : ℝ) + 1 / (η * n) <
      δ / (n : ℝ) ^ (1 / 4 : ℝ)  := by
    have he : δ / (n : ℝ) ^ (1 / 4 : ℝ) = 2 * ((δ / 2) / (n : ℝ) ^ (1 / 4 : ℝ)) := by ring
    rw [he]
    linarith
  exact (not_lt_of_ge (hbad.trans hsup)) ((ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 hlt)

private theorem cond_real_le_one (P : Measure Tree) [IsFiniteMeasure P] (s A : Set Tree) :
    (P[|s]).real A ≤ 1 := by
  by_cases hs : P s = 0
  · simp [cond_eq_zero_of_meas_eq_zero hs]
  · have := cond_isProbabilityMeasure (μ := P) hs
    exact measureReal_le_one

private theorem cond_real_eq_div (P : Measure Tree) [IsFiniteMeasure P]
    {s A : Set Tree} (hs : MeasurableSet s) :
    (P[|s]).real A = P.real (s ∩ A) / P.real s := by
  simp only [measureReal_def, cond_apply hs, ENNReal.toReal_mul, ENNReal.toReal_inv,
    div_eq_mul_inv, mul_comm]

private theorem eventually_shift_lt {η δ : ℝ} (_hη : 0 < η) (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop, 1 / (η * n) < (δ / 2) / (n : ℝ) ^ (1 / 4 : ℝ) := by
  have h0t := ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 3 / 4)).comp
    tendsto_natCast_atTop_atTop).div_const η
  have h : Tendsto (fun n : ℕ => (n : ℝ) ^ (-(3 / 4 : ℝ)) / η) atTop (𝓝 0) := by simpa using h0t
  have ht : Tendsto (fun n : ℕ => (n : ℝ) ^ (1 / 4 : ℝ) / (η * n)) atTop (𝓝 0) := by
    apply h.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have he : (n : ℝ) ^ (-(3 / 4 : ℝ)) = (n : ℝ) ^ (1 / 4 : ℝ) / n := by
      calc _ = (n : ℝ) ^ ((1 / 4 : ℝ) - 1) := by norm_num
           _ = _ := by rw [Real.rpow_sub hn0, Real.rpow_one]
    rw [he]
    ring
  filter_upwards [ht.eventually (eventually_lt_nhds (half_pos hδ)), eventually_ge_atTop 1] with n hn hn1
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  rw [lt_div_iff₀ (Real.rpow_pos_of_pos hn0 _)]
  simpa [div_eq_mul_inv, mul_comm] using hn

/-- Lemma 2.5(ii), using only the stated polynomial lower bound on the size mass. -/
theorem lem_GdesDev_tree_of_lower (μ : PMF ℕ) (h0 : μ 0 ≠ 0) (h1 : μ 0 ≠ 1) {η δ : ℝ}
    (hη0 : 0 < η) (hη1 : η < 1) (hδ : 0 < δ) (A : ℝ) (N : ℕ)
    (hlow : ∀ n : ℕ, N ≤ n → bienaymeLaw μ.toMeasure (sizeEvent n) ≠ 0 →
      (n : ℝ) ^ (-A) ≤ (bienaymeLaw μ.toMeasure).real (sizeEvent n)) :
    IsOe (1 / 2) fun n : ℕ =>
      (((bienaymeLaw μ.toMeasure)[|sizeEvent n]).real
        (finiteTreeEvent fun t =>
          ENNReal.ofReal (δ / (n : ℝ) ^ (1 / 4 : ℝ)) ≤
            supDev η (treeLeafDev (μ 0).toReal t n))) := by
  let P := bienaymeLaw μ.toMeasure
  let W := Measure.infinitePi fun _ : ℕ => μ.toMeasure
  let Q := fun (n : ℕ) (t : PlaneTree) =>
    ENNReal.ofReal (δ / (n : ℝ) ^ (1 / 4 : ℝ)) ≤ supDev η (treeLeafDev (μ 0).toReal t n)
  let E := fun n : ℕ => {ω : ℕ → ℕ | ENNReal.ofReal ((δ / 2) / (n : ℝ) ^ (1 / 4 : ℝ)) <
    supDev η (walkLeafDev (μ 0).toReal ω n)}
  have hw := WalkDeviation.lem_GdesDev_walk μ h0 h1 hη0 hη1 (half_pos hδ)
  obtain ⟨C, c, hC, hc, hb⟩ := OeLemmas.IsOe.poly_mul (by norm_num) hw A
  apply WalkDeviation.isOe_of_eventually_bound (by norm_num)
    (fun n => cond_real_le_one P _ _) hC hc
  filter_upwards [eventually_shift_lt hη0 hδ, eventually_ge_atTop (max N 1)] with n hsh hn
  have hn1 : 1 ≤ n := (le_max_right _ _).trans hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  change (P[|sizeEvent n]).real (finiteTreeEvent (Q n)) ≤ _
  by_cases hz : P (sizeEvent n) = 0
  · simp only [cond_eq_zero_of_meas_eq_zero hz, Measure.real, Measure.coe_zero, Pi.zero_apply,
      ENNReal.toReal_zero]
    positivity
  · have hlow' := hlow n ((le_max_left _ _).trans hn) hz
    have hnum : P.real (sizeEvent n ∩ finiteTreeEvent (Q n)) ≤ W.real (E n) := by
      rw [finiteTreeEvent_inter_size]
      have hlaw := congrArg ENNReal.toReal (WalkDeviation.tree_law_eq_walk_law μ
        (fun t => t.size = n ∧ Q n t))
      change P.real (finiteTreeEvent (fun t => t.size = n ∧ Q n t)) = _ at hlaw
      rw [hlaw]
      apply measureReal_mono (μ := W) _ (measure_ne_top _ _)
      rintro ω ⟨t, ⟨ht, hbad⟩, hω⟩
      exact tree_bad_implies_walk_bad _ _ _ hη0 hδ hn1 hsh t ht ω hω hbad
    rw [cond_real_eq_div P (measurableSet_sizeEvent n)]
    calc P.real (sizeEvent n ∩ finiteTreeEvent (Q n)) / P.real (sizeEvent n)
        ≤ W.real (E n) / (n : ℝ) ^ (-A) :=
          div_le_div₀ measureReal_nonneg hnum (Real.rpow_pos_of_pos hn0 _) hlow'
      _ = (n : ℝ) ^ A * W.real (E n) := by simp only [Real.rpow_neg hn0.le, div_eq_mul_inv, inv_inv]; ring
      _ ≤ C * Real.exp (-c * (n : ℝ) ^ (1 / 2 : ℝ)) := hb n

/-- A finite-tree event conditioned on a size tail is a subprobability mixture of its size laws. -/
private theorem finiteTreeEvent_cond_sizeGe_le (P : Measure Tree) [IsFiniteMeasure P]
    (n : ℕ) (Q : PlaneTree → Prop) {B : ℝ} (hB : 0 ≤ B)
    (h : ∀ k : ℕ, n ≤ k → (P[|sizeEvent k]).real (finiteTreeEvent Q) ≤ B) :
    (P[|sizeGeEvent n]).real (finiteTreeEvent Q) ≤ B := by
  let A := finiteTreeEvent Q
  let S := sizeGeEvent n
  by_cases hz : P S = 0
  · change (P[|S]).real A ≤ B
    simpa only [cond_eq_zero_of_meas_eq_zero hz, measureReal_def, Measure.coe_zero, Pi.zero_apply,
      ENNReal.toReal_zero] using hB
  have hpart : S ∩ A = ⋃ j : ℕ, sizeEvent (n + j) ∩ A := by
    ext T
    constructor
    · rintro ⟨hs, t, rfl, ht⟩
      have hsize : n ≤ t.size := by
        rcases hs with hinf | hsize
        · exact False.elim (hinf t.finiteVertices_toLocallyFinite)
        · simpa [ncard_present_toLocallyFinite] using hsize
      obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_le hsize
      exact Set.mem_iUnion.2 ⟨j, (toLocallyFinite_mem_sizeEvent_iff t (n + j)).2 hj, t, rfl, ht⟩
    · intro hm
      obtain ⟨j, hs, ha⟩ := Set.mem_iUnion.1 hm
      refine ⟨Or.inr ?_, ha⟩
      rw [hs.2]
      omega
  have hdisj : Pairwise (fun i j : ℕ => Disjoint (sizeEvent (n + i)) (sizeEvent (n + j))) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro T hi hj
    apply hij
    have := hi.2
    have := hj.2
    omega
  have hmass : ∑' j : ℕ, P (sizeEvent (n + j)) ≤ P S := by
    rw [← measure_iUnion hdisj (fun j => measurableSet_sizeEvent (n + j))]
    apply measure_mono
    intro T hT
    obtain ⟨j, hj⟩ := Set.mem_iUnion.1 hT
    exact Or.inr (by have := hj.2; change n ≤ {u | Present T u}.ncard; omega)
  have hpiece : ∀ j : ℕ, P (sizeEvent (n + j) ∩ A) ≤ ENNReal.ofReal B * P (sizeEvent (n + j)) := by
    intro j
    by_cases hj : P (sizeEvent (n + j)) = 0
    · simp [hj, measure_inter_null_of_null_left]
    · have := cond_isProbabilityMeasure (μ := P) hj
      have hc : (P[|sizeEvent (n + j)]) A ≤ ENNReal.ofReal B :=
        (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) hB).2 (h (n + j) (by omega))
      rw [← cond_mul_eq_inter (measurableSet_sizeEvent (n + j)) A P]
      gcongr
  have hnum : P (S ∩ A) ≤ ENNReal.ofReal B * P S := by
    rw [hpart]
    calc P (⋃ j : ℕ, sizeEvent (n + j) ∩ A) ≤ ∑' j : ℕ, P (sizeEvent (n + j) ∩ A) := measure_iUnion_le _
      _ ≤ ∑' j : ℕ, ENNReal.ofReal B * P (sizeEvent (n + j)) := ENNReal.tsum_le_tsum hpiece
      _ = ENNReal.ofReal B * ∑' j : ℕ, P (sizeEvent (n + j)) := ENNReal.tsum_mul_left
      _ ≤ ENNReal.ofReal B * P S := by gcongr
  apply ENNReal.toReal_le_of_le_ofReal hB
  change (P[|S]) A ≤ ENNReal.ofReal B
  rw [cond_apply' (finiteTreeEvent_measurable Q) P]
  calc (P S)⁻¹ * P (S ∩ A) ≤ (P S)⁻¹ * (ENNReal.ofReal B * P S) := by gcongr
    _ = ENNReal.ofReal B := by
      rw [mul_comm (ENNReal.ofReal B), ENNReal.inv_mul_cancel_left hz (measure_ne_top _ _)]

private theorem critical_zero_ne_one {μ : PMF ℕ} (hc : IsCritical μ) : μ 0 ≠ 1 := by
  intro h
  have hsupp := (PMF.apply_eq_one_iff μ 0).1 h
  have hz : ∀ j : ℕ, j ≠ 0 → μ j = 0 := fun j hj => by
    by_contra hne
    have : j ∈ μ.support := (PMF.mem_support_iff μ j).2 hne
    rw [hsupp] at this
    exact hj (by simpa using this)
  have hsum : ∑' j : ℕ, (j : ℝ≥0∞) * μ j = 0 := by
    have hh : ∀ j : ℕ, (j : ℝ≥0∞) * μ j = 0 := by
      intro j
      by_cases hj : j = 0
      · simp [hj]
      · simp [hz j hj]
    simp [hh]
  exact zero_ne_one (hsum.symm.trans hc)

/-- Corollary 2.6: the size-tail conditional law inherits the same concentration exponent. -/
theorem cor_GD2mieux {μ : PMF ℕ} {θ : ℝ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hap : Aperiodic μ) (hDA : ∃ b, StableDomain μ θ b) {η δ : ℝ}
    (hη0 : 0 < η) (hη1 : η < 1) (hδ : 0 < δ) :
    IsOe (1 / 2) fun n : ℕ =>
      (((bienaymeLaw μ.toMeasure)[|sizeGeEvent n]).real
        (finiteTreeEvent fun t =>
          ENNReal.ofReal (δ / (n : ℝ) ^ (1 / 4 : ℝ)) ≤
            supDev η (treeLeafDev (μ 0).toReal t (t.size : ℝ)))) := by
  obtain ⟨N, hN⟩ := SizeLower.sizeProb_poly_lower hc hne hap hDA
  have h0 := hc.apply_zero_ne_zero hne
  have h1 := critical_zero_ne_one hc
  obtain ⟨C, c, hC, hcp, hb⟩ := lem_GdesDev_tree_of_lower μ h0 h1 hη0 hη1 hδ
    (1 / θ + 2) N (fun n hn _ => hN n hn)
  let P := bienaymeLaw μ.toMeasure
  let Q := fun (n : ℕ) (t : PlaneTree) =>
    ENNReal.ofReal (δ / (n : ℝ) ^ (1 / 4 : ℝ)) ≤
      supDev η (treeLeafDev (μ 0).toReal t (t.size : ℝ))
  apply WalkDeviation.isOe_of_eventually_bound (by norm_num)
    (fun n => cond_real_le_one P _ _) hC hcp
  filter_upwards [eventually_ge_atTop 1] with n hn
  change (P[|sizeGeEvent n]).real (finiteTreeEvent (Q n)) ≤ _
  apply finiteTreeEvent_cond_sizeGe_le P n (Q n) (by positivity)
  intro k hnk
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hnk' : (n : ℝ) ≤ k := by exact_mod_cast hnk
  have hth : δ / (k : ℝ) ^ (1 / 4 : ℝ) ≤ δ / (n : ℝ) ^ (1 / 4 : ℝ) :=
    div_le_div_of_nonneg_left hδ.le (Real.rpow_pos_of_pos hn0 _)
      (Real.rpow_le_rpow hn0.le hnk' (by norm_num))
  have hsub : sizeEvent k ∩ finiteTreeEvent (Q n) ⊆
      sizeEvent k ∩ finiteTreeEvent (fun t =>
        ENNReal.ofReal (δ / (k : ℝ) ^ (1 / 4 : ℝ)) ≤ supDev η (treeLeafDev (μ 0).toReal t k)) := by
    rintro T ⟨hs, t, rfl, ht⟩
    have htk := (toLocallyFinite_mem_sizeEvent_iff t k).1 hs
    refine ⟨hs, t, rfl, ?_⟩
    have ht' : ENNReal.ofReal (δ / (n : ℝ) ^ (1 / 4 : ℝ)) ≤
        supDev η (treeLeafDev (μ 0).toReal t k) := by simpa only [Q, htk] using ht
    exact (ENNReal.ofReal_le_ofReal hth).trans ht'
  have hcond : (P[|sizeEvent k]).real (finiteTreeEvent (Q n)) ≤
      C * Real.exp (-c * (k : ℝ) ^ (1 / 2 : ℝ)) := by
    rw [cond_real_eq_div P (measurableSet_sizeEvent k)]
    calc _ ≤ P.real (sizeEvent k ∩ finiteTreeEvent (fun t =>
          ENNReal.ofReal (δ / (k : ℝ) ^ (1 / 4 : ℝ)) ≤ supDev η (treeLeafDev (μ 0).toReal t k))) /
          P.real (sizeEvent k) :=
            div_le_div_of_nonneg_right (measureReal_mono (μ := P) hsub (measure_ne_top _ _)) measureReal_nonneg
      _ ≤ _ := by rw [← cond_real_eq_div P (measurableSet_sizeEvent k)]; exact hb k
  refine hcond.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hC.le)
  have hpow := Real.rpow_le_rpow (Nat.cast_nonneg n) hnk' (by norm_num : (0 : ℝ) ≤ 1 / 2)
  nlinarith

end BGWLeaves.LeafConcentration.TreeDeviation
