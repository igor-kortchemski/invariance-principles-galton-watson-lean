module

public import BGWLeaves.Conditioning.Defs

/-!
# M6 provider `Basics`

Provider for measurability of the lifted functionals, the bridges `psi_one`, `psiStar_one` to the one-tree objects, `forestLaw_infinite_null`, `sizeGeEvent_ne_zero`, `leafGeEvent_ne_zero`, `leafCutoff_surjective`.  The theorems to be proved here are the registered holes of
`BGWLeaves.Conditioning`; they are exported in namespace `BGWLeaves.Conditioning.Basics` with exactly the types of the
statements file.
-/

@[expose] public section

namespace BGWLeaves.Conditioning.Basics

open MeasureTheory ProbabilityTheory Filter Asymptotics BGW
open BGW.StableTrees BGW.LocallyFinite BGWLeaves.StableAnalysis
open scoped ENNReal Topology

/-! ## Measurability of the lifts -/

theorem measurable_finiteTreeLift (g : PlaneTree → ℝ≥0∞) : Measurable (finiteTreeLift g) := by
  have hsing : ∀ t : PlaneTree, MeasurableSet ({t.toLocallyFinite} : Set LocallyFinite.Tree) :=
    fun t => measurableSet_singleton _
  have h : finiteTreeLift g = fun T =>
      ∑' t : PlaneTree, ({t.toLocallyFinite} : Set LocallyFinite.Tree).indicator (fun _ => g t) T := by
    funext T
    by_cases hT : ∃ t : PlaneTree, t.toLocallyFinite = T
    · obtain ⟨t0, rfl⟩ := hT
      rw [finiteTreeLift_toLocallyFinite, tsum_eq_single t0]
      · simp
      · intro t ht
        have : t.toLocallyFinite ≠ t0.toLocallyFinite := fun h =>
          ht (PlaneTree.toLocallyFinite_injective h)
        simp [Set.indicator, this.symm]
    · have h0 : finiteTreeLift g T = 0 := by
        simp only [finiteTreeLift, hT, ↓reduceDIte]
      rw [h0]
      symm
      refine ENNReal.tsum_eq_zero.2 fun t => ?_
      have : T ≠ t.toLocallyFinite := fun h => hT ⟨t, h.symm⟩
      simp [Set.indicator, this]
  rw [h]
  exact Measurable.tsum fun t => measurable_const.indicator (hsing t)

theorem measurable_finiteTreeLiftR (g : PlaneTree → ℝ) : Measurable (finiteTreeLiftR g) := by
  have h : finiteTreeLiftR g = fun T =>
      (finiteTreeLift (fun t => ENNReal.ofReal (g t)) T).toReal -
        (finiteTreeLift (fun t => ENNReal.ofReal (-g t)) T).toReal := by
    funext T
    by_cases hT : ∃ t : PlaneTree, t.toLocallyFinite = T
    · obtain ⟨t0, rfl⟩ := hT
      rw [finiteTreeLiftR_toLocallyFinite, finiteTreeLift_toLocallyFinite,
        finiteTreeLift_toLocallyFinite]
      rcases le_total 0 (g t0) with h | h
      · simp [ENNReal.toReal_ofReal h, ENNReal.ofReal_of_nonpos (neg_nonpos.2 h)]
      · simp [ENNReal.toReal_ofReal (neg_nonneg.2 h), ENNReal.ofReal_of_nonpos h]
    · have h0 : finiteTreeLiftR g T = 0 := by
        simp only [finiteTreeLiftR, hT, ↓reduceDIte]
      have h1 : ∀ f : PlaneTree → ℝ≥0∞, finiteTreeLift f T = 0 := fun f => by
        simp only [finiteTreeLift, hT, ↓reduceDIte]
      simp [h0, h1]
  rw [h]
  exact ((measurable_finiteTreeLift _).ennreal_toReal).sub
    ((measurable_finiteTreeLift _).ennreal_toReal)

/-! ## Bridges to one tree -/

private theorem forestLaw_one_apply (μ : PMF ℕ) (S : Set LocallyFinite.Tree) :
    forestLaw μ 1 ((MeasurableEquiv.funUnique (Fin 1) LocallyFinite.Tree) ⁻¹' S) =
      bienaymeLaw μ.toMeasure S := by
  have : IsProbabilityMeasure (bienaymeLaw μ.toMeasure) := inferInstance
  exact (measurePreserving_funUnique (bienaymeLaw μ.toMeasure) (Fin 1)).measure_preimage_equiv S

theorem psi_one (μ : PMF ℕ) (p : ℕ) :
    psi μ p 1 = bienaymeLaw μ.toMeasure (leafCountEvent p) := by
  rw [← forestLaw_one_apply]
  unfold psi
  congr 1
  ext F
  simp only [forestLeafCountEvent, forestEvent, leafCountEvent, finiteTreeEvent, Set.mem_iUnion,
    Set.mem_preimage, Set.mem_ofPred_eq, MeasurableEquiv.funUnique_apply]
  constructor
  · rintro ⟨q, ts, -, h2, rfl⟩
    refine ⟨ts default, rfl, ?_⟩
    simpa using h2
  · rintro ⟨t, ht, h⟩
    refine ⟨t.size, fun _ => t, by simp, by simpa using h, ?_⟩
    funext i
    rw [Subsingleton.elim i default]
    exact ht.symm

theorem psiStar_one (μ : PMF ℕ) (p : ℕ) :
    psiStar μ p 1 = bienaymeLaw μ.toMeasure (leafGeEvent p) := by
  rw [← forestLaw_one_apply]
  unfold psiStar
  congr 1
  ext F
  simp only [forestLeafGeEvent, forestEvent, leafGeEvent, finiteTreeEvent,
    Set.mem_preimage, Set.mem_ofPred_eq, MeasurableEquiv.funUnique_apply]
  constructor
  · rintro ⟨q, m', hm, ts, -, h2, rfl⟩
    refine ⟨ts default, rfl, ?_⟩
    have : ∑ i, (ts i).degreeCount 0 = (ts default).degreeCount 0 := by simp
    omega
  · rintro ⟨t, ht, h⟩
    refine ⟨t.size, t.degreeCount 0, h, fun _ => t, by simp, by simp, ?_⟩
    funext i
    rw [Subsingleton.elim i default]
    exact ht.symm

theorem forestLaw_infinite_null {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1) (j : ℕ) :
    forestLaw μ j {F | ∃ i, ¬ FiniteVertices (F i)} = 0 := by
  have hm : ∫⁻ k : ℕ, (k : ℝ≥0∞) ∂μ.toMeasure ≤ 1 := by
    have : ∫⁻ k : ℕ, (k : ℝ≥0∞) ∂μ.toMeasure = ∑' k : ℕ, (k : ℝ≥0∞) * μ k := by
      rw [lintegral_countable']
      refine tsum_congr fun k => ?_
      rw [PMF.toMeasure_apply_singleton μ k (measurableSet_singleton _)]
    rw [this]; exact hc.le
  have hne' : μ.toMeasure {1} ≠ 1 := by
    rwa [PMF.toMeasure_apply_singleton μ 1 (measurableSet_singleton _)]
  have hae := ae_finiteVertices_bienaymeLaw μ.toMeasure hm hne'
  have h2 : ∀ᵐ F ∂(forestLaw μ j), ∀ i, FiniteVertices (F i) := by
    rw [ae_all_iff]
    intro i
    exact (Measure.tendsto_eval_ae_ae (μ := fun _ : Fin j => bienaymeLaw μ.toMeasure) (i := i)).eventually hae
  rw [← compl_compl {F : Fin j → LocallyFinite.Tree | ∃ i, ¬ FiniteVertices (F i)}] 
  simpa [ae_iff] using h2

/-! ## Positivity of the tails (spine trees) -/

private theorem degrees_spine (t : PlaneTree) (r : ℕ) :
    (PlaneTree.node (t :: List.replicate r PlaneTree.leaf)).degrees =
      (r + 1) :: (t.degrees ++ List.replicate r 0) := by
  have hl : PlaneTree.leaf.degrees = [0] := by simp [PlaneTree.leaf]
  have : ∀ r : ℕ, (List.replicate r [0]).flatten = List.replicate r (0 : ℕ) := by
    intro r
    induction r with
    | zero => simp
    | succ r ih => simp [List.replicate_succ, ih]
  simp [PlaneTree.degrees_node, hl, this]

private theorem exists_spine {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1) (m : ℕ) :
    ∃ t : PlaneTree, (∀ d ∈ t.degrees, μ d ≠ 0) ∧ m ≤ t.degreeCount 0 := by
  obtain ⟨k, hk2, hk⟩ := hc.exists_two_le_ne_zero hne
  have h0 := hc.apply_zero_ne_zero hne
  induction m with
  | zero => exact ⟨PlaneTree.leaf, by simp [PlaneTree.leaf, h0], Nat.zero_le _⟩
  | succ m ih =>
    obtain ⟨t, ht, hm⟩ := ih
    obtain ⟨r, rfl⟩ : ∃ r, k = r + 2 := ⟨k - 2, by omega⟩
    refine ⟨PlaneTree.node (t :: List.replicate (r + 1) PlaneTree.leaf), ?_, ?_⟩
    · intro d hd
      rw [degrees_spine] at hd
      rcases List.mem_cons.1 hd with rfl | hd
      · exact hk
      · rcases List.mem_append.1 hd with hd | hd
        · exact ht d hd
        · rw [(List.eq_of_mem_replicate hd)]; exact h0
    · rw [PlaneTree.degreeCount, degrees_spine, List.count_cons, List.count_append,
        List.count_replicate_self]
      have : t.degreeCount 0 = t.degrees.count 0 := rfl
      omega

private theorem spine_atom_ne_zero {μ : PMF ℕ} {t : PlaneTree} (ht : ∀ d ∈ t.degrees, μ d ≠ 0) :
    bienaymeLaw μ.toMeasure {t.toLocallyFinite} ≠ 0 := by
  rw [bienaymeLaw_toLocallyFinite, PlaneTree.weight_ne_zero_iff]
  intro d hd
  rw [PMF.toMeasure_apply_singleton μ d (measurableSet_singleton _)]
  exact ht d hd

theorem sizeGeEvent_ne_zero {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1) (n : ℕ) :
    bienaymeLaw μ.toMeasure (sizeGeEvent n) ≠ 0 := by
  obtain ⟨t, ht, hm⟩ := exists_spine hc hne n
  have h1 := spine_atom_ne_zero ht
  refine fun h => h1 (le_antisymm ?_ zero_le)
  rw [← h]
  refine measure_mono ?_
  rintro T rfl
  right
  rw [ncard_present_toLocallyFinite]
  exact hm.trans (PlaneTree.degreeCount_le_size t 0)

theorem leafGeEvent_ne_zero {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1) (n : ℕ) :
    bienaymeLaw μ.toMeasure (leafGeEvent n) ≠ 0 := by
  obtain ⟨t, ht, hm⟩ := exists_spine hc hne n
  have h1 := spine_atom_ne_zero ht
  refine fun h => h1 (le_antisymm ?_ zero_le)
  rw [← h]
  refine measure_mono ?_
  rintro T rfl
  exact ⟨t, rfl, hm⟩

/-! ## The leaf cutoff takes every positive integer value -/

theorem leafCutoff_surjective {μ : PMF ℕ} (h0 : 0 < (μ 0).toReal) (h1 : (μ 0).toReal < 1) :
    ∀ m : ℕ, 1 ≤ m → ∃ n : ℕ, leafCutoff μ n = m := by
  intro m hm
  set a : ℝ := (μ 0).toReal with ha
  have hex : ∃ n, m ≤ leafCutoff μ n := by
    obtain ⟨N, hN⟩ := exists_nat_ge (max (2 / a) (m : ℝ))
    have hN1 : 2 / a ≤ N := (le_max_left _ _).trans hN
    have hN2 : (m : ℝ) ≤ N := (le_max_right _ _).trans hN
    have haN : 2 ≤ a * N := by
      have := (div_le_iff₀ h0).1 hN1
      linarith
    have hNpos : (0 : ℝ) ≤ N := by positivity
    refine ⟨N ^ 4, ?_⟩
    unfold leafCutoff
    have hr : (((N ^ 4 : ℕ) : ℝ)) ^ (3 / 4 : ℝ) = (N : ℝ) ^ 3 := by
      rw [Nat.cast_pow, ← Real.rpow_natCast, ← Real.rpow_mul hNpos]
      norm_num
    rw [hr, ← ha]
    refine Nat.cast_le.1 ((?_ : (m : ℝ) ≤ _).trans (Nat.le_ceil _))
    have hN1' : (1 : ℝ) ≤ N := (by exact_mod_cast hm : (1 : ℝ) ≤ m).trans hN2
    push_cast
    have e1 : a * (N : ℝ) ^ 4 - (N : ℝ) ^ 3 = (N : ℝ) ^ 3 * (a * N - 1) := by ring
    have e2 : (N : ℝ) ^ 3 * 1 ≤ (N : ℝ) ^ 3 * (a * N - 1) :=
      mul_le_mul_of_nonneg_left (by linarith) (pow_nonneg hNpos 3)
    have e3 : (N : ℝ) ≤ (N : ℝ) ^ 3 := by nlinarith [mul_nonneg hNpos hNpos]
    linarith
  classical
  have hn0 : m ≤ leafCutoff μ (Nat.find hex) := Nat.find_spec hex
  have hz : leafCutoff μ 0 = 0 := by simp [leafCutoff]
  have hn0pos : Nat.find hex ≠ 0 := by
    intro h
    rw [h, hz] at hn0
    omega
  obtain ⟨k, hk⟩ : ∃ k, Nat.find hex = k + 1 := Nat.exists_eq_succ_of_ne_zero hn0pos
  have hlt : ¬ m ≤ leafCutoff μ k := Nat.find_min hex (by omega)
  rw [hk] at hn0
  have hstep : leafCutoff μ (k + 1) ≤ leafCutoff μ k + 1 := by
    unfold leafCutoff
    rw [← ha]
    refine Nat.ceil_le.2 ?_
    have h1 : (k : ℝ) ^ (3 / 4 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) ^ (3 / 4 : ℝ) :=
      Real.rpow_le_rpow (Nat.cast_nonneg _) (by push_cast; linarith) (by norm_num)
    have h2 := Nat.le_ceil (a * k - (k : ℝ) ^ (3 / 4 : ℝ))
    push_cast at h1 ⊢
    nlinarith
  exact ⟨k + 1, by omega⟩

end BGWLeaves.Conditioning.Basics
