module

public import BGWLeaves.Vervaat.Defs
import BGW.StableTrees.CriticalSupport
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# The displayed law and the uniform trees (7.3)

Proofs for the displayed law and the uniform trees (7.3).  The theorems are those stated in
`BGWLeaves.Vervaat`; they are exported in namespace `BGWLeaves.Vervaat.UniformTree` with exactly the types
stated there.
-/

@[expose] public section

namespace BGWLeaves.Vervaat.UniformTree

open MeasureTheory ProbabilityTheory Filter BGW
open BGW.StableTrees BGW.LocallyFinite BGWLeaves.StableAnalysis
open scoped ENNReal Topology

/-! ## Real weights `geomW z q` and their series -/

/-- `w 0 = z`, `w 1 = 0`, `w (i+2) = q^(i+1)`. -/
private def geomW (z q : ℝ) : ℕ → ℝ
  | 0 => z
  | 1 => 0
  | i + 2 => q ^ (i + 1)

private theorem geomW_nonneg {z q : ℝ} (hz : 0 ≤ z) (hq : 0 ≤ q) (i : ℕ) : 0 ≤ geomW z q i := by
  rcases i with _ | _ | i
  · simpa [geomW] using hz
  · simp [geomW]
  · simpa [geomW] using pow_nonneg hq _

private theorem hasSum_geom_shift {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    HasSum (fun i : ℕ => q ^ (i + 1)) (q / (1 - q)) := by
  have := (hasSum_geometric_of_lt_one hq0 hq1).mul_left q
  convert this using 1
  · ext i; ring
  · rw [div_eq_mul_inv]

private theorem hasSum_geomW {z q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    HasSum (geomW z q) (z + q / (1 - q)) := by
  rw [← hasSum_nat_add_iff' 2]
  convert hasSum_geom_shift hq0 hq1 using 1
  · ext i; simp [geomW]
  · simp [Finset.sum_range_succ, geomW]

private theorem hasSum_geomW_mean {z q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    HasSum (fun j : ℕ => (j : ℝ) * geomW z q j) (1 / (1 - q) ^ 2 - 1) := by
  have hA : HasSum (fun n : ℕ => (n : ℝ) * q ^ n) (q / (1 - q) ^ 2) :=
    hasSum_coe_mul_geometric_of_norm_lt_one (by rwa [Real.norm_of_nonneg hq0])
  have hA' : HasSum (fun i : ℕ => ((i + 1 : ℕ) : ℝ) * q ^ (i + 1)) (q / (1 - q) ^ 2) := by
    have := (hasSum_nat_add_iff' 1).2 hA
    simpa using this
  have hC := hA'.add (hasSum_geom_shift hq0 hq1)
  rw [← hasSum_nat_add_iff' 2]
  have h1q : (1 - q) ≠ 0 := by linarith
  convert hC using 1
  · ext i; simp [geomW]; ring
  · simp [Finset.sum_range_succ, geomW]
    field_simp
    ring

/-! ## The displayed constants -/

private theorem sqrt2_sq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)

private theorem sqrt2_lt : Real.sqrt 2 < 2 := by
  have h := sqrt2_sq
  nlinarith [Real.sqrt_nonneg 2]

private theorem sqrt2_gt : 1 < Real.sqrt 2 := by
  have h := sqrt2_sq
  nlinarith [Real.sqrt_nonneg 2]

private theorem q0_pos : 0 < (2 - Real.sqrt 2) / 2 := by linarith [sqrt2_lt]

private theorem q0_lt : (2 - Real.sqrt 2) / 2 < 1 := by linarith [sqrt2_gt]

private theorem z0_pos : 0 < 2 - Real.sqrt 2 := by linarith [sqrt2_lt]

private theorem one_sub_q0 : 1 - (2 - Real.sqrt 2) / 2 = Real.sqrt 2 / 2 := by ring

private theorem sum_z0 : (2 - Real.sqrt 2) + (2 - Real.sqrt 2) / 2 / (1 - (2 - Real.sqrt 2) / 2) = 1 := by
  rw [one_sub_q0]
  have := sqrt2_sq
  have hpos : 0 < Real.sqrt 2 := by linarith [sqrt2_gt]
  field_simp
  nlinarith

private theorem mean_q0 : 1 / (1 - (2 - Real.sqrt 2) / 2) ^ 2 - 1 = 1 := by
  rw [one_sub_q0]
  have := sqrt2_sq
  have hpos : 0 < Real.sqrt 2 := by linarith [sqrt2_gt]
  field_simp
  nlinarith

private theorem displayedWeight_eq (i : ℕ) :
    displayedWeight i = ENNReal.ofReal (geomW (2 - Real.sqrt 2) ((2 - Real.sqrt 2) / 2) i) := by
  rcases i with _ | _ | i <;> simp [displayedWeight, geomW]

private theorem displayed_apply {μ : PMF ℕ} (hμ : IsDisplayedLaw μ) (i : ℕ) :
    μ i = ENNReal.ofReal (geomW (2 - Real.sqrt 2) ((2 - Real.sqrt 2) / 2) i) := by
  rw [hμ i, displayedWeight_eq]

private theorem displayed_toReal {μ : PMF ℕ} (hμ : IsDisplayedLaw μ) (i : ℕ) :
    (μ i).toReal = geomW (2 - Real.sqrt 2) ((2 - Real.sqrt 2) / 2) i := by
  rw [displayed_apply hμ, ENNReal.toReal_ofReal
    (geomW_nonneg z0_pos.le q0_pos.le i)]

theorem exists_displayedLaw : ∃ μ : PMF ℕ, IsDisplayedLaw μ := by
  have hs := hasSum_geomW (z := 2 - Real.sqrt 2) q0_pos.le q0_lt
  rw [sum_z0] at hs
  have hnn := geomW_nonneg (z := 2 - Real.sqrt 2) (q := (2 - Real.sqrt 2) / 2) z0_pos.le q0_pos.le
  have h1 : ∑' i, displayedWeight i = 1 := by
    simp_rw [displayedWeight_eq]
    rw [← ENNReal.ofReal_tsum_of_nonneg hnn hs.summable, hs.tsum_eq]
    simp
  exact ⟨⟨displayedWeight, h1 ▸ ENNReal.summable.hasSum⟩, fun i => rfl⟩

theorem displayedLaw_critical {μ : PMF ℕ} (hμ : IsDisplayedLaw μ) : IsCritical μ := by
  have hs := hasSum_geomW_mean (z := 2 - Real.sqrt 2) q0_pos.le q0_lt
  rw [mean_q0] at hs
  have hnn : ∀ j : ℕ, 0 ≤ (j : ℝ) * geomW (2 - Real.sqrt 2) ((2 - Real.sqrt 2) / 2) j :=
    fun j => mul_nonneg (Nat.cast_nonneg _) (geomW_nonneg z0_pos.le q0_pos.le j)
  unfold IsCritical
  have : ∀ j : ℕ, (j : ℝ≥0∞) * μ j =
      ENNReal.ofReal ((j : ℝ) * geomW (2 - Real.sqrt 2) ((2 - Real.sqrt 2) / 2) j) := by
    intro j
    rw [displayed_apply hμ, ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
  simp_rw [this]
  rw [← ENNReal.ofReal_tsum_of_nonneg hnn hs.summable, hs.tsum_eq]
  simp

theorem displayedLaw_two {μ : PMF ℕ} (hμ : IsDisplayedLaw μ) :
    (μ 2).toReal = 1 / bConst := by
  rw [displayed_toReal hμ]
  simp only [geomW, zero_add, pow_one, bConst]
  have := sqrt2_sq
  have hpos : 0 < Real.sqrt 2 := by linarith [sqrt2_gt]
  field_simp
  nlinarith

private theorem summable_sq_geomW :
    Summable (fun k : ℕ => (((k : ℝ) - 1) ^ 2) *
      geomW (2 - Real.sqrt 2) ((2 - Real.sqrt 2) / 2) k) := by
  have hg : Summable (fun n : ℕ => (n : ℝ) ^ 2 * ((2 - Real.sqrt 2) / 2) ^ n) :=
    summable_pow_mul_geometric_of_norm_lt_one 2 (by rw [Real.norm_of_nonneg q0_pos.le]; exact q0_lt)
  have h1 := (summable_nat_add_iff 1).2 hg
  rw [← summable_nat_add_iff 2]
  convert h1 using 1
  ext i
  simp only [geomW]
  push_cast
  ring

theorem displayedLaw_hypotheses {μ : PMF ℕ} (hμ : IsDisplayedLaw μ) :
    IsCritical μ ∧ μ 1 ≠ 1 ∧ Aperiodic μ ∧
      Integrable (fun z : ℤ => (z : ℝ) ^ 2) (stepLaw μ) := by
  refine ⟨displayedLaw_critical hμ, ?_, ?_, ?_⟩
  · rw [hμ 1]; simp [displayedWeight]
  · have h2 : μ 2 ≠ 0 := by
      rw [displayed_apply hμ]
      simp [geomW]
    have h3 : μ 3 ≠ 0 := by
      rw [displayed_apply hμ]
      simp [geomW]
      exact z0_pos.ne'
    have m2 : ((2 : ℕ) : ℤ) ∈ AddSubgroup.closure (((↑) : ℕ → ℤ) '' {j : ℕ | μ j ≠ 0}) :=
      AddSubgroup.subset_closure ⟨2, h2, rfl⟩
    have m3 : ((3 : ℕ) : ℤ) ∈ AddSubgroup.closure (((↑) : ℕ → ℤ) '' {j : ℕ | μ j ≠ 0}) :=
      AddSubgroup.subset_closure ⟨3, h3, rfl⟩
    have m1 : (1 : ℤ) ∈ AddSubgroup.closure (((↑) : ℕ → ℤ) '' {j : ℕ | μ j ≠ 0}) := by
      have := sub_mem m3 m2
      simpa using this
    unfold Aperiodic
    rw [eq_top_iff]
    intro z _
    have := AddSubgroup.zsmul_mem _ m1 z
    simpa using this
  · unfold stepLaw
    have hf : Measurable (fun k : ℕ => (k : ℤ) - 1) := measurable_of_countable _
    rw [integrable_map_measure (measurable_of_countable _).aestronglyMeasurable hf.aemeasurable]
    refine ⟨(measurable_of_countable _).aestronglyMeasurable, ?_⟩
    unfold HasFiniteIntegral
    rw [lintegral_countable']
    have hterm : ∀ k : ℕ, ‖((fun z : ℤ => (z : ℝ) ^ 2) ∘ fun k : ℕ => (k : ℤ) - 1) k‖ₑ *
        μ.toMeasure {k} = ENNReal.ofReal ((((k : ℝ) - 1) ^ 2) *
          geomW (2 - Real.sqrt 2) ((2 - Real.sqrt 2) / 2) k) := by
      intro k
      rw [PMF.toMeasure_apply_singleton μ k (measurableSet_singleton _), displayed_apply hμ,
        ← ofReal_norm, ← ENNReal.ofReal_mul (norm_nonneg _)]
      congr 1
      simp [Function.comp]
    simp_rw [hterm]
    rw [← ENNReal.ofReal_tsum_of_nonneg
      (fun k => mul_nonneg (sq_nonneg _) (geomW_nonneg z0_pos.le q0_pos.le k)) summable_sq_geomW]
    exact ENNReal.ofReal_lt_top

/-! ## Weights of finite trees -/

private theorem atom_eq (μ : PMF ℕ) (t : PlaneTree) :
    bienaymeLaw μ.toMeasure {t.toLocallyFinite} = (t.degrees.map fun d => μ d).prod := by
  rw [bienaymeLaw_toLocallyFinite]
  unfold PlaneTree.weight
  congr 2
  ext d
  exact PMF.toMeasure_apply_singleton μ d (measurableSet_singleton _)

private theorem list_two_le (L : List ℕ) (h : 1 ∉ L) : 2 * (L.length - L.count 0) ≤ L.sum := by
  induction L with
  | nil => simp
  | cons a L ih =>
    have h1 : a ≠ 1 := fun e => h (by simp [e])
    have h2 : 1 ∉ L := fun e => h (List.mem_cons_of_mem _ e)
    have := ih h2
    have hc : L.count 0 ≤ L.length := List.count_le_length
    rw [List.count_cons, List.sum_cons, List.length_cons]
    by_cases ha : a = 0
    · subst ha; simp; omega
    · have : 2 ≤ a := by omega
      simp [ha]; omega

private theorem list_prod_geomW {z q : ℝ} (L : List ℕ) (h : 1 ∉ L) :
    (L.map (geomW z q)).prod * q ^ L.length = z ^ L.count 0 * q ^ (L.sum + L.count 0) := by
  induction L with
  | nil => simp
  | cons a L ih =>
    have h1 : a ≠ 1 := fun e => h (by simp [e])
    have h2 : 1 ∉ L := fun e => h (List.mem_cons_of_mem _ e)
    have := ih h2
    rw [List.map_cons, List.prod_cons, List.length_cons, List.sum_cons]
    rcases a with _ | _ | i
    · rw [List.count_cons_self]
      simp only [geomW]
      calc _ = z * ((L.map (geomW z q)).prod * q ^ L.length) * q := by ring
        _ = _ := by rw [this]; ring
    · exact absurd rfl h1
    · rw [List.count_cons_of_ne (by omega)]
      simp only [geomW]
      calc _ = q ^ (i + 1) * ((L.map (geomW z q)).prod * q ^ L.length) * q := by ring
        _ = _ := by rw [this]; ring

private theorem ofReal_list_prod {f : ℕ → ℝ} (hf : ∀ i, 0 ≤ f i) (L : List ℕ) :
    (L.map fun d => ENNReal.ofReal (f d)).prod = ENNReal.ofReal ((L.map f).prod) := by
  induction L with
  | nil => simp
  | cons a L ih =>
    rw [List.map_cons, List.prod_cons, List.map_cons, List.prod_cons, ih,
      ENNReal.ofReal_mul (hf a)]

theorem displayedLaw_atom {μ : PMF ℕ} (hμ : IsDisplayedLaw μ) (t : PlaneTree) :
    bienaymeLaw μ.toMeasure {t.toLocallyFinite} =
      if 1 ∉ t.degrees then
        ENNReal.ofReal ((2 - Real.sqrt 2) ^ (t.degreeCount 0) *
          ((2 - Real.sqrt 2) / 2) ^ (t.degreeCount 0 - 1))
      else 0 := by
  rw [atom_eq]
  by_cases h' : 1 ∈ t.degrees
  · simp only [h', not_true_eq_false, ↓reduceIte]
    apply List.prod_eq_zero
    rw [List.mem_map]
    exact ⟨1, h', by rw [displayed_apply hμ]; simp [geomW]⟩
  · have h : 1 ∉ t.degrees := h'
    simp only [h, not_false_eq_true, ↓reduceIte]
    simp_rw [displayed_apply hμ]
    rw [ofReal_list_prod (geomW_nonneg z0_pos.le q0_pos.le)]
    congr 1
    have hid := list_prod_geomW (z := 2 - Real.sqrt 2) (q := (2 - Real.sqrt 2) / 2) t.degrees h
    have hlen := t.length_degrees
    have hsum := t.sum_degrees_add_one
    have hle := list_two_le t.degrees h
    have hc : t.degreeCount 0 = t.degrees.count 0 := rfl
    have hsz : 0 < t.size := t.size_pos
    have hc1 : 1 ≤ t.degrees.count 0 := by omega
    rw [hc]
    have hq : 0 < ((2 - Real.sqrt 2) / 2) ^ t.degrees.length := pow_pos q0_pos _
    have : t.degrees.sum + t.degrees.count 0 = t.degrees.length + (t.degrees.count 0 - 1) := by omega
    rw [this, pow_add] at hid
    have := mul_right_cancel₀ hq.ne' (by rw [hid]; ring :
      (t.degrees.map (geomW (2 - Real.sqrt 2) ((2 - Real.sqrt 2) / 2))).prod *
        ((2 - Real.sqrt 2) / 2) ^ t.degrees.length =
      (2 - Real.sqrt 2) ^ t.degrees.count 0 * ((2 - Real.sqrt 2) / 2) ^ (t.degrees.count 0 - 1) *
        ((2 - Real.sqrt 2) / 2) ^ t.degrees.length)
    exact this

/-! ## Witness trees -/

private def corolla (n : ℕ) : PlaneTree := PlaneTree.node (List.replicate n PlaneTree.leaf)

private theorem degrees_corolla (n : ℕ) : (corolla n).degrees = n :: List.replicate n 0 := by
  simp [corolla, PlaneTree.leaf, List.map_replicate]

/-- root with `n - 1` children, one of which has two children (`n ≥ 2`) -/
private def corolla2 (n : ℕ) : PlaneTree :=
  PlaneTree.node (PlaneTree.node [PlaneTree.leaf, PlaneTree.leaf] :: List.replicate (n - 2) PlaneTree.leaf)

private theorem degrees_corolla2 {n : ℕ} (hn : 2 ≤ n) :
    (corolla2 n).degrees = (n - 1) :: 2 :: 0 :: 0 :: List.replicate (n - 2) 0 := by
  have : (n - 2 + 1) = n - 1 := by omega
  simp [corolla2, PlaneTree.leaf, List.map_replicate, this]

private def cat : ℕ → PlaneTree
  | 0 => PlaneTree.leaf
  | n + 1 => PlaneTree.node [PlaneTree.leaf, cat n]

private theorem degrees_cat (n : ℕ) :
    (∀ d ∈ (cat n).degrees, d = 0 ∨ d = 2) ∧ (cat n).degreeCount 0 = n + 1 := by
  induction n with
  | zero => simp [cat, PlaneTree.leaf, PlaneTree.degreeCount]
  | succ n ih =>
    obtain ⟨h1, h2⟩ := ih
    have hd : (cat (n + 1)).degrees = 2 :: 0 :: (cat n).degrees := by
      simp [cat, PlaneTree.leaf]
    refine ⟨?_, ?_⟩
    · rw [hd]
      intro d hd'
      simp only [List.mem_cons] at hd'
      rcases hd' with rfl | rfl | hd'
      · simp
      · simp
      · exact h1 d hd'
    · unfold PlaneTree.degreeCount at h2 ⊢
      rw [hd, List.count_cons_of_ne (by norm_num), List.count_cons_self, h2]

private theorem measurableSet_leafCount (n : ℕ) : MeasurableSet (leafCountEvent n) := by
  apply Set.Countable.measurableSet
  refine (Set.countable_range PlaneTree.toLocallyFinite).mono ?_
  rintro T ⟨t, rfl, -⟩
  exact ⟨t, rfl⟩

theorem uniformTrees_nonempty {n : ℕ} (hn : 1 ≤ n) : (uniformTrees n).Nonempty := by
  by_cases h1 : n = 1
  · subst h1
    refine ⟨PlaneTree.leaf.toLocallyFinite, PlaneTree.leaf, rfl, ?_, ?_⟩
    · simp [PlaneTree.leaf, PlaneTree.degreeCount]
    · simp [PlaneTree.leaf]
  · refine ⟨(corolla n).toLocallyFinite, corolla n, rfl, ?_, ?_⟩
    · unfold PlaneTree.degreeCount
      rw [degrees_corolla, List.count_cons_of_ne (by omega), List.count_replicate_self]
    · simp [degrees_corolla]
      omega

theorem displayedLaw_leafProb_ne_zero {μ : PMF ℕ} (hμ : IsDisplayedLaw μ) {n : ℕ} (hn : 1 ≤ n) :
    bienaymeLaw μ.toMeasure (leafCountEvent n) ≠ 0 := by
  obtain ⟨T, t, rfl, h0, h1⟩ := uniformTrees_nonempty hn
  intro h
  have hat := displayedLaw_atom hμ t
  simp only [h1, not_false_eq_true, ↓reduceIte] at hat
  have hsub : ({t.toLocallyFinite} : Set LocallyFinite.Tree) ⊆ leafCountEvent n :=
    fun T hT => by
      rw [Set.mem_singleton_iff] at hT
      exact ⟨t, hT.symm, h0⟩
  have hz := measure_mono_null hsub h
  rw [hat] at hz
  have hpos : 0 < (2 - Real.sqrt 2) ^ t.degreeCount 0 *
      ((2 - Real.sqrt 2) / 2) ^ (t.degreeCount 0 - 1) :=
    mul_pos (pow_pos z0_pos _) (pow_pos q0_pos _)
  exact (ENNReal.ofReal_pos.2 hpos).ne' hz

private theorem uniform_of_displayed {μ : PMF ℕ} (hμ : IsDisplayedLaw μ) :
    IsUniformConditioned μ := by
  intro n hn hP
  classical
  set ν := bienaymeLaw μ.toMeasure with hν
  set s := (finite_uniformTrees n).toFinset with hs
  set c := ENNReal.ofReal ((2 - Real.sqrt 2) ^ n * ((2 - Real.sqrt 2) / 2) ^ (n - 1)) with hcdef
  have hc : c ≠ 0 := by
    rw [hcdef, Ne, ENNReal.ofReal_eq_zero, not_le]
    exact mul_pos (pow_pos z0_pos _) (pow_pos q0_pos _)
  have hctop : c ≠ ⊤ := ENNReal.ofReal_ne_top
  have hUsub : uniformTrees n ⊆ leafCountEvent n := by
    rintro T ⟨t, rfl, h0, -⟩
    exact ⟨t, rfl, h0⟩
  have hatom : ∀ T ∈ s, ν {T} = c := by
    intro T hT
    have hT' : T ∈ uniformTrees n := by simpa [s] using hT
    obtain ⟨t, rfl, h0, h1⟩ := hT'
    rw [hν, displayedLaw_atom hμ]
    simp only [h1, not_false_eq_true, ↓reduceIte]
    have : t.degreeCount 0 = n := h0
    rw [this]
  have hnull : ν (leafCountEvent n \ uniformTrees n) = 0 := by
    have hsub : leafCountEvent n \ uniformTrees n ⊆
        ⋃ t : {t : PlaneTree // 1 ∈ t.degrees}, ({t.1.toLocallyFinite} : Set LocallyFinite.Tree) := by
      rintro T ⟨⟨t, rfl, h0⟩, hT⟩
      have h1 : 1 ∈ t.degrees := by
        by_contra h1
        exact hT ⟨t, rfl, h0, h1⟩
      exact Set.mem_iUnion.2 ⟨⟨t, h1⟩, rfl⟩
    refine measure_mono_null hsub (measure_iUnion_null fun t => ?_)
    rw [hν, displayedLaw_atom hμ]
    simp [t.2]
  have hmass (A : Set LocallyFinite.Tree) :
      ν (leafCountEvent n ∩ A) = ((s.filter (fun T => T ∈ A)).card : ℝ≥0∞) * c := by
    have h1 : ν (leafCountEvent n ∩ A) = ν (uniformTrees n ∩ A) := by
      apply le_antisymm
      · calc ν (leafCountEvent n ∩ A) ≤ ν ((uniformTrees n ∩ A) ∪ (leafCountEvent n \ uniformTrees n)) := by
              apply measure_mono
              rintro T ⟨hT, hA⟩
              by_cases hU : T ∈ uniformTrees n
              · exact Or.inl ⟨hU, hA⟩
              · exact Or.inr ⟨hT, hU⟩
          _ ≤ ν (uniformTrees n ∩ A) + ν (leafCountEvent n \ uniformTrees n) := measure_union_le _ _
          _ = ν (uniformTrees n ∩ A) := by rw [hnull, add_zero]
      · exact measure_mono (Set.inter_subset_inter_left _ hUsub)
    have hset : uniformTrees n ∩ A = (↑(s.filter (fun T => T ∈ A)) : Set LocallyFinite.Tree) := by
      ext T
      simp [s]
    rw [h1, hset, ← sum_measure_singleton]
    calc ∑ T ∈ s.filter (fun T => T ∈ A), ν {T} = ∑ _T ∈ s.filter (fun T => T ∈ A), c :=
          Finset.sum_congr rfl fun T hT => hatom T (Finset.mem_filter.mp hT).1
      _ = _ := by simp
  have htotal : ν (leafCountEvent n) = (s.card : ℝ≥0∞) * c := by
    simpa using hmass Set.univ
  ext A _hA
  rw [cond_apply (measurableSet_leafCount n), htotal, hmass, Measure.uniformOfFinset_apply,
    ← ENNReal.div_eq_inv_mul]
  exact ENNReal.mul_div_mul_right _ _ hc hctop

/-! ## The converse of `rem_uniformtree_iff` -/

private theorem toLF_mem_uniform {t : PlaneTree} {n : ℕ} :
    t.toLocallyFinite ∈ uniformTrees n ↔ t.degreeCount 0 = n ∧ 1 ∉ t.degrees := by
  constructor
  · rintro ⟨t', ht', h0, h1⟩
    obtain rfl := PlaneTree.toLocallyFinite_injective ht'
    exact ⟨h0, h1⟩
  · rintro ⟨h0, h1⟩
    exact ⟨t, rfl, h0, h1⟩

private theorem toLF_mem_leaf {t : PlaneTree} {n : ℕ} :
    t.toLocallyFinite ∈ leafCountEvent n ↔ t.degreeCount 0 = n := by
  constructor
  · rintro ⟨t', ht', h0⟩
    obtain rfl := PlaneTree.toLocallyFinite_injective ht'
    exact h0
  · intro h0
    exact ⟨t, rfl, h0⟩

private theorem uniform_consequences {μ : PMF ℕ} (hU : IsUniformConditioned μ) {n : ℕ} (hn : 1 ≤ n)
    (hP : bienaymeLaw μ.toMeasure (leafCountEvent n) ≠ 0) :
    (∀ t : PlaneTree, t.degreeCount 0 = n → 1 ∈ t.degrees →
        (t.degrees.map fun d => μ d).prod = 0) ∧
    (∀ t t' : PlaneTree, t.degreeCount 0 = n → 1 ∉ t.degrees → t'.degreeCount 0 = n →
        1 ∉ t'.degrees →
        (t.degrees.map fun d => μ d).prod = (t'.degrees.map fun d => μ d).prod) := by
  classical
  set ν := bienaymeLaw μ.toMeasure with hν
  have h := hU n hn hP
  have hPtop : ν (leafCountEvent n) ≠ ⊤ := measure_ne_top _ _
  have key : ∀ t : PlaneTree, t.degreeCount 0 = n →
      ν {t.toLocallyFinite} = if t.toLocallyFinite ∈ uniformTrees n then
        ν (leafCountEvent n) * ((finite_uniformTrees n).toFinset.card : ℝ≥0∞)⁻¹ else 0 := by
    intro t ht
    have hT : t.toLocallyFinite ∈ leafCountEvent n := toLF_mem_leaf.2 ht
    have h1 : (ν[|leafCountEvent n]) {t.toLocallyFinite} =
        (Measure.uniformOfFinset (finite_uniformTrees n).toFinset) {t.toLocallyFinite} := by rw [h]
    rw [cond_apply (measurableSet_leafCount n), Set.inter_eq_right.2 (Set.singleton_subset_iff.2 hT),
      Measure.uniformOfFinset_apply_singleton] at h1
    have h2 : ν {t.toLocallyFinite} = ν (leafCountEvent n) * ((ν (leafCountEvent n))⁻¹ * ν {t.toLocallyFinite}) := by
      rw [← mul_assoc, ENNReal.mul_inv_cancel hP hPtop, one_mul]
    rw [h2, h1]
    simp [Set.Finite.mem_toFinset]
  refine ⟨fun t h0 h1 => ?_, fun t t' h0 h1 h0' h1' => ?_⟩
  · have := key t h0
    rw [hν, atom_eq] at this
    rw [this]
    have : t.toLocallyFinite ∉ uniformTrees n := fun hm => (toLF_mem_uniform.1 hm).2 h1
    simp [this]
  · have e := key t h0
    have e' := key t' h0'
    rw [hν, atom_eq] at e e'
    rw [e, e']
    simp [toLF_mem_uniform, h0, h1, h0', h1']

private theorem solve_params {z q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (hsum : z + q / (1 - q) = 1)
    (hmean : 1 / (1 - q) ^ 2 - 1 = 1) :
    q = (2 - Real.sqrt 2) / 2 ∧ z = 2 - Real.sqrt 2 := by
  have h1q : 0 < 1 - q := by linarith
  have hsq : (1 - q) ^ 2 = 1 / 2 := by
    field_simp at hmean
    linarith
  have hs := sqrt2_sq
  have hpos : 0 < Real.sqrt 2 := by linarith [sqrt2_gt]
  have hq : q = (2 - Real.sqrt 2) / 2 := by
    have : (1 - q - Real.sqrt 2 / 2) * (1 - q + Real.sqrt 2 / 2) = 0 := by nlinarith
    rcases mul_eq_zero.1 this with h | h
    · linarith
    · nlinarith
  refine ⟨hq, ?_⟩
  subst hq
  have := sum_z0
  linarith

private theorem hasSum_toReal (μ : PMF ℕ) : HasSum (fun n => (μ n).toReal) 1 := by
  have h := ENNReal.tsum_toReal_eq (fun a => μ.apply_ne_top a)
  rw [μ.tsum_coe] at h
  have hs := ENNReal.summable_toReal (f := fun a => μ a) (by rw [μ.tsum_coe]; exact ENNReal.one_ne_top)
  have : ∑' a, (μ a).toReal = 1 := by simpa using h.symm
  rw [← this]
  exact hs.hasSum

private theorem hasSum_mean_toReal {μ : PMF ℕ} (hc : IsCritical μ) :
    HasSum (fun n : ℕ => (n : ℝ) * (μ n).toReal) 1 := by
  have hne : ∀ a : ℕ, (a : ℝ≥0∞) * μ a ≠ ⊤ :=
    fun a => ENNReal.mul_ne_top (ENNReal.natCast_ne_top a) (μ.apply_ne_top a)
  have h := ENNReal.tsum_toReal_eq hne
  have hc' : ∑' a : ℕ, (a : ℝ≥0∞) * μ a = 1 := hc
  rw [hc'] at h
  have hs := ENNReal.summable_toReal (f := fun a : ℕ => (a : ℝ≥0∞) * μ a)
    (by rw [hc']; exact ENNReal.one_ne_top)
  have e : ∀ a : ℕ, ((a : ℝ≥0∞) * μ a).toReal = (a : ℝ) * (μ a).toReal := by
    intro a; simp
  simp_rw [e] at h hs
  have : ∑' a : ℕ, (a : ℝ) * (μ a).toReal = 1 := by simpa using h.symm
  rw [← this]
  exact hs.hasSum

private theorem leaf_ne_zero_of_weight {μ : PMF ℕ} {t : PlaneTree} {n : ℕ}
    (h0 : t.degreeCount 0 = n) (hw : (t.degrees.map fun d => μ d).prod ≠ 0) :
    bienaymeLaw μ.toMeasure (leafCountEvent n) ≠ 0 := by
  intro h
  have hsub : ({t.toLocallyFinite} : Set LocallyFinite.Tree) ⊆ leafCountEvent n :=
    fun T hT => by
      rw [Set.mem_singleton_iff] at hT
      exact ⟨t, hT.symm, h0⟩
  exact hw (by rw [← atom_eq]; exact measure_mono_null hsub h)

private theorem prod_corolla (μ : PMF ℕ) (n : ℕ) :
    ((corolla n).degrees.map fun d => μ d).prod = μ n * μ 0 ^ n := by
  rw [degrees_corolla]; simp [List.map_replicate]

private theorem prod_corolla2 (μ : PMF ℕ) {n : ℕ} (hn : 2 ≤ n) :
    ((corolla2 n).degrees.map fun d => μ d).prod = μ (n - 1) * μ 2 * μ 0 ^ n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  rw [degrees_corolla2 hn]
  simp only [List.map_cons, List.prod_cons, List.map_replicate, List.prod_replicate,
    Nat.add_sub_cancel, show k + 2 - 1 = k + 1 by omega]
  ring

private theorem displayed_of_uniform {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hU : IsUniformConditioned μ) : IsDisplayedLaw μ := by
  have h0 : μ 0 ≠ 0 := hc.apply_zero_ne_zero hne
  have h0top : μ 0 ≠ ⊤ := μ.apply_ne_top 0
  -- Step 1: μ 1 = 0
  have h1 : μ 1 = 0 := by
    have hleaf : ((PlaneTree.leaf).degrees.map fun d => μ d).prod ≠ 0 := by
      simpa [PlaneTree.leaf] using h0
    have hP := leaf_ne_zero_of_weight (n := 1) (t := PlaneTree.leaf)
      (by simp [PlaneTree.leaf, PlaneTree.degreeCount]) hleaf
    obtain ⟨hz, -⟩ := uniform_consequences hU le_rfl hP
    have := hz (PlaneTree.node [PlaneTree.leaf]) (by simp [PlaneTree.leaf, PlaneTree.degreeCount])
      (by simp [PlaneTree.leaf])
    simp [PlaneTree.leaf] at this
    tauto
  -- the recursion
  have hrec : ∀ n : ℕ, 3 ≤ n → bienaymeLaw μ.toMeasure (leafCountEvent n) ≠ 0 →
      μ n = μ 2 * μ (n - 1) := by
    intro n hn hP
    obtain ⟨-, hq⟩ := uniform_consequences hU (by omega) hP
    have := hq (corolla n) (corolla2 n)
      (by unfold PlaneTree.degreeCount; rw [degrees_corolla, List.count_cons_of_ne (by omega),
        List.count_replicate_self])
      (by rw [degrees_corolla]; simp; omega)
      (by unfold PlaneTree.degreeCount; rw [degrees_corolla2 (by omega)]
          rw [List.count_cons_of_ne (by omega), List.count_cons_of_ne (by omega),
            List.count_cons_self, List.count_cons_self, List.count_replicate_self]; omega)
      (by rw [degrees_corolla2 (by omega)]; simp; omega)
    rw [prod_corolla, prod_corolla2 μ (by omega)] at this
    have hpow : μ 0 ^ n ≠ 0 := pow_ne_zero _ h0
    have hpowtop : μ 0 ^ n ≠ ⊤ := ENNReal.pow_ne_top h0top
    have := (ENNReal.mul_left_inj hpow hpowtop).1 this
    rw [this]; ring
  -- Step 2: μ 2 ≠ 0
  have h2 : μ 2 ≠ 0 := by
    classical
    have hex := hc.exists_two_le_ne_zero hne
    obtain ⟨ha, ha0⟩ := Nat.find_spec hex
    have hmin := fun m (hm : m < Nat.find hex) => Nat.find_min hex hm
    set a := Nat.find hex with hadef
    by_cases ha2 : a = 2
    · rw [← ha2]; exact ha0
    · have ha3 : 3 ≤ a := by omega
      have hP := leaf_ne_zero_of_weight (n := a) (t := corolla a)
        (by unfold PlaneTree.degreeCount; rw [degrees_corolla, List.count_cons_of_ne (by omega),
          List.count_replicate_self])
        (by rw [prod_corolla]; exact mul_ne_zero ha0 (pow_ne_zero _ h0))
      have := hrec a ha3 hP
      have hm1 : μ (a - 1) ≠ 0 := by
        intro hz; rw [hz, mul_zero] at this; exact ha0 this
      exact absurd ⟨by omega, hm1⟩ (hmin (a - 1) (by omega))
  -- Step 3: P[λ = n] ≠ 0 for all n ≥ 1
  have hall : ∀ n : ℕ, 1 ≤ n → bienaymeLaw μ.toMeasure (leafCountEvent n) ≠ 0 := by
    intro n hn
    obtain ⟨hd, hcnt⟩ := degrees_cat (n - 1)
    refine leaf_ne_zero_of_weight (t := cat (n - 1)) (by rw [hcnt]; omega) ?_
    rw [Ne, List.prod_eq_zero_iff, List.mem_map]
    rintro ⟨d, hd', hz⟩
    rcases hd d hd' with rfl | rfl
    · exact h0 hz
    · exact h2 hz
  -- Step 4: μ n = μ 2 ^ (n - 1)
  have hpow : ∀ n : ℕ, 2 ≤ n → μ n = μ 2 ^ (n - 1) := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => simp
    | succ n hn ih =>
      rw [hrec (n + 1) (by omega) (hall _ (by omega))]
      rw [show n + 1 - 1 = n by omega, ih, ← pow_succ' ]
      congr 1
      omega
  -- Step 5: reals
  set q : ℝ := (μ 2).toReal with hq
  set z : ℝ := (μ 0).toReal with hz
  have hmw : ∀ i : ℕ, (μ i).toReal = geomW z q i := by
    intro i
    rcases i with _ | _ | i
    · simp [geomW, hz]
    · simp [geomW, h1]
    · simp only [geomW]
      rw [hpow (i + 2) (by omega), ENNReal.toReal_pow]
      simp [hq]
  have hq0 : 0 < q := ENNReal.toReal_pos h2 (μ.apply_ne_top 2)
  have hsum1 := hasSum_toReal μ
  have hmean := hasSum_mean_toReal hc
  simp_rw [hmw] at hsum1 hmean
  have hz0 : 0 ≤ z := ENNReal.toReal_nonneg
  have hq1 : q < 1 := by
    have h23 := sum_le_hasSum (Finset.range 4)
      (fun i _ => geomW_nonneg hz0 hq0.le i) hsum1
    simp [Finset.sum_range_succ, geomW] at h23
    nlinarith
  have hs1 := hsum1.unique (hasSum_geomW hq0.le hq1)
  have hs2 := hmean.unique (hasSum_geomW_mean (z := z) hq0.le hq1)
  obtain ⟨hqq, hzz⟩ := solve_params hq0 hq1 hs1.symm (by linarith)
  intro i
  rw [displayedWeight_eq, ← hqq, ← hzz, ← hmw, ENNReal.ofReal_toReal (μ.apply_ne_top i)]

theorem rem_uniformtree_iff {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1) :
    IsDisplayedLaw μ ↔ IsUniformConditioned μ :=
  ⟨uniform_of_displayed, displayed_of_uniform hc hne⟩

/-! ## The geometric tail and the displayed limits -/

private theorem bConst_gt : 1 < bConst := by
  unfold bConst; linarith [Real.sqrt_nonneg 2]

private theorem q0_eq : (2 - Real.sqrt 2) / 2 = 1 / bConst := by
  unfold bConst
  have := sqrt2_sq
  have hpos : 0 < Real.sqrt 2 := by linarith [sqrt2_gt]
  field_simp
  nlinarith

private theorem inv_one_sub_q0 : 1 / (1 - (2 - Real.sqrt 2) / 2) = Real.sqrt 2 := by
  rw [one_sub_q0]
  have := sqrt2_sq
  have hpos : 0 < Real.sqrt 2 := by linarith [sqrt2_gt]
  field_simp
  nlinarith

theorem displayedLaw_stepTail {μ : PMF ℕ} (hμ : IsDisplayedLaw μ) {j : ℕ} (hj : 1 ≤ j) :
    stepTail μ j = Real.sqrt 2 * (1 / bConst) ^ j := by
  unfold stepTail stepLaw
  rw [Measure.real, Measure.map_apply (measurable_of_countable _) (MeasurableSet.of_discrete),
    PMF.toMeasure_apply _ (MeasurableSet.of_discrete),
    ENNReal.tsum_toReal_eq (fun k => by
      by_cases hk : k ∈ ((fun k : ℕ => (k : ℤ) - 1) ⁻¹' {z : ℤ | (j : ℝ) ≤ (z : ℝ)})
      · rw [Set.indicator_of_mem hk]; exact μ.apply_ne_top k
      · rw [Set.indicator_of_notMem hk]; exact ENNReal.zero_ne_top)]
  have hf : ∀ k : ℕ, ((((fun k : ℕ => (k : ℤ) - 1) ⁻¹' {z : ℤ | (j : ℝ) ≤ (z : ℝ)}).indicator
      (⇑μ)) k).toReal =
      if j + 1 ≤ k then geomW (2 - Real.sqrt 2) ((2 - Real.sqrt 2) / 2) k else 0 := by
    intro k
    by_cases hk : j + 1 ≤ k
    · have hm : k ∈ ((fun k : ℕ => (k : ℤ) - 1) ⁻¹' {z : ℤ | (j : ℝ) ≤ (z : ℝ)}) := by
        show (j : ℝ) ≤ (((k : ℤ) - 1 : ℤ) : ℝ)
        have : ((j : ℤ)) ≤ (k : ℤ) - 1 := by omega
        exact_mod_cast this
      rw [Set.indicator_of_mem hm, displayed_toReal hμ]
      simp [hk]
    · have hm : k ∉ ((fun k : ℕ => (k : ℤ) - 1) ⁻¹' {z : ℤ | (j : ℝ) ≤ (z : ℝ)}) := by
        intro h
        have h' : (j : ℝ) ≤ (((k : ℤ) - 1 : ℤ) : ℝ) := h
        have : ((j : ℤ)) ≤ (k : ℤ) - 1 := by exact_mod_cast h'
        omega
      rw [Set.indicator_of_notMem hm]; simp [hk]
  simp_rw [hf]
  have hs : HasSum (fun k : ℕ => if j + 1 ≤ k then
      geomW (2 - Real.sqrt 2) ((2 - Real.sqrt 2) / 2) k else 0)
      (((2 - Real.sqrt 2) / 2) ^ j / (1 - (2 - Real.sqrt 2) / 2)) := by
    rw [← hasSum_nat_add_iff' (j + 1)]
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    convert (hasSum_geometric_of_lt_one q0_pos.le q0_lt).mul_left (((2 - Real.sqrt 2) / 2) ^ (j' + 1))
      using 1
    · ext n
      have : j' + 1 + 1 ≤ n + (j' + 1 + 1) := by omega
      simp only [this, ↓reduceIte]
      obtain ⟨m, hm⟩ : ∃ m, n + (j' + 1 + 1) = m + 2 := ⟨n + j', by omega⟩
      rw [hm]
      simp only [geomW]
      rw [show m = n + j' by omega]
      ring
    · rw [Finset.sum_eq_zero (fun i hi => by
        simp at hi; simp only [show ¬ (j' + 1 + 1 ≤ i) by omega, ↓reduceIte]), sub_zero, div_eq_mul_inv]
  rw [hs.tsum_eq, div_eq_mul_inv, ← one_div, inv_one_sub_q0, q0_eq]
  ring

private theorem bConst_pos : 0 < bConst := by linarith [bConst_gt]

private theorem inv_bConst_lt : 1 / bConst < 1 := by
  rw [div_lt_one bConst_pos]; exact bConst_gt

private instance isProbabilityMeasure_stepLaw (μ : PMF ℕ) : IsProbabilityMeasure (stepLaw μ) := by
  unfold stepLaw
  infer_instance

private theorem stepTail_real_bounds {μ : PMF ℕ} (hμ : IsDisplayedLaw μ) {a : ℝ} (ha : 0 < a) :
    Real.sqrt 2 * (1 / bConst) ^ (a + 1) ≤ stepTail μ a ∧
      stepTail μ a ≤ Real.sqrt 2 * (1 / bConst) ^ a := by
  have hj : 0 < ⌈a⌉₊ := Nat.ceil_pos.2 ha
  have hset : {z : ℤ | a ≤ (z : ℝ)} = {z : ℤ | ((⌈a⌉₊ : ℕ) : ℝ) ≤ (z : ℝ)} := by
    ext z
    simp only [Set.mem_ofPred_eq]
    constructor
    · intro h
      have hz : 0 ≤ z := by
        have : (0 : ℝ) ≤ z := ha.le.trans h
        exact_mod_cast this
      obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hz
      have : a ≤ (m : ℝ) := by simpa using h
      have := Nat.ceil_le.2 this
      exact_mod_cast (by exact_mod_cast this : ((⌈a⌉₊ : ℕ) : ℝ) ≤ (m : ℝ))
    · intro h
      exact (Nat.le_ceil a).trans h
  have hst : stepTail μ a = stepTail μ (⌈a⌉₊ : ℕ) := by
    unfold stepTail
    rw [hset]
  rw [hst, displayedLaw_stepTail hμ hj]
  have hb0 : 0 < 1 / bConst := by have := bConst_pos; positivity
  have hb1 : 1 / bConst ≤ 1 := inv_bConst_lt.le
  have hnat : ((1 / bConst) ^ (⌈a⌉₊ : ℕ) : ℝ) = (1 / bConst) ^ ((⌈a⌉₊ : ℕ) : ℝ) :=
    (Real.rpow_natCast _ _).symm
  rw [hnat]
  have hs2 : 0 < Real.sqrt 2 := by linarith [sqrt2_gt]
  constructor
  · apply mul_le_mul_of_nonneg_left _ hs2.le
    exact Real.rpow_le_rpow_of_exponent_ge hb0 hb1 (Nat.ceil_lt_add_one ha.le).le
  · apply mul_le_mul_of_nonneg_left _ hs2.le
    exact Real.rpow_le_rpow_of_exponent_ge hb0 hb1 (Nat.le_ceil a)

private theorem bq_pow_minus {x : ℝ} (hx : 0 < x) (hl : 0 < Real.logb bConst x) (c : ℝ) :
    (1 / bConst) ^ (Real.logb bConst x - c * Real.logb bConst (Real.logb bConst x)) =
      (Real.logb bConst x) ^ c / x := by
  have hb := bConst_pos
  have hb1 : bConst ≠ 1 := bConst_gt.ne'
  rw [one_div, Real.inv_rpow hb.le, Real.rpow_sub hb, Real.rpow_logb hb hb1 hx,
    mul_comm c, Real.rpow_mul hb.le, Real.rpow_logb hb hb1 hl, inv_div]

private theorem bq_pow_plus {x : ℝ} (hx : 0 < x) (hl : 0 < Real.logb bConst x) (c : ℝ) :
    (1 / bConst) ^ (Real.logb bConst x + c * Real.logb bConst (Real.logb bConst x)) =
      (x * (Real.logb bConst x) ^ c)⁻¹ := by
  have hb := bConst_pos
  have hb1 : bConst ≠ 1 := bConst_gt.ne'
  rw [one_div, Real.inv_rpow hb.le, Real.rpow_add hb, Real.rpow_logb hb hb1 hx,
    mul_comm c, Real.rpow_mul hb.le, Real.rpow_logb hb hb1 hl]

private theorem ell_tendsto : Tendsto (fun n : ℕ => Real.logb bConst n) atTop atTop :=
  (Real.tendsto_logb_atTop bConst_gt).comp tendsto_natCast_atTop_atTop

private theorem eventually_c_log_small {c : ℝ} (hc : 0 < c) :
    ∀ᶠ x : ℝ in atTop, c * Real.logb bConst x ≤ x / 2 := by
  have hlb : 0 < Real.log bConst := Real.log_pos bConst_gt
  have h := Real.isLittleO_log_id_atTop.def (c := Real.log bConst / (2 * c)) (by positivity)
  filter_upwards [h, eventually_gt_atTop 0] with x hx hx0
  rw [Real.norm_eq_abs, Real.norm_eq_abs, id, abs_of_pos hx0] at hx
  have h1 : Real.log x ≤ Real.log bConst / (2 * c) * x := (le_abs_self _).trans hx
  rw [Real.logb, mul_div_assoc', div_le_iff₀ hlb]
  have : c * Real.log x ≤ c * (Real.log bConst / (2 * c) * x) := mul_le_mul_of_nonneg_left h1 hc.le
  have e : c * (Real.log bConst / (2 * c) * x) = x / 2 * Real.log bConst := by field_simp
  linarith

private theorem stepTail_nonneg_le_one (μ : PMF ℕ) (a : ℝ) : 0 ≤ stepTail μ a ∧ stepTail μ a ≤ 1 :=
  ⟨measureReal_nonneg, measureReal_le_one⟩

private theorem one_sub_rpow_le_exp {P r : ℝ} (hP1 : P ≤ 1) (hr : 0 ≤ r) :
    (1 - P) ^ r ≤ Real.exp (-(P * r)) := by
  have h1 : 1 - P ≤ Real.exp (-P) := by linarith [Real.add_one_le_exp (-P)]
  calc (1 - P) ^ r ≤ (Real.exp (-P)) ^ r := Real.rpow_le_rpow (by linarith) h1 hr
    _ = Real.exp (-(P * r)) := by rw [← Real.exp_mul]; ring_nf

theorem rem_uniformtree_tail_lower {μ : PMF ℕ} (hμ : IsDisplayedLaw μ) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun n : ℕ =>
      (1 - stepTail μ (Real.logb bConst n - c * Real.logb bConst (Real.logb bConst n))) ^
        ((n : ℝ) / (4 * (μ 0).toReal))) atTop (𝓝 0) := by
  have hz : (μ 0).toReal = 2 - Real.sqrt 2 := by simpa [geomW] using displayed_toReal hμ 0
  have hzpos := z0_pos
  have hs2 : 0 < Real.sqrt 2 := by linarith [sqrt2_gt]
  have hb := bConst_pos
  set κ : ℝ := Real.sqrt 2 / bConst / (4 * (2 - Real.sqrt 2)) with hκ
  have hκpos : 0 < κ := by positivity
  have hY : Tendsto (fun n : ℕ => (Real.logb bConst n) ^ c) atTop atTop :=
    (tendsto_rpow_atTop hc).comp ell_tendsto
  have hg : Tendsto (fun n : ℕ => Real.exp (-(κ * (Real.logb bConst n) ^ c))) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp (hY.const_mul_atTop hκpos))
  have hev : ∀ᶠ n : ℕ in atTop, 2 ≤ n ∧ 0 < Real.logb bConst n ∧
      c * Real.logb bConst (Real.logb bConst n) ≤ Real.logb bConst n / 2 :=
    (eventually_ge_atTop 2).and (((ell_tendsto.eventually_gt_atTop 0)).and
      (ell_tendsto.eventually (eventually_c_log_small hc)))
  refine squeeze_zero' (Eventually.of_forall fun n => ?_) ?_ hg
  · exact Real.rpow_nonneg (by linarith [(stepTail_nonneg_le_one μ
      (Real.logb bConst n - c * Real.logb bConst (Real.logb bConst n))).2]) _
  filter_upwards [hev] with n ⟨hn2, hl, hcl⟩
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  set a := Real.logb bConst n - c * Real.logb bConst (Real.logb bConst n) with ha
  have hapos : 0 < a := by rw [ha]; linarith
  obtain ⟨hP0, hP1⟩ := stepTail_nonneg_le_one μ a
  have hP := (stepTail_real_bounds hμ hapos).1
  have hb0 : 0 < 1 / bConst := by positivity
  rw [Real.rpow_add hb0, Real.rpow_one, ha, bq_pow_minus hn0 hl c] at hP
  have hr : 0 ≤ (n : ℝ) / (4 * (μ 0).toReal) := by rw [hz]; positivity
  refine (one_sub_rpow_le_exp hP1 hr).trans (Real.exp_le_exp.2 (neg_le_neg ?_))
  have hYpos : 0 < (Real.logb bConst n) ^ c := Real.rpow_pos_of_pos hl _
  calc κ * (Real.logb bConst n) ^ c = Real.sqrt 2 * ((Real.logb bConst n) ^ c / n * (1 / bConst)) *
        ((n : ℝ) / (4 * (μ 0).toReal)) := by
        rw [hz, hκ]; field_simp
    _ ≤ stepTail μ a * ((n : ℝ) / (4 * (μ 0).toReal)) := mul_le_mul_of_nonneg_right hP hr

private theorem tail_upper_gen {μ : PMF ℕ} (hμ : IsDisplayedLaw μ) {c : ℝ} (hc : 0 < c)
    {r : ℕ → ℝ} (hr : ∀ᶠ n : ℕ in atTop, 1 ≤ r n ∧ r n ≤ (n : ℝ) / (μ 0).toReal) :
    Tendsto (fun n : ℕ =>
      (1 - stepTail μ (Real.logb bConst n + c * Real.logb bConst (Real.logb bConst n))) ^ (r n))
      atTop (𝓝 1) := by
  have hz : (μ 0).toReal = 2 - Real.sqrt 2 := by simpa [geomW] using displayed_toReal hμ 0
  have hzpos := z0_pos
  have hs2 : 0 < Real.sqrt 2 := by linarith [sqrt2_gt]
  have hb := bConst_pos
  have hY : Tendsto (fun n : ℕ => (Real.logb bConst n) ^ c) atTop atTop :=
    (tendsto_rpow_atTop hc).comp ell_tendsto
  have hg : Tendsto (fun n : ℕ => 1 - Real.sqrt 2 / (2 - Real.sqrt 2) *
      ((Real.logb bConst n) ^ c)⁻¹) atTop (𝓝 1) := by
    have := (tendsto_inv_atTop_zero.comp hY).const_mul (Real.sqrt 2 / (2 - Real.sqrt 2))
    simpa using this.const_sub 1
  have hev : ∀ᶠ n : ℕ in atTop, 2 ≤ n ∧ 1 ≤ Real.logb bConst n :=
    (eventually_ge_atTop 2).and (ell_tendsto.eventually_ge_atTop 1)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hg tendsto_const_nhds ?_ ?_
  · filter_upwards [hev, hr] with n ⟨hn2, hl1⟩ ⟨hr1, hr2⟩
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hl : 0 < Real.logb bConst n := by linarith
    set a := Real.logb bConst n + c * Real.logb bConst (Real.logb bConst n) with ha
    have hL : 0 ≤ Real.logb bConst (Real.logb bConst n) := Real.logb_nonneg bConst_gt hl1
    have hapos : 0 < a := by rw [ha]; nlinarith
    obtain ⟨hP0, hP1⟩ := stepTail_nonneg_le_one μ a
    have hP := (stepTail_real_bounds hμ hapos).2
    rw [ha, bq_pow_plus hn0 hl c] at hP
    have hYpos : 0 < (Real.logb bConst n) ^ c := Real.rpow_pos_of_pos hl _
    have hB := one_add_mul_self_le_rpow_one_add (s := -stepTail μ a) (by linarith) hr1
    rw [← sub_eq_add_neg] at hB
    refine le_trans ?_ hB
    have h1 : r n * stepTail μ a ≤ (n : ℝ) / (μ 0).toReal * stepTail μ a :=
      mul_le_mul_of_nonneg_right hr2 hP0
    have h2 : (n : ℝ) / (μ 0).toReal * stepTail μ a ≤ Real.sqrt 2 / (2 - Real.sqrt 2) *
        ((Real.logb bConst n) ^ c)⁻¹ := by
      calc (n : ℝ) / (μ 0).toReal * stepTail μ a
          ≤ (n : ℝ) / (μ 0).toReal * (Real.sqrt 2 * (n * (Real.logb bConst n) ^ c)⁻¹) :=
            mul_le_mul_of_nonneg_left hP (by positivity)
        _ = _ := by rw [hz]; field_simp
    have : 1 + r n * -stepTail μ a = 1 - r n * stepTail μ a := by ring
    rw [this]
    linarith
  · filter_upwards [hev, hr] with n ⟨hn2, hl1⟩ ⟨hr1, hr2⟩
    have hl : 0 < Real.logb bConst n := by linarith
    obtain ⟨hP0, hP1⟩ := stepTail_nonneg_le_one μ
      (Real.logb bConst n + c * Real.logb bConst (Real.logb bConst n))
    exact Real.rpow_le_one (by linarith) (by linarith) (by linarith)

theorem rem_uniformtree_tail_upper {μ : PMF ℕ} (hμ : IsDisplayedLaw μ) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun n : ℕ =>
      (1 - stepTail μ (Real.logb bConst n + c * Real.logb bConst (Real.logb bConst n))) ^
        ((n : ℝ) / (μ 0).toReal)) atTop (𝓝 1) := by
  have hz : (μ 0).toReal = 2 - Real.sqrt 2 := by simpa [geomW] using displayed_toReal hμ 0
  refine tail_upper_gen hμ hc ?_
  filter_upwards [eventually_ge_atTop ⌈2 - Real.sqrt 2⌉₊] with n hn
  refine ⟨?_, le_rfl⟩
  rw [hz, le_div_iff₀ z0_pos]
  have := Nat.le_of_ceil_le hn
  simpa using this

theorem rem_uniformtree_tail_upper_printed {μ : PMF ℕ} (hμ : IsDisplayedLaw μ) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun n : ℕ =>
      (1 - stepTail μ (Real.logb bConst n + c * Real.logb bConst (Real.logb bConst n))) ^
        ((n : ℝ) / (4 * (μ 0).toReal))) atTop (𝓝 1) := by
  have hz : (μ 0).toReal = 2 - Real.sqrt 2 := by simpa [geomW] using displayed_toReal hμ 0
  refine tail_upper_gen hμ hc ?_
  filter_upwards [eventually_ge_atTop ⌈4 * (2 - Real.sqrt 2)⌉₊] with n hn
  have hn' : 4 * (2 - Real.sqrt 2) ≤ (n : ℝ) := Nat.le_of_ceil_le hn
  have hz0 := z0_pos
  refine ⟨?_, ?_⟩
  · rw [hz, le_div_iff₀ (by positivity)]
    linarith
  · rw [hz]
    apply div_le_div_of_nonneg_left (Nat.cast_nonneg _) z0_pos
    linarith

end BGWLeaves.Vervaat.UniformTree
