module

public import BGWLeaves.Vervaat.Defs

/-!
# The Vervaat transform and the Cyclic Lemma (6.3, 6.4)

Proofs for the Vervaat transform and the Cyclic Lemma (6.3, 6.4): `vervaatIdx_mem`, `mem_SBar_iff`,
`vervaat_mem_SBar`, `vervaatIdx_unique`, `walkWord_atom`, `sum_walkWord`, `lem_cool_i_joint`, `lem_cool_i`,
`lem_cool_ii`, `vervaat_prob_eq`.  The theorems are those stated in `BGWLeaves.Vervaat`; they are exported in
namespace `BGWLeaves.Vervaat.Cyclic` with exactly the types stated there.
-/

@[expose] public section

namespace BGWLeaves.Vervaat.Cyclic

open MeasureTheory ProbabilityTheory Filter BGW
open BGW.StableTrees BGW.LocallyFinite BGWLeaves.StableAnalysis
open scoped ENNReal Topology

local notation "𝐏w[" μ "]" => Measure.infinitePi (fun _ : ℕ => μ)

/-! ## 6.3 The Vervaat transform: list-level facts -/

theorem vervaatIdx_spec {x : List ℤ} (hx : x ≠ []) :
    (1 ≤ vervaatIdx x ∧ vervaatIdx x ≤ x.length) ∧
    (∀ i, 1 ≤ i → i ≤ x.length → (x.take (vervaatIdx x)).sum ≤ (x.take i).sum) ∧
    (∀ j, 1 ≤ j → j < vervaatIdx x → (x.take (vervaatIdx x)).sum < (x.take j).sum) := by
  classical
  have hlen : 0 < x.length := List.length_pos_iff.mpr hx
  obtain ⟨i0, hi0, hmin⟩ := Finset.exists_min_image (Finset.Icc 1 x.length)
    (fun j => (x.take j).sum) ⟨1, by simp; omega⟩
  have hne : {j : ℕ | 1 ≤ j ∧ j ≤ x.length ∧
      ∀ i : ℕ, 1 ≤ i → i ≤ x.length → (x.take j).sum ≤ (x.take i).sum}.Nonempty :=
    ⟨i0, by
      simp only [Finset.mem_Icc] at hi0
      exact ⟨hi0.1, hi0.2, fun i h1 h2 => hmin i (by simp only [Finset.mem_Icc]; omega)⟩⟩
  have e : vervaatIdx x = sInf {j : ℕ | 1 ≤ j ∧ j ≤ x.length ∧
      ∀ i : ℕ, 1 ≤ i → i ≤ x.length → (x.take j).sum ≤ (x.take i).sum} := rfl
  obtain ⟨a1, a2, a3⟩ := Nat.sInf_mem hne
  rw [← e] at a1 a2 a3
  refine ⟨⟨a1, a2⟩, a3, fun j hj1 hjlt => ?_⟩
  have hnot := Nat.notMem_of_lt_sInf (e ▸ hjlt)
  simp only [Set.mem_ofPred_eq, not_and, not_forall, not_le] at hnot
  obtain ⟨i, hi1, hi2, hlt⟩ := hnot hj1 (by omega)
  exact lt_of_le_of_lt (a3 i hi1 hi2) hlt

/-- Prefix sums of the rotation by `i`, for a word of sum `-1`. -/
theorem rot_prefix {x : List ℤ} (hsum : x.sum = -1) {i m : ℕ} (hi : i ≤ x.length)
    (hm : m ≤ x.length) :
    ((x.rotate i).take m).sum =
      if m ≤ x.length - i then (x.take (i + m)).sum - (x.take i).sum
      else -1 - (x.take i).sum + (x.take (m - (x.length - i))).sum := by
  rw [sum_take_rotate x hi hm, hsum]

/-- `1 ≤ i_*(x) ≤ k` for `k ≥ 1`. -/
theorem vervaatIdx_mem {x : List ℤ} (hx : x ≠ []) : 1 ≤ vervaatIdx x ∧ vervaatIdx x ≤ x.length :=
  (vervaatIdx_spec hx).1

theorem mem_SBar_iff {x : List ℤ} {k n : ℕ} :
    x ∈ SBar k n ↔ x.length = k ∧ IsTreeExcursion x ∧ x.count (-1) = n := by
  constructor
  · rintro ⟨h1, h2, h3, h4, h5⟩
    refine ⟨h1, ⟨h2, h3, fun i hi => ?_⟩, h4⟩
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · simp
    · have := h5 i hi0 (h1 ▸ hi)
      omega
  · rintro ⟨h1, ⟨h2, h3, h5⟩, h4⟩
    refine ⟨h1, h2, h3, h4, fun m hm1 hm2 => ?_⟩
    have := h5 m (h1 ▸ hm2)
    omega

/-- Prefix sums of a shift that lies in `SBar`: the min characterization. -/
theorem rot_min_of_SBar {x : List ℤ} (hsum : x.sum = -1) {i n : ℕ}
    (hi : 1 ≤ i ∧ i ≤ x.length) (hS : x.rotate i ∈ SBar x.length n) :
    (∀ l, i ≤ l → l ≤ x.length → (x.take i).sum ≤ (x.take l).sum) ∧
    (∀ l, 1 ≤ l → l < i → (x.take i).sum < (x.take l).sum) := by
  obtain ⟨hl, -, -, -, hp⟩ := hS
  have hk : (x.rotate i).length = x.length := List.length_rotate _ _
  constructor
  · intro l hl1 hl2
    rcases Nat.eq_zero_or_pos (l - i) with h0 | hpos
    · have : l = i := by omega
      subst this; exact le_rfl
    · have h := hp (l - i) hpos (by omega)
      rw [rot_prefix hsum hi.2 (by omega), ite_eq_left (by omega),
        show i + (l - i) = l by omega] at h
      omega
  · intro l hl1 hl2
    have h := hp (x.length - i + l) (by omega) (by omega)
    rw [rot_prefix hsum hi.2 (by omega), ite_eq_right (by omega),
      show x.length - i + l - (x.length - i) = l by omega] at h
    omega

theorem vervaat_mem_SBar {x : List ℤ} (hx : x ≠ []) (hge : ∀ a ∈ x, -1 ≤ a) (hsum : x.sum = -1) :
    vervaat x ∈ SBar x.length (x.count (-1)) := by
  obtain ⟨⟨h1, h2⟩, hmin, hfirst⟩ := vervaatIdx_spec hx
  have hrot : vervaat x = x.rotate (vervaatIdx x) := by
    rw [vervaat, cyclicShift_eq_rotate]
  refine ⟨by rw [length_vervaat], ?_, by rw [sum_vervaat, hsum], count_vervaat x (-1), ?_⟩
  · intro a ha
    rw [hrot] at ha
    exact hge a (List.mem_rotate.mp ha)
  · intro m hm1 hm2
    rw [hrot, rot_prefix hsum h2 hm2.le]
    split_ifs with hc
    · have := hmin (vervaatIdx x + m) (by omega) (by omega)
      omega
    · have := hfirst (m - (x.length - vervaatIdx x)) (by omega) (by omega)
      omega

theorem vervaatIdx_unique {x : List ℤ} (hge : ∀ a ∈ x, -1 ≤ a) (hsum : x.sum = -1) {i n : ℕ}
    (hi : 1 ≤ i ∧ i ≤ x.length) (hS : cyclicShift x i ∈ SBar x.length n) : vervaatIdx x = i := by
  have _ := hge
  rw [cyclicShift_eq_rotate] at hS
  obtain ⟨h1, h2⟩ := rot_min_of_SBar hsum hi hS
  refine vervaatIdx_eq_of hi.1 hi.2 (fun l hl1 hl2 => ?_) (fun j' hj1 hj2 => ?_)
  · rcases lt_or_ge l i with h | h
    · exact (h2 l hl1 h).le
    · exact h1 l h hl2
  · exact ⟨i, hi.1, hi.2, h2 j' hj1 hj2⟩


/-! ## Walk words -/

theorem sum_walkWord (ω : ℕ → ℕ) (k : ℕ) : (walkWord ω k).sum = walkSum ω k := by
  induction k with
  | zero => simp [walkWord, walkSum]
  | succ k ih =>
    rw [walkSum, Finset.sum_range_succ, ← walkSum, ← ih, walkWord, List.range_succ,
      List.map_append, List.sum_append]
    simp [walkWord]

theorem length_walkWord (ω : ℕ → ℕ) (k : ℕ) : (walkWord ω k).length = k := by
  simp [walkWord]

theorem getElem_walkWord (ω : ℕ → ℕ) (k i : ℕ) (hi : i < (walkWord ω k).length) :
    (walkWord ω k)[i] = (ω i : ℤ) - 1 := by
  simp [walkWord]

theorem walkWord_ge (ω : ℕ → ℕ) (k : ℕ) : ∀ a ∈ walkWord ω k, -1 ≤ a := by
  intro a ha
  obtain ⟨i, -, rfl⟩ := List.mem_map.mp ha
  omega

theorem int_step_eq_iff_nat (z : ℤ) (n : ℕ) (hz : -1 ≤ z) :
    ((n : ℤ) - 1 = z) ↔ n = (z + 1).toNat := by omega

theorem walkWord_event {y : List ℤ} (hy : ∀ a ∈ y, -1 ≤ a) :
    {ω : ℕ → ℕ | walkWord ω y.length = y} =
      Set.pi (Finset.range y.length) (fun i => {((y[i]?.getD 0 + 1).toNat)}) := by
  ext ω
  simp only [Set.mem_ofPred_eq, Set.mem_pi, Set.mem_singleton_iff, Finset.mem_coe,
    Finset.mem_range]
  constructor
  · intro h i hi
    have h1 := getElem_walkWord ω y.length i (by rw [length_walkWord]; exact hi)
    have h2 : (walkWord ω y.length)[i]'(by rw [length_walkWord]; exact hi) = y[i] :=
      List.getElem_of_eq h _
    have hge := hy _ (List.getElem_mem hi)
    have : y[i]?.getD 0 = y[i] := by simp [List.getElem?_eq_getElem hi]
    rw [this]
    omega
  · intro h
    apply List.ext_getElem (by rw [length_walkWord])
    intro i h1 h2
    rw [getElem_walkWord]
    have hi : i < y.length := h2
    have := h i hi
    have hge := hy _ (List.getElem_mem hi)
    have e : y[i]?.getD 0 = y[i] := by simp [List.getElem?_eq_getElem hi]
    rw [e] at this
    omega

theorem walkWord_event_empty {y : List ℤ} (hy : ¬ ∀ a ∈ y, -1 ≤ a) {k : ℕ} :
    {ω : ℕ → ℕ | walkWord ω k = y} = ∅ := by
  ext ω
  simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
  intro h
  exact hy (h ▸ walkWord_ge ω k)

theorem list_map_prod_eq_range {α : Type*} [Inhabited α] (x : List α)
    (f : α → ℝ≥0∞) :
    (x.map f).prod = ∏ i ∈ Finset.range x.length, f (x[i]?.getD default) := by
  induction x with
  | nil => simp
  | cons a xs ih =>
    simp only [List.map_cons, List.prod_cons, List.length_cons]
    rw [Finset.prod_range_succ']
    simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]
    rw [ih]
    ac_rfl

theorem walkWord_atom (μ : Measure ℕ) [IsProbabilityMeasure μ] (y : List ℤ) :
    𝐏w[μ] {ω | walkWord ω y.length = y} =
      if ∀ a ∈ y, -1 ≤ a then (y.map fun a => μ {(a + 1).toNat}).prod else 0 := by
  by_cases hy : ∀ a ∈ y, -1 ≤ a
  · rw [ite_eq_left hy, walkWord_event hy,
      Measure.infinitePi_pi (fun _ : ℕ => μ) (s := Finset.range y.length)
        (t := fun i => ({((y[i]?.getD 0 + 1).toNat)} : Set ℕ))]
    · simpa using (list_map_prod_eq_range y (fun a => μ {(a + 1).toNat})).symm
    · intro i hi
      exact measurableSet_singleton _
  · rw [ite_eq_right hy, walkWord_event_empty hy]
    simp

theorem measurableSet_walkWord_eq (k : ℕ) (y : List ℤ) :
    MeasurableSet {ω : ℕ → ℕ | walkWord ω k = y} := by
  by_cases hk : y.length = k
  · subst hk
    by_cases hy : ∀ a ∈ y, -1 ≤ a
    · rw [walkWord_event hy]
      exact MeasurableSet.pi (Finset.range y.length).countable_toSet
        (fun _ _ => measurableSet_singleton _)
    · rw [walkWord_event_empty hy]; exact MeasurableSet.empty
  · have : {ω : ℕ → ℕ | walkWord ω k = y} = ∅ := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      intro h
      apply hk
      rw [← h, length_walkWord]
    rw [this]; exact MeasurableSet.empty

theorem measurable_walkSum (k : ℕ) : Measurable fun ω : ℕ → ℕ => walkSum ω k := by
  unfold walkSum
  refine Finset.measurable_sum _ (fun i _ => ?_)
  exact (measurable_from_top.comp (measurable_pi_apply i)).sub_const _


/-! ## The Cyclic Lemma for walk words -/

theorem rotate_back {Z x : List ℤ} {i : ℕ} (hx : x = Z.rotate i) (hi : i ≤ Z.length) :
    Z = x.rotate (Z.length - i) := by
  subst hx
  rw [List.rotate_rotate, show i + (Z.length - i) = Z.length by omega, List.rotate_length]

theorem one_le_of_SBar {k n : ℕ} {x : List ℤ} (hx : x ∈ SBar k n) : 1 ≤ k := by
  obtain ⟨hl, -, hsum, -, -⟩ := hx
  by_contra h
  have : x = [] := List.length_eq_zero_iff.mp (by omega)
  simp [this] at hsum

theorem good_of_rot {k n : ℕ} {x : List ℤ} (hx : x ∈ SBar k n) {j : ℕ} (hj : j < k)
    {Z : List ℤ} (hZ : Z = x.rotate j) :
    vervaatIdx Z = k - j ∧ vervaat Z = x ∧ Z.sum = -1 ∧ ∀ a ∈ Z, -1 ≤ a := by
  have hx' := hx
  obtain ⟨hl, hge, hsum, -, -⟩ := hx
  subst hZ
  have hlen : (x.rotate j).length = k := by simp [hl]
  have hsumZ : (x.rotate j).sum = -1 := by rw [(List.rotate_perm x j).sum_eq]; exact hsum
  have hgeZ : ∀ a ∈ x.rotate j, -1 ≤ a := fun a ha => hge a (List.mem_rotate.mp ha)
  have hback : (x.rotate j).rotate (k - j) = x := by
    rw [List.rotate_rotate, show j + (k - j) = k by omega, ← hl, List.rotate_length]
  have hS : cyclicShift (x.rotate j) (k - j) ∈ SBar (x.rotate j).length n := by
    rw [cyclicShift_eq_rotate, hback, hlen]; exact hx'
  have hidx : vervaatIdx (x.rotate j) = k - j :=
    vervaatIdx_unique hgeZ hsumZ ⟨by omega, by omega⟩ hS
  refine ⟨hidx, ?_, hsumZ, hgeZ⟩
  rw [vervaat, hidx, cyclicShift_eq_rotate, hback]

theorem idx_range {k : ℕ} (hk : 1 ≤ k) (ω : ℕ → ℕ) :
    1 ≤ vervaatIdx (walkWord ω k) ∧ vervaatIdx (walkWord ω k) ≤ k := by
  have hne : walkWord ω k ≠ [] := by
    intro h
    have := length_walkWord ω k
    rw [h] at this
    simp at this
    omega
  have := vervaatIdx_mem hne
  rwa [length_walkWord] at this

theorem E_eq {k n : ℕ} {x : List ℤ} (hx : x ∈ SBar k n) {i : ℕ} (hi : 1 ≤ i ∧ i ≤ k) :
    {ω : ℕ → ℕ | vervaatIdx (walkWord ω k) = i ∧ vervaat (walkWord ω k) = x ∧
        walkSum ω k = -1} =
      {ω | walkWord ω k = x.rotate (k - i)} := by
  ext ω
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨h1, h2, -⟩
    have hrot : x = (walkWord ω k).rotate i := by
      rw [← h2, vervaat, h1, cyclicShift_eq_rotate]
    have := rotate_back hrot (by rw [length_walkWord]; exact hi.2)
    rwa [length_walkWord] at this
  · intro h
    obtain ⟨a, b, c, -⟩ := good_of_rot hx (j := k - i) (by omega) h
    refine ⟨by omega, b, ?_⟩
    rw [← sum_walkWord]; exact c

theorem F_empty {k : ℕ} (hk : 1 ≤ k) {x : List ℤ} (hno : ∀ n, x ∉ SBar k n) :
    {ω : ℕ → ℕ | vervaat (walkWord ω k) = x ∧ walkSum ω k = -1} = ∅ := by
  ext ω
  simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
  rintro ⟨h2, h3⟩
  have hne : walkWord ω k ≠ [] := by
    intro h
    have := length_walkWord ω k
    rw [h] at this
    simp at this
    omega
  have := vervaat_mem_SBar hne (walkWord_ge ω k) (by rw [sum_walkWord]; exact h3)
  rw [h2, length_walkWord] at this
  exact hno _ this

theorem E_empty {k : ℕ} (hk : 1 ≤ k) (x : List ℤ) {i : ℕ} (hi : ¬ (1 ≤ i ∧ i ≤ k)) :
    {ω : ℕ → ℕ | vervaatIdx (walkWord ω k) = i ∧ vervaat (walkWord ω k) = x ∧
        walkSum ω k = -1} = ∅ := by
  ext ω
  simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
  rintro ⟨h1, -, -⟩
  exact hi (h1 ▸ idx_range hk ω)

theorem E_empty' {k : ℕ} (hk : 1 ≤ k) {x : List ℤ} (hno : ∀ n, x ∉ SBar k n) (i : ℕ) :
    {ω : ℕ → ℕ | vervaatIdx (walkWord ω k) = i ∧ vervaat (walkWord ω k) = x ∧
        walkSum ω k = -1} = ∅ := by
  have := F_empty hk hno
  ext ω
  simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
  rintro ⟨-, h2, h3⟩
  have h : ω ∈ {ω : ℕ → ℕ | vervaat (walkWord ω k) = x ∧ walkSum ω k = -1} := ⟨h2, h3⟩
  rw [this] at h
  exact h

theorem F_eq {k : ℕ} (hk : 1 ≤ k) (x : List ℤ) :
    {ω : ℕ → ℕ | vervaat (walkWord ω k) = x ∧ walkSum ω k = -1} =
      ⋃ i ∈ Finset.Icc 1 k, {ω : ℕ → ℕ | vervaatIdx (walkWord ω k) = i ∧
        vervaat (walkWord ω k) = x ∧ walkSum ω k = -1} := by
  ext ω
  simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Finset.mem_Icc, exists_prop]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨_, idx_range hk ω, rfl, h1, h2⟩
  · rintro ⟨i, -, -, h1, h2⟩
    exact ⟨h1, h2⟩

theorem measurableSet_E {k : ℕ} (hk : 1 ≤ k) (x : List ℤ) (i : ℕ) :
    MeasurableSet {ω : ℕ → ℕ | vervaatIdx (walkWord ω k) = i ∧ vervaat (walkWord ω k) = x ∧
        walkSum ω k = -1} := by
  by_cases h : ∃ n, x ∈ SBar k n
  · obtain ⟨n, hn⟩ := h
    by_cases hi : 1 ≤ i ∧ i ≤ k
    · rw [E_eq hn hi]; exact measurableSet_walkWord_eq k _
    · rw [E_empty hk x hi]; exact MeasurableSet.empty
  · push Not at h
    rw [E_empty' hk h]; exact MeasurableSet.empty

theorem measurableSet_F {k : ℕ} (hk : 1 ≤ k) (x : List ℤ) :
    MeasurableSet {ω : ℕ → ℕ | vervaat (walkWord ω k) = x ∧ walkSum ω k = -1} := by
  rw [F_eq hk]
  exact Finset.measurableSet_biUnion _ (fun i _ => measurableSet_E hk x i)

theorem measurableSet_A (k : ℕ) : MeasurableSet {ω : ℕ → ℕ | walkSum ω k = -1} :=
  measurable_walkSum k (measurableSet_singleton (-1))

theorem prob_rot (μ : Measure ℕ) [IsProbabilityMeasure μ] {k n : ℕ} {x : List ℤ}
    (hx : x ∈ SBar k n) (j : ℕ) :
    𝐏w[μ] {ω | walkWord ω k = x.rotate j} = 𝐏w[μ] {ω | walkWord ω k = x} := by
  have hl : x.length = k := hx.1
  have hge := hx.2.1
  have h1 : (x.rotate j).length = k := by simp [hl]
  have hge' : ∀ a ∈ x.rotate j, -1 ≤ a := fun a ha => hge a (List.mem_rotate.mp ha)
  have a1 := walkWord_atom μ (x.rotate j)
  rw [h1] at a1
  have a2 := walkWord_atom μ x
  rw [hl] at a2
  rw [a1, a2, ite_eq_left hge', ite_eq_left hge, List.map_rotate, (List.rotate_perm _ _).prod_eq]

theorem prob_F (μ : Measure ℕ) [IsProbabilityMeasure μ] {k n : ℕ} {x : List ℤ}
    (hx : x ∈ SBar k n) :
    𝐏w[μ] {ω | vervaat (walkWord ω k) = x ∧ walkSum ω k = -1} =
      (k : ℝ≥0∞) * 𝐏w[μ] {ω | walkWord ω k = x} := by
  have hk := one_le_of_SBar hx
  rw [F_eq hk, measure_biUnion_finset]
  · rw [Finset.sum_congr rfl (fun i hi => by
      rw [E_eq hx (Finset.mem_Icc.1 hi), prob_rot μ hx])]
    simp [Finset.sum_const]
  · intro i _ j _ hij
    refine Set.disjoint_left.mpr (fun ω h1 h2 => hij ?_)
    exact h1.1.symm.trans h2.1
  · exact fun i _ => measurableSet_E hk x i

theorem lem_cool_i_joint (μ : Measure ℕ) [IsProbabilityMeasure μ] {k : ℕ} (hk : 1 ≤ k) {i : ℕ}
    (hi : 1 ≤ i ∧ i ≤ k) (x : List ℤ) :
    𝐏w[μ] {ω | vervaatIdx (walkWord ω k) = i ∧ vervaat (walkWord ω k) = x ∧ walkSum ω k = -1} =
      (1 / (k : ℝ≥0∞)) * 𝐏w[μ] {ω | vervaat (walkWord ω k) = x ∧ walkSum ω k = -1} := by
  by_cases h : ∃ n, x ∈ SBar k n
  · obtain ⟨n, hn⟩ := h
    rw [E_eq hn hi, prob_F μ hn, prob_rot μ hn, ← mul_assoc, one_div,
      ENNReal.inv_mul_cancel (by exact_mod_cast (by omega : k ≠ 0)) (ENNReal.natCast_ne_top k),
      one_mul]
  · push Not at h
    rw [E_empty' hk h, F_empty hk h]
    simp

theorem vervaat_prob_eq (μ : Measure ℕ) [IsProbabilityMeasure μ] {k n : ℕ} {x : List ℤ}
    (hx : x ∈ SBar k n) :
    𝐏w[μ] {ω | vervaat (walkWord ω k) = x} = (k : ℝ≥0∞) * 𝐏w[μ] {ω | walkWord ω k = x} := by
  rw [← prob_F μ hx]
  congr 1
  ext ω
  simp only [Set.mem_ofPred_eq]
  constructor
  · intro h
    refine ⟨h, ?_⟩
    rw [← sum_walkWord, ← sum_vervaat, h]
    exact hx.2.2.1
  · exact fun h => h.1


theorem prob_A_inter_idx (μ : Measure ℕ) [IsProbabilityMeasure μ] {k : ℕ} (hk : 1 ≤ k)
    {i : ℕ} (hi : 1 ≤ i ∧ i ≤ k) :
    𝐏w[μ] ({ω : ℕ → ℕ | walkSum ω k = -1} ∩ {ω | vervaatIdx (walkWord ω k) = i}) =
      (1 / (k : ℝ≥0∞)) * 𝐏w[μ] {ω | walkSum ω k = -1} := by
  have h1 : {ω : ℕ → ℕ | walkSum ω k = -1} ∩ {ω | vervaatIdx (walkWord ω k) = i} =
      ⋃ x : List ℤ, {ω : ℕ → ℕ | vervaatIdx (walkWord ω k) = i ∧ vervaat (walkWord ω k) = x ∧
        walkSum ω k = -1} := by
    ext ω
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨vervaat (walkWord ω k), h2, rfl, h1⟩
    · rintro ⟨x, h2, -, h1⟩; exact ⟨h1, h2⟩
  have h2 : {ω : ℕ → ℕ | walkSum ω k = -1} =
      ⋃ x : List ℤ, {ω : ℕ → ℕ | vervaat (walkWord ω k) = x ∧ walkSum ω k = -1} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
    constructor
    · intro h; exact ⟨vervaat (walkWord ω k), rfl, h⟩
    · rintro ⟨x, -, h⟩; exact h
  have h3 : 𝐏w[μ] {ω : ℕ → ℕ | walkSum ω k = -1} =
      ∑' x : List ℤ, 𝐏w[μ] {ω : ℕ → ℕ | vervaat (walkWord ω k) = x ∧ walkSum ω k = -1} := by
    rw [h2]
    refine measure_iUnion (fun x y hxy => ?_) (fun x => measurableSet_F hk x)
    refine Set.disjoint_left.mpr (fun ω h1 h2 => hxy ?_)
    exact h1.1.symm.trans h2.1
  rw [h1, measure_iUnion (fun x y hxy => ?_) (fun x => measurableSet_E hk x i)]
  · simp_rw [lem_cool_i_joint μ hk hi]
    rw [ENNReal.tsum_mul_left, h3]
  · refine Set.disjoint_left.mpr (fun ω h1 h2 => hxy ?_)
    exact h1.2.1.symm.trans h2.2.1

theorem lem_cool_i (μ : Measure ℕ) [IsProbabilityMeasure μ] {k : ℕ} (hk : 1 ≤ k)
    (hpos : 𝐏w[μ] {ω | walkSum ω k = -1} ≠ 0) :
    (∀ i : ℕ, ((𝐏w[μ])[|{ω | walkSum ω k = -1}]) {ω | vervaatIdx (walkWord ω k) = i} =
        if 1 ≤ i ∧ i ≤ k then 1 / (k : ℝ≥0∞) else 0) ∧
      (∀ (i : ℕ) (x : List ℤ),
        ((𝐏w[μ])[|{ω | walkSum ω k = -1}])
            {ω | vervaatIdx (walkWord ω k) = i ∧ vervaat (walkWord ω k) = x} =
          ((𝐏w[μ])[|{ω | walkSum ω k = -1}]) {ω | vervaatIdx (walkWord ω k) = i} *
            ((𝐏w[μ])[|{ω | walkSum ω k = -1}]) {ω | vervaat (walkWord ω k) = x}) := by
  have hA := measurableSet_A k
  have hPA : 𝐏w[μ] {ω : ℕ → ℕ | walkSum ω k = -1} ≠ ⊤ := measure_ne_top _ _
  have hP1 : ∀ i : ℕ, ((𝐏w[μ])[|{ω | walkSum ω k = -1}])
      {ω | vervaatIdx (walkWord ω k) = i} = if 1 ≤ i ∧ i ≤ k then 1 / (k : ℝ≥0∞) else 0 := by
    intro i
    rw [cond_apply hA]
    by_cases hi : 1 ≤ i ∧ i ≤ k
    · rw [ite_eq_left hi, prob_A_inter_idx μ hk hi, mul_left_comm,
        ENNReal.inv_mul_cancel hpos hPA, mul_one]
    · rw [ite_eq_right hi]
      have : {ω : ℕ → ℕ | walkSum ω k = -1} ∩ {ω | vervaatIdx (walkWord ω k) = i} = ∅ := by
        ext ω
        simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
        rintro ⟨-, h⟩
        exact hi (h ▸ idx_range hk ω)
      rw [this]; simp
  refine ⟨hP1, fun i x => ?_⟩
  rw [hP1 i, cond_apply hA, cond_apply hA]
  have e1 : {ω : ℕ → ℕ | walkSum ω k = -1} ∩
      {ω | vervaatIdx (walkWord ω k) = i ∧ vervaat (walkWord ω k) = x} =
      {ω : ℕ → ℕ | vervaatIdx (walkWord ω k) = i ∧ vervaat (walkWord ω k) = x ∧
        walkSum ω k = -1} := by
    ext ω
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
    tauto
  have e2 : {ω : ℕ → ℕ | walkSum ω k = -1} ∩ {ω | vervaat (walkWord ω k) = x} =
      {ω : ℕ → ℕ | vervaat (walkWord ω k) = x ∧ walkSum ω k = -1} := by
    ext ω
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
    tauto
  rw [e1, e2]
  by_cases hi : 1 ≤ i ∧ i ≤ k
  · rw [ite_eq_left hi, lem_cool_i_joint μ hk hi x]
    ring
  · rw [ite_eq_right hi, zero_mul, E_empty hk x hi]
    simp

/-! ## 6.4 (ii) -/

theorem getD_walkWord {k : ℕ} (hk : 1 ≤ k) (ω : ℕ → ℕ) :
    (walkWord ω k).getD (k - 1) 0 = (ω (k - 1) : ℤ) - 1 := by
  have h : k - 1 < (walkWord ω k).length := by rw [length_walkWord]; omega
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, Option.getD_some,
    getElem_walkWord]

theorem cyl_inter (μ : Measure ℕ) [IsProbabilityMeasure μ] {k : ℕ} (hk : 1 ≤ k)
    (y : List ℤ) :
    𝐏w[μ] ({ω : ℕ → ℕ | walkWord ω k = y} ∩ {ω | ω (k - 1) = 0}) =
      if y.getD (k - 1) 0 = -1 then 𝐏w[μ] {ω | walkWord ω k = y} else 0 := by
  by_cases h : y.getD (k - 1) 0 = -1
  · rw [ite_eq_left h]
    congr 1
    ext ω
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
    constructor
    · exact fun a => a.1
    · intro a
      refine ⟨a, ?_⟩
      have := getD_walkWord hk ω
      rw [a, h] at this
      omega
  · rw [ite_eq_right h]
    have : {ω : ℕ → ℕ | walkWord ω k = y} ∩ {ω | ω (k - 1) = 0} = ∅ := by
      ext ω
      simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨a, b⟩
      have := getD_walkWord hk ω
      rw [a, b] at this
      apply h
      rw [this]; simp
    rw [this]; simp

theorem count_eq_card (l : List ℤ) (a : ℤ) :
    l.count a = ((Finset.range l.length).filter (fun m => l.getD m 0 = a)).card := by
  induction l with
  | nil => simp
  | cons b t ih =>
    rw [Finset.card_filter] at ih ⊢
    rw [List.count_cons, ih, List.length_cons, Finset.sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    simp [beq_iff_eq]

theorem getD_rotate_last {x : List ℤ} {k : ℕ} (hl : x.length = k) (hk : 1 ≤ k) (j : ℕ) :
    (x.rotate j).getD (k - 1) 0 = x.getD ((k - 1 + j) % k) 0 := by
  have h : k - 1 < x.length := by omega
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_rotate h, hl]

theorem sum_rotate_last (w : ℝ≥0∞) {x : List ℤ} {k : ℕ} (hl : x.length = k) (hk : 1 ≤ k) :
    ∑ i ∈ Finset.Icc 1 k, (if (x.rotate (k - i)).getD (k - 1) 0 = -1 then w else 0) =
      (x.count (-1) : ℝ≥0∞) * w := by
  have hσ : ∀ i ∈ Finset.Icc 1 k, (k - 1 + (k - i)) % k = if i = k then k - 1 else k - 1 - i := by
    intro i hi
    rw [Finset.mem_Icc] at hi
    split_ifs with h
    · subst h
      rw [Nat.sub_self, Nat.add_zero, Nat.mod_eq_of_lt (by omega)]
    · have : k - 1 + (k - i) = (k - 1 - i) + k := by omega
      rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  have step1 : ∑ i ∈ Finset.Icc 1 k, (if (x.rotate (k - i)).getD (k - 1) 0 = -1 then w else 0) =
      ∑ m ∈ Finset.range k, (if x.getD m 0 = -1 then w else 0) := by
    rw [Finset.sum_congr rfl (fun i hi => by rw [getD_rotate_last hl hk, hσ i hi])]
    refine Finset.sum_nbij' (fun i => if i = k then k - 1 else k - 1 - i)
      (fun m => if m = k - 1 then k else k - 1 - m) ?_ ?_ ?_ ?_ ?_
    · intro i hi
      rw [Finset.mem_Icc] at hi
      simp only [Finset.mem_range]
      split_ifs <;> omega
    · intro m hm
      simp only [Finset.mem_range] at hm
      simp only [Finset.mem_Icc]
      split_ifs <;> omega
    · intro i hi
      rw [Finset.mem_Icc] at hi
      split_ifs <;> omega
    · intro m hm
      simp only [Finset.mem_range] at hm
      split_ifs <;> omega
    · intro i hi
      rfl
  rw [step1, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, count_eq_card, hl]

theorem lem_cool_ii (μ : Measure ℕ) [IsProbabilityMeasure μ] {k n : ℕ} (hn : 1 ≤ n) (hkn : n ≤ k)
    {x : List ℤ} (hx : x ∈ SBar k n) :
    𝐏w[μ] {ω | vervaat (walkWord ω k) = x ∧ ω (k - 1) = 0} =
      ((n : ℝ≥0∞) / k) * 𝐏w[μ] {ω | vervaat (walkWord ω k) = x} := by
  have _ := hn
  have _ := hkn
  have hk := one_le_of_SBar hx
  rw [vervaat_prob_eq μ hx]
  have hset : {ω : ℕ → ℕ | vervaat (walkWord ω k) = x ∧ ω (k - 1) = 0} =
      ⋃ i ∈ Finset.Icc 1 k, ({ω : ℕ → ℕ | walkWord ω k = x.rotate (k - i)} ∩
        {ω | ω (k - 1) = 0}) := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff, Finset.mem_Icc, exists_prop]
    constructor
    · rintro ⟨h1, h2⟩
      have hW : walkSum ω k = -1 := by
        rw [← sum_walkWord, ← sum_vervaat, h1]; exact hx.2.2.1
      have hi := idx_range hk ω
      refine ⟨vervaatIdx (walkWord ω k), hi, ?_, h2⟩
      have hm : ω ∈ {ω : ℕ → ℕ | vervaatIdx (walkWord ω k) = vervaatIdx (walkWord ω k) ∧
        vervaat (walkWord ω k) = x ∧ walkSum ω k = -1} := ⟨rfl, h1, hW⟩
      exact (E_eq hx hi).subset hm
    · rintro ⟨i, hi, h1, h2⟩
      obtain ⟨-, b, -, -⟩ := good_of_rot hx (j := k - i) (by omega) h1
      exact ⟨b, h2⟩
  have hC : MeasurableSet {ω : ℕ → ℕ | ω (k - 1) = 0} :=
    (measurable_pi_apply (k - 1)) (measurableSet_singleton 0)
  rw [hset, measure_biUnion_finset]
  · have hlen : ∀ i ∈ Finset.Icc 1 k, (x.rotate (k - i)).length = k := fun i _ => by
      simp [hx.1]
    rw [Finset.sum_congr rfl (fun i hi => cyl_inter μ hk (x.rotate (k - i))),
      Finset.sum_congr rfl (fun i hi => by rw [prob_rot μ hx (k - i)]),
      sum_rotate_last _ hx.1 hk]
    have hk0 : (k : ℝ≥0∞) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
    have hkT : (k : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top k
    rw [hx.2.2.2.1, div_eq_mul_inv]
    calc (n : ℝ≥0∞) * 𝐏w[μ] {ω | walkWord ω k = x}
        = (n : ℝ≥0∞) * ((k : ℝ≥0∞)⁻¹ * k) * 𝐏w[μ] {ω | walkWord ω k = x} := by
          rw [ENNReal.inv_mul_cancel hk0 hkT, mul_one]
      _ = _ := by ring
  · intro i hi j hj hij
    have hi' := Finset.mem_Icc.1 (Finset.mem_coe.1 hi)
    have hj' := Finset.mem_Icc.1 (Finset.mem_coe.1 hj)
    refine Set.disjoint_left.mpr (fun ω h1 h2 => hij ?_)
    obtain ⟨a, -, -, -⟩ := good_of_rot hx (j := k - i) (by omega) h1.1
    obtain ⟨b, -, -, -⟩ := good_of_rot hx (j := k - j) (by omega) h2.1
    omega
  · exact fun i _ => (measurableSet_walkWord_eq k _).inter hC

end BGWLeaves.Vervaat.Cyclic
