/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module
public import BGW.Probability.PoissonCharacterizationCauchy
public import Mathlib.Order.Interval.Set.Union
public import Mathlib.MeasureTheory.Measure.Real

/-! Dyadic separation of distinct arrivals and the small-window multiple-arrival estimate. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal BigOperators

namespace BGW.Probability

variable {Ω M : Type*} [MeasurableSpace Ω] [MeasurableSpace M]
variable {P : Measure Ω} [IsProbabilityMeasure P] {ξ : Ω → Measure (ℝ≥0 × M)} {A : Set M}

/-- A counting measure assigning mass greater than one contains two distinct points. -/
lemma exists_ne_of_one_lt_count {μ : Measure (ℝ≥0 × M)} {S : Set (ℝ≥0 × M)}
    (hμ : μ = Measure.sum (fun p : S => Measure.dirac (p : ℝ≥0 × M)))
    {B : Set (ℝ≥0 × M)} (hB : MeasurableSet B) (h : 1 < μ B) :
    ∃ p q : S, p ≠ q ∧ (p : ℝ≥0 × M) ∈ B ∧ (q : ℝ≥0 × M) ∈ B := by
  rw [hμ, Measure.sum_apply _ hB] at h
  have hex : ∃ p : S, (p : ℝ≥0 × M) ∈ B := by
    by_contra hn
    push Not at hn
    have hz : (Measure.sum (fun p : S => Measure.dirac (p : ℝ≥0 × M))) B = 0 := by
      rw [hμ, Measure.sum_apply _ hB] at *
      simp [Measure.dirac_apply' _ hB, hn]
    rw [Measure.sum_apply _ hB] at hz
    rw [hz] at h
    exact (not_lt_of_ge zero_le_one) h
  obtain ⟨p, hp⟩ := hex
  have hpterm : Measure.dirac (p : ℝ≥0 × M) B = 1 := by
    simp [Measure.dirac_apply' _ hB, hp]
  by_contra hn
  have hall : ∀ q : S, q ≠ p → Measure.dirac (q : ℝ≥0 × M) B = 0 := by
    intro q hqp
    have hq : (q : ℝ≥0 × M) ∉ B := by
      intro hq
      exact hn ⟨p, q, Ne.symm hqp, hp, hq⟩
    simp [Measure.dirac_apply' _ hB, hq]
  have hsingle : (∑' q : S, Measure.dirac (q : ℝ≥0 × M) B) = 1 := by
    rw [tsum_eq_single p hall, hpterm]
  rw [hsingle] at h
  exact lt_irrefl 1 h

/-- The left endpoint of cell `i` in a uniform `n`-cell partition of `(0, h]`. -/
noncomputable def pointGridTime (h : ℝ≥0) (n i : ℕ) : ℝ≥0 := h * (i : ℝ≥0) / (n : ℝ≥0)

/-- The set of points in cell `i` of a uniform time partition and with mark in `A`. -/
noncomputable def gridBox (h : ℝ≥0) (n i : ℕ) (A : Set M) : Set (ℝ≥0 × M) :=
  Ioc (pointGridTime h n i) (pointGridTime h n (i + 1)) ×ˢ A

/-- The event that two different grid cells each contain an arrival. -/
def separatedDouble (ξ : Ω → Measure (ℝ≥0 × M)) (h : ℝ≥0) (n : ℕ)
    (A : Set M) : Set Ω :=
  {ω | ∃ i j : Fin n, i < j ∧ 1 ≤ ξ ω (gridBox h n i A) ∧ 1 ≤ ξ ω (gridBox h n j A)}

lemma pointGridTime_monotone (h : ℝ≥0) {n : ℕ} (hn : n ≠ 0) : Monotone (pointGridTime h n) := by
  intro i j hij
  dsimp [pointGridTime]
  gcongr

lemma pointGridTime_start (h : ℝ≥0) (n : ℕ) : pointGridTime h n 0 = 0 := by
  simp [pointGridTime]

lemma pointGridTime_end (h : ℝ≥0) {n : ℕ} (hn : n ≠ 0) : pointGridTime h n n = h := by
  simp [pointGridTime, hn]

lemma pointGridTime_width (h : ℝ≥0) {n i : ℕ} (hn : n ≠ 0) :
    pointGridTime h n (i + 1) - pointGridTime h n i = h / (n : ℝ≥0) := by
  have hna : (n : ℝ≥0) ≠ 0 := by exact_mod_cast hn
  apply tsub_eq_of_eq_add
  rw [pointGridTime, pointGridTime]
  field_simp [hna]
  push_cast
  ring

lemma exists_grid_box {h : ℝ≥0} {n : ℕ} (hn : n ≠ 0) {x : ℝ≥0} (hx : x ∈ Ioc 0 h) :
    ∃ i : Fin n, x ∈ Ioc (pointGridTime h n i) (pointGridTime h n (i + 1)) := by
  have he : Ioc (pointGridTime h n 0) (pointGridTime h n n) = Ioc 0 h := by
    rw [pointGridTime_start, pointGridTime_end h hn]
  have hx' : x ∈ Ioc (pointGridTime h n 0) (pointGridTime h n n) := he.symm ▸ hx
  have hcov := Ioc_subset_biUnion_Ioc n (pointGridTime h n) hx'
  obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp hcov
  exact ⟨⟨i, Finset.mem_range.mp hi⟩, hxi⟩

private lemma one_lt_count_of_two_ne {μ : Measure (ℝ≥0 × M)} {S : Set (ℝ≥0 × M)}
    (hμ : μ = Measure.sum (fun p : S => Measure.dirac (p : ℝ≥0 × M)))
    {B : Set (ℝ≥0 × M)} (hB : MeasurableSet B) {p q : S} (hpq : p ≠ q)
    (hp : (p : ℝ≥0 × M) ∈ B) (hq : (q : ℝ≥0 × M) ∈ B) : 1 < μ B := by
  classical
  rw [hμ, Measure.sum_apply _ hB]
  have hpterm : Measure.dirac (p : ℝ≥0 × M) B = 1 := by simp [Measure.dirac_apply' _ hB, hp]
  have hqterm : Measure.dirac (q : ℝ≥0 × M) B = 1 := by simp [Measure.dirac_apply' _ hB, hq]
  calc
    1 < (2 : ℝ≥0∞) := ENNReal.one_lt_two
    _ = ∑ x ∈ ({p, q} : Finset S), Measure.dirac (x : ℝ≥0 × M) B := by
      rw [Finset.sum_pair hpq, hpterm, hqterm]
      rw [← one_add_one_eq_two]
    _ ≤ _ := ENNReal.sum_le_tsum _

private lemma one_le_count_of_mem {μ : Measure (ℝ≥0 × M)} {S : Set (ℝ≥0 × M)}
    (hμ : μ = Measure.sum (fun p : S => Measure.dirac (p : ℝ≥0 × M)))
    {B : Set (ℝ≥0 × M)} (hB : MeasurableSet B) {p : S}
    (hp : (p : ℝ≥0 × M) ∈ B) : 1 ≤ μ B := by
  calc
    1 = Measure.dirac (p : ℝ≥0 × M) B := by simp [Measure.dirac_apply' _ hB, hp]
    _ ≤ _ := by
      rw [hμ]
      exact (Measure.le_sum (fun q : S => Measure.dirac (q : ℝ≥0 × M)) p) B

lemma pointGridTime_two_even (h : ℝ≥0) {n : ℕ} (hn : n ≠ 0) (i : ℕ) :
    pointGridTime h (2 * n) (2 * i) = pointGridTime h n i := by
  have hn2 : (n : ℝ≥0) ≠ 0 := by exact_mod_cast hn
  rw [pointGridTime, pointGridTime]
  push_cast
  field_simp [hn2]

lemma pointGridTime_two_odd (h : ℝ≥0) {n : ℕ} (hn : n ≠ 0) (i : ℕ) :
    pointGridTime h (2 * n) (2 * i + 1) =
      (pointGridTime h n i + pointGridTime h n (i + 1)) / 2 := by
  have hn2 : (n : ℝ≥0) ≠ 0 := by exact_mod_cast hn
  rw [pointGridTime, pointGridTime, pointGridTime]
  push_cast
  field_simp [hn2]
  ring

lemma exists_mem_of_one_le_count {μ : Measure (ℝ≥0 × M)} {S : Set (ℝ≥0 × M)}
    (hμ : μ = Measure.sum (fun p : S => Measure.dirac (p : ℝ≥0 × M)))
    {B : Set (ℝ≥0 × M)} (hB : MeasurableSet B) (h : 1 ≤ μ B) :
    ∃ p : S, (p : ℝ≥0 × M) ∈ B := by
  by_contra hn
  push Not at hn
  have hz : μ B = 0 := by
    rw [hμ, Measure.sum_apply _ hB]
    simp [Measure.dirac_apply' _ hB, hn]
  rw [hz] at h
  simp at h

omit [MeasurableSpace Ω] in
lemma separatedDouble_subset_double {h : ℝ≥0} {n : ℕ} (hn : n ≠ 0)
    (hAm : MeasurableSet A) :
    separatedDouble ξ h n A ⊆ {ω | 2 ≤ ξ ω (Ioc 0 h ×ˢ A)} := by
  intro ω hω
  obtain ⟨i, j, hij, hi, hj⟩ := hω
  have hdisj : Disjoint (gridBox h n i A) (gridBox h n j A) := by
    apply Set.disjoint_left.2
    intro p hp hq
    have hle : pointGridTime h n (i + 1) ≤ pointGridTime h n j :=
      pointGridTime_monotone h hn (by omega)
    exact (not_lt_of_ge (hp.1.2.trans hle)) hq.1.1
  have hsub (k : Fin n) : gridBox h n k A ⊆ Ioc 0 h ×ˢ A := by
    apply Set.prod_mono _ Subset.rfl
    intro x hx
    exact ⟨(pointGridTime_start h n ▸ pointGridTime_monotone h hn (Nat.zero_le k)).trans_lt hx.1,
      hx.2.trans (by simpa [pointGridTime_end h hn] using
        pointGridTime_monotone h hn (show k + 1 ≤ n by omega))⟩
  calc
    2 = (1 : ℝ≥0∞) + 1 := by rw [← one_add_one_eq_two]
    _ ≤ ξ ω (gridBox h n i A) + ξ ω (gridBox h n j A) := by gcongr
    _ = ξ ω (gridBox h n i A ∪ gridBox h n j A) :=
      (measure_union hdisj (measurableSet_Ioc.prod hAm)).symm
    _ ≤ ξ ω (Ioc 0 h ×ˢ A) := measure_mono (union_subset (hsub i) (hsub j))

omit [IsProbabilityMeasure P] in
lemma ae_double_eq_iUnion_separated (hξ : IsTimeSimpleLevy P ξ) (hA : IsFiniteRate P ξ A)
    (h : ℝ≥0) : {ω | 2 ≤ ξ ω (Ioc 0 h ×ˢ A)} =ᵐ[P]
      ⋃ N : ℕ, separatedDouble ξ h (2 ^ N) A := by
  filter_upwards [hξ.counting, hξ.timeSimple] with ω hcount htime
  obtain ⟨S, hS, hμ⟩ := hcount
  apply propext
  constructor
  · intro hdouble
    obtain ⟨p, q, hpq, hpB, hqB⟩ := exists_ne_of_one_lt_count hμ (measurable_box hA.1)
      (ENNReal.one_lt_two.trans_le hdouble)
    have hpS : (p : ℝ≥0 × M) ∈ Ioc 0 h ×ˢ A := hpB
    have hqS : (q : ℝ≥0 × M) ∈ Ioc 0 h ×ˢ A := hqB
    have hpqt : (p : ℝ≥0 × M).1 ≠ (q : ℝ≥0 × M).1 := by
      intro heq
      have hb : MeasurableSet ({(p : ℝ≥0 × M).1} ×ˢ (univ : Set M)) :=
        (measurableSet_singleton _).prod MeasurableSet.univ
      have hp : (p : ℝ≥0 × M) ∈ {(p : ℝ≥0 × M).1} ×ˢ univ := by simp
      have hq : (q : ℝ≥0 × M) ∈ {(p : ℝ≥0 × M).1} ×ˢ univ := by simp [heq]
      exact (not_lt_of_ge (htime _)) (one_lt_count_of_two_ne hμ hb hpq hp hq)
    have hsep : ∀ u v : S, (u : ℝ≥0 × M).1 < (v : ℝ≥0 × M).1 →
        (u : ℝ≥0 × M) ∈ Ioc 0 h ×ˢ A →
        (v : ℝ≥0 × M) ∈ Ioc 0 h ×ˢ A → ∃ N : ℕ,
          ω ∈ separatedDouble ξ h (2 ^ N) A := by
      intro u v huv hu hv
      let gap : ℝ≥0 := (v : ℝ≥0 × M).1 - (u : ℝ≥0 × M).1
      have hgap : 0 < gap := tsub_pos_iff_lt.2 huv
      obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt (R := ℝ≥0)
        (h / gap) (one_lt_two)
      have hN' : h / (2 ^ N : ℝ≥0) < gap := by
        apply (div_lt_iff₀ (by positivity : (0 : ℝ≥0) < 2 ^ N)).2
        have := (div_lt_iff₀ hgap).1 hN
        simpa [mul_comm] using this
      have hn : 2 ^ N ≠ 0 := by positivity
      obtain ⟨i, hi⟩ := exists_grid_box hn hu.1
      obtain ⟨j, hj⟩ := exists_grid_box hn hv.1
      have hij : i < j := by
        rcases lt_trichotomy i j with hij | hij | hij
        · exact hij
        · subst i
          have hle : (v : ℝ≥0 × M).1 - (u : ℝ≥0 × M).1 ≤
              pointGridTime h (2 ^ N) (j + 1) - pointGridTime h (2 ^ N) j :=
            tsub_le_tsub hj.2 hi.1.le
          rw [pointGridTime_width h (n := 2 ^ N) (i := j) hn] at hle
          have hle' : gap ≤ h / (2 ^ N : ℝ≥0) := by simpa [gap] using hle
          exact False.elim ((not_le_of_gt hN') hle')
        · have hle : pointGridTime h (2 ^ N) (j + 1) ≤ pointGridTime h (2 ^ N) i :=
            pointGridTime_monotone h hn (by omega)
          have hvu : (v : ℝ≥0 × M).1 < (u : ℝ≥0 × M).1 :=
            (hj.2.trans hle).trans_lt hi.1
          exact False.elim ((not_lt_of_ge hvu.le) huv)
      exact ⟨N, i, j, hij, one_le_count_of_mem hμ (measurableSet_Ioc.prod hA.1) ⟨hi, hu.2⟩,
        one_le_count_of_mem hμ (measurableSet_Ioc.prod hA.1) ⟨hj, hv.2⟩⟩
    rcases lt_or_gt_of_ne hpqt with hpq' | hqp'
    · exact mem_iUnion.2 (hsep p q hpq' hpS hqS)
    · exact mem_iUnion.2 (hsep q p hqp' hqS hpS)
  · intro hω
    obtain ⟨N, hN⟩ := mem_iUnion.1 hω
    exact separatedDouble_subset_double (ξ := ξ) (A := A) (by positivity) hA.1 hN

/-- The nonzero-arrival version of `separatedDouble`, useful for exact refinement. -/
def separatedDoubleNE (ξ : Ω → Measure (ℝ≥0 × M)) (h : ℝ≥0) (n : ℕ)
    (A : Set M) : Set Ω :=
  {ω | ∃ i j : Fin n, i < j ∧ ξ ω (gridBox h n i A) ≠ 0 ∧ ξ ω (gridBox h n j A) ≠ 0}

omit [MeasurableSpace Ω] in
lemma separatedDouble_subset_NE {h : ℝ≥0} {n : ℕ} :
    separatedDouble ξ h n A ⊆ separatedDoubleNE ξ h n A := by
  intro ω hω
  obtain ⟨i, j, hij, hi, hj⟩ := hω
  exact ⟨i, j, hij, (zero_lt_one.trans_le hi).ne', (zero_lt_one.trans_le hj).ne'⟩

lemma gridBox_split (h : ℝ≥0) (_hAm : MeasurableSet A) {n : ℕ} (hn : n ≠ 0) (i : Fin n) :
    gridBox h n i A = gridBox h (2 * n) (2 * i) A ∪ gridBox h (2 * n) (2 * i + 1) A := by
  ext p
  simp only [gridBox, mem_union, mem_prod, mem_Ioc, pointGridTime_two_even h hn,
    pointGridTime_two_odd h hn]
  have heven : pointGridTime h (2 * n) (2 * i + 2) = pointGridTime h n (i + 1) := by
    convert pointGridTime_two_even h hn (i + 1) using 1
  rw [heven]
  have hle : pointGridTime h n i ≤ pointGridTime h n (i + 1) :=
    pointGridTime_monotone h hn (Nat.le_succ i)
  have hmid_le :
      (pointGridTime h n i + pointGridTime h n (i + 1)) / 2 ≤ pointGridTime h n (i + 1) :=
    (div_le_iff₀ (by norm_num : (0 : ℝ≥0) < 2)).2 (by
      rw [mul_two]
      exact add_le_add hle (le_refl _))
  have hle_mid : pointGridTime h n i ≤ (pointGridTime h n i + pointGridTime h n (i + 1)) / 2 :=
    (le_div_iff₀ (by norm_num : (0 : ℝ≥0) < 2)).2 (by
      rw [mul_two]
      exact add_le_add (le_refl _) hle)
  constructor
  · rintro ⟨hi, hpA⟩
    by_cases hmid : p.1 ≤ (pointGridTime h n i + pointGridTime h n (i + 1)) / 2
    · exact Or.inl ⟨⟨hi.1, hmid⟩, hpA⟩
    · exact Or.inr ⟨⟨lt_of_not_ge hmid, hi.2⟩, hpA⟩
  · rintro (⟨hi, hpA⟩ | ⟨hi, hpA⟩)
    · exact ⟨⟨hi.1, hi.2.trans hmid_le⟩, hpA⟩
    · exact ⟨⟨hle_mid.trans_lt hi.1, hi.2⟩, hpA⟩

omit [MeasurableSpace Ω] in
lemma separatedDoubleNE_mono_two (h : ℝ≥0) (hAm : MeasurableSet A) {n : ℕ} (hn : n ≠ 0) :
    separatedDoubleNE ξ h n A ⊆ separatedDoubleNE ξ h (2 * n) A := by
  intro ω hω
  obtain ⟨i, j, hij, hi, hj⟩ := hω
  have hsplit (k : Fin n) : ξ ω (gridBox h n k A) =
      ξ ω (gridBox h (2 * n) (2 * k) A) + ξ ω (gridBox h (2 * n) (2 * k + 1) A) := by
    rw [gridBox_split h hAm hn k, measure_union]
    · apply Set.disjoint_left.2
      intro p hp hq
      exact (not_lt_of_ge hp.1.2) hq.1.1
    · exact measurableSet_Ioc.prod hAm
  rw [hsplit i] at hi
  rw [hsplit j] at hj
  have hi' : ξ ω (gridBox h (2 * n) (2 * i) A) ≠ 0 ∨
      ξ ω (gridBox h (2 * n) (2 * i + 1) A) ≠ 0 := by
    by_contra hn'
    push Not at hn'
    exact hi (add_eq_zero.2 hn')
  have hj' : ξ ω (gridBox h (2 * n) (2 * j) A) ≠ 0 ∨
      ξ ω (gridBox h (2 * n) (2 * j + 1) A) ≠ 0 := by
    by_contra hn'
    push Not at hn'
    exact hj (add_eq_zero.2 hn')
  rcases hi' with hi' | hi' <;> rcases hj' with hj' | hj'
  · exact ⟨⟨2 * i, by omega⟩, ⟨2 * j, by omega⟩,
      by apply Fin.lt_def.2; dsimp; omega, hi', hj'⟩
  · exact ⟨⟨2 * i, by omega⟩, ⟨2 * j + 1, by omega⟩,
      by apply Fin.lt_def.2; dsimp; omega, hi', hj'⟩
  · exact ⟨⟨2 * i + 1, by omega⟩, ⟨2 * j, by omega⟩,
      by apply Fin.lt_def.2; dsimp; omega, hi', hj'⟩
  · exact ⟨⟨2 * i + 1, by omega⟩, ⟨2 * j + 1, by omega⟩,
      by apply Fin.lt_def.2; dsimp; omega, hi', hj'⟩

omit [MeasurableSpace Ω] in
lemma separatedDoubleNE_mono (h : ℝ≥0) (hAm : MeasurableSet A) :
    Monotone (fun N : ℕ => separatedDoubleNE ξ h (2 ^ N) A) := by
  intro m n hmn
  induction hmn with
  | refl => exact Subset.rfl
  | @step n hmn ih =>
      exact ih.trans (by
        simpa [pow_succ, mul_comm] using separatedDoubleNE_mono_two (ξ := ξ) (A := A)
          (n := 2 ^ n) h hAm (pow_ne_zero n (by norm_num : (2 : ℕ) ≠ 0)))

omit [IsProbabilityMeasure P] in
lemma ae_double_eq_iUnion_separatedNE (hξ : IsTimeSimpleLevy P ξ)
    (hA : IsFiniteRate P ξ A) (h : ℝ≥0) : {ω | 2 ≤ ξ ω (Ioc 0 h ×ˢ A)} =ᵐ[P]
      ⋃ N : ℕ, separatedDoubleNE ξ h (2 ^ N) A := by
  filter_upwards [ae_double_eq_iUnion_separated hξ hA h, hξ.counting] with ω hdouble hcount
  obtain ⟨S, _hS, hμ⟩ := hcount
  apply propext
  constructor
  · intro hω
    obtain ⟨N, hN⟩ := mem_iUnion.1 (hdouble.mp hω)
    exact mem_iUnion.2 ⟨N, separatedDouble_subset_NE hN⟩
  · intro hω
    apply hdouble.mpr
    obtain ⟨N, hN⟩ := mem_iUnion.1 hω
    obtain ⟨i, j, hij, hi, hj⟩ := hN
    exact mem_iUnion.2 ⟨N, i, j, hij,
      one_le_count_of_ne_zero hμ (measurableSet_Ioc.prod hA.1) hi,
      one_le_count_of_ne_zero hμ (measurableSet_Ioc.prod hA.1) hj⟩

lemma pointGridTime_succ_eq_add (h : ℝ≥0) {n i : ℕ} (hn : n ≠ 0) :
    pointGridTime h n (i + 1) = pointGridTime h n i + h / (n : ℝ≥0) := by
  have hle : pointGridTime h n i ≤ pointGridTime h n (i + 1) :=
    pointGridTime_monotone h hn (Nat.le_succ i)
  rw [← pointGridTime_width h (n := n) (i := i) hn]
  exact (add_tsub_cancel_of_le hle).symm

omit [IsProbabilityMeasure P] in
lemma prob_noMark_stationary (hξ : IsTimeSimpleLevy P ξ) (hA : IsFiniteRate P ξ A)
    (a h : ℝ≥0) : P {ω | ξ ω (Ioc a (a + h) ×ˢ A) = 0} =
      P {ω | ξ ω (Ioc 0 h ×ˢ A) = 0} := by
  let B : Set (ℝ≥0 × M) := Ioc 0 h ×ˢ A
  have hB : MeasurableSet B := measurableSet_Ioc.prod hA.1
  have hz : MeasurableSet {ν : Measure (ℝ≥0 × M) | ν B = 0} :=
    measurableSet_eq_fun (Measure.measurable_coe hB) measurable_const
  have heval := congrArg (fun Q : Measure (Measure (ℝ≥0 × M)) => Q {ν | ν B = 0})
    (hξ.stationary a h)
  rw [Measure.map_apply (measurable_windowShift hξ.measurable a (a + h)) hz,
    Measure.map_apply (measurable_windowShift hξ.measurable 0 h) hz] at heval
  have hleft : (fun ω => windowShift a (a + h) (ξ ω)) ⁻¹' {ν | ν B = 0} =
      {ω | ξ ω (Ioc a (a + h) ×ˢ A) = 0} := by
    ext ω
    simp only [mem_preimage, mem_ofPred_eq]
    change windowShift a (a + h) (ξ ω) (Ioc 0 h ×ˢ A) = 0 ↔ _
    rw [windowShift_box _ _ _ hA.1]
  have hright : (fun ω => windowShift 0 h (ξ ω)) ⁻¹' {ν | ν B = 0} =
      {ω | ξ ω (Ioc 0 h ×ˢ A) = 0} := by
    ext ω
    simp only [mem_preimage, mem_ofPred_eq]
    change windowShift 0 h (ξ ω) (Ioc 0 h ×ˢ A) = 0 ↔ _
    have hs := windowShift_box (ξ ω) 0 h hA.1
    simp only [zero_add] at hs
    rw [hs]
  rw [← hleft, ← hright]
  exact heval

omit [IsProbabilityMeasure P] in
lemma iIndep_grid_counts (hξ : IsTimeSimpleLevy P ξ) (hA : IsFiniteRate P ξ A)
    (h : ℝ≥0) {n : ℕ} (hn : n ≠ 0) :
    iIndepFun (fun i : Fin n => fun ω => ξ ω (gridBox h n i A)) P := by
  let t : Fin (n + 1) → ℝ≥0 := fun i => pointGridTime h n i
  have ht : Monotone t := by
    intro i j hij
    exact pointGridTime_monotone h hn (by exact_mod_cast hij)
  have hi := hξ.indep n t ht
  apply hi.comp (fun i μ => μ (gridBox h n i A))
    (fun i => Measure.measurable_coe (measurableSet_Ioc.prod hA.1)) |>.congr
  intro i
  apply Eventually.of_forall
  intro ω
  simp only [Function.comp_apply, t, windowRestrict, gridBox]
  rw [Measure.restrict_apply' (measurableSet_Ioc.prod MeasurableSet.univ)]
  change ξ ω ((Ioc (pointGridTime h n i) (pointGridTime h n (i + 1)) ×ˢ A) ∩
    (Ioc (pointGridTime h n i) (pointGridTime h n (i + 1)) ×ˢ univ)) = _
  rw [inter_eq_left.2 (Set.prod_mono Subset.rfl (subset_univ A))]

end BGW.Probability
