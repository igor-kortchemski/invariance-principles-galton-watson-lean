/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.Skorokhod.VervaatRotate
public import BGW.Tree.CycleLemma
import Mathlib.Topology.Algebra.Order.Floor

/-!
# Discrete Vervaat indices and step paths

Step paths include their terminal prefix sum. The discrete index is the first
minimizer among the nonempty prefixes, as in Definition 6.3 of the source.
-/

@[expose] public section

open Set Filter Topology

namespace BGW.Skorokhod

private theorem isCadlag_floor_step (k : ℕ) (v : ℕ → ℝ) :
    IsCadlag (fun t : Icc (0 : ℝ) 1 => v ⌊(k : ℝ) * t⌋₊) := by
  by_cases hk : k = 0
  · subst k
    simp
  have hkpos : (0 : ℝ) < k := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hk)
  let a : Icc (0 : ℝ) 1 → ℝ := fun t => k * t
  have ha : Continuous a := continuous_const.mul continuous_subtype_val
  have hmono : StrictMono a := fun s t h => mul_lt_mul_of_pos_left h hkpos
  constructor
  · intro t
    have ht : Tendsto a (𝓝[>] t) (𝓝[≥] (a t)) :=
      tendsto_nhdsWithin_iff.mpr ⟨ha.continuousAt.tendsto.mono_left nhdsWithin_le_nhds,
        by filter_upwards [self_mem_nhdsWithin] with s hs using (hmono hs).le⟩
    have hfloor := (tendsto_floor_right_pure_floor (a t)).comp ht
    simpa only [ContinuousWithinAt, Function.comp_def, Int.floor_toNat, a] using
      (tendsto_pure_nhds (fun j : ℤ => v j.toNat) ⌊a t⌋).comp hfloor
  · intro t
    have ht : Tendsto a (𝓝[<] t) (𝓝[<] (a t)) :=
      tendsto_nhdsWithin_iff.mpr ⟨ha.continuousAt.tendsto.mono_left nhdsWithin_le_nhds,
        by filter_upwards [self_mem_nhdsWithin] with s hs using hmono hs⟩
    have hfloor := (tendsto_floor_left_pure_ceil_sub_one (a t)).comp ht
    refine ⟨v (⌈a t⌉ - 1).toNat, ?_⟩
    simpa only [Function.comp_def, Int.floor_toNat] using
      (tendsto_pure_nhds (fun j : ℤ => v j.toNat) (⌈a t⌉ - 1)).comp hfloor

/-- The step path `t ↦ w_{⌊k t⌋} / B` of a word `x` of length `k`, where `w_j` is the sum of
the first `j` letters; its value at `1` is `w_k / B` (C33.5). -/
noncomputable def stepPath (x : List ℤ) (B : ℝ) : D 1 ℝ where
  toFun t := ((x.take ⌊(x.length : ℝ) * t⌋₊).sum : ℝ) / B
  isCadlag' := by
    exact isCadlag_floor_step x.length fun j => ((x.take j).sum : ℝ) / B

/-- The paper's discrete Vervaat index: the first `i ∈ [1, k]` at which the prefix sum `w_i`
attains `min_{1 ≤ j ≤ k} w_j` (C33.5); `0` for the empty word. -/
noncomputable def vervaatIndex (x : List ℤ) : ℕ :=
  sInf {i | 1 ≤ i ∧ i ≤ x.length ∧ ∀ j, 1 ≤ j → j ≤ x.length → (x.take i).sum ≤ (x.take j).sum}

private theorem vervaatIndex_spec (x : List ℤ) (hx : 0 < x.length) :
    1 ≤ vervaatIndex x ∧ vervaatIndex x ≤ x.length ∧
      ∀ j, 1 ≤ j → j ≤ x.length → (x.take (vervaatIndex x)).sum ≤ (x.take j).sum := by
  classical
  apply Nat.sInf_mem (s := {i | 1 ≤ i ∧ i ≤ x.length ∧
    ∀ j, 1 ≤ j → j ≤ x.length → (x.take i).sum ≤ (x.take j).sum})
  obtain ⟨i, hi, hmin⟩ := Finset.exists_min_image (Finset.Icc 1 x.length)
    (fun j => (x.take j).sum) ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, hx⟩⟩
  exact ⟨i, (Finset.mem_Icc.mp hi).1, (Finset.mem_Icc.mp hi).2,
    fun j hj hj' => hmin j (Finset.mem_Icc.mpr ⟨hj, hj'⟩)⟩

private theorem index_minimum {x : List ℤ}
    (hx : ∃ j, 1 ≤ j ∧ j ≤ x.length ∧ (x.take j).sum < 0) :
    (x.take (vervaatIndex x)).sum < 0 ∧
      (∀ j, j ≤ x.length → (x.take (vervaatIndex x)).sum ≤ (x.take j).sum) ∧
      ∀ j, j < vervaatIndex x →
        (x.take (vervaatIndex x)).sum + 1 ≤ (x.take j).sum := by
  obtain ⟨j, hj, hjlen, hjneg⟩ := hx
  obtain ⟨_, hilen, hmin⟩ := vervaatIndex_spec x (by omega)
  have hneg := (hmin j hj hjlen).trans_lt hjneg
  have hmin' (l : ℕ) (hl : l ≤ x.length) :
      (x.take (vervaatIndex x)).sum ≤ (x.take l).sum := by
    rcases Nat.eq_zero_or_pos l with rfl | hl0
    · simpa using hneg.le
    · exact hmin l hl0 hl
  refine ⟨hneg, hmin', ?_⟩
  intro l hl
  by_cases hl0 : l = 0
  · subst l
    simpa using (show (x.take (vervaatIndex x)).sum + 1 ≤ 0 by omega)
  · have hle := hmin' l (hl.le.trans hilen)
    have hne : (x.take (vervaatIndex x)).sum ≠ (x.take l).sum := by
      intro heq
      have hidx : vervaatIndex x ≤ l := Nat.sInf_le
        ⟨by omega, hl.le.trans hilen, fun k hk hk' => heq ▸ hmin k hk hk'⟩
      omega
    omega

private theorem iInf_stepPath {x : List ℤ}
    (hx : ∃ j, 1 ≤ j ∧ j ≤ x.length ∧ (x.take j).sum < 0)
    {B : ℝ} (hB : 0 < B) :
    (⨅ t, stepPath x B t) = ((x.take (vervaatIndex x)).sum : ℝ) / B := by
  have hex := hx
  obtain ⟨j, hj, hjlen, _⟩ := hex
  have hk : (0 : ℝ) < x.length := Nat.cast_pos.mpr (by omega)
  obtain ⟨_, hilen, _⟩ := vervaatIndex_spec x (by omega)
  have hmem : (vervaatIndex x : ℝ) / x.length ∈ Icc (0 : ℝ) 1 := by
    constructor
    · positivity
    · exact (div_le_one hk).mpr (by exact_mod_cast hilen)
  have hval : stepPath x B ⟨(vervaatIndex x : ℝ) / x.length, hmem⟩ =
      ((x.take (vervaatIndex x)).sum : ℝ) / B := by
    change ((x.take ⌊(x.length : ℝ) * ((vervaatIndex x : ℝ) / x.length)⌋₊).sum : ℝ) / B = _
    rw [mul_div_cancel₀ _ hk.ne', Nat.floor_natCast]
  apply le_antisymm
  · exact (ciInf_le (isBounded_range (stepPath x B)).bddBelow _).trans_eq hval
  · apply le_ciInf
    intro t
    change _ ≤ ((x.take ⌊(x.length : ℝ) * t⌋₊).sum : ℝ) / B
    apply (div_le_div_iff_of_pos_right hB).mpr
    exact_mod_cast (index_minimum hx).2.1 _ (Nat.floor_le_of_le
      (mul_le_of_le_one_right hk.le t.2.2))

/-- The minimizing time of a step path is the first minimizing prefix divided by the length. -/
theorem vervaatTime_stepPath {x : List ℤ}
    (hx : ∃ j, 1 ≤ j ∧ j ≤ x.length ∧ (x.take j).sum < 0)
    {B : ℝ} (hB : 0 < B) :
    (vervaatTime (stepPath x B) : ℝ) = (vervaatIndex x : ℝ) / x.length := by
  have hex := hx
  obtain ⟨j, hj, hjlen, _⟩ := hex
  have hk : (0 : ℝ) < x.length := Nat.cast_pos.mpr (by omega)
  obtain ⟨_, hilen, _⟩ := vervaatIndex_spec x (by omega)
  have hmem : (vervaatIndex x : ℝ) / x.length ∈ Icc (0 : ℝ) 1 := by
    constructor
    · positivity
    · exact (div_le_one hk).mpr (by exact_mod_cast hilen)
  let ti : Icc (0 : ℝ) 1 := ⟨(vervaatIndex x : ℝ) / x.length, hmem⟩
  have hval : stepPath x B ti = ((x.take (vervaatIndex x)).sum : ℝ) / B := by
    change ((x.take ⌊(x.length : ℝ) * ((vervaatIndex x : ℝ) / x.length)⌋₊).sum : ℝ) / B = _
    rw [mul_div_cancel₀ _ hk.ne', Nat.floor_natCast]
  have hle : vervaatTime (stepPath x B) ≤ ti := by
    apply vervaatTime_le
    apply le_antisymm
    · rw [iInf_stepPath hx hB]
      exact (min_le_right _ _).trans_eq hval
    · apply le_min
      · apply isClosed_Ici.mem_of_mapClusterPt (mapClusterPt_leftLim (stepPath x B) ti)
        exact Eventually.of_forall fun s => ciInf_le (isBounded_range (stepPath x B)).bddBelow s
      · exact ciInf_le (isBounded_range (stepPath x B)).bddBelow ti
  apply le_antisymm (show (vervaatTime (stepPath x B) : ℝ) ≤
    (vervaatIndex x : ℝ) / x.length from hle)
  by_contra! hlt
  let g := vervaatTime (stepPath x B)
  have hbound (s : Icc (0 : ℝ) 1) (hs : s ≤ g) :
      (((x.take (vervaatIndex x)).sum : ℝ) + 1) / B ≤ stepPath x B s := by
    have hks : (x.length : ℝ) * s < vervaatIndex x := by
      have hsg : (s : ℝ) ≤ g := hs
      have hgi : (g : ℝ) < (vervaatIndex x : ℝ) / x.length := hlt
      exact (lt_div_iff₀' hk).mp (hsg.trans_lt hgi)
    have hfloor : ⌊(x.length : ℝ) * s⌋₊ < vervaatIndex x :=
      (Nat.floor_lt (mul_nonneg hk.le s.2.1)).mpr hks
    change _ ≤ ((x.take ⌊(x.length : ℝ) * s⌋₊).sum : ℝ) / B
    apply (div_le_div_iff_of_pos_right hB).mpr
    exact_mod_cast (index_minimum hx).2.2 _ hfloor
  have hl : (((x.take (vervaatIndex x)).sum : ℝ) + 1) / B ≤
      Function.leftLim (stepPath x B) g := by
    apply isClosed_Ici.mem_of_mapClusterPt (mapClusterPt_leftLim (stepPath x B) g)
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact hbound s hs
  have hmin := min_leftLim_vervaatTime (stepPath x B)
  rw [iInf_stepPath hx hB] at hmin
  have hge := le_min hl (hbound g le_rfl)
  rw [hmin] at hge
  have hbad := (div_le_div_iff_of_pos_right hB).mp hge
  linarith

/-- Discrete correspondence: for a word whose prefix sums go below zero, the càdlàg Vervaat
map of its step path is the step path of its rotation at the Vervaat index (C33.5). -/
theorem vervaatD_stepPath {x : List ℤ} (hx : ∃ j, 1 ≤ j ∧ j ≤ x.length ∧ (x.take j).sum < 0)
    {B : ℝ} (hB : 0 < B) :
    vervaatD (stepPath x B) = stepPath (x.rotate (vervaatIndex x)) B := by
  have hex := hx
  obtain ⟨j, hj, hjlen, _⟩ := hex
  have hk : (0 : ℝ) < x.length := Nat.cast_pos.mpr (by omega)
  obtain ⟨_, hilen, _⟩ := vervaatIndex_spec x (by omega)
  apply BGW.Skorokhod.ext
  intro t
  have hkt : 0 ≤ (x.length : ℝ) * t := mul_nonneg hk.le t.2.1
  have hjlen' : ⌊(x.length : ℝ) * t⌋₊ ≤ x.length :=
    Nat.floor_le_of_le (mul_le_of_le_one_right hk.le t.2.2)
  have hadd : ⌊(x.length : ℝ) * ((vervaatIndex x : ℝ) / x.length + t)⌋₊ =
      vervaatIndex x + ⌊(x.length : ℝ) * t⌋₊ := by
    rw [mul_add, mul_div_cancel₀ _ hk.ne', add_comm, Nat.floor_add_natCast hkt, add_comm]
  have hsub : ⌊(x.length : ℝ) * ((vervaatIndex x : ℝ) / x.length + t - 1)⌋₊ =
      ⌊(x.length : ℝ) * t⌋₊ - (x.length - vervaatIndex x) := by
    rw [mul_sub, mul_one, Nat.floor_sub_natCast, hadd]
    omega
  have hzero : stepPath x B ⟨0, le_rfl, zero_le_one⟩ = 0 := by simp [stepPath]
  have hone : stepPath x B ⟨1, zero_le_one, le_rfl⟩ = (x.sum : ℝ) / B := by
    change ((x.take ⌊(x.length : ℝ) * 1⌋₊).sum : ℝ) / B = _
    rw [mul_one, Nat.floor_natCast, List.take_length]
  change (if (vervaatTime (stepPath x B) : ℝ) + t ≤ 1 then _ else _) = _
  rw [vervaatTime_stepPath hx hB, iInf_stepPath hx hB]
  split_ifs with ht
  · have hmem : (vervaatIndex x : ℝ) / x.length + t ∈ Icc (0 : ℝ) 1 :=
      ⟨add_nonneg (div_nonneg (Nat.cast_nonneg _) hk.le) t.2.1, ht⟩
    rw [projIcc_of_mem zero_le_one hmem]
    change ((x.take ⌊(x.length : ℝ) * ((vervaatIndex x : ℝ) / x.length + t)⌋₊).sum : ℝ) / B -
      ((x.take (vervaatIndex x)).sum : ℝ) / B =
        (((x.rotate (vervaatIndex x)).take ⌊((x.rotate (vervaatIndex x)).length : ℝ) * t⌋₊).sum : ℝ) / B
    rw [List.length_rotate, hadd, sum_take_rotate x hilen hjlen']
    have hjle : ⌊(x.length : ℝ) * t⌋₊ ≤ x.length - vervaatIndex x := by
      apply Nat.floor_le_of_le
      rw [Nat.cast_sub hilen]
      have hi := (div_le_iff₀' hk).mp (show (vervaatIndex x : ℝ) / x.length ≤ 1 - t by linarith)
      nlinarith
    rw [ite_eq_left hjle, Int.cast_sub, sub_div]
  · have hmem : (vervaatIndex x : ℝ) / x.length + t - 1 ∈ Icc (0 : ℝ) 1 := by
      constructor
      · linarith
      · have hi : (vervaatIndex x : ℝ) / x.length ≤ 1 :=
          (div_le_one hk).mpr (by exact_mod_cast hilen)
        linarith [t.2.2]
    rw [projIcc_of_mem zero_le_one hmem, hone, hzero, sub_zero]
    change ((x.take ⌊(x.length : ℝ) * ((vervaatIndex x : ℝ) / x.length + t - 1)⌋₊).sum : ℝ) / B +
      (x.sum : ℝ) / B - ((x.take (vervaatIndex x)).sum : ℝ) / B =
        (((x.rotate (vervaatIndex x)).take ⌊((x.rotate (vervaatIndex x)).length : ℝ) * t⌋₊).sum : ℝ) / B
    rw [List.length_rotate, hsub, sum_take_rotate x hilen hjlen']
    split_ifs with hjle
    · have hjge : x.length - vervaatIndex x ≤ ⌊(x.length : ℝ) * t⌋₊ := by
        apply Nat.le_floor
        rw [Nat.cast_sub hilen]
        have hi : 1 - t < (vervaatIndex x : ℝ) / x.length := by linarith
        have hi' := (lt_div_iff₀' hk).mp hi
        nlinarith
      have heq := le_antisymm hjle hjge
      rw [heq, Nat.sub_self, List.take_zero, List.sum_nil, Int.cast_zero, zero_div, zero_add,
        show vervaatIndex x + (x.length - vervaatIndex x) = x.length by omega,
        List.take_length, Int.cast_sub, sub_div]
    · rw [Int.cast_add, Int.cast_sub, add_div, sub_div]
      ring

/-- For a bridge word, the rotation at the Vervaat index is a tree excursion (C33.5, in the
library's walk language). -/
theorem isTreeExcursion_rotate_vervaatIndex {n : ℕ} {x : List ℤ} (hx : x ∈ bridgeWords n) :
    IsTreeExcursion (x.rotate (vervaatIndex x)) := by
  classical
  obtain ⟨_, hletters, hsum⟩ := hx
  have hlen : 0 < x.length := by
    by_contra! h
    have he : x = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero h)
    simp [he] at hsum
  obtain ⟨hi0, hilen, hmin⟩ := vervaatIndex_spec x hlen
  have hstrict (j : ℕ) (hj : j < vervaatIndex x) :
      (x.take (vervaatIndex x)).sum + 1 ≤ (x.take j).sum := by
    by_cases hj0 : j = 0
    · subst j
      have h := hmin x.length hlen le_rfl
      simp only [List.take_length, hsum, List.take_zero, List.sum_nil] at h ⊢
      omega
    · have hjpos : 1 ≤ j := Nat.one_le_iff_ne_zero.mpr hj0
      have hle := hmin j hjpos (hj.le.trans hilen)
      have hne : (x.take (vervaatIndex x)).sum ≠ (x.take j).sum := by
        intro heq
        have hidx : vervaatIndex x ≤ j := Nat.sInf_le
          ⟨hjpos, hj.le.trans hilen, fun l hl hl' => heq ▸ hmin l hl hl'⟩
        omega
      omega
  refine ⟨fun a ha => hletters a (List.mem_rotate.mp ha),
    (List.rotate_perm x _).sum_eq.trans hsum, ?_⟩
  intro k hk
  rw [List.length_rotate] at hk
  rw [sum_take_rotate x hilen hk.le]
  split_ifs with h
  · have hle := hmin (vervaatIndex x + k) (by omega) (by omega)
    omega
  · have hj : k - (x.length - vervaatIndex x) < vervaatIndex x := by omega
    have hle := hstrict _ hj
    rw [hsum]
    omega

end BGW.Skorokhod
