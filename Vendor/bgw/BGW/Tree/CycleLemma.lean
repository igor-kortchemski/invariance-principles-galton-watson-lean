/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.Tree.WalkWeight
public import Mathlib.Data.List.Rotate
import Lean.Elab.Tactic.Omega

/-!
# The cycle lemma for Łukasiewicz bridges

A bridge word of length `n` has entries at least `-1` and sum `-1`. Writing `S j` for its prefix
sums, the rotation by `i < n` is a tree excursion exactly when `i` is the first index in `[0, n)` at
which `S` attains its minimum. Hence every bridge word has exactly one rotation that is a tree
excursion, and `(t, i) ↦ (increments t).rotate i` is a bijection from the pairs of a tree of size
`n` and an index `i < n` onto the bridge words of length `n`. Since rotating a word permutes its
entries, the walk weight is rotation invariant, and `n` times the total weight of the trees of
size `n` is the total walk weight of the bridge words. Adapted from
`PoissonDeclumping/Lukasiewicz/CyclicShift.lean`, with the library's prefix-sum excursions.
-/

@[expose] public section

namespace BGW

/-- Words of length `n` with all entries at least `-1` and total sum `-1`. -/
def bridgeWords (n : ℕ) : Set (List ℤ) :=
  {x | x.length = n ∧ (∀ a ∈ x, -1 ≤ a) ∧ x.sum = -1}

/-- Prefix sums of a rotation, in terms of prefix sums of the original word. -/
theorem sum_take_rotate (x : List ℤ) {i k : ℕ} (hi : i ≤ x.length)
    (hk : k ≤ x.length) :
    ((x.rotate i).take k).sum =
      if k ≤ x.length - i then (x.take (i + k)).sum - (x.take i).sum
      else x.sum - (x.take i).sum + (x.take (k - (x.length - i))).sum := by
  rw [List.rotate_eq_drop_append_take hi]
  split_ifs with h
  · rw [List.take_append_of_le_length (by simp; omega), List.take_drop]
    have := List.sum_take_add_sum_drop (x.take (i + k)) i
    rw [List.take_take, min_eq_left (by omega)] at this
    omega
  · rw [List.take_append, List.take_of_length_le (by simp; omega), List.sum_append,
      List.length_drop, List.take_take, min_eq_left (by omega)]
    have := List.sum_take_add_sum_drop x i
    omega

/-- The rotation of a bridge word by `i < n` is a tree excursion iff `i` is the first index in
`[0, n)` where the prefix sums attain their minimum. -/
private theorem isTreeExcursion_rotate_iff {x : List ℤ} {n : ℕ} (hx : x ∈ bridgeWords n)
    {i : ℕ} (hi : i < n) :
    IsTreeExcursion (x.rotate i) ↔
      (∀ j < i, (x.take i).sum + 1 ≤ (x.take j).sum) ∧
        ∀ j, i ≤ j → j < n → (x.take i).sum ≤ (x.take j).sum := by
  obtain ⟨hlen, hge, hsum⟩ := hx
  have hS0 : (x.take 0).sum = 0 := by simp
  have hSn : (x.take n).sum = -1 := by rw [← hlen, List.take_length]; exact hsum
  have hent : ∀ a ∈ x.rotate i, -1 ≤ a := fun a ha => hge a (List.mem_rotate.mp ha)
  have hs : (x.rotate i).sum = -1 := by rw [(List.rotate_perm x i).sum_eq]; exact hsum
  have hlen' : (x.rotate i).length = n := by simp [hlen]
  have key : ∀ k, k < n → ((x.rotate i).take k).sum =
      if k ≤ n - i then (x.take (i + k)).sum - (x.take i).sum
      else -1 - (x.take i).sum + (x.take (k - (n - i))).sum := by
    intro k hk
    rw [sum_take_rotate x (by omega) (by omega), hsum, hlen]
  unfold IsTreeExcursion
  rw [hlen']
  constructor
  · rintro ⟨-, -, hpre⟩
    refine ⟨fun j hj => ?_, fun j hij hjn => ?_⟩
    · rcases Nat.eq_zero_or_pos j with rfl | hj0
      · have h := hpre (n - i) (by omega)
        rw [key _ (by omega), ite_eq_left le_rfl, show i + (n - i) = n by omega, hSn] at h
        omega
      · have h := hpre (n - i + j) (by omega)
        rw [key _ (by omega), ite_eq_right (by omega), show n - i + j - (n - i) = j by omega] at h
        omega
    · have h := hpre (j - i) (by omega)
      rw [key _ (by omega), ite_eq_left (by omega), show i + (j - i) = j by omega] at h
      omega
  · rintro ⟨hlt, hge'⟩
    refine ⟨hent, hs, fun k hk => ?_⟩
    rw [key k hk]
    split_ifs with hkn
    · rcases Nat.lt_or_ge (i + k) n with hlt' | hge''
      · have := hge' (i + k) (by omega) hlt'
        omega
      · have hin : i + k = n := by omega
        have hi0 : 0 < i := by omega
        have := hlt 0 hi0
        rw [hin, hSn]
        omega
    · have hk1 : 0 < k - (n - i) := by omega
      have := hlt (k - (n - i)) (by omega)
      omega

/-- The first index in `[0, n)` where the prefix sums attain their minimum. -/
private theorem exists_first_min {x : List ℤ} {n : ℕ} (hx : x ∈ bridgeWords n) :
    ∃ i, i < n ∧ (∀ j < i, (x.take i).sum + 1 ≤ (x.take j).sum) ∧
      ∀ j, i ≤ j → j < n → (x.take i).sum ≤ (x.take j).sum := by
  classical
  obtain ⟨hlen, -, hsum⟩ := hx
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with rfl | h
    · have : x = [] := List.length_eq_zero_iff.mp hlen
      simp [this] at hsum
    · exact h
  have hex : ∃ i, i < n ∧ ∀ l < n, (x.take i).sum ≤ (x.take l).sum := by
    obtain ⟨i, hi, hmin⟩ := Finset.exists_min_image (Finset.range n)
      (fun j => (x.take j).sum) ⟨0, Finset.mem_range.mpr hn⟩
    exact ⟨i, Finset.mem_range.mp hi, fun l hl => hmin l (Finset.mem_range.mpr hl)⟩
  refine ⟨Nat.find hex, (Nat.find_spec hex).1, fun j hj => ?_,
    fun j _ hjn => (Nat.find_spec hex).2 j hjn⟩
  have hnot := Nat.find_min hex hj
  have hjn : j < n := lt_trans hj (Nat.find_spec hex).1
  push Not at hnot
  obtain ⟨l, hl, hlt⟩ := hnot hjn
  have := (Nat.find_spec hex).2 l hl
  omega

/-- A bridge word has exactly one rotation, by an index below its length, that is a tree
excursion: the cycle lemma. -/
theorem exists_unique_rotate_isTreeExcursion {x : List ℤ} {n : ℕ} (hx : x ∈ bridgeWords n) :
    ∃! i, i < n ∧ IsTreeExcursion (x.rotate i) := by
  obtain ⟨i, hi, h1, h2⟩ := exists_first_min hx
  refine ⟨i, ⟨hi, (isTreeExcursion_rotate_iff hx hi).mpr ⟨h1, h2⟩⟩, ?_⟩
  rintro i' ⟨hi', hexc⟩
  obtain ⟨g1, g2⟩ := (isTreeExcursion_rotate_iff hx hi').mp hexc
  rcases lt_trichotomy i i' with h | h | h
  · have a := g1 i h
    have b := h2 i' h.le hi'
    omega
  · exact h.symm
  · have a := h1 i' h
    have b := g2 i h.le hi
    omega

/-- Rotating by `i` and then by the complementary index is the identity. -/
private theorem rotate_rotate_complement {α : Type*} (l : List α) {i : ℕ} (hi : i < l.length) :
    (l.rotate i).rotate ((l.length - i) % l.length) = l := by
  rw [List.rotate_rotate]
  rcases Nat.eq_zero_or_pos i with rfl | hi0
  · simp
  · rw [Nat.mod_eq_of_lt (by omega), show i + (l.length - i) = l.length by omega,
      List.rotate_length]

private theorem rotate_mem_bridgeWords {x : List ℤ} {n : ℕ} (hx : x ∈ bridgeWords n) (i : ℕ) :
    x.rotate i ∈ bridgeWords n := by
  obtain ⟨hlen, hge, hsum⟩ := hx
  exact ⟨by simp [hlen], fun a ha => hge a (List.mem_rotate.mp ha),
    by rw [(List.rotate_perm x i).sum_eq]; exact hsum⟩

open scoped ENNReal

/-- Rotating a word permutes its entries, so the walk weight is unchanged. -/
theorem walkWeight_rotate (p : ℕ → ℝ≥0∞) (x : List ℤ) (i : ℕ) :
    walkWeight p (x.rotate i) = walkWeight p x := by
  unfold walkWeight
  rw [List.map_rotate]
  exact (List.rotate_perm _ _).prod_eq

namespace PlaneTree

theorem increments_mem_bridgeWords (t : PlaneTree) : t.increments ∈ bridgeWords t.size :=
  ⟨length_increments t, fun _ hx => neg_one_le_increment t hx, sum_increments t⟩

/-- Cyclic shifts of the codes of trees with `n` vertices. -/
def shiftMap (n : ℕ) (q : {t : PlaneTree // t.size = n} × Fin n) : bridgeWords n :=
  ⟨q.1.1.increments.rotate q.2, by
    have := rotate_mem_bridgeWords (increments_mem_bridgeWords q.1.1) q.2
    rwa [q.1.2] at this⟩

theorem shiftMap_injective (n : ℕ) : Function.Injective (shiftMap n) := by
  rintro ⟨⟨t, ht⟩, i⟩ ⟨⟨t', ht'⟩, i'⟩ h
  have hz : t.increments.rotate i = t'.increments.rotate i' := congrArg Subtype.val h
  have hlen : t.increments.length = n := by rw [length_increments, ht]
  have hlen' : t'.increments.length = n := by rw [length_increments, ht']
  have hz_mem : t.increments.rotate i ∈ bridgeWords n := by
    have := rotate_mem_bridgeWords (increments_mem_bridgeWords t) i
    rwa [ht] at this
  have e1 : IsTreeExcursion ((t.increments.rotate i).rotate ((n - i) % n)) := by
    have := rotate_rotate_complement t.increments (i := i) (by omega)
    rw [hlen] at this
    rw [this]; exact isTreeExcursion_increments t
  have e2 : IsTreeExcursion ((t.increments.rotate i).rotate ((n - i') % n)) := by
    have := rotate_rotate_complement t'.increments (i := i') (by omega)
    rw [hlen'] at this
    rw [hz, this]; exact isTreeExcursion_increments t'
  have hmod1 : (n - i) % n < n := Nat.mod_lt _ (Fin.pos i)
  have hmod2 : (n - i') % n < n := Nat.mod_lt _ (Fin.pos i')
  have hidx : (n - i) % n = (n - i') % n :=
    (exists_unique_rotate_isTreeExcursion hz_mem).unique ⟨hmod1, e1⟩ ⟨hmod2, e2⟩
  have hi_lt : i < n := Fin.is_lt i
  have hi'_lt : i' < n := Fin.is_lt i'
  have hii : i = i' := by
    apply Fin.ext
    rcases Nat.eq_zero_or_pos (i : ℕ) with h0 | h0 <;>
      rcases Nat.eq_zero_or_pos (i' : ℕ) with h0' | h0'
    · omega
    · rw [h0, Nat.sub_zero, Nat.mod_self, Nat.mod_eq_of_lt (by omega)] at hidx; omega
    · rw [h0', Nat.sub_zero, Nat.mod_self, Nat.mod_eq_of_lt (by omega)] at hidx; omega
    · rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hidx; omega
  subst hii
  have : t.increments = t'.increments := by
    have := congrArg (fun z => z.rotate ((n - (i : ℕ)) % n)) hz
    have h1 := rotate_rotate_complement t.increments (i := (i : ℕ)) (by omega)
    have h2 := rotate_rotate_complement t'.increments (i := (i : ℕ)) (by omega)
    rw [hlen] at h1
    rw [hlen'] at h2
    rw [h1, h2] at this
    exact this
  exact Prod.ext (Subtype.ext (increments_injective this)) rfl

theorem shiftMap_surjective (n : ℕ) : Function.Surjective (shiftMap n) := by
  rintro ⟨x, hx⟩
  obtain ⟨i, ⟨hi, hexc⟩, -⟩ := exists_unique_rotate_isTreeExcursion hx
  obtain ⟨t, ht, -⟩ := (isTreeExcursion_iff_existsUnique _).mp hexc
  have hlenx : x.length = n := hx.1
  have hsize : t.size = n := by
    rw [← length_increments, ht]; simp [hlenx]
  refine ⟨(⟨t, hsize⟩, ⟨(n - i) % n, Nat.mod_lt _ (by omega)⟩), Subtype.ext ?_⟩
  change t.increments.rotate ((n - i) % n) = x
  rw [ht]
  have := rotate_rotate_complement x (i := i) (by omega)
  rwa [hlenx] at this

/-- The cycle lemma as an equivalence. -/
noncomputable def shiftEquiv (n : ℕ) :
    {t : PlaneTree // t.size = n} × Fin n ≃ bridgeWords n :=
  Equiv.ofBijective (shiftMap n) ⟨shiftMap_injective n, shiftMap_surjective n⟩

/-- Kemperman–Dwass identity in weight form: `n` times the total weight of the trees of size `n`
is the total walk weight of the bridge words of length `n`. No hypothesis on `p`. -/
theorem natCast_mul_tsum_weight_size (p : ℕ → ℝ≥0∞) (n : ℕ) :
    (n : ℝ≥0∞) * ∑' t : PlaneTree, (if t.size = n then weight p t else 0) =
      ∑' x : List ℤ, Set.indicator (bridgeWords n) (walkWeight p) x := by
  have hl : ∑' t : PlaneTree, (if t.size = n then weight p t else 0) =
      ∑' t : {t : PlaneTree // t.size = n}, weight p t.1 := by
    have h := tsum_subtype {t : PlaneTree | t.size = n} (weight p)
    have h' : ∑' t : PlaneTree, (if t.size = n then weight p t else 0) =
        ∑' t : PlaneTree, Set.indicator {t : PlaneTree | t.size = n} (weight p) t :=
      tsum_congr fun t => by by_cases h : t.size = n <;> simp [Set.indicator, h]
    rw [h']
    exact h.symm
  have hr : ∑' x : List ℤ, Set.indicator (bridgeWords n) (walkWeight p) x =
      ∑' x : bridgeWords n, walkWeight p x.1 :=
    (tsum_subtype (bridgeWords n) (walkWeight p)).symm
  rw [hl, hr, ← (shiftEquiv n).tsum_eq]
  have hq : ∀ q : {t : PlaneTree // t.size = n} × Fin n,
      walkWeight p (shiftEquiv n q).1 = weight p q.1.1 := fun q => by
    change walkWeight p (q.1.1.increments.rotate q.2) = _
    rw [walkWeight_rotate, walkWeight_increments]
  simp_rw [hq]
  rw [ENNReal.tsum_prod (f := fun (a : {t : PlaneTree // t.size = n}) (_ : Fin n) => weight p a.1),
    ← ENNReal.tsum_mul_left]
  refine tsum_congr fun t => ?_
  simp [tsum_fintype]

end PlaneTree

end BGW
