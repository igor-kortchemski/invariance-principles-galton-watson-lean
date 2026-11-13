/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.Tree.CycleLemma
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Lean.Elab.Tactic.Omega

/-!
# Forest codes

For `ℓ ≥ 1`, a forest code is an integer word with all entries at least `-1`, sum `-ℓ`, and all
proper prefix sums (the empty prefix included) strictly above `-ℓ`: the first passage to `-ℓ`
happens at the terminal time. Prepending the artificial-root increment `ℓ - 1` turns such a word
into a tree excursion, so forest codes are exactly the increments of the ordered forests with `ℓ`
components, each forest being determined by its code. The weight of a forest, the product of the
weights of its components, is the walk weight of its code.

The rotation of a word of sum `-ℓ` is a forest code exactly when its starting index is a strict
running minimum of the prefix sums that later prefix sums do not undercut by `ℓ` or more. The
generalized cycle lemma follows: a word of length `n`, entries at least `-1` and sum `-ℓ` has
exactly `ℓ` good rotation indices (indices are counted, not distinct rotated words, so periodic
words are covered). Counting the pairs of a bridge word and a good index in two ways gives
Kemperman's formula for forests in weight form,
`n * forestWeight p ℓ n = ℓ * (total walk weight of the words of length n and sum -ℓ)`,
for arbitrary step masses `p`. Adapted from `PoissonDeclumping/Bridge/Kemperman.lean`
(`card_filter_rotate_firstPassageAt`, `forestMap_bijective`, `natCast_mul_forestSizeWeight`); the
forest coding goes through the artificial root and the tree excursion bijection instead of a second
parser, and the first-passage convolution is not part of this module.
-/

@[expose] public section

namespace BGW

open scoped ENNReal

/-- Words of steps at least `-1` whose first passage to `-ℓ` is at the terminal time. -/
def IsForestCode (ℓ : ℕ) (xs : List ℤ) : Prop :=
  (∀ x ∈ xs, -1 ≤ x) ∧ xs.sum = -(ℓ : ℤ) ∧ ∀ i < xs.length, -(ℓ : ℤ) < (xs.take i).sum

/-- The artificial root: a forest code with `ℓ` components is a tree excursion once the increment
`ℓ - 1` of a root with `ℓ` children is prepended. -/
theorem isForestCode_iff_isTreeExcursion_cons {ℓ : ℕ} (hℓ : 1 ≤ ℓ) (xs : List ℤ) :
    IsForestCode ℓ xs ↔ IsTreeExcursion (((ℓ : ℤ) - 1) :: xs) := by
  unfold IsForestCode IsTreeExcursion
  constructor
  · rintro ⟨hge, hs, hpre⟩
    refine ⟨?_, ?_, ?_⟩
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · omega
      · exact hge x hx
    · simp only [List.sum_cons, hs]
      omega
    · intro i hi
      cases i with
      | zero => simp
      | succ j =>
        have := hpre j (by simpa using hi)
        simp only [List.take_succ_cons, List.sum_cons]
        omega
  · rintro ⟨hge, hs, hpre⟩
    refine ⟨fun x hx => hge x (List.mem_cons_of_mem _ hx), ?_, fun i hi => ?_⟩
    · simp only [List.sum_cons] at hs
      omega
    · have := hpre (i + 1) (by simpa using hi)
      simp only [List.take_succ_cons, List.sum_cons] at this
      omega

namespace PlaneForest

/-- A forest is determined by its code. -/
theorem increments_injective : Function.Injective increments := by
  intro ts ts' h
  have hlen : ts.length = ts'.length := by
    have := congrArg List.sum h
    rw [sum_increments, sum_increments] at this
    omega
  have : (PlaneTree.node ts).increments = (PlaneTree.node ts').increments := by
    rw [PlaneTree.increments_node, PlaneTree.increments_node, hlen]
    exact congrArg _ h
  exact PlaneTree.node_inj.mp (PlaneTree.increments_injective this)

/-- Forest codes with `ℓ ≥ 1` components are exactly the codes of the unique ordered forests
with `ℓ` components. -/
theorem isForestCode_iff_existsUnique {ℓ : ℕ} (hℓ : 1 ≤ ℓ) (xs : List ℤ) :
    IsForestCode ℓ xs ↔ ∃! ts : PlaneForest, ts.length = ℓ ∧ increments ts = xs := by
  rw [isForestCode_iff_isTreeExcursion_cons hℓ, PlaneTree.isTreeExcursion_iff_existsUnique]
  constructor
  · rintro ⟨t, ht, huniq⟩
    cases t with
    | node ts =>
      rw [PlaneTree.increments_node] at ht
      obtain ⟨h1, h2⟩ := List.cons.inj ht
      refine ⟨ts, ⟨by omega, h2⟩, ?_⟩
      rintro ts' ⟨hl', hinc⟩
      have : (PlaneTree.node ts').increments = ((ℓ : ℤ) - 1) :: xs := by
        rw [PlaneTree.increments_node, hl']
        exact congrArg _ hinc
      exact PlaneTree.node_inj.mp (huniq _ this)
  · rintro ⟨ts, ⟨hl, hinc⟩, huniq⟩
    refine ⟨PlaneTree.node ts, ?_, ?_⟩
    · show (PlaneTree.node ts).increments = _
      rw [PlaneTree.increments_node, hl]
      exact congrArg _ hinc
    · intro t ht
      cases t with
      | node ss =>
        rw [PlaneTree.increments_node] at ht
        obtain ⟨h1, h2⟩ := List.cons.inj ht
        rw [huniq ss ⟨by omega, h2⟩]

/-- The weight of a forest is the walk weight of its code. -/
theorem walkWeight_increments (p : ℕ → ℝ≥0∞) (ts : PlaneForest) :
    walkWeight p (increments ts) = (ts.map (PlaneTree.weight p)).prod := by
  induction ts with
  | nil => simp [increments, walkWeight]
  | cons t ts ih =>
    change walkWeight p (PlaneTree.increments t ++ increments ts) = _
    rw [walkWeight, List.map_append, List.prod_append, ← walkWeight,
      PlaneTree.walkWeight_increments, ← walkWeight, ih, List.map_cons, List.prod_cons]

end PlaneForest

/-- Words of length `n` with entries at least `-1` and sum `-ℓ`; `ℓ = 1` gives `bridgeWords n`. -/
def forestBridgeWords (ℓ n : ℕ) : Set (List ℤ) :=
  {x | x.length = n ∧ (∀ a ∈ x, -1 ≤ a) ∧ x.sum = -(ℓ : ℤ)}

theorem forestBridgeWords_one (n : ℕ) : forestBridgeWords 1 n = bridgeWords n := by
  ext x
  simp [forestBridgeWords, bridgeWords]

/-- Discrete intermediate value property: if the steps are at least `-1`, `v ≤ 0` and some prefix
sum is at most `v`, then `v` is attained at a first time, all earlier prefix sums being above `v`.
Adapted from `PoissonDeclumping/Bridge/Kemperman.lean`. -/
theorem exists_first_sum_take_eq {x : List ℤ} (hx : ∀ a ∈ x, -1 ≤ a) {v : ℤ} (hv : v ≤ 0)
    {b : ℕ} (hb : (x.take b).sum ≤ v) :
    ∃ l ≤ b, (x.take l).sum = v ∧ ∀ l' < l, v < (x.take l').sum := by
  classical
  have hex : ∃ l, (x.take l).sum ≤ v := ⟨b, hb⟩
  refine ⟨Nat.find hex, Nat.find_min' hex hb, ?_, fun l' hl' => ?_⟩
  · have hle := Nat.find_spec hex
    rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
    · rw [h0] at hle ⊢
      simp only [List.take_zero, List.sum_nil] at hle ⊢
      omega
    · obtain ⟨l, hl⟩ : ∃ l, Nat.find hex = l + 1 := ⟨Nat.find hex - 1, by omega⟩
      have hprev : v < (x.take l).sum :=
        lt_of_not_ge (Nat.find_min hex (show l < Nat.find hex by omega))
      rw [hl] at hle ⊢
      rcases lt_or_ge l x.length with hlt | hge
      · rw [List.sum_take_succ _ _ hlt] at hle ⊢
        have := hx _ (List.getElem_mem hlt)
        omega
      · rw [List.take_of_length_le (by omega)] at hle
        rw [List.take_of_length_le hge] at hprev
        omega
  · exact lt_of_not_ge (Nat.find_min hex hl')

/-- The rotation of a word of sum `-ℓ` by `i < n` is a forest code iff `i` is a strict running
minimum of the prefix sums that later prefix sums (before time `n`) do not undercut by `ℓ`. -/
theorem isForestCode_rotate_iff {x : List ℤ} {ℓ : ℕ} (hge : ∀ a ∈ x, -1 ≤ a)
    (hs : x.sum = -(ℓ : ℤ)) {i : ℕ} (hi : i < x.length) :
    IsForestCode ℓ (x.rotate i) ↔
      (∀ l, i ≤ l → l < x.length → (x.take i).sum - ℓ < (x.take l).sum) ∧
        ∀ l < i, (x.take i).sum < (x.take l).sum := by
  have hS0 : (x.take 0).sum = 0 := by simp
  have hSn : (x.take x.length).sum = -(ℓ : ℤ) := by rw [List.take_length]; exact hs
  have hent : ∀ a ∈ x.rotate i, -1 ≤ a := fun a ha => hge a (List.mem_rotate.mp ha)
  have hsr : (x.rotate i).sum = -(ℓ : ℤ) := by rw [(List.rotate_perm x i).sum_eq]; exact hs
  have key : ∀ k, k < x.length → ((x.rotate i).take k).sum =
      if k ≤ x.length - i then (x.take (i + k)).sum - (x.take i).sum
      else -(ℓ : ℤ) - (x.take i).sum + (x.take (k - (x.length - i))).sum := by
    intro k hk
    rw [sum_take_rotate x hi.le hk.le, hs]
  unfold IsForestCode
  rw [List.length_rotate]
  constructor
  · rintro ⟨-, -, hpre⟩
    refine ⟨fun l hil hl => ?_, fun l hl => ?_⟩
    · have h := hpre (l - i) (by omega)
      rw [key _ (by omega), ite_eq_left (by omega), show i + (l - i) = l by omega] at h
      omega
    · have h := hpre (x.length - i + l) (by omega)
      rw [key _ (by omega)] at h
      split_ifs at h with hc
      · rw [show i + (x.length - i + l) = x.length by omega, hSn] at h
        have hl0 : l = 0 := by omega
        subst hl0
        omega
      · rw [show x.length - i + l - (x.length - i) = l by omega] at h
        omega
  · rintro ⟨h1, h2⟩
    refine ⟨hent, hsr, fun k hk => ?_⟩
    rw [key k hk]
    split_ifs with hkn
    · rcases Nat.lt_or_ge (i + k) x.length with hlt' | hge''
      · have := h1 (i + k) (by omega) hlt'
        omega
      · have hin : i + k = x.length := by omega
        have hi0 : 0 < i := by omega
        have := h2 0 hi0
        rw [hin, hSn]
        omega
    · have hk1 : 0 < k - (x.length - i) := by omega
      have := h2 (k - (x.length - i)) (by omega)
      omega

/-- **Generalized cycle lemma.** A word of length `n`, entries at least `-1` and sum `-ℓ` with
`ℓ ≥ 1` has exactly `ℓ` indices `i < n` whose left rotation is a forest code. Indices are counted,
not distinct rotated words, so periodic words are covered: `[-1, -1]` has two good indices. -/
theorem ncard_rotate_isForestCode {x : List ℤ} (hx : ∀ a ∈ x, -1 ≤ a) {ℓ : ℕ} (hℓ : 1 ≤ ℓ)
    (hs : x.sum = -(ℓ : ℤ)) :
    {i : ℕ | i < x.length ∧ IsForestCode ℓ (x.rotate i)}.ncard = ℓ := by
  have hq1 : 1 ≤ x.length := by
    rcases Nat.eq_zero_or_pos x.length with h0 | h
    · have : x = [] := List.eq_nil_of_length_eq_zero h0
      rw [this, List.sum_nil] at hs
      omega
    · exact h
  set S : ℕ → ℤ := fun l => (x.take l).sum with hS
  obtain ⟨l₀, hl₀, hmin⟩ := Finset.exists_min_image (Finset.range x.length) S
    ⟨0, Finset.mem_range.mpr (by omega)⟩
  have hl₀q : l₀ < x.length := Finset.mem_range.mp hl₀
  set m := S l₀ with hm
  have hmin' : ∀ l < x.length, m ≤ S l := fun l hl => hmin l (Finset.mem_range.mpr hl)
  have hm0 : m ≤ 0 := by
    have := hmin' 0 (by omega)
    simpa [hS] using this
  have hmℓ : m + ℓ - 1 ≤ 0 := by
    have h1 := hmin' (x.length - 1) (by omega)
    have h2 : S x.length = S (x.length - 1) + x[x.length - 1] := by
      have := List.sum_take_succ x (x.length - 1) (by omega)
      rw [show x.length - 1 + 1 = x.length by omega] at this
      exact this
    have h3 : S x.length = -(ℓ : ℤ) := by simp only [hS, List.take_length, hs]
    have h4 := hx _ (List.getElem_mem (show x.length - 1 < x.length by omega))
    omega
  have hIcc : Set.ncard (Set.Icc m (m + ℓ - 1)) = ℓ := by
    rw [← Finset.coe_Icc, Set.ncard_coe_finset, Int.card_Icc]
    omega
  refine Eq.trans (Set.ncard_congr (t := Set.Icc m (m + ℓ - 1)) (fun i _ => S i) ?_ ?_ ?_) hIcc
  · rintro i ⟨hi, hfc⟩
    obtain ⟨h1, h2⟩ := (isForestCode_rotate_iff hx hs hi).mp hfc
    refine ⟨hmin' i hi, ?_⟩
    rcases le_or_gt i l₀ with hil | hil
    · have := h1 l₀ hil hl₀q
      change S i - ℓ < m at this
      omega
    · have := h2 l₀ hil
      have := hmin' i hi
      change S i < m at *
      omega
  · rintro i i' ⟨hi, hfc⟩ ⟨hi', hfc'⟩ he
    obtain ⟨-, h2⟩ := (isForestCode_rotate_iff hx hs hi).mp hfc
    obtain ⟨-, h2'⟩ := (isForestCode_rotate_iff hx hs hi').mp hfc'
    change S i = S i' at he
    rcases lt_trichotomy i i' with h | h | h
    · have := h2' i h
      change S i' < S i at this
      omega
    · exact h
    · have := h2 i' h
      change S i < S i' at this
      omega
  · intro v hv
    obtain ⟨hv1, hv2⟩ := hv
    obtain ⟨l, hll₀, hlv, hlt⟩ := exists_first_sum_take_eq hx (v := v) (b := l₀) (by omega)
      (by change m ≤ v; omega)
    have hlq : l < x.length := lt_of_le_of_lt hll₀ hl₀q
    refine ⟨l, ⟨hlq, (isForestCode_rotate_iff hx hs hlq).mpr
      ⟨fun l' _ hl' => ?_, fun l' hl' => ?_⟩⟩, hlv⟩
    · have := hmin' l' hl'
      change m ≤ S l' at this
      change S l - ℓ < S l'
      change S l = v at hlv
      omega
    · have := hlt l' hl'
      change v < S l' at this
      change S l = v at hlv
      change S l < S l'
      omega

private theorem rotate_rotate_eq_self {α : Type*} (l : List α) {a b : ℕ}
    (h : (a + b) % l.length = 0) : (l.rotate a).rotate b = l := by
  rw [List.rotate_rotate, ← List.rotate_mod, h, List.rotate_zero]

private theorem mod_complement_add {n i : ℕ} (hi : i < n) : ((n - i) % n + i) % n = 0 := by
  rcases Nat.eq_zero_or_pos i with rfl | hi0
  · simp
  · have h1 : (n - i) % n = n - i := Nat.mod_eq_of_lt (by omega)
    rw [h1, show n - i + i = n by omega, Nat.mod_self]

private theorem rotate_mem_forestBridgeWords {x : List ℤ} {ℓ n : ℕ}
    (hx : x ∈ forestBridgeWords ℓ n) (i : ℕ) : x.rotate i ∈ forestBridgeWords ℓ n := by
  obtain ⟨hlen, hge, hsum⟩ := hx
  exact ⟨by simp [hlen], fun a ha => hge a (List.mem_rotate.mp ha),
    by rw [(List.rotate_perm x i).sum_eq]; exact hsum⟩

/-- The sum of a constant over a finite set of indices. -/
private theorem tsum_indicator_const_ncard {S : Set ℕ} (hS : S.Finite) (c : ℝ≥0∞) :
    ∑' i, S.indicator (fun _ => c) i = (S.ncard : ℝ≥0∞) * c := by
  rw [tsum_eq_sum (s := hS.toFinset) (fun i hi =>
      Set.indicator_of_notMem (fun h => hi (hS.mem_toFinset.mpr h)) _),
    Finset.sum_congr rfl (fun i hi => Set.indicator_of_mem (hS.mem_toFinset.mp hi) _),
    Finset.sum_const, nsmul_eq_mul, Set.ncard_eq_toFinset_card S hS]

/-- Total weight of the ordered forests of `ℓ` trees with `n` vertices in total. -/
noncomputable def forestWeight (p : ℕ → ℝ≥0∞) (ℓ n : ℕ) : ℝ≥0∞ :=
  ∑' ts : PlaneForest,
    if ts.length = ℓ ∧ PlaneForest.size ts = n then (ts.map (PlaneTree.weight p)).prod else 0

/-- The weights of forests reindexed by their codes. -/
theorem forestWeight_eq_tsum_codes (p : ℕ → ℝ≥0∞) {ℓ : ℕ} (hℓ : 1 ≤ ℓ) (n : ℕ) :
    forestWeight p ℓ n = ∑' x : List ℤ,
      Set.indicator {x : List ℤ | IsForestCode ℓ x ∧ x.length = n} (walkWeight p) x := by
  have hrange : Function.support
      (Set.indicator {x : List ℤ | IsForestCode ℓ x ∧ x.length = n} (walkWeight p)) ⊆
        Set.range PlaneForest.increments := by
    intro x hx
    by_contra hr
    apply hx
    have hx' : x ∉ {x : List ℤ | IsForestCode ℓ x ∧ x.length = n} := fun h =>
      hr (by
        obtain ⟨ts, ⟨-, hinc⟩, -⟩ := (PlaneForest.isForestCode_iff_existsUnique hℓ x).mp h.1
        exact ⟨ts, hinc⟩)
    exact Set.indicator_of_notMem hx' _
  unfold forestWeight
  rw [← PlaneForest.increments_injective.tsum_eq hrange]
  refine tsum_congr fun ts => ?_
  by_cases h : ts.length = ℓ ∧ PlaneForest.size ts = n
  · have hmem : PlaneForest.increments ts ∈
        {x : List ℤ | IsForestCode ℓ x ∧ x.length = n} :=
      ⟨(PlaneForest.isForestCode_iff_existsUnique hℓ _).mpr
        ⟨ts, ⟨h.1, rfl⟩, fun ts' hts' => PlaneForest.increments_injective hts'.2⟩,
        by rw [PlaneForest.length_increments]; exact h.2⟩
    rw [ite_eq_left h, Set.indicator_of_mem hmem, PlaneForest.walkWeight_increments]
  · have hmem : PlaneForest.increments ts ∉
        {x : List ℤ | IsForestCode ℓ x ∧ x.length = n} := by
      rintro ⟨hc, hl⟩
      obtain ⟨ts', ⟨hl', hinc⟩, -⟩ := (PlaneForest.isForestCode_iff_existsUnique hℓ _).mp hc
      have := PlaneForest.increments_injective hinc
      subst this
      exact h ⟨hl', by rwa [PlaneForest.length_increments] at hl⟩
    rw [ite_eq_right h, Set.indicator_of_notMem hmem]

/-- **Kemperman's formula for forests, in weight form.** For every `p : ℕ → ℝ≥0∞`, `ℓ ≥ 1` and
`n`: `n` times the total weight of the ordered forests of `ℓ` trees with `n` vertices is `ℓ` times
the total walk weight of the words of length `n`, entries at least `-1` and sum `-ℓ`. -/
theorem natCast_mul_forestWeight (p : ℕ → ℝ≥0∞) {ℓ : ℕ} (hℓ : 1 ≤ ℓ) (n : ℕ) :
    (n : ℝ≥0∞) * forestWeight p ℓ n =
      (ℓ : ℝ≥0∞) * ∑' x : List ℤ, Set.indicator (forestBridgeWords ℓ n) (walkWeight p) x := by
  rw [forestWeight_eq_tsum_codes p hℓ]
  set B := forestBridgeWords ℓ n with hB
  set FC : Set (List ℤ) := {x | IsForestCode ℓ x ∧ x.length = n} with hFC
  set Q : Set (List ℤ × ℕ) := {q | q.1 ∈ B ∧ q.2 < n ∧ IsForestCode ℓ (q.1.rotate q.2)} with hQ
  -- counting the pairs `(x, i)` with the cycle lemma
  have ha : ∑' q, Q.indicator (fun q => walkWeight p q.1) q =
      (ℓ : ℝ≥0∞) * ∑' x, B.indicator (walkWeight p) x := by
    rw [ENNReal.tsum_prod', ← ENNReal.tsum_mul_left]
    refine tsum_congr fun x => ?_
    by_cases hx : x ∈ B
    · have hS : ∀ i, Q.indicator (fun q => walkWeight p q.1) (x, i) =
          {i : ℕ | i < x.length ∧ IsForestCode ℓ (x.rotate i)}.indicator
            (fun _ => walkWeight p x) i := by
        intro i
        by_cases hi : i < x.length ∧ IsForestCode ℓ (x.rotate i)
        · rw [Set.indicator_of_mem (show (x, i) ∈ Q from ⟨hx, by rw [← hx.1]; exact hi.1, hi.2⟩),
            Set.indicator_of_mem (show i ∈ {i : ℕ | i < x.length ∧ IsForestCode ℓ (x.rotate i)}
              from hi)]
        · rw [Set.indicator_of_notMem (show (x, i) ∉ Q from fun h =>
              hi ⟨by rw [hx.1]; exact h.2.1, h.2.2⟩),
            Set.indicator_of_notMem (show i ∉ {i : ℕ | i < x.length ∧
              IsForestCode ℓ (x.rotate i)} from hi)]
      simp_rw [hS]
      have hfin : {i : ℕ | i < x.length ∧ IsForestCode ℓ (x.rotate i)}.Finite :=
        (Set.finite_Iio x.length).subset fun i hi => hi.1
      rw [tsum_indicator_const_ncard hfin, ncard_rotate_isForestCode hx.2.1 hℓ hx.2.2,
        Set.indicator_of_mem hx]
    · have : ∀ i : ℕ, Q.indicator (fun q => walkWeight p q.1) (x, i) = 0 := fun i =>
        Set.indicator_of_notMem (fun h => hx h.1) _
      simp [this, Set.indicator_of_notMem hx]
  -- counting the pairs `(x, i)` with rotations of forest codes
  have hb : ∑' q, Q.indicator (fun q => walkWeight p q.1) q =
      (n : ℝ≥0∞) * ∑' y, FC.indicator (walkWeight p) y := by
    rw [ENNReal.tsum_prod', ENNReal.tsum_comm]
    have hfib : ∀ i : ℕ, ∑' x, Q.indicator (fun q => walkWeight p q.1) (x, i) =
        if i < n then ∑' y, FC.indicator (walkWeight p) y else 0 := by
      intro i
      by_cases hi : i < n
      · rw [ite_eq_left hi]
        have hg : Function.Injective (fun y : List ℤ => y.rotate ((n - i) % n)) :=
          List.rotate_injective _
        have hrange : Function.support (fun x => Q.indicator (fun q => walkWeight p q.1) (x, i))
            ⊆ Set.range (fun y : List ℤ => y.rotate ((n - i) % n)) := by
          intro x hx
          by_contra hr
          apply hx
          refine Set.indicator_of_notMem (fun hq => hr ⟨x.rotate i, ?_⟩) _
          have hlen : x.length = n := hq.1.1
          exact rotate_rotate_eq_self x (by rw [hlen, add_comm]; exact mod_complement_add hi)
        rw [← hg.tsum_eq hrange]
        refine tsum_congr fun y => ?_
        by_cases hy : y ∈ FC
        · have hyB : y ∈ B := ⟨hy.2, hy.1.1, hy.1.2.1⟩
          have hmem : (y.rotate ((n - i) % n), i) ∈ Q := by
            refine ⟨rotate_mem_forestBridgeWords hyB _, hi, ?_⟩
            show IsForestCode ℓ ((y.rotate ((n - i) % n)).rotate i)
            rw [rotate_rotate_eq_self y (by rw [hy.2]; exact mod_complement_add hi)]
            exact hy.1
          simp only [Set.indicator_of_mem hmem, Set.indicator_of_mem hy]
          exact walkWeight_rotate p y _
        · have hmem : (y.rotate ((n - i) % n), i) ∉ Q := by
            rintro ⟨hB', -, hfc⟩
            have hlen : y.length = n := by simpa using hB'.1
            apply hy
            refine ⟨?_, hlen⟩
            have := rotate_rotate_eq_self y (a := (n - i) % n) (b := i)
              (by rw [hlen]; exact mod_complement_add hi)
            rw [this] at hfc
            exact hfc
          simp only [Set.indicator_of_notMem hmem, Set.indicator_of_notMem hy]
      · rw [ite_eq_right hi]
        exact (tsum_congr fun x => Set.indicator_of_notMem (fun h => hi h.2.1) _).trans tsum_zero
    simp_rw [hfib]
    rw [tsum_eq_sum (s := Finset.range n) (fun i hi => by
        rw [ite_eq_right (by simpa using hi)]),
      Finset.sum_congr rfl (fun i hi => ite_eq_left (Finset.mem_range.mp hi)), Finset.sum_const,
      Finset.card_range, nsmul_eq_mul]
  rw [← hb, ha]

namespace PlaneForest

theorem length_le_size (ts : PlaneForest) : ts.length ≤ size ts := by
  have := List.length_le_sum_of_one_le (ts.map PlaneTree.size)
    (fun a ha => by
      obtain ⟨t, -, rfl⟩ := List.mem_map.mp ha
      exact PlaneTree.size_pos t)
  simpa [size] using this

end PlaneForest

/-- Fewer vertices than components: no forest. -/
theorem forestWeight_eq_zero_of_lt (p : ℕ → ℝ≥0∞) {ℓ n : ℕ} (h : n < ℓ) :
    forestWeight p ℓ n = 0 := by
  unfold forestWeight
  refine (tsum_congr fun ts => ?_).trans tsum_zero
  refine ite_eq_right fun hts => ?_
  have := PlaneForest.length_le_size ts
  omega

end BGW
