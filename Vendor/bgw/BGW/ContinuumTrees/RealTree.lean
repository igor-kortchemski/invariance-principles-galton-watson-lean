/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import Mathlib.Topology.MetricSpace.GromovHausdorff
public import Mathlib.Topology.MetricSpace.GromovProduct
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Real trees

A metric space is a **real tree** if any two points `s, t` are joined by a geodesic
segment, this segment is unique, and every injective continuous path from `s` to
`t` has the same image as the segment. This is the standard definition.

We prove that a complete metric space satisfying the four-point condition
(`0`-hyperbolicity) and having midpoints is a real tree:

* midpoints and completeness give geodesic segments (dyadic construction);
* the four-point condition forces their uniqueness, and characterizes their
  points as those `c` with `d(s,c) + d(c,t) = d(s,t)`;
* removing an interior point of the segment separates `s` from `t` (via the
  Gromov product at that point), so every path from `s` to `t` passes through every
  point of the segment, and injectivity forbids any other point.

The Gromov product and its nonnegativity are reused from Mathlib.

Adapted from `Freezing2/Geometry/RealTree.lean` in
`igor-kortchemski/uniform-attachment-freezing-scaling-limits`, commit
`8bace72d36cdf7d250414f3d98acfaa415de23d9` (Apache-2.0).
-/

@[expose] public section

open Set Filter Topology Metric

namespace BGW.ContinuumTrees.RealTree

variable {X : Type*} [MetricSpace X]

/-- `γ` parametrizes a geodesic segment from `s` to `t` on `[0, d(s, t)]`. -/
def IsSegment (s t : X) (γ : ℝ → X) : Prop :=
  γ 0 = s ∧ γ (dist s t) = t ∧
    ∀ a ∈ Icc 0 (dist s t), ∀ b ∈ Icc 0 (dist s t), dist (γ a) (γ b) = |a - b|

/-- **Real tree.** Any two points are joined by a unique geodesic segment, and every
injective continuous path between them has the image of that segment. -/
def IsRealTree (X : Type*) [MetricSpace X] : Prop :=
  ∀ s t : X, (∃ γ, IsSegment s t γ) ∧
    (∀ γ γ', IsSegment s t γ → IsSegment s t γ' → EqOn γ γ' (Icc 0 (dist s t))) ∧
    ∀ γ q : ℝ → X, IsSegment s t γ → ContinuousOn q (Icc 0 1) → InjOn q (Icc 0 1) →
      q 0 = s → q 1 = t → q '' Icc 0 1 = γ '' Icc 0 (dist s t)

/-- The four-point condition (`0`-hyperbolicity). -/
def FourPoint (X : Type*) [MetricSpace X] : Prop :=
  ∀ x y z w : X, dist x y + dist z w ≤ max (dist x z + dist y w) (dist x w + dist y z)

/-- Every pair of points has a midpoint. -/
def HasMidpoints (X : Type*) [MetricSpace X] : Prop :=
  ∀ x y : X, ∃ m, dist x m = dist x y / 2 ∧ dist m y = dist x y / 2

/-- Every pair of points has an `ε`-approximate midpoint. -/
def ApproxMidpoints (ε : ℝ) (X : Type*) [MetricSpace X] : Prop :=
  ∀ x y : X, ∃ m, |dist x m - dist x y / 2| ≤ ε ∧ |dist m y - dist x y / 2| ≤ ε

section Segments

variable {s t : X} {γ : ℝ → X}

theorem IsSegment.dist_left (hγ : IsSegment s t γ) {a : ℝ} (ha : a ∈ Icc 0 (dist s t)) :
    dist s (γ a) = a := by
  have h := hγ.2.2 0 (left_mem_Icc.mpr dist_nonneg) a ha
  rw [hγ.1, zero_sub, abs_neg, abs_of_nonneg ha.1] at h
  exact h

theorem IsSegment.dist_right (hγ : IsSegment s t γ) {a : ℝ} (ha : a ∈ Icc 0 (dist s t)) :
    dist (γ a) t = dist s t - a := by
  have h := hγ.2.2 a ha (dist s t) (right_mem_Icc.mpr dist_nonneg)
  rw [hγ.2.1, abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr ha.2)] at h
  exact h

/-- Under the four-point condition a point between `s` and `t` lies on every segment. -/
theorem eq_of_dist_add_dist (h4 : FourPoint X) (hγ : IsSegment s t γ) {c : X}
    (hc : dist s c + dist c t = dist s t) : γ (dist s c) = c := by
  have ha : dist s c ∈ Icc 0 (dist s t) :=
    ⟨dist_nonneg, by linarith [dist_nonneg (x := c) (y := t)]⟩
  have h := h4 s t c (γ (dist s c))
  rw [hγ.dist_left ha, dist_comm t (γ (dist s c)), hγ.dist_right ha, dist_comm t c] at h
  have hmax : max (dist s c + (dist s t - dist s c)) (dist s c + dist c t) = dist s t := by
    rw [hc]
    simp
  rw [hmax] at h
  exact (dist_le_zero.mp (by linarith)).symm

/-- **Uniqueness of segments.** -/
theorem segment_unique (h4 : FourPoint X) {γ γ' : ℝ → X} (hγ : IsSegment s t γ)
    (hγ' : IsSegment s t γ') : EqOn γ γ' (Icc 0 (dist s t)) := by
  intro a ha
  have hc : dist s (γ' a) + dist (γ' a) t = dist s t := by
    rw [hγ'.dist_left ha, hγ'.dist_right ha]
    ring
  have := eq_of_dist_add_dist h4 hγ hc
  rwa [hγ'.dist_left ha] at this

end Segments

section GromovProduct

theorem continuous_gromovProduct (w x : X) : Continuous (gromovProduct w x) := by
  change Continuous (fun y : X => Metric.gromovProduct w x y)
  simp_rw [Metric.gromovProduct_eq]
  fun_prop

theorem gromovProduct_ge_min (h4 : FourPoint X) (w x y z : X) :
    min (gromovProduct w x z) (gromovProduct w z y) ≤ gromovProduct w x y := by
  have h := h4 x y z w
  have e1 := dist_comm y w
  have e2 := dist_comm x w
  have e3 := dist_comm z w
  have e4 := dist_comm z y
  simp only [Metric.gromovProduct_eq]
  rcases le_max_iff.mp h with h' | h'
  · exact (min_le_left _ _).trans (by linarith)
  · exact (min_le_right _ _).trans (by linarith)

/-- Points `p ≠ c` with vanishing Gromov product with `s` at `c` form an open set. -/
theorem isOpen_gromovProduct_eq_zero (h4 : FourPoint X) (c s : X) :
    IsOpen {p : X | p ≠ c ∧ gromovProduct c s p = 0} := by
  rw [Metric.isOpen_iff]
  rintro p ⟨hpc, hp0⟩
  have hδ : 0 < dist c p := dist_pos.mpr (Ne.symm hpc)
  refine ⟨dist c p, hδ, fun p' hp' ↦ ?_⟩
  have hpp' : dist p' p < dist c p := mem_ball.mp hp'
  have hcp' : dist c p - dist p' p ≤ dist c p' := by
    linarith [dist_triangle c p' p]
  refine ⟨fun he ↦ ?_, ?_⟩
  · subst he
    rw [dist_comm] at hpp'
    exact lt_irrefl _ hpp'
  · have hmin := gromovProduct_ge_min h4 c s p p'
    rw [hp0] at hmin
    have hpos : 0 < gromovProduct c p' p := by
      have e := dist_comm p' p
      simp only [Metric.gromovProduct_eq]
      linarith
    have hle : gromovProduct c s p' ≤ 0 := by
      rcases min_le_iff.mp (le_of_eq_of_le rfl hmin) with h | h
      · exact h
      · exact absurd h (not_le.mpr hpos)
    exact le_antisymm hle (gromovProduct_nonneg c s p')

/-- **Separation.** Under the four-point condition, every continuous path from `s` to
`t` passes through every point of a segment from `s` to `t`. -/
theorem mem_image_of_isSegment (h4 : FourPoint X) {s t : X} {γ : ℝ → X}
    (hγ : IsSegment s t γ) {q : ℝ → X} (hq : ContinuousOn q (Icc 0 1)) (hq0 : q 0 = s)
    (hq1 : q 1 = t) {a : ℝ} (ha : a ∈ Icc 0 (dist s t)) : γ a ∈ q '' Icc 0 1 := by
  rcases eq_or_lt_of_le ha.1 with h0 | h0
  · subst h0
    exact ⟨0, left_mem_Icc.mpr zero_le_one, by rw [hq0, hγ.1]⟩
  rcases eq_or_lt_of_le ha.2 with hD | hD
  · subst hD
    exact ⟨1, right_mem_Icc.mpr zero_le_one, by rw [hq1, hγ.2.1]⟩
  by_contra hc
  set c := γ a
  have hsc : dist c s = a := by rw [dist_comm]; exact hγ.dist_left ha
  have hct : dist c t = dist s t - a := hγ.dist_right ha
  set O₁ : Set X := {p | 0 < gromovProduct c s p}
  set O₂ : Set X := {p | p ≠ c ∧ gromovProduct c s p = 0}
  have hO₁ : IsOpen O₁ := isOpen_lt continuous_const (continuous_gromovProduct c s)
  have hO₂ : IsOpen O₂ := isOpen_gromovProduct_eq_zero h4 c s
  have hpre : IsPreconnected (q '' Icc 0 1) := isPreconnected_Icc.image q hq
  have hcover : q '' Icc 0 1 ⊆ O₁ ∪ O₂ := by
    rintro p ⟨r, hr, rfl⟩
    rcases eq_or_lt_of_le (gromovProduct_nonneg c s (q r)) with h | h
    · exact Or.inr ⟨fun he ↦ hc ⟨r, hr, he⟩, h.symm⟩
    · exact Or.inl h
  have hs : s ∈ q '' Icc 0 1 ∩ O₁ := by
    refine ⟨⟨0, left_mem_Icc.mpr zero_le_one, hq0⟩, ?_⟩
    show 0 < gromovProduct c s s
    simp only [Metric.gromovProduct_eq]
    rw [hsc, dist_self]
    linarith
  have ht : t ∈ q '' Icc 0 1 ∩ O₂ := by
    refine ⟨⟨1, right_mem_Icc.mpr zero_le_one, hq1⟩, fun he ↦ ?_, ?_⟩
    · have h1 : dist c t = dist s t - a := hγ.dist_right ha
      have h2 : dist c t = 0 := by rw [he, dist_self]
      linarith
    · simp only [Metric.gromovProduct_eq]
      rw [hsc, hct]
      ring
  obtain ⟨p, -, h1, h2⟩ := hpre O₁ O₂ hO₁ hO₂ hcover ⟨s, hs⟩ ⟨t, ht⟩
  rw [mem_ofPred_eq] at h1
  rw [h2.2] at h1
  exact lt_irrefl _ h1

/-- **Arcs are segments.** Under the four-point condition, when segments exist between
any two points, an injective continuous path from `s` to `t` has the image of the
segment from `s` to `t`. -/
theorem image_eq_of_injOn (h4 : FourPoint X) (hseg : ∀ x y : X, ∃ γ, IsSegment x y γ)
    {s t : X} {γ : ℝ → X} (hγ : IsSegment s t γ) {q : ℝ → X} (hq : ContinuousOn q (Icc 0 1))
    (hinj : InjOn q (Icc 0 1)) (hq0 : q 0 = s) (hq1 : q 1 = t) :
    q '' Icc 0 1 = γ '' Icc 0 (dist s t) := by
  apply Subset.antisymm
  · rintro _ ⟨r₀, hr₀, rfl⟩
    by_contra hp
    set p := q r₀ with hpdef
    set D := dist s t
    set a := (dist s p + D - dist p t) / 2 with hadef
    have h1 := dist_triangle p s t
    have h2 := dist_triangle s t p
    have h3 := dist_triangle s p t
    have e1 := dist_comm p s
    have e2 := dist_comm t p
    have ha : a ∈ Icc 0 D := ⟨by rw [hadef]; linarith, by rw [hadef]; linarith⟩
    set c := γ a
    have hsc : dist s c = a := hγ.dist_left ha
    have hct : dist c t = D - a := hγ.dist_right ha
    have hcp : dist c p = dist s p - a := by
      apply le_antisymm
      · have h := h4 s t c p
        rw [hsc, dist_comm t p, dist_comm t c, hct] at h
        have hmax : max (a + dist p t) (dist s p + (D - a)) = dist s p + (D - a) := by
          rw [hadef]
          apply max_eq_right
          linarith
        rw [hmax] at h
        linarith
      · linarith [dist_triangle s c p]
    have hcne : c ≠ p := fun h ↦ hp ⟨a, ha, h⟩
    -- the path from `s` to `p`
    obtain ⟨γ₁, hγ₁⟩ := hseg s p
    have hc₁ : γ₁ (dist s c) = c := eq_of_dist_add_dist h4 hγ₁ (by rw [hsc, hcp]; ring)
    have hq₁ : ContinuousOn (fun θ ↦ q (r₀ * θ)) (Icc 0 1) := by
      refine hq.comp (continuous_const.mul continuous_id).continuousOn ?_
      intro θ hθ
      exact ⟨mul_nonneg hr₀.1 hθ.1, (mul_le_of_le_one_left hθ.1 hr₀.2).trans hθ.2⟩
    have hdc₁ : dist s c ∈ Icc 0 (dist s p) := ⟨dist_nonneg, by rw [hsc]; linarith⟩
    obtain ⟨θ₁, hθ₁, he₁⟩ := mem_image_of_isSegment h4 hγ₁ hq₁ (by simp [hq0]) (by simp [hpdef])
      hdc₁
    -- the path from `p` to `t`
    obtain ⟨γ₂, hγ₂⟩ := hseg p t
    have hc₂ : γ₂ (dist p c) = c := eq_of_dist_add_dist h4 hγ₂ (by
      rw [dist_comm p c, hcp, hct, hadef]
      ring)
    have hq₂ : ContinuousOn (fun θ ↦ q (r₀ + θ * (1 - r₀))) (Icc 0 1) := by
      refine hq.comp (continuous_const.add (continuous_id.mul continuous_const)).continuousOn ?_
      intro θ hθ
      refine ⟨by nlinarith [hr₀.1, hr₀.2, hθ.1], by nlinarith [hr₀.1, hr₀.2, hθ.2]⟩
    have hdc₂ : dist p c ∈ Icc 0 (dist p t) := ⟨dist_nonneg, by
      rw [dist_comm p c, hcp]
      linarith⟩
    obtain ⟨θ₂, hθ₂, he₂⟩ := mem_image_of_isSegment h4 hγ₂ hq₂ (by simp [hpdef]) (by simp [hq1])
      hdc₂
    simp only at he₁ he₂
    rw [hc₁] at he₁
    rw [hc₂] at he₂
    have hm₁ : r₀ * θ₁ ∈ Icc (0 : ℝ) 1 :=
      ⟨mul_nonneg hr₀.1 hθ₁.1, (mul_le_of_le_one_left hθ₁.1 hr₀.2).trans hθ₁.2⟩
    have hm₂ : r₀ + θ₂ * (1 - r₀) ∈ Icc (0 : ℝ) 1 :=
      ⟨by nlinarith [hr₀.1, hr₀.2, hθ₂.1], by nlinarith [hr₀.1, hr₀.2, hθ₂.2]⟩
    have heq := hinj hm₁ hm₂ (he₁.trans he₂.symm)
    have hr : r₀ * θ₁ = r₀ := by nlinarith [hr₀.1, hr₀.2, hθ₁.1, hθ₁.2, hθ₂.1, hθ₂.2]
    rw [hr] at he₁
    exact hcne he₁.symm
  · rintro _ ⟨a, ha, rfl⟩
    exact mem_image_of_isSegment h4 hγ hq hq0 hq1 ha

end GromovProduct

section Construction

/-- Dyadic points of a segment built from a midpoint choice. -/
noncomputable def dyadicSeg (mid : X → X → X) (s t : X) : ℕ → ℕ → X
  | 0, i => if i = 0 then s else t
  | m + 1, i => if i % 2 = 0 then dyadicSeg mid s t m (i / 2)
      else mid (dyadicSeg mid s t m (i / 2)) (dyadicSeg mid s t m (i / 2 + 1))

variable {mid : X → X → X} {s t : X}

omit [MetricSpace X] in
theorem dyadicSeg_zero_right (m : ℕ) : dyadicSeg mid s t m 0 = s := by
  induction m with
  | zero => simp [dyadicSeg]
  | succ m ih => simp [dyadicSeg, ih]

omit [MetricSpace X] in
theorem dyadicSeg_pow (m : ℕ) : dyadicSeg mid s t m (2 ^ m) = t := by
  induction m with
  | zero => simp [dyadicSeg]
  | succ m ih =>
    simp only [dyadicSeg, pow_succ, Nat.mul_mod_left, ↓reduceIte, Nat.mul_div_cancel _ two_pos]
    exact ih

omit [MetricSpace X] in
theorem dyadicSeg_two_mul (m i : ℕ) : dyadicSeg mid s t (m + 1) (2 * i) = dyadicSeg mid s t m i := by
  simp [dyadicSeg]

theorem dyadicSeg_adjacent
    (hmid : ∀ x y, dist x (mid x y) = dist x y / 2 ∧ dist (mid x y) y = dist x y / 2)
    (m : ℕ) : ∀ i < 2 ^ m, dist (dyadicSeg mid s t m i) (dyadicSeg mid s t m (i + 1)) =
      dist s t / 2 ^ m := by
  induction m with
  | zero =>
    intro i hi
    have : i = 0 := by simpa using hi
    subst this
    simp [dyadicSeg]
  | succ m ih =>
    intro i hi
    obtain ⟨a, rfl | rfl⟩ := Nat.even_or_odd' i
    · have ha : a < 2 ^ m := by rw [pow_succ] at hi; omega
      have h1 : dyadicSeg mid s t (m + 1) (2 * a + 1) =
          mid (dyadicSeg mid s t m a) (dyadicSeg mid s t m (a + 1)) := by
        simp only [dyadicSeg]
        rw [ite_eq_right (by omega), show (2 * a + 1) / 2 = a by omega]
      rw [dyadicSeg_two_mul, h1, (hmid _ _).1, ih a ha, pow_succ]
      ring
    · have ha : a < 2 ^ m := by rw [pow_succ] at hi; omega
      have h1 : dyadicSeg mid s t (m + 1) (2 * a + 1) =
          mid (dyadicSeg mid s t m a) (dyadicSeg mid s t m (a + 1)) := by
        simp only [dyadicSeg]
        rw [ite_eq_right (by omega), show (2 * a + 1) / 2 = a by omega]
      rw [show 2 * a + 1 + 1 = 2 * (a + 1) by ring, dyadicSeg_two_mul, h1, (hmid _ _).2,
        ih a ha, pow_succ]
      ring

theorem dyadicSeg_dist_le
    (hmid : ∀ x y, dist x (mid x y) = dist x y / 2 ∧ dist (mid x y) y = dist x y / 2)
    (m : ℕ) {i : ℕ} : ∀ j, i ≤ j → j ≤ 2 ^ m →
      dist (dyadicSeg mid s t m i) (dyadicSeg mid s t m j) ≤ ((j : ℝ) - i) * (dist s t / 2 ^ m) := by
  intro j
  induction j with
  | zero =>
    intro hij _
    have : i = 0 := by omega
    subst this
    simp
  | succ j ih =>
    intro hij hj
    rcases eq_or_lt_of_le hij with h | h
    · subst h
      simp
    · have := ih (by omega) (by omega)
      have hadj := dyadicSeg_adjacent hmid m j (by omega) (s := s) (t := t)
      calc dist (dyadicSeg mid s t m i) (dyadicSeg mid s t m (j + 1)) ≤
            dist (dyadicSeg mid s t m i) (dyadicSeg mid s t m j) +
              dist (dyadicSeg mid s t m j) (dyadicSeg mid s t m (j + 1)) := dist_triangle _ _ _
        _ ≤ ((j : ℝ) - i) * (dist s t / 2 ^ m) + dist s t / 2 ^ m := by rw [hadj]; linarith
        _ = (((j + 1 : ℕ) : ℝ) - i) * (dist s t / 2 ^ m) := by push_cast; ring

theorem dyadicSeg_dist
    (hmid : ∀ x y, dist x (mid x y) = dist x y / 2 ∧ dist (mid x y) y = dist x y / 2)
    (m : ℕ) {i j : ℕ} (hi : i ≤ 2 ^ m) (hj : j ≤ 2 ^ m) :
    dist (dyadicSeg mid s t m i) (dyadicSeg mid s t m j) = |(i : ℝ) - j| * (dist s t / 2 ^ m) := by
  have hpos : (0 : ℝ) < 2 ^ m := by positivity
  have key : ∀ i j, i ≤ j → j ≤ 2 ^ m →
      dist (dyadicSeg mid s t m i) (dyadicSeg mid s t m j) = ((j : ℝ) - i) * (dist s t / 2 ^ m) := by
    intro i j hij hj
    apply le_antisymm (dyadicSeg_dist_le hmid m j hij hj)
    have h0 := dyadicSeg_dist_le hmid m (s := s) (t := t) (i := 0) i (Nat.zero_le _) (hij.trans hj)
    have h2 := dyadicSeg_dist_le hmid m (s := s) (t := t) (i := j) (2 ^ m) hj le_rfl
    have htri := dist_triangle4 (dyadicSeg mid s t m 0) (dyadicSeg mid s t m i)
      (dyadicSeg mid s t m j) (dyadicSeg mid s t m (2 ^ m))
    rw [dyadicSeg_zero_right, dyadicSeg_pow] at htri
    rw [dyadicSeg_zero_right] at h0
    rw [dyadicSeg_pow] at h2
    have hD : dist s t = (2 : ℝ) ^ m * (dist s t / 2 ^ m) := by field_simp
    push_cast at h0 h2
    nlinarith [hD]
  rcases le_total i j with h | h
  · rw [key i j h hj, abs_sub_comm, abs_of_nonneg (by exact_mod_cast (sub_nonneg.mpr
      (by exact_mod_cast h : (i : ℝ) ≤ j)))]
  · rw [dist_comm, key j i h hi, abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast h : (j : ℝ) ≤ i))]

end Construction

section Limit

theorem floor_two_mul_bounds {y : ℝ} (hy : 0 ≤ y) :
    ⌊2 * y⌋₊ = 2 * ⌊y⌋₊ ∨ ⌊2 * y⌋₊ = 2 * ⌊y⌋₊ + 1 := by
  have h1 : 2 * ⌊y⌋₊ ≤ ⌊2 * y⌋₊ := by
    apply Nat.le_floor
    push_cast
    linarith [Nat.floor_le hy]
  have h2 : ⌊2 * y⌋₊ < 2 * ⌊y⌋₊ + 2 := by
    rw [Nat.floor_lt (by linarith)]
    push_cast
    linarith [Nat.lt_floor_add_one y]
  omega

/-- **Segments from midpoints.** In a complete metric space with midpoints, any two
points are joined by a geodesic segment. -/
theorem exists_isSegment [CompleteSpace X] (hm : HasMidpoints X) (s t : X) :
    ∃ γ, IsSegment s t γ := by
  classical
  choose mid hmid using hm
  set D := dist s t with hDdef
  rcases eq_or_lt_of_le (dist_nonneg (x := s) (y := t)) with hD | hD
  · have hst : s = t := dist_eq_zero.mp hD.symm
    refine ⟨fun _ ↦ s, rfl, hst, ?_⟩
    intro a ha b hb
    rw [← hD] at ha hb
    have ha0 : a = 0 := le_antisymm ha.2 ha.1
    have hb0 : b = 0 := le_antisymm hb.2 hb.1
    simp [ha0, hb0]
  set idx : ℕ → ℝ → ℕ := fun m a ↦ ⌊a / D * 2 ^ m⌋₊ with hidx
  have hidx_le : ∀ m a, a ≤ D → idx m a ≤ 2 ^ m := by
    intro m a ha
    apply Nat.floor_le_of_le
    push_cast
    have : a / D ≤ 1 := (div_le_one hD).mpr ha
    nlinarith [pow_pos (two_pos : (0 : ℝ) < 2) m]
  have hidx_succ : ∀ m a, 0 ≤ a → idx (m + 1) a = 2 * idx m a ∨ idx (m + 1) a = 2 * idx m a + 1 := by
    intro m a ha
    have := floor_two_mul_bounds (y := a / D * 2 ^ m) (by positivity)
    simp only [hidx, pow_succ]
    rwa [show a / D * (2 ^ m * 2) = 2 * (a / D * 2 ^ m) by ring]
  set u : ℝ → ℕ → X := fun a m ↦ dyadicSeg mid s t m (idx m a) with hu
  have hstep : ∀ a ∈ Icc 0 D, ∀ m, dist (u a m) (u a (m + 1)) ≤ 2 * D / 2 / 2 ^ m := by
    intro a ha m
    have hle1 := hidx_le (m + 1) a ha.2
    have hle0 := hidx_le m a ha.2
    simp only [hu]
    rw [← dyadicSeg_two_mul m (idx m a) (mid := mid) (s := s) (t := t),
      dyadicSeg_dist hmid (m + 1) (by rw [pow_succ]; omega) hle1]
    have hpos : (0 : ℝ) < 2 ^ m := by positivity
    have habs : |((2 * idx m a : ℕ) : ℝ) - (idx (m + 1) a : ℝ)| ≤ 1 := by
      rcases hidx_succ m a ha.1 with h | h <;> rw [h] <;> push_cast <;> norm_num
    calc |((2 * idx m a : ℕ) : ℝ) - (idx (m + 1) a : ℝ)| * (D / 2 ^ (m + 1)) ≤ 1 * (D / 2 ^ (m + 1)) :=
          mul_le_mul_of_nonneg_right habs (by positivity)
      _ ≤ 2 * D / 2 / 2 ^ m := by
          rw [pow_succ, one_mul]
          apply div_le_div_of_nonneg_left hD.le hpos (by nlinarith)
            |>.trans_eq (by ring)
  have hcauchy : ∀ a ∈ Icc 0 D, CauchySeq (u a) := fun a ha ↦
    cauchySeq_of_le_geometric_two (hstep a ha)
  have : Nonempty X := ⟨s⟩
  let γ : ℝ → X := fun a ↦ if a ∈ Icc 0 D then limUnder atTop (u a) else s
  have hlim : ∀ a ∈ Icc 0 D, Tendsto (u a) atTop (𝓝 (γ a)) := by
    intro a ha
    simp only [γ, ite_eq_left ha]
    exact tendsto_nhds_limUnder (cauchySeq_tendsto_of_complete (hcauchy a ha))
  have hpow : Tendsto (fun m : ℕ ↦ (2 : ℝ) ^ m) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt one_lt_two
  have hscaled : ∀ a ∈ Icc 0 D, Tendsto (fun m ↦ (idx m a : ℝ) * (D / 2 ^ m)) atTop (𝓝 a) := by
    intro a ha
    have h := ((tendsto_nat_floor_mul_div_atTop (div_nonneg ha.1 hD.le)).comp hpow).mul_const D
    rw [div_mul_cancel₀ a hD.ne'] at h
    apply h.congr
    intro m
    simp only [Function.comp_apply, hidx]
    ring
  have h0mem : (0 : ℝ) ∈ Icc 0 D := ⟨le_rfl, hD.le⟩
  have hDmem : D ∈ Icc 0 D := ⟨hD.le, le_rfl⟩
  refine ⟨γ, ?_, ?_, ?_⟩
  · refine tendsto_nhds_unique (hlim 0 h0mem) (tendsto_const_nhds.congr fun m ↦ ?_)
    simp [hu, hidx, dyadicSeg_zero_right]
  · refine tendsto_nhds_unique (hlim D hDmem) (tendsto_const_nhds.congr fun m ↦ ?_)
    have : idx m D = 2 ^ m := by
      show ⌊D / D * 2 ^ m⌋₊ = 2 ^ m
      rw [div_self hD.ne', one_mul]
      exact_mod_cast Nat.floor_natCast (2 ^ m)
    simp only [hu, this, dyadicSeg_pow]
  · intro a ha b hb
    have h1 := (hlim a ha).dist (hlim b hb)
    have h2 : Tendsto (fun m ↦ dist (u a m) (u b m)) atTop (𝓝 |a - b|) := by
      have := ((hscaled a ha).sub (hscaled b hb)).abs
      apply this.congr
      intro m
      simp only [hu]
      rw [dyadicSeg_dist hmid m (hidx_le m a ha.2) (hidx_le m b hb.2), ← sub_mul, abs_mul,
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ D / 2 ^ m)]
    exact tendsto_nhds_unique h1 h2

/-- Approximate midpoints at every scale give exact midpoints in a compact space. -/
theorem hasMidpoints_of_approx [CompactSpace X] (h : ∀ ε > 0, ApproxMidpoints ε X) :
    HasMidpoints X := by
  intro x y
  choose m hm using fun n : ℕ ↦ h (1 / ((n : ℝ) + 1)) (by positivity) x y
  obtain ⟨z, -, φ, hφ, hz⟩ := isCompact_univ.tendsto_subseq (fun n ↦ mem_univ (m n))
  have hε : Tendsto (fun n ↦ 1 / ((φ n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ.tendsto_atTop
  have key : ∀ (f : X → ℝ), Continuous f → (∀ n, |f (m n) - dist x y / 2| ≤ 1 / ((n : ℝ) + 1)) →
      f z = dist x y / 2 := by
    intro f hf hb
    have h1 : Tendsto (fun n ↦ f (m (φ n))) atTop (𝓝 (f z)) := (hf.tendsto z).comp hz
    have h2 : Tendsto (fun n ↦ f (m (φ n))) atTop (𝓝 (dist x y / 2)) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      exact squeeze_zero (fun _ ↦ norm_nonneg _) (fun n ↦ hb (φ n)) hε
    exact tendsto_nhds_unique h1 h2
  exact ⟨z, key (dist x) (continuous_const.dist continuous_id) (fun n ↦ (hm n).1),
    key (fun w ↦ dist w y) (continuous_id.dist continuous_const) (fun n ↦ (hm n).2)⟩

/-- **Complete `0`-hyperbolic spaces with midpoints are real trees.** -/
theorem isRealTree_of_fourPoint [CompleteSpace X] (h4 : FourPoint X) (hm : HasMidpoints X) :
    IsRealTree X := fun _ _ ↦
  ⟨exists_isSegment hm _ _, fun _ _ ↦ segment_unique h4,
    fun _ _ hγ hq hinj hq0 hq1 ↦ image_eq_of_injOn h4 (exists_isSegment hm) hγ hq hinj hq0 hq1⟩

end Limit

section Invariance

variable {Y : Type*} [MetricSpace Y]

theorem FourPoint.of_isometryEquiv (e : X ≃ᵢ Y) (h : FourPoint X) : FourPoint Y := by
  intro x y z w
  have := h (e.symm x) (e.symm y) (e.symm z) (e.symm w)
  simpa only [e.symm.dist_eq] using this

theorem ApproxMidpoints.of_isometryEquiv (e : X ≃ᵢ Y) {ε : ℝ} (h : ApproxMidpoints ε X) :
    ApproxMidpoints ε Y := by
  intro x y
  obtain ⟨m, hm⟩ := h (e.symm x) (e.symm y)
  refine ⟨e m, ?_⟩
  have h1 : dist x (e m) = dist (e.symm x) m := by
    rw [← e.symm.dist_eq, IsometryEquiv.symm_apply_apply]
  have h2 : dist (e m) y = dist m (e.symm y) := by
    rw [← e.symm.dist_eq, IsometryEquiv.symm_apply_apply]
  rw [h1, h2, ← e.symm.dist_eq x y]
  exact hm

end Invariance

end BGW.ContinuumTrees.RealTree

