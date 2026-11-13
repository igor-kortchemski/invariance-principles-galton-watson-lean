/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.DiscreteHeightApproxBasic
import Mathlib.Probability.Independence.InfinitePi

/-!
# Reversal of the discrete forest walk

Reversal retains weak records, and sends the half-open forest interval to the
positive integer times through the endpoint. It preserves the iid sequence law.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal Classical
open BGW.StableTrees.DiscreteForest

namespace BGW.StableTrees.DiscreteHeightApprox

private def revIndex (k i : ℕ) : ℕ := if i < k then k - 1 - i else i

private theorem revIndex_involutive (k : ℕ) : Function.Involutive (revIndex k) := by
  intro i
  unfold revIndex
  split_ifs <;> omega

/-- Reversal of a finite prefix is measurable. -/
theorem measurable_revSeq (k : ℕ) : Measurable (revSeq k) := by
  apply Measurable.of_eval
  intro i
  unfold revSeq
  split_ifs <;> exact measurable_pi_apply _

/-- Exchangeability: reversing the first `k` coordinates preserves the iid law. -/
theorem map_revSeq_offspringSeqLaw (μ : PMF ℕ) (k : ℕ) :
    ((offspringSeqLaw μ : ProbabilityMeasure (ℕ → ℕ)) : Measure (ℕ → ℕ)).map (revSeq k) =
      ((offspringSeqLaw μ : ProbabilityMeasure (ℕ → ℕ)) : Measure (ℕ → ℕ)) := by
  have he : revSeq k = (fun (ω : ℕ → ℕ) i => ω (revIndex k i)) := by
    funext ω i
    unfold revSeq revIndex
    split_ifs <;> rfl
  rw [he]
  exact Measure.map_infinitePi_infinitePi_of_inj
    (P := fun _ : ℕ => μ.toMeasure) (revIndex_involutive k).injective

/-- `walk (revSeq k ω) u = W_k - W_{k-u}` for `u ≤ k`. -/
theorem walk_revSeq (ω : ℕ → ℕ) {k u : ℕ} (hu : u ≤ k) :
    walk (revSeq k ω) u = walk ω k - walk ω (k - u) := by
  induction u with
  | zero => simp [walk]
  | succ u ih =>
    rw [walk_succ_eq, ih (by omega)]
    have he := walk_succ_eq ω (k - (u + 1))
    have hk : k - (u + 1) + 1 = k - u := by omega
    rw [hk] at he
    have hu' : u < k := by omega
    simp only [revSeq, ite_eq_left hu']
    have hi : k - 1 - u = k - (u + 1) := by omega
    rw [hi]
    omega

/-- The reflected gap is nonnegative. -/
theorem reflGap_nonneg (ω : ℕ → ℕ) (u : ℕ) : 0 ≤ reflGap ω u := by
  apply sub_nonneg.mpr
  exact Finset.le_sup' (walk ω) (by simp : u ∈ Finset.range (u + 1))

/-- A zero gap is precisely a weak ascending record. -/
theorem reflGap_zero_iff_record (ω : ℕ → ℕ) (u : ℕ) :
    reflGap ω u = 0 ↔ ∀ v ≤ u, walk ω v ≤ walk ω u := by
  have hn := reflGap_nonneg ω u
  simp only [reflGap, sub_nonneg] at hn
  rw [reflGap, sub_eq_zero]
  constructor
  · intro he v hv
    rw [← he]
    exact Finset.le_sup' (walk ω) (Finset.mem_range.mpr (by omega))
  · intro h
    exact le_antisymm (Finset.sup'_le _ _
      (fun v hv => h v (Nat.le_of_lt_succ (Finset.mem_range.mp hv)))) hn

/-- A strict band condition can be tested at every preceding walk value. -/
theorem reflGap_lt_iff (ω : ℕ → ℕ) (u : ℕ) (a : ℝ) :
    (reflGap ω u : ℝ) < a ↔
      ∀ v ≤ u, (walk ω v : ℝ) - (walk ω u : ℝ) < a := by
  obtain ⟨v, hv, he⟩ := (Finset.range (u + 1)).exists_mem_eq_sup'
    ⟨0, by simp⟩ (walk ω)
  constructor
  · intro h v hv
    have hle := Finset.le_sup' (walk ω) (Finset.mem_range.mpr (by omega : v < u + 1))
    have hcast : (walk ω v : ℝ) ≤
        (((Finset.range (u + 1)).sup' ⟨0, by simp⟩ (walk ω) : ℤ) : ℝ) := by exact_mod_cast hle
    simp only [reflGap, Int.cast_sub] at h
    linarith
  · intro h
    have hv' : v ≤ u := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hv
    specialize h v hv'
    simpa only [reflGap, Int.cast_sub, he] using h

private theorem reversed_record_iff (ω : ℕ → ℕ) {k j : ℕ} (hj : j ≤ k) :
    reflGap (revSeq k ω) (k - j) = 0 ↔
      ∀ l, j ≤ l → l ≤ k → walk ω j ≤ walk ω l := by
  rw [reflGap_zero_iff_record]
  have hj' : k - (k - j) = j := by omega
  constructor
  · intro h l hjl hlk
    have he := h (k - l) (by omega)
    rw [walk_revSeq ω (by omega), walk_revSeq ω (by omega), hj',
      Nat.sub_sub_self hlk] at he
    omega
  · intro h v hv
    rw [walk_revSeq ω (by omega), walk_revSeq ω (by omega), hj']
    have he := h (k - v) (by omega) (by omega)
    omega

private theorem reversed_band_iff (ω : ℕ → ℕ) {k j : ℕ} (hj : j ≤ k) (a : ℝ) :
    (reflGap (revSeq k ω) (k - j) : ℝ) < a ↔
      ∀ l, j ≤ l → l ≤ k → (walk ω j : ℝ) - (walk ω l : ℝ) < a := by
  rw [reflGap_lt_iff]
  have hj' : k - (k - j) = j := by omega
  constructor
  · intro h l hjl hlk
    have he := h (k - l) (by omega)
    rw [walk_revSeq ω (by omega), walk_revSeq ω (by omega), hj',
      Nat.sub_sub_self hlk] at he
    push_cast at he
    linarith
  · intro h v hv
    rw [walk_revSeq ω (by omega), walk_revSeq ω (by omega), hj']
    have he := h (k - v) (by omega) (by omega)
    push_cast
    linarith

private theorem card_filter_reverse (k : ℕ) (P Q : ℕ → Prop)
    [DecidablePred P] [DecidablePred Q] (h : ∀ j < k, P j ↔ Q (k - j)) :
    ((Finset.range k).filter P).card = ((Finset.Icc 1 k).filter Q).card := by
  apply Finset.card_bij (fun j _ => k - j)
  · intro j hj
    obtain ⟨hj, hp⟩ := Finset.mem_filter.mp hj
    have hj' : j < k := Finset.mem_range.mp hj
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩,
      (h j hj').mp hp⟩
  · intro i hi j hj he
    have hi' := Finset.mem_range.mp (Finset.mem_filter.mp hi).1
    have hj' := Finset.mem_range.mp (Finset.mem_filter.mp hj).1
    omega
  · intro u hu
    obtain ⟨hu, hp⟩ := Finset.mem_filter.mp hu
    obtain ⟨hu1, huk⟩ := Finset.mem_Icc.mp hu
    have he : k - (k - u) = u := by omega
    refine ⟨k - u, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), ?_⟩, he⟩
    exact (h (k - u) (by omega)).mpr (he.symm ▸ hp)

/-- (Deterministic) the forest height is the weak ladder count of the reversed sequence. -/
theorem forestHeight_eq_weakLadderCount (ω : ℕ → ℕ) (k : ℕ) :
    forestHeight ω k = weakLadderCount (revSeq k ω) k := by
  exact card_filter_reverse k _ _ fun j hj =>
    (reversed_record_iff ω (Nat.le_of_lt hj)).symm

/-- (Deterministic) the discrete occupation count is the band count of the reversed sequence. -/
theorem discreteCount_eq_bandCount (ω : ℕ → ℕ) (k : ℕ) (a : ℝ) :
    discreteCount ω k a = bandCount (revSeq k ω) k a := by
  exact card_filter_reverse k _ _ fun j hj =>
    (reversed_band_iff ω (Nat.le_of_lt hj) a).symm

end BGW.StableTrees.DiscreteHeightApprox
