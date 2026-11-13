/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.DiscreteHeightApproxCycleBasic

/-!
# Stopping times and deterministic restart of weak ascending cycles

The first time at which the record count reaches `i` is a genuine stopping time with
value infinity if the record does not exist; on `EpochsFinite` it agrees with the natural
epoch. Shifting to an epoch sends that cycle to the first cycle. Prefix agreement through
a completed epoch determines every preceding cycle, even if later epochs fail.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal Classical
open BGW.StableTrees.DiscreteForest

namespace BGW.StableTrees.DiscreteHeightApprox

/-- The genuine extended stopping time of the `i`th positive-time weak record. -/
noncomputable def weakEpochStop (ω : ℕ → ℕ) (i : ℕ) : ℕ∞ :=
  ⨅ u : {u : ℕ // i ≤ weakLadderCount ω u}, (u.val : ℕ∞)

/-- A finite record stopping time is characterized entirely by its finite prefix. -/
private theorem weakEpochStop_eq_natCast_iff (ω : ℕ → ℕ) (i n : ℕ) :
    weakEpochStop ω i = n ↔
      i ≤ weakLadderCount ω n ∧ ∀ u < n, weakLadderCount ω u < i := by
  rw [weakEpochStop, ENat.iInf_eq_natCast_iff]
  constructor
  · rintro ⟨⟨⟨u, hu⟩, he⟩, hlo⟩
    have hun : u = n := ENat.natCast_inj.mp he
    subst u
    refine ⟨hu, fun u hun => ?_⟩
    by_contra hn
    have hle := hlo ⟨u, by omega⟩
    have : n ≤ u := ENat.natCast_le_natCast.mp hle
    omega
  · rintro ⟨hn, hpre⟩
    refine ⟨⟨⟨n, hn⟩, rfl⟩, ?_⟩
    intro u
    apply ENat.natCast_le_natCast.mpr
    by_contra hle
    have hlt := hpre u.val (by omega)
    exact (not_lt_of_ge u.property) hlt

/-- The extended epoch is a stopping time for the offspring coordinate filtration. -/
theorem isSeqStoppingTime_weakEpochStop (i : ℕ) :
    IsSeqStoppingTime (fun ω => weakEpochStop ω i) := by
  intro n ω ξ hn he
  refine ⟨?_, Iff.rfl⟩
  apply (weakEpochStop_eq_natCast_iff ξ i n).mpr
  obtain ⟨hni, hpre⟩ := (weakEpochStop_eq_natCast_iff ω i n).mp hn
  have hc (u : ℕ) (hu : u ≤ n) := weakLadderCount_eq_of_agree he hu
  exact ⟨by rwa [← hc n le_rfl], fun u hu => by rw [← hc u hu.le]; exact hpre u hu⟩

/-- At the `i`th epoch, precisely `i` positive-time weak records have occurred. -/
private theorem weakLadderCount_weakEpoch {ω : ℕ → ℕ} (hω : EpochsFinite ω) (i : ℕ) :
    weakLadderCount ω (weakEpoch ω i) = i := by
  have hs := strictMono_weakEpoch hω
  obtain ⟨hlo, hhi⟩ := weakEpoch_bracket hω (weakEpoch ω i)
  have hle := hs.le_iff_le.mp hlo
  have hlt := hs.lt_iff_lt.mp hhi
  omega

/-- Before the `i`th epoch fewer than `i` positive-time weak records have occurred. -/
private theorem weakLadderCount_lt_of_lt_epoch {ω : ℕ → ℕ} (hω : EpochsFinite ω) {i u : ℕ}
    (hu : u < weakEpoch ω i) : weakLadderCount ω u < i := by
  have hlo := (weakEpoch_bracket hω u).1
  exact (strictMono_weakEpoch hω).lt_iff_lt.mp (lt_of_le_of_lt hlo hu)

/-- The extended stopping time agrees with the natural epoch on finite paths. -/
theorem weakEpochStop_eq_epoch {ω : ℕ → ℕ} (hω : EpochsFinite ω) (i : ℕ) :
    weakEpochStop ω i = (weakEpoch ω i : ℕ∞) := by
  apply (weakEpochStop_eq_natCast_iff ω i _).mpr
  exact ⟨(weakLadderCount_weakEpoch hω i).ge,
    fun _ hu => weakLadderCount_lt_of_lt_epoch hω hu⟩

/-- Every genuine record stopping time is finite almost surely. -/
theorem ae_weakEpochStop_ne_top (μ : PMF ℕ) (hc : IsCritical μ) (hne : μ 1 ≠ 1) (i : ℕ) :
    ∀ᵐ ω ∂(offspringSeqLaw μ).toMeasure, weakEpochStop ω i ≠ ⊤ := by
  filter_upwards [ae_epochsFinite μ hc hne] with ω hω
  rw [weakEpochStop_eq_epoch hω]
  simp

/-- The first epoch after shifting to `τ_i` has duration `τ_{i+1} - τ_i`. -/
private theorem weakEpoch_shift_one {ω : ℕ → ℕ} (hω : EpochsFinite ω) (i : ℕ) :
    weakEpoch (shiftSeq (weakEpoch ω i) ω) 1 = weakEpoch ω (i + 1) - weakEpoch ω i := by
  let s := weakEpoch ω i
  let e := weakEpoch ω (i + 1)
  have hse : s < e := weakEpoch_lt_succ hω i
  have hw : walk ω s ≤ walk ω e := by
    have he : weakEpoch ω i < nextEpoch ω (weakEpoch ω i) ∧
        walk ω (weakEpoch ω i) ≤ walk ω (nextEpoch ω (weakEpoch ω i)) :=
      Nat.sInf_mem (hω i)
    simpa only [← weakEpoch_succ] using he.2
  have hz : walk (shiftSeq s ω) 0 = 0 := by simp [walk]
  have hhit : 0 < e - s ∧ walk (shiftSeq s ω) 0 ≤ walk (shiftSeq s ω) (e - s) := by
    rw [hz, walk_shiftSeq, Nat.add_sub_of_le hse.le]
    exact ⟨by omega, by omega⟩
  have hmem : 0 < nextEpoch (shiftSeq s ω) 0 ∧
      walk (shiftSeq s ω) 0 ≤ walk (shiftSeq s ω) (nextEpoch (shiftSeq s ω) 0) :=
    Nat.sInf_mem (s := {u | 0 < u ∧
      walk (shiftSeq s ω) 0 ≤ walk (shiftSeq s ω) u}) ⟨e - s, hhit⟩
  have hle : nextEpoch (shiftSeq s ω) 0 ≤ e - s := Nat.sInf_le hhit
  have hback : nextEpoch ω s ≤ s + nextEpoch (shiftSeq s ω) 0 := by
    apply Nat.sInf_le
    refine ⟨by omega, ?_⟩
    rw [hz, walk_shiftSeq] at hmem
    omega
  have he : nextEpoch ω s = e := (weakEpoch_succ ω i).symm
  rw [he] at hback
  rw [weakEpoch_succ, weakEpoch_zero]
  change nextEpoch (shiftSeq s ω) 0 = e - s
  omega

/-- The cycle occupation after shifting to its initial epoch is the first-cycle occupation. -/
theorem clusterVisits_shift_zero {ω : ℕ → ℕ} (hω : EpochsFinite ω) (a : ℝ) (i : ℕ) :
    clusterVisits ω a i = clusterVisits (shiftSeq (weakEpoch ω i) ω) a 0 := by
  unfold clusterVisits
  rw [weakEpoch_zero, weakEpoch_shift_one hω i]
  let s := weakEpoch ω i
  let e := weakEpoch ω (i + 1)
  have hse : s < e := weakEpoch_lt_succ hω i
  have hz : walk (shiftSeq s ω) 0 = 0 := by simp [walk]
  have hgap (u : ℕ) (hu : s ≤ u) :
      walk (shiftSeq s ω) 0 - walk (shiftSeq s ω) (u - s) = walk ω s - walk ω u := by
    rw [hz, walk_shiftSeq, Nat.add_sub_of_le hu]
    ring
  apply Finset.card_bij (fun u _ => u - s)
  · intro u hu
    obtain ⟨hu, hp⟩ := Finset.mem_filter.mp hu
    obtain ⟨hsu, hue⟩ := Finset.mem_Ico.mp hu
    exact Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨by omega, by omega⟩,
      by rwa [hgap u hsu]⟩
  · intro u hu v hv he
    have hsu := (Finset.mem_Ico.mp (Finset.mem_filter.mp hu).1).1
    have hsv := (Finset.mem_Ico.mp (Finset.mem_filter.mp hv).1).1
    omega
  · intro u hu
    obtain ⟨hu, hp⟩ := Finset.mem_filter.mp hu
    obtain ⟨_, hue⟩ := Finset.mem_Ico.mp hu
    refine ⟨s + u, Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨by omega, by omega⟩, ?_⟩,
      by omega⟩
    have he := hgap (s + u) (by omega)
    simp only [Nat.add_sub_cancel_left] at he
    rwa [← he]

private theorem nextEpoch_eq_of_agree {ω ξ : ℕ → ℕ} {s n u : ℕ}
    (he : ∀ k < n, ω k = ξ k) (hu : u ≤ n)
    (hreturn : s < u ∧ walk ω s ≤ walk ω u) : nextEpoch ω s = nextEpoch ξ s := by
  have hsn : s ≤ n := by omega
  have hreturn' : s < u ∧ walk ξ s ≤ walk ξ u := by
    rwa [← walk_eq_of_agree he hsn, ← walk_eq_of_agree he hu]
  have hm : s < nextEpoch ω s ∧ walk ω s ≤ walk ω (nextEpoch ω s) :=
    Nat.sInf_mem (s := {u | s < u ∧ walk ω s ≤ walk ω u}) ⟨u, hreturn⟩
  have hm' : s < nextEpoch ξ s ∧ walk ξ s ≤ walk ξ (nextEpoch ξ s) :=
    Nat.sInf_mem (s := {u | s < u ∧ walk ξ s ≤ walk ξ u}) ⟨u, hreturn'⟩
  have hn : nextEpoch ω s ≤ n := (Nat.sInf_le hreturn).trans hu
  have hn' : nextEpoch ξ s ≤ n := (Nat.sInf_le hreturn').trans hu
  apply le_antisymm
  · apply Nat.sInf_le
    refine ⟨hm'.1, ?_⟩
    rw [walk_eq_of_agree he hsn, walk_eq_of_agree he hn']
    exact hm'.2
  · apply Nat.sInf_le
    refine ⟨hm.1, ?_⟩
    rw [← walk_eq_of_agree he hsn, ← walk_eq_of_agree he hn]
    exact hm.2

/-- Agreement through a completed epoch determines each earlier epoch. -/
private theorem weakEpoch_eq_of_agree {ω ξ : ℕ → ℕ} (hω : EpochsFinite ω) {n i : ℕ}
    (he : ∀ k < n, ω k = ξ k) (hi : weakEpoch ω i ≤ n) {j : ℕ} (hj : j ≤ i) :
    weakEpoch ω j = weakEpoch ξ j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    have hj' : j ≤ i := by omega
    have hu : weakEpoch ω (j + 1) ≤ n :=
      ((strictMono_weakEpoch hω).monotone hj).trans hi
    have hreturn : weakEpoch ω j < weakEpoch ω (j + 1) ∧
        walk ω (weakEpoch ω j) ≤ walk ω (weakEpoch ω (j + 1)) := by
      have hh : weakEpoch ω j < nextEpoch ω (weakEpoch ω j) ∧
          walk ω (weakEpoch ω j) ≤ walk ω (nextEpoch ω (weakEpoch ω j)) :=
        Nat.sInf_mem (hω j)
      simpa only [← weakEpoch_succ] using hh
    rw [weakEpoch_succ, weakEpoch_succ, ← ih hj']
    exact nextEpoch_eq_of_agree he hu hreturn

/-- Agreement through a completed epoch determines each preceding cycle occupation. -/
theorem clusterVisits_eq_of_agree {ω ξ : ℕ → ℕ} (hω : EpochsFinite ω) {n i j : ℕ}
    (he : ∀ k < n, ω k = ξ k) (hi : weakEpoch ω i ≤ n) (hj : j < i) (a : ℝ) :
    clusterVisits ω a j = clusterVisits ξ a j := by
  have hs := weakEpoch_eq_of_agree hω he hi (show j ≤ i by omega)
  have ht := weakEpoch_eq_of_agree hω he hi (show j + 1 ≤ i by omega)
  unfold clusterVisits
  rw [← hs, ← ht]
  congr 1
  apply Finset.filter_congr
  intro u hu
  obtain ⟨_, hue⟩ := Finset.mem_Ico.mp hu
  have hsn : weakEpoch ω j ≤ n := ((strictMono_weakEpoch hω).monotone (by omega)).trans hi
  have htn : weakEpoch ω (j + 1) ≤ n :=
    ((strictMono_weakEpoch hω).monotone (by omega)).trans hi
  rw [walk_eq_of_agree he hsn, walk_eq_of_agree he (by omega : u ≤ n)]

/-- Shifting to a finite weak epoch sends the next epoch to the cycle duration. -/
theorem weakEpoch_shift_duration {ω : ℕ → ℕ} (hω : EpochsFinite ω) (i : ℕ) :
    weakEpoch (shiftSeq (weakEpoch ω i) ω) 1 = weakEpoch ω (i + 1) - weakEpoch ω i :=
  weakEpoch_shift_one hω i

end BGW.StableTrees.DiscreteHeightApprox
