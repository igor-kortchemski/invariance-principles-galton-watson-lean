/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.Skorokhod.ExitPartitionAux
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Deterministic exit partitions

Restart exit times give a finite partition with small oscillation on its half-open blocks.
When successive exits of the walk are far apart and the initial and terminal windows are good,
Billingsley's modulus `w'` of the rescaled step path `t ↦ S_{⌊nt⌋} / b` is at most `4ε`
(`cadlagModulus_realStepPath_le`). This is the deterministic step of the tightness argument for
walks in a stable domain of attraction (Billingsley 1999, §12–13), following the campaign's
audited plan (node 8).
-/

@[expose] public section

open Filter Set

namespace BGW.Probability.RealWalk

open Classical in
/-- The first index `k ∈ (a, M]` with `|S_k - S_a| > r`, and the sentinel `M + 1` if none. -/
noncomputable def nextExit (M : ℕ) (r : ℝ) (ω : ℕ → ℝ) (a : ℕ) : ℕ :=
  if h : ∃ k, a < k ∧ k ≤ M ∧ r < |partialSum ω k - partialSum ω a| then Nat.find h else M + 1

/-- Restart exit times: `exitTimes M r ω 0 = 0` and the `(j+1)`-st exit is the first exit of the
walk restarted at the `j`-th one; the sentinel `M + 1` (absorbing) means "no further exit up to
index `M`". Actual exits are `≤ M`. -/
noncomputable def exitTimes (M : ℕ) (r : ℝ) (ω : ℕ → ℝ) : ℕ → ℕ
  | 0 => 0
  | j + 1 => if exitTimes M r ω j ≤ M then nextExit M r ω (exitTimes M r ω j) else M + 1

open Classical in
/-- The number of actual exits (indices `≤ M`, not counting the starting point `0`). -/
noncomputable def exitCount (M : ℕ) (r : ℝ) (ω : ℕ → ℝ) : ℕ :=
  ((Finset.range (M + 1)).filter (fun j => 1 ≤ j ∧ exitTimes M r ω j ≤ M)).card

/-- Two successive actual exits (the first being a genuine exit, `j ≥ 1`) are at most `l`
indices apart. The gap between the start `0` and the first exit is deliberately not covered
(it is the `initialBad` event). -/
def closeExit (M : ℕ) (r : ℝ) (l : ℕ) (ω : ℕ → ℝ) : Prop :=
  ∃ j : ℕ, 1 ≤ j ∧ exitTimes M r ω (j + 1) ≤ M ∧
    exitTimes M r ω (j + 1) - exitTimes M r ω j ≤ l

/-- The step path value `S_{⌊n t⌋} / b` at a real time `t`. -/
noncomputable def stepValue (n : ℕ) (b : ℝ) (ω : ℕ → ℝ) (t : ℝ) : ℝ :=
  partialSum ω ⌊(n : ℝ) * t⌋₊ / b

/-- Initial window: the path moves by more than `ε` from its start within time `2δ`. -/
def initialBad (T : ℝ) (n : ℕ) (b ε δ : ℝ) (ω : ℕ → ℝ) : Prop :=
  ∃ t : ℝ, 0 ≤ t ∧ t ≤ 2 * δ ∧ t ≤ T ∧ ε < |stepValue n b ω t - stepValue n b ω 0|

/-- Terminal window: after time `T - 2δ` the path moves by more than `ε` from its value at
`T - 2δ` (measured from the left endpoint of the window, up to and including `T`). -/
def terminalBad (T : ℝ) (n : ℕ) (b ε δ : ℝ) (ω : ℕ → ℝ) : Prop :=
  ∃ t : ℝ, T - 2 * δ ≤ t ∧ t ≤ T ∧
    ε < |stepValue n b ω t - stepValue n b ω (T - 2 * δ)|

/-- The walk oscillates by more than `ε b` in the initial window `[0, 2δ]` or in the terminal
window `[T - 2δ, T]`. -/
def edgeBad (T : ℝ) (n : ℕ) (b ε δ : ℝ) (ω : ℕ → ℝ) : Prop :=
  initialBad T n b ε δ ω ∨ terminalBad T n b ε δ ω

end BGW.Probability.RealWalk

namespace BGW.Skorokhod

open BGW.Probability.RealWalk

/-- The càdlàg floor-step path `t ↦ S_{⌊n t⌋} / b` on `[0,T]` (Node 2). The same formula is used
at `T`: if `n T` is an integer there is a genuine terminal jump. -/
noncomputable def realStepPath (T : ℝ) (n : ℕ) (b : ℝ) (ω : ℕ → ℝ) : D T ℝ where
  toFun t := partialSum ω ⌊(n : ℝ) * (t : ℝ)⌋₊ / b
  isCadlag' := isCadlag_stepPath n b ω

/-- Value of the step path: the partial sum up to `⌊n t⌋`, divided by `b`. -/
theorem realStepPath_apply {T : ℝ} {n : ℕ} {b : ℝ} {ω : ℕ → ℝ} (t : Set.Icc (0 : ℝ) T) :
    realStepPath T n b ω t = partialSum ω ⌊(n : ℝ) * (t : ℝ)⌋₊ / b := rfl

/-- The step path agrees with `stepValue`. -/
theorem realStepPath_apply_eq_stepValue {T : ℝ} {n : ℕ} {b : ℝ} {ω : ℕ → ℝ}
    (t : Set.Icc (0 : ℝ) T) : realStepPath T n b ω t = stepValue n b ω t := rfl

private lemma nextExit_le (M : ℕ) (r : ℝ) (ω : ℕ → ℝ) (a : ℕ) :
    nextExit M r ω a ≤ M + 1 := by
  classical
  unfold nextExit
  split_ifs with h
  · exact (Nat.find_spec h).2.1.trans (Nat.le_succ M)
  · exact le_rfl

private lemma nextExit_spec {M : ℕ} {r : ℝ} {ω : ℕ → ℝ} {a : ℕ}
    (h : nextExit M r ω a ≤ M) :
    a < nextExit M r ω a ∧ nextExit M r ω a ≤ M ∧
      r < |partialSum ω (nextExit M r ω a) - partialSum ω a| := by
  classical
  unfold nextExit at h ⊢
  split_ifs at h ⊢ with hex
  · exact Nat.find_spec hex
  · omega

private lemma nextExit_no_before {M : ℕ} {r : ℝ} {ω : ℕ → ℝ} {a k : ℕ}
    (hak : a < k) (hkM : k ≤ M) (hk : k < nextExit M r ω a) :
    |partialSum ω k - partialSum ω a| ≤ r := by
  classical
  by_contra! hbad
  have hex : ∃ q, a < q ∧ q ≤ M ∧ r < |partialSum ω q - partialSum ω a| :=
    ⟨k, hak, hkM, hbad⟩
  have hfind : nextExit M r ω a = Nat.find hex := by simp [nextExit, hex]
  rw [hfind] at hk
  exact (Nat.not_le_of_lt hk) (Nat.find_le (⟨hak, hkM, hbad⟩ : _))

private lemma lt_nextExit {M : ℕ} {r : ℝ} {ω : ℕ → ℝ} {a : ℕ} (ha : a ≤ M) :
    a < nextExit M r ω a := by
  by_cases h : nextExit M r ω a ≤ M
  · exact (nextExit_spec h).1
  · have heq := le_antisymm (nextExit_le M r ω a) (Nat.succ_le_of_lt (lt_of_not_ge h))
    omega

private lemma le_exitTimes_of_le (M : ℕ) (r : ℝ) (ω : ℕ → ℝ) {j : ℕ}
    (hj : j ≤ M + 1) : j ≤ exitTimes M r ω j := by
  induction j with
  | zero => simp [exitTimes]
  | succ j ih =>
      rw [exitTimes]
      split_ifs with h
      · have hlt := lt_nextExit (r := r) (ω := ω) h
        have hle := ih (by omega)
        omega
      · omega

private theorem lastExitExists (M : ℕ) (r : ℝ) (ω : ℕ → ℝ) :
    ∃ j, M < exitTimes M r ω (j + 1) := by
  refine ⟨M + 1, ?_⟩
  have hlt : M < exitTimes M r ω (M + 1) :=
    (le_exitTimes_of_le M r ω (j := M + 1) le_rfl).trans_lt' (by omega)
  have heq : exitTimes M r ω (M + 1 + 1) = M + 1 := by
    rw [exitTimes]
    split_ifs with h
    · exact (not_le_of_gt hlt h).elim
    · rfl
  rw [heq]
  omega

private noncomputable def lastExit (M : ℕ) (r : ℝ) (ω : ℕ → ℝ) : ℕ :=
  Nat.find (p := fun j => M < exitTimes M r ω (j + 1)) (lastExitExists M r ω)

private lemma lastExit_spec (M : ℕ) (r : ℝ) (ω : ℕ → ℝ) :
    M < exitTimes M r ω (lastExit M r ω + 1) := by
  unfold lastExit
  exact Nat.find_spec (lastExitExists M r ω)

private lemma exitTimes_le_of_lt_lastExit {M : ℕ} {r : ℝ} {ω : ℕ → ℝ} {j : ℕ}
    (hj : j < lastExit M r ω) : exitTimes M r ω (j + 1) ≤ M := by
  unfold lastExit at hj
  exact le_of_not_gt (Nat.find_min (lastExitExists M r ω) hj)

private lemma exitTimes_last_le (M : ℕ) (r : ℝ) (ω : ℕ → ℝ) :
    exitTimes M r ω (lastExit M r ω) ≤ M := by
  by_cases h : lastExit M r ω = 0
  · simp [h, exitTimes]
  · have hlt : lastExit M r ω - 1 < lastExit M r ω := Nat.sub_one_lt h
    have hle := exitTimes_le_of_lt_lastExit hlt
    rwa [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 h)] at hle

private lemma exitTimes_succ_eq_nextExit (M : ℕ) (r : ℝ) (ω : ℕ → ℝ)
    {j : ℕ} (hj : j ≤ lastExit M r ω) :
    exitTimes M r ω (j + 1) = nextExit M r ω (exitTimes M r ω j) := by
  have hprev : exitTimes M r ω j ≤ M := by
    rcases eq_or_lt_of_le hj with rfl | hlt
    · exact exitTimes_last_le M r ω
    · have hn := exitTimes_le_of_lt_lastExit hlt
      by_contra hnot
      have hgt : M < exitTimes M r ω j := lt_of_not_ge hnot
      simp [exitTimes, not_le_of_gt hgt] at hn
  simp [exitTimes, hprev]

private lemma exitTimes_lt_succ {M : ℕ} {r : ℝ} {ω : ℕ → ℝ} {j : ℕ}
    (hj : j < lastExit M r ω) : exitTimes M r ω j < exitTimes M r ω (j + 1) := by
  rw [exitTimes_succ_eq_nextExit M r ω hj.le]
  apply (nextExit_spec ?_).1
  rw [← exitTimes_succ_eq_nextExit M r ω hj.le]
  exact exitTimes_le_of_lt_lastExit hj

private lemma strictMonoOn_exitTimes (M : ℕ) (r : ℝ) (ω : ℕ → ℝ) :
    StrictMonoOn (exitTimes M r ω) (Set.Iic (lastExit M r ω)) := by
  apply strictMonoOn_Iic_of_lt_succ
  intro j hj
  exact exitTimes_lt_succ hj

private lemma mul_exitTime_div {n : ℕ} (hn : n ≠ 0) (a : ℕ) :
    (n : ℝ) * ((a : ℝ) / n) = a := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn
  field_simp

private lemma floor_exitTime_div {n : ℕ} (hn : n ≠ 0) (a : ℕ) :
    ⌊(n : ℝ) * ((a : ℝ) / n)⌋₊ = a := by
  rw [mul_exitTime_div hn, Nat.floor_natCast]

private lemma stepValue_sub_le_of_no_exit {T : ℝ} {M n : ℕ} {r b : ℝ}
    {ω : ℕ → ℝ} {a N : ℕ} {t : Set.Icc (0 : ℝ) T} (hn : 0 < n) (hb : 0 < b)
    (hr : 0 ≤ r) (hN : N = nextExit M r ω a) (ha : (a : ℝ) / n ≤ t)
    (ht : (t : ℝ) < (N : ℝ) / n) (hM : ⌊(n : ℝ) * t⌋₊ ≤ M) :
    |stepValue n b ω t - stepValue n b ω ((a : ℝ) / n)| ≤ r / b := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hna : (a : ℝ) ≤ (n : ℝ) * t := by
    calc
      (a : ℝ) = (n : ℝ) * ((a : ℝ) / n) := (mul_exitTime_div hn.ne' a).symm
      _ ≤ (n : ℝ) * t := mul_le_mul_of_nonneg_left ha (Nat.cast_nonneg n)
  have hak : a ≤ ⌊(n : ℝ) * t⌋₊ := Nat.le_floor hna
  have hN0 : N ≠ 0 := by
    intro hzero
    have ht' : (t : ℝ) < 0 := by
      rw [hzero] at ht
      simpa using ht
    exact (not_lt_of_ge t.property.1) ht'
  have hnt : (n : ℝ) * t < N := by
    calc
      (n : ℝ) * t < (n : ℝ) * ((N : ℝ) / n) := mul_lt_mul_of_pos_left ht hnpos
      _ = N := mul_exitTime_div hn.ne' N
  have htk : ⌊(n : ℝ) * t⌋₊ < N := (Nat.floor_lt' hN0).2 hnt
  have hdiff : |partialSum ω ⌊(n : ℝ) * t⌋₊ - partialSum ω a| ≤ r := by
    rcases eq_or_lt_of_le hak with heq | hlt
    · rw [← heq, sub_self, abs_zero]
      exact hr
    · rw [hN] at htk
      exact nextExit_no_before hlt hM htk
  simp only [stepValue, floor_exitTime_div hn.ne', ← sub_div, abs_div, abs_of_pos hb]
  exact (div_le_div_iff_of_pos_right hb).2 hdiff

private lemma stepValue_dist_le_of_no_exit {T : ℝ} {M n : ℕ} {r b : ℝ}
    {ω : ℕ → ℝ} {a N : ℕ} {s u : Set.Icc (0 : ℝ) T} (hn : 0 < n)
    (hb : 0 < b) (hr : 0 ≤ r) (hN : N = nextExit M r ω a)
    (has : (a : ℝ) / n ≤ s) (hs : (s : ℝ) < (N : ℝ) / n)
    (hau : (a : ℝ) / n ≤ u) (hu : (u : ℝ) < (N : ℝ) / n)
    (hsM : ⌊(n : ℝ) * s⌋₊ ≤ M) (huM : ⌊(n : ℝ) * u⌋₊ ≤ M) :
    |stepValue n b ω s - stepValue n b ω u| ≤ 2 * (r / b) := by
  have hs' := stepValue_sub_le_of_no_exit hn hb hr hN has hs hsM
  have hu' := stepValue_sub_le_of_no_exit hn hb hr hN hau hu huM
  calc
    |stepValue n b ω s - stepValue n b ω u| ≤
        |stepValue n b ω s - stepValue n b ω ((a : ℝ) / n)| +
          |stepValue n b ω u - stepValue n b ω ((a : ℝ) / n)| := by
      calc
        _ = |(stepValue n b ω s - stepValue n b ω ((a : ℝ) / n)) -
            (stepValue n b ω u - stepValue n b ω ((a : ℝ) / n))| := by
          congr 1
          ring
        _ ≤ _ := abs_sub _ _
    _ ≤ 2 * (r / b) := by linarith

private lemma floor_step_le_floor {T : ℝ} {n : ℕ} (t : Set.Icc (0 : ℝ) T) :
    ⌊(n : ℝ) * t⌋₊ ≤ ⌊(n : ℝ) * T⌋₊ := by
  apply Nat.floor_le_floor
  exact mul_le_mul_of_nonneg_left t.property.2 (Nat.cast_nonneg n)

private lemma exitTime_div_le_T {T : ℝ} {n a : ℕ} (hT : 0 < T) (hn : 0 < n)
    (ha : a ≤ ⌊(n : ℝ) * T⌋₊) : (a : ℝ) / n ≤ T := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  apply (div_le_iff₀ hnpos).2
  have hcast : (a : ℝ) ≤ (⌊(n : ℝ) * T⌋₊ : ℕ) := by exact_mod_cast ha
  have hfloor := Nat.floor_le (mul_nonneg (Nat.cast_nonneg n) hT.le)
  nlinarith

private lemma firstExit_gap {T : ℝ} {n : ℕ} {b ε δ : ℝ} {ω : ℕ → ℝ}
    (hT : 0 < T) (hn : 0 < n) (hb : 0 < b)
    (hinit : ¬ initialBad T n b ε δ ω)
    (hexit : exitTimes ⌊(n : ℝ) * T⌋₊ (ε * b) ω 1 ≤ ⌊(n : ℝ) * T⌋₊) :
    2 * δ < (exitTimes ⌊(n : ℝ) * T⌋₊ (ε * b) ω 1 : ℝ) / n := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  by_contra! hsmall
  apply hinit
  have hone : exitTimes ⌊(n : ℝ) * T⌋₊ (ε * b) ω 1 =
      nextExit ⌊(n : ℝ) * T⌋₊ (ε * b) ω 0 := by simp [exitTimes]
  have hnext : nextExit ⌊(n : ℝ) * T⌋₊ (ε * b) ω 0 ≤ ⌊(n : ℝ) * T⌋₊ := by
    rwa [← hone]
  have hspec := nextExit_spec hnext
  have htT := exitTime_div_le_T hT hn hexit
  refine ⟨(exitTimes ⌊(n : ℝ) * T⌋₊ (ε * b) ω 1 : ℝ) / n,
    by positivity, hsmall, htT, ?_⟩
  have hzero : partialSum ω 0 = 0 := by simp [partialSum]
  simp only [stepValue, floor_exitTime_div hn.ne', mul_zero, Nat.floor_zero,
    hzero, sub_zero, zero_div]
  rw [abs_div, abs_of_pos hb]
  apply (lt_div_iff₀ hb).2
  rw [hone]
  simpa only [hzero, sub_zero] using hspec.2.2

private lemma consecutiveExit_gap {T : ℝ} {n : ℕ} {b ε δ : ℝ} {ω : ℕ → ℝ}
    (hn : 0 < n)
    (hsep : ¬ closeExit ⌊(n : ℝ) * T⌋₊ (ε * b) ⌈2 * n * δ + 2⌉₊ ω)
    {j : ℕ} (hj : 1 ≤ j) (hjL : j < lastExit ⌊(n : ℝ) * T⌋₊ (ε * b) ω) :
    2 * δ < (exitTimes ⌊(n : ℝ) * T⌋₊ (ε * b) ω (j + 1) : ℝ) / n -
      (exitTimes ⌊(n : ℝ) * T⌋₊ (ε * b) ω j : ℝ) / n := by
  have hactual := exitTimes_le_of_lt_lastExit hjL
  have hlt := exitTimes_lt_succ hjL
  have hgap : ⌈2 * (n : ℝ) * δ + 2⌉₊ <
      exitTimes ⌊(n : ℝ) * T⌋₊ (ε * b) ω (j + 1) -
        exitTimes ⌊(n : ℝ) * T⌋₊ (ε * b) ω j := by
    by_contra! hle
    exact hsep ⟨j, hj, hactual, hle⟩
  have hceil := Nat.le_ceil (2 * (n : ℝ) * δ + 2)
  have hgc : (⌈2 * (n : ℝ) * δ + 2⌉₊ : ℝ) <
      ((exitTimes ⌊(n : ℝ) * T⌋₊ (ε * b) ω (j + 1) -
        exitTimes ⌊(n : ℝ) * T⌋₊ (ε * b) ω j : ℕ) : ℝ) := by exact_mod_cast hgap
  have hcastsub : ((exitTimes ⌊(n : ℝ) * T⌋₊ (ε * b) ω (j + 1) -
      exitTimes ⌊(n : ℝ) * T⌋₊ (ε * b) ω j : ℕ) : ℝ) =
      (exitTimes ⌊(n : ℝ) * T⌋₊ (ε * b) ω (j + 1) : ℝ) -
        (exitTimes ⌊(n : ℝ) * T⌋₊ (ε * b) ω j : ℝ) := Nat.cast_sub hlt.le
  rw [hcastsub] at hgc
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hmul : (n : ℝ) * (2 * δ) < (n : ℝ) *
      ((exitTimes ⌊(n : ℝ) * T⌋₊ (ε * b) ω (j + 1) : ℝ) / n -
        (exitTimes ⌊(n : ℝ) * T⌋₊ (ε * b) ω j : ℝ) / n) := by
    rw [mul_sub, mul_exitTime_div hn.ne', mul_exitTime_div hn.ne']
    nlinarith
  nlinarith [hmul]

private lemma exitTimes_last_succ_eq (M : ℕ) (r : ℝ) (ω : ℕ → ℝ) :
    exitTimes M r ω (lastExit M r ω + 1) = M + 1 := by
  rw [exitTimes_succ_eq_nextExit M r ω le_rfl]
  apply le_antisymm (nextExit_le M r ω _)
  have hspec := lastExit_spec M r ω
  rw [exitTimes_succ_eq_nextExit M r ω le_rfl] at hspec
  omega

private lemma T_lt_last_succ_div {T : ℝ} {n : ℕ} {r : ℝ} {ω : ℕ → ℝ}
    (hn : 0 < n) :
    T < (exitTimes ⌊(n : ℝ) * T⌋₊ r ω
      (lastExit ⌊(n : ℝ) * T⌋₊ r ω + 1) : ℝ) / n := by
  rw [exitTimes_last_succ_eq]
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  apply (lt_div_iff₀ hnpos).2
  norm_num only [Nat.cast_add, Nat.cast_one]
  have h := Nat.lt_floor_add_one ((n : ℝ) * T)
  nlinarith

private lemma stepValue_sub_le_terminal {T : ℝ} {n : ℕ} {b ε δ : ℝ}
    {ω : ℕ → ℝ} (hterm : ¬ terminalBad T n b ε δ ω)
    {t : Set.Icc (0 : ℝ) T} (ht : T - 2 * δ ≤ t) :
    |stepValue n b ω t - stepValue n b ω (T - 2 * δ)| ≤ ε := by
  by_contra! hbad
  exact hterm ⟨t, ht, t.property.2, hbad⟩

private noncomputable def endpointCuts (T : ℝ) (n : ℕ) (a : ℕ → ℕ) (K : ℕ) :
    Fin (K + 2) → ℝ := fun i =>
  if i.val = 0 then 0 else if i.val = K + 1 then T else (a i.val : ℝ) / n

private lemma endpointCuts_zero (T : ℝ) (n : ℕ) (a : ℕ → ℕ) (K : ℕ) :
    endpointCuts T n a K 0 = 0 := by simp [endpointCuts]

private lemma endpointCuts_last (T : ℝ) (n : ℕ) (a : ℕ → ℕ) (K : ℕ) :
    endpointCuts T n a K (Fin.last (K + 1)) = T := by
  simp [endpointCuts, Fin.last]

private lemma endpointCuts_inner {T : ℝ} {n : ℕ} {a : ℕ → ℕ} {K i : ℕ}
    (hi : 1 ≤ i) (hiK : i ≤ K) :
    endpointCuts T n a K ⟨i, by omega⟩ = (a i : ℝ) / n := by
  simp [endpointCuts, show i ≠ 0 by omega, show i ≠ K + 1 by omega]

private lemma strictMono_endpointCuts {T : ℝ} {n : ℕ} {a : ℕ → ℕ} {K : ℕ}
    (hT : 0 < T) (hn : 0 < n)
    (ha : ∀ i, 1 ≤ i → i ≤ K → 0 < a i)
    (hamono : ∀ i j, 1 ≤ i → i < j → j ≤ K → a i < a j)
    (haT : ∀ i, 1 ≤ i → i ≤ K → (a i : ℝ) / n < T) :
    StrictMono (endpointCuts T n a K) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  intro i j hij
  have hij' : i.val < j.val := hij
  by_cases hi : i.val = 0
  · by_cases hj : j.val = K + 1
    · simp [endpointCuts, hi, hj, hT]
    · have hj0 : j.val ≠ 0 := by omega
      have hjK : j.val ≤ K := by omega
      have haj : 0 < a j.val := ha j.val (by omega) hjK
      have hajR : (0 : ℝ) < a j.val := by exact_mod_cast haj
      simp [endpointCuts, hi, hj, hj0]
      positivity
  · by_cases hilast : i.val = K + 1
    · have := j.isLt
      omega
    · by_cases hjlast : j.val = K + 1
      · have hiK : i.val ≤ K := by omega
        have hi1 : 1 ≤ i.val := by omega
        simpa [endpointCuts, hi, hilast, hjlast] using haT i.val hi1 hiK
      · have hi1 : 1 ≤ i.val := by omega
        have hj1 : 1 ≤ j.val := by omega
        have hiK : i.val ≤ K := by omega
        have hjK : j.val ≤ K := by omega
        have hlt := hamono i.val j.val hi1 hij' hjK
        have hltR : (a i.val : ℝ) < a j.val := by exact_mod_cast hlt
        simp [endpointCuts, hi, hilast, hjlast, show j.val ≠ 0 by omega]
        exact (div_lt_div_iff_of_pos_right hnpos).2 hltR

private lemma endpointCuts_castSucc {T : ℝ} {n : ℕ} {a : ℕ → ℕ} {K : ℕ}
    (ha0 : a 0 = 0) (i : Fin (K + 1)) :
    endpointCuts T n a K i.castSucc = (a i.val : ℝ) / n := by
  by_cases hi : i.val = 0
  · simp [endpointCuts, hi, ha0]
  · have hiK : i.val ≠ K + 1 := by have := i.isLt; omega
    simp [endpointCuts, hi, hiK]

private lemma endpointCuts_succ_ne_last {T : ℝ} {n : ℕ} {a : ℕ → ℕ} {K : ℕ}
    {i : Fin (K + 1)} (hi : i.val ≠ K) :
    endpointCuts T n a K i.succ = (a (i.val + 1) : ℝ) / n := by
  simp [endpointCuts, Fin.succ, hi]

private lemma endpointCuts_succ_last {T : ℝ} {n : ℕ} {a : ℕ → ℕ} {K : ℕ}
    {i : Fin (K + 1)} (hi : i.val = K) :
    endpointCuts T n a K i.succ = T := by
  simp [endpointCuts, Fin.succ, hi]

/-- Node 8, deterministic bound. Hypotheses (i) no close consecutive exits at scale `ε b`, with
index gap `l = ⌈2 n δ + 2⌉₊` (so that consecutive cuts are more than `2δ` apart in time, the
`+2` absorbing the floors), (ii) no big initial move, (iii) no big terminal move. The exits
live in the walk of length `M = ⌊n T⌋₊`. Conclusion: `w'(δ) ≤ 4 ε` for Billingsley's modulus
(half-open blocks, all steps `> δ`, `δ < T`). -/
theorem cadlagModulus_realStepPath_le {T : ℝ} {n : ℕ} {b ε δ : ℝ} {ω : ℕ → ℝ}
    (hT : 0 < T) (hn : 1 ≤ n) (hb : 0 < b) (hε : 0 < ε) (hδ : 0 < δ) (hδT : 4 * δ < T)
    (hsep : ¬ closeExit ⌊(n : ℝ) * T⌋₊ (ε * b) ⌈2 * n * δ + 2⌉₊ ω)
    (hinit : ¬ initialBad T n b ε δ ω)
    (hterm : ¬ terminalBad T n b ε δ ω) :
    cadlagModulus (realStepPath T n b ω) δ ≤ 4 * ε := by
  classical
  have hnposNat : 0 < n := hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hnposNat
  let M := ⌊(n : ℝ) * T⌋₊
  let r := ε * b
  let τ := exitTimes M r ω
  let L := lastExit M r ω
  let K := if 0 < L ∧ T - (τ L : ℝ) / n ≤ δ then L - 1 else L
  have hr : 0 < r := mul_pos hε hb
  have hrb : r / b = ε := by dsimp [r]; field_simp
  have hτ0 : τ 0 = 0 := by simp [τ, exitTimes]
  have hKcases : K = L ∨ (0 < L ∧ K = L - 1 ∧ T - (τ L : ℝ) / n ≤ δ) := by
    dsimp [K]
    split_ifs with h
    · exact Or.inr ⟨h.1, rfl, h.2⟩
    · exact Or.inl rfl
  have hKL : K ≤ L := by
    rcases hKcases with h | h
    · omega
    · omega
  have hosc (j : ℕ) (hj : j ≤ L) (s u : Set.Icc (0 : ℝ) T)
      (hjs : (τ j : ℝ) / n ≤ s) (hs : (s : ℝ) < (τ (j + 1) : ℝ) / n)
      (hju : (τ j : ℝ) / n ≤ u) (hu : (u : ℝ) < (τ (j + 1) : ℝ) / n) :
      |stepValue n b ω s - stepValue n b ω u| ≤ 2 * ε := by
    have hnext : τ (j + 1) = nextExit M r ω (τ j) :=
      exitTimes_succ_eq_nextExit M r ω hj
    have h := stepValue_dist_le_of_no_exit hnposNat hb hr.le hnext hjs hs hju hu
      (floor_step_le_floor s) (floor_step_le_floor u)
    rwa [hrb] at h
  have hgap (j : ℕ) (hj : 1 ≤ j) (hjL : j < L) :
      2 * δ < (τ (j + 1) : ℝ) / n - (τ j : ℝ) / n :=
    consecutiveExit_gap hnposNat hsep hj hjL
  have hmono : StrictMono (endpointCuts T n τ K) := by
    apply strictMono_endpointCuts hT hnposNat
    · intro i hi hiK
      have h := strictMonoOn_exitTimes M r ω (show 0 ∈ Set.Iic L by simp)
        (show i ∈ Set.Iic L from hiK.trans hKL) (show 0 < i by omega)
      simpa [τ, hτ0] using h
    · intro i j hi hij hjK
      exact strictMonoOn_exitTimes M r ω (show i ∈ Set.Iic L from (le_of_lt hij).trans
        (hjK.trans hKL)) (show j ∈ Set.Iic L from hjK.trans hKL) hij
    · intro i hi hiK
      have hlastT : (τ L : ℝ) / n ≤ T := exitTime_div_le_T hT hnposNat
        (exitTimes_last_le M r ω)
      by_cases hiL : i = L
      · subst i
        have hKL' : K = L := le_antisymm hKL hiK
        have hnotmerge : ¬ (0 < L ∧ T - (τ L : ℝ) / n ≤ δ) := by
          intro hc
          have : L - 1 = L := by simpa [K, hc] using hKL'
          omega
        have hgap : δ < T - (τ L : ℝ) / n := by
          by_contra! hle
          exact hnotmerge ⟨by omega, hle⟩
        linarith
      · have hiLlt : i < L := lt_of_le_of_ne (hiK.trans hKL) hiL
        have hlt := strictMonoOn_exitTimes M r ω
          (show i ∈ Set.Iic L from hiLlt.le) (show L ∈ Set.Iic L from show L ≤ L from le_rfl) hiLlt
        have hltR : (τ i : ℝ) < τ L := by exact_mod_cast hlt
        exact ((div_lt_div_iff_of_pos_right hnpos).2 hltR).trans_le hlastT
  refine cadlagModulus_le_of_partition _ (by positivity) (endpointCuts T n τ K)
    (endpointCuts_zero T n τ K) (endpointCuts_last T n τ K) hmono ?_ ?_
  · intro i
    rw [endpointCuts_castSucc hτ0]
    by_cases hiK : i.val = K
    · rw [endpointCuts_succ_last hiK]
      rcases hKcases with hcase | hmerge
      · have hiL : i.val = L := by omega
        by_cases hL0 : L = 0
        · have hi0 : i.val = 0 := by omega
          rw [hi0, hτ0]
          simp only [Nat.cast_zero, zero_div, sub_zero]
          linarith
        · have hnotmerge : ¬ (0 < L ∧ T - (τ L : ℝ) / n ≤ δ) := by
            intro hc
            have : L - 1 = L := by simpa [K, hc] using hcase
            omega
          have hgap : δ < T - (τ L : ℝ) / n := by
            by_contra! hle
            exact hnotmerge ⟨Nat.pos_of_ne_zero hL0, hle⟩
          rw [hiL]
          exact hgap
      · have hiL : i.val + 1 = L := by omega
        have hlastT : (τ L : ℝ) / n ≤ T := exitTime_div_le_T hT hnposNat
          (exitTimes_last_le M r ω)
        by_cases hi0 : i.val = 0
        · simp [hi0, τ, exitTimes]
          linarith
        · have hgap := hgap i.val (by omega) (by omega)
          change 2 * δ < (τ (i.val + 1) : ℝ) / n - (τ i.val : ℝ) / n at hgap
          rw [hiL] at hgap
          linarith [hmerge.2.2]
    · rw [endpointCuts_succ_ne_last hiK]
      by_cases hi0 : i.val = 0
      · have hL0 : 0 < L := by omega
        have hactual : τ 1 ≤ M := exitTimes_le_of_lt_lastExit hL0
        have hgap := firstExit_gap hT hnposNat hb hinit hactual
        rw [hi0, hτ0]
        simp only [Nat.cast_zero, zero_div, sub_zero]
        change 2 * δ < (τ 1 : ℝ) / n at hgap
        linarith
      · have hgap := hgap i.val (by omega) (by omega)
        change 2 * δ < (τ (i.val + 1) : ℝ) / n - (τ i.val : ℝ) / n at hgap
        linarith
  · intro i s u hslo hsu hulo huu
    rw [endpointCuts_castSucc hτ0] at hslo hulo
    rw [realStepPath_apply_eq_stepValue, realStepPath_apply_eq_stepValue, Real.dist_eq]
    by_cases hiK : i.val = K
    · rw [endpointCuts_succ_last hiK] at hsu huu
      rcases hKcases with hcase | hmerge
      · have hiL : i.val = L := by omega
        rw [hiL] at hslo hulo
        have hsN : (s : ℝ) < (τ (L + 1) : ℝ) / n :=
          hsu.trans (T_lt_last_succ_div hnposNat)
        have huN : (u : ℝ) < (τ (L + 1) : ℝ) / n :=
          huu.trans (T_lt_last_succ_div hnposNat)
        exact (hosc L le_rfl s u hslo hsN hulo huN).trans (by linarith)
      · have hiL : i.val + 1 = L := by omega
        have hlastT : (τ L : ℝ) / n ≤ T := exitTime_div_le_T hT hnposNat
          (exitTimes_last_le M r ω)
        let q : Set.Icc (0 : ℝ) T := ⟨T - 2 * δ, by constructor <;> linarith⟩
        have hqhi : (q : ℝ) < (τ L : ℝ) / n := by
          dsimp [q]
          linarith [hmerge.2.2]
        have hqlo : (τ i.val : ℝ) / n ≤ q := by
          by_cases hi0 : i.val = 0
          · simp [hi0, τ, exitTimes, q]
            linarith
          · have hgap := hgap i.val (by omega) (by omega)
            change 2 * δ < (τ (i.val + 1) : ℝ) / n - (τ i.val : ℝ) / n at hgap
            rw [hiL] at hgap
            dsimp [q]
            linarith
        have hpoint (t : Set.Icc (0 : ℝ) T) (htlo : (τ i.val : ℝ) / n ≤ t)
            (htT : (t : ℝ) < T) :
            |stepValue n b ω t - stepValue n b ω q| ≤ 2 * ε := by
          by_cases ht : (t : ℝ) < (τ L : ℝ) / n
          · have ht' : (t : ℝ) < (τ (i.val + 1) : ℝ) / n := by rwa [hiL]
            have hqhi' : (q : ℝ) < (τ (i.val + 1) : ℝ) / n := by rwa [hiL]
            exact hosc i.val (by omega) t q htlo ht' hqlo hqhi'
          · have htq : T - 2 * δ ≤ t := by
              dsimp [q] at hqhi
              linarith
            exact (stepValue_sub_le_terminal hterm htq).trans (by linarith)
        calc
          |stepValue n b ω s - stepValue n b ω u| ≤
              |stepValue n b ω s - stepValue n b ω q| +
                |stepValue n b ω u - stepValue n b ω q| := by
            calc
              _ = |(stepValue n b ω s - stepValue n b ω q) -
                  (stepValue n b ω u - stepValue n b ω q)| := by congr 1; ring
              _ ≤ _ := abs_sub _ _
          _ ≤ 4 * ε := by linarith [hpoint s hslo hsu, hpoint u hulo huu]
    · rw [endpointCuts_succ_ne_last hiK] at hsu huu
      exact (hosc i.val (by omega) s u hslo hsu hulo huu).trans (by linarith)

end BGW.Skorokhod
