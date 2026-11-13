module

public import BGWLeaves.GeneralAFunctional.Walk
public import BGW.StableTrees.BridgeProjectiveClose
public import BGW.StableTrees.StableBridgeClosed
public import BGW.Skorokhod.Restrict
public import BGWLeaves.LeafLimits.BridgeTerminal
public import Mathlib.MeasureTheory.Integral.Indicator

/-!
# Terminal oscillation control of the A-marked bridge path (O_A)

`aBridge_terminal_oscillation` derives, from the prefix convergence (P_A) of the A-marked bridge path
`(W_{⌊T_n t⌋} / B_{T_n})_{0 ≤ t ≤ 1}` under `P[· | W_{T_n} = -1]` (`T_n` the `n`-th A-mark time), the
control of its oscillation on `[a, 1]` as `a ↑ 1`, in the form of the hypothesis `hosc` of BGW's
`Skorokhod.tendsto_of_tendsto_restrict_of_oscillation`.

Route (the A = {0} template is `BGWLeaves.LeafLimits.BridgeTerminal`).
* On `{T_n = m + 1, W_{T_n} = -1}` the walk satisfies `ω m = v ∈ A`, `W_m = -v`, `Λ_A(m) = n - 1`
  (`aBridge_succ_iff`). The final marked increment `v - 1` is random: no bound on it is needed.
* Deterministic bound (`exists_rev_of_jump`): with `x_a = ⌊(m+1)a⌋`, an oscillation larger than `η` on
  `[a, 1]` with `B_{m+1} ≥ 2/η` forces either `|W_{x_a}| ≥ η B_{m+1}/2` (the jump to the endpoint `-1`)
  or a reversed value `|Ŵ_i| = |W_m - W_{m-i}| > η B_{m+1}/2` with `i ≤ m - x_a`.
* Time reversal (`WalkReversal.timeReversal_map`, arbitrary signed endpoint `-v` and A-count `n - 1`) of
  the first `m` increments, conditionally on the last coordinate `ω m = v`, which is independent of them
  (`iidWalk_coord_inter`); summed over `(m, v)` (`iidWalk_aBridge_inter_le`): the reversed event becomes
  the start-escape event `{sup_{t ≤ δ} |X_t| ≥ η/2}` (`1 - a ≤ δ`), closed at the horizon `1/2`.
* The endpoint event `{|X_a| ≥ η/2}` is closed in `D([0,a])` (evaluation at the right endpoint is
  1-Lipschitz), so (P_A) at the horizon `a` bounds its `limsup` by `P(|X^br_a| ≥ η/2)`, which tends to
  `0` as `a ↑ 1` since `X^br_{1-} = 0` almost surely (`stableBridgeLaw_endpoints`).
-/

@[expose] public section

namespace BGWLeaves.GeneralAFunctional.WalkTerminal

open MeasureTheory ProbabilityTheory Filter BGW
open BGW.StableTrees BGW.LocallyFinite BGWLeaves.StableAnalysis BGWLeaves.GeneralAFunctional.Walk BGWLeaves.GeneralAFunctional.WalkVervaat
open scoped ENNReal NNReal Topology

/-! ## The last marked step of the A-stopped bridge -/

/-- Splitting the A-stopped bridge at its last (marked) step `ω m = v`: the first `m` increments sum to
`-v` and contain `n - 1` marks. -/
theorem aBridge_succ_iff {A : Set ℕ} {n m : ℕ} {ω : ℕ → ℕ} (hn : 1 ≤ n) :
    (WalkCyclic.IsAMarkTime A n ω (m + 1) ∧ walkSum ω (m + 1) = -1) ↔
      (ω m ∈ A ∧ ω ∈ WalkReversal.aReversalEvent A (-(ω m : ℤ)) m (n - 1)) := by
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  have hsum : walkSum ω (m + 1) = walkSum ω m + ((ω m : ℤ) - 1) := by
    unfold walkSum
    rw [Finset.sum_range_succ]
  rw [WalkStopped.last_mark_iff A n' ω m, Nat.add_sub_cancel, hsum]
  constructor
  · rintro ⟨⟨hc, hA⟩, hs⟩
    exact ⟨hA, by omega, hc⟩
  · rintro ⟨hA, hs, hc⟩
    exact ⟨⟨hc, hA⟩, by omega⟩

/-- On the A-stopped bridge (`n ≥ 1`) the clock is positive, so the bridge splits at its last step. -/
theorem exists_succ_of_mem_bridgeAtAMark {A : Set ℕ} {n : ℕ} (hn : 1 ≤ n) {ω : ℕ → ℕ}
    (hω : ω ∈ WalkCyclic.bridgeAtAMark A n) :
    ∃ m, ω m ∈ A ∧ ω ∈ WalkReversal.aReversalEvent A (-(ω m : ℤ)) m (n - 1) := by
  obtain ⟨k, hk, hs⟩ := hω
  rcases k with _ | m
  · exfalso
    have h := hk.1
    simp [WalkCyclic.walkACount] at h
    omega
  · exact ⟨m, (aBridge_succ_iff hn).1 ⟨hk, hs⟩⟩

/-- On `{T_n = m}`, the A-bridge path at time `t` is `W_{⌊m t⌋} / B_m`. -/
theorem aBridgeWalkPath_apply {A : Set ℕ} {B : ℕ → ℝ} {n m : ℕ} {ω : ℕ → ℕ}
    (hm : WalkCyclic.IsAMarkTime A n ω m) (t : Set.Icc (0 : ℝ) 1) :
    aBridgeWalkPath A B n ω t = (walkSum ω ⌊(m : ℝ) * t⌋₊ : ℝ) / B m := by
  have hle : ⌊(m : ℝ) * t⌋₊ ≤ m := by
    apply Nat.floor_le_of_le
    calc (m : ℝ) * t ≤ m * 1 := by gcongr; exact t.2.2
      _ = m := mul_one _
  rw [aBridgeWalkPath, aMarkTime_eq hm]
  change (((walkWord ω m).take ⌊((walkWord ω m).length : ℝ) * t⌋₊).sum : ℝ) / B m = _
  rw [LeafLimits.BridgeTerminal.length_walkWord, LeafLimits.BridgeTerminal.take_walkWord ω hle,
    sum_walkWord]

/-! ## Independence of the last coordinate and time reversal -/

/-- For an event depending on the first `m` coordinates only, `{ω m = v}` factorizes. -/
theorem iidWalk_coord_inter (μ : PMF ℕ) (m v : ℕ) {G : Set (ℕ → ℕ)}
    (hG : ∀ ω ω' : ℕ → ℕ, (∀ i < m, ω i = ω' i) → (ω ∈ G ↔ ω' ∈ G)) :
    iidWalk μ ({ω | ω m = v} ∩ G) = iidWalk μ G * iidWalk μ {ω | ω m = v} := by
  have hGe : G = LeafLimits.BridgeTerminal.pref m ⁻¹'
      {y | LeafLimits.BridgeTerminal.extendZ m y ∈ G} := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_ofPred_eq]
    exact hG _ _ (LeafLimits.BridgeTerminal.extendZ_pref_agree m ω)
  have hind := (LeafLimits.BridgeTerminal.indepFun_pref_coord μ m).measure_inter_preimage_eq_mul
    {y | LeafLimits.BridgeTerminal.extendZ m y ∈ G} {v} (Set.to_countable _).measurableSet
    (measurableSet_singleton v)
  calc iidWalk μ ({ω | ω m = v} ∩ G)
      = iidWalk μ (LeafLimits.BridgeTerminal.pref m ⁻¹'
            {y | LeafLimits.BridgeTerminal.extendZ m y ∈ G} ∩ (fun ω : ℕ → ℕ => ω m) ⁻¹' {v}) := by
        rw [Set.inter_comm, ← hGe]
        rfl
    _ = iidWalk μ (LeafLimits.BridgeTerminal.pref m ⁻¹'
            {y | LeafLimits.BridgeTerminal.extendZ m y ∈ G}) *
          iidWalk μ ((fun ω : ℕ → ℕ => ω m) ⁻¹' {v}) := hind
    _ = iidWalk μ G * iidWalk μ {ω | ω m = v} := by
        rw [← hGe]
        rfl

open Classical in
theorem walkACount_congr {A : Set ℕ} {ω ω' : ℕ → ℕ} {q : ℕ} (h : ∀ i < q, ω i = ω' i) :
    WalkCyclic.walkACount A ω q = WalkCyclic.walkACount A ω' q := by
  unfold WalkCyclic.walkACount
  congr 1
  exact Finset.filter_congr fun i hi => by rw [h i (Finset.mem_range.1 hi)]

open Classical in
theorem walkACount_le (A : Set ℕ) (ω : ℕ → ℕ) (m : ℕ) : WalkCyclic.walkACount A ω m ≤ m :=
  (Finset.card_filter_le _ _).trans (by simp)

theorem aReversalEvent_congr {A : Set ℕ} {s : ℤ} {m n' : ℕ} {ω ω' : ℕ → ℕ}
    (h : ∀ i < m, ω i = ω' i) :
    ω ∈ WalkReversal.aReversalEvent A s m n' ↔ ω' ∈ WalkReversal.aReversalEvent A s m n' := by
  simp only [WalkReversal.aReversalEvent, Set.mem_ofPred_eq,
    LeafLimits.BridgeTerminal.walkSum_congr h, walkACount_congr h]

/-- Time reversal (Proposition 6.8 with an arbitrary A-count and signed endpoint), unconditioned form. -/
theorem iidWalk_aTimeReversal (μ : PMF ℕ) (A : Set ℕ) (s : ℤ) (m n' : ℕ)
    (S : Set (Fin (m + 1) → ℤ)) :
    iidWalk μ (WalkReversal.aReversalEvent A s m n' ∩ walkPath m ⁻¹' S) =
      iidWalk μ (WalkReversal.aReversalEvent A s m n' ∩ reversedPath m ⁻¹' S) := by
  have hS : MeasurableSet S := (Set.to_countable S).measurableSet
  have hT := WalkReversal.measurableSet_aReversalEvent A s m n'
  have hmap := WalkReversal.timeReversal_map μ.toMeasure A s m n'
  have h1 := congrArg (fun ν : Measure (Fin (m + 1) → ℤ) => ν S) hmap
  simp only [Measure.map_apply (Vervaat.TimeReversal.measurable_walkPath m) hS,
    Measure.map_apply (Vervaat.TimeReversal.measurable_reversedPath m) hS] at h1
  rw [cond_apply hT, cond_apply hT] at h1
  by_cases h0 : iidWalk μ (WalkReversal.aReversalEvent A s m n') = 0
  · rw [measure_mono_null Set.inter_subset_left h0, measure_mono_null Set.inter_subset_left h0]
  · exact (ENNReal.mul_right_inj (ENNReal.inv_ne_zero.2 (measure_ne_top _ _))
      (ENNReal.inv_ne_top.2 h0)).1 h1

/-- **Reversal comparison for the A-stopped bridge.** If, on `{T_n = m + 1, W_{T_n} = -1}` (that is,
`ω m ∈ A`, `W_m = -ω m`, `Λ_A(m) = n - 1`), the event `X` forces the reversed path into `S m` and the
forward path in `S m` forces `X'`, then `P[W_{T_n} = -1, X] ≤ P[W_{T_n} = -1, X']`. The fibres are
indexed by the clock `m` and the random final mark `v = ω m`. -/
theorem iidWalk_aBridge_inter_le (μ : PMF ℕ) (A : Set ℕ) {n : ℕ} (hn : 1 ≤ n)
    (S : (m : ℕ) → Set (Fin (m + 1) → ℤ)) {X X' : Set (ℕ → ℕ)}
    (h1 : ∀ m ω, ω m ∈ A → ω ∈ WalkReversal.aReversalEvent A (-(ω m : ℤ)) m (n - 1) →
      ω ∈ X → reversedPath m ω ∈ S m)
    (h2 : ∀ m ω, ω m ∈ A → ω ∈ WalkReversal.aReversalEvent A (-(ω m : ℤ)) m (n - 1) →
      walkPath m ω ∈ S m → ω ∈ X') :
    iidWalk μ (WalkCyclic.bridgeAtAMark A n ∩ X) ≤
      iidWalk μ (WalkCyclic.bridgeAtAMark A n ∩ X') := by
  let R : ℕ × ℕ → Set (ℕ → ℕ) := fun p =>
    {ω | ω p.1 = p.2} ∩ ({_ω | p.2 ∈ A} ∩
      (WalkReversal.aReversalEvent A (-(p.2 : ℤ)) p.1 (n - 1) ∩ reversedPath p.1 ⁻¹' S p.1))
  let W : ℕ × ℕ → Set (ℕ → ℕ) := fun p =>
    {ω | ω p.1 = p.2} ∩ ({_ω | p.2 ∈ A} ∩
      (WalkReversal.aReversalEvent A (-(p.2 : ℤ)) p.1 (n - 1) ∩ walkPath p.1 ⁻¹' S p.1))
  have hRW : ∀ p, iidWalk μ (R p) = iidWalk μ (W p) := by
    rintro ⟨m, v⟩
    have hrev : ∀ ω ω' : ℕ → ℕ, (∀ i < m, ω i = ω' i) →
        (ω ∈ {_ω : ℕ → ℕ | v ∈ A} ∩ (WalkReversal.aReversalEvent A (-(v : ℤ)) m (n - 1) ∩
            reversedPath m ⁻¹' S m) ↔
          ω' ∈ {_ω : ℕ → ℕ | v ∈ A} ∩ (WalkReversal.aReversalEvent A (-(v : ℤ)) m (n - 1) ∩
            reversedPath m ⁻¹' S m)) := by
      intro ω ω' h
      simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_ofPred_eq, aReversalEvent_congr h,
        LeafLimits.BridgeTerminal.reversedPath_congr h]
    have hwalk : ∀ ω ω' : ℕ → ℕ, (∀ i < m, ω i = ω' i) →
        (ω ∈ {_ω : ℕ → ℕ | v ∈ A} ∩ (WalkReversal.aReversalEvent A (-(v : ℤ)) m (n - 1) ∩
            walkPath m ⁻¹' S m) ↔
          ω' ∈ {_ω : ℕ → ℕ | v ∈ A} ∩ (WalkReversal.aReversalEvent A (-(v : ℤ)) m (n - 1) ∩
            walkPath m ⁻¹' S m)) := by
      intro ω ω' h
      simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_ofPred_eq, aReversalEvent_congr h,
        LeafLimits.BridgeTerminal.walkPath_congr h]
    dsimp only [R, W]
    rw [iidWalk_coord_inter μ m v hrev, iidWalk_coord_inter μ m v hwalk]
    congr 1
    by_cases hv : v ∈ A
    · simp only [hv, Set.ofPred_true, Set.univ_inter]
      exact (iidWalk_aTimeReversal μ A (-(v : ℤ)) m (n - 1) (S m)).symm
    · simp only [hv, Set.ofPred_false, Set.empty_inter]
  have hsubR : WalkCyclic.bridgeAtAMark A n ∩ X ⊆ ⋃ p, R p := by
    rintro ω ⟨hb, hX⟩
    obtain ⟨m, hA, hT⟩ := exists_succ_of_mem_bridgeAtAMark hn hb
    exact Set.mem_iUnion.2 ⟨(m, ω m), rfl, hA, hT, h1 m ω hA hT hX⟩
  have hsubW : (⋃ p, W p) ⊆ WalkCyclic.bridgeAtAMark A n ∩ X' := by
    intro ω hω
    obtain ⟨⟨m, v⟩, hv, hA, hT, hW⟩ := Set.mem_iUnion.1 hω
    change ω m = v at hv
    subst hv
    exact ⟨⟨m + 1, (aBridge_succ_iff hn).2 ⟨hA, hT⟩⟩, h2 m ω hA hT hW⟩
  have hWmeas : ∀ p, MeasurableSet (W p) := fun p => by
    dsimp only [W]
    exact ((measurable_pi_apply p.1) (measurableSet_singleton p.2)).inter
      ((MeasurableSet.const _).inter
        ((WalkReversal.measurableSet_aReversalEvent A _ p.1 (n - 1)).inter
          ((Vervaat.TimeReversal.measurable_walkPath p.1) (Set.to_countable _).measurableSet)))
  have hWdisj : Pairwise (Function.onFun Disjoint W) := by
    rintro ⟨m, v⟩ ⟨m', v'⟩ hne
    rw [Function.onFun, Set.disjoint_left]
    rintro ω ⟨hv, hA, hT, -⟩ ⟨hv', hA', hT', -⟩
    change ω m = v at hv
    change ω m' = v' at hv'
    subst hv hv'
    have e := WalkCyclic.IsAMarkTime.unique ((aBridge_succ_iff hn).2 ⟨hA, hT⟩).1
      ((aBridge_succ_iff hn).2 ⟨hA', hT'⟩).1
    have hmm : m = m' := by omega
    subst hmm
    exact hne rfl
  calc iidWalk μ (WalkCyclic.bridgeAtAMark A n ∩ X) ≤ iidWalk μ (⋃ p, R p) := measure_mono hsubR
    _ ≤ ∑' p, iidWalk μ (R p) := measure_iUnion_le _
    _ = ∑' p, iidWalk μ (W p) := tsum_congr hRW
    _ = iidWalk μ (⋃ p, W p) := (measure_iUnion hWdisj hWmeas).symm
    _ ≤ iidWalk μ (WalkCyclic.bridgeAtAMark A n ∩ X') := measure_mono hsubW

/-! ## The deterministic oscillation bound -/

/-- An increment `|W_{xs} - W_{xa}| > c ≥ 2` between `xa ≤ xs ≤ m + 1` of a walk with `W_{m+1} = -1`
and `|W_{xa}| < c/2` produces a reversed value `|W_m - W_{m-i}| > c/2` with `i ≤ m - xa`. -/
theorem exists_rev_of_jump {W : ℕ → ℤ} {m xa xs : ℕ} {c : ℝ} (hW1 : W (m + 1) = -1)
    (hxa : xa ≤ m) (hxs : xa ≤ xs) (hxs1 : xs ≤ m + 1) (hc : 2 ≤ c)
    (hsmall : |(W xa : ℝ)| < c / 2) (hbig : c < |(W xs : ℝ) - W xa|) :
    ∃ i, i + xa ≤ m ∧ c / 2 < |(W m : ℝ) - W (m - i)| := by
  rcases Nat.lt_or_ge m xs with h | h
  · exfalso
    have hxs' : xs = m + 1 := by omega
    rw [hxs', hW1] at hbig
    have h1 := abs_sub (((-1 : ℤ)) : ℝ) (W xa)
    have h2 : |(((-1 : ℤ)) : ℝ)| = 1 := by norm_num
    linarith
  · have htri := abs_sub ((W m : ℝ) - W xa) ((W m : ℝ) - W xs)
    have e : (W m : ℝ) - W xa - ((W m : ℝ) - W xs) = (W xs : ℝ) - W xa := by ring
    rw [e] at htri
    by_cases hu : c / 2 < |(W m : ℝ) - W xa|
    · exact ⟨m - xa, by omega, by rwa [Nat.sub_sub_self hxa]⟩
    · refine ⟨m - xs, by omega, ?_⟩
      rw [Nat.sub_sub_self h]
      linarith [not_lt.mp hu]

/-- On `{T_n = m + 1, W_{T_n} = -1}` with `η B_{m+1} ≥ 2`, an oscillation larger than `η` on `[a, 1]`
together with `|X_a| < η/2` produces a reversed value `|W_m - W_{m-i}| > η B_{m+1}/2`,
`i ≤ m - ⌊(m+1)a⌋`. -/
theorem exists_rev_of_osc {A : Set ℕ} {B : ℕ → ℝ} {n m : ℕ} {ω : ℕ → ℕ} {a η : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a < 1) (hBpos : 0 < B (m + 1)) (hηB : 2 ≤ η * B (m + 1))
    (hmark : WalkCyclic.IsAMarkTime A n ω (m + 1)) (hs : walkSum ω (m + 1) = -1)
    (hosc : η < ⨆ s : {s : Set.Icc (0 : ℝ) 1 // a ≤ (s : ℝ)},
      dist (aBridgeWalkPath A B n ω s) (aBridgeWalkPath A B n ω ⟨a, ha0, ha1.le⟩))
    (hsmall : |aBridgeWalkPath A B n ω ⟨a, ha0, ha1.le⟩| < η / 2) :
    ∃ i : ℕ, i + ⌊((m + 1 : ℕ) : ℝ) * a⌋₊ ≤ m ∧
      η * B (m + 1) / 2 < |(walkSum ω m : ℝ) - walkSum ω (m - i)| := by
  have : Nonempty {s : Set.Icc (0 : ℝ) 1 // a ≤ (s : ℝ)} := ⟨⟨⟨a, ha0, ha1.le⟩, le_rfl⟩⟩
  obtain ⟨s, hηs⟩ := exists_lt_of_lt_ciSup hosc
  rw [aBridgeWalkPath_apply hmark, aBridgeWalkPath_apply hmark, Real.dist_eq, ← sub_div,
    abs_div, abs_of_pos hBpos, lt_div_iff₀ hBpos] at hηs
  rw [aBridgeWalkPath_apply hmark, abs_div, abs_of_pos hBpos, div_lt_iff₀ hBpos] at hsmall
  have hm1 : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by positivity
  have hxa : ⌊((m + 1 : ℕ) : ℝ) * a⌋₊ ≤ m := by
    have : ⌊((m + 1 : ℕ) : ℝ) * a⌋₊ < m + 1 := by
      rw [Nat.floor_lt (by positivity)]
      calc ((m + 1 : ℕ) : ℝ) * a < ((m + 1 : ℕ) : ℝ) * 1 := by gcongr
        _ = ((m + 1 : ℕ) : ℝ) := mul_one _
    omega
  have hxs : ⌊((m + 1 : ℕ) : ℝ) * a⌋₊ ≤ ⌊((m + 1 : ℕ) : ℝ) * ((s : Set.Icc (0 : ℝ) 1) : ℝ)⌋₊ :=
    Nat.floor_le_floor (mul_le_mul_of_nonneg_left s.2 hm1.le)
  have hxs1 : ⌊((m + 1 : ℕ) : ℝ) * ((s : Set.Icc (0 : ℝ) 1) : ℝ)⌋₊ ≤ m + 1 := by
    apply Nat.floor_le_of_le
    calc ((m + 1 : ℕ) : ℝ) * ((s : Set.Icc (0 : ℝ) 1) : ℝ) ≤ ((m + 1 : ℕ) : ℝ) * 1 := by
          gcongr; exact (s : Set.Icc (0 : ℝ) 1).2.2
      _ = ((m + 1 : ℕ) : ℝ) := mul_one _
  exact exists_rev_of_jump hs hxa hxs hxs1 hηB (lt_of_lt_of_eq hsmall (by ring)) hηs

/-- On `{T_n = m + 1}`, a forward value `|W_i| > η B_{m+1}/2` with `i ≤ m - ⌊(m+1)b⌋` and
`1 - b ≤ δ < 1/2` puts the restriction of the path to `[0, 1/2]` in `{sup_{t ≤ δ} |x(t)| ≥ η/2}`. -/
theorem mem_startEscape_of_fwd {A : Set ℕ} {B : ℕ → ℝ} {n m : ℕ} {ω : ℕ → ℕ}
    (hmark : WalkCyclic.IsAMarkTime A n ω (m + 1)) (hBpos : 0 < B (m + 1))
    {b η δ : ℝ} (hδ : δ < 1 / 2) (hbδ : 1 - b ≤ δ) (hr : (1 / 2 : ℝ) ≤ 1) {i : ℕ}
    (hi : i + ⌊((m + 1 : ℕ) : ℝ) * b⌋₊ ≤ m)
    (hηi : η * B (m + 1) / 2 < |(walkSum ω i : ℝ)|) :
    Skorokhod.restrict hr (aBridgeWalkPath A B n ω) ∈
      LeafLimits.BridgeTerminal.startEscape (1 / 2) δ (η / 2) := by
  have hm1 : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by positivity
  have hxa := Nat.lt_floor_add_one (((m + 1 : ℕ) : ℝ) * b)
  have hi' : ((i : ℕ) : ℝ) + (⌊((m + 1 : ℕ) : ℝ) * b⌋₊ : ℝ) ≤ (m : ℝ) := by exact_mod_cast hi
  have ht1 : ((i : ℕ) : ℝ) / ((m + 1 : ℕ) : ℝ) < 1 - b := by
    rw [div_lt_iff₀ hm1]
    push_cast at hxa hi' ⊢
    linarith
  have ht0 : 0 ≤ ((i : ℕ) : ℝ) / ((m + 1 : ℕ) : ℝ) := by positivity
  have htδ : ((i : ℕ) : ℝ) / ((m + 1 : ℕ) : ℝ) ≤ δ := by linarith
  rintro ⟨c', hc', hall⟩
  have h := hall ⟨((i : ℕ) : ℝ) / ((m + 1 : ℕ) : ℝ), ht0, by linarith⟩ htδ
  change |aBridgeWalkPath A B n ω ⟨((i : ℕ) : ℝ) / ((m + 1 : ℕ) : ℝ), ht0, by linarith⟩| ≤ c' at h
  rw [aBridgeWalkPath_apply hmark] at h
  have hfl : ⌊((m + 1 : ℕ) : ℝ) * (((i : ℕ) : ℝ) / ((m + 1 : ℕ) : ℝ))⌋₊ = (i : ℕ) := by
    rw [mul_div_cancel₀ _ hm1.ne', Nat.floor_natCast]
  simp only [hfl] at h
  rw [abs_div, abs_of_pos hBpos, div_le_iff₀ hBpos] at h
  have := mul_lt_mul_of_pos_right hc' hBpos
  linarith

/-! ## The endpoint event -/

/-- Paths on `[0, r]` whose terminal value has absolute value at least `c`. -/
def endEscape {r : ℝ} (hr : 0 ≤ r) (c : ℝ) : Set (Skorokhod.D r ℝ) :=
  {y | c ≤ |y ⟨r, hr, le_rfl⟩|}

/-- Closed in the J1 topology: evaluation at the right endpoint is 1-Lipschitz. -/
theorem isClosed_endEscape {r : ℝ} (hr : 0 ≤ r) (c : ℝ) : IsClosed (endEscape hr c) :=
  isClosed_le continuous_const
    (continuous_abs.comp (Skorokhod.lipschitzWith_one_eval_right hr).continuous)

theorem stableBridge_endEscape_eq {θ r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (c : ℝ) :
    (((stableBridgeLaw θ).map (Skorokhod.restrict hr1) : ProbabilityMeasure _) :
        Measure (Skorokhod.D r ℝ)) (endEscape hr0 c) =
      (stableBridgeLaw θ : Measure (Skorokhod.D 1 ℝ)) {f | c ≤ |f ⟨r, hr0, hr1⟩|} := by
  rw [ProbabilityMeasure.toMeasure_map, Measure.map_apply
    (Skorokhod.measurable_restrict_of_nonneg hr0 hr1) (isClosed_endEscape hr0 c).measurableSet]
  rfl

/-- `P(|X^br_{a_j}| ≥ c) → 0` as `a_j ↑ 1`, since `X^br_{1-} = 0` almost surely. -/
theorem tendsto_stableBridge_endEscape {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {a : ℕ → ℝ}
    (ha0 : ∀ j, 0 ≤ a j) (ha1 : ∀ j, a j < 1) (hlim : Tendsto a atTop (𝓝 1)) {c : ℝ}
    (hc : 0 < c) :
    Tendsto (fun j => (stableBridgeLaw θ : Measure (Skorokhod.D 1 ℝ))
      {f | c ≤ |f ⟨a j, ha0 j, (ha1 j).le⟩|}) atTop (𝓝 0) := by
  have hmeas : ∀ j, MeasurableSet {f : Skorokhod.D 1 ℝ | c ≤ |f ⟨a j, ha0 j, (ha1 j).le⟩|} :=
    fun j => (Skorokhod.measurable_eval _)
      (isClosed_le continuous_const continuous_abs).measurableSet
  have h := tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure atTop
    (μ := (stableBridgeLaw θ : Measure (Skorokhod.D 1 ℝ))) MeasurableSet.empty hmeas ?_
  · simpa only [measure_empty] using h
  filter_upwards [stableBridgeLaw_endpoints hθ] with f hf
  have hl := (Skorokhod.isCadlag f).tendsto_nhdsLT_leftLim
    (⟨1, zero_le_one, le_rfl⟩ : Set.Icc (0 : ℝ) 1)
  rw [hf.2.2] at hl
  have hseq : Tendsto (fun j => (⟨a j, ha0 j, (ha1 j).le⟩ : Set.Icc (0 : ℝ) 1)) atTop
      (𝓝[<] (⟨1, zero_le_one, le_rfl⟩ : Set.Icc (0 : ℝ) 1)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨tendsto_subtype_rng.2 hlim, Eventually.of_forall fun j => ?_⟩
    exact Set.mem_Iio.2 (Subtype.coe_lt_coe.1 (ha1 j))
  filter_upwards [(hl.comp hseq).eventually (Metric.ball_mem_nhds 0 hc)] with j hj
  simp only [Function.comp_apply, Real.dist_eq, sub_zero] at hj
  simp only [Set.mem_empty_iff_false, iff_false, not_le]
  exact hj

/-! ## The comparison under the conditional law -/

/-- **Key comparison.** For `n ≥ 1` admissible with `B_T ≥ 2/η` for every `T ≥ n`, and
`1 - b ≤ δ < 1/2`, the probability under the A-marked bridge of an oscillation larger than `η` on
`[b, 1]` is at most the probability that the restriction to `[0, 1/2]` lies in
`{sup_{t ≤ δ} |x(t)| ≥ η/2}` plus the probability that `|X_b| ≥ η/2`. -/
theorem aBridgeLaw_osc_le {μ : PMF ℕ} {A : Set ℕ} {B : ℕ → ℝ} {n : ℕ} (hn : 1 ≤ n)
    (hadm : ZetaAAdmissible μ A n) {η : ℝ} (hη : 0 < η) (hBn : ∀ T, n ≤ T → 2 / η ≤ B T)
    {b : ℝ} (hb0 : 0 ≤ b) (hb1 : b < 1) {δ : ℝ} (hδ : δ < 1 / 2)
    (hbδ : 1 - b ≤ δ) (hr : (1 / 2 : ℝ) ≤ 1) :
    (aBridgeLaw μ A n : Measure (ℕ → ℕ))
        {ω | η < ⨆ s : {s : Set.Icc (0 : ℝ) 1 // b ≤ (s : ℝ)},
          dist (aBridgeWalkPath A B n ω s) (aBridgeWalkPath A B n ω ⟨b, hb0, hb1.le⟩)} ≤
      (aBridgeLaw μ A n : Measure (ℕ → ℕ))
          ((Skorokhod.restrict hr ∘ aBridgeWalkPath A B n) ⁻¹'
            LeafLimits.BridgeTerminal.startEscape (1 / 2) δ (η / 2)) +
        (aBridgeLaw μ A n : Measure (ℕ → ℕ))
          ((Skorokhod.restrict hb1.le ∘ aBridgeWalkPath A B n) ⁻¹' endEscape hb0 (η / 2)) := by
  set O : Set (ℕ → ℕ) := {ω | η < ⨆ s : {s : Set.Icc (0 : ℝ) 1 // b ≤ (s : ℝ)},
    dist (aBridgeWalkPath A B n ω s) (aBridgeWalkPath A B n ω ⟨b, hb0, hb1.le⟩)} with hO
  set E : Set (ℕ → ℕ) :=
    (Skorokhod.restrict hb1.le ∘ aBridgeWalkPath A B n) ⁻¹' endEscape hb0 (η / 2) with hE
  have hsplit : O ⊆ (O ∩ Eᶜ) ∪ E := fun ω hω => by
    by_cases h : ω ∈ E
    · exact Or.inr h
    · exact Or.inl ⟨hω, h⟩
  refine (measure_mono hsplit).trans ((measure_union_le _ _).trans (add_le_add_left ?_ _))
  rw [coe_aBridgeLaw hn hadm, cond_apply (WalkCyclic.measurableSet_bridgeAtAMark A n),
    cond_apply (WalkCyclic.measurableSet_bridgeAtAMark A n)]
  refine mul_le_mul_of_nonneg_left ?_ zero_le
  have h2η : 0 < 2 / η := by positivity
  have hBclock : ∀ (m : ℕ) (ω : ℕ → ℕ),
      ω ∈ WalkReversal.aReversalEvent A (-(ω m : ℤ)) m (n - 1) → 2 / η ≤ B (m + 1) := by
    intro m ω hT
    apply hBn
    have h := hT.2
    have hle := walkACount_le A ω m
    omega
  apply iidWalk_aBridge_inter_le μ A hn (fun m => {p : Fin (m + 1) → ℤ | ∃ i : Fin (m + 1),
      (i : ℕ) + ⌊((m + 1 : ℕ) : ℝ) * b⌋₊ ≤ m ∧ η * B (m + 1) / 2 < |((p i : ℤ) : ℝ)|})
  · rintro m ω hA hT ⟨hosc, hE'⟩
    have hmark := (aBridge_succ_iff hn).2 ⟨hA, hT⟩
    have hB2 := hBclock m ω hT
    have hBpos : 0 < B (m + 1) := h2η.trans_le hB2
    have hηB : 2 ≤ η * B (m + 1) := by
      rw [div_le_iff₀ hη] at hB2
      linarith
    have hE'' : ¬ (η / 2 ≤ |aBridgeWalkPath A B n ω ⟨b, hb0, hb1.le⟩|) := hE'
    obtain ⟨i, hi, hηi⟩ :=
      exists_rev_of_osc hb0 hb1 hBpos hηB hmark.1 hmark.2 hosc (lt_of_not_ge hE'')
    refine ⟨⟨i, by omega⟩, hi, ?_⟩
    simp only [reversedPath, Int.cast_sub]
    exact hηi
  · rintro m ω hA hT ⟨i, hi, hηi⟩
    have hmark := (aBridge_succ_iff hn).2 ⟨hA, hT⟩
    have hBpos : 0 < B (m + 1) := h2η.trans_le (hBclock m ω hT)
    exact mem_startEscape_of_fwd hmark.1 hBpos hδ hbδ hr hi hηi

/-! ## The terminal oscillation control -/

-- `hA`, `hc`, `hne`, `hap`, `hAfin` (and the binder `ha0` inside `hpre`) belong to the uniform
-- interface of the A-marked bridge principle and are not needed for (O_A).
set_option linter.unusedVariables false in
/-- (O_A) terminal oscillation control of the A-marked bridge path (the `hosc` hypothesis of BGW's
`Skorokhod.tendsto_of_tendsto_restrict_of_oscillation`, `T = 1`), from the prefix convergence (P_A), by the
reversal of the preterminal increments conditionally on the final marked increment.  No bound on the final
increment is needed: the jump to the endpoint is controlled by the endpoint event `{|X_a| ≥ η/2}` (see the
module header). -/
theorem aBridge_terminal_oscillation {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ} {A : Set ℕ} (hA : A.Nonempty)
    (hc : IsCritical μ) (hne : μ 1 ≠ 1) (hap : Aperiodic μ)
    (hB : IsRealStableAttracted (realOffspringStepLaw μ) θ B)
    (hAfin : ¬ Integrable (fun z : ℤ => (z : ℝ) ^ 2) (stepLaw μ) → A.Finite ∨ Aᶜ.Finite)
    {q : ℕ → ℕ} (hqtop : Tendsto q atTop atTop) (hq : ∀ k, ZetaAAdmissible μ A (q k))
    (hpre : ∀ (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1),
      Tendsto (fun k => (aBridgeLaw μ A (q k)).map
          (Skorokhod.restrict ha1.le ∘ aBridgeWalkPath A B (q k)))
        atTop (𝓝 ((stableBridgeLaw θ).map (Skorokhod.restrict ha1.le))))
    {a : ℕ → ℝ} (ha0 : ∀ j, 0 ≤ a j) (ha1 : ∀ j, a j < 1) (hlim : Tendsto a atTop (𝓝 1)) :
    ∀ η > 0, Tendsto (fun j => limsup (fun k => ((aBridgeLaw μ A (q k) : Measure (ℕ → ℕ))).real
        {ω | η < ⨆ s : {s : Set.Icc (0 : ℝ) 1 // a j ≤ (s : ℝ)},
          dist (aBridgeWalkPath A B (q k) ω s)
            (aBridgeWalkPath A B (q k) ω ⟨a j, ha0 j, (ha1 j).le⟩)}) atTop)
      atTop (𝓝 0) := by
  intro η hη
  have hc2 : 0 < η / 2 := by positivity
  have h12 : (1 / 2 : ℝ) < 1 := by norm_num
  have hhalf := hpre (1 / 2) (by norm_num) h12
  obtain ⟨NB, hNB⟩ := eventually_atTop.1
    (hB.tendsto_norming_atTop.eventually_ge_atTop (2 / η))
  have hK : ∀ᶠ k in atTop, max NB 1 ≤ q k := hqtop.eventually_ge_atTop (max NB 1)
  have hL0 : ∀ j, 0 ≤ limsup (fun k => ((aBridgeLaw μ A (q k) : Measure (ℕ → ℕ))).real
      {ω | η < ⨆ s : {s : Set.Icc (0 : ℝ) 1 // a j ≤ (s : ℝ)},
        dist (aBridgeWalkPath A B (q k) ω s)
          (aBridgeWalkPath A B (q k) ω ⟨a j, ha0 j, (ha1 j).le⟩)}) atTop := fun j =>
    le_limsup_of_frequently_le (Filter.Frequently.of_forall fun k => measureReal_nonneg)
      (isBoundedUnder_of ⟨1, fun k => measureReal_le_one⟩)
  have hend := tendsto_stableBridge_endEscape hB.index_mem ha0 ha1 hlim hc2
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hε4 : 0 < ε / 4 := by positivity
  obtain ⟨δ, hδ0, hδ12, hνδ⟩ :=
    LeafLimits.BridgeTerminal.exists_small_startEscape hB.index_mem h12.le hc2 hε4
  have hport := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hhalf
    (LeafLimits.BridgeTerminal.isClosed_startEscape (c := η / 2) hδ0.le hδ12)
  have hev := eventually_lt_of_limsup_lt (hport.trans_lt hνδ)
  obtain ⟨J, hJ⟩ := eventually_atTop.1
    (hlim.eventually (Ioi_mem_nhds (show 1 - δ < 1 by linarith)))
  obtain ⟨J', hJ'⟩ := eventually_atTop.1
    (hend.eventually (gt_mem_nhds (ENNReal.ofReal_pos.2 hε4)))
  refine ⟨max J J', fun j hj => ?_⟩
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (hL0 j)]
  refine lt_of_le_of_lt ?_ (half_lt_self hε)
  have hportj := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto
    (hpre (a j) (ha0 j) (ha1 j)) (isClosed_endEscape (ha0 j) (η / 2))
  rw [stableBridge_endEscape_eq (ha0 j) (ha1 j).le] at hportj
  have hevj := eventually_lt_of_limsup_lt (hportj.trans_lt (hJ' j (le_of_max_le_right hj)))
  have haj : 1 - a j ≤ δ := by
    have : 1 - δ < a j := hJ j (le_of_max_le_left hj)
    linarith
  apply limsup_le_of_le (Filter.isCoboundedUnder_le_of_le atTop fun k => measureReal_nonneg)
  filter_upwards [hev, hevj, hK] with k hk1 hk1' hk2
  have hn : 1 ≤ q k := le_of_max_le_right hk2
  have hBn : ∀ T, q k ≤ T → 2 / η ≤ B T := fun T hT =>
    hNB T ((le_of_max_le_left hk2).trans hT)
  apply ENNReal.toReal_le_of_le_ofReal (half_pos hε).le
  calc (aBridgeLaw μ A (q k) : Measure (ℕ → ℕ))
        {ω | η < ⨆ s : {s : Set.Icc (0 : ℝ) 1 // a j ≤ (s : ℝ)},
          dist (aBridgeWalkPath A B (q k) ω s)
            (aBridgeWalkPath A B (q k) ω ⟨a j, ha0 j, (ha1 j).le⟩)}
      ≤ (aBridgeLaw μ A (q k) : Measure (ℕ → ℕ))
            ((Skorokhod.restrict h12.le ∘ aBridgeWalkPath A B (q k)) ⁻¹'
              LeafLimits.BridgeTerminal.startEscape (1 / 2) δ (η / 2)) +
          (aBridgeLaw μ A (q k) : Measure (ℕ → ℕ))
            ((Skorokhod.restrict (ha1 j).le ∘ aBridgeWalkPath A B (q k)) ⁻¹'
              endEscape (ha0 j) (η / 2)) :=
        aBridgeLaw_osc_le hn (hq k) hη hBn (ha0 j) (ha1 j) hδ12 haj h12.le
    _ ≤ (((aBridgeLaw μ A (q k)).map (Skorokhod.restrict h12.le ∘ aBridgeWalkPath A B (q k)) :
            ProbabilityMeasure _) : Measure (Skorokhod.D (1 / 2) ℝ))
            (LeafLimits.BridgeTerminal.startEscape (1 / 2) δ (η / 2)) +
          (((aBridgeLaw μ A (q k)).map
              (Skorokhod.restrict (ha1 j).le ∘ aBridgeWalkPath A B (q k)) :
            ProbabilityMeasure _) : Measure (Skorokhod.D (a j) ℝ)) (endEscape (ha0 j) (η / 2)) :=
        add_le_add
          (Measure.le_map_apply ((Skorokhod.measurable_restrict_of_nonneg (by norm_num)
            h12.le).comp (measurable_aBridgeWalkPath A B (q k))).aemeasurable _)
          (Measure.le_map_apply ((Skorokhod.measurable_restrict_of_nonneg (ha0 j)
            (ha1 j).le).comp (measurable_aBridgeWalkPath A B (q k))).aemeasurable _)
    _ ≤ ENNReal.ofReal (ε / 4) + ENNReal.ofReal (ε / 4) := add_le_add hk1.le hk1'.le
    _ = ENNReal.ofReal (ε / 4 + ε / 4) := (ENNReal.ofReal_add hε4.le hε4.le).symm
    _ ≤ ENNReal.ofReal (ε / 2) := ENNReal.ofReal_le_ofReal (by linarith)

end BGWLeaves.GeneralAFunctional.WalkTerminal
