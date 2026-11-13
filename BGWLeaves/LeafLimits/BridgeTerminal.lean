module

public import BGWLeaves.LeafLimits.Defs
public import BGWLeaves.Coding.Defs
public import BGW.StableTrees.BridgeProjectiveClose
public import BGW.StableTrees.StableBridgeClosed
public import BGW.StableTrees.RealAttractionBounds
public import BGW.Skorokhod.Restrict
public import BGW.Skorokhod.Prefix
public import Mathlib.Probability.Independence.InfinitePi
public import Mathlib.MeasureTheory.Measure.Portmanteau

/-!
# M13: terminal oscillation control of the bridge path (part (O) of the bridge principle)

Source: arXiv:1110.2163v4, proof of Theorem 6.1, lines 2279-2312 (`eq:montrertension`).

`bridge_terminal_oscillation` derives, from the prefix convergence (P) of the bridge path
`(W_{⌊T_n t⌋} / B_{T_n})_{0 ≤ t ≤ 1}` under `P[· | W_{T_n} = -1]`, the control of its oscillation on
`[a, 1]` as `a ↑ 1`, in the form of the hypothesis `hosc` of BGW's
`Skorokhod.tendsto_of_tendsto_restrict_of_oscillation`.

Route.
* On `{T_n = m + 1, W_{T_n} = -1}` the walk satisfies `ω m = 0`, `W_m = 0`, `Λ(m) = n - 1`
  (`bridgeAtMark_succ_iff`); the final step `-1` is handled separately (it contributes `1/B_{m+1}`).
* Deterministic bound: the oscillation of the path on `[a, 1]` exceeds `η` only if some reversed value
  `Ŵ_i = W_m - W_{m-i}`, `i ≤ m - ⌊(m+1)a⌋`, satisfies `η < (2|Ŵ_i| + 1)/B_{m+1}`.
* Time reversal (Proposition 6.8, `timeReversal_map`) on `{W_m = 0, Λ(m) = n-1}`, the last coordinate
  `ω m` being independent of the first `m` (`iidWalk_coord_inter`), summed over `m`
  (`iidWalk_bridge_inter_le`): the same event for the forward values `W_i`, `i < (m+1)(1-a)`.
* For `B_{T_n} ≥ 2/η` this is contained in `{sup_{t ≤ δ} |X(t)| ≥ η/4}` (`1 - a ≤ δ`), a closed condition on
  the restriction to `[0, 1/2]` (`isClosed_startEscape`), so the portmanteau theorem and (P) at the horizon
  `1/2` bound the `limsup` by the stable-bridge probability, which tends to `0` as `δ → 0` since
  `X^br_0 = 0` and the paths are right-continuous at `0` (`exists_small_startEscape`).
-/

@[expose] public section

namespace BGWLeaves.LeafLimits.BridgeTerminal

open MeasureTheory ProbabilityTheory Filter BGW
open BGW.StableTrees BGW.LocallyFinite BGWLeaves.StableAnalysis
open scoped ENNReal NNReal Topology

/-! ## Mark times and the last step -/

/-- A witness of the first mark time determines the extended-valued clock. -/
theorem walkLeafTime_eq_of_isMarkTime {n m : ℕ} {ω : ℕ → ℕ} (hm : IsMarkTime n ω m) :
    walkLeafTime ω n = (m : ℕ∞) := by
  unfold walkLeafTime
  apply le_antisymm
  · exact iInf₂_le m hm.1
  · refine le_iInf₂ fun q hq => ?_
    have hmq : m ≤ q := by
      by_contra h
      have := hm.2 q (not_le.mp h)
      omega
    exact_mod_cast hmq

/-- The natural-valued clock agrees with any witness of the first mark time. -/
theorem markTime_eq_of_isMarkTime {n m : ℕ} {ω : ℕ → ℕ} (hm : IsMarkTime n ω m) :
    markTime n ω = m := by
  simp [markTime, walkLeafTime_eq_of_isMarkTime hm]

/-- Splitting a stopped bridge at its last step yields the fixed-length time-reversal event. -/
theorem bridgeAtMark_succ_iff {n m : ℕ} {ω : ℕ → ℕ} (hn : 1 ≤ n) :
    (IsMarkTime n ω (m + 1) ∧ walkSum ω (m + 1) = -1) ↔
      (ω m = 0 ∧ ω ∈ timeReversalEvent m (n - 1)) := by
  have hcount : walkLeafCount ω (m + 1) =
      walkLeafCount ω m + if ω m = 0 then 1 else 0 := by
    unfold walkLeafCount
    rw [Finset.card_filter, Finset.card_filter, Finset.sum_range_succ]
    by_cases h : ω m = 0 <;> simp [h]
  have hsum : walkSum ω (m + 1) = walkSum ω m + ((ω m : ℤ) - 1) := by
    unfold walkSum
    rw [Finset.sum_range_succ]
  constructor
  · rintro ⟨hm, hs⟩
    have hmark := hm.1
    have hlt := hm.2 m (Nat.lt_succ_self m)
    have hzero : ω m = 0 := by
      by_contra h
      simp only [h, ↓reduceIte, add_zero] at hcount
      omega
    refine ⟨hzero, ?_, ?_⟩
    · rw [hzero] at hsum
      omega
    · simp only [hzero, ↓reduceIte] at hcount
      omega
  · rintro ⟨hzero, hs, hc⟩
    simp only [hzero, ↓reduceIte] at hcount
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · omega
    · intro q hq
      have hle : walkLeafCount ω q ≤ walkLeafCount ω m := by
        unfold walkLeafCount
        exact Finset.card_le_card (Finset.filter_subset_filter _
          (Finset.range_mono (by omega)))
      omega
    · rw [hsum, hs, hzero]
      simp

/-- On the stopped bridge (`n ≥ 1`) the clock is positive, so the bridge splits at its last step. -/
theorem exists_succ_of_mem_bridgeAtMark {n : ℕ} (hn : 1 ≤ n) {ω : ℕ → ℕ}
    (hω : ω ∈ bridgeAtMark n) : ∃ m, ω m = 0 ∧ ω ∈ timeReversalEvent m (n - 1) := by
  obtain ⟨k, hk, hs⟩ := hω
  rcases k with _ | m
  · exfalso
    have h := hk.1
    simp [walkLeafCount] at h
    omega
  · exact ⟨m, (bridgeAtMark_succ_iff hn).1 ⟨hk, hs⟩⟩

/-! ## The bridge path as a function of the partial sums -/

theorem take_walkWord (ω : ℕ → ℕ) {i k : ℕ} (h : i ≤ k) :
    (walkWord ω k).take i = walkWord ω i := by
  unfold walkWord
  rw [← List.map_take, List.take_range, min_eq_left h]

theorem length_walkWord (ω : ℕ → ℕ) (k : ℕ) : (walkWord ω k).length = k := by
  simp [walkWord]

/-- On `{T_n = m}`, the bridge path at time `t` is `W_{⌊m t⌋} / B_m`. -/
theorem bridgeWalkPath_apply {B : ℕ → ℝ} {n m : ℕ} {ω : ℕ → ℕ} (hm : IsMarkTime n ω m)
    (t : Set.Icc (0 : ℝ) 1) :
    bridgeWalkPath B n ω t = (walkSum ω ⌊(m : ℝ) * t⌋₊ : ℝ) / B m := by
  have hle : ⌊(m : ℝ) * t⌋₊ ≤ m := by
    apply Nat.floor_le_of_le
    calc (m : ℝ) * t ≤ m * 1 := by gcongr; exact t.2.2
      _ = m := mul_one _
  rw [bridgeWalkPath, markTime_eq_of_isMarkTime hm]
  change (((walkWord ω m).take ⌊((walkWord ω m).length : ℝ) * t⌋₊).sum : ℝ) / B m = _
  rw [length_walkWord, take_walkWord ω hle, sum_walkWord]

/-! ## Independence of the last coordinate and time reversal -/

/-- The first `m` coordinates. -/
def pref (m : ℕ) (ω : ℕ → ℕ) : Fin m → ℕ := fun i => ω i

/-- Extension by zero of a finite word. -/
def extendZ (m : ℕ) (x : Fin m → ℕ) : ℕ → ℕ := fun i => if h : i < m then x ⟨i, h⟩ else 0

theorem measurable_pref (m : ℕ) : Measurable (pref m) :=
  measurable_pi_iff.2 fun _ => measurable_pi_apply _

theorem extendZ_pref_agree (m : ℕ) (ω : ℕ → ℕ) : ∀ i < m, ω i = extendZ m (pref m ω) i := by
  intro i hi
  simp [extendZ, pref, hi]

/-- Under the iid walk, the first `m` coordinates are independent of the coordinate `m`. -/
theorem indepFun_pref_coord (μ : PMF ℕ) (m : ℕ) :
    IndepFun (pref m) (fun ω : ℕ → ℕ => ω m) (iidWalk μ) := by
  have hI : iIndepFun (fun (i : ℕ) (ω : ℕ → ℕ) => ω i) (iidWalk μ) :=
    iIndepFun_infinitePi (P := fun _ : ℕ => μ.toMeasure) (X := fun _ x => x)
      (fun _ => measurable_id)
  have h := hI.indepFun_set (Set.Iio m) {m}
    (Set.disjoint_left.2 fun x hx hx' => by
      simp only [Set.mem_Iio, Set.mem_singleton_iff] at hx hx'
      omega)
    (fun i => measurable_pi_apply i)
  exact h.comp (φ := fun (s : Set.Iio m → ℕ) (i : Fin m) => s ⟨i, i.2⟩)
    (ψ := fun (s : ({m} : Set ℕ) → ℕ) => s ⟨m, Set.mem_singleton m⟩)
    (measurable_pi_iff.2 fun _ => measurable_pi_apply _) (measurable_pi_apply _)

/-- For an event depending on the first `m` coordinates only, `{ω m = 0}` factorizes. -/
theorem iidWalk_coord_inter (μ : PMF ℕ) (m : ℕ) {G : Set (ℕ → ℕ)}
    (hG : ∀ ω ω' : ℕ → ℕ, (∀ i < m, ω i = ω' i) → (ω ∈ G ↔ ω' ∈ G)) :
    iidWalk μ ({ω | ω m = 0} ∩ G) = iidWalk μ G * iidWalk μ {ω | ω m = 0} := by
  have hGe : G = pref m ⁻¹' {y | extendZ m y ∈ G} := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_ofPred_eq]
    exact hG _ _ (extendZ_pref_agree m ω)
  have hind := (indepFun_pref_coord μ m).measure_inter_preimage_eq_mul
    {y | extendZ m y ∈ G} {0} (Set.to_countable _).measurableSet (measurableSet_singleton 0)
  calc iidWalk μ ({ω | ω m = 0} ∩ G)
      = iidWalk μ (pref m ⁻¹' {y | extendZ m y ∈ G} ∩ (fun ω : ℕ → ℕ => ω m) ⁻¹' {0}) := by
        rw [Set.inter_comm, ← hGe]
        rfl
    _ = iidWalk μ (pref m ⁻¹' {y | extendZ m y ∈ G}) *
          iidWalk μ ((fun ω : ℕ → ℕ => ω m) ⁻¹' {0}) := hind
    _ = iidWalk μ G * iidWalk μ {ω | ω m = 0} := by
        rw [← hGe]
        rfl

theorem walkSum_congr {ω ω' : ℕ → ℕ} {q : ℕ} (h : ∀ i < q, ω i = ω' i) :
    walkSum ω q = walkSum ω' q := by
  unfold walkSum
  exact Finset.sum_congr rfl fun i hi => by rw [h i (Finset.mem_range.1 hi)]

theorem walkLeafCount_congr {ω ω' : ℕ → ℕ} {q : ℕ} (h : ∀ i < q, ω i = ω' i) :
    walkLeafCount ω q = walkLeafCount ω' q := by
  unfold walkLeafCount
  congr 1
  exact Finset.filter_congr fun i hi => by rw [h i (Finset.mem_range.1 hi)]

theorem timeReversalEvent_congr {m n' : ℕ} {ω ω' : ℕ → ℕ} (h : ∀ i < m, ω i = ω' i) :
    ω ∈ timeReversalEvent m n' ↔ ω' ∈ timeReversalEvent m n' := by
  simp only [timeReversalEvent, Set.mem_ofPred_eq, walkSum_congr h, walkLeafCount_congr h]

theorem walkPath_congr {m : ℕ} {ω ω' : ℕ → ℕ} (h : ∀ i < m, ω i = ω' i) :
    walkPath m ω = walkPath m ω' := by
  funext i
  exact walkSum_congr fun j hj => h j (by omega)

theorem reversedPath_congr {m : ℕ} {ω ω' : ℕ → ℕ} (h : ∀ i < m, ω i = ω' i) :
    reversedPath m ω = reversedPath m ω' := by
  funext i
  simp only [reversedPath]
  rw [walkSum_congr h, walkSum_congr fun j hj => h j (by omega)]

/-- Proposition 6.8 for events of the path (no conditioning). -/
theorem iidWalk_timeReversal (μ : PMF ℕ) (m n' : ℕ) (S : Set (Fin (m + 1) → ℤ)) :
    iidWalk μ (timeReversalEvent m n' ∩ walkPath m ⁻¹' S) =
      iidWalk μ (timeReversalEvent m n' ∩ reversedPath m ⁻¹' S) := by
  have hS : MeasurableSet S := (Set.to_countable S).measurableSet
  have hT := measurableSet_timeReversalEvent m n'
  have hmap := BGWLeaves.timeReversal_map μ.toMeasure m n'
  have h1 := congrArg (fun ν : Measure (Fin (m + 1) → ℤ) => ν S) hmap
  simp only [Measure.map_apply (measurable_walkPath m) hS,
    Measure.map_apply (measurable_reversedPath m) hS] at h1
  rw [cond_apply hT, cond_apply hT] at h1
  by_cases h0 : iidWalk μ (timeReversalEvent m n') = 0
  · rw [measure_mono_null Set.inter_subset_left h0, measure_mono_null Set.inter_subset_left h0]
  · exact (ENNReal.mul_right_inj (ENNReal.inv_ne_zero.2 (measure_ne_top _ _))
      (ENNReal.inv_ne_top.2 h0)).1 h1

/-- The reversal on the event `{ω m = 0, W_m = 0, Λ(m) = n'}` of the last step of a bridge. -/
theorem iidWalk_reversal_piece (μ : PMF ℕ) (m n' : ℕ) (S : Set (Fin (m + 1) → ℤ)) :
    iidWalk μ ({ω | ω m = 0} ∩ (timeReversalEvent m n' ∩ reversedPath m ⁻¹' S)) =
      iidWalk μ ({ω | ω m = 0} ∩ (timeReversalEvent m n' ∩ walkPath m ⁻¹' S)) := by
  have hrev : ∀ ω ω' : ℕ → ℕ, (∀ i < m, ω i = ω' i) →
      (ω ∈ timeReversalEvent m n' ∩ reversedPath m ⁻¹' S ↔
        ω' ∈ timeReversalEvent m n' ∩ reversedPath m ⁻¹' S) := by
    intro ω ω' h
    simp only [Set.mem_inter_iff, Set.mem_preimage, timeReversalEvent_congr h,
      reversedPath_congr h]
  have hwalk : ∀ ω ω' : ℕ → ℕ, (∀ i < m, ω i = ω' i) →
      (ω ∈ timeReversalEvent m n' ∩ walkPath m ⁻¹' S ↔
        ω' ∈ timeReversalEvent m n' ∩ walkPath m ⁻¹' S) := by
    intro ω ω' h
    simp only [Set.mem_inter_iff, Set.mem_preimage, timeReversalEvent_congr h, walkPath_congr h]
  rw [iidWalk_coord_inter μ m hrev, iidWalk_coord_inter μ m hwalk, iidWalk_timeReversal]

/-- **Reversal comparison.** If, on `{ω m = 0, W_m = 0, Λ(m) = n - 1}` (that is, on
`{T_n = m + 1, W_{T_n} = -1}`), the event `A` forces the reversed path into `S m` and the forward path in
`S m` forces `A'`, then `P[W_{T_n} = -1, A] ≤ P[W_{T_n} = -1, A']`. -/
theorem iidWalk_bridge_inter_le (μ : PMF ℕ) {n : ℕ} (hn : 1 ≤ n)
    (S : (m : ℕ) → Set (Fin (m + 1) → ℤ)) {A A' : Set (ℕ → ℕ)}
    (h1 : ∀ m ω, ω m = 0 → ω ∈ timeReversalEvent m (n - 1) → ω ∈ A → reversedPath m ω ∈ S m)
    (h2 : ∀ m ω, ω m = 0 → ω ∈ timeReversalEvent m (n - 1) → walkPath m ω ∈ S m → ω ∈ A') :
    iidWalk μ (bridgeAtMark n ∩ A) ≤ iidWalk μ (bridgeAtMark n ∩ A') := by
  let R : ℕ → Set (ℕ → ℕ) := fun m =>
    {ω | ω m = 0} ∩ (timeReversalEvent m (n - 1) ∩ reversedPath m ⁻¹' S m)
  let W : ℕ → Set (ℕ → ℕ) := fun m =>
    {ω | ω m = 0} ∩ (timeReversalEvent m (n - 1) ∩ walkPath m ⁻¹' S m)
  have hRW : ∀ m, iidWalk μ (R m) = iidWalk μ (W m) := fun m =>
    iidWalk_reversal_piece μ m (n - 1) (S m)
  have hsubR : bridgeAtMark n ∩ A ⊆ ⋃ m, R m := by
    rintro ω ⟨hb, hA⟩
    obtain ⟨m, h0, hT⟩ := exists_succ_of_mem_bridgeAtMark hn hb
    exact Set.mem_iUnion.2 ⟨m, h0, hT, h1 m ω h0 hT hA⟩
  have hsubW : (⋃ m, W m) ⊆ bridgeAtMark n ∩ A' := by
    intro ω hω
    obtain ⟨m, h0, hT, hW⟩ := Set.mem_iUnion.1 hω
    exact ⟨⟨m + 1, (bridgeAtMark_succ_iff hn).2 ⟨h0, hT⟩⟩, h2 m ω h0 hT hW⟩
  have hWmeas : ∀ m, MeasurableSet (W m) := fun m =>
    ((measurable_pi_apply m) (measurableSet_singleton 0)).inter
      ((measurableSet_timeReversalEvent m (n - 1)).inter
        ((measurable_walkPath m) (Set.to_countable _).measurableSet))
  have hWdisj : Pairwise (Function.onFun Disjoint W) := by
    intro m m' hmm'
    rw [Function.onFun, Set.disjoint_left]
    rintro ω ⟨h0, hT, -⟩ ⟨h0', hT', -⟩
    have e := IsMarkTime.unique ((bridgeAtMark_succ_iff hn).2 ⟨h0, hT⟩).1
      ((bridgeAtMark_succ_iff hn).2 ⟨h0', hT'⟩).1
    exact hmm' (by omega)
  calc iidWalk μ (bridgeAtMark n ∩ A) ≤ iidWalk μ (⋃ m, R m) := measure_mono hsubR
    _ ≤ ∑' m, iidWalk μ (R m) := measure_iUnion_le _
    _ = ∑' m, iidWalk μ (W m) := tsum_congr hRW
    _ = iidWalk μ (⋃ m, W m) := (measure_iUnion hWdisj hWmeas).symm
    _ ≤ iidWalk μ (bridgeAtMark n ∩ A') := measure_mono hsubW

/-! ## The deterministic oscillation bound -/

/-- The increment between two indices `xa ≤ xs ≤ m + 1` of a walk with `W_{m+1} = -1` is bounded by
`2 |W_{m-i}| + 1` for some `i ≤ m - xa`. -/
theorem exists_abs_sub_le {W : ℕ → ℤ} {m xa xs : ℕ} (hW1 : W (m + 1) = -1) (hxa : xa ≤ m)
    (hxs : xa ≤ xs) (hxs1 : xs ≤ m + 1) :
    ∃ i, i + xa ≤ m ∧ |(W xs : ℝ) - W xa| ≤ 2 * |(W (m - i) : ℝ)| + 1 := by
  have htri := abs_sub (W xs : ℝ) (W xa)
  by_cases h : xs = m + 1
  · refine ⟨m - xa, by omega, ?_⟩
    rw [show m - (m - xa) = xa by omega]
    rw [h, hW1] at htri
    have : |(((-1 : ℤ)) : ℝ)| = 1 := by simp
    rw [h, hW1]
    linarith [abs_nonneg (W xa : ℝ)]
  · by_cases hc : |(W xs : ℝ)| ≤ |(W xa : ℝ)|
    · refine ⟨m - xa, by omega, ?_⟩
      rw [show m - (m - xa) = xa by omega]
      linarith
    · refine ⟨m - xs, by omega, ?_⟩
      rw [show m - (m - xs) = xs by omega]
      push Not at hc
      linarith

/-- On `{T_n = m + 1, W_{T_n} = -1}`, an oscillation larger than `η` on `[a, 1]` produces a reversed value
`Ŵ_i = W_m - W_{m - i} = -W_{m-i}`, `i ≤ m - ⌊(m+1)a⌋`, with `η < (2|Ŵ_i| + 1)/B_{m+1}`. -/
theorem exists_rev_of_osc {B : ℕ → ℝ} {n m : ℕ} {ω : ℕ → ℕ} (hn : 1 ≤ n) {a η : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a < 1) (hBpos : 0 < B (m + 1)) (h0 : ω m = 0)
    (hT : ω ∈ timeReversalEvent m (n - 1))
    (hA : η < ⨆ s : {s : Set.Icc (0 : ℝ) 1 // a ≤ (s : ℝ)},
      dist (bridgeWalkPath B n ω s) (bridgeWalkPath B n ω ⟨a, ha0, ha1.le⟩)) :
    ∃ i : ℕ, i + ⌊((m + 1 : ℕ) : ℝ) * a⌋₊ ≤ m ∧
      η < (2 * |(walkSum ω (m - i) : ℝ)| + 1) / B (m + 1) := by
  have hmark := (bridgeAtMark_succ_iff hn).2 ⟨h0, hT⟩
  have : Nonempty {s : Set.Icc (0 : ℝ) 1 // a ≤ (s : ℝ)} := ⟨⟨⟨a, ha0, ha1.le⟩, le_rfl⟩⟩
  obtain ⟨⟨s, hs⟩, hηs⟩ := exists_lt_of_lt_ciSup hA
  rw [bridgeWalkPath_apply hmark.1, bridgeWalkPath_apply hmark.1] at hηs
  have hm1 : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by positivity
  have hxa : ⌊((m + 1 : ℕ) : ℝ) * a⌋₊ ≤ m := by
    have : ⌊((m + 1 : ℕ) : ℝ) * a⌋₊ < m + 1 := by
      rw [Nat.floor_lt (by positivity)]
      calc ((m + 1 : ℕ) : ℝ) * a < ((m + 1 : ℕ) : ℝ) * 1 := by gcongr
        _ = ((m + 1 : ℕ) : ℝ) := mul_one _
    omega
  have hxs : ⌊((m + 1 : ℕ) : ℝ) * a⌋₊ ≤ ⌊((m + 1 : ℕ) : ℝ) * s⌋₊ :=
    Nat.floor_le_floor (by gcongr)
  have hxs1 : ⌊((m + 1 : ℕ) : ℝ) * s⌋₊ ≤ m + 1 := by
    apply Nat.floor_le_of_le
    calc ((m + 1 : ℕ) : ℝ) * s ≤ ((m + 1 : ℕ) : ℝ) * 1 := by gcongr; exact s.2.2
      _ = ((m + 1 : ℕ) : ℝ) := mul_one _
  obtain ⟨i, hi, hle⟩ := exists_abs_sub_le (W := walkSum ω) hmark.2 hxa hxs hxs1
  refine ⟨i, hi, ?_⟩
  calc η < dist ((walkSum ω ⌊((m + 1 : ℕ) : ℝ) * s⌋₊ : ℝ) / B (m + 1))
        ((walkSum ω ⌊((m + 1 : ℕ) : ℝ) * a⌋₊ : ℝ) / B (m + 1)) := hηs
    _ = |(walkSum ω ⌊((m + 1 : ℕ) : ℝ) * s⌋₊ : ℝ) - walkSum ω ⌊((m + 1 : ℕ) : ℝ) * a⌋₊| /
          B (m + 1) := by
        rw [Real.dist_eq, ← sub_div, abs_div, abs_of_pos hBpos]
    _ ≤ (2 * |(walkSum ω (m - i) : ℝ)| + 1) / B (m + 1) := by gcongr

/-! ## The closed set `{sup_{t ≤ δ} |x(t)| ≥ c}` of paths on `[0, r]` -/

/-- Paths whose absolute value stays below some `c' < c` on `[0, δ]`. -/
def smallStart (r δ c : ℝ) : Set (Skorokhod.D r ℝ) :=
  {y | ∃ c' < c, ∀ t : Set.Icc (0 : ℝ) r, (t : ℝ) ≤ δ → |y t| ≤ c'}

/-- Its complement, `{sup_{t ≤ δ} |x(t)| ≥ c}`. -/
def startEscape (r δ c : ℝ) : Set (Skorokhod.D r ℝ) := (smallStart r δ c)ᶜ

/-- `smallStart` is open in the J1 topology (right continuity at `δ < r`). -/
theorem isOpen_smallStart {r δ c : ℝ} (hδ0 : 0 ≤ δ) (hδ : δ < r) :
    IsOpen (smallStart r δ c) := by
  rw [Metric.isOpen_iff]
  rintro y ⟨c', hc', hy⟩
  set c'' := (c' + c) / 2 with hc''
  have hrc := (Skorokhod.isCadlag y).isRightContinuous ⟨δ, hδ0, hδ.le⟩
  rw [Metric.continuousWithinAt_iff] at hrc
  obtain ⟨ρ, hρ, hρy⟩ := hrc (c'' - c') (by linarith)
  have hbound : ∀ t : Set.Icc (0 : ℝ) r, (t : ℝ) < δ + ρ → |y t| ≤ c'' := by
    intro t ht
    by_cases htδ : (t : ℝ) ≤ δ
    · linarith [hy t htδ]
    · have h1 : t ∈ Set.Ioi (⟨δ, hδ0, hδ.le⟩ : Set.Icc (0 : ℝ) r) := by
        show (⟨δ, hδ0, hδ.le⟩ : Set.Icc (0 : ℝ) r) < t
        exact Subtype.mk_lt_mk.mpr (lt_of_not_ge htδ)
      have h2 : dist t (⟨δ, hδ0, hδ.le⟩ : Set.Icc (0 : ℝ) r) < ρ := by
        rw [Subtype.dist_eq, Real.dist_eq, abs_lt]
        constructor <;> simp only <;> linarith
      have h3 := hρy h1 h2
      rw [Real.dist_eq] at h3
      have h4 := hy ⟨δ, hδ0, hδ.le⟩ le_rfl
      linarith [abs_sub_abs_le_abs_sub (y t) (y ⟨δ, hδ0, hδ.le⟩)]
  refine ⟨min ρ ((c - c'') / 2), lt_min hρ (by linarith), ?_⟩
  intro z hz
  rw [Metric.mem_ball, Skorokhod.dist_eq_j1Dist, Skorokhod.j1Dist] at hz
  have : Nonempty (Skorokhod.TimeChange r) := ⟨OrderIso.refl _⟩
  obtain ⟨σ, hσ⟩ := exists_lt_of_ciInf_lt hz
  rw [max_lt_iff] at hσ
  refine ⟨c'' + (c - c'') / 2, by linarith, ?_⟩
  intro t ht
  have hr : 0 ≤ r := hδ0.trans hδ.le
  have hb1 : BddAbove (Set.range fun t : Set.Icc (0 : ℝ) r => |((σ t : ℝ)) - t|) :=
    ⟨r, by rintro _ ⟨t, rfl⟩; exact Skorokhod.TimeChange.abs_sub_le σ hr t⟩
  have h1 : |((σ t : ℝ)) - t| < min ρ ((c - c'') / 2) :=
    lt_of_le_of_lt (le_ciSup hb1 t) hσ.1
  have h2 : dist (z t) (y (σ t)) < min ρ ((c - c'') / 2) :=
    lt_of_le_of_lt (le_ciSup (Skorokhod.bddAbove_range_dist z y σ) t) hσ.2
  have hmin1 := min_le_left ρ ((c - c'') / 2)
  have hmin2 := min_le_right ρ ((c - c'') / 2)
  have h3 : |y (σ t)| ≤ c'' := by
    apply hbound
    have := (abs_lt.1 h1).2
    linarith
  rw [Real.dist_eq] at h2
  linarith [abs_sub_abs_le_abs_sub (z t) (y (σ t))]

theorem isClosed_startEscape {r δ c : ℝ} (hδ0 : 0 ≤ δ) (hδ : δ < r) :
    IsClosed (startEscape r δ c) :=
  (isOpen_smallStart hδ0 hδ).isClosed_compl

theorem startEscape_mono {r δ δ' c : ℝ} (h : δ ≤ δ') :
    startEscape r δ c ⊆ startEscape r δ' c := by
  intro y hy hy'
  apply hy
  obtain ⟨c', hc', hall⟩ := hy'
  exact ⟨c', hc', fun t ht => hall t (ht.trans h)⟩

/-- A path vanishing at `0` stays small on a short initial interval (right continuity at `0`). -/
theorem exists_mem_smallStart {r : ℝ} (hr : 0 ≤ r) {y : Skorokhod.D r ℝ}
    (hy : y ⟨0, le_rfl, hr⟩ = 0) {c : ℝ} (hc : 0 < c) :
    ∃ N : ℕ, y ∈ smallStart r (1 / ((N : ℝ) + 4)) c := by
  have hrc := (Skorokhod.isCadlag y).isRightContinuous ⟨0, le_rfl, hr⟩
  rw [Metric.continuousWithinAt_iff] at hrc
  obtain ⟨ρ, hρ, hρy⟩ := hrc (c / 2) (by linarith)
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt hρ
  refine ⟨N, c / 2, by linarith, fun t ht => ?_⟩
  have hNle : 1 / ((N : ℝ) + 4) ≤ 1 / ((N : ℝ) + 1) := by
    apply one_div_le_one_div_of_le (by positivity)
    linarith
  by_cases ht0 : (t : ℝ) = 0
  · have : t = ⟨0, le_rfl, hr⟩ := Subtype.ext ht0
    rw [this, hy]
    simp only [abs_zero]
    linarith
  · have h1 : t ∈ Set.Ioi (⟨0, le_rfl, hr⟩ : Set.Icc (0 : ℝ) r) := by
      show (⟨0, le_rfl, hr⟩ : Set.Icc (0 : ℝ) r) < t
      exact Subtype.mk_lt_mk.mpr (lt_of_le_of_ne t.2.1 (Ne.symm ht0))
    have h2 : dist t (⟨0, le_rfl, hr⟩ : Set.Icc (0 : ℝ) r) < ρ := by
      rw [Subtype.dist_eq, Real.dist_eq]
      simp only [sub_zero]
      rw [abs_of_nonneg t.2.1]
      linarith
    have h3 := hρy h1 h2
    rw [Real.dist_eq, hy, sub_zero] at h3
    exact h3.le

/-- Under the stable bridge restricted to `[0, 1/2]`, `P(sup_{t ≤ δ} |X_t| ≥ c)` is small for small `δ`
(`X^br_0 = 0`, BGW `stableBridgeLaw_endpoints`). -/
theorem exists_small_startEscape {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (hr : (1 / 2 : ℝ) ≤ 1) {c : ℝ}
    (hc : 0 < c) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ, 0 < δ ∧ δ < 1 / 2 ∧
      (((stableBridgeLaw θ).map (Skorokhod.restrict hr) : ProbabilityMeasure _) :
        Measure (Skorokhod.D (1 / 2) ℝ)) (startEscape (1 / 2) δ c) < ENNReal.ofReal ε := by
  let δs : ℕ → ℝ := fun N => 1 / ((N : ℝ) + 4)
  have hδpos : ∀ N, 0 < δs N := fun N => by positivity
  have hδlt : ∀ N, δs N < 1 / 2 := fun N => by
    show 1 / ((N : ℝ) + 4) < 1 / 2
    apply one_div_lt_one_div_of_lt (by norm_num)
    have : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    linarith
  have hanti : Antitone fun N => startEscape (1 / 2) (δs N) c := by
    intro N N' h
    apply startEscape_mono
    show 1 / ((N' : ℝ) + 4) ≤ 1 / ((N : ℝ) + 4)
    apply one_div_le_one_div_of_le (by positivity)
    have : (N : ℝ) ≤ N' := Nat.cast_le.2 h
    linarith
  have hclosed : ∀ N, IsClosed (startEscape (1 / 2) (δs N) c) := fun N =>
    isClosed_startEscape (hδpos N).le (hδlt N)
  set ν : Measure (Skorokhod.D (1 / 2) ℝ) :=
    (((stableBridgeLaw θ).map (Skorokhod.restrict hr) : ProbabilityMeasure _) :
      Measure (Skorokhod.D (1 / 2) ℝ)) with hν
  have hlim := tendsto_measure_iInter_atTop (μ := ν)
    (fun N => (hclosed N).measurableSet.nullMeasurableSet) hanti ⟨0, measure_ne_top _ _⟩
  have hzero : ν (⋂ N, startEscape (1 / 2) (δs N) c) = 0 := by
    rw [hν, ProbabilityMeasure.toMeasure_map,
      Measure.map_apply (Skorokhod.measurable_restrict_of_nonneg (by norm_num) hr)
        (MeasurableSet.iInter fun N => (hclosed N).measurableSet)]
    apply measure_mono_null _ (ae_iff.1 (stableBridgeLaw_endpoints hθ))
    intro f hf hcontra
    obtain ⟨N, hN⟩ := exists_mem_smallStart (r := 1 / 2) (by norm_num)
      (y := Skorokhod.restrict hr f) hcontra.1 hc
    exact Set.mem_iInter.1 hf N hN
  rw [hzero] at hlim
  obtain ⟨N, hN⟩ := (hlim.eventually (gt_mem_nhds (ENNReal.ofReal_pos.2 hε))).exists
  exact ⟨δs N, hδpos N, hδlt N, hN⟩

/-! ## The comparison under the conditional law -/

/-- **Key comparison.** For `n ≥ 1` admissible with `B_T ≥ 2/η` for every `T ≥ n`, and `1 - b ≤ δ < 1/2`,
the probability under `P[· | W_{T_n} = -1]` of an oscillation larger than `η` on `[b, 1]` is at most the
probability that the restriction to `[0, 1/2]` lies in `{sup_{t ≤ δ} |x(t)| ≥ η/4}`. -/
theorem bridgeWalkLaw_osc_le {μ : PMF ℕ} {B : ℕ → ℝ} {n : ℕ} (hn : 1 ≤ n)
    (hadm : LeafAdmissible μ n) {η : ℝ} (hη : 0 < η) (hBn : ∀ T, n ≤ T → 2 / η ≤ B T)
    {b : ℝ} (hb0 : 0 ≤ b) (hb1 : b < 1) {δ : ℝ} (hδ : δ < 1 / 2)
    (hbδ : 1 - b ≤ δ) (hr : (1 / 2 : ℝ) ≤ 1) :
    (bridgeWalkLaw μ n : Measure (ℕ → ℕ))
        {ω | η < ⨆ s : {s : Set.Icc (0 : ℝ) 1 // b ≤ (s : ℝ)},
          dist (bridgeWalkPath B n ω s) (bridgeWalkPath B n ω ⟨b, hb0, hb1.le⟩)} ≤
      (bridgeWalkLaw μ n : Measure (ℕ → ℕ))
        ((Skorokhod.restrict hr ∘ bridgeWalkPath B n) ⁻¹' startEscape (1 / 2) δ (η / 4)) := by
  rw [coe_bridgeWalkLaw ((iidWalk_bridgeAtMark_ne_zero_iff μ hn).2 hadm),
    cond_apply (measurableSet_bridgeAtMark n), cond_apply (measurableSet_bridgeAtMark n)]
  refine mul_le_mul_of_nonneg_left ?_ zero_le
  have h2η : 0 < 2 / η := by positivity
  -- the bound on the norming at the clock `m + 1 ≥ n`
  have hBclock : ∀ (m : ℕ) (ω : ℕ → ℕ), ω m = 0 → ω ∈ timeReversalEvent m (n - 1) →
      2 / η ≤ B (m + 1) := by
    intro m ω h0 hT
    apply hBn
    have h := hT.2
    have hle : walkLeafCount ω m ≤ m := by
      unfold walkLeafCount
      exact (Finset.card_filter_le _ _).trans (by simp)
    omega
  apply iidWalk_bridge_inter_le μ hn (fun m => {p : Fin (m + 1) → ℤ | ∃ i : Fin (m + 1),
      (i : ℕ) + ⌊((m + 1 : ℕ) : ℝ) * b⌋₊ ≤ m ∧ η < (2 * |((p i : ℤ) : ℝ)| + 1) / B (m + 1)})
  · intro m ω h0 hT hA
    have hBpos : 0 < B (m + 1) := h2η.trans_le (hBclock m ω h0 hT)
    obtain ⟨i, hi, hηi⟩ := exists_rev_of_osc hn hb0 hb1 hBpos h0 hT hA
    refine ⟨⟨i, by omega⟩, hi, ?_⟩
    have hWm : walkSum ω m = 0 := hT.1
    simp only [reversedPath, hWm, zero_sub, Int.cast_neg, abs_neg]
    exact hηi
  · rintro m ω h0 hT ⟨i, hi, hηi⟩
    have hmark := (bridgeAtMark_succ_iff hn).2 ⟨h0, hT⟩
    have hB2 := hBclock m ω h0 hT
    have hBpos : 0 < B (m + 1) := h2η.trans_le hB2
    have hm1 : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by positivity
    -- the time `t = i / (m + 1) < 1 - b ≤ δ`
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
    change |bridgeWalkPath B n ω ⟨((i : ℕ) : ℝ) / ((m + 1 : ℕ) : ℝ), ht0, by linarith⟩| ≤ c' at h
    rw [bridgeWalkPath_apply hmark.1] at h
    have hfl : ⌊((m + 1 : ℕ) : ℝ) * (((i : ℕ) : ℝ) / ((m + 1 : ℕ) : ℝ))⌋₊ = (i : ℕ) := by
      rw [mul_div_cancel₀ _ hm1.ne', Nat.floor_natCast]
    simp only [hfl] at h
    have hwp : (walkPath m ω i : ℤ) = walkSum ω (i : ℕ) := rfl
    rw [hwp] at hηi
    rw [abs_div, abs_of_pos hBpos, div_le_iff₀ hBpos] at h
    have hηB : 2 ≤ η * B (m + 1) := by
      rw [div_le_iff₀ hη] at hB2
      linarith
    have h3 : η * B (m + 1) < 2 * |(walkSum ω (i : ℕ) : ℝ)| + 1 := by
      rwa [lt_div_iff₀ hBpos] at hηi
    nlinarith

/-! ## The terminal oscillation control -/

/-- **General form of (O).** Only the attraction `hB` (for `1 < θ ≤ 2` and `B → ∞`), the admissible
`q k → ∞` and the prefix convergence at the single horizon `1/2` are used. -/
theorem bridge_terminal_oscillation_of_half {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ}
    (hB : IsRealStableAttracted (realOffspringStepLaw μ) θ B) {q : ℕ → ℕ}
    (hqtop : Tendsto q atTop atTop) (hq : ∀ k, LeafAdmissible μ (q k))
    (hr : (1 / 2 : ℝ) ≤ 1)
    (hpre : Tendsto (fun k => (bridgeWalkLaw μ (q k)).map
          (Skorokhod.restrict hr ∘ bridgeWalkPath B (q k)))
        atTop (𝓝 ((stableBridgeLaw θ).map (Skorokhod.restrict hr))))
    {a : ℕ → ℝ} (ha0 : ∀ j, 0 ≤ a j) (ha1 : ∀ j, a j < 1) (hlim : Tendsto a atTop (𝓝 1)) :
    ∀ η > 0, Tendsto (fun j => limsup (fun k => ((bridgeWalkLaw μ (q k) : Measure (ℕ → ℕ))).real
        {ω | η < ⨆ s : {s : Set.Icc (0 : ℝ) 1 // a j ≤ (s : ℝ)},
          dist (bridgeWalkPath B (q k) ω s) (bridgeWalkPath B (q k) ω ⟨a j, ha0 j, (ha1 j).le⟩)}) atTop)
      atTop (𝓝 0) := by
  intro η hη
  have hc4 : 0 < η / 4 := by positivity
  obtain ⟨NB, hNB⟩ := eventually_atTop.1
    (hB.tendsto_norming_atTop.eventually_ge_atTop (2 / η))
  have hK : ∀ᶠ k in atTop, max NB 1 ≤ q k := hqtop.eventually_ge_atTop (max NB 1)
  have hL0 : ∀ j, 0 ≤ limsup (fun k => ((bridgeWalkLaw μ (q k) : Measure (ℕ → ℕ))).real
      {ω | η < ⨆ s : {s : Set.Icc (0 : ℝ) 1 // a j ≤ (s : ℝ)},
        dist (bridgeWalkPath B (q k) ω s) (bridgeWalkPath B (q k) ω ⟨a j, ha0 j, (ha1 j).le⟩)})
      atTop := fun j =>
    le_limsup_of_frequently_le (Filter.Frequently.of_forall fun k => measureReal_nonneg)
      (isBoundedUnder_of ⟨1, fun k => measureReal_le_one⟩)
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨δ, hδ0, hδ12, hνδ⟩ := exists_small_startEscape hB.index_mem hr hc4 (half_pos hε)
  have hport := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hpre
    (isClosed_startEscape (c := η / 4) hδ0.le hδ12)
  have hev := eventually_lt_of_limsup_lt (hport.trans_lt hνδ)
  obtain ⟨J, hJ⟩ := eventually_atTop.1
    (hlim.eventually (Ioi_mem_nhds (show 1 - δ < 1 by linarith)))
  refine ⟨J, fun j hj => ?_⟩
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (hL0 j)]
  refine lt_of_le_of_lt ?_ (half_lt_self hε)
  apply limsup_le_of_le (Filter.isCoboundedUnder_le_of_le atTop fun k => measureReal_nonneg)
  filter_upwards [hev, hK] with k hk1 hk2
  have hn : 1 ≤ q k := le_of_max_le_right hk2
  have hBn : ∀ T, q k ≤ T → 2 / η ≤ B T := fun T hT =>
    hNB T ((le_of_max_le_left hk2).trans hT)
  have haj : 1 - a j ≤ δ := by
    have : 1 - δ < a j := hJ j hj
    linarith
  apply ENNReal.toReal_le_of_le_ofReal (half_pos hε).le
  calc (bridgeWalkLaw μ (q k) : Measure (ℕ → ℕ))
        {ω | η < ⨆ s : {s : Set.Icc (0 : ℝ) 1 // a j ≤ (s : ℝ)},
          dist (bridgeWalkPath B (q k) ω s) (bridgeWalkPath B (q k) ω ⟨a j, ha0 j, (ha1 j).le⟩)}
      ≤ (bridgeWalkLaw μ (q k) : Measure (ℕ → ℕ))
          ((Skorokhod.restrict hr ∘ bridgeWalkPath B (q k)) ⁻¹'
            startEscape (1 / 2) δ (η / 4)) :=
        bridgeWalkLaw_osc_le hn (hq k) hη hBn (ha0 j) (ha1 j) hδ12 haj hr
    _ ≤ (((bridgeWalkLaw μ (q k)).map (Skorokhod.restrict hr ∘ bridgeWalkPath B (q k)) :
          ProbabilityMeasure _) : Measure (Skorokhod.D (1 / 2) ℝ))
          (startEscape (1 / 2) δ (η / 4)) :=
        Measure.le_map_apply ((Skorokhod.measurable_restrict_of_nonneg (by norm_num)
          hr).comp (measurable_bridgeWalkPath B (q k))).aemeasurable _
    _ ≤ ENNReal.ofReal (ε / 2) := hk1.le

-- `hc`, `hne`, `hap`, `hnl` (and the binder `ha0` inside `hpre`) belong to the uniform interface of the
-- bridge principle and are not needed for (O): see `bridge_terminal_oscillation_of_half`.
set_option linter.unusedVariables false in
/-- (O) Terminal oscillation control of the bridge path, in the form of the hypothesis `hosc` of BGW's
`Skorokhod.tendsto_of_tendsto_restrict_of_oscillation` (C11b), derived from the prefix convergence (P) by the
time reversal of the increments (paper lines 2279-2312). -/
theorem bridge_terminal_oscillation {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ} (hc : IsCritical μ)
    (hne : μ 1 ≠ 1) (hap : Aperiodic μ)
    (hB : IsRealStableAttracted (realOffspringStepLaw μ) θ B)
    (hnl : ¬ IsLatticeLaw (etaLaw μ)) {q : ℕ → ℕ}
    (hqtop : Tendsto q atTop atTop) (hq : ∀ k, LeafAdmissible μ (q k))
    (hpre : ∀ (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1),
      Tendsto (fun k => (bridgeWalkLaw μ (q k)).map
          (Skorokhod.restrict ha1.le ∘ bridgeWalkPath B (q k)))
        atTop (𝓝 ((stableBridgeLaw θ).map (Skorokhod.restrict ha1.le))))
    {a : ℕ → ℝ} (ha0 : ∀ j, 0 ≤ a j) (ha1 : ∀ j, a j < 1) (hlim : Tendsto a atTop (𝓝 1)) :
    ∀ η > 0, Tendsto (fun j => limsup (fun k => ((bridgeWalkLaw μ (q k) : Measure (ℕ → ℕ))).real
        {ω | η < ⨆ s : {s : Set.Icc (0 : ℝ) 1 // a j ≤ (s : ℝ)},
          dist (bridgeWalkPath B (q k) ω s) (bridgeWalkPath B (q k) ω ⟨a j, ha0 j, (ha1 j).le⟩)}) atTop)
      atTop (𝓝 0) :=
  have h12 : (1 / 2 : ℝ) < 1 := by norm_num
  bridge_terminal_oscillation_of_half hB hqtop hq h12.le (hpre (1 / 2) (by norm_num) h12)
    ha0 ha1 hlim

end BGWLeaves.LeafLimits.BridgeTerminal
