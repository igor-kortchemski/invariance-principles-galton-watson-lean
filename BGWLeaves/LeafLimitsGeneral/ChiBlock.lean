module

public import BGWLeaves.LocalEstimates.Defs
public import BGWLeaves.GeneralAInf.BlockLocal
import BGWLeaves.Vervaat.MarkTime
import BGWLeaves.Vervaat.Discrete
import BGWLeaves.Vervaat.Cyclic
import BGWLeaves.Vervaat.TimeReversal
import Mathlib.Probability.Independence.InfinitePi

/-! Exact stopped-walk law, without analytic or non-lattice assumptions.
The elementary stopping-time and prefix-law proofs are copied and adapted from
`LocalEstimates.Chi` (the signed bridge argument). -/

@[expose] public section
namespace BGWLeaves.LeafLimitsGeneral.ChiBlock
open MeasureTheory ProbabilityTheory Filter BGW BGW.StableTrees
open BGWLeaves.StableAnalysis
open BGWLeaves.GeneralA MarkedWalk Regroup MarkedTime MarkedSpan
open scoped ENNReal NNReal Topology

private def bridgeSum {p : ℕ} (ω : Fin p → ℕ) : ℤ := ∑ i, (ω i : ℤ)

private def zeroCount {p : ℕ} (ω : Fin p → ℕ) : ℕ :=
  (Finset.univ.filter fun i => ω i = 0).card

private def bridgePredicate (p n : ℕ) (j : ℤ) (ω : Fin p → ℕ) : Prop :=
  bridgeSum ω + j = p ∧ zeroCount ω = n

private noncomputable def bridgeMass (μ : Measure ℕ) (p n : ℕ) (j : ℤ) : ℝ≥0∞ :=
  ∑' ω : Fin p → ℕ,
    Set.indicator {ω | bridgePredicate p n j ω} (fun ω => ∏ i, μ {ω i}) ω


private theorem isMarkTime_walkLeafTime {n : ℕ} {ω : ℕ → ℕ} {m : ℕ} (h : IsMarkTime n ω m) :
    walkLeafTime ω n = (m : ℕ∞) := by
  unfold walkLeafTime
  apply le_antisymm
  · exact iInf₂_le m h.1
  · refine le_iInf₂ fun q hq => ?_
    have : m ≤ q := by
      by_contra hlt
      have := h.2 q (not_le.1 hlt)
      omega
    exact_mod_cast this

private theorem walkLeafTime_ne_top_iff {n : ℕ} {ω : ℕ → ℕ} :
    walkLeafTime ω n ≠ ⊤ ↔ ∃ m, IsMarkTime n ω m := by
  constructor
  · intro h
    by_contra hne
    apply h
    have : ¬ ∃ m, walkLeafCount ω m = n := by
      rw [← BGWLeaves.Vervaat.MarkTime.exists_isMarkTime_iff]; exact hne
    unfold walkLeafTime
    simp only [iInf_eq_top]
    intro m hm
    exact absurd ⟨m, hm⟩ this
  · rintro ⟨m, hm⟩
    rw [isMarkTime_walkLeafTime hm]
    exact ENat.natCast_ne_top m

private theorem walkLeafTime_eq_coe_iff {n : ℕ} {ω : ℕ → ℕ} {m : ℕ} :
    walkLeafTime ω n = (m : ℕ∞) ↔ IsMarkTime n ω m := by
  constructor
  · intro h
    have hne : walkLeafTime ω n ≠ ⊤ := by rw [h]; exact ENat.natCast_ne_top m
    obtain ⟨m', hm'⟩ := walkLeafTime_ne_top_iff.1 hne
    have := isMarkTime_walkLeafTime hm'
    rw [h] at this
    have : m = m' := by exact_mod_cast this
    subst this
    exact hm'
  · exact isMarkTime_walkLeafTime



private theorem last_mark_iff {n : ℕ} (hn : 1 ≤ n) (ω : ℕ → ℕ) (p : ℕ) :
    IsMarkTime n ω (p + 1) ↔ walkLeafCount ω p = n - 1 ∧ ω p = 0 := by
  rw [IsMarkTime]
  constructor
  · rintro ⟨hc, hmin⟩
    have hh := hmin p (by omega)
    rw [Vervaat.Discrete.walkLeafCount_succ'] at hc
    split_ifs at hc with h
    · exact ⟨by omega, h⟩
    · omega
  · rintro ⟨hp, hz⟩
    refine ⟨by rw [Vervaat.Discrete.walkLeafCount_succ', hp, ite_eq_left hz]; omega, ?_⟩
    intro q hq
    have hh := Vervaat.Discrete.walkLeafCount_mono' ω (show q ≤ p by omega)
    omega

private theorem walk_sum_succ (ω : ℕ → ℕ) (p : ℕ) : walkSum ω (p + 1) = walkSum ω p + ((ω p : ℤ) - 1) := by
  unfold walkSum
  rw [Finset.sum_range_succ]

private theorem prefix_count (ω : ℕ → ℕ) (p : ℕ) :
    zeroCount (fun i : Fin p => ω i) = walkLeafCount ω p := by
  classical
  simp only [zeroCount, walkLeafCount, Finset.card_filter]
  rw [Finset.sum_range]
  apply Finset.sum_congr rfl
  intro i _
  have he : ((ω i : ℤ) - 1 = -1) ↔ ω i = 0 := by omega
  simp only [he]

private theorem prefix_sum (ω : ℕ → ℕ) (p : ℕ) :
    bridgeSum (fun i : Fin p => ω i) = walkSum ω p + p := by
  unfold bridgeSum walkSum
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range]
  simp only [nsmul_eq_mul, mul_one]
  rw [Finset.sum_range]
  ring

private def lastMarkEvent (n : ℕ) (j : ℤ) (p : ℕ) : Set (ℕ → ℕ) :=
  {ω | walkLeafCount ω p = n - 1 ∧ ω p = 0 ∧ walkSum ω p = -j}

private theorem lastMarkEvent_iff {n : ℕ} (hn : 1 ≤ n) (j : ℤ) (p : ℕ) (ω : ℕ → ℕ) :
    ω ∈ lastMarkEvent n j p ↔ IsMarkTime n ω (p + 1) ∧ walkSum ω (p + 1) = -1 - j := by
  rw [last_mark_iff hn, walk_sum_succ]
  simp only [lastMarkEvent, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hc, hz, hs⟩
    exact ⟨⟨hc, hz⟩, by rw [hz, hs]; simp; ring⟩
  · rintro ⟨⟨hc, hz⟩, hs⟩
    refine ⟨hc, hz, ?_⟩
    rw [hz] at hs
    omega

private theorem prefix_pair_law (μ : PMF ℕ) (p : ℕ) :
    (iidWalk μ).map (fun ω => (ω p, fun i : Fin p => ω i)) =
      μ.toMeasure.prod (Measure.pi (fun _ : Fin p => μ.toMeasure)) := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (p + 1) => ℕ) (Fin.last p)
  have hp : (iidWalk μ).map (fun ω => fun i : Fin (p + 1) => ω i) = Measure.pi (fun _ : Fin (p + 1) => μ.toMeasure) := by
    rw [iidWalk, Measure.map_infinitePi_infinitePi_of_inj (P := fun _ : ℕ => μ.toMeasure) Fin.val_injective,
      Measure.infinitePi_eq_pi]
  have he := (measurePreserving_piFinSuccAbove (fun _ : Fin (p + 1) => μ.toMeasure) (Fin.last p)).map_eq
  rw [← hp, Measure.map_map e.measurable (by fun_prop)] at he
  convert he using 1
  congr 1
  funext ω
  apply Prod.ext
  · rfl
  · funext i
    change ω i = ω ((Fin.last p).succAbove i)
    rw [Fin.succAbove_last]
    rfl

private theorem lastMarkEvent_mass (μ : PMF ℕ) (n : ℕ) (j : ℤ) (p : ℕ) :
    iidWalk μ (lastMarkEvent n j p) = μ 0 * bridgeMass μ.toMeasure p (n - 1) j := by
  let B : Set (Fin p → ℕ) := {ω | bridgePredicate p (n - 1) j ω}
  have hm : Measurable (fun ω : ℕ → ℕ => (ω p, fun i : Fin p => ω i)) := by fun_prop
  have hB : MeasurableSet B := (Set.to_countable _).measurableSet
  have hpre : (fun ω : ℕ → ℕ => (ω p, fun i : Fin p => ω i)) ⁻¹' ({0} ×ˢ B) = lastMarkEvent n j p := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_prod, Set.mem_singleton_iff, B, bridgePredicate,
      Set.mem_ofPred_eq, lastMarkEvent, prefix_count, prefix_sum]
    constructor <;> intro h <;> omega
  have hh := congrArg (fun P : Measure (ℕ × (Fin p → ℕ)) => P ({0} ×ˢ B)) (prefix_pair_law μ p)
  rw [Measure.map_apply hm ((measurableSet_singleton 0).prod hB), hpre,
    Measure.prod_prod, PMF.toMeasure_apply_singleton μ 0 (measurableSet_singleton 0)] at hh
  rw [hh, BGW.pi_eq_tsum_indicator μ.toMeasure B]
  rfl

private theorem lastMarkEvent_measurable (n : ℕ) (j : ℤ) (p : ℕ) : MeasurableSet (lastMarkEvent n j p) := by
  exact (measurableSet_eq_fun (Vervaat.TimeReversal.measurable_walkLeafCount p) measurable_const).inter
    (((measurable_pi_apply p) (measurableSet_singleton 0)).inter
      (Vervaat.Cyclic.measurable_walkSum p (measurableSet_singleton (-j))))


private theorem stop_event_union {n : ℕ} (hn : 1 ≤ n) (j : ℤ) :
    walkStopEvent n (-1 - j) = ⋃ q : ℕ, lastMarkEvent n j (n - 1 + q) := by
  ext ω
  constructor
  · rintro ⟨hfinite, hpos⟩
    obtain ⟨m, hm⟩ := walkLeafTime_ne_top_iff.mp hfinite
    have hm0 : m ≠ 0 := by
      intro hz
      have hh := hm.1
      simp [hz, walkLeafCount] at hh
      omega
    obtain ⟨p, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm0
    have hcount := (last_mark_iff hn ω p).mp hm
    have hp : n - 1 ≤ p := by
      have hh : walkLeafCount ω p ≤ p := by
        unfold walkLeafCount
        exact (Finset.card_filter_le _ _).trans (by simp)
      omega
    apply Set.mem_iUnion.mpr
    refine ⟨p - (n - 1), ?_⟩
    rw [Nat.add_sub_of_le hp]
    apply (lastMarkEvent_iff hn j p ω).mpr
    refine ⟨hm, ?_⟩
    simpa only [walkStopPos, isMarkTime_walkLeafTime hm, ENat.toNat_natCast] using hpos
  · intro h
    obtain ⟨q, hq⟩ := Set.mem_iUnion.mp h
    obtain ⟨hm, hpos⟩ := (lastMarkEvent_iff hn j (n - 1 + q) ω).mp hq
    refine ⟨by rw [isMarkTime_walkLeafTime hm]; exact ENat.natCast_ne_top _, ?_⟩
    simpa only [walkStopPos, isMarkTime_walkLeafTime hm, ENat.toNat_natCast] using hpos

private theorem lastMarkEvent_disjoint {n : ℕ} (hn : 1 ≤ n) (j : ℤ) :
    Pairwise (Function.onFun Disjoint (lastMarkEvent n j)) := by
  intro p q hpq
  apply Set.disjoint_left.mpr
  intro ω hp hq
  have hmp := ((lastMarkEvent_iff hn j p ω).mp hp).1
  have hmq := ((lastMarkEvent_iff hn j q ω).mp hq).1
  have hh := Vervaat.MarkTime.IsMarkTime.unique hmp hmq
  omega


/-- The stopped walk is the sum over the location of its final marked letter. -/
private theorem chi_eq_tsum_bridge (μ : PMF ℕ) {n : ℕ} (hn : 1 ≤ n) (j : ℤ) :
    chi μ n j = ∑' q : ℕ, μ 0 * bridgeMass μ.toMeasure (n - 1 + q) (n - 1) j := by
  unfold chi
  rw [stop_event_union hn,
    measure_iUnion (f := fun q => lastMarkEvent n j (n - 1 + q))
      (fun p q hpq => by apply lastMarkEvent_disjoint hn j; omega)
      (fun q => lastMarkEvent_measurable n j (n - 1 + q))]
  exact tsum_congr fun q => lastMarkEvent_mass μ n j (n - 1 + q)

local instance markedStep_sfinite (μ : PMF ℕ) (A : Set ℕ) :
    SFinite (markedStep (fun k => μ k) A) := by
  unfold markedStep weightedStep
  infer_instance

local instance unmarkedStep_sfinite (μ : PMF ℕ) (A : Set ℕ) :
    SFinite (unmarkedStep (fun k => μ k) A) := by
  unfold unmarkedStep
  infer_instance

local instance walk_sfinite (ν : Measure ℤ) [SFinite ν] (n : ℕ) :
    SFinite (intWalk ν n) := by
  induction n with
  | zero => simp only [intWalk]; infer_instance
  | succ n ih => simpa only [intWalk] using
      (inferInstance : SFinite ((intWalk ν n).conv ν))

private theorem bridgeMass_eq_markedWalk (μ : PMF ℕ) (p n : ℕ) (j : ℤ) :
    bridgeMass μ.toMeasure p n j = markedWalk (fun k => μ k) {0} p n {-j} := by
  classical
  rw [markedWalk, Measure.sum_apply _ (measurableSet_singleton _)]
  unfold bridgeMass
  apply tsum_congr
  intro ω
  have hs : wordSum ω = -j ↔ bridgeSum ω + j = p := by
    simp only [wordSum, bridgeSum, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    omega
  have hc : markCount {0} ω = zeroCount ω := by simp only [markCount, zeroCount, Set.mem_singleton_iff]
  simp only [PMF.toMeasure_apply_singleton μ _ (measurableSet_singleton _),
    Measure.smul_apply, smul_eq_mul, Measure.dirac_apply' _ (measurableSet_singleton _),
    Set.indicator, Set.mem_singleton_iff, hc, bridgePredicate, Set.mem_ofPred_eq]
  split_ifs <;> simp_all

private theorem markedStep_zero (μ : PMF ℕ) :
    markedStep (fun k => μ k) {0} = μ 0 • Measure.dirac (-1 : ℤ) := by
  classical
  simp only [markedStep, weightedStep, Set.mem_singleton_iff, ite_smul, zero_smul]
  ext s hs
  rw [Measure.sum_apply _ hs, tsum_eq_single 0]
  · simp
  · intro k hk
    simp [hk]

/-- The leaf-clock bridge is exactly the marked-block walk, at every signed endpoint.
No criticality, attraction, aperiodicity, or non-lattice assumption is needed. -/
theorem chi_eq_blockWalk (μ : PMF ℕ) {n : ℕ} (hn : 1 ≤ n) (j : ℤ) :
    chi μ n j = intWalk (blockStep μ {0}) n {-1 - j} := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  rw [chi_eq_tsum_bridge μ (by omega), blockStep, blockLaw_walk _ _ m,
    Measure.sum_apply _ (measurableSet_singleton _)]
  apply tsum_congr
  intro q
  rw [bridgeMass_eq_markedWalk, markedWalk_binomial]
  simp only [Nat.succ_sub_one, Nat.add_sub_cancel_left,
    Measure.smul_apply, smul_eq_mul]
  have hconv : (intWalk (markedStep (fun k => μ k) {0}) (m + 1)).conv
      (intWalk (unmarkedStep (fun k => μ k) {0}) q) =
      (markedStep (fun k => μ k) {0}).conv
        ((intWalk (markedStep (fun k => μ k) {0}) m).conv
          (intWalk (unmarkedStep (fun k => μ k) {0}) q)) := by
    rw [intWalk, Measure.conv_comm (intWalk _ m), Measure.conv_assoc]
  rw [hconv, markedStep_zero, Measure.conv_smul_left,
    Measure.dirac_conv, Measure.smul_apply, smul_eq_mul,
    Measure.map_apply (by fun_prop) (measurableSet_singleton _)]
  have he : (fun x : ℤ => -1 + x) ⁻¹' {-1 - j} = {-j} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    omega
  rw [he, Nat.add_comm m q]
  ring

/-- Real-valued version of the exact leaf-clock identity. -/
theorem chi_toReal_eq_blockWalk (μ : PMF ℕ) {n : ℕ} (hn : 1 ≤ n) (j : ℤ) :
    (chi μ n j).toReal = intWalkProb (blockStep μ {0}) n (-1 - j) := by
  rw [chi_eq_blockWalk μ hn]
  rfl

end BGWLeaves.LeafLimitsGeneral.ChiBlock
