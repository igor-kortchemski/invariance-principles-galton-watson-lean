module

public import BGWLeaves.GeneralAFunctional.WalkClock
public import BGWLeaves.GeneralA.MarkedTime
public import BGWLeaves.GeneralAInf.Defs

/-! The endpoint law at an arbitrary offspring mark. -/

@[expose] public section
namespace BGWLeaves.GeneralAFunctional.WalkStopped
open MeasureTheory ProbabilityTheory Filter BGW BGW.StableTrees
open BGWLeaves.StableAnalysis
open BGWLeaves.GeneralA MarkedWalk MarkedTime Regroup
open BGWLeaves.GeneralAFunctional.WalkCyclic BGWLeaves.GeneralAFunctional.WalkVervaat
open BGWLeaves.Vervaat.Cyclic
open scoped ENNReal

noncomputable section
attribute [local instance] Classical.propDecidable

def aStopEvent (A : Set ℕ) (n : ℕ) (z : ℤ) : Set (ℕ → ℕ) :=
  {ω | ∃ k, IsAMarkTime A n ω k ∧ walkSum ω k = z}

def lastMarkEvent (A : Set ℕ) (n : ℕ) (z : ℤ) (p : ℕ) : Set (ℕ → ℕ) :=
  {ω | walkACount A ω p = n ∧ ω p ∈ A ∧ walkSum ω (p + 1) = z}

theorem last_mark_iff (A : Set ℕ) (n : ℕ) (ω : ℕ → ℕ) (p : ℕ) :
    IsAMarkTime A (n + 1) ω (p + 1) ↔ walkACount A ω p = n ∧ ω p ∈ A := by
  constructor
  · rintro ⟨hc, hmin⟩
    have hh := hmin p (by omega)
    rw [walkACount_succ] at hc
    split_ifs at hc with h
    · exact ⟨by omega, h⟩
    · omega
  · rintro ⟨hp, hm⟩
    refine ⟨by rw [walkACount_succ, hp, ite_eq_left hm], ?_⟩
    intro q hq
    have := walkACount_mono A ω (show q ≤ p by omega)
    omega

private theorem prefix_count (A : Set ℕ) (ω : ℕ → ℕ) (p : ℕ) :
    markCount A (fun i : Fin p => ω i) = walkACount A ω p := by
  simp only [markCount, walkACount, Finset.card_filter]
  rw [Finset.sum_range]

private theorem prefix_sum (ω : ℕ → ℕ) (p : ℕ) :
    wordSum (fun i : Fin p => ω i) = walkSum ω p := by
  unfold wordSum walkSum
  rw [Finset.sum_range]

private theorem prefix_pair_law (μ : PMF ℕ) (p : ℕ) :
    (iidWalk μ).map (fun ω => (ω p, fun i : Fin p => ω i)) =
      μ.toMeasure.prod (Measure.pi (fun _ : Fin p => μ.toMeasure)) := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (p + 1) => ℕ) (Fin.last p)
  have hp : (iidWalk μ).map (fun ω => fun i : Fin (p + 1) => ω i) =
      Measure.pi (fun _ : Fin (p + 1) => μ.toMeasure) := by
    rw [iidWalk, Measure.map_infinitePi_infinitePi_of_inj
      (P := fun _ : ℕ => μ.toMeasure) Fin.val_injective, Measure.infinitePi_eq_pi]
  have he := (measurePreserving_piFinSuccAbove
    (fun _ : Fin (p + 1) => μ.toMeasure) (Fin.last p)).map_eq
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

private instance markedStep_sfinite (μ : PMF ℕ) (A : Set ℕ) :
    SFinite (markedStep (fun k => μ k) A) := by
  unfold markedStep weightedStep
  infer_instance

private instance unmarkedStep_sfinite (μ : PMF ℕ) (A : Set ℕ) :
    SFinite (unmarkedStep (fun k => μ k) A) := by
  unfold unmarkedStep
  infer_instance

private instance markedWalk_sfinite (μ : PMF ℕ) (A : Set ℕ) (p n : ℕ) :
    SFinite (markedWalk (fun k => μ k) A p n) := by
  unfold markedWalk
  infer_instance

private theorem conv_sums_dirac {ι κ : Type*} [Countable κ]
    (u : ι → ℝ≥0∞) (v : κ → ℝ≥0∞) (a : ι → ℤ) (b : κ → ℤ) :
    (Measure.sum fun i => u i • Measure.dirac (a i)).conv
        (Measure.sum fun j => v j • Measure.dirac (b j)) =
      Measure.sum fun p : ι × κ => (u p.1 * v p.2) • Measure.dirac (a p.1 + b p.2) := by
  rw [Measure.conv, Measure.prod_sum, Measure.map_sum (by fun_prop)]
  congr 1
  funext p
  change (u p.1 • Measure.dirac (a p.1)).conv (v p.2 • Measure.dirac (b p.2)) = _
  rw [Measure.conv_smul_left, Measure.conv_smul_right, smul_smul, Measure.dirac_conv_dirac]

/-- At a fixed final-mark location, the earlier letters have exactly `n` marks
and the last increment has the unnormalized marked-step law. -/
theorem lastMarkEvent_mass (μ : PMF ℕ) (A : Set ℕ) (n : ℕ) (z : ℤ) (p : ℕ) :
    iidWalk μ (lastMarkEvent A n z p) =
      ((markedStep (fun k => μ k) A).conv (markedWalk (fun k => μ k) A p n)) {z} := by
  let E : Set (ℕ × (Fin p → ℕ)) :=
    {x | x.1 ∈ A ∧ markCount A x.2 = n ∧ ((x.1 : ℤ) - 1) + wordSum x.2 = z}
  have hm : Measurable (fun ω : ℕ → ℕ => (ω p, fun i : Fin p => ω i)) := by fun_prop
  have hE : MeasurableSet E := MeasurableSet.of_discrete
  have he : (fun ω : ℕ → ℕ => (ω p, fun i : Fin p => ω i)) ⁻¹' E =
      lastMarkEvent A n z p := by
    ext ω
    simp only [E, Set.mem_preimage, Set.mem_ofPred_eq, prefix_count, prefix_sum, lastMarkEvent]
    have hs : walkSum ω (p + 1) = walkSum ω p + ((ω p : ℤ) - 1) := by
      unfold walkSum
      rw [Finset.sum_range_succ]
    rw [hs, add_comm ((ω p : ℤ) - 1)]
    tauto
  have hp := congrArg (fun P : Measure (ℕ × (Fin p → ℕ)) => P E) (prefix_pair_law μ p)
  rw [Measure.map_apply hm hE, he, Measure.prod_apply hE, lintegral_countable'] at hp
  rw [hp]
  unfold markedStep weightedStep markedWalk
  rw [conv_sums_dirac, Measure.sum_apply _ (measurableSet_singleton _), ENNReal.tsum_prod']
  apply tsum_congr
  intro a
  rw [BGW.pi_eq_tsum_indicator μ.toMeasure]
  rw [← ENNReal.tsum_mul_right]
  apply tsum_congr
  intro v
  simp only [PMF.toMeasure_apply_singleton μ _ (measurableSet_singleton _), E,
    Set.mem_preimage, Set.mem_ofPred_eq, Set.indicator, Measure.smul_apply, smul_eq_mul,
    Measure.dirac_apply' _ (measurableSet_singleton _), Set.mem_singleton_iff]
  split_ifs <;> simp_all [mul_comm]

theorem measurableSet_lastMarkEvent (A : Set ℕ) (n : ℕ) (z : ℤ) (p : ℕ) :
    MeasurableSet (lastMarkEvent A n z p) :=
  (measurable_walkACount A p (measurableSet_singleton _)).inter
    (((measurable_pi_apply p) MeasurableSet.of_discrete).inter
      (measurable_walkSum (p + 1) (measurableSet_singleton _)))

theorem aStopEvent_eq_iUnion (A : Set ℕ) (n : ℕ) (z : ℤ) :
    aStopEvent A (n + 1) z = ⋃ q : ℕ, lastMarkEvent A n z (n + q) := by
  ext ω
  constructor
  · rintro ⟨k, hk, hs⟩
    have hk0 : k ≠ 0 := by
      intro he
      have := hk.1
      simp [he, walkACount] at this
    obtain ⟨p, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk0
    obtain ⟨hc, hm⟩ := (last_mark_iff A n ω p).mp hk
    have hn : n ≤ p := by
      rw [← hc]
      exact (Finset.card_filter_le _ _).trans (by simp)
    apply Set.mem_iUnion.mpr
    refine ⟨p - n, ?_⟩
    rw [Nat.add_sub_of_le hn]
    exact ⟨hc, hm, hs⟩
  · intro h
    obtain ⟨q, hc, hm, hs⟩ := Set.mem_iUnion.mp h
    exact ⟨n + q + 1, (last_mark_iff A n ω (n + q)).mpr ⟨hc, hm⟩, hs⟩

theorem lastMarkEvent_disjoint (A : Set ℕ) (n : ℕ) (z : ℤ) :
    Pairwise (Function.onFun Disjoint (lastMarkEvent A n z)) := by
  intro p q hpq
  refine Set.disjoint_left.mpr fun ω hp hq => hpq ?_
  have h1 := (last_mark_iff A n ω p).mpr ⟨hp.1, hp.2.1⟩
  have h2 := (last_mark_iff A n ω q).mpr ⟨hq.1, hq.2.1⟩
  have he := IsAMarkTime.unique h1 h2
  omega

/-- F: exact endpoint law at the nth A-mark, at every signed endpoint. This is
an identity for the original walk, whose increments remain at least `-1`. -/
theorem aStopEvent_mass (μ : PMF ℕ) (A : Set ℕ) (n : ℕ) (z : ℤ) :
    iidWalk μ (aStopEvent A (n + 1) z) = intWalk (blockStep μ A) (n + 1) {z} := by
  rw [aStopEvent_eq_iUnion, measure_iUnion]
  · rw [blockStep, blockLaw_walk, Measure.sum_apply _ (measurableSet_singleton _)]
    apply tsum_congr
    intro q
    rw [lastMarkEvent_mass, markedWalk_binomial, Measure.conv_smul_right,
      Measure.smul_apply]
    simp only [Nat.add_sub_cancel_left, smul_eq_mul]
    rw [Nat.add_comm n q]
    congr 1
    have he : (markedStep (fun k => μ k) A).conv
        ((intWalk (markedStep (fun k => μ k) A) n).conv
          (intWalk (unmarkedStep (fun k => μ k) A) q)) =
        (intWalk (markedStep (fun k => μ k) A) (n + 1)).conv
          (intWalk (unmarkedStep (fun k => μ k) A) q) := by
      rw [← Measure.conv_assoc, Measure.conv_comm (markedStep _ A)]
      rfl
    rw [he]
    rfl
  · intro p q hpq
    exact lastMarkEvent_disjoint A n z (by omega : n + p ≠ n + q)
  · exact fun q => measurableSet_lastMarkEvent A n z (n + q)

end
end BGWLeaves.GeneralAFunctional.WalkStopped
