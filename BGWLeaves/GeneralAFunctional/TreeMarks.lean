module

public import BGWLeaves.GeneralAFunctional.TreeConcentration
public import BGWLeaves.LeafConcentration.Chernoff

/-! Bounded Bernoulli marks in deterministic exploration prefixes. -/

@[expose] public section

namespace BGWLeaves.GeneralAFunctional.TreeMarks

open MeasureTheory ProbabilityTheory Filter Set BGW
open BGW.StableTrees BGW.StableTrees.DiscreteForest BGW.LocallyFinite
open BGWLeaves.GeneralAFunctional.TreePrefix BGWLeaves.GeneralAFunctional.TreeDensity
open BGWLeaves.GeneralAFunctional.TreeEvents BGWLeaves.GeneralAFunctional.TreeLocal
open BGWLeaves.GeneralAFunctional.TreeConcentration
open scoped ENNReal Topology Classical

/-- The revealed count is a sum of bounded indicator variables. -/
theorem prefixMarks_seqPrefix (A : Set ℕ) (ω : ℕ → ℕ) (n : ℕ) :
    (prefixMarks A (seqPrefix n ω) : ℝ) =
      ∑ i ∈ Finset.range n, if ω i ∈ A then (1 : ℝ) else 0 := by
  induction n with
  | zero => simp [prefixMarks, seqPrefix]
  | succ n ih =>
    rw [show n + 1 = n + 1 from rfl, seqPrefix_add, prefixMarks_append]
    simp only [Nat.cast_add, Finset.sum_range_succ, ih]
    simp [prefixMarks, seqPrefix, DiscreteForest.shiftSeq]

/-- Fixed positive deviations of the prefix mark proportion have exponential tails.
No assumption about offspring increments is used here: these are Bernoulli indicators. -/
theorem prefix_marks_chernoff {μ : PMF ℕ} {A : Set ℕ}
    (hA0 : μ.toMeasure A ≠ 0) (hA1 : μ.toMeasure A ≠ 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 1 ≤ n →
      (offspringSeqLaw μ).toMeasure.real
        {ω | ε < |(prefixMarks A (seqPrefix n ω) : ℝ) / n - (μ.toMeasure A).toReal|} ≤
      4 * Real.exp (-c * n) := by
  let p := (μ.toMeasure A).toReal
  have hp0 : 0 < p := ENNReal.toReal_pos hA0 (measure_ne_top _ _)
  have hp1 : p < 1 := by
    have hlt : μ.toMeasure A < 1 := lt_of_le_of_ne prob_le_one hA1
    simpa only [ENNReal.toReal_one] using
      (ENNReal.toReal_lt_toReal (measure_ne_top _ _) ENNReal.one_ne_top).mpr hlt
  let P := (offspringSeqLaw μ).toMeasure
  let X : ℕ → (ℕ → ℕ) → ℝ := fun i ω => if ω i ∈ A then 1 else 0
  have hX : ∀ i, Measurable (X i) := fun i =>
    (measurable_of_countable (fun k : ℕ => if k ∈ A then (1 : ℝ) else 0)).comp (measurable_pi_apply i)
  have hind : iIndepFun X P :=
    iIndepFun_infinitePi (X := fun (_ : ℕ) (k : ℕ) => if k ∈ A then (1 : ℝ) else 0)
      (fun _ => measurable_of_countable _)
  have hber : ∀ i, P {ω | X i ω = 1} = ENNReal.ofReal p ∧
      P {ω | X i ω = 0} = ENNReal.ofReal (1 - p) := by
    intro i
    have hmap : P.map (Function.eval i) = μ.toMeasure := Measure.infinitePi_map_eval _ _
    have hone : {ω | X i ω = 1} = (Function.eval i) ⁻¹' A := by ext ω; simp [X]
    have hzero : {ω | X i ω = 0} = (Function.eval i) ⁻¹' Aᶜ := by ext ω; simp [X]
    rw [hone, hzero, ← Measure.map_apply (measurable_pi_apply i) MeasurableSet.of_discrete,
      ← Measure.map_apply (measurable_pi_apply i) MeasurableSet.of_discrete, hmap]
    constructor
    · exact (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
    · rw [prob_compl_eq_one_sub MeasurableSet.of_discrete]
      change 1 - μ.toMeasure A = ENNReal.ofReal (1 - (μ.toMeasure A).toReal)
      rw [← ENNReal.toReal_one, ← ENNReal.toReal_sub_of_le prob_le_one ENNReal.one_ne_top,
        ENNReal.ofReal_toReal (by finiteness)]
  obtain ⟨d, hd, N, hN⟩ := LeafConcentration.Chernoff.phiStar_lower hp0 hp1 hε
  let r := max N 1
  have hr : (1 : ℝ) ≤ r := by exact_mod_cast (le_max_right N 1)
  have hr0 : (0 : ℝ) < r := lt_of_lt_of_le zero_lt_one hr
  let a : ℝ := ε / (r : ℝ) ^ (1 / 4 : ℝ)
  have ha : 0 < a := by dsimp [a]; positivity
  have hae : a ≤ ε := by
    dsimp [a]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < (r : ℝ) ^ (1 / 4 : ℝ))).mpr
    have hpow : (1 : ℝ) ≤ (r : ℝ) ^ (1 / 4 : ℝ) := Real.one_le_rpow hr (by norm_num)
    nlinarith
  have hp := hN r (le_max_left N 1)
  have hplus : 0 < phiStar p (p + a) := (div_pos hd (by positivity)).trans hp.1
  have hminus : 0 < phiStar p (p - a) := (div_pos hd (by positivity)).trans hp.2
  let c := min (phiStar p (p + a)) (phiStar p (p - a))
  refine ⟨c, lt_min hplus hminus, fun n hn => ?_⟩
  obtain ⟨hu, hl⟩ := LeafConcentration.Chernoff.lem_phi_i P hp0 hp1 X hX hind hber ha hn
  have hs : {ω | ε < |(prefixMarks A (seqPrefix n ω) : ℝ) / n - p|} ⊆
      {ω | p + a < (∑ i ∈ Finset.range n, X i ω) / n} ∪
        {ω | (∑ i ∈ Finset.range n, X i ω) / n < p - a} := by
    intro ω hω
    change ε < |(prefixMarks A (seqPrefix n ω) : ℝ) / n - p| at hω
    rw [prefixMarks_seqPrefix] at hω
    rcases (lt_abs.mp hω) with h | h
    · left; change p + a < (∑ i ∈ Finset.range n, if ω i ∈ A then (1 : ℝ) else 0) / n; linarith
    · right; change (∑ i ∈ Finset.range n, if ω i ∈ A then (1 : ℝ) else 0) / n < p - a; linarith
  have hup : 2 * Real.exp (-(n * phiStar p (p + a))) ≤ 2 * Real.exp (-c * n) := by
    apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by norm_num)
    nlinarith [min_le_left (phiStar p (p + a)) (phiStar p (p - a)), Nat.cast_nonneg (α := ℝ) n]
  have hlo : 2 * Real.exp (-(n * phiStar p (p - a))) ≤ 2 * Real.exp (-c * n) := by
    apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by norm_num)
    nlinarith [min_le_right (phiStar p (p + a)) (phiStar p (p - a)), Nat.cast_nonneg (α := ℝ) n]
  calc
    _ ≤ P.real ({ω | p + a < (∑ i ∈ Finset.range n, X i ω) / n} ∪
        {ω | (∑ i ∈ Finset.range n, X i ω) / n < p - a}) :=
      measureReal_mono hs (measure_ne_top _ _)
    _ ≤ _ := measureReal_union_le _ _
    _ ≤ 2 * Real.exp (-c * n) + 2 * Real.exp (-c * n) := add_le_add (hu.trans hup) (hl.trans hlo)
    _ = _ := by ring

end BGWLeaves.GeneralAFunctional.TreeMarks
