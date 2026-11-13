module

public import BGWLeaves.GeneralAFunctional.TreeLocal
public import BGWLeaves.LeafLimits.Bridge
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! Conditional total-size concentration from the already proved marked-forest
Chernoff estimate and the admissible denominator local limit. -/

@[expose] public section

namespace BGWLeaves.GeneralAFunctional.TreeConcentration

open MeasureTheory ProbabilityTheory Filter Set BGW
open BGW.StableTrees BGW.StableTrees.DiscreteForest BGW.LocallyFinite
open BGWLeaves.StableAnalysis BGWLeaves.GeneralA.MarkedLaw
open BGWLeaves.GeneralAFunctional.TreePrefix BGWLeaves.GeneralAFunctional.TreeDensity
open BGWLeaves.GeneralAFunctional.TreeEvents BGWLeaves.GeneralAFunctional.TreeLocal
open scoped ENNReal Topology Classical

/-- The unconditioned joint bad-size/mark-count mass has an exponential bound. -/
theorem joint_size_error_bound {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    {A : Set ℕ} (hA : μ.toMeasure A ≠ 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ n : ℕ, 1 ≤ n →
      bienaymeLaw μ.toMeasure
        ({T | FiniteVertices T ∧ zetaA A T = (n : ℕ∞)} ∩
          {T | ε * n < |(treeSize T : ℝ) - n / (μ.toMeasure A).toReal|}) ≤
        ENNReal.ofReal (C * Real.exp (-c * n)) := by
  obtain ⟨C, c, hC, hc', hb⟩ := GeneralAInf.Forest.eq_gen2_concentration hc hne hA hε
  refine ⟨C, c, hC, hc', fun n hn => ?_⟩
  have heq : (MeasurableEquiv.funUnique (Fin 1) LocallyFinite.Tree) ⁻¹'
      ({T | FiniteVertices T ∧ zetaA A T = (n : ℕ∞)} ∩
        {T | ε * n < |(treeSize T : ℝ) - n / (μ.toMeasure A).toReal|}) =
      ⋃ p ∈ {p : ℕ | ε * n < |(p : ℝ) - n / (μ.toMeasure A).toReal|},
        forestAEvent A 1 p n := by
    ext F
    constructor
    · rintro ⟨⟨hF, hcount⟩, hbad⟩
      obtain ⟨t, ht⟩ := (exists_toLocallyFinite_iff (F default)).mpr hF
      apply mem_iUnion.mpr
      refine ⟨t.size, mem_iUnion.mpr ⟨?_, ?_⟩⟩
      · change ε * n < |(t.size : ℝ) - n / (μ.toMeasure A).toReal|
        change ε * n < |(treeSize (F default) : ℝ) - n / (μ.toMeasure A).toReal| at hbad
        simpa only [← ht, treeSize, ncard_present_toLocallyFinite] using hbad
      · refine ⟨fun _ => t, by simp, ?_, ?_⟩
        · change zetaA A (F default) = (n : ℕ∞) at hcount
          rw [← ht, zetaA_toLocallyFinite] at hcount
          simpa using ENat.natCast_inj.mp hcount
        · funext i
          simpa only [Subsingleton.elim i default] using ht.symm
    · intro h
      obtain ⟨p, hp⟩ := mem_iUnion.mp h
      obtain ⟨hbad, ts, hsize, hcount, rfl⟩ := mem_iUnion.mp hp
      have hsz : (ts default).size = p := by simpa using hsize
      have hcnt : GeneralA.Marked.treeACount A (ts default) = n := by simpa using hcount
      change (FiniteVertices (ts default).toLocallyFinite ∧
        zetaA A (ts default).toLocallyFinite = (n : ℕ∞)) ∧ _
      refine ⟨⟨(ts default).finiteVertices_toLocallyFinite, ?_⟩, ?_⟩
      · rw [zetaA_toLocallyFinite, hcnt]
      · simpa only [mem_ofPred_eq, MeasurableEquiv.funUnique_apply, treeSize,
          ncard_present_toLocallyFinite, hsz] using hbad
  have hm := (measurePreserving_funUnique (bienaymeLaw μ.toMeasure) (Fin 1)).measure_preimage_equiv
    ({T | FiniteVertices T ∧ zetaA A T = (n : ℕ∞)} ∩
      {T | ε * n < |(treeSize T : ℝ) - n / (μ.toMeasure A).toReal|})
  rw [heq] at hm
  rw [← hm]
  convert hb 1 n le_rfl hn using 1
  all_goals first | rfl | norm_num

/-- The canonical marked exploration scale has at most quadratic growth. -/
theorem markScale_poly_bound {μ : PMF ℕ} {θ : ℝ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hDA : ∃ a, StableDomain μ θ a) {A : Set ℕ} (hA : μ.toMeasure A ≠ 0) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ n : ℕ in atTop, markScale μ A θ n ≤ K * (n : ℝ) ^ 2 := by
  have hm : 0 < (μ.toMeasure A).toReal := ENNReal.toReal_pos hA (measure_ne_top _ _)
  have hcan := isRealStableAttracted_norming hc hne hDA
  obtain ⟨C, hC, hb⟩ := LeafLimits.Bridge.attracted_norming_poly_bound hcan
  have hi : Tendsto (fun n : ℕ => ⌊(n : ℝ) / (μ.toMeasure A).toReal⌋₊) atTop atTop :=
    tendsto_nat_floor_atTop.comp (tendsto_natCast_atTop_atTop.atTop_div_const hm)
  refine ⟨C / (μ.toMeasure A).toReal ^ 2, by positivity, ?_⟩
  filter_upwards [hi.eventually hb] with n hn
  have hfloor : (⌊(n : ℝ) / (μ.toMeasure A).toReal⌋₊ : ℝ) ≤
      (n : ℝ) / (μ.toMeasure A).toReal := Nat.floor_le (by positivity)
  calc markScale μ A θ n ≤ C * (⌊(n : ℝ) / (μ.toMeasure A).toReal⌋₊ : ℝ) ^ 2 := hn
    _ ≤ C * ((n : ℝ) / (μ.toMeasure A).toReal) ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ hC.le
      nlinarith [Nat.cast_nonneg (α := ℝ) ⌊(n : ℝ) / (μ.toMeasure A).toReal⌋₊]
    _ = _ := by ring

/-- Exponential errors remain negligible after division by the marked conditioning mass. -/
theorem exp_div_markedMass_tendsto {μ : PMF ℕ} {θ : ℝ}
    (hc : IsCritical μ) (hne : μ 1 ≠ 1) (hDA : ∃ a, StableDomain μ θ a)
    {A : Set ℕ} (hA : μ.toMeasure A ≠ 0) {q : ℕ → ℕ}
    (hqtop : Tendsto q atTop atTop) (hq : ∀ k, ZetaAAdmissible μ A (q k))
    {C c : ℝ} (hC : 0 ≤ C) (hc' : 0 < c) :
    Tendsto (fun k => C * Real.exp (-c * q k) / markedMass μ A (q k)) atTop (𝓝 0) := by
  obtain ⟨a, ha⟩ := hDA
  obtain ⟨K, hK, hbound⟩ := markScale_poly_bound hc hne ⟨a, ha⟩ hA
  have hpoly : Tendsto (fun n : ℕ => C * K * ((n : ℝ)^3 * Real.exp (-c * n))) atTop (𝓝 0) := by
    have ht := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 3 c hc').comp tendsto_natCast_atTop_atTop
    simpa only [Function.comp_def, Real.rpow_ofNat, mul_zero] using ht.const_mul (C * K)
  have hnum : Tendsto (fun k => (q k : ℝ) * markScale μ A θ (q k) *
      (C * Real.exp (-c * q k))) atTop (𝓝 0) := by
    apply squeeze_zero' ?_ ?_ (hpoly.comp hqtop)
    · filter_upwards [(markScale_atTop hc hne ⟨a, ha⟩ hA).comp hqtop |>.eventually (eventually_gt_atTop 0)]
        with k hk
      change 0 < markScale μ A θ (q k) at hk
      exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hk.le) (mul_nonneg hC (Real.exp_pos _).le)
    · filter_upwards [hqtop.eventually hbound] with k hk
      have ht := mul_le_mul_of_nonneg_left hk (Nat.cast_nonneg (α := ℝ) (q k))
      have ht' := mul_le_mul_of_nonneg_right ht (mul_nonneg hC (Real.exp_pos (-c * q k)).le)
      dsimp only [Function.comp_def]
      convert ht' using 1
      ring
  have hD : (arithFactor μ A : ℝ) * Scalar.stableDensity θ 0 ≠ 0 := by
    apply mul_ne_zero
    · exact_mod_cast (GeneralA.Arithmetic.arithFactor_pos hc hne A).ne'
    · exact (Scalar.stableDensity_zero_pos ha.alpha_mem).ne'
  have ht := hnum.div (normalized_markedMass_tendsto hc hne ⟨a, ha⟩ hA hqtop hq) hD
  rw [zero_div] at ht
  apply ht.congr'
  filter_upwards [hqtop.eventually_ne_atTop 0,
    ((markScale_atTop hc hne ⟨a, ha⟩ hA).comp hqtop).eventually (eventually_gt_atTop 0)] with k hk hp
  change 0 < markScale μ A θ (q k) at hp
  have hq0 : (q k : ℝ) ≠ 0 := by exact_mod_cast hk
  dsimp only [Pi.div_apply]
  field_simp [hq0, hp.ne']

/-- Step A: conditional concentration at the reciprocal mark probability. -/
theorem conditional_size_concentration {μ : PMF ℕ} {θ : ℝ}
    (hc : IsCritical μ) (hne : μ 1 ≠ 1) (hDA : ∃ a, StableDomain μ θ a)
    {A : Set ℕ} (hA : μ.toMeasure A ≠ 0) {q : ℕ → ℕ}
    (hqtop : Tendsto q atTop atTop) (hq : ∀ k, ZetaAAdmissible μ A (q k))
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun k => (zetaATreeLaw μ A (q k)).toMeasure.real
      {T | ε < |(treeSize T : ℝ) / q k - 1 / (μ.toMeasure A).toReal|}) atTop (𝓝 0) := by
  obtain ⟨C, c, hC, hc', hb⟩ := joint_size_error_bound hc hne hA hε
  apply squeeze_zero' (Eventually.of_forall fun _ => measureReal_nonneg) ?_
    (exp_div_markedMass_tendsto hc hne hDA hA hqtop hq hC.le hc')
  filter_upwards [hqtop.eventually_ge_atTop 1] with k hn
  have hqR : (0 : ℝ) < q k := by exact_mod_cast hn
  have heq : {T : LocallyFinite.Tree | ε < |(treeSize T : ℝ) / q k -
      1 / (μ.toMeasure A).toReal|} =
      {T | ε * q k < |(treeSize T : ℝ) - q k / (μ.toMeasure A).toReal|} := by
    ext T
    simp only [mem_ofPred_eq]
    rw [show (treeSize T : ℝ) / q k - 1 / (μ.toMeasure A).toReal =
      ((treeSize T : ℝ) - q k / (μ.toMeasure A).toReal) / q k by field_simp,
      abs_div, abs_of_pos hqR, lt_div_iff₀ hqR]
  rw [heq, coe_zetaATreeLaw (hq k), measureReal_def,
    cond_apply (measurableSet_zetaAEvent A (q k)), ENNReal.toReal_mul, ENNReal.toReal_inv]
  change (markedMass μ A (q k))⁻¹ * _ ≤ _
  rw [← div_eq_inv_mul]
  apply div_le_div_of_nonneg_right _ (markedMass_pos (hq k)).le
  have ht := ENNReal.toReal_mono (ENNReal.ofReal_ne_top) (hb (q k) hn)
  rwa [ENNReal.toReal_ofReal (by positivity)] at ht

end BGWLeaves.GeneralAFunctional.TreeConcentration
