module

public import BGWLeaves.GeneralAInf.Defs
public import BGWLeaves.LeafConcentration.Chernoff
public import BGWLeaves.LeafMass.Arithmetic
public import Mathlib.MeasureTheory.MeasurableSpace.NCard
public import Mathlib.Probability.Distributions.Binomial
public import Mathlib.Probability.StrongLaw

/-!
# M10 provider `Forest`

Forests of `j` trees and the discrete content of 8.1(II): the marked-forest
Kemperman identities, their binomial factorization, and the exact lattice
vanishing statement.
-/

@[expose] public section

namespace BGWLeaves.GeneralAInf.Forest

open MeasureTheory Filter ProbabilityTheory
open scoped ENNReal BigOperators Topology unitInterval
open BGW BGW.StableTrees BGW.LocallyFinite BGWLeaves.StableAnalysis
open BGWLeaves.GeneralA.Marked BGWLeaves.GeneralA.MarkedLaw
open BGWLeaves.GeneralA.MarkedWalk BGWLeaves.GeneralA.Regroup
open BGWLeaves.GeneralA.MarkedTime BGWLeaves.GeneralA.MarkedSpan

noncomputable section
attribute [local instance] Classical.propDecidable

/-- The general-forest form of `markedWalk_apply_bridge`. -/
private theorem markedWalk_apply_forestBridge (w : ℕ → ℝ≥0∞) (A : Set ℕ) (j p n : ℕ) :
    markedWalk w A p n {-(j : ℤ)} =
      ∑' ω : Fin p → ℕ, (markedForestBridges A j p n).indicator
        (fun ω => ∏ i, w (ω i)) ω := by
  rw [markedWalk, Measure.sum_apply _ (measurableSet_singleton _)]
  apply tsum_congr
  intro ω
  have hs : wordSum ω = -(j : ℤ) ↔ (∑ i, ω i) + j = p := by
    simp only [wordSum, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one, ← Nat.cast_sum]
    omega
  by_cases hn : markCount A ω = n
  · have hn' := hn
    unfold markCount at hn'
    rw [ite_eq_left hn, Measure.smul_apply, smul_eq_mul]
    by_cases hsum : wordSum ω = -(j : ℤ)
    · simp [hsum, Set.indicator, markedForestBridges, hn', hs.mp hsum]
    · simp [hsum, Set.indicator, markedForestBridges, hn', mt hs.mpr hsum]
  · have hn' := hn
    unfold markCount at hn'
    simp [hn', Set.indicator, markedForestBridges, markCount]

private theorem forestAEvent_measurable (A : Set ℕ) (j p n : ℕ) :
    MeasurableSet (forestAEvent A j p n) := by
  let toLF : (Fin j → PlaneTree) → (Fin j → LocallyFinite.Tree) :=
    fun ts i => (ts i).toLocallyFinite
  let good : Set (Fin j → PlaneTree) :=
    {ts | (∑ i, (ts i).size = p) ∧ (∑ i, treeACount A (ts i) = n)}
  have hevent : forestAEvent A j p n = ⋃ ts : good, ({toLF ts.1} : Set (Fin j → LocallyFinite.Tree)) := by
    ext F
    constructor
    · rintro ⟨ts, hp, hn, rfl⟩
      exact Set.mem_iUnion.mpr ⟨⟨ts, hp, hn⟩, rfl⟩
    · intro hF
      obtain ⟨⟨ts, hp, hn⟩, rfl⟩ := Set.mem_iUnion.mp hF
      exact ⟨ts, hp, hn, rfl⟩
  rw [hevent]
  exact MeasurableSet.iUnion fun _ => measurableSet_singleton _

/-- The total marked-count law of a critical forest is its finite-forest weight series. -/
private theorem pi_bienaymeLaw_zetaA_eq_tsum {μ : PMF ℕ} (hc : IsCritical μ)
    (hne : μ 1 ≠ 1) (A : Set ℕ) (j n : ℕ) :
    (Measure.pi fun _ : Fin j => bienaymeLaw μ.toMeasure)
        {F | ∑ i, zetaA A (F i) = (n : ℕ∞)} =
      ∑' p : ℕ, forestAWeight A (fun k => μ k) j p n := by
  have hmean : (∫⁻ k : ℕ, (k : ℝ≥0∞) ∂μ.toMeasure) = 1 := by
    rw [lintegral_countable']
    simp only [PMF.toMeasure_apply_singleton μ _ (measurableSet_singleton _)]
    exact hc
  have hne' : μ.toMeasure {1} ≠ 1 := by
    simpa only [PMF.toMeasure_apply_singleton μ _ (measurableSet_singleton _)] using hne
  have hae := LocallyFinite.ae_finiteVertices_bienaymeLaw μ.toMeasure hmean.le hne'
  have hfinite : ∀ᵐ F ∂(Measure.pi fun _ : Fin j => bienaymeLaw μ.toMeasure),
      ∀ i, LocallyFinite.FiniteVertices (F i) := by
    exact ae_all_iff.2 fun _ => Measure.tendsto_eval_ae_ae.eventually hae
  have hevent : {F | ∑ i, zetaA A (F i) = (n : ℕ∞)} =ᵐ[
      Measure.pi fun _ : Fin j => bienaymeLaw μ.toMeasure]
      ⋃ p : ℕ, forestAEvent A j p n := by
    filter_upwards [hfinite] with F hF
    apply propext
    constructor
    · intro hz
      choose ts hts using fun i => (LocallyFinite.exists_toLocallyFinite_iff (F i)).2 (hF i)
      have hc : (∑ i, zetaA A (F i)) = ((∑ i, treeACount A (ts i) : ℕ) : ℕ∞) := by
        rw [Nat.cast_sum]
        apply Finset.sum_congr rfl
        intro i hi
        rw [← hts i, zetaA_toLocallyFinite]
      rw [hc] at hz
      exact Set.mem_iUnion.mpr ⟨∑ i, (ts i).size,
        ⟨ts, rfl, ENat.natCast_inj.mp hz, funext fun i => (hts i).symm⟩⟩
    · intro h
      obtain ⟨p, ts, hp, hn, rfl⟩ := Set.mem_iUnion.mp h
      change (∑ i, zetaA A ((ts i).toLocallyFinite)) = (n : ℕ∞)
      simp_rw [zetaA_toLocallyFinite]
      rw [← Nat.cast_sum, hn]
  have hdisj : Pairwise (Function.onFun Disjoint fun p : ℕ => forestAEvent A j p n) := by
    intro p q hpq
    change Disjoint (forestAEvent A j p n) (forestAEvent A j q n)
    rw [Set.disjoint_left]
    rintro F ⟨ts, hp, hn, hF⟩ ⟨us, hq, hm, hG⟩
    have hEq : (fun i => (ts i).toLocallyFinite) = (fun i => (us i).toLocallyFinite) :=
      hF.symm.trans hG
    have hts : ts = us := by
      funext i
      exact PlaneTree.toLocallyFinite_injective (congrFun hEq i)
    subst us
    exact hpq (hp.symm.trans hq)
  rw [measure_congr hevent, measure_iUnion hdisj (fun p => forestAEvent_measurable A j p n)]
  apply tsum_congr
  intro p
  rw [pi_bienaymeLaw_forestAEvent]
  simp only [PMF.toMeasure_apply_singleton μ _ (measurableSet_singleton _)]

private theorem forestAWeight_zero (w : ℕ → ℝ≥0∞) (A : Set ℕ) {j : ℕ}
    (hj : 1 ≤ j) (n : ℕ) : forestAWeight A w j 0 n = 0 := by
  rw [forestAWeight_eq_tsum_fin]
  apply ENNReal.tsum_eq_zero.mpr
  intro ts
  have hs : ∑ i, (ts i).size ≠ 0 := by
    intro hs
    let i : Fin j := ⟨0, by omega⟩
    have hi : (ts i).size = 0 := Finset.sum_eq_zero_iff.mp hs i (Finset.mem_univ i)
    exact (PlaneTree.size_pos (ts i)).ne' hi
  simp [hs]

private theorem forestAWeight_eq_walk (w : ℕ → ℝ≥0∞) (A : Set ℕ) {j : ℕ}
    (hj : 1 ≤ j) (p n : ℕ) :
    forestAWeight A w j p n = (p : ℝ≥0∞)⁻¹ * (j * markedWalk w A p n {-(j : ℤ)}) := by
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · have hj0 : j ≠ 0 := by omega
    have hjZ : -(j : ℤ) ≠ 0 := neg_ne_zero.mpr (by exact_mod_cast hj0)
    have hwalk : markedWalk w A 0 n {-(j : ℤ)} = 0 := by
      rw [markedWalk_zero]
      split_ifs with hn0
      · rw [Measure.dirac_apply' _ (measurableSet_singleton _)]
        simp [hjZ]
      · simp
    rw [forestAWeight_zero w A hj n, hwalk]
    simp
  · rw [markedWalk_apply_forestBridge, ← natCast_mul_forestAWeight A w hj p n,
      ← mul_assoc, ENNReal.inv_mul_cancel (by exact_mod_cast hp.ne') (by simp), one_mul]

/-- Forest marked-count law in unnormalized walk form. -/
private theorem pi_bienaymeLaw_zetaA_series {μ : PMF ℕ} (hc : IsCritical μ)
    (hne : μ 1 ≠ 1) (A : Set ℕ) {j : ℕ} (hj : 1 ≤ j) (n : ℕ) :
    (Measure.pi fun _ : Fin j => bienaymeLaw μ.toMeasure)
        {F | ∑ i, zetaA A (F i) = (n : ℕ∞)} =
      ∑' p : ℕ, (p : ℝ≥0∞)⁻¹ *
        (j * markedWalk (fun k => μ k) A p n {-(j : ℤ)}) := by
  rw [pi_bienaymeLaw_zetaA_eq_tsum hc hne A j n]
  apply tsum_congr
  intro p
  exact forestAWeight_eq_walk (fun k => μ k) A hj p n

private theorem choose_weight (n k : ℕ) :
    ((k + n + 1 : ℕ) : ℝ≥0∞)⁻¹ * ((k + n + 1).choose (n + 1) : ℝ≥0∞) =
      ((n + 1 : ℕ) : ℝ≥0∞)⁻¹ * ((k + n).choose n : ℝ≥0∞) := by
  have hp : ((k + n + 1 : ℕ) : ℝ≥0∞) ≠ 0 := by positivity
  have hn : ((n + 1 : ℕ) : ℝ≥0∞) ≠ 0 := by positivity
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).1
  simp only [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast]
  have h := Nat.add_one_mul_choose_eq (k + n) n
  have hr : ((k + n + 1 : ℕ) : ℝ) * ((k + n).choose n : ℝ) =
      ((k + n + 1).choose (n + 1) : ℝ) * ((n + 1 : ℕ) : ℝ) := by exact_mod_cast h
  have hpR : ((k + n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hnR : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp
  nlinarith [hr]

/-- **A-time-walk identity for forests.** -/
theorem zetaA_forest_blockLaw {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1) (A : Set ℕ)
    {j : ℕ} (hj : 1 ≤ j) {n : ℕ} (hn : 1 ≤ n) :
    (Measure.pi fun _ : Fin j => bienaymeLaw μ.toMeasure)
        {F | ∑ i, zetaA A (F i) = (n : ℕ∞)} =
      (j : ℝ≥0∞) * (n : ℝ≥0∞)⁻¹ * intWalk (blockStep μ A) n {-(j : ℤ)} := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  have : SFinite (markedStep (fun k => μ k) A) := by
    unfold markedStep weightedStep
    infer_instance
  have : SFinite (unmarkedStep (fun k => μ k) A) := by
    unfold unmarkedStep markedStep weightedStep
    infer_instance
  rw [pi_bienaymeLaw_zetaA_series hc hne A hj (m + 1)]
  let f : ℕ → ℝ≥0∞ := fun p => (p : ℝ≥0∞)⁻¹ *
    (j * markedWalk (fun k => μ k) A p (m + 1) {-(j : ℤ)})
  have hs : Function.support f ⊆ Set.range (fun k : ℕ => k + (m + 1)) := by
    intro p hp
    have hle : m + 1 ≤ p := by
      by_contra h
      apply hp
      simp [f, markedWalk_eq_zero_of_lt (fun k => μ k) A (by omega : p < m + 1)]
    exact ⟨p - (m + 1), Nat.sub_add_cancel hle⟩
  have he := (show Function.Injective (fun k : ℕ => k + (m + 1)) from
    fun _ _ h => Nat.add_right_cancel h).tsum_eq hs
  change (∑' p, f p) = _
  rw [← he, blockLaw_walk _ _ m, Measure.sum_apply _ (measurableSet_singleton _)]
  rw [← ENNReal.tsum_mul_left]
  apply tsum_congr
  intro k
  dsimp [f]
  rw [markedWalk_binomial]
  simp only [Nat.add_sub_cancel, Measure.smul_apply, smul_eq_mul]
  let W : ℝ≥0∞ := (((intWalk (markedStep (fun k => μ k) A) (m + 1)).conv
    (intWalk (unmarkedStep (fun k => μ k) A) k)) {-(j : ℤ)})
  change ((k + (m + 1) : ℕ) : ℝ≥0∞)⁻¹ *
      (j * (((k + (m + 1)).choose (m + 1) : ℝ≥0∞) * W)) =
    (j : ℝ≥0∞) * ((m + 1 : ℕ) : ℝ≥0∞)⁻¹ * (((k + m).choose m : ℝ≥0∞) * W)
  calc
    ((k + (m + 1) : ℕ) : ℝ≥0∞)⁻¹ *
        (j * (((k + (m + 1)).choose (m + 1) : ℝ≥0∞) * W)) =
      j * ((((k + (m + 1) : ℕ) : ℝ≥0∞)⁻¹ *
        ((k + (m + 1)).choose (m + 1) : ℝ≥0∞)) * W) := by ac_rfl
    _ = j * ((((m + 1 : ℕ) : ℝ≥0∞)⁻¹ * ((k + m).choose m : ℝ≥0∞)) * W) := by
      rw [show k + (m + 1) = k + m + 1 by omega, choose_weight]
    _ = (j : ℝ≥0∞) * ((m + 1 : ℕ) : ℝ≥0∞)⁻¹ *
        (((k + m).choose m : ℝ≥0∞) * W) := by ac_rfl

private theorem intWalk_smul (r : ℝ≥0∞) (ν : Measure ℤ) [IsProbabilityMeasure ν] (n : ℕ) :
    intWalk (r • ν) n = r ^ n • intWalk ν n := by
  induction n with
  | zero => simp [intWalk]
  | succ n ih =>
    rw [intWalk, ih, Measure.conv_smul_left, Measure.conv_smul_right, smul_smul, ← pow_succ]
    rfl

/-- **The generalized marked-forest factorization.** -/
theorem marked_forest_factorization {μ : PMF ℕ} (_hc : IsCritical μ) (_hne : μ 1 ≠ 1) (A : Set ℕ)
    {j p n : ℕ} (hj : 1 ≤ j) (hp : 1 ≤ p) :
    (Measure.pi fun _ : Fin j => bienaymeLaw μ.toMeasure) (forestAEvent A j p n) =
      (j : ℝ≥0∞) * (p : ℝ≥0∞)⁻¹ *
        ((p.choose n : ℝ≥0∞) * (μ.toMeasure A) ^ n * (1 - μ.toMeasure A) ^ (p - n)) *
        ((intWalk (insideMarkLaw μ A) n).conv (intWalk (outsideMarkLaw μ A) (p - n)))
          {-(j : ℤ)} := by
  let α := markedStep (fun k => μ k) A
  let β := unmarkedStep (fun k => μ k) A
  have hαfin : IsFiniteMeasure α := by
    dsimp [α]
    rw [markedStep_eq_map_restrict]
    infer_instance
  have hβfin : IsFiniteMeasure β := by
    dsimp [β, unmarkedStep]
    rw [markedStep_eq_map_restrict]
    infer_instance
  let := hαfin
  let := hβfin
  have := normalized_probability α
  have := normalized_probability β
  have hα : μ.toMeasure A • normalized α = α := by
    simpa only [α, markedStep_mass] using mass_smul_normalized α
  have hβ : (1 - μ.toMeasure A) • normalized β = β := by
    have hm : β Set.univ = 1 - μ.toMeasure A := by
      dsimp [β, unmarkedStep]
      rw [markedStep_mass, prob_compl_eq_one_sub MeasurableSet.of_discrete]
    rw [← hm]
    exact mass_smul_normalized β
  have hαwalk : intWalk α n = (μ.toMeasure A) ^ n • intWalk (normalized α) n := by
    calc
      intWalk α n = intWalk (μ.toMeasure A • normalized α) n :=
        congrArg (fun ν => intWalk ν n) hα.symm
      _ = (μ.toMeasure A) ^ n • intWalk (normalized α) n := intWalk_smul _ _ _
  have hβwalk : intWalk β (p - n) =
      (1 - μ.toMeasure A) ^ (p - n) • intWalk (normalized β) (p - n) := by
    calc
      intWalk β (p - n) = intWalk ((1 - μ.toMeasure A) • normalized β) (p - n) :=
        congrArg (fun ν => intWalk ν (p - n)) hβ.symm
      _ = (1 - μ.toMeasure A) ^ (p - n) • intWalk (normalized β) (p - n) :=
        intWalk_smul _ _ _
  have hnorm : ((intWalk α n).conv (intWalk β (p - n))) {-(j : ℤ)} =
      ((μ.toMeasure A) ^ n * (1 - μ.toMeasure A) ^ (p - n)) *
        ((intWalk (normalized α) n).conv (intWalk (normalized β) (p - n))) {-(j : ℤ)} := by
    rw [hαwalk, hβwalk, Measure.conv_smul_left, Measure.conv_smul_right]
    simp only [Measure.smul_apply, smul_eq_mul, smul_smul]
  have hp0 : (p : ℝ≥0∞) ≠ 0 := by exact_mod_cast (by omega : p ≠ 0)
  calc
    (Measure.pi fun _ : Fin j => bienaymeLaw μ.toMeasure) (forestAEvent A j p n) =
        (p : ℝ≥0∞)⁻¹ * ((p : ℝ≥0∞) *
          (Measure.pi fun _ : Fin j => bienaymeLaw μ.toMeasure) (forestAEvent A j p n)) := by
      rw [← mul_assoc, ENNReal.inv_mul_cancel hp0 (by simp), one_mul]
    _ = (p : ℝ≥0∞)⁻¹ * (j * markedWalk (fun k => μ k) A p n {-(j : ℤ)}) := by
      rw [pi_bienaymeLaw_forestAEvent]
      simp only [PMF.toMeasure_apply_singleton μ _ (measurableSet_singleton _)]
      rw [natCast_mul_forestAWeight A (fun k => μ k) hj p n,
        markedWalk_apply_forestBridge]
    _ = (j : ℝ≥0∞) * (p : ℝ≥0∞)⁻¹ * markedWalk (fun k => μ k) A p n {-(j : ℤ)} := by
      ac_rfl
    _ = (j : ℝ≥0∞) * (p : ℝ≥0∞)⁻¹ *
        ((p.choose n : ℝ≥0∞) * (μ.toMeasure A) ^ n * (1 - μ.toMeasure A) ^ (p - n)) *
        ((intWalk (insideMarkLaw μ A) n).conv (intWalk (outsideMarkLaw μ A) (p - n)))
          {-(j : ℤ)} := by
      rw [markedWalk_binomial]
      simp only [Measure.smul_apply, smul_eq_mul]
      change (j : ℝ≥0∞) * (p : ℝ≥0∞)⁻¹ *
        ((p.choose n : ℝ≥0∞) * ((intWalk α n).conv (intWalk β (p - n))) {-(j : ℤ)}) = _
      rw [hnorm]
      change _ = (j : ℝ≥0∞) * (p : ℝ≥0∞)⁻¹ *
        ((p.choose n : ℝ≥0∞) * (μ.toMeasure A) ^ n * (1 - μ.toMeasure A) ^ (p - n)) *
        ((intWalk (normalized α) n).conv (intWalk (normalized β) (p - n))) {-(j : ℤ)}
      ac_rfl

private theorem binomial_marks (m : ℝ) (hm0 : 0 < m) (hm1 : m < 1) (p n : ℕ) (_hp : 1 ≤ p) :
    (p.choose n : ℝ) * m ^ n * (1 - m) ^ (p - n) =
      (Measure.infinitePi (fun _ : ℕ => bernoulliMeasure True False ⟨m, hm0.le, hm1.le⟩)).real
        {ω | (∑ k ∈ Finset.range p, if ω k then (1 : ℝ) else 0) = n} := by
  let q : I := ⟨m, hm0.le, hm1.le⟩
  let P : Measure (ℕ → Prop) := Measure.infinitePi (fun _ : ℕ => bernoulliMeasure True False q)
  let X : ℕ → (ℕ → Prop) → ℝ := fun i ω => if ω i then 1 else 0
  let Y : Fin p → (Fin p → Prop) → ℝ := fun i ω => if ω i then 1 else 0
  let v : (Fin p → Prop) → Set (Fin p) := fun ω => {i | ω i}
  let : IsProbabilityMeasure P := by dsimp [P]; infer_instance
  have hvec : P.map (fun ω (i : Fin p) => ω (i : ℕ)) =
      Measure.pi (fun _ : Fin p => bernoulliMeasure True False q) := by
    dsimp [P]
    rw [Measure.map_infinitePi_infinitePi_of_inj Fin.val_injective, Measure.infinitePi_eq_pi]
  have hv : (Measure.pi (fun _ : Fin p => bernoulliMeasure True False q)).map v = setBer(Set.univ, q) := by
    rw [setBernoulli_eq_map, Measure.infinitePi_eq_pi]
    simp only [Set.mem_univ]
    rfl
  have hsum (ω : Fin p → Prop) : Set.ncard (v ω) = ∑ i, Y i ω := by
    classical
    rw [Set.ncard_eq_toFinset_card']
    dsimp only [v]
    change (({i | ω i} : Set (Fin p)).toFinset.card : ℝ) = _
    rw [Set.toFinset_ofPred, Finset.card_filter]
    push_cast
    rfl
  have hmap : (Measure.pi (fun _ : Fin p => bernoulliMeasure True False q)).map
      (fun ω => ∑ i, Y i ω) = ((setBer((Set.univ : Set (Fin p)), q)).map (fun s : Set (Fin p) => (Set.ncard s : ℝ))) := by
    rw [← hv, Measure.map_map (by fun_prop) (by fun_prop)]
    congr 1
    funext ω
    exact (hsum ω).symm
  have hformula := map_ncard_setBernoulli_real_singleton (u := (Set.univ : Set (Fin p)))
    Set.finite_univ q n
  have hcastformula : (((setBer((Set.univ : Set (Fin p)), q)).map (fun s : Set (Fin p) => (Set.ncard s : ℝ)))).real {(n : ℝ)} =
      (p.choose n : ℝ) * m ^ n * (1 - m) ^ (p - n) := by
    rw [map_measureReal_apply (by fun_prop) (measurableSet_singleton _)]
    have hpre : (fun s : Set (Fin p) => (Set.ncard s : ℝ)) ⁻¹' {(n : ℝ)} =
        Set.ncard ⁻¹' {n} := by ext s; simp
    rw [hpre, ← map_measureReal_apply measurable_ncard (measurableSet_singleton _)]
    simpa using hformula
  change (p.choose n : ℝ) * m ^ n * (1 - m) ^ (p - n) = P.real {ω | ∑ k ∈ Finset.range p, X k ω = n}
  simp_rw [Finset.sum_range]
  symm
  calc
    P.real {ω | ∑ i : Fin p, X (i : ℕ) ω = n} =
        (P.map (fun ω (i : Fin p) => ω (i : ℕ))).real {v | ∑ i, Y i v = n} := by
      symm
      simpa [X, Y] using
        (map_measureReal_apply (μ := P) (f := fun ω (i : Fin p) => ω (i : ℕ))
          (s := {v | ∑ i, Y i v = (n : ℝ)}) (by fun_prop) MeasurableSet.of_discrete)
    _ = (Measure.pi (fun _ : Fin p => bernoulliMeasure True False q)).real
        {v | ∑ i, Y i v = n} := by rw [hvec]
    _ = ((Measure.pi (fun _ : Fin p => bernoulliMeasure True False q)).map
        (fun v => ∑ i, Y i v)).real {(n : ℝ)} := by
      symm
      apply map_measureReal_apply (by fun_prop) (measurableSet_singleton _)
    _ = _ := by rw [hmap, hcastformula]

private theorem binomial_chernoff (m : ℝ) (hm0 : 0 < m) (hm1 : m < 1) {a : ℝ} (ha : 0 < a)
    {p n : ℕ} (hp : 1 ≤ p) :
    ((m + a < (n : ℝ) / p → (p.choose n : ℝ) * m ^ n * (1 - m) ^ (p - n) ≤
      2 * Real.exp (-(p * phiStar m (m + a)))) ∧
    ((n : ℝ) / p < m - a → (p.choose n : ℝ) * m ^ n * (1 - m) ^ (p - n) ≤
      2 * Real.exp (-(p * phiStar m (m - a))))) := by
  let q : I := ⟨m, hm0.le, hm1.le⟩
  let P : Measure (ℕ → Prop) := Measure.infinitePi (fun _ : ℕ => bernoulliMeasure True False q)
  let X : ℕ → (ℕ → Prop) → ℝ := fun i ω => if ω i then 1 else 0
  let : IsProbabilityMeasure P := by dsimp [P]; infer_instance
  have hX : ∀ i, Measurable (X i) := by
    intro i
    have hm : MeasurableSet {ω : ℕ → Prop | ω i} := by
      have ht : MeasurableSet ({True} : Set Prop) := MeasurableSet.of_discrete
      have h := (measurable_pi_apply i : Measurable (fun ω : ℕ → Prop => ω i)) ht
      convert h using 1; ext ω; simp
    change Measurable (fun ω : ℕ → Prop => if ω i then (1 : ℝ) else 0)
    exact Measurable.ite hm measurable_const measurable_const
  have hind : iIndepFun X P := by
    dsimp [X, P]
    exact iIndepFun_infinitePi (X := fun (_ : ℕ) (b : Prop) => if b then (1 : ℝ) else 0)
      (fun _ => Measurable.of_discrete)
  have heval (i : ℕ) : P.map (Function.eval i) = bernoulliMeasure True False q := by
    exact Measure.infinitePi_map_eval _ _
  have hber : ∀ i, P {ω | X i ω = 1} = ENNReal.ofReal m ∧
      P {ω | X i ω = 0} = ENNReal.ofReal (1 - m) := by
    intro i
    have h1 : P {ω | X i ω = 1} = (bernoulliMeasure True False q) {True} := by
      rw [← heval i, Measure.map_apply (measurable_pi_apply _) (measurableSet_singleton _)]
      congr 1
      ext ω
      simp [X]
    have h0 : P {ω | X i ω = 0} = (bernoulliMeasure True False q) {False} := by
      rw [← heval i, Measure.map_apply (measurable_pi_apply _) (measurableSet_singleton _)]
      congr 1
      ext ω
      simp [X]
    rw [h1, h0]
    rw [bernoulliMeasure_apply_of_mem_of_notMem q (measurableSet_singleton _) (by simp) (by simp),
      bernoulliMeasure_apply_of_notMem_of_mem q (measurableSet_singleton _) (by simp) (by simp)]
    constructor
    · symm
      change ENNReal.ofReal (unitInterval.toNNReal q).1 = ↑(unitInterval.toNNReal q)
      exact ENNReal.ofReal_coe_nnreal
    · rw [← ENNReal.ofReal_coe_nnreal]
      congr 1
  obtain ⟨hu, hl⟩ := BGWLeaves.LeafConcentration.Chernoff.lem_phi_i P hm0 hm1 X hX hind hber ha hp
  rw [binomial_marks m hm0 hm1 p n hp]
  constructor
  · intro hn
    apply le_trans (measureReal_mono ?_ (measure_ne_top _ _)) hu
    intro ω hω
    change (∑ k ∈ Finset.range p, X k ω) = n at hω
    change m + a < (∑ k ∈ Finset.range p, X k ω) / p
    rwa [hω]
  · intro hn
    apply le_trans (measureReal_mono ?_ (measure_ne_top _ _)) hl
    intro ω hω
    change (∑ k ∈ Finset.range p, X k ω) = n at hω
    change (∑ k ∈ Finset.range p, X k ω) / p < m - a
    rwa [hω]


private instance intWalk_probability (ν : Measure ℤ) [IsProbabilityMeasure ν] (n : ℕ) :
    IsProbabilityMeasure (intWalk ν n) := by
  induction n with
  | zero => simp only [intWalk]; infer_instance
  | succ n ih => simpa only [intWalk] using
      (inferInstance : IsProbabilityMeasure ((intWalk ν n).conv ν))

private theorem forest_event_le_binomial {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (A : Set ℕ) {j : ℕ} (hj : 1 ≤ j) (p n : ℕ) :
    (Measure.pi fun _ : Fin j => bienaymeLaw μ.toMeasure) (forestAEvent A j p n) ≤
      (j : ℝ≥0∞) * ((p.choose n : ℝ≥0∞) * (μ.toMeasure A) ^ n *
        (1 - μ.toMeasure A) ^ (p - n)) := by
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · have he : forestAEvent A j 0 n = ∅ := by
      ext F
      constructor
      · rintro ⟨ts, hs, hn', rfl⟩
        have hi : (ts ⟨0, by omega⟩).size = 0 :=
          Finset.sum_eq_zero_iff.mp hs ⟨0, by omega⟩ (Finset.mem_univ _)
        exact (PlaneTree.size_pos _).ne' hi
      · simp
    rw [he]
    simp
  · let α := markedStep (fun k => μ k) A
    let β := unmarkedStep (fun k => μ k) A
    have hαfin : IsFiniteMeasure α := by
      dsimp [α]
      rw [markedStep_eq_map_restrict]
      infer_instance
    have hβfin : IsFiniteMeasure β := by
      dsimp [β, unmarkedStep]
      rw [markedStep_eq_map_restrict]
      infer_instance
    let := hαfin
    let := hβfin
    let : IsProbabilityMeasure (insideMarkLaw μ A) := normalized_probability α
    let : IsProbabilityMeasure (outsideMarkLaw μ A) := normalized_probability β
    rw [marked_forest_factorization hc hne A hj hp]
    have hw : ((intWalk (insideMarkLaw μ A) n).conv
        (intWalk (outsideMarkLaw μ A) (p - n))) {-(j : ℤ)} ≤ 1 := prob_le_one
    calc
      (j : ℝ≥0∞) * (p : ℝ≥0∞)⁻¹ *
          ((p.choose n : ℝ≥0∞) * (μ.toMeasure A) ^ n * (1 - μ.toMeasure A) ^ (p - n)) *
          ((intWalk (insideMarkLaw μ A) n).conv (intWalk (outsideMarkLaw μ A) (p - n)))
            {-(j : ℤ)} ≤
        (j : ℝ≥0∞) * 1 *
          ((p.choose n : ℝ≥0∞) * (μ.toMeasure A) ^ n * (1 - μ.toMeasure A) ^ (p - n)) * 1 := by
            gcongr
            exact ENNReal.inv_le_one.mpr (by exact_mod_cast (by omega : 1 ≤ p))
      _ = _ := by simp

private theorem phiStar_pos_of_ne {m x : ℝ} (hm0 : 0 < m) (hm1 : m < 1) (hx0 : 0 < x) (hx1 : x < 1)
    (hne : x ≠ m) : 0 < phiStar m x := by
  have hr1 : m / x ≠ 1 := by
    intro h
    apply hne
    have h' := congrArg (fun y => y * x) h
    field_simp at h'
    exact h'.symm
  have hl1 := Real.log_lt_sub_one_of_pos (div_pos hm0 hx0) hr1
  have hl2 := Real.log_le_sub_one_of_pos (div_pos (sub_pos.mpr hm1) (sub_pos.mpr hx1))
  have hm1' := mul_lt_mul_of_pos_left hl1 hx0
  have hm2' := mul_le_mul_of_nonneg_left hl2 (sub_nonneg.mpr hx1.le)
  have hd1 : m / x * x = m := div_mul_cancel₀ _ hx0.ne'
  have hd2 : (1 - m) / (1 - x) * (1 - x) = 1 - m := div_mul_cancel₀ _ (sub_ne_zero.mpr (Ne.symm hx1.ne))
  rw [Real.log_div hm0.ne' hx0.ne'] at hm1'
  rw [Real.log_div (sub_ne_zero.mpr (Ne.symm hm1.ne)) (sub_ne_zero.mpr (Ne.symm hx1.ne))] at hm2'
  rw [phiStar, Real.log_div hx0.ne' hm0.ne',
    Real.log_div (sub_ne_zero.mpr (Ne.symm hx1.ne)) (sub_ne_zero.mpr (Ne.symm hm1.ne))]
  nlinarith

private theorem binomial_outside_bound {m ε : ℝ} (hm0 : 0 < m) (hm1 : m < 1)
    (hε : 0 < ε) {p n : ℕ} (hn : 1 ≤ n)
    (hout : ε * n < |(p : ℝ) - n / m|) :
    let xU := m / (1 + ε * m)
    let xL := m + min (ε * m ^ 2) ((1 - m) / 2)
    let c := min (phiStar m xU) (phiStar m xL) / 2
    (p.choose n : ℝ) * m ^ n * (1 - m) ^ (p - n) ≤
      2 * Real.exp (-c * n) * Real.exp (-c * p) := by
  let xU := m / (1 + ε * m)
  let xL := m + min (ε * m ^ 2) ((1 - m) / 2)
  let c := min (phiStar m xU) (phiStar m xL) / 2
  have hden : 0 < 1 + ε * m := by positivity
  have hxU0 : 0 < xU := div_pos hm0 hden
  have hxUm : xU < m := by
    dsimp [xU]
    rw [div_lt_iff₀ hden]
    nlinarith [mul_pos hε hm0]
  have hxU1 : xU < 1 := hxUm.trans hm1
  have hmin : 0 < min (ε * m ^ 2) ((1 - m) / 2) :=
    lt_min (by positivity) (by linarith)
  have hxLm : m < xL := by dsimp [xL]; linarith
  have hxL1 : xL < 1 := by
    have hle := min_le_right (ε * m ^ 2) ((1 - m) / 2)
    dsimp [xL]
    linarith
  have hxL0 : 0 < xL := hm0.trans hxLm
  have hφU : 0 < phiStar m xU :=
    phiStar_pos_of_ne hm0 hm1 hxU0 hxU1 hxUm.ne
  have hφL : 0 < phiStar m xL :=
    phiStar_pos_of_ne hm0 hm1 hxL0 hxL1 hxLm.ne'
  have hc : 0 < c := half_pos (lt_min hφU hφL)
  by_cases hnp : p < n
  · rw [Nat.choose_eq_zero_of_lt hnp, Nat.cast_zero, zero_mul, zero_mul]
    positivity
  · have hnp' : n ≤ p := Nat.le_of_not_gt hnp
    have hp : 1 ≤ p := hn.trans hnp'
    have hpR : (0 : ℝ) < p := by exact_mod_cast hp
    have hnR : (0 : ℝ) ≤ n := by positivity
    have hpR0 : (0 : ℝ) ≤ p := hpR.le
    have hnpR : (n : ℝ) ≤ p := by exact_mod_cast hnp'
    rw [lt_abs, or_comm] at hout
    have hmain (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) (hxm : x ≠ m)
        (hcx : 2 * c ≤ phiStar m x)
        (hb : (p.choose n : ℝ) * m ^ n * (1 - m) ^ (p - n) ≤
          2 * Real.exp (-(p * phiStar m x))) :
        (p.choose n : ℝ) * m ^ n * (1 - m) ^ (p - n) ≤
          2 * Real.exp (-c * n) * Real.exp (-c * p) := by
      apply hb.trans
      have hexp : Real.exp (-(p * phiStar m x)) ≤
          Real.exp (-c * n) * Real.exp (-c * p) := by
        rw [← Real.exp_add]
        apply Real.exp_le_exp.mpr
        have h1 := mul_le_mul_of_nonneg_left hcx hpR0
        have h2 := mul_le_mul_of_nonneg_left hnpR hc.le
        nlinarith
      nlinarith [Real.exp_pos (-(p * phiStar m x)),
        Real.exp_pos (-c * n), Real.exp_pos (-c * p)]
    rcases hout with hout | hout
    · have hpm : m * p < n * (1 - ε * m) := by
        have hmul := mul_lt_mul_of_pos_right hout hm0
        field_simp at hmul
        ring_nf at hmul ⊢
        nlinarith [hmul]
      have hmp : m * p < n := by
        have hz : 0 ≤ ε * m * n := by positivity
        nlinarith
      have hdev : (m + ε * m ^ 2) * p < n := by
        have hh := mul_le_mul_of_nonneg_left hmp.le (mul_nonneg hε.le hm0.le)
        nlinarith
      have hnpx : xL < (n : ℝ) / p := by
        apply lt_of_le_of_lt (show xL ≤ m + ε * m ^ 2 by
          dsimp [xL]
          gcongr
          exact min_le_left _ _)
        rw [lt_div_iff₀ hpR]
        exact hdev
      have ha : 0 < xL - m := sub_pos.mpr hxLm
      have hb := (binomial_chernoff m hm0 hm1 ha hp).1 (by simpa using hnpx)
      apply hmain xL hxL0 hxL1 hxLm.ne'
      · dsimp [c]
        nlinarith [min_le_right (phiStar m xU) (phiStar m xL)]
      · simpa using hb
    · have hpout : n * (1 + ε * m) < m * p := by
        have hmul := mul_lt_mul_of_pos_right hout hm0
        field_simp at hmul
        ring_nf at hmul ⊢
        nlinarith [hmul]
      have hnpx : (n : ℝ) / p < xU := by
        rw [div_lt_iff₀ hpR]
        dsimp [xU]
        rw [div_mul_eq_mul_div, lt_div_iff₀ hden]
        nlinarith
      have ha : 0 < m - xU := sub_pos.mpr hxUm
      have hb := (binomial_chernoff m hm0 hm1 ha hp).2 (by simpa using hnpx)
      apply hmain xU hxU0 hxU1 hxUm.ne
      · dsimp [c]
        nlinarith [min_le_left (phiStar m xU) (phiStar m xL)]
      · simpa using hb

/-- **The law of large numbers for the inside-mark sum. -/
theorem insideMark_LLN {μ : PMF ℕ} (hc : IsCritical μ) {A : Set ℕ} (_hA : μ.toMeasure A ≠ 0)
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => (intWalk (insideMarkLaw μ A) n).real
        {z : ℤ | ε * n < |(z : ℝ) - n * mean (insideMarkLaw μ A)|}) atTop (𝓝 0) := by
  let α := markedStep (fun k => μ k) A
  let ρ := insideMarkLaw μ A
  have hαfin : IsFiniteMeasure α := by
    dsimp [α]
    rw [markedStep_eq_map_restrict]
    infer_instance
  let := hαfin
  let : IsProbabilityMeasure ρ := normalized_probability α
  have hαle : α ≤ stepLaw μ := by
    rw [stepLaw_decomposition μ A]
    exact Measure.le_add_right le_rfl
  have hintρ : Integrable (fun z : ℤ => (z : ℝ)) ρ :=
    integrable_normalized α _ ((integrable_stepLaw hc).mono_measure hαle)
  let P : Measure (ℕ → ℤ) := Measure.infinitePi (fun _ => ρ)
  let X : ℕ → (ℕ → ℤ) → ℝ := fun i ω => (ω i : ℝ)
  let : IsProbabilityMeasure P := by dsimp [P]; infer_instance
  have hXint : Integrable (X 0) P := by
    exact (measurePreserving_eval_infinitePi (fun _ : ℕ => ρ) 0).integrable_comp_of_integrable hintρ
  have hXindep : iIndepFun X P := by
    exact iIndepFun_infinitePi (fun _ => measurable_of_countable _)
  have hXident : ∀ i, IdentDistrib (X i) (X 0) P P := by
    intro i
    refine ⟨(by fun_prop), (by fun_prop), ?_⟩
    dsimp [X, P]
    rw [show (fun ω : ℕ → ℤ => ((ω i : ℤ) : ℝ)) =
        (fun z : ℤ => (z : ℝ)) ∘ Function.eval i from rfl,
      show (fun ω : ℕ → ℤ => ((ω 0 : ℤ) : ℝ)) =
        (fun z : ℤ => (z : ℝ)) ∘ Function.eval 0 from rfl,
      ← Measure.map_map (by fun_prop) (by fun_prop),
      ← Measure.map_map (by fun_prop) (by fun_prop),
      Measure.infinitePi_map_eval, Measure.infinitePi_map_eval]
  have hstrong : ∀ᵐ ω ∂P, Tendsto
      (fun n : ℕ => (n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, X i ω) atTop (𝓝 (mean ρ)) := by
    have h := strong_law_ae X hXint (fun _ _ hij => hXindep.indepFun hij) hXident
    have hmean : (∫ ω, X 0 ω ∂P) = mean ρ := by
      change (∫ ω, ((fun z : ℤ => (z : ℝ)) (ω 0)) ∂P) = ∫ z : ℤ, (z : ℝ) ∂ρ
      calc
        _ = ∫ z : ℤ, (z : ℝ) ∂(P.map (Function.eval 0)) :=
          (integral_map (measurable_pi_apply 0).aemeasurable (by fun_prop)).symm
        _ = _ := by rw [show P.map (Function.eval 0) = ρ from
          measurePreserving_eval_infinitePi (fun _ : ℕ => ρ) 0 |>.map_eq]
    simpa only [hmean] using h
  have hmeas : ∀ n : ℕ, AEStronglyMeasurable
      (fun ω => (n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, X i ω) P := by
    intro n
    fun_prop
  have hcm := tendstoInMeasure_of_tendsto_ae hmeas hstrong
  have hbound : Tendsto (fun n : ℕ => P.real
      {ω | ε ≤ ‖(n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, X i ω - mean ρ‖}) atTop (𝓝 0) :=
    (tendstoInMeasure_iff_measureReal_norm.mp hcm) ε hε
  have hlaw (n : ℕ) : P.map (fun ω => ∑ i ∈ Finset.range n, ω i) = intWalk ρ n := by
    have hvec : P.map (fun ω (i : Fin n) => ω (i : ℕ)) = Measure.pi (fun _ : Fin n => ρ) := by
      dsimp [P]
      rw [Measure.map_infinitePi_infinitePi_of_inj Fin.val_injective, Measure.infinitePi_eq_pi]
    rw [LeafMass.Arithmetic.intWalk_eq_map_sum, ← hvec,
      Measure.map_map (by fun_prop) (by fun_prop)]
    congr 1
    funext ω
    exact (Fin.sum_univ_eq_sum_range (fun i => ω i) n).symm
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hbound
  · exact Eventually.of_forall (fun _ => measureReal_nonneg)
  · filter_upwards [eventually_ge_atTop 1] with n hn
    change (intWalk ρ n).real _ ≤ _
    rw [← hlaw n, map_measureReal_apply (by fun_prop) (MeasurableSet.of_discrete)]
    apply measureReal_mono _ (measure_ne_top _ _)
    intro ω hω
    change ε * n < |(∑ i ∈ Finset.range n, (ω i : ℤ) : ℤ) - n * mean ρ| at hω
    change ε ≤ ‖(n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, X i ω - mean ρ‖
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    rw [Real.norm_eq_abs]
    simp only [X, smul_eq_mul]
    have heq : (n : ℝ)⁻¹ * (∑ i ∈ Finset.range n, ((ω i : ℤ) : ℝ)) - mean ρ =
        (n : ℝ)⁻¹ * (((∑ i ∈ Finset.range n, (ω i : ℤ) : ℤ) : ℝ) - n * mean ρ) := by
      push_cast
      field_simp
    rw [heq, abs_mul, abs_inv, abs_of_nonneg (Nat.cast_nonneg n)]
    rw [inv_mul_eq_div, le_div_iff₀ hnR]
    exact hω.le

/-- **`eq:gen2`, the concentration step**, proved by the marked-forest
factorization and Chernoff bounds for the binomial mark count. -/
theorem eq_gen2_concentration {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1) {A : Set ℕ}
    (hA : μ.toMeasure A ≠ 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ j n : ℕ, 1 ≤ j → 1 ≤ n →
      (Measure.pi fun _ : Fin j => bienaymeLaw μ.toMeasure)
          (⋃ p ∈ {p : ℕ | ε * n < |(p : ℝ) - n / (μ.toMeasure A).toReal|}, forestAEvent A j p n) ≤
        ENNReal.ofReal (C * j * Real.exp (-c * n)) := by
  let q := μ.toMeasure A
  have hqle : q ≤ 1 := prob_le_one
  by_cases hq1 : q = 1
  · refine ⟨2, ε, by norm_num, hε, ?_⟩
    intro j n hj hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    let S : Set ℕ := {p : ℕ | ε * n < |(p : ℝ) - n / q.toReal|}
    have hzero (p : ℕ) (hp : p ∈ S) :
        (Measure.pi fun _ : Fin j => bienaymeLaw μ.toMeasure) (forestAEvent A j p n) = 0 := by
      apply le_antisymm ?_ zero_le
      apply (forest_event_le_binomial hc hne A hj p n).trans
      by_cases hpn : p = n
      · subst p
        have hf : ε * (n : ℝ) < 0 := by simpa [S, hq1] using hp
        nlinarith [mul_pos hε hnpos]
      by_cases hnp : p < n
      · simp [Nat.choose_eq_zero_of_lt hnp]
      · have hnp' : n ≤ p := Nat.le_of_not_gt hnp
        have hlt : n < p := lt_of_le_of_ne hnp' (Ne.symm hpn)
        have hq1' : μ.toMeasure A = 1 := hq1
        simp [hq1', (Nat.sub_pos_of_lt hlt).ne']
    calc
      (Measure.pi fun _ : Fin j => bienaymeLaw μ.toMeasure)
          (⋃ p ∈ S, forestAEvent A j p n) ≤
          ∑' p : S, (Measure.pi fun _ : Fin j => bienaymeLaw μ.toMeasure)
            (forestAEvent A j p n) := measure_biUnion_le _ (Set.to_countable S) _
      _ = 0 := by
        apply ENNReal.tsum_eq_zero.mpr
        intro p
        exact hzero p p.property
      _ ≤ _ := zero_le
  · have hq1' : q < 1 := lt_of_le_of_ne hqle hq1
    have hqtop : q ≠ ∞ := measure_ne_top _ _
    have hm0 : 0 < q.toReal := ENNReal.toReal_pos hA hqtop
    have hm1 : q.toReal < 1 := by
      simpa using (ENNReal.toReal_lt_toReal hqtop ENNReal.one_ne_top).2 hq1'
    let xU := q.toReal / (1 + ε * q.toReal)
    let xL := q.toReal + min (ε * q.toReal ^ 2) ((1 - q.toReal) / 2)
    let c := min (phiStar q.toReal xU) (phiStar q.toReal xL) / 2
    have hden : 0 < 1 + ε * q.toReal := by positivity
    have hxU0 : 0 < xU := div_pos hm0 hden
    have hxUm : xU < q.toReal := by
      dsimp [xU]
      rw [div_lt_iff₀ hden]
      nlinarith [mul_pos hε hm0]
    have hmin : 0 < min (ε * q.toReal ^ 2) ((1 - q.toReal) / 2) :=
      lt_min (by positivity) (by linarith)
    have hxLm : q.toReal < xL := by dsimp [xL]; linarith
    have hxL1 : xL < 1 := by
      have hle := min_le_right (ε * q.toReal ^ 2) ((1 - q.toReal) / 2)
      dsimp [xL]
      linarith
    have hφU : 0 < phiStar q.toReal xU :=
      phiStar_pos_of_ne hm0 hm1 hxU0 (hxUm.trans hm1) hxUm.ne
    have hφL : 0 < phiStar q.toReal xL :=
      phiStar_pos_of_ne hm0 hm1 (hm0.trans hxLm) hxL1 hxLm.ne'
    have hcpos : 0 < c := half_pos (lt_min hφU hφL)
    let r := Real.exp (-c)
    have hr0 : 0 < r := Real.exp_pos _
    have hr1 : r < 1 := Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hcpos)
    let C := 2 / (1 - r)
    have hC : 0 < C := div_pos (by norm_num) (sub_pos.mpr hr1)
    refine ⟨C, c, hC, hcpos, ?_⟩
    intro j n hj hn
    let S : Set ℕ := {p : ℕ | ε * n < |(p : ℝ) - n / q.toReal|}
    have hB (p : ℕ) : (p.choose n : ℝ≥0∞) * q ^ n * (1 - q) ^ (p - n) =
        ENNReal.ofReal ((p.choose n : ℝ) * q.toReal ^ n * (1 - q.toReal) ^ (p - n)) := by
      rw [← ENNReal.ofReal_toReal (by finiteness :
        (p.choose n : ℝ≥0∞) * q ^ n * (1 - q) ^ (p - n) ≠ ∞)]
      congr 1
      simp only [ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_pow,
        ENNReal.toReal_sub_of_le hqle ENNReal.one_ne_top, ENNReal.toReal_one]
    let b : ℕ → ℝ := fun p => (p.choose n : ℝ) * q.toReal ^ n * (1 - q.toReal) ^ (p - n)
    let K := (j : ℝ) * (2 * Real.exp (-c * n))
    let t : ℕ → ℝ := fun p => K * r ^ p
    have ht : Summable t := by
      exact (summable_geometric_of_lt_one hr0.le hr1).mul_left K
    calc
      (Measure.pi fun _ : Fin j => bienaymeLaw μ.toMeasure)
          (⋃ p ∈ S, forestAEvent A j p n) ≤
          ∑' p : S, (Measure.pi fun _ : Fin j => bienaymeLaw μ.toMeasure)
            (forestAEvent A j p n) := measure_biUnion_le _ (Set.to_countable S) _
      _ = ∑' p, S.indicator (fun p => (Measure.pi fun _ : Fin j => bienaymeLaw μ.toMeasure)
          (forestAEvent A j p n)) p := tsum_subtype S
        (fun p : ℕ => (Measure.pi fun _ : Fin j => bienaymeLaw μ.toMeasure)
          (forestAEvent A j p n))
      _ ≤ ∑' p, S.indicator (fun p => (j : ℝ≥0∞) *
          ((p.choose n : ℝ≥0∞) * q ^ n * (1 - q) ^ (p - n))) p := by
        apply ENNReal.tsum_le_tsum
        intro p
        by_cases hp : p ∈ S
        · simpa [hp] using forest_event_le_binomial hc hne A hj p n
        · simp [hp]
      _ = ∑' p, S.indicator (fun p => ENNReal.ofReal ((j : ℝ) * b p)) p := by
        apply tsum_congr
        intro p
        by_cases hp : p ∈ S
        · simp only [Set.indicator_of_mem hp]
          rw [hB, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
        · simp [hp]
      _ ≤ ∑' p, ENNReal.ofReal (t p) := by
        apply ENNReal.tsum_le_tsum
        intro p
        by_cases hp : p ∈ S
        · simp only [Set.indicator_of_mem hp]
          apply ENNReal.ofReal_le_ofReal
          have hb := binomial_outside_bound hm0 hm1 hε hn hp
          have hbj := mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg j)
          rw [show -c * (p : ℝ) = (p : ℝ) * (-c) by ring, Real.exp_nat_mul] at hbj
          simpa only [b, t, K, r, xU, xL, c, mul_assoc] using hbj
        · simp [hp, t]
      _ = ENNReal.ofReal (∑' p, t p) :=
        (ENNReal.ofReal_tsum_of_nonneg (fun p => by dsimp [t]; positivity) ht).symm
      _ = ENNReal.ofReal (K * (1 - r)⁻¹) := by
        congr 1
        exact tsum_mul_left.trans (congrArg (fun z => K * z) (tsum_geometric_of_lt_one hr0.le hr1))
      _ = ENNReal.ofReal (C * j * Real.exp (-c * n)) := by
        congr 1
        dsimp [C, K]
        ring

private theorem treeACount_pos_of_zero_mem (A : Set ℕ) (hA : 0 ∈ A) (t : PlaneTree) :
    1 ≤ treeACount A t := by
  by_contra hn
  have hz : treeACount A t = 0 := by omega
  have hnone : ∀ d ∈ t.degrees, d ∉ A := by
    intro d hd hdA
    have hpos : 0 < t.degrees.countP (fun k => decide (k ∈ A)) :=
      List.countP_pos_iff.mpr ⟨d, hd, by simpa using hdA⟩
    change t.degrees.countP (fun k => decide (k ∈ A)) = 0 at hz
    omega
  have hzero : 0 ∉ t.degrees := fun h => hnone 0 h hA
  have hsum := List.length_le_sum_of_one_le t.degrees (fun i hi => by
    have hne : i ≠ 0 := fun h => hzero (h ▸ hi)
    omega)
  rw [PlaneTree.length_degrees] at hsum
  have h := t.sum_degrees_add_one
  omega

/-- **The exact lattice vanishing for forests.** -/
theorem zetaA_forest_eq_zero_of_not_dvd {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1) (A : Set ℕ)
    {j n : ℕ} (hj : 1 ≤ j) (hn : ¬ ((arithFactor μ A : ℤ) ∣ (n : ℤ) - j)) :
    (Measure.pi fun _ : Fin j => bienaymeLaw μ.toMeasure)
        {F | ∑ i, zetaA A (F i) = (n : ℕ∞)} = 0 := by
  rcases Nat.eq_zero_or_pos n with rfl | hnpos
  · by_cases hA : 0 ∈ A
    · rw [pi_bienaymeLaw_zetaA_eq_tsum hc hne A j 0]
      apply ENNReal.tsum_eq_zero.mpr
      intro p
      rw [forestAWeight_eq_tsum_fin]
      apply ENNReal.tsum_eq_zero.mpr
      intro ts
      have hm : ∑ i, treeACount A (ts i) ≠ 0 := by
        intro hm
        have hi : treeACount A (ts ⟨0, by omega⟩) = 0 :=
          Finset.sum_eq_zero_iff.mp hm ⟨0, by omega⟩ (Finset.mem_univ _)
        have hp := treeACount_pos_of_zero_mem A hA (ts ⟨0, by omega⟩)
        omega
      simp [hm]
    · have hzero := LeafMass.Arithmetic.mu_zero_ne_zero hc hne
      have hd := BGWLeaves.GeneralA.Arithmetic.arithFactor_dvd hc hne (A := A)
        (s := (-1 : ℤ)) ⟨0, hzero, Or.inr ⟨hA, by simp⟩⟩
      have hd1 : (arithFactor μ A : ℤ) ∣ (1 : ℤ) := by
        simpa using dvd_neg.mp (by simpa using hd)
      have he : arithFactor μ A = 1 := Nat.dvd_one.mp (Int.natCast_dvd_natCast.mp hd1)
      exfalso
      apply hn
      simp [he]
  · rw [pi_bienaymeLaw_zetaA_eq_tsum hc hne A j n]
    apply ENNReal.tsum_eq_zero.mpr
    intro p
    rw [forestAWeight_eq_tsum_fin]
    apply ENNReal.tsum_eq_zero.mpr
    intro ts
    by_cases hcond : (∑ i, (ts i).size = p) ∧ (∑ i, treeACount A (ts i) = n)
    · rw [ite_eq_left hcond]
      by_contra hw
      have hwi : ∀ i, PlaneTree.weight (fun k => μ k) (ts i) ≠ 0 := by
        intro i
        exact (Finset.prod_ne_zero_iff.mp hw) i (Finset.mem_univ i)
      have hd : (arithFactor μ A : ℤ) ∣
          ∑ i, ((treeACount A (ts i) : ℤ) - 1) := by
        apply Finset.dvd_sum
        intro i hi
        exact arithFactor_dvd_treeACount_sub_one A hc hne (ts i) (hwi i)
      have heq : (∑ i, ((treeACount A (ts i) : ℤ) - 1)) = (n : ℤ) - j := by
        rw [Finset.sum_sub_distrib, ← Nat.cast_sum, hcond.2]
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
      exact hn (heq ▸ hd)
    · simp [hcond]

end

end BGWLeaves.GeneralAInf.Forest
