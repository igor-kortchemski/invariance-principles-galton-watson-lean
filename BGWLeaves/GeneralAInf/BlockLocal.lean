module

public import BGWLeaves.GeneralAInf.Defs
public import BGWLeaves.GeneralAInf.BlockStable
public import BGWLeaves.GeneralAInf.Forest
public import BGWLeaves.LeafMass.YLaw
public import BGWLeaves.GeneralA.Arithmetic

/-!
# Theorem 8.1(I): the lattice local limit for the A-time walk

Proofs of the lattice local limit for the A-time walk `ν` at the point `-1`
(`LeafMass.YLaw.llt_lattice_abstract`) and of its uniform forest version: `thm81_corrected_general` (the
corrected Theorem 8.1(I)) and `eq_gen_corrected`.  The theorems are those stated in `BGWLeaves.GeneralAInf`;
they are exported in namespace `BGWLeaves.GeneralAInf.BlockLocal` with exactly the types stated there.
-/

@[expose] public section

namespace BGWLeaves.GeneralAInf.BlockLocal

/- The local-limit assembly uses block attraction proved in BlockStable.
The uniform weighted lattice estimate is converted to the forest statement by
Forest.zetaA_forest_blockLaw for positive n. -/


open MeasureTheory ProbabilityTheory Filter BGW BGW.StableTrees BGW.LocallyFinite
open BGWLeaves.StableAnalysis BGWLeaves.GeneralA
open MarkedWalk Regroup MarkedTime MarkedSpan
open scoped ENNReal Topology

/-- The local-limit assembly for a block walk with the specified stable attraction.
The additional premise is the analytic block-attraction helper, not a local-limit conclusion. -/
private theorem thm81_limit_of_block_attraction {μ : PMF ℕ} {θ : ℝ}
    (hc : IsCritical μ) (hne : μ 1 ≠ 1) (hDA : ∃ a, StableDomain μ θ a)
    {A : Set ℕ} (hA : μ.toMeasure A ≠ 0)
    (hblock : IsStableAttracted (blockStep μ A) θ 0
      (fun n : ℕ => norming (stepLaw μ) θ ⌊(n : ℝ) / (μ.toMeasure A).toReal⌋₊)) :
    (∀ n : ℕ, ¬ ((arithFactor μ A : ℤ) ∣ (n : ℤ) - 1) →
        bienaymeLaw μ.toMeasure {T | zetaA A T = n} = 0) ∧
    Tendsto (fun j : ℕ =>
        ((arithFactor μ A * j + 1 : ℕ) : ℝ) * norming (stepLaw μ) θ (arithFactor μ A * j + 1) *
          zetaAProb μ A (arithFactor μ A * j + 1)) atTop
      (𝓝 ((μ.toMeasure A).toReal ^ (1 / θ) * Scalar.stableDensity θ 0 * (arithFactor μ A : ℝ))) := by
  refine ⟨fun n hn => MarkedLaw.zetaA_eq_zero_of_not_dvd A hc hne n hn, ?_⟩
  let ν := blockStep μ A
  let b := fun n : ℕ => norming (stepLaw μ) θ ⌊(n : ℝ) / (μ.toMeasure A).toReal⌋₊
  obtain ⟨hprob, hi, hm⟩ := BlockStable.blockStep_firstMoment hc hA
  have : IsProbabilityMeasure ν := hprob
  change mean ν = 0 at hm
  have hattr : IsStableAttracted ν θ (mean ν) b := by rw [hm]; exact hblock
  have hmono : Monotone b := BlockStable.monotone_norming_floor hc hne hDA hA
  obtain ⟨hspan, hsupp⟩ := blockLaw_span hc hne hA
  have hBtop := TransformConvergence.tendsto_atTop ν hattr
  let e := arithFactor μ A
  let N : ℕ → ℕ := fun j => e * j + 1
  have he : 0 < e := Arithmetic.arithFactor_pos hc hne A
  have hNtop : Tendsto N atTop atTop :=
    tendsto_atTop_mono (fun j => by dsimp [N]; nlinarith) tendsto_id
  have herr : Tendsto (fun j : ℕ => b (N j) * intWalkProb ν (N j) (-1) -
      (e : ℝ) * Scalar.stableDensity θ ((-1 : ℝ) / b (N j))) atTop (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨K, hK⟩ := LeafMass.YLaw.llt_lattice_abstract ν hi hspan (-1) hsupp hmono hattr (half_pos hε)
    filter_upwards [hNtop.eventually (eventually_ge_atTop K)] with j hj
    have hmod : (e : ℤ) ∣ (-1 : ℤ) - (N j : ℤ) * (-1) := by
      have hd : e ∣ e * j := dvd_mul_right _ _
      convert Int.natCast_dvd_natCast.2 hd using 1; dsimp [N]; ring
    have hmod' : (arithFactor μ A : ℤ) ∣ (-1 : ℤ) - (N j : ℤ) * (-1) := hmod
    have hbound := hK (N j) hj (-1)
    simp only [hm, mul_zero, sub_zero, ite_eq_left hmod', Int.cast_neg, Int.cast_one] at hbound
    rw [Real.dist_eq, sub_zero]
    exact lt_of_le_of_lt hbound (half_lt_self hε)
  have harg : Tendsto (fun j => (-1 : ℝ) / b (N j)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (hBtop.comp hNtop)
  have hp := ((Scalar.continuous_stableDensity hattr.alpha_mem).continuousAt.tendsto.comp harg).const_mul (e : ℝ)
  have hllt := herr.add hp
  simp only [sub_add_cancel, zero_add, Function.comp_apply] at hllt
  have hid (j : ℕ) : zetaAProb μ A (N j) =
      (N j : ℝ)⁻¹ * intWalkProb ν (N j) (-1) := by
    change (bienaymeLaw μ.toMeasure {T | zetaA A T = ((e * j + 1 : ℕ) : ℕ∞)}).toReal = _
    rw [MarkedSeries.zetaA_blockLaw hc hne A (e * j), ENNReal.toReal_mul,
      ENNReal.toReal_inv, ENNReal.toReal_natCast]
    rfl
  have hratio := (BlockStable.norming_floor_ratio hc hne hDA hA).comp hNtop
  have ht := hratio.mul hllt
  have hbpos : ∀ᶠ n : ℕ in atTop, 0 < b n := eventually_atTop.2 hattr.pos
  have heq : ∀ᶠ j : ℕ in atTop,
      (norming (stepLaw μ) θ (N j) / b (N j)) *
        (b (N j) * intWalkProb ν (N j) (-1)) =
      (N j : ℝ) * norming (stepLaw μ) θ (N j) * zetaAProb μ A (N j) := by
    filter_upwards [hNtop.eventually hbpos] with j hj
    have hx : (N j : ℝ) ≠ 0 := by dsimp [N]; positivity
    rw [hid]
    field_simp [hj.ne', hx]
  have hconstant : (μ.toMeasure A).toReal ^ (1 / θ) *
      ((e : ℝ) * Scalar.stableDensity θ 0) =
      (μ.toMeasure A).toReal ^ (1 / θ) * Scalar.stableDensity θ 0 * (e : ℝ) := by ring
  rw [hconstant] at ht
  exact ht.congr' heq

/-- The uniform weighted walk estimate needed by the forest formula. This keeps
both the corrected lattice indicator and its span factor. The forest probability
bridge is applied in `eq_gen_corrected` below. -/
private theorem eq_gen_walk_of_block_attraction {μ : PMF ℕ} {θ : ℝ}
    (hc : IsCritical μ) (hne : μ 1 ≠ 1) (hDA : ∃ a, StableDomain μ θ a)
    {A : Set ℕ} (hA : μ.toMeasure A ≠ 0)
    (hblock : IsStableAttracted (blockStep μ A) θ 0
      (fun n : ℕ => norming (stepLaw μ) θ ⌊(n : ℝ) / (μ.toMeasure A).toReal⌋₊))
    {α : ℝ} (hα : 0 < α) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ j : ℕ, 1 ≤ j →
      (j : ℝ) ≤ α * norming (stepLaw μ) θ n →
      |(j : ℝ) * intWalkProb (blockStep μ A) n (-(j : ℤ)) -
          (if (arithFactor μ A : ℤ) ∣ (n : ℤ) - j then
            (arithFactor μ A : ℝ) *
              q₁ θ (j / norming (stepLaw μ) θ ⌊(n : ℝ) / (μ.toMeasure A).toReal⌋₊)
           else 0)| ≤ ε := by
  let ν := blockStep μ A
  let b := fun n : ℕ => norming (stepLaw μ) θ ⌊(n : ℝ) / (μ.toMeasure A).toReal⌋₊
  let M := (μ.toMeasure A).toReal ^ (1 / θ)
  have hM : 0 < M := Real.rpow_pos_of_pos (ENNReal.toReal_pos hA (measure_ne_top _ _)) _
  have hC : 0 < α * (M + 1) := mul_pos hα (by linarith)
  obtain ⟨hprob, hi, hm⟩ := BlockStable.blockStep_firstMoment hc hA
  have : IsProbabilityMeasure ν := hprob
  change mean ν = 0 at hm
  have hattr : IsStableAttracted ν θ (mean ν) b := by rw [hm]; exact hblock
  have hmono : Monotone b := BlockStable.monotone_norming_floor hc hne hDA hA
  obtain ⟨hspan, hsupp⟩ := blockLaw_span hc hne hA
  obtain ⟨K, hK⟩ := LeafMass.YLaw.llt_lattice_abstract ν hi hspan (-1) hsupp hmono hattr
    (div_pos hε hC)
  have hr : ∀ᶠ n : ℕ in atTop, norming (stepLaw μ) θ n / b n < M + 1 :=
    (BlockStable.norming_floor_ratio hc hne hDA hA).eventually (gt_mem_nhds (lt_add_one M))
  have hb : ∀ᶠ n : ℕ in atTop, 0 < b n := eventually_atTop.2 hattr.pos
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hr.and hb)
  refine ⟨max K N, fun n hn j hj hjbound => ?_⟩
  obtain ⟨hrn, hbn⟩ := hN n (le_trans (le_max_right _ _) hn)
  have hbound := hK n (le_trans (le_max_left _ _) hn) (-(j : ℤ))
  have hres : (-(j : ℤ)) - (n : ℤ) * (-1) = (n : ℤ) - j := by ring
  simp only [hm, mul_zero, sub_zero, hres, Int.cast_neg, Int.cast_natCast, neg_div] at hbound
  have hmult : (j : ℝ) / b n ≤ α * (M + 1) := by
    calc
      _ ≤ (α * norming (stepLaw μ) θ n) / b n :=
        div_le_div_of_nonneg_right hjbound hbn.le
      _ = α * (norming (stepLaw μ) θ n / b n) := by ring
      _ ≤ α * (M + 1) := mul_le_mul_of_nonneg_left hrn.le hα.le
  have hid : (j : ℝ) * intWalkProb ν n (-(j : ℤ)) -
      (if (arithFactor μ A : ℤ) ∣ (n : ℤ) - j then
        (arithFactor μ A : ℝ) * q₁ θ (j / b n) else 0) =
      ((j : ℝ) / b n) * (b n * intWalkProb ν n (-(j : ℤ)) -
        (if (arithFactor μ A : ℤ) ∣ (n : ℤ) - j then
          (arithFactor μ A : ℝ) * Scalar.stableDensity θ (-(j / b n)) else 0)) := by
    unfold q₁
    split_ifs <;> field_simp [hbn.ne']
    all_goals ring
  change |(j : ℝ) * intWalkProb ν n (-(j : ℤ)) -
      (if (arithFactor μ A : ℤ) ∣ (n : ℤ) - j then
        (arithFactor μ A : ℝ) * q₁ θ (j / b n) else 0)| ≤ ε
  rw [hid, abs_mul, abs_of_nonneg (div_nonneg (Nat.cast_nonneg _) hbn.le)]
  calc
    _ ≤ (α * (M + 1)) * (ε / (α * (M + 1))) :=
      mul_le_mul hmult hbound (abs_nonneg _) hC.le
    _ = ε := mul_div_cancel₀ ε hC.ne'

/-- Corrected Theorem 8.1(I), with the stable attraction supplied by the block CF argument. -/
theorem thm81_corrected_general {μ : PMF ℕ} {θ : ℝ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hDA : ∃ a, StableDomain μ θ a) {A : Set ℕ} (hA : μ.toMeasure A ≠ 0) :
    (∀ n : ℕ, ¬ ((arithFactor μ A : ℤ) ∣ (n : ℤ) - 1) →
        bienaymeLaw μ.toMeasure {T | zetaA A T = n} = 0) ∧
    Tendsto (fun j : ℕ =>
        ((arithFactor μ A * j + 1 : ℕ) : ℝ) * norming (stepLaw μ) θ (arithFactor μ A * j + 1) *
          zetaAProb μ A (arithFactor μ A * j + 1))
      atTop
      (𝓝 ((μ.toMeasure A).toReal ^ (1 / θ) * Scalar.stableDensity θ 0 * (arithFactor μ A : ℝ))) :=
  thm81_limit_of_block_attraction hc hne hDA hA
    (BlockStable.blockStep_isStableAttracted hc hne hDA hA)

/-- The corrected uniform forest local limit, including the exact lattice indicator. -/
theorem eq_gen_corrected {μ : PMF ℕ} {θ : ℝ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hDA : ∃ a, StableDomain μ θ a) {A : Set ℕ} (hA : μ.toMeasure A ≠ 0) {α : ℝ} (hα : 0 < α)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ j : ℕ, 1 ≤ j → (j : ℝ) ≤ α * norming (stepLaw μ) θ n →
      |(n : ℝ) * (Measure.pi fun _ : Fin j => bienaymeLaw μ.toMeasure).real
            {F | ∑ i, zetaA A (F i) = (n : ℕ∞)} -
          (if (arithFactor μ A : ℤ) ∣ (n : ℤ) - j then
            (arithFactor μ A : ℝ) *
              q₁ θ (j / norming (stepLaw μ) θ ⌊(n : ℝ) / (μ.toMeasure A).toReal⌋₊)
           else 0)| ≤ ε := by
  obtain ⟨N, hN⟩ := eq_gen_walk_of_block_attraction hc hne hDA hA
    (BlockStable.blockStep_isStableAttracted hc hne hDA hA) hα hε
  refine ⟨max N 1, fun n hn j hj hjbound => ?_⟩
  have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
  have hid : (n : ℝ) * (Measure.pi fun _ : Fin j => bienaymeLaw μ.toMeasure).real
      {F | ∑ i, zetaA A (F i) = (n : ℕ∞)} =
      (j : ℝ) * intWalkProb (blockStep μ A) n (-(j : ℤ)) := by
    change (n : ℝ) * ((Measure.pi fun _ : Fin j => bienaymeLaw μ.toMeasure)
      {F | ∑ i, zetaA A (F i) = (n : ℕ∞)}).toReal = _
    rw [Forest.zetaA_forest_blockLaw hc hne A hj hn1,
      ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_inv,
      ENNReal.toReal_natCast, ENNReal.toReal_natCast]
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
    field_simp
    rfl
  rw [hid]
  exact hN n (le_trans (le_max_left _ _) hn) j hj hjbound

end BGWLeaves.GeneralAInf.BlockLocal
