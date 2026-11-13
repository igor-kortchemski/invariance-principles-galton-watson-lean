module

public import BGWLeaves.GeneralAInf.Defs
public import BGWLeaves.GeneralAInf.BlockLocal

/-!
# Theorem 8.1(I): consequences and calibrations

Proofs of the consequences of `thm81_corrected_general` and of the calibrations:
`thm81_corrected_general_finiteVariance_iff`, `thm81_printed_form`, `thm81_pos_iff`,
`zetaA_eq_zero_of_measure_zero`, `arithFactor_univ_eq_latticeSpan`, `zetaA_univ_eq_sizeEvent`,
`zetaA_zero_eq_leafCount`.  The theorems are those stated in `BGWLeaves.GeneralAInf`; they are exported
in namespace `BGWLeaves.GeneralAInf.Asymptotic` with exactly the types stated there.

The four calibrations `zetaA_eq_zero_of_measure_zero`, `arithFactor_univ_eq_latticeSpan`,
`zetaA_univ_eq_sizeEvent` and `zetaA_zero_eq_leafCount` are proved here, together with the three
consequences `thm81_corrected_general_finiteVariance_iff`, `thm81_printed_form` and
`thm81_pos_iff` of the main theorem `BlockLocal.thm81_corrected_general`.
-/

@[expose] public section

namespace BGWLeaves.GeneralAInf.Asymptotic

open MeasureTheory ProbabilityTheory Filter Asymptotics BGW BGW.StableTrees BGW.LocallyFinite BGWLeaves
open BGWLeaves.StableAnalysis
open scoped ENNReal Topology

attribute [local instance] Classical.propDecidable

/-- The mass of a finite-tree event is the total weight of its finite plane trees. -/
private theorem bienaymeLaw_finiteTreeEvent_eq_tsum (ν : Measure ℕ) [IsProbabilityMeasure ν]
    (Q : PlaneTree → Prop) :
    LocallyFinite.bienaymeLaw ν (BGWLeaves.finiteTreeEvent Q) =
      ∑' t : PlaneTree, if Q t then PlaneTree.weight (fun d => ν {d}) t else 0 := by
  have hA : MeasurableSet (BGWLeaves.finiteTreeEvent Q) := by
    have hEq : BGWLeaves.finiteTreeEvent Q = PlaneTree.toLocallyFinite '' {t : PlaneTree | Q t} := by
      ext T
      simp only [BGWLeaves.finiteTreeEvent, Set.mem_ofPred_eq, Set.mem_image]
      constructor
      · rintro ⟨t, rfl, ht⟩
        exact ⟨t, ht, rfl⟩
      · rintro ⟨t, ht, rfl⟩
        exact ⟨t, rfl, ht⟩
    rw [hEq]
    exact (Set.to_countable _).image _ |>.measurableSet
  have hsub : BGWLeaves.finiteTreeEvent Q ⊆ {T : LocallyFinite.Tree | FiniteVertices T} := by
    rintro T ⟨t, rfl, -⟩
    exact t.finiteVertices_toLocallyFinite
  have h : LocallyFinite.bienaymeLaw ν (BGWLeaves.finiteTreeEvent Q) =
      (LocallyFinite.bienaymeLaw ν).restrict {T : LocallyFinite.Tree | FiniteVertices T}
        (BGWLeaves.finiteTreeEvent Q) := by
    rw [Measure.restrict_apply hA, Set.inter_eq_left.mpr hsub]
  rw [h, LocallyFinite.bienaymeLaw_restrict_finiteVertices, Measure.sum_apply _ hA]
  refine tsum_congr fun t => ?_
  rw [Measure.smul_apply, Measure.dirac_apply' _ hA, smul_eq_mul]
  by_cases ht : Q t
  · have hmem : t.toLocallyFinite ∈ BGWLeaves.finiteTreeEvent Q := ⟨t, rfl, ht⟩
    simp [hmem, ht]
  · have hmem : t.toLocallyFinite ∉ BGWLeaves.finiteTreeEvent Q := by
      rintro ⟨s, hs, hq⟩
      exact ht (PlaneTree.toLocallyFinite_injective hs ▸ hq)
    simp [hmem, ht]

/-- With `A = {0}`, the marked count is the leaf count. -/
private theorem treeACount_singleton_zero (t : PlaneTree) :
    GeneralA.Marked.treeACount {0} t = t.degreeCount 0 := by
  unfold GeneralA.Marked.treeACount PlaneTree.degreeCount
  rw [List.count_eq_countP]
  apply List.countP_congr
  intro k hk
  simp

/-- With `A = ℕ`, the marked count is the total size. -/
private theorem treeACount_univ (t : PlaneTree) :
    GeneralA.Marked.treeACount Set.univ t = t.size := by
  unfold GeneralA.Marked.treeACount
  rw [List.countP_congr (q := fun _ => true) (l := t.degrees) (by intro k hk; simp)]
  simp [PlaneTree.length_degrees]

/-! ## Consequences of the corrected general theorem -/

/-- The printed slowly varying denominator equals the norming denominator at positive integers. -/
private theorem hSlow_mul_rpow {μ : PMF ℕ} {θ : ℝ} {n : ℕ} (hn : 0 < n) :
    hSlow μ θ n * (n : ℝ) ^ (1 / θ + 1) = (n : ℝ) * norming (stepLaw μ) θ n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  rw [hSlow, Nat.floor_natCast, Real.rpow_add hnR, Real.rpow_one]
  have hp : (n : ℝ) ^ (1 / θ) ≠ 0 := (Real.rpow_pos_of_pos hnR _).ne'
  field_simp

/-- Every positive index on the lattice has the sequence form `e * j + 1`. -/
private theorem exists_eq_mul_add_one_of_dvd {e n : ℕ} (hn : 1 ≤ n)
    (h : (e : ℤ) ∣ (n : ℤ) - 1) : ∃ j : ℕ, n = e * j + 1 := by
  have hd : e ∣ n - 1 := by
    apply Int.natCast_dvd_natCast.mp
    simpa [Nat.cast_sub hn] using h
  obtain ⟨j, hj⟩ := hd
  exact ⟨j, by omega⟩

private theorem eventual_lattice {e : ℕ} :
    ∀ᶠ n : ℕ in atTop ⊓ 𝓟 {n : ℕ | (e : ℤ) ∣ (n : ℤ) - 1},
      (e : ℤ) ∣ (n : ℤ) - 1 :=
  (show ∀ᶠ n : ℕ in 𝓟 {n : ℕ | (e : ℤ) ∣ (n : ℤ) - 1},
      (e : ℤ) ∣ (n : ℤ) - 1 from eventually_principal.mpr fun _ h => h).filter_mono inf_le_right

/-- Reindex the normalized sequence limit along its arithmetic lattice. -/
private theorem tendsto_lattice_of_tendsto_mul_add_one {e : ℕ} (he : 0 < e)
    {f : ℕ → ℝ} {C : ℝ} (h : Tendsto (fun j : ℕ => f (e * j + 1)) atTop (𝓝 C)) :
    Tendsto f (atTop ⊓ 𝓟 {n : ℕ | (e : ℤ) ∣ (n : ℤ) - 1}) (𝓝 C) := by
  let g : ℕ → ℕ := fun n => (n - 1) / e
  have hg : Tendsto g (atTop ⊓ 𝓟 {n : ℕ | (e : ℤ) ∣ (n : ℤ) - 1}) atTop := by
    apply tendsto_atTop.2
    intro b
    have hlarge : ∀ᶠ n : ℕ in atTop ⊓ 𝓟 {n : ℕ | (e : ℤ) ∣ (n : ℤ) - 1},
        e * b + 1 ≤ n := (eventually_ge_atTop (e * b + 1)).filter_mono inf_le_left
    filter_upwards [hlarge, eventual_lattice] with n hn hd
    have hn1 : 1 ≤ n := by omega
    obtain ⟨j, hj⟩ := exists_eq_mul_add_one_of_dvd hn1 hd
    have hbj : b ≤ j := by
      have hmul : e * b ≤ e * j := by omega
      exact Nat.le_of_mul_le_mul_left hmul he
    have hdiv : (n - 1) / e = j := by rw [hj]; simp [Nat.mul_div_right, he]
    simpa [g, hdiv] using hbj
  refine (h.comp hg).congr' ?_
  filter_upwards [(eventually_ge_atTop 1).filter_mono inf_le_left, eventual_lattice] with n hn hd
  obtain ⟨j, hj⟩ := exists_eq_mul_add_one_of_dvd hn hd
  have hdiv : (n - 1) / e = j := by rw [hj]; simp [Nat.mul_div_right, he]
  dsimp [g]
  rw [hdiv, hj]

/-- Consistency of the general corrected theorem with the finite-variance local limit. -/
theorem thm81_corrected_general_finiteVariance_iff {μ : PMF ℕ} {θ : ℝ} (hc : IsCritical μ)
    (hne : μ 1 ≠ 1) (hDA : ∃ a, StableDomain μ θ a)
    (hvar : Integrable (fun z : ℤ => (z : ℝ) ^ 2) (stepLaw μ)) {A : Set ℕ}
    (hA : μ.toMeasure A ≠ 0) :
    θ = 2 ∧
      (Tendsto (fun j : ℕ =>
          ((arithFactor μ A * j + 1 : ℕ) : ℝ) * norming (stepLaw μ) θ (arithFactor μ A * j + 1) *
            zetaAProb μ A (arithFactor μ A * j + 1))
        atTop
        (𝓝 ((μ.toMeasure A).toReal ^ (1 / θ) * Scalar.stableDensity θ 0 * (arithFactor μ A : ℝ))) ↔
      Tendsto (fun j : ℕ =>
          ((arithFactor μ A * j + 1 : ℕ) : ℝ) ^ ((3 : ℝ) / 2) *
            zetaAProb μ A (arithFactor μ A * j + 1)) atTop
        (𝓝 ((arithFactor μ A : ℝ) * Real.sqrt (2 * (μ.toMeasure A).toReal) /
          (2 * Real.sqrt (variance (stepLaw μ)) * Real.sqrt Real.pi)))) := by
  obtain ⟨a, ha⟩ := hDA
  have hθ := Scalar.alpha_eq_two_of_finiteVariance ha
    (StableDomainTail.memLp_offspring_of_integrable_sq hvar)
  refine ⟨hθ, ?_⟩
  subst θ
  have hgen := (BlockLocal.thm81_corrected_general hc hne ⟨a, ha⟩ hA).2
  have hσ := DomainCriterion.variance_pos_of_integrable_sq
    (stableDomain_isStableAttracted ha) (integrable_stepLaw hc) hvar
  let N : ℕ → ℕ := fun j => arithFactor μ A * j + 1
  let c : ℝ := Real.sqrt 2 / Real.sqrt (variance (stepLaw μ))
  have hfun (j : ℕ) :
      c * ((N j : ℝ) * norming (stepLaw μ) 2 (N j) * zetaAProb μ A (N j)) =
        (N j : ℝ) ^ ((3 : ℝ) / 2) * zetaAProb μ A (N j) := by
    have hx : (0 : ℝ) < N j := by dsimp [N]; positivity
    have hσroot := (Real.sqrt_pos.2 hσ).ne'
    have htwo := (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2)).ne'
    have hpow : (N j : ℝ) ^ ((3 : ℝ) / 2) = (N j : ℝ) * Real.sqrt (N j) := by
      rw [show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num, Real.rpow_add hx,
        Real.rpow_one, ← Real.sqrt_eq_rpow]
    rw [hpow, norming_of_integrable_sq hvar, Real.sqrt_div hx.le]
    dsimp [c]
    field_simp
  have hfour : Real.sqrt (4 * Real.pi) = 2 * Real.sqrt Real.pi := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4),
      show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num, Real.sqrt_sq_eq_abs,
      abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hconst : c * ((μ.toMeasure A).toReal ^ (1 / (2 : ℝ)) * Scalar.stableDensity 2 0 *
      (arithFactor μ A : ℝ)) =
      (arithFactor μ A : ℝ) * Real.sqrt (2 * (μ.toMeasure A).toReal) /
        (2 * Real.sqrt (variance (stepLaw μ)) * Real.sqrt Real.pi) := by
    have hσroot := (Real.sqrt_pos.2 hσ).ne'
    have htwo := (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2)).ne'
    have hπroot := (Real.sqrt_pos.2 Real.pi_pos).ne'
    rw [← Real.sqrt_eq_rpow, stableDensity_two]
    simp only [gaussDensity, zero_pow (by omega : 2 ≠ 0), neg_zero, zero_div, Real.exp_zero]
    rw [hfour, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    dsimp [c]
    field_simp
  have ht := hgen.const_mul c
  change Tendsto (fun j : ℕ => c * ((N j : ℝ) * norming (stepLaw μ) 2 (N j) *
    zetaAProb μ A (N j))) atTop
    (𝓝 (c * ((μ.toMeasure A).toReal ^ (1 / (2 : ℝ)) * Scalar.stableDensity 2 0 *
      (arithFactor μ A : ℝ)))) at ht
  rw [hconst] at ht
  have hfin : Tendsto (fun j : ℕ => (N j : ℝ) ^ ((3 : ℝ) / 2) * zetaAProb μ A (N j))
      atTop (𝓝 ((arithFactor μ A : ℝ) * Real.sqrt (2 * (μ.toMeasure A).toReal) /
        (2 * Real.sqrt (variance (stepLaw μ)) * Real.sqrt Real.pi))) :=
    ht.congr' (Eventually.of_forall hfun)
  change Tendsto (fun j : ℕ => (N j : ℝ) * norming (stepLaw μ) 2 (N j) *
    zetaAProb μ A (N j)) atTop
    (𝓝 ((μ.toMeasure A).toReal ^ (1 / (2 : ℝ)) * Scalar.stableDensity 2 0 *
      (arithFactor μ A : ℝ))) at hgen
  exact iff_of_true hgen hfin

set_option linter.unusedVariables false in
/-- The corrected Theorem 8.1(I) in its printed asymptotic-equivalence form. -/
theorem thm81_printed_form {μ : PMF ℕ} {θ : ℝ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hap : Aperiodic μ) (hDA : ∃ a, StableDomain μ θ a) {A : Set ℕ} (hA : μ.toMeasure A ≠ 0)
    (hfc : ¬ Integrable (fun z : ℤ => (z : ℝ) ^ 2) (stepLaw μ) → A.Finite ∨ Aᶜ.Finite) :
    (fun n : ℕ => zetaAProb μ A n)
      ~[atTop ⊓ 𝓟 {n : ℕ | (arithFactor μ A : ℤ) ∣ (n : ℤ) - 1}]
      (fun n : ℕ => (μ.toMeasure A).toReal ^ (1 / θ) * Scalar.stableDensity θ 0 *
        (arithFactor μ A : ℝ) / (hSlow μ θ n * (n : ℝ) ^ (1 / θ + 1))) := by
  obtain ⟨a, ha⟩ := hDA
  have hθ := (stableDomain_isStableAttracted ha).alpha_mem
  have hq : 0 < (μ.toMeasure A).toReal := ENNReal.toReal_pos hA (measure_ne_top _ _)
  have he : 0 < arithFactor μ A := GeneralA.Arithmetic.arithFactor_pos hc hne A
  let C := (μ.toMeasure A).toReal ^ (1 / θ) * Scalar.stableDensity θ 0 * (arithFactor μ A : ℝ)
  have hCpos : 0 < C := mul_pos (mul_pos (Real.rpow_pos_of_pos hq _)
    (Scalar.stableDensity_zero_pos hθ)) (by exact_mod_cast he)
  let F : Filter ℕ := atTop ⊓ 𝓟 {n : ℕ | (arithFactor μ A : ℤ) ∣ (n : ℤ) - 1}
  have hmain : Tendsto (fun n : ℕ => (n : ℝ) * norming (stepLaw μ) θ n * zetaAProb μ A n)
      F (𝓝 C) := by
    apply tendsto_lattice_of_tendsto_mul_add_one he
    exact (BlockLocal.thm81_corrected_general hc hne ⟨a, ha⟩ hA).2
  have ht := hmain.div_const C
  change Tendsto (fun n : ℕ => (n : ℝ) * norming (stepLaw μ) θ n * zetaAProb μ A n / C)
    F (𝓝 (C / C)) at ht
  rw [div_self hCpos.ne'] at ht
  apply isEquivalent_of_tendsto_one
  refine ht.congr' ?_
  filter_upwards [(eventually_gt_atTop 0).filter_mono inf_le_left] with n hn
  change (n : ℝ) * norming (stepLaw μ) θ n * zetaAProb μ A n / C =
    zetaAProb μ A n / (C / (hSlow μ θ n * (n : ℝ) ^ (1 / θ + 1)))
  rw [hSlow_mul_rpow hn, div_div_eq_mul_div]
  ring

/-- Eventual positivity exactly on the arithmetic lattice of attainable indices. -/
theorem thm81_pos_iff {μ : PMF ℕ} {θ : ℝ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hDA : ∃ a, StableDomain μ θ a) {A : Set ℕ} (hA : μ.toMeasure A ≠ 0) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (bienaymeLaw μ.toMeasure {T | zetaA A T = (n : ℕ∞)} ≠ 0 ↔
        (arithFactor μ A : ℤ) ∣ (n : ℤ) - 1) := by
  obtain ⟨a, ha⟩ := hDA
  have hθ := (stableDomain_isStableAttracted ha).alpha_mem
  have hq : 0 < (μ.toMeasure A).toReal := ENNReal.toReal_pos hA (measure_ne_top _ _)
  have he : 0 < arithFactor μ A := GeneralA.Arithmetic.arithFactor_pos hc hne A
  let C := (μ.toMeasure A).toReal ^ (1 / θ) * Scalar.stableDensity θ 0 * (arithFactor μ A : ℝ)
  have hCpos : 0 < C := mul_pos (mul_pos (Real.rpow_pos_of_pos hq _)
    (Scalar.stableDensity_zero_pos hθ)) (by exact_mod_cast he)
  have ht := (BlockLocal.thm81_corrected_general hc hne ⟨a, ha⟩ hA).2
  change Tendsto (fun j : ℕ =>
      ((arithFactor μ A * j + 1 : ℕ) : ℝ) * norming (stepLaw μ) θ (arithFactor μ A * j + 1) *
        zetaAProb μ A (arithFactor μ A * j + 1)) atTop (𝓝 C) at ht
  have hev := (Metric.tendsto_nhds.1 ht) (C / 2) (half_pos hCpos)
  obtain ⟨J, hJ⟩ := eventually_atTop.1 hev
  refine ⟨arithFactor μ A * J + 1, fun n hn => ?_⟩
  let hgeneral := BlockLocal.thm81_corrected_general hc hne ⟨a, ha⟩ hA
  constructor
  · intro hpos
    by_contra hd
    exact hpos (hgeneral.1 n hd)
  · intro hd hzero
    have hn1 : 1 ≤ n := by omega
    obtain ⟨j, rfl⟩ := exists_eq_mul_add_one_of_dvd hn1 hd
    have hJj : J ≤ j := by
      have hmul : arithFactor μ A * J ≤ arithFactor μ A * j := by omega
      exact Nat.le_of_mul_le_mul_left hmul he
    have hbound := hJ j hJj
    have hreal : zetaAProb μ A (arithFactor μ A * j + 1) = 0 := by
      change (bienaymeLaw μ.toMeasure
        {T | zetaA A T = ((arithFactor μ A * j + 1 : ℕ) : ℕ∞)}).toReal = 0
      exact (measureReal_eq_zero_iff (measure_ne_top _ _)).2 hzero
    rw [hreal, mul_zero, Real.dist_eq, zero_sub, abs_neg, abs_of_pos hCpos] at hbound
    linarith


/-- Edge case `A ≠ ∅` but `μ(A) = 0` (the printed hypothesis "non-empty" does not exclude it): `ζ_A = 0`
almost surely, so `P[ζ_A = n] = 0` for every `n ≥ 1` and the printed statement is vacuous (there is no
`n` with positive probability; the printed constant would be `0^{1/θ} = 0`). -/
theorem zetaA_eq_zero_of_measure_zero {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1) {A : Set ℕ}
    (hA : μ.toMeasure A = 0) {n : ℕ} (hn : 1 ≤ n) :
    bienaymeLaw μ.toMeasure {T | zetaA A T = (n : ℕ∞)} = 0 := by
  rw [GeneralA.MarkedLaw.bienaymeLaw_zetaA_eq_tsum A hc hne n, ENNReal.tsum_eq_zero]
  intro t
  by_cases ht : GeneralA.Marked.treeACount A t = n
  · rw [ite_eq_left ht]
    by_contra hw
    have hforall := (PlaneTree.weight_ne_zero_iff (fun k => μ k) t).1 hw
    have hpos : 0 < GeneralA.Marked.treeACount A t := by rw [ht]; omega
    have hmem : ∃ k, k ∈ t.degrees ∧ k ∈ A := by
      rw [GeneralA.Marked.treeACount, List.countP_eq_length_filter] at hpos
      obtain ⟨k, hk⟩ := List.length_pos_iff_exists_mem.mp hpos
      exact ⟨k, (List.mem_filter.mp hk).1, by simpa using (List.mem_filter.mp hk).2⟩
    obtain ⟨k, hkdeg, hkA⟩ := hmem
    have hk0 := hforall k hkdeg
    have hle : μ.toMeasure {k} ≤ μ.toMeasure A :=
      measure_mono (Set.singleton_subset_iff.mpr hkA)
    rw [PMF.toMeasure_apply_singleton μ k (measurableSet_singleton k), hA] at hle
    exact hk0 (le_antisymm hle bot_le)
  · rw [ite_eq_right ht]

/-- Calibration `A = ℕ` (`ζ_A = ` total progeny, `μ(A) = 1`): `arithFactor μ ℕ = gcd supp μ`
is the lattice span `d` of Remark 1.12 (`1` for aperiodic `μ`). -/
theorem arithFactor_univ_eq_latticeSpan {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1) :
    arithFactor μ Set.univ = Scalar.latticeSpan μ := by
  have hdiv : ∀ k : ℕ, μ k ≠ 0 → ((Scalar.latticeSpan μ : ℕ) : ℤ) ∣ (k : ℤ) := by
    intro k hk
    exact Scalar.latticeSpan_dvd_of_ne_zero hc hne hk
  have hg : IsGreatest {e : ℕ | 1 ≤ e ∧ ∀ s ∈ arithSet μ Set.univ, (e : ℤ) ∣ s}
      (Scalar.latticeSpan μ) := by
    constructor
    · refine ⟨Nat.one_le_iff_ne_zero.mpr (Scalar.latticeSpan_pos hc hne).ne', ?_⟩
      intro s hs
      rcases hs with ⟨k, hk, ⟨hkA, rfl⟩ | ⟨hkA, rfl⟩⟩
      · exact hdiv k hk
      · simp at hkA
    · intro e he
      have hediv : ∀ k : ℕ, μ k ≠ 0 → (e : ℤ) ∣ (k : ℤ) := by
        intro k hk
        exact he.2 (k : ℤ) ⟨k, hk, Or.inl ⟨Set.mem_univ k, rfl⟩⟩
      have hspan : Ideal.span (Scalar.supportDiffs μ) ≤ Ideal.span {(e : ℤ)} := by
        rw [Ideal.span_le]
        rintro m ⟨i, j, hi, hj, rfl⟩
        show ((i : ℤ) - j) ∈ Ideal.span {(e : ℤ)}
        rw [Ideal.mem_span_singleton]
        exact dvd_sub (hediv i hi) (hediv j hj)
      have hgen : (e : ℤ) ∣ Submodule.IsPrincipal.generator (Ideal.span (Scalar.supportDiffs μ)) :=
        Ideal.mem_span_singleton.1 (hspan (Submodule.IsPrincipal.generator_mem _))
      have hgen' : e ∣ Scalar.latticeSpan μ := by
        rw [Scalar.latticeSpan_eq_natAbs_generator]
        exact Int.natCast_dvd.1 hgen
      exact Nat.le_of_dvd (Scalar.latticeSpan_pos hc hne) hgen'
  exact (GeneralA.Arithmetic.arithFactor_isGreatest hc hne Set.univ).unique hg

set_option linter.unusedVariables false in
/-- Calibration `A = ℕ`: `ζ_ℕ(T)` is the size of `T`; the events `{ζ_ℕ = n}` and `{ζ = n}` agree up to the
null set of infinite trees (so `thm81_corrected_general` at `A = ℕ` is Lemma 1.11 / Remark 1.12,
`sizeProb_lattice_asymp`). -/
theorem zetaA_univ_eq_sizeEvent {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1) (n : ℕ) :
    {T : LocallyFinite.Tree | zetaA Set.univ T = (n : ℕ∞)} =ᵐ[bienaymeLaw μ.toMeasure]
      sizeEvent n := by
  apply Filter.EventuallyEq.of_eq
  ext T
  simp only [Set.mem_ofPred_eq, sizeEvent, zetaA, Set.mem_univ, and_true, FiniteVertices]
  constructor
  · intro h
    have hfin : {u | Present T u}.Finite := Set.finite_of_encard_eq_coe h
    refine ⟨hfin, ?_⟩
    rw [Set.ncard_def, h]
    simp
  · rintro ⟨hfin, hn⟩
    rw [← hfin.cast_ncard_eq, hn]

/-- Calibration `A = {0}` (`ζ_A = ` number of leaves, up to the null set of infinite trees):
with it the corrected 8.1(I) is Theorem 3.1(ii) (`ltn_ii_tendsto`), `arithFactor μ {0}` being its `g`. -/
theorem zetaA_zero_eq_leafCount {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1) (n : ℕ) :
    bienaymeLaw μ.toMeasure {T | zetaA {0} T = (n : ℕ∞)} =
      bienaymeLaw μ.toMeasure (leafCountEvent n) := by
  rw [GeneralA.MarkedLaw.bienaymeLaw_zetaA_eq_tsum {0} hc hne n]
  rw [show leafCountEvent n = finiteTreeEvent (fun t : PlaneTree => t.degreeCount 0 = n) from rfl]
  rw [bienaymeLaw_finiteTreeEvent_eq_tsum]
  simp_rw [PMF.toMeasure_apply_singleton μ _ (measurableSet_singleton _)]
  refine tsum_congr fun t => ?_
  rw [treeACount_singleton_zero]

end BGWLeaves.GeneralAInf.Asymptotic
