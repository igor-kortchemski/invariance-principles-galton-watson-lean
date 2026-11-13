module

public import BGWLeaves.LeafLimits.Defs
public import BGWLeaves.LeafLimits.ContourHeight
public import BGWLeaves.LeafLimits.Helpers
public import BGWLeaves.Coding.Norming
public import BGW.StableTrees.ExactContourClock
public import BGW.StableTrees.RealAttractionBounds
public import BGW.Probability.WeakConvergence
public import BGW.ContinuumTrees.ContourPaperTransfer
public import BGW.ContinuumTrees.LeafLawConvergence
public import BGW.MetricMeasure.RootedUnderlyingGH
public import Mathlib.Topology.ContinuousMap.SecondCountableSpace

/-!
# Gromov-Hausdorff and GHP consequences

Proofs of the GH and GHP consequences `cvG_GHP`, `cvG_GH` and
`intro_GHP_leaf` of `BGWLeaves.LeafLimits`, exported in namespace `BGWLeaves.LeafLimits.Trees` with exactly
the types stated there (`cvG_GH` uses the Borel σ-algebra of `GHSpace`, declared as LOCAL
instances `BGWLeaves.ghMeasurableSpace`, `BGWLeaves.ghBorelSpace` in `BGWLeaves.LeafLimits`; this module
declares its own local instances `borel GHSpace` and `⟨rfl⟩`, definitionally equal to those, so that
`BGWLeaves.LeafLimits` proves `cvG_GH` by `exact`).

Route (the joint Remark 5.10 `rem_changement` is NOT used).
* The contour part of Remark 5.10 (`tendsto_rescaledContour_remark`): Theorem 5.9(ii) (module
  `ContourHeight`, `thm_cvG_ii`) gives `(B_ζ/ζ) C_{2ζ·}(τ_n) → H^exc`; the amplitude ratio
  `(μ₀^{1-1/θ} B_n/n)/(B_ζ/ζ) = μ₀^{1-1/θ} (ζ/n)/(B_ζ/B_n) → μ₀^{1-1/θ} μ₀^{-1}/μ₀^{-1/θ} = 1` in
  probability (`ζ/n → 1/μ₀`, module `Helpers`, and the uniform regular variation of `B`, BGW
  `IsRealStableAttracted.uniform_ratio`, as in `BGWLeaves.MaxDegreeLimit.Jump`); Slutsky (BGW
  `tendsto_map_prodMk_of_tendsto_of_error`) and the continuity of `(f, c) ↦ c • f`.  On
  `{λ = n}`, `ζ ≥ n`, so the identity `c_n C = R · (B_ζ/ζ) C` holds almost surely for `n` large.
* The paper contour `C_{2ζ s}` of BGW (`paperContourFunction`) is `rescaledContour` at the random size
  (`rescaledContour_treeSize_eq_smul`, from BGW `paperContourFunction_eq_contourLin`).
* `cvG_GHP`: BGW `tendsto_rooted_laws_of_paperContour_remarkDivisor` with `N k = q k`,
  `B' k = B (q k)` (positive for ALL `k` after a shift of the sequence), `hsize` from
  `ζ/n → 1/μ₀`, `hNB` from `B_n/n → 0` (Potter bound, BGW `IsRealStableAttracted.potter_upper`).
* `cvG_GH`: BGW `Coding.tendsto_map_forgetToGH`.
* `intro_GHP_leaf`: BGW `LeafMeasure.tendsto_rooted_leaf_laws_of_contour_of_top`, with `hleaf` from
  `tendsto_leafIndex_discrepancy` (module `Helpers`), `hratio` from BGW `tendsto_ratio_remarkDivisor`,
  `hlim` from the paper-clock contour convergence through the BGW adapter
  `tendsto_map_contour_of_tendsto_map_paperContour`, with
  `tendsto_real_size_lt_of_ratio`.

This module does not import `BGWLeaves.LeafLimits`.
-/

@[expose] public section

namespace BGWLeaves.LeafLimits.Trees

open MeasureTheory ProbabilityTheory Filter BGW
open BGW.StableTrees BGW.LocallyFinite BGWLeaves.StableAnalysis
open scoped ENNReal NNReal Topology

/-- The Borel structure on `GHSpace` (as in `BGWLeaves.LeafLimits` and in BGW): local. -/
noncomputable local instance ghMeasurableSpace : MeasurableSpace GromovHausdorff.GHSpace :=
  borel GromovHausdorff.GHSpace

/-- The local Borel-space instance accompanying `ghMeasurableSpace`. -/
local instance ghBorelSpace : BorelSpace GromovHausdorff.GHSpace := ⟨rfl⟩

/-! ## Elementary tools -/

private theorem mu0_pos {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1) : 0 < (μ 0).toReal :=
  ENNReal.toReal_pos (hc.apply_zero_ne_zero hne) (PMF.apply_ne_top μ 0)

/-- `B_n/n → 0` for an admissible norming (Potter bound with an exponent `1/θ + ε' < 1`). -/
private theorem tendsto_norming_div_self {ν : ProbabilityMeasure ℝ} {θ : ℝ} {B : ℕ → ℝ}
    (hB : IsRealStableAttracted ν θ B) : Tendsto (fun n : ℕ => B n / n) atTop (𝓝 0) := by
  obtain ⟨hθ1, -⟩ := hB.index_mem
  have hθ0 : 0 < θ := by linarith
  have hρ1 : 1 / θ < 1 := (div_lt_one hθ0).2 hθ1
  obtain ⟨ε', hε', hγ1⟩ : ∃ ε' : ℝ, 0 < ε' ∧ 1 / θ + ε' < 1 :=
    ⟨(1 - 1 / θ) / 2, by linarith, by linarith⟩
  obtain ⟨N, hN⟩ := hB.potter_upper hε' (by norm_num : (1 : ℝ) < 2)
  obtain ⟨Np, hNp⟩ := eventually_atTop.1 hB.pos
  obtain ⟨n₀, hn₀N, hn₀p, hn₀1⟩ : ∃ n₀ : ℕ, N ≤ n₀ ∧ Np ≤ n₀ ∧ 1 ≤ n₀ :=
    ⟨max (max N Np) 1, le_trans (le_max_left _ _) (le_max_left _ _),
      le_trans (le_max_right _ _) (le_max_left _ _), le_max_right _ _⟩
  have hn₀R : (0 : ℝ) < n₀ := by exact_mod_cast hn₀1
  have hBn₀ : 0 < B n₀ := hNp _ hn₀p
  have hlim : Tendsto (fun m : ℕ => 2 * B n₀ / (n₀ : ℝ) ^ (1 / θ + ε') *
      (m : ℝ) ^ (1 / θ + ε' - 1)) atTop (𝓝 0) := by
    have h := ((tendsto_rpow_neg_atTop (show 0 < 1 - (1 / θ + ε') by linarith)).comp
      tendsto_natCast_atTop_atTop).const_mul (2 * B n₀ / (n₀ : ℝ) ^ (1 / θ + ε'))
    rw [mul_zero] at h
    refine h.congr fun m => ?_
    simp only [Function.comp_apply, neg_sub]
  refine squeeze_zero' ?_ ?_ hlim
  · filter_upwards [eventually_ge_atTop Np] with m hm
    exact div_nonneg (hNp m hm).le (Nat.cast_nonneg m)
  · filter_upwards [eventually_ge_atTop n₀] with m hm
    have hmR : (n₀ : ℝ) ≤ m := by exact_mod_cast hm
    have hm0 : (0 : ℝ) < m := lt_of_lt_of_le hn₀R hmR
    have hratio1 : 1 ≤ (m : ℝ) / n₀ := (one_le_div hn₀R).2 hmR
    have hP := hN n₀ hn₀N m (hn₀N.trans hm)
    have hmax : max (((m : ℝ) / n₀) ^ (1 / θ + ε')) (((m : ℝ) / n₀) ^ (1 / θ - ε')) =
        ((m : ℝ) / n₀) ^ (1 / θ + ε') :=
      max_eq_left (Real.rpow_le_rpow_of_exponent_le hratio1 (by linarith))
    rw [hmax] at hP
    have hBm : B m ≤ 2 * B n₀ * ((m : ℝ) ^ (1 / θ + ε') / (n₀ : ℝ) ^ (1 / θ + ε')) := by
      rw [← Real.div_rpow hm0.le hn₀R.le]
      calc B m ≤ 2 * ((m : ℝ) / n₀) ^ (1 / θ + ε') * B n₀ := (div_le_iff₀ hBn₀).1 hP
        _ = 2 * B n₀ * ((m : ℝ) / n₀) ^ (1 / θ + ε') := by ring
    have hmγ : (m : ℝ) ^ (1 / θ + ε' - 1) * m = (m : ℝ) ^ (1 / θ + ε') := by
      rw [Real.rpow_sub_one hm0.ne', div_mul_cancel₀ _ hm0.ne']
    rw [div_le_iff₀ hm0]
    calc B m ≤ 2 * B n₀ * ((m : ℝ) ^ (1 / θ + ε') / (n₀ : ℝ) ^ (1 / θ + ε')) := hBm
      _ = 2 * B n₀ / (n₀ : ℝ) ^ (1 / θ + ε') * ((m : ℝ) ^ (1 / θ + ε' - 1) * m) := by
        rw [hmγ]; ring
      _ = 2 * B n₀ / (n₀ : ℝ) ^ (1 / θ + ε') * (m : ℝ) ^ (1 / θ + ε' - 1) * m := by ring

/-- Continuous mapping for convergence in probability to constants (copy of the `ContourHeight`
helper). -/
private theorem probability_continuous_pair {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, ProbabilityMeasure (Ω n)) {X Y : ∀ n, Ω n → ℝ} {c d : ℝ}
    (hX : ∀ ε > 0, Tendsto (fun n => (P n).toMeasure.real {ω | ε < dist (X n ω) c}) atTop (𝓝 0))
    (hY : ∀ ε > 0, Tendsto (fun n => (P n).toMeasure.real {ω | ε < dist (Y n ω) d}) atTop (𝓝 0))
    {G : ℝ × ℝ → ℝ} (hG : ContinuousAt G (c, d)) :
    ∀ ε > 0, Tendsto (fun n => (P n).toMeasure.real
      {ω | ε < dist (G (X n ω, Y n ω)) (G (c, d))}) atTop (𝓝 0) := by
  intro ε hε
  obtain ⟨δ, hδ, hclose⟩ := Metric.continuousAt_iff.mp hG ε hε
  have hlim := (hX (δ / 2) (half_pos hδ)).add (hY (δ / 2) (half_pos hδ))
  simp only [zero_add] at hlim
  refine squeeze_zero (fun _ => measureReal_nonneg) (fun n => ?_) hlim
  apply (measureReal_mono (s₂ := {ω | δ / 2 < dist (X n ω) c} ∪
    {ω | δ / 2 < dist (Y n ω) d}) ?_).trans (measureReal_union_le _ _)
  intro ω hω
  by_contra hout
  have hx : dist (X n ω) c ≤ δ / 2 := le_of_not_gt (fun h => hout (Or.inl h))
  have hy : dist (Y n ω) d ≤ δ / 2 := le_of_not_gt (fun h => hout (Or.inr h))
  have hp : dist (X n ω, Y n ω) (c, d) < δ := by
    rw [Prod.dist_eq]
    exact max_lt (hx.trans_lt (half_lt_self hδ)) (hy.trans_lt (half_lt_self hδ))
  exact (not_lt_of_ge (hclose hp).le) hω

/-- Regular variation of the norming in probability: if `M/q_n → c > 0` in probability, then
`B_M/B_{q_n} → c^{1/θ}` in probability (copy of the `Jump` helper; BGW
`IsRealStableAttracted.uniform_ratio`). -/
private theorem tendsto_norming_ratio_prob {Ω : Type*} [MeasurableSpace Ω]
    {ν : ProbabilityMeasure ℝ} {θ : ℝ} {B : ℕ → ℝ}
    (hB : IsRealStableAttracted ν θ B) {P : ℕ → ProbabilityMeasure Ω}
    {q : ℕ → ℕ} (hq : Tendsto q atTop atTop) (M : Ω → ℕ) {c : ℝ} (hc : 0 < c)
    (hM : ∀ ε > 0, Tendsto (fun n => (P n).toMeasure.real {ω | ε < |(M ω : ℝ) / q n - c|})
      atTop (𝓝 0)) :
    ∀ ε > 0, Tendsto (fun n => (P n).toMeasure.real
      {ω | ε < |B (M ω) / B (q n) - c ^ (1 / θ)|}) atTop (𝓝 0) := by
  intro ε hε
  obtain ⟨δ, hδ, hlocal⟩ := Metric.continuousAt_iff.mp
    (Real.continuousAt_rpow_const c (1 / θ) (Or.inl hc.ne')) (ε / 2) (half_pos hε)
  let d := min (c / 2) (min 1 (δ / 2))
  have hd : 0 < d := lt_min (half_pos hc) (lt_min zero_lt_one (half_pos hδ))
  obtain ⟨N, hN⟩ := hB.uniform_ratio (show 0 < c / 2 by positivity)
    (show c / 2 ≤ c + 1 by linarith) (ε / 2) (half_pos hε)
  apply squeeze_zero' (Eventually.of_forall fun _ => measureReal_nonneg) _ (hM d hd)
  filter_upwards [hq.eventually_ge_atTop N] with n hn
  refine measureReal_mono ?_
  intro ω hω
  have hω' : ε < |B (M ω) / B (q n) - c ^ (1 / θ)| := hω
  change d < |(M ω : ℝ) / q n - c|
  by_contra h
  have habs : |(M ω : ℝ) / q n - c| ≤ d := not_lt.mp h
  have hlow : c / 2 * q n ≤ (M ω : ℝ) := by
    have h := (abs_le.mp habs).1
    have hdle : d ≤ c / 2 := min_le_left _ _
    by_cases hqzero : q n = 0
    · simp [hqzero]
    · have : (0 : ℝ) < q n := by exact_mod_cast Nat.pos_of_ne_zero hqzero
      apply (le_div_iff₀ this).mp
      linarith
  have hhigh : (M ω : ℝ) ≤ (c + 1) * q n := by
    have h := (abs_le.mp habs).2
    have hdle : d ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
    by_cases hqzero : q n = 0
    · have : c ≤ d := by simpa [hqzero, abs_of_pos hc] using habs
      have : d ≤ c / 2 := min_le_left _ _
      linarith
    · have : (0 : ℝ) < q n := by exact_mod_cast Nat.pos_of_ne_zero hqzero
      apply (div_le_iff₀ this).mp
      linarith
  have happrox := hN (q n) hn (M ω) hlow hhigh
  have hrpow : |((M ω : ℝ) / q n) ^ (1 / θ) - c ^ (1 / θ)| < ε / 2 := by
    apply hlocal
    exact habs.trans_lt (lt_of_le_of_lt ((min_le_right _ _).trans (min_le_right _ _))
      (half_lt_self hδ))
  have hh := abs_sub_le (B (M ω) / B (q n)) (((M ω : ℝ) / q n) ^ (1 / θ)) (c ^ (1 / θ))
  linarith

/-- Under `P_μ[· | λ = n]` (admissible `n`), the tree is almost surely a finite tree with `n` leaves. -/
private theorem ae_mem_leafCountEvent {μ : PMF ℕ} {n : ℕ} (hn : LeafAdmissible μ n) :
    ∀ᵐ τ ∂(leafTreeLaw μ n : Measure LocallyFinite.Tree), τ ∈ leafCountEvent n := by
  rw [coe_leafTreeLaw hn]
  exact ae_cond_mem (measurableSet_leafCountEvent n)

/-- Monotonicity of a conditional probability through the conditioning event. -/
private theorem cond_real_le_of_inter_subset {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] {L E F : Set Ω} (hL : MeasurableSet L) (h : L ∩ E ⊆ F) :
    (P[|L]).real E ≤ (P[|L]).real F := by
  have hm : P (L ∩ E) ≤ P (L ∩ F) := measure_mono (Set.subset_inter Set.inter_subset_left h)
  have hle : P[|L] E ≤ P[|L] F := by
    rw [cond_apply hL, cond_apply hL]
    gcongr
  exact ENNReal.toReal_mono (measure_ne_top _ _) hle

/-! ## The paper contour and the rescaled contour -/

/-- `a C_{2ζ t}(τ)` (`rescaledContour` at the random size) is `a` times BGW's paper-clock contour of the
plane tree of `τ`, for every tree (both vanish on an infinite tree). -/
theorem rescaledContour_treeSize_eq_smul (a : ℝ) (τ : LocallyFinite.Tree) :
    rescaledContour (treeSize τ) a τ = a • (toPlaneTree τ).paperContourFunction := by
  ext s
  rw [ContinuousMap.smul_apply, smul_eq_mul, PlaneTree.paperContourFunction_eq_contourLin]
  by_cases hτ : FiniteVertices τ
  · obtain ⟨t, rfl⟩ := (exists_toLocallyFinite_iff τ).2 hτ
    change a * ExactContour.treeContourLin t.toLocallyFinite
      (2 * (treeSize t.toLocallyFinite : ℝ) * (s : ℝ)) = _
    rw [ExactContour.treeContourLin_toLocallyFinite, treeSize_toLocallyFinite,
      toPlaneTree_toLocallyFinite]
  · rw [rescaledContour_apply_of_not_finiteVertices hτ, toPlaneTree_of_not_finiteVertices hτ,
      PlaneTree.contourLin_of_end_le, mul_zero]
    have h1 : (PlaneTree.node []).size = 1 := by simp
    rw [h1]
    norm_num
    linarith [s.2.1]

/-! ## The contour part of Remark 5.10 -/

/-- **Remark 5.10, contour coordinate**: under `P_μ[· | λ = n]`, along admissible `q k`,
`(μ₀^{1-1/θ} B_n/n) C_{2ζt}(τ_n) → H^exc` in law on `C([0,1])`.  From Theorem 5.9(ii) (`thm_cvG_ii`), the
ratio of the amplitudes in probability and Slutsky. -/
theorem tendsto_rescaledContour_remark {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ} (hc : IsCritical μ)
    (hne : μ 1 ≠ 1) (hap : Aperiodic μ) (hB : IsRealStableAttracted (realOffspringStepLaw μ) θ B)
    (hnl : ¬ IsLatticeLaw (etaLaw μ)) {q : ℕ → ℕ}
    (hqtop : Tendsto q atTop atTop) (hq : ∀ k, LeafAdmissible μ (q k)) :
    Tendsto (fun k => (leafTreeLaw μ (q k)).map (fun τ => rescaledContour (treeSize τ)
        ((μ 0).toReal ^ (1 - 1 / θ) * B (q k) / q k) τ))
      atTop (𝓝 ((excLaw θ).map Prod.snd)) := by
  have hp : 0 < (μ 0).toReal := mu0_pos hc hne
  let P : ℕ → ProbabilityMeasure LocallyFinite.Tree := fun k => leafTreeLaw μ (q k)
  let X : LocallyFinite.Tree → C(Set.Icc (0 : ℝ) 1, ℝ) := fun τ =>
    rescaledContour (treeSize τ) (B (treeSize τ) / treeSize τ) τ
  have hX : Measurable X := measurable_rescaledContour_treeSize (fun m => B m / m)
  -- Theorem 5.9(ii), contour coordinate.
  have hlimX : Tendsto (fun k => (P k).map X) atTop (𝓝 ((excLaw θ).map Prod.snd)) := by
    have h := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _
      (ContourHeight.thm_cvG_ii hc hne hap hB hnl hqtop hq) continuous_fst
    have hL : ((excLaw θ).map (fun p => (p.2, p.2))).map Prod.fst = (excLaw θ).map Prod.snd := by
      apply ProbabilityMeasure.toMeasure_injective
      simp only [ProbabilityMeasure.toMeasure_map]
      rw [Measure.map_map measurable_fst (measurable_snd.prodMk measurable_snd)]
      rfl
    rw [hL] at h
    refine h.congr fun k => ?_
    apply ProbabilityMeasure.toMeasure_injective
    simp only [ProbabilityMeasure.toMeasure_map]
    rw [Measure.map_map measurable_fst (show Measurable (fun τ => (codingTriple B τ).2) from
      measurable_snd.comp (measurable_codingTriple B))]
    rfl
  -- The amplitude ratio `R = μ₀^{1-1/θ} (ζ/n)/(B_ζ/B_n) → 1` in probability.
  have hDA := (BGWLeaves.Coding.Norming.stableDomain_of_isRealStableAttracted hc hne hB).1
  have hsizeP : ∀ ε > 0, Tendsto (fun k => (P k).toMeasure.real
      {τ | ε < dist ((treeSize τ : ℝ) / q k) (1 / (μ 0).toReal)}) atTop (𝓝 0) := by
    intro ε hε
    simp only [Real.dist_eq]
    exact LeafLimits.Helpers.tendsto_treeSize_div_leaf hc hne hap hDA hqtop hq hε
  have hnormP : ∀ ε > 0, Tendsto (fun k => (P k).toMeasure.real
      {τ | ε < dist (B (treeSize τ) / B (q k)) ((1 / (μ 0).toReal) ^ (1 / θ))}) atTop (𝓝 0) := by
    intro ε hε
    simp only [Real.dist_eq]
    exact tendsto_norming_ratio_prob hB (P := P) hqtop treeSize (one_div_pos.mpr hp)
      (fun ε hε => LeafLimits.Helpers.tendsto_treeSize_div_leaf hc hne hap hDA hqtop hq hε) ε hε
  let G : ℝ × ℝ → ℝ := fun p => (μ 0).toReal ^ (1 - 1 / θ) * p.1 / p.2
  have hd0 : (1 / (μ 0).toReal) ^ (1 / θ) ≠ 0 :=
    (Real.rpow_pos_of_pos (one_div_pos.mpr hp) _).ne'
  have hGc : ContinuousAt G (1 / (μ 0).toReal, (1 / (μ 0).toReal) ^ (1 / θ)) :=
    ((continuous_const.mul continuous_fst).continuousAt).div continuous_snd.continuousAt hd0
  have hG1 : G (1 / (μ 0).toReal, (1 / (μ 0).toReal) ^ (1 / θ)) = 1 := by
    have hr : (μ 0).toReal ^ (1 / θ) ≠ 0 := (Real.rpow_pos_of_pos hp _).ne'
    have hp' : (μ 0).toReal ≠ 0 := hp.ne'
    simp only [G]
    rw [Real.div_rpow zero_le_one hp.le, Real.one_rpow, Real.rpow_sub hp, Real.rpow_one]
    field_simp
  let R : ℕ → LocallyFinite.Tree → ℝ := fun k τ =>
    G ((treeSize τ : ℝ) / q k, B (treeSize τ) / B (q k))
  have hR : ∀ k, Measurable (R k) := fun k =>
    (measurable_from_nat (f := fun m : ℕ => G ((m : ℝ) / q k, B m / B (q k)))).comp
      measurable_treeSize
  have herrR : ∀ ε > 0, Tendsto (fun k => (P k : Measure LocallyFinite.Tree).real
      {τ | ε < dist (R k τ) 1}) atTop (𝓝 0) := by
    have h := probability_continuous_pair (Ω := fun _ => LocallyFinite.Tree) P
      (X := fun k τ => (treeSize τ : ℝ) / q k) (Y := fun k τ => B (treeSize τ) / B (q k))
      hsizeP hnormP hGc
    rw [hG1] at h
    exact h
  -- Slutsky, then the continuous map `(f, c) ↦ c • f`.
  have hprod := BGW.Probability.tendsto_map_prodMk_of_tendsto_of_error
    (Ω := fun _ => LocallyFinite.Tree) P (X := fun _ => X) (Y := R) (fun _ => hX) hR hlimX herrR
  let H : C(Set.Icc (0 : ℝ) 1, ℝ) × ℝ → C(Set.Icc (0 : ℝ) 1, ℝ) := fun p => p.2 • p.1
  have hH : Continuous H := continuous_snd.smul continuous_fst
  have hlimRX : Tendsto (fun k => (P k).map (fun τ => R k τ • X τ)) atTop
      (𝓝 ((excLaw θ).map Prod.snd)) := by
    have hL : (((excLaw θ).map Prod.snd).map (fun x => (x, (1 : ℝ)))).map H =
        (excLaw θ).map Prod.snd := by
      apply ProbabilityMeasure.toMeasure_injective
      simp only [ProbabilityMeasure.toMeasure_map]
      rw [Measure.map_map hH.measurable (show Measurable fun x : C(Set.Icc (0 : ℝ) 1, ℝ) =>
        (x, (1 : ℝ)) from measurable_id.prodMk measurable_const)]
      have hid : (H ∘ fun x : C(Set.Icc (0 : ℝ) 1, ℝ) => (x, (1 : ℝ))) = id := by
        funext x
        simp [H]
      rw [hid, Measure.map_id]
    rw [← hL]
    refine (ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _ hprod hH).congr
      fun k => ?_
    apply ProbabilityMeasure.toMeasure_injective
    simp only [ProbabilityMeasure.toMeasure_map]
    rw [Measure.map_map hH.measurable (hX.prodMk (hR k))]
    rfl
  -- For `n` large, `R • X` is the deterministic-amplitude contour almost surely (`ζ ≥ λ = n`).
  refine hlimRX.congr' ?_
  obtain ⟨Np, hNp⟩ := eventually_atTop.1 hB.pos
  filter_upwards [hqtop.eventually_ge_atTop (max Np 1)] with k hk
  apply ProbabilityMeasure.toMeasure_injective
  simp only [ProbabilityMeasure.toMeasure_map]
  apply Measure.map_congr
  filter_upwards [ae_mem_leafCountEvent (hq k)] with τ hτ
  obtain ⟨t, rfl, ht⟩ := hτ
  have hsize : q k ≤ treeSize t.toLocallyFinite := by
    rw [treeSize_toLocallyFinite]
    exact ht ▸ t.degreeCount_le_size 0
  have hqk1 : 1 ≤ q k := (le_max_right _ _).trans hk
  have hz : (treeSize t.toLocallyFinite : ℝ) ≠ 0 := by
    have : 0 < treeSize t.toLocallyFinite := hqk1.trans hsize
    exact_mod_cast this.ne'
  have hBz : B (treeSize t.toLocallyFinite) ≠ 0 :=
    (hNp _ (((le_max_left _ _).trans hk).trans hsize)).ne'
  have hBq : B (q k) ≠ 0 := (hNp _ ((le_max_left _ _).trans hk)).ne'
  have hq0 : (q k : ℝ) ≠ 0 := by exact_mod_cast (show q k ≠ 0 by omega)
  simp only [X, R, G, rescaledContour_treeSize_eq_smul, smul_smul]
  congr 1
  field_simp

/-! ## Rescaled trees: the adapters to BGW's GHP convergence theorems -/

/-- The inverse of BGW's divisor of Remark 5.10 is the amplitude `μ₀^{1-1/θ} B_n/n`. -/
private theorem inv_remarkDivisor (μ₀ θ : ℝ) (q : ℕ → ℕ) (B : ℕ → ℝ) (k : ℕ) :
    (ContinuumTrees.FiniteTree.remarkDivisor μ₀ θ q (fun k => B (q k)) k)⁻¹ =
      μ₀ ^ (1 - 1 / θ) * B (q k) / q k := by
  rw [ContinuumTrees.FiniteTree.remarkDivisor, inv_div]

private theorem remark_pos {μ₀ θ : ℝ} (hμ₀ : 0 < μ₀) {q : ℕ → ℕ} {B : ℕ → ℝ}
    (hq1 : ∀ k, 0 < q k) (hBq : ∀ k, 0 < B (q k)) (k : ℕ) :
    0 < μ₀ ^ (1 - 1 / θ) * B (q k) / q k :=
  div_pos (mul_pos (Real.rpow_pos_of_pos hμ₀ _) (hBq k)) (by exact_mod_cast hq1 k)

private theorem scale_congr {x y : ℝ} (hxy : x = y) (hx : 0 < x) (hy : 0 < y)
    (X : MetricMeasure.RootedMeasuredGHSpace) :
    MetricMeasure.RootedMeasuredGHSpace.scale x hx X =
      MetricMeasure.RootedMeasuredGHSpace.scale y hy X := by
  subst hxy
  rfl

/-- A shift of the sequence makes `q` and `B ∘ q` positive at every index. -/
private theorem exists_shift {ν : ProbabilityMeasure ℝ} {θ : ℝ} {B : ℕ → ℝ}
    (hB : IsRealStableAttracted ν θ B) {q : ℕ → ℕ} (hqtop : Tendsto q atTop atTop) :
    ∃ K0 : ℕ, ∀ k, 0 < q (k + K0) ∧ 0 < B (q (k + K0)) := by
  obtain ⟨K0, hK0⟩ := eventually_atTop.1 (hqtop.eventually ((eventually_ge_atTop 1).and hB.pos))
  exact ⟨K0, fun k => hK0 (k + K0) (Nat.le_add_left _ _)⟩

/-- Lower tail of the size (hypothesis `hsize` of BGW `tendsto_rooted_laws_of_paperContour_remarkDivisor`): `P(ζ < c n) → 0` for `c < 1/μ₀`. -/
private theorem tendsto_size_lt {μ : PMF ℕ} {θ : ℝ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hap : Aperiodic μ) (hDA : ∃ a, StableDomain μ θ a) {q : ℕ → ℕ}
    (hqtop : Tendsto q atTop atTop) (hq : ∀ k, LeafAdmissible μ (q k)) (hq1 : ∀ k, 0 < q k)
    (c : ℝ) (_hc0 : 0 < c) (hc1 : c < 1 / (μ 0).toReal) :
    Tendsto (fun k => (leafTreeLaw μ (q k) : Measure LocallyFinite.Tree).real
      {τ | ((toPlaneTree τ).size : ℝ) < c * (q k : ℝ)}) atTop (𝓝 0) := by
  have h := LeafLimits.Helpers.tendsto_treeSize_div_leaf hc hne hap hDA hqtop hq (sub_pos.2 hc1)
  refine squeeze_zero (fun _ => measureReal_nonneg) (fun k => ?_) h
  rw [coe_leafTreeLaw (hq k)]
  apply cond_real_le_of_inter_subset (measurableSet_leafCountEvent (q k))
  rintro τ ⟨⟨t, rfl, -⟩, hE⟩
  have hE' : (t.size : ℝ) < c * q k := by simpa [toPlaneTree_toLocallyFinite] using hE
  show 1 / (μ 0).toReal - c < |(treeSize t.toLocallyFinite : ℝ) / q k - 1 / (μ 0).toReal|
  rw [treeSize_toLocallyFinite]
  have hq0 : (0 : ℝ) < q k := by exact_mod_cast hq1 k
  have h1 : (t.size : ℝ) / q k < c := (div_lt_iff₀ hq0).2 hE'
  rw [abs_sub_comm, abs_of_pos (by linarith)]
  linarith

/-- The paper-clock contour convergence in BGW's form (hypothesis `hlim` of `tendsto_rooted_laws_of_paperContour_remarkDivisor`). -/
private theorem tendsto_paperContour_remark {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ} (hc : IsCritical μ)
    (hne : μ 1 ≠ 1) (hap : Aperiodic μ) (hB : IsRealStableAttracted (realOffspringStepLaw μ) θ B)
    (hnl : ¬ IsLatticeLaw (etaLaw μ)) {q : ℕ → ℕ}
    (hqtop : Tendsto q atTop atTop) (hq : ∀ k, LeafAdmissible μ (q k)) :
    Tendsto (fun k => (leafTreeLaw μ (q k)).map (fun τ =>
        (ContinuumTrees.FiniteTree.remarkDivisor (μ 0).toReal θ q (fun k => B (q k)) k)⁻¹ •
          (toPlaneTree τ).paperContourFunction))
      atTop (𝓝 ((excLaw θ).map Prod.snd)) := by
  refine (tendsto_rescaledContour_remark hc hne hap hB hnl hqtop hq).congr fun k => ?_
  simp only [rescaledContour_treeSize_eq_smul]
  rw [inv_remarkDivisor]

/-- `cvG_GHP` along a sequence with `q k > 0` and `B (q k) > 0` for every `k`. -/
private theorem cvG_GHP_of_pos {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ} (hc : IsCritical μ)
    (hne : μ 1 ≠ 1) (hap : Aperiodic μ) (hB : IsRealStableAttracted (realOffspringStepLaw μ) θ B)
    (hnl : ¬ IsLatticeLaw (etaLaw μ)) {q : ℕ → ℕ}
    (hqtop : Tendsto q atTop atTop) (hq : ∀ k, LeafAdmissible μ (q k))
    (hq1 : ∀ k, 0 < q k) (hBq : ∀ k, 0 < B (q k)) :
    Tendsto (fun k => (leafTreeLaw μ (q k)).map
        (scaledTreeGHP ((μ 0).toReal ^ (1 - 1 / θ) * B (q k) / q k)))
      atTop (𝓝 (((excLaw θ).map Prod.snd).map ContinuumTrees.Coding.rootedMeasuredGHSpace)) := by
  have hp : 0 < (μ 0).toReal := mu0_pos hc hne
  have hDA := (BGWLeaves.Coding.Norming.stableDomain_of_isRealStableAttracted hc hne hB).1
  have h := ContinuumTrees.FiniteTree.tendsto_rooted_laws_of_paperContour_remarkDivisor
    (Ω := fun _ => LocallyFinite.Tree) (fun k => leafTreeLaw μ (q k)) (fun _ => toPlaneTree)
    (fun _ => measurable_toPlaneTree) hp hq1 hBq (hB.tendsto_norming_atTop.comp hqtop)
    ((tendsto_norming_div_self hB).comp hqtop)
    (fun c hc0 hc1 => tendsto_size_lt hc hne hap hDA hqtop hq hq1 c hc0 hc1)
    (tendsto_paperContour_remark hc hne hap hB hnl hqtop hq)
  refine h.congr fun k => ?_
  congr 1
  funext τ
  rw [scaledTreeGHP, dite_eq_left (remark_pos hp hq1 hBq k)]
  exact scale_congr (inv_remarkDivisor _ _ q B k) _ _ _

/-- `intro_GHP_leaf` along a sequence with `q k > 0` and `B (q k) > 0` for every `k`. -/
private theorem intro_GHP_leaf_of_pos {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ} (hc : IsCritical μ)
    (hne : μ 1 ≠ 1) (hap : Aperiodic μ) (hB : IsRealStableAttracted (realOffspringStepLaw μ) θ B)
    (hnl : ¬ IsLatticeLaw (etaLaw μ)) {q : ℕ → ℕ}
    (hqtop : Tendsto q atTop atTop) (hq : ∀ k, LeafAdmissible μ (q k))
    (hq1 : ∀ k, 0 < q k) (hBq : ∀ k, 0 < B (q k)) :
    Tendsto (fun k => (leafTreeLaw μ (q k)).map
        (scaledLeafTreeGHP ((μ 0).toReal ^ (1 - 1 / θ) * B (q k) / q k)))
      atTop (𝓝 (((excLaw θ).map Prod.snd).map ContinuumTrees.Coding.rootedMeasuredGHSpace)) := by
  have hp : 0 < (μ 0).toReal := mu0_pos hc hne
  have hDA := (BGWLeaves.Coding.Norming.stableDomain_of_isRealStableAttracted hc hne hB).1
  have hb := ContinuumTrees.FiniteTree.remarkDivisor_pos (θ := θ) hp hq1 hBq
  have hbinfty := ContinuumTrees.FiniteTree.tendsto_remarkDivisor_atTop (θ := θ) hp hq1 hBq
    ((tendsto_norming_div_self hB).comp hqtop)
  have hratio := ContinuumTrees.FiniteTree.tendsto_ratio_remarkDivisor (θ := θ) hp hq1 hBq
    (hB.tendsto_norming_atTop.comp hqtop) (Ω := fun _ => LocallyFinite.Tree)
    (fun k => leafTreeLaw μ (q k)) (fun _ => toPlaneTree)
    (fun c hc0 hc1 => tendsto_size_lt hc hne hap hDA hqtop hq hq1 c hc0 hc1)
  have hsize' := ContinuumTrees.FiniteTree.tendsto_real_size_lt_of_ratio
    (Ω := fun _ => LocallyFinite.Tree) (fun k => leafTreeLaw μ (q k)) (fun _ => toPlaneTree)
    _ hb hbinfty hratio
  have hlimC := ContinuumTrees.FiniteTree.tendsto_map_contour_of_tendsto_map_paperContour
    (Ω := fun _ => LocallyFinite.Tree) (fun k => leafTreeLaw μ (q k)) (fun _ => toPlaneTree)
    _ hb
    (fun n => measurable_comp_toPlaneTree (fun t : PlaneTree =>
      (ContinuumTrees.FiniteTree.remarkDivisor (μ 0).toReal θ q (fun k => B (q k)) n)⁻¹ •
        t.paperContourFunction))
    (fun n => measurable_comp_toPlaneTree (fun t : PlaneTree =>
      (ContinuumTrees.FiniteTree.remarkDivisor (μ 0).toReal θ q (fun k => B (q k)) n)⁻¹ •
        t.contourFunction))
    hsize' (tendsto_paperContour_remark hc hne hap hB hnl hqtop hq)
  have h := ContinuumTrees.LeafMeasure.tendsto_rooted_leaf_laws_of_contour_of_top
    (Ω := fun _ => LocallyFinite.Tree) (fun k => leafTreeLaw μ (q k)) (fun _ => toPlaneTree)
    (fun _ => measurable_toPlaneTree) _ hb hbinfty hratio
    (fun ε hε => LeafLimits.Helpers.tendsto_leafIndex_discrepancy hc hne hap hDA hqtop hq hε)
    hlimC
  refine h.congr fun k => ?_
  congr 1
  funext τ
  rw [scaledLeafTreeGHP, dite_eq_left (remark_pos hp hq1 hBq k)]
  exact scale_congr (inv_remarkDivisor _ _ q B k) _ _ _

/-! ## The three statements: `cvG_GHP`, `cvG_GH`, `intro_GHP_leaf` -/

/-- **GH claim after 5.10 (lines 1593-1597)**, rooted measured GHP form (vertex measure). -/
theorem cvG_GHP {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hap : Aperiodic μ) (hB : IsRealStableAttracted (realOffspringStepLaw μ) θ B)
    (hnl : ¬ IsLatticeLaw (etaLaw μ)) {q : ℕ → ℕ}
    (hqtop : Tendsto q atTop atTop) (hq : ∀ k, LeafAdmissible μ (q k)) :
    Tendsto (fun k => (leafTreeLaw μ (q k)).map
        (scaledTreeGHP ((μ 0).toReal ^ (1 - 1 / θ) * B (q k) / q k)))
      atTop (𝓝 (((excLaw θ).map Prod.snd).map ContinuumTrees.Coding.rootedMeasuredGHSpace)) := by
  obtain ⟨K0, hK0⟩ := exists_shift hB hqtop
  exact (tendsto_add_atTop_iff_nat K0).1 (cvG_GHP_of_pos hc hne hap hB hnl
    (hqtop.comp (tendsto_add_atTop_nat K0)) (fun k => hq _) (fun k => (hK0 k).1)
    (fun k => (hK0 k).2))

/-- **GH claim after 5.10 (lines 1593-1597)**, printed (Gromov-Hausdorff) form. -/
theorem cvG_GH {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hap : Aperiodic μ) (hB : IsRealStableAttracted (realOffspringStepLaw μ) θ B)
    (hnl : ¬ IsLatticeLaw (etaLaw μ)) {q : ℕ → ℕ}
    (hqtop : Tendsto q atTop atTop) (hq : ∀ k, LeafAdmissible μ (q k)) :
    Tendsto (fun k => (leafTreeLaw μ (q k)).map (fun τ => ContinuumTrees.Coding.forgetToGH
        (scaledTreeGHP ((μ 0).toReal ^ (1 - 1 / θ) * B (q k) / q k) τ)))
      atTop (𝓝 ((((excLaw θ).map Prod.snd).map ContinuumTrees.Coding.rootedMeasuredGHSpace).map
        ContinuumTrees.Coding.forgetToGH)) := by
  have h := ContinuumTrees.Coding.tendsto_map_forgetToGH _
    (cvG_GHP hc hne hap hB hnl hqtop hq)
  refine h.congr fun k => ?_
  apply ProbabilityMeasure.toMeasure_injective
  simp only [ProbabilityMeasure.toMeasure_map]
  rw [Measure.map_map ContinuumTrees.Coding.continuous_forgetToGH.measurable
    (measurable_scaledTreeGHP _)]
  rfl

/-- **Introduction, GHP claim (lines 326-328)**, with the uniform measure on the leaves. -/
theorem intro_GHP_leaf {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hap : Aperiodic μ) (hB : IsRealStableAttracted (realOffspringStepLaw μ) θ B)
    (hnl : ¬ IsLatticeLaw (etaLaw μ)) {q : ℕ → ℕ}
    (hqtop : Tendsto q atTop atTop) (hq : ∀ k, LeafAdmissible μ (q k)) :
    Tendsto (fun k => (leafTreeLaw μ (q k)).map
        (scaledLeafTreeGHP ((μ 0).toReal ^ (1 - 1 / θ) * B (q k) / q k)))
      atTop (𝓝 (((excLaw θ).map Prod.snd).map ContinuumTrees.Coding.rootedMeasuredGHSpace)) := by
  obtain ⟨K0, hK0⟩ := exists_shift hB hqtop
  exact (tendsto_add_atTop_iff_nat K0).1 (intro_GHP_leaf_of_pos hc hne hap hB hnl
    (hqtop.comp (tendsto_add_atTop_nat K0)) (fun k => hq _) (fun k => (hK0 k).1)
    (fun k => (hK0 k).2))

end BGWLeaves.LeafLimits.Trees
