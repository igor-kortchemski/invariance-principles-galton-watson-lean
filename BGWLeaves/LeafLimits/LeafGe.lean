module

public import BGWLeaves.LeafLimits.Defs
public import BGWLeaves.Conditioning
public import BGWLeaves.LocalEstimates
public import BGWLeaves.ClassicalLimits.Cited
public import BGW.StableTrees.RealAttraction
public import BGW.StableTrees.BrownianPair
public import BGW.StableTrees.Scalar.FiniteVariance
public import BGW.StableTrees.DiscreteForestPrefixMass
public import BGW.ContinuumTrees.VervaatBridge

/-!
# Theorem 4.5 and Remark 4.6: conditioning on `λ ≥ n`

Proofs for the conditioning on `λ ≥ n`: `thm_inv1` (Theorem 4.5) and
`rem_inv1_finiteVariance` (Remark 4.6) of `BGWLeaves.LeafLimits`, exported in namespace
`BGWLeaves.LeafLimits.LeafGe` with exactly the types stated there.

Route (Theorem 4.5).  Fix a bounded continuous test `f` on `C([0,1])` and put
`U τ = f((B_ζ/ζ) C(τ)) + ‖f‖`, a fixed bounded nonnegative measurable function of the tree.  On
`{ζ = n}` the random-size contour is BGW's `treeContourPath B n 1` (`rescaledContour_eq_treeContourPath`),
so Theorem 4.1 (`thm_cv1`, along the eventually admissible sizes) gives `E[U | ζ = n] → ∫ f dH + ‖f‖`.
Proposition 4.4(i) transfers this to `ζ ≥ n`, Proposition 4.4(ii) to `λ ≥ leafCutoff n`, and since
`leafCutoff` hits every `m ≥ 1` (`leafCutoff_surjective`) the convergence holds along all `m`.
Portmanteau: `ProbabilityMeasure.tendsto_iff_forall_integral_tendsto`.

Route (Remark 4.6).  Theorem 4.5 with the finite-variance norming `B_n = (σ/√2)√n` (BGW
`Scalar.stableDomain_of_finiteVariance`), the identity `(1/√2)(B_z/z) = σ/(2√z)` (all `z`, both sides
vanish at `z = 0`), `(excLaw 2).map snd = (√2 •)_* e` (BGW `excLaw_two_map_snd`), and the continuous
scaling by `1/√2`.
-/

@[expose] public section

namespace BGWLeaves.LeafLimits.LeafGe

open MeasureTheory ProbabilityTheory Filter BGW
open BGW.StableTrees BGW.LocallyFinite BGWLeaves.StableAnalysis
open scoped ENNReal NNReal Topology BoundedContinuousFunction

/-- If `a ∘ g → l` and `g` hits every `m ≥ 1`, then `a → l`. -/
private theorem tendsto_of_tendsto_comp_of_surj {a : ℕ → ℝ} {g : ℕ → ℕ} {l : ℝ}
    (hg : ∀ m, 1 ≤ m → ∃ n, g n = m) (h : Tendsto (fun n => a (g n)) atTop (𝓝 l)) :
    Tendsto a atTop (𝓝 l) := by
  rw [Filter.tendsto_def] at h ⊢
  intro s hs
  obtain ⟨N0, hN0⟩ := Filter.mem_atTop_sets.1 (h s hs)
  rw [Filter.mem_atTop_sets]
  refine ⟨(Finset.range N0).sup g + 1, fun m hm => ?_⟩
  obtain ⟨n, rfl⟩ := hg m (by omega)
  have hn : N0 ≤ n := by
    by_contra hlt
    have := Finset.le_sup (f := g) (Finset.mem_range.2 (Nat.lt_of_not_le hlt))
    omega
  exact hN0 n hn

/-- Shifting a bounded continuous test by its norm, under a probability measure. -/
private theorem integral_add_norm {E : Type*} [TopologicalSpace E] [MeasurableSpace E]
    [OpensMeasurableSpace E] {ν : Measure LocallyFinite.Tree} [IsProbabilityMeasure ν]
    (f : E →ᵇ ℝ) {Φ : LocallyFinite.Tree → E} (hΦ : Measurable Φ) :
    ∫ τ, (f (Φ τ) + ‖f‖) ∂ν = ∫ τ, f (Φ τ) ∂ν + ‖f‖ := by
  have hint : Integrable (fun τ => f (Φ τ)) ν :=
    Integrable.of_bound (f.continuous.measurable.comp hΦ).aestronglyMeasurable ‖f‖
      (Eventually.of_forall fun τ => f.norm_coe_le_norm (Φ τ))
  rw [integral_add hint (integrable_const _), integral_const]
  simp

/-- The shifted test is a bounded nonnegative measurable function of the tree. -/
private theorem isBoundedTest_add_norm {E : Type*} [TopologicalSpace E] [MeasurableSpace E]
    [OpensMeasurableSpace E] (f : E →ᵇ ℝ) {Φ : LocallyFinite.Tree → E} (hΦ : Measurable Φ) :
    IsBoundedTest (2 * ‖f‖) (fun τ => f (Φ τ) + ‖f‖) := by
  refine ⟨(f.continuous.measurable.comp hΦ).add_const _, fun τ => ?_⟩
  have h := abs_le.1 ((Real.norm_eq_abs _).symm.le.trans (f.norm_coe_le_norm (Φ τ)))
  constructor <;> linarith [h.1, h.2]

/-- **Theorem 4.5 (`thm:inv1`, line 1237)**. -/
theorem thm_inv1 {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hap : Aperiodic μ) (hB : IsRealStableAttracted (realOffspringStepLaw μ) θ B) :
    Tendsto (fun n : ℕ => (leafGeTreeLaw μ n).map
        (fun τ => rescaledContour (treeSize τ) (B (treeSize τ) / treeSize τ) τ))
      atTop (𝓝 ((excLaw θ).map Prod.snd)) := by
  set Φ : LocallyFinite.Tree → C(Set.Icc (0 : ℝ) 1, ℝ) :=
    fun τ => rescaledContour (treeSize τ) (B (treeSize τ) / treeSize τ) τ with hΦdef
  have hΦ : Measurable Φ := measurable_rescaledContour_treeSize (fun k => B k / k)
  have hDA := (BGWLeaves.stableDomain_of_isRealStableAttracted hc hne hB).1
  obtain ⟨N, hN⟩ := BGWLeaves.sizeEvent_ne_zero_eventually hc hne hap hDA
  have hcv := BGWLeaves.ClassicalLimits.Cited.thm_cv1 hc hne hB (q := fun k => k + N)
    (tendsto_add_atTop_nat N) (fun k => hN (k + N) (Nat.le_add_left N k))
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto] at hcv ⊢
  intro f
  set L : ℝ := ∫ x, f x ∂((excLaw θ).map Prod.snd : Measure C(Set.Icc (0 : ℝ) 1, ℝ)) with hL
  let U : LocallyFinite.Tree → ℝ := fun τ => f (Φ τ) + ‖f‖
  have hU : IsBoundedTest (2 * ‖f‖) U := isBoundedTest_add_norm f hΦ
  -- Step 1: exact size `ζ = n`.
  have h1 : Tendsto (fun n : ℕ => ∫ τ, U τ ∂((bienaymeLaw μ.toMeasure)[|sizeEvent n])) atTop
      (𝓝 (L + ‖f‖)) := by
    refine (tendsto_add_atTop_iff_nat N).1 ((hcv f).add_const ‖f‖ |>.congr fun k => ?_)
    have hadm : Admissible μ (k + N) := hN (k + N) (Nat.le_add_left N k)
    have := cond_isProbabilityMeasure (μ := bienaymeLaw μ.toMeasure) hadm
    have hmap : ((DiscreteForest.exactTreeLaw μ (k + N)).map
        (ExactContour.treeContourPath B (k + N) 1)).toMeasure =
        ((bienaymeLaw μ.toMeasure)[|sizeEvent (k + N)]).map
          (ExactContour.treeContourPath B (k + N) 1) := by
      rw [ProbabilityMeasure.toMeasure_map, DiscreteForest.exactTreeLaw_toMeasure μ _ hadm]
    rw [hmap]
    let ψ : LocallyFinite.Tree → C(Set.Icc (0 : ℝ) 1, ℝ) :=
      fun τ => ExactContour.treeContourPath B (k + N) 1 τ
    have hψ : Measurable ψ := ExactContour.measurable_treeContourPath B (k + N) 1
    change ∫ ω, f ω ∂(Measure.map ψ ((bienaymeLaw μ.toMeasure)[|sizeEvent (k + N)])) + ‖f‖ =
      ∫ τ, (f (Φ τ) + ‖f‖) ∂_
    rw [integral_map hψ.aemeasurable f.continuous.aestronglyMeasurable]
    rw [integral_add_norm f hΦ]
    congr 1
    refine integral_congr_ae ?_
    filter_upwards [ae_cond_mem (measurableSet_sizeEvent (k + N))] with τ hτ
    have hsize : treeSize τ = k + N := hτ.2
    simp only [hΦdef, hsize, rescaledContour_eq_treeContourPath]
    rfl
  -- Step 2: Proposition 4.4(i), `ζ ≥ n`.
  have h2 := BGWLeaves.prop_passage_i hc hne hap hDA hU h1
  -- Step 3: Proposition 4.4(ii), `λ ≥ leafCutoff n`.
  have h3 := BGWLeaves.prop_passage_ii hc hne hap hDA (U := fun _ => U) (fun _ => hU) h2
  -- Step 4: every `m ≥ 1` is a cutoff.
  have hμ0 : 0 < (μ 0).toReal :=
    ENNReal.toReal_pos (hc.apply_zero_ne_zero hne) (PMF.apply_ne_top μ 0)
  have hμ1 : (μ 0).toReal < 1 := by
    have hle : (μ 0).toReal ≤ 1 := by
      simpa using ENNReal.toReal_mono ENNReal.one_ne_top (PMF.coe_le_one μ 0)
    refine lt_of_le_of_ne hle fun heq => BGWLeaves.mu0_ne_one hc hne ?_
    exact (ENNReal.toReal_eq_toReal_iff' (μ.apply_ne_top 0) ENNReal.one_ne_top).1
      (by simpa using heq)
  have h4 := tendsto_of_tendsto_comp_of_surj
    (a := fun m => ∫ τ, U τ ∂((bienaymeLaw μ.toMeasure)[|leafGeEvent m]))
    (BGWLeaves.leafCutoff_surjective hμ0 hμ1) h3
  -- Step 5: back to the law of the rescaled contour.
  have h5 := h4.sub_const ‖f‖
  rw [add_sub_cancel_right] at h5
  refine h5.congr fun m => ?_
  have hm := BGWLeaves.leafGeEvent_ne_zero hc hne m
  have :=cond_isProbabilityMeasure (μ := bienaymeLaw μ.toMeasure) hm
  change ∫ τ, (f (Φ τ) + ‖f‖) ∂_ - ‖f‖ = _
  rw [integral_add_norm f hΦ, add_sub_cancel_right, ProbabilityMeasure.toMeasure_map,
    coe_leafGeTreeLaw hm, integral_map hΦ.aemeasurable f.continuous.aestronglyMeasurable]

/-- **Remark 4.6 (line 1259)**. -/
theorem rem_inv1_finiteVariance {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hap : Aperiodic μ) (hfin : MemLp (fun j : ℕ => (j : ℝ)) 2 μ.toMeasure) :
    Tendsto (fun n : ℕ => (leafGeTreeLaw μ n).map (fun τ => rescaledContour (treeSize τ)
        (Real.sqrt (∫ z : ℤ, (z : ℝ) ^ 2 ∂stepLaw μ) / (2 * Real.sqrt (treeSize τ))) τ))
      atTop (𝓝 ContinuumTrees.VervaatBridge.law) := by
  set σ : ℝ := Real.sqrt (∫ z : ℤ, (z : ℝ) ^ 2 ∂stepLaw μ) with hσ
  set B : ℕ → ℝ := fun n => (σ / Real.sqrt 2) * Real.sqrt n with hBdef
  have hB : IsRealStableAttracted (realOffspringStepLaw μ) 2 B :=
    StableDomain.isRealStableAttracted (Scalar.stableDomain_of_finiteVariance hc hne hfin)
  have h := thm_inv1 hc hne hap hB
  have hs : Continuous (fun e : C(Set.Icc (0 : ℝ) 1, ℝ) => (1 / Real.sqrt 2) • e) := by fun_prop
  have h' := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _ h hs
  have hs2 : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  have hlim : ((excLaw 2).map Prod.snd).map (fun e : C(Set.Icc (0 : ℝ) 1, ℝ) =>
      (1 / Real.sqrt 2) • e) = ContinuumTrees.VervaatBridge.law := by
    rw [BrownianIdentification.excLaw_two_map_snd]
    apply Subtype.ext
    change Measure.map _ (Measure.map _ _) = _
    rw [Measure.map_map hs.measurable (by fun_prop)]
    have hid : ((fun e : C(Set.Icc (0 : ℝ) 1, ℝ) => (1 / Real.sqrt 2) • e) ∘
        fun e => Real.sqrt 2 • e) = id := by
      funext e
      simp [smul_smul, hs2]
    rw [hid, Measure.map_id]
    rfl
  have hamp (z : ℕ) : 1 / Real.sqrt 2 * (B z / z) = σ / (2 * Real.sqrt z) := by
    rcases Nat.eq_zero_or_pos z with hz | hz
    · subst hz
      simp
    · have hp : (0 : ℝ) < z := Nat.cast_pos.mpr hz
      have hrz : Real.sqrt z ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hp)
      simp only [hBdef]
      field_simp
      rw [Real.sq_sqrt hp.le, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
      ring
  have hseq : (fun n => ((leafGeTreeLaw μ n).map
      (fun τ => rescaledContour (treeSize τ) (B (treeSize τ) / treeSize τ) τ)).map
        (fun e : C(Set.Icc (0 : ℝ) 1, ℝ) => (1 / Real.sqrt 2) • e)) =
      fun n => (leafGeTreeLaw μ n).map (fun τ => rescaledContour (treeSize τ)
        (σ / (2 * Real.sqrt (treeSize τ))) τ) := by
    funext n
    apply Subtype.ext
    change Measure.map _ (Measure.map _ _) = Measure.map _ _
    rw [Measure.map_map hs.measurable (measurable_rescaledContour_treeSize (fun k => B k / k))]
    congr 1
    funext τ
    ext t
    simp only [Function.comp_apply, ContinuousMap.smul_apply, smul_eq_mul, rescaledContour,
      ContinuousMap.coe_mk, ← hamp (treeSize τ)]
    ring
  rw [hseq, hlim] at h'
  exact h'

end BGWLeaves.LeafLimits.LeafGe
