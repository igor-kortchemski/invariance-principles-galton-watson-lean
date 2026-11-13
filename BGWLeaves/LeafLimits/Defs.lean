module

public import BGWLeaves.Coding.Defs
public import BGWLeaves.ClassicalLimits.Defs
public import BGWLeaves.Conditioning.Defs
public import BGWLeaves.Vervaat
public import BGWLeaves.Vervaat.Defs
public import BGW.Skorokhod.Scaling
public import BGW.Skorokhod.VervaatStep
public import BGW.Skorokhod.VervaatMeasurable
public import BGW.ContinuumTrees.ContourPaperTransfer
public import BGW.ContinuumTrees.LeafLawConvergence
public import BGW.MetricMeasure.RootedUnderlyingGH

/-!
# Tranche 2, package M13 `LeafLimits`: definitions and proved bridges

Source: arXiv:1110.2163v4 (`.orchestration/t2-arch/paper_utf8.tex`): Lemma 5.8 (`lem:absolue`,
line 1505; the tree clock `T_u` of §5, lines 1280 and 1471), Corollary 6.7 (`cor:vervaatC`, line 2128;
the walk clock `T_n` of line 1999), the GH claim after Remark 5.10 (lines 1593-1597) and the GHP claim
of the Introduction (lines 326-328).

This file contains the definitions of package M13 and the PROVED bridges: measurability of every map
pushed forward in the statements of `BGWLeaves.LeafLimits` (the tree maps are constant on the infinite
trees, `measurable_of_eq_of_not_finiteVertices`; the walk maps factor through the countable-valued
clock `T_n`, `measurable_comp_nat`), the conditional-law bridges `coe_bridgeWalkLaw`, and audit B's B-5,
`iidWalk_bridgeAtMark_ne_zero_iff` (`P[W_{T_n} = -1] > 0 ↔ P_μ[λ = n] > 0` for `n ≥ 1`, from
tranche 1's `prop_vervaatdiscrete_total`).  No proof hole, no axiom.  It will be frozen whole.
-/

@[expose] public section

namespace BGWLeaves

open MeasureTheory ProbabilityTheory Filter BGW
open BGW.StableTrees BGW.LocallyFinite BGWLeaves.StableAnalysis
open scoped ENNReal NNReal Topology

/-! ## Definitions -/

/-- `T_u(τ) = T_{⌊u⌋}(τ)` of §5 (tree leaf clock, tranche 1's `treeLeafTime`, lines 1280 and 1471) as a
natural number; junk `0` when `T = ∞` (fewer than `⌊u⌋` leaves). -/
noncomputable def treeLeafClock (τ : LocallyFinite.Tree) (u : ℝ) : ℕ :=
  (treeLeafTime (toPlaneTree τ) ⌊u⌋₊).toNat

/-- `r_n` of Lemma 5.8: the greatest positive integer `r` with `⌈μ₀ r - r^{3/4}⌉ = n`
(`leafCutoff μ r`); junk `0` if the set is empty or unbounded (never for `n ≥ 1`, `0 < μ₀ < 1`, which
follows from `IsCritical μ` and `μ 1 ≠ 1`). -/
noncomputable def rGreatest (μ : PMF ℕ) (n : ℕ) : ℕ := sSup {r : ℕ | 1 ≤ r ∧ leafCutoff μ r = n}

/-- The pair of Lemma 5.8 on `[0,a]`:
`((1/B_r) W_{⌊T_{a μ₀ r}(τ) t/a⌋}(τ), (B_r/r) H_{T_{a μ₀ r}(τ) t/a}(τ))_{0 ≤ t ≤ a}`. -/
noncomputable def absPair (μ0 : ℝ) (B : ℕ → ℝ) (r : ℕ) (a : ℝ≥0) (ha : 0 < (a : ℝ))
    (τ : LocallyFinite.Tree) : Skorokhod.D (a : ℝ) ℝ × C(Set.Icc (0 : ℝ) a, ℝ) :=
  (Skorokhod.timeSpaceScale (a : ℝ) zero_le_one
      (rescaledLuka (treeLeafClock τ ((a : ℝ) * μ0 * r)) (B r) τ, 1,
        ⟨1 / (a : ℝ), Set.mem_Ioi.mpr (one_div_pos.mpr ha)⟩),
    ⟨fun t => B r / r * TailPair.treeHeightLin τ
        ((treeLeafClock τ ((a : ℝ) * μ0 * r) : ℝ) * (t : ℝ) / a),
      continuous_const.mul ((TailPair.continuous_treeHeightLin τ).comp
        ((continuous_const.mul continuous_subtype_val).div_const _))⟩)

/-- `T_n` of the walk (time just after the `n`-th step `-1`, tranche 1's `walkLeafTime`, line 1999) as a
natural number; junk `0` if `T_n = ∞` (null for `μ 0 ≠ 0`). -/
noncomputable def markTime (n : ℕ) (ω : ℕ → ℕ) : ℕ := (walkLeafTime ω n).toNat

/-- `(W_{⌊T_n t⌋} / B_{T_n})_{0 ≤ t ≤ 1}` (Corollary 6.7), as BGW's word step path of
`(W_1, …, W_{T_n} - W_{T_n - 1})` (`walkWord`, tranche 1).  Its value at `t = 1` is `-1/B_{T_n}` on
`{W_{T_n} = -1}`. -/
noncomputable def bridgeWalkPath (B : ℕ → ℝ) (n : ℕ) (ω : ℕ → ℕ) : Skorokhod.D 1 ℝ :=
  Skorokhod.stepPath (walkWord ω (markTime n ω)) (B (markTime n ω))

open Classical in
/-- `P[· | W_{T_n} = -1]` (`bridgeAtMark n`, tranche 1) as a probability measure; junk Dirac at the
constant sequence `0` when the event is null (never for `n ≥ 1` admissible:
`iidWalk_bridgeAtMark_ne_zero_iff`). -/
noncomputable def bridgeWalkLaw (μ : PMF ℕ) (n : ℕ) : ProbabilityMeasure (ℕ → ℕ) :=
  if h : iidWalk μ (bridgeAtMark n) ≠ 0 then
    ⟨(iidWalk μ)[|bridgeAtMark n], @cond_isProbabilityMeasure _ _ _ _
      (by unfold iidWalk; infer_instance) h⟩
  else ⟨Measure.dirac (fun _ => 0), inferInstance⟩

open Classical in
/-- The rooted measured tree `(τ, c · d_gr, uniform measure on the vertices)` (BGW C38 objects;
`c > 0`, else unscaled junk). -/
noncomputable def scaledTreeGHP (c : ℝ) (τ : LocallyFinite.Tree) :
    MetricMeasure.RootedMeasuredGHSpace.{0} :=
  if h : 0 < c then
    MetricMeasure.RootedMeasuredGHSpace.scale c h (MetricMeasure.toRootedMeasuredGHSpace
      (ContinuumTrees.FiniteTree.rootedCompactMeasuredSpace (toPlaneTree τ)))
  else MetricMeasure.toRootedMeasuredGHSpace
      (ContinuumTrees.FiniteTree.rootedCompactMeasuredSpace (toPlaneTree τ))

open Classical in
/-- The rooted measured tree `(τ, c · d_gr, uniform measure on the LEAVES)` (BGW C39 objects). -/
noncomputable def scaledLeafTreeGHP (c : ℝ) (τ : LocallyFinite.Tree) :
    MetricMeasure.RootedMeasuredGHSpace.{0} :=
  if h : 0 < c then
    MetricMeasure.RootedMeasuredGHSpace.scale c h (MetricMeasure.toRootedMeasuredGHSpace
      (ContinuumTrees.LeafMeasure.leafRootedCompactMeasuredSpace (toPlaneTree τ)))
  else MetricMeasure.toRootedMeasuredGHSpace
      (ContinuumTrees.LeafMeasure.leafRootedCompactMeasuredSpace (toPlaneTree τ))

/-! ## Measurability of the tree maps -/

/-- The tree leaf clock is measurable. -/
theorem measurable_treeLeafClock (u : ℝ) : Measurable (fun τ => treeLeafClock τ u) :=
  measurable_comp_toPlaneTree (fun t => (treeLeafTime t ⌊u⌋₊).toNat)

/-- The pair of Lemma 5.8 is a measurable function of the tree. -/
theorem measurable_absPair (μ0 : ℝ) (B : ℕ → ℝ) (r : ℕ) (a : ℝ≥0) (ha : 0 < (a : ℝ)) :
    Measurable (absPair μ0 B r a ha) := by
  refine Measurable.prodMk ?_ ?_
  · exact (measurable_timeSpaceScale (E := ℝ) (a : ℝ) zero_le_one).comp
      ((measurable_rescaledLuka_comp (fun τ => treeLeafClock τ ((a : ℝ) * μ0 * r))
        (fun _ => B r)).prodMk (measurable_const.prodMk measurable_const))
  · refine measurable_of_eq_of_not_finiteVertices fun τ τ' h h' => ContinuousMap.ext fun t => ?_
    change B r / r * TailPair.treeHeightLin τ _ = B r / r * TailPair.treeHeightLin τ' _
    simp [TailPair.treeHeightLin, h, h']

/-- The rescaled vertex-measured tree is measurable. -/
theorem measurable_scaledTreeGHP (c : ℝ) : Measurable (scaledTreeGHP c) :=
  measurable_of_eq_of_not_finiteVertices fun τ τ' h h' => by
    simp only [scaledTreeGHP, toPlaneTree_of_not_finiteVertices h,
      toPlaneTree_of_not_finiteVertices h']

/-- The rescaled leaf-measured tree is measurable. -/
theorem measurable_scaledLeafTreeGHP (c : ℝ) : Measurable (scaledLeafTreeGHP c) :=
  measurable_of_eq_of_not_finiteVertices fun τ τ' h h' => by
    simp only [scaledLeafTreeGHP, toPlaneTree_of_not_finiteVertices h,
      toPlaneTree_of_not_finiteVertices h']

/-- The underlying GH space of the rescaled tree is measurable, for ANY σ-algebra on `GHSpace` (in
particular the local Borel structure of the statements file). -/
theorem measurable_forgetToGH_scaledTreeGHP [MeasurableSpace GromovHausdorff.GHSpace] (c : ℝ) :
    Measurable (fun τ => ContinuumTrees.Coding.forgetToGH (scaledTreeGHP c τ)) :=
  measurable_of_eq_of_not_finiteVertices fun τ τ' h h' => by
    simp only [scaledTreeGHP, toPlaneTree_of_not_finiteVertices h,
      toPlaneTree_of_not_finiteVertices h']

/-! ## Measurability of the walk maps -/

/-- The walk clock `T_n` is measurable. -/
theorem measurable_markTime (n : ℕ) : Measurable (markTime n) :=
  measurable_walkLeafTime_toNat n

/-- The word step path of the first `k` steps, with a fixed divisor, is measurable (it depends on
`ω 0, …, ω (k-1)` only, a countable-valued measurable map). -/
theorem measurable_stepPath_walkWord (k : ℕ) (b : ℝ) :
    Measurable (fun ω : ℕ → ℕ => Skorokhod.stepPath (walkWord ω k) b) := by
  let R : (ℕ → ℕ) → (Fin k → ℕ) := fun ω i => ω i
  have hR : Measurable R := by
    apply Measurable.of_eval
    intro i
    exact measurable_pi_apply (i : ℕ)
  let F : (Fin k → ℕ) → Skorokhod.D 1 ℝ := fun x =>
    Skorokhod.stepPath (walkWord (fun i => if h : i < k then x ⟨i, h⟩ else 0) k) b
  have hFR : (fun ω : ℕ → ℕ => Skorokhod.stepPath (walkWord ω k) b) = F ∘ R := by
    funext ω
    simp only [Function.comp_apply, F, R]
    congr 1
    unfold walkWord
    refine List.map_congr_left fun i hi => ?_
    rw [List.mem_range] at hi
    simp [hi]
  rw [hFR]
  exact (measurable_of_countable F).comp hR

/-- The bridge walk path of Corollary 6.7 is measurable. -/
theorem measurable_bridgeWalkPath (B : ℕ → ℝ) (n : ℕ) : Measurable (bridgeWalkPath B n) :=
  measurable_comp_nat (G := fun k ω => Skorokhod.stepPath (walkWord ω k) (B k))
    (measurable_markTime n) (fun k => measurable_stepPath_walkWord k (B k))

/-- Its Vervaat transform is measurable (BGW `measurable_vervaatD`). -/
theorem measurable_vervaatD_bridgeWalkPath (B : ℕ → ℝ) (n : ℕ) :
    Measurable (fun ω => Skorokhod.vervaatD (bridgeWalkPath B n ω)) :=
  Skorokhod.measurable_vervaatD.comp (measurable_bridgeWalkPath B n)

/-! ## Conditional-law bridges -/

/-- **Audit B, B-5**: for `n ≥ 1`, `P[W_{T_n} = -1] ≠ 0 ↔ P_μ[λ = n] ≠ 0` (tranche 1
`prop_vervaatdiscrete_total`: `P[W_{T_n} = -1] = n P_μ[λ = n]`), so `bridgeWalkLaw μ n` is the genuine
conditional law along admissible `n`. -/
theorem iidWalk_bridgeAtMark_ne_zero_iff (μ : PMF ℕ) {n : ℕ} (hn : 1 ≤ n) :
    iidWalk μ (bridgeAtMark n) ≠ 0 ↔ LeafAdmissible μ n := by
  unfold iidWalk LeafAdmissible
  rw [prop_vervaatdiscrete_total μ.toMeasure hn]
  have hn0 : (n : ℝ≥0∞) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  constructor
  · intro h h0
    exact h (by rw [h0, mul_zero])
  · intro h
    exact mul_ne_zero hn0 h

/-- `bridgeWalkLaw` is the conditional law when `P[W_{T_n} = -1] ≠ 0`. -/
theorem coe_bridgeWalkLaw {μ : PMF ℕ} {n : ℕ} (hn : iidWalk μ (bridgeAtMark n) ≠ 0) :
    (bridgeWalkLaw μ n : Measure (ℕ → ℕ)) = (iidWalk μ)[|bridgeAtMark n] := by
  have h : bridgeWalkLaw μ n = ⟨(iidWalk μ)[|bridgeAtMark n], @cond_isProbabilityMeasure _ _ _ _
      (by unfold iidWalk; infer_instance) hn⟩ := by
    unfold bridgeWalkLaw
    exact dite_eq_left hn
  rw [h]
  rfl

end BGWLeaves
