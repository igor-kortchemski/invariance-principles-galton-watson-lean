module

public import BGWLeaves.Conditioning.Defs
public import BGWLeaves.LeafMass
public import BGW.StableTrees.TailPairBasic
public import BGW.StableTrees.ExactContourPaths
public import BGW.StableTrees.NonmonotoneNorming
public import BGW.StableTrees.JointExcursion
public import BGW.StableTrees.WalkPathTightness
public import BGW.Skorokhod.ExitPartition
public import BGW.Skorokhod.VervaatStep
public import BGW.LocallyFinite.SizeConditioning
public import BGW.Tree.Height
public import BGW.Tree.Excursion

/-!
# Tranche 2, package M11 `Coding`: definitions and proved bridges

Source: arXiv:1110.2163v4 (`.orchestration/t2-arch/paper_utf8.tex` line numbers): the coding functions
of the Introduction (`def:fonctions`, lines 471-496; `intro:enc`, lines 226-232 and 496), the
leaf-conditioned laws of Introduction (II) (line 254), and the extension of `W` and `H` of §5.2
(lines 1356-1362).

This file contains every definition of package M11 and the PROVED bridges (no proof hole, no axiom).
It will be frozen whole.  The statements still to be proved are in `BGWLeaves.Coding`.

Conventions (tranche 2).
* A random tree is `BGW.LocallyFinite.Tree` under `bienaymeLaw μ.toMeasure` (tranche 1).
* `ζ(τ) = treeSize τ` (`0` for an infinite tree: those are null in the critical case).
* The leaf-conditioned law `P_μ[· | λ = n]` is the `ProbabilityMeasure` `leafTreeLaw μ n`
  (the Dirac mass at the one-vertex tree when `P_μ[λ = n] = 0`, as BGW's `exactTreeLaw`).
  Sequence-indexed leaf-conditioned limits assume `LeafAdmissible μ (q k)`. The all-size canonical
  corollary may use the Dirac branch at finitely many sizes; eventual admissibility makes these
  irrelevant.
* Rescaled codings, time on `[0,1]`, arbitrary time scale `z` and amplitude:
  `rescaledLuka z b τ t = W_{⌊z t⌋}(τ) / b` (càdlàg, `D 1 ℝ`),
  `rescaledContour z a τ t = a · C_{2 z t}(τ)` and `rescaledHeight z a τ t = a · H_{z t}(τ)`
  (continuous, `C(Icc 0 1, ℝ)`; `C = 0` on `[2(ζ-1), 2ζ]`, `H` linearly interpolated, `H = 0`
  from `ζ` on, as in §5.2, lines 1359-1361).  At the random size, `z = ζ(τ)`, `b = B_ζ`, `a = B_ζ/ζ`.
* Endpoint convention of the Łukasiewicz path.  BGW's `PathTail.treeIncrementSeq` pads the
  increments with `0`, so `W_i = W_ζ = -1` for `i ≥ ζ` (the value of line 496).  Line 1357 of the paper
  instead extends `W_i(τ) = 0` for `i ≥ ζ`, which conflicts with `W_ζ = -1` at `i = ζ`.  At time
  scale `z = ζ` only the indices `i ≤ ζ` occur on `[0,1]`, and the two conventions differ only at
  `t = 1` (value `-1/B_ζ` here, `0` with the line-1357 extension): the normalized discrepancy is at most
  `1/|B_ζ|`, which tends to `0` in every limit theorem of the tranche.
* Measurability.  `ProbabilityMeasure.map` takes no measurability proof, so every map pushed forward in
  a statement has a proved measurability lemma here.  All maps of trees are handled by one principle
  (`measurable_of_eq_of_not_finiteVertices`): the finite trees form a countable set of points of the
  Polish space `LocallyFinite.Tree`, and every map below is constant on the infinite trees.
-/

@[expose] public section

namespace BGWLeaves

open MeasureTheory ProbabilityTheory Filter BGW
open BGW.StableTrees BGW.LocallyFinite BGWLeaves.StableAnalysis
open scoped ENNReal NNReal Topology

/-! ## Definitions -/

/-- `ζ(τ)`: the number of vertices of `τ` (`0` for an infinite tree, `Set.ncard` convention). -/
noncomputable def treeSize (τ : LocallyFinite.Tree) : ℕ := {u | Present τ u}.ncard

/-- `P_μ[λ(τ) = n] > 0`: the `n` along which Intro (II) is stated. -/
def LeafAdmissible (μ : PMF ℕ) (n : ℕ) : Prop := bienaymeLaw μ.toMeasure (leafCountEvent n) ≠ 0

open Classical in
/-- `P_μ[· | λ = n]` as a probability measure on trees; the Dirac mass at the one-vertex tree when
`P_μ[λ = n] = 0` (junk; excluded by admissibility in sequence-indexed limits and eventually excluded in
the all-size canonical corollary). -/
noncomputable def leafTreeLaw (μ : PMF ℕ) (n : ℕ) : ProbabilityMeasure LocallyFinite.Tree :=
  if h : LeafAdmissible μ n then
    ⟨(bienaymeLaw μ.toMeasure)[|leafCountEvent n], cond_isProbabilityMeasure h⟩
  else ⟨Measure.dirac LocallyFinite.leaf, inferInstance⟩

open Classical in
/-- `P_μ[· | λ ≥ n]` as a probability measure (Theorem 4.5); junk Dirac if the event is null
(never for critical `μ` with `μ 1 ≠ 1`: `leafGeEvent_ne_zero`, tranche 1). -/
noncomputable def leafGeTreeLaw (μ : PMF ℕ) (n : ℕ) : ProbabilityMeasure LocallyFinite.Tree :=
  if h : bienaymeLaw μ.toMeasure (leafGeEvent n) ≠ 0 then
    ⟨(bienaymeLaw μ.toMeasure)[|leafGeEvent n], cond_isProbabilityMeasure h⟩
  else ⟨Measure.dirac LocallyFinite.leaf, inferInstance⟩

/-- `t ↦ W_{⌊z t⌋}(τ) / b` on `[0,1]` (Łukasiewicz path, time scale `z`, divisor `b`). -/
noncomputable def rescaledLuka (z : ℕ) (b : ℝ) (τ : LocallyFinite.Tree) : Skorokhod.D 1 ℝ :=
  Skorokhod.realStepPath 1 z b (PathTail.treeIncrementSeq τ)

/-- `t ↦ a · C_{2 z t}(τ)` on `[0,1]` (contour function, paper clock: `C = 0` on `[2(ζ-1), 2ζ]`). -/
noncomputable def rescaledContour (z : ℕ) (a : ℝ) (τ : LocallyFinite.Tree) :
    C(Set.Icc (0 : ℝ) 1, ℝ) :=
  ⟨fun t => a * ExactContour.treeContourLin τ (2 * (z : ℝ) * (t : ℝ)),
    continuous_const.mul ((ExactContour.continuous_treeContourLin τ).comp
      (continuous_const.mul continuous_subtype_val))⟩

/-- `t ↦ a · H_{z t}(τ)` on `[0,1]` (height function, linear interpolation, `H = 0` after `ζ`). -/
noncomputable def rescaledHeight (z : ℕ) (a : ℝ) (τ : LocallyFinite.Tree) :
    C(Set.Icc (0 : ℝ) 1, ℝ) :=
  ⟨fun t => a * TailPair.treeHeightLin τ ((z : ℝ) * (t : ℝ)),
    continuous_const.mul ((TailPair.continuous_treeHeightLin τ).comp
      (continuous_const.mul continuous_subtype_val))⟩

/-- The three rescaled codings of Intro (II) at the RANDOM size `ζ = ζ(τ)`:
`(W_{⌊ζ t⌋}/B_ζ, (B_ζ/ζ) C_{2ζt}, (B_ζ/ζ) H_{ζt})_{0 ≤ t ≤ 1}` (lines 256-259). -/
noncomputable def codingTriple (B : ℕ → ℝ) (τ : LocallyFinite.Tree) :
    Skorokhod.D 1 ℝ × C(Set.Icc (0 : ℝ) 1, ℝ) × C(Set.Icc (0 : ℝ) 1, ℝ) :=
  (rescaledLuka (treeSize τ) (B (treeSize τ)) τ,
    rescaledContour (treeSize τ) (B (treeSize τ) / treeSize τ) τ,
    rescaledHeight (treeSize τ) (B (treeSize τ) / treeSize τ) τ)

/-- The codings of Remark 5.10 (`rem:changement`, lines 1587-1589): time scale `ζ(τ)` but
DETERMINISTIC amplitudes `μ₀^{1/θ}/B_n` and `μ₀^{1-1/θ} B_n / n` (`μ0 = μ₀ = μ(0)`). -/
noncomputable def codingTripleAt (μ0 θ : ℝ) (B : ℕ → ℝ) (n : ℕ) (τ : LocallyFinite.Tree) :
    Skorokhod.D 1 ℝ × C(Set.Icc (0 : ℝ) 1, ℝ) × C(Set.Icc (0 : ℝ) 1, ℝ) :=
  (rescaledLuka (treeSize τ) (B n / μ0 ^ (1 / θ)) τ,
    rescaledContour (treeSize τ) (μ0 ^ (1 - 1 / θ) * B n / n) τ,
    rescaledHeight (treeSize τ) (μ0 ^ (1 - 1 / θ) * B n / n) τ)

/-- The limit `(X^exc, H^exc, H^exc)` of Intro (II): the joint law `excLaw θ` of
`(X, H)` under `N(· | ζ = 1)` (BGW, C22.R-H), with the height duplicated (a joint law, not a
product of marginals). -/
noncomputable def excTripleLaw (θ : ℝ) :
    ProbabilityMeasure (Skorokhod.D 1 ℝ × C(Set.Icc (0 : ℝ) 1, ℝ) × C(Set.Icc (0 : ℝ) 1, ℝ)) :=
  (excLaw θ).map (fun p => (p.1, p.2, p.2))

open Classical in
/-- The finite plane tree of a finite `τ` (BGW's `PlaneTree.equivFiniteVertices`); junk one-vertex tree
for an infinite `τ` (null in the critical case). -/
noncomputable def toPlaneTree (τ : LocallyFinite.Tree) : PlaneTree :=
  if h : FiniteVertices τ then PlaneTree.equivFiniteVertices.symm ⟨τ, h⟩ else PlaneTree.node []

/-! ## Values on infinite trees (all maps are constant there) -/

theorem treeSize_of_not_finiteVertices {τ : LocallyFinite.Tree} (hτ : ¬ FiniteVertices τ) :
    treeSize τ = 0 :=
  Set.Infinite.ncard hτ

theorem treeIncrementSeq_of_not_finiteVertices {τ : LocallyFinite.Tree}
    (hτ : ¬ FiniteVertices τ) : PathTail.treeIncrementSeq τ = fun _ => 0 := by
  funext i
  simp [PathTail.treeIncrementSeq, PathTail.treeIncrements, hτ]

theorem rescaledLuka_apply_of_not_finiteVertices {τ : LocallyFinite.Tree}
    (hτ : ¬ FiniteVertices τ) (z : ℕ) (b : ℝ) (t : Set.Icc (0 : ℝ) 1) :
    rescaledLuka z b τ t = 0 := by
  change Probability.RealWalk.partialSum (PathTail.treeIncrementSeq τ) _ / b = 0
  rw [treeIncrementSeq_of_not_finiteVertices hτ]
  simp [Probability.RealWalk.partialSum]

theorem rescaledContour_apply_of_not_finiteVertices {τ : LocallyFinite.Tree}
    (hτ : ¬ FiniteVertices τ) (z : ℕ) (a : ℝ) (t : Set.Icc (0 : ℝ) 1) :
    rescaledContour z a τ t = 0 := by
  change a * ExactContour.treeContourLin τ _ = 0
  simp [ExactContour.treeContourLin, hτ]

theorem rescaledHeight_apply_of_not_finiteVertices {τ : LocallyFinite.Tree}
    (hτ : ¬ FiniteVertices τ) (z : ℕ) (a : ℝ) (t : Set.Icc (0 : ℝ) 1) :
    rescaledHeight z a τ t = 0 := by
  change a * TailPair.treeHeightLin τ _ = 0
  simp [TailPair.treeHeightLin, hτ]

theorem toPlaneTree_of_not_finiteVertices {τ : LocallyFinite.Tree} (hτ : ¬ FiniteVertices τ) :
    toPlaneTree τ = PlaneTree.node [] := by
  simp [toPlaneTree, hτ]

theorem toPlaneTree_toLocallyFinite (t : PlaneTree) : toPlaneTree t.toLocallyFinite = t := by
  rw [toPlaneTree, dite_eq_left t.finiteVertices_toLocallyFinite]
  change PlaneTree.equivFiniteVertices.symm (PlaneTree.equivFiniteVertices t) = t
  exact Equiv.symm_apply_apply _ _

theorem treeSize_toLocallyFinite (t : PlaneTree) : treeSize t.toLocallyFinite = t.size :=
  ncard_present_toLocallyFinite t

/-! ## Measurability -/

/-- **The measurability principle on trees**: a map of trees that is constant on the infinite trees
is measurable, whatever the target σ-algebra (the finite trees are countably many points of the
Polish space `LocallyFinite.Tree`, BGW `countable_finiteVertices`). -/
theorem measurable_of_eq_of_not_finiteVertices {Z : Type*} [MeasurableSpace Z]
    {f : LocallyFinite.Tree → Z}
    (hf : ∀ τ τ', ¬ FiniteVertices τ → ¬ FiniteVertices τ' → f τ = f τ') : Measurable f := by
  apply measurable_of_measurable_on_compl_countable _ ExactContour.countable_finiteVertices
  by_cases h : ∃ τ₀, ¬ FiniteVertices τ₀
  · obtain ⟨τ₀, h₀⟩ := h
    have he : ({τ : LocallyFinite.Tree | FiniteVertices τ}ᶜ).domRestrict f = fun _ => f τ₀ := by
      funext τ
      exact hf τ τ₀ τ.2 h₀
    rw [he]
    exact measurable_const
  · have : IsEmpty ({τ : LocallyFinite.Tree | FiniteVertices τ}ᶜ : Set LocallyFinite.Tree) :=
      ⟨fun τ => h ⟨τ, τ.2⟩⟩
    exact Subsingleton.measurable

/-- `ζ` is measurable. -/
theorem measurable_treeSize : Measurable treeSize :=
  measurable_of_eq_of_not_finiteVertices fun τ τ' h h' => by
    rw [treeSize_of_not_finiteVertices h, treeSize_of_not_finiteVertices h']

/-- `toPlaneTree` is measurable into `PlaneTree` with the discrete σ-algebra `⊤` (the σ-algebra BGW
uses for random plane trees, `measurable_comp_of_top`). -/
theorem measurable_toPlaneTree :
    @Measurable LocallyFinite.Tree PlaneTree _ ⊤ toPlaneTree :=
  @measurable_of_eq_of_not_finiteVertices PlaneTree ⊤ _ fun τ τ' h h' => by
    rw [toPlaneTree_of_not_finiteVertices h, toPlaneTree_of_not_finiteVertices h']

/-- Every function of `toPlaneTree τ` is measurable (any target σ-algebra). -/
theorem measurable_comp_toPlaneTree {Z : Type*} [MeasurableSpace Z] (F : PlaneTree → Z) :
    Measurable (fun τ => F (toPlaneTree τ)) :=
  measurable_of_eq_of_not_finiteVertices fun τ τ' h h' => by
    simp only [toPlaneTree_of_not_finiteVertices h, toPlaneTree_of_not_finiteVertices h']

/-- The Łukasiewicz path with a time scale and a divisor that depend on the tree is measurable. -/
theorem measurable_rescaledLuka_comp (z : LocallyFinite.Tree → ℕ) (b : LocallyFinite.Tree → ℝ) :
    Measurable (fun τ => rescaledLuka (z τ) (b τ) τ) :=
  measurable_of_eq_of_not_finiteVertices fun τ τ' h h' => Skorokhod.ext fun t => by
    rw [rescaledLuka_apply_of_not_finiteVertices h, rescaledLuka_apply_of_not_finiteVertices h']

/-- The contour path with a time scale and an amplitude that depend on the tree is measurable. -/
theorem measurable_rescaledContour_comp (z : LocallyFinite.Tree → ℕ)
    (a : LocallyFinite.Tree → ℝ) : Measurable (fun τ => rescaledContour (z τ) (a τ) τ) :=
  measurable_of_eq_of_not_finiteVertices fun τ τ' h h' => ContinuousMap.ext fun t => by
    rw [rescaledContour_apply_of_not_finiteVertices h,
      rescaledContour_apply_of_not_finiteVertices h']

/-- The height path with a time scale and an amplitude that depend on the tree is measurable. -/
theorem measurable_rescaledHeight_comp (z : LocallyFinite.Tree → ℕ)
    (a : LocallyFinite.Tree → ℝ) : Measurable (fun τ => rescaledHeight (z τ) (a τ) τ) :=
  measurable_of_eq_of_not_finiteVertices fun τ τ' h h' => ContinuousMap.ext fun t => by
    rw [rescaledHeight_apply_of_not_finiteVertices h,
      rescaledHeight_apply_of_not_finiteVertices h']

/-- Fixed parameters. -/
theorem measurable_rescaledLuka (z : ℕ) (b : ℝ) : Measurable (rescaledLuka z b) :=
  measurable_rescaledLuka_comp (fun _ => z) (fun _ => b)

/-- Fixed parameters. -/
theorem measurable_rescaledContour (z : ℕ) (a : ℝ) : Measurable (rescaledContour z a) :=
  measurable_rescaledContour_comp (fun _ => z) (fun _ => a)

/-- Fixed parameters. -/
theorem measurable_rescaledHeight (z : ℕ) (a : ℝ) : Measurable (rescaledHeight z a) :=
  measurable_rescaledHeight_comp (fun _ => z) (fun _ => a)

/-- At the random size `ζ(τ)`, with divisor `b ζ` (Theorems 5.9(i), 6.1, Corollary 6.7). -/
theorem measurable_rescaledLuka_treeSize (b : ℕ → ℝ) :
    Measurable (fun τ => rescaledLuka (treeSize τ) (b (treeSize τ)) τ) :=
  measurable_rescaledLuka_comp treeSize (fun τ => b (treeSize τ))

/-- At the random size `ζ(τ)`, with amplitude `a ζ` (Theorem 4.5 with `a z = B_z / z`, Remark 4.6
with `a z = σ / (2 √z)`). -/
theorem measurable_rescaledContour_treeSize (a : ℕ → ℝ) :
    Measurable (fun τ => rescaledContour (treeSize τ) (a (treeSize τ)) τ) :=
  measurable_rescaledContour_comp treeSize (fun τ => a (treeSize τ))

/-- At the random size `ζ(τ)`, with amplitude `a ζ`. -/
theorem measurable_rescaledHeight_treeSize (a : ℕ → ℝ) :
    Measurable (fun τ => rescaledHeight (treeSize τ) (a (treeSize τ)) τ) :=
  measurable_rescaledHeight_comp treeSize (fun τ => a (treeSize τ))

/-- The coding map of Intro (II) is measurable. -/
theorem measurable_codingTriple (B : ℕ → ℝ) : Measurable (codingTriple B) :=
  (measurable_rescaledLuka_treeSize B).prodMk
    ((measurable_rescaledContour_treeSize fun k => B k / k).prodMk
      (measurable_rescaledHeight_treeSize fun k => B k / k))

/-- The coding map of Remark 5.10 is measurable. -/
theorem measurable_codingTripleAt (μ0 θ : ℝ) (B : ℕ → ℝ) (n : ℕ) :
    Measurable (codingTripleAt μ0 θ B n) :=
  (measurable_rescaledLuka_comp treeSize fun _ => B n / μ0 ^ (1 / θ)).prodMk
    ((measurable_rescaledContour_comp treeSize fun _ => μ0 ^ (1 - 1 / θ) * B n / n).prodMk
      (measurable_rescaledHeight_comp treeSize fun _ => μ0 ^ (1 - 1 / θ) * B n / n))

/-! ## Bridges -/

/-- `leafTreeLaw` is the conditional law at admissible `n`. -/
theorem coe_leafTreeLaw {μ : PMF ℕ} {n : ℕ} (hn : LeafAdmissible μ n) :
    (leafTreeLaw μ n : Measure LocallyFinite.Tree) =
      (bienaymeLaw μ.toMeasure)[|leafCountEvent n] := by
  have h : leafTreeLaw μ n =
      ⟨(bienaymeLaw μ.toMeasure)[|leafCountEvent n], cond_isProbabilityMeasure hn⟩ := by
    unfold leafTreeLaw
    exact dite_eq_left hn
  rw [h]
  rfl

/-- `leafGeTreeLaw` is the conditional law when `P_μ[λ ≥ n] > 0`. -/
theorem coe_leafGeTreeLaw {μ : PMF ℕ} {n : ℕ} (hn : bienaymeLaw μ.toMeasure (leafGeEvent n) ≠ 0) :
    (leafGeTreeLaw μ n : Measure LocallyFinite.Tree) =
      (bienaymeLaw μ.toMeasure)[|leafGeEvent n] := by
  have h : leafGeTreeLaw μ n =
      ⟨(bienaymeLaw μ.toMeasure)[|leafGeEvent n], cond_isProbabilityMeasure hn⟩ := by
    unfold leafGeTreeLaw
    exact dite_eq_left hn
  rw [h]
  rfl

/-- At deterministic size `n`, `rescaledLuka` is BGW's `PathTail.treePrefixPath`. -/
theorem rescaledLuka_eq_treePrefixPath (B : ℕ → ℝ) (n : ℕ) (τ : LocallyFinite.Tree) :
    rescaledLuka n (B n) τ = PathTail.treePrefixPath B n 1 τ :=
  rfl

/-- At deterministic size `n`, `rescaledHeight` is BGW's `TailPair.treeHeightPath`. -/
theorem rescaledHeight_eq_treeHeightPath (B : ℕ → ℝ) (n : ℕ) (τ : LocallyFinite.Tree) :
    rescaledHeight n (B n / n) τ = TailPair.treeHeightPath B n 1 τ := by
  unfold TailPair.treeHeightPath
  rw [dite_eq_left (TailPair.continuous_treeHeightLin τ)]
  rfl

/-- At deterministic size `n`, `rescaledContour` is BGW's `ExactContour.treeContourPath`. -/
theorem rescaledContour_eq_treeContourPath (B : ℕ → ℝ) (n : ℕ) (τ : LocallyFinite.Tree) :
    rescaledContour n (B n / n) τ = ExactContour.treeContourPath B n 1 τ := by
  unfold ExactContour.treeContourPath
  rw [dite_eq_left (ExactContour.continuous_treeContourLin τ)]
  rfl

private theorem partialSum_getD (x : List ℤ) (m : ℕ) :
    Probability.RealWalk.partialSum (fun i => ((x.getD i 0 : ℤ) : ℝ)) m =
      (((x.take m).sum : ℤ) : ℝ) := by
  induction m with
  | zero => simp [Probability.RealWalk.partialSum]
  | succ m ih =>
    rw [Probability.RealWalk.partialSum, Finset.sum_range_succ, ← Probability.RealWalk.partialSum,
      ih, List.take_add_one, List.sum_append]
    cases h : x[m]? <;> simp [List.getD_eq_getElem?_getD, h]

theorem treeIncrements_toLocallyFinite (t : PlaneTree) :
    PathTail.treeIncrements t.toLocallyFinite = t.increments := by
  rw [PathTail.treeIncrements, dite_eq_left t.finiteVertices_toLocallyFinite]
  change (PlaneTree.equivFiniteVertices.symm (PlaneTree.equivFiniteVertices t)).increments = _
  rw [Equiv.symm_apply_apply]

/-- For a finite tree, the Łukasiewicz path at its own size is BGW's word step path of the increment
word (C33.5 input); in particular `treeSize τ = (treeIncrements τ).length`. -/
theorem rescaledLuka_eq_stepPath (τ : LocallyFinite.Tree) (hτ : FiniteVertices τ) (b : ℝ) :
    rescaledLuka (treeSize τ) b τ = Skorokhod.stepPath (PathTail.treeIncrements τ) b := by
  obtain ⟨t, rfl⟩ := (exists_toLocallyFinite_iff τ).2 hτ
  apply Skorokhod.ext
  intro s
  change Probability.RealWalk.partialSum (PathTail.treeIncrementSeq t.toLocallyFinite)
      ⌊(treeSize t.toLocallyFinite : ℝ) * (s : ℝ)⌋₊ / b =
    (((PathTail.treeIncrements t.toLocallyFinite).take
      ⌊((PathTail.treeIncrements t.toLocallyFinite).length : ℝ) * (s : ℝ)⌋₊).sum : ℝ) / b
  rw [treeSize_toLocallyFinite, treeIncrements_toLocallyFinite, PlaneTree.length_increments]
  unfold PathTail.treeIncrementSeq
  rw [treeIncrements_toLocallyFinite, partialSum_getD]

end BGWLeaves
