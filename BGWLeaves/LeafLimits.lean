module

public import BGWLeaves.LeafLimits.Defs
public import BGWLeaves.Coding.Defs
public import BGWLeaves.ClassicalLimits.Defs
public import BGWLeaves.Conditioning.Defs
public import BGWLeaves.Vervaat.Defs
public import BGWLeaves.LeafMass
public import BGWLeaves.StableAnalysis
public import BGW.StableTrees.RealAttraction
public import BGW.StableTrees.TailPairBasic
public import BGW.StableTrees.ExactContourPaths
public import BGW.StableTrees.NonmonotoneNorming
public import BGW.StableTrees.JointExcursion
public import BGW.StableTrees.UnitExcursionLaw
public import BGW.StableTrees.UnitExcursionLawBasic
public import BGW.StableTrees.FiniteVarianceContour
public import BGW.StableTrees.StableBridgeClosed
public import BGW.StableTrees.BridgeProjectiveClose
public import BGW.StableTrees.ExcursionJump
public import BGW.Skorokhod.ExitPartition
public import BGW.Skorokhod.VervaatStep
public import BGW.Skorokhod.VervaatRotate
public import BGW.Skorokhod.Vervaat
public import BGW.Skorokhod.Scaling
public import BGW.ContinuumTrees.VervaatBridge
public import BGW.ContinuumTrees.CodingStability
public import BGW.ContinuumTrees.ContourPaperTransfer
public import BGW.ContinuumTrees.LeafLawConvergence
public import BGW.ContinuumTrees.LeafMeasure
public import BGW.MetricMeasure.RootedUnderlyingGH
public import BGW.Tree
public import BGW.StableTrees.Defs
public import BGW.Skorokhod.Basic
public import BGW.Skorokhod.Measurable
public import BGW.Skorokhod.Restrict
public import BGW.LocallyFinite.Basic
public import BGW.LocallyFinite.Law
public import BGW.MetricMeasure.RootedMeasuredGHSpace
public import BGWLeaves.LeafMass.Defs
public import BGWLeaves.StableAnalysis.Defs
import BGWLeaves.LeafLimits.Proof

/-!
# `LeafLimits`: the leaf-conditioned limit theorems

Source: arXiv:1110.2163v4 (line numbers refer to its LaTeX source): Theorem 4.5 (`thm:inv1`,
line 1237), Remark 4.6 (line 1259), Lemma 5.8 (`lem:absolue`, line 1505), Theorem 5.9 (`thm:cvG`,
line 1568), Remark 5.10 (`rem:changement`, line 1587), the GH claim after 5.10 (lines 1593-1597),
Corollary 6.7 (`cor:vervaatC`, line 2128), Theorem 6.1 (`thm:cvW3`, line 1986), Introduction (II)
(line 254) and its GHP claim (lines 326-328).

Each declaration here is proved in the modules `BGWLeaves.LeafLimits.*` (imported through
`BGWLeaves.LeafLimits.Proof`).  Definitions and bridges
(measurability of every pushed-forward map, `coe_bridgeWalkLaw`, `iidWalk_bridgeAtMark_ne_zero_iff`) are in
`BGWLeaves.LeafLimits.Defs`; the codings are those of `BGWLeaves.Coding.Defs`.

Hypotheses common to the leaf-conditioned statements.
* `(H_θ)` spelled out: `IsCritical μ`, `μ 1 ≠ 1`, `Aperiodic μ`, and the domain of
  attraction given by an ARBITRARY admissible norming `B` (`IsRealStableAttracted
  (realOffspringStepLaw μ) θ B`, which implies `∃ a, StableDomain μ θ a`,
  `stableDomain_of_isRealStableAttracted`).  The paper's "there exists `B_n`" is the special case
  `B = norming (stepLaw μ) θ` (`isRealStableAttracted_norming`), see `intro_II_canonical`.
* `hnl : ¬ IsLatticeLaw (etaLaw μ)` (`supp μ ∖ {0}` non-lattice) is the STANDING ASSUMPTION of §5,
  line 1269 ("To avoid technical issues, we suppose that supp(μ)∖{0} is non-lattice, so that
  P[λ = n] > 0 for n large"), needed by the inputs 5.4(ii) and 6.11 (which fail as printed in the
  lattice case).  The proofs of
  Theorem 5.9 (lines 1602-1603) and of §6 (lines 1996-1997) announce instead the WEAKER condition
  "`P_μ[λ = n] > 0` for all `n` sufficiently large" (`gcd(b - 1, d) = 1` in the notation of Theorem 3.1,
  versus `d = 1` for `hnl`; e.g. support `{0, 2, 5}` satisfies the weaker condition and not `hnl`).
  `hnl` is a SUFFICIENT RESTRICTION, kept for both §5 and §6; the results that carry it are proved
  under the paper's standing assumption of line 1269, and the printed generality is the statement
  `intro_II_general` (`BGWLeaves.LeafLimitsGeneral`).  Next to `hnl`, the hypotheses `hap` and `hne` are
  REDUNDANT (`hnl` forces two points of `supp μ ∖ {0}` whose differences generate `ℤ`, hence aperiodicity
  and `μ 1 ≠ 1`); they are kept for uniformity with the other statements.
* Convergence "as `n → ∞` along the `n` with `P_μ[λ = n] > 0`": along every sequence `q k → ∞` of
  admissible sizes (BGW's convention for `ζ = n`).  Non-vacuous: `exists_seq_leafAdmissible`.

Layout (modules).
* Helpers (module `Helpers`): `tendsto_treeSize_div_leaf`, `tendsto_leafIndex_discrepancy`,
  `vervaatD_stepPath_vervaat`.
* Theorem 4.5, Remark 4.6 (module `LeafGe`): `thm_inv1`, `rem_inv1_finiteVariance`.
* Lemma 5.8 (module `Absolue`): `lem_absolue`.
* Theorem 5.9 (module `ContourHeight`): `thm_cvG_i`, `thm_cvG_ii`.
* Corollary 6.7 (module `VervaatLaw`): `cor_vervaatC`.
* The bridge invariance principle (module `Bridge`): `tendsto_bridgeWalkPath`.
* Theorem 6.1 (module `Walk`): `thm_cvW3`.
* Introduction (II) (module `Joint`): `intro_II`, `intro_II_canonical`, `rem_changement`.
* Trees (module `Trees`): `cvG_GHP`, `cvG_GH`, `intro_GHP_leaf`.
-/

@[expose] public section

namespace BGWLeaves

open MeasureTheory ProbabilityTheory Filter BGW
open BGW.StableTrees BGW.LocallyFinite BGWLeaves.StableAnalysis
open scoped ENNReal NNReal Topology

/-! ## Helpers (discrete glue and in-probability inputs) -/

/-- Under `P_μ[· | λ = n]`, `ζ(τ_n)/n → 1/μ₀` in probability.  Not printed as a statement: it is the
content of `eq:lg` (line 278) / Lemma 3.4(ii), used for `K_n`, `S_n` in 5.9, 6.1 and for
Remark 5.10.  The hypotheses use `∃ a, StableDomain μ θ a` (equivalent to `hB`,
`stableDomain_of_isRealStableAttracted`).  Proof: `cor_Lambda` and `P_μ[λ = n] ≥ n^{-C}` along
admissible `n`. -/
theorem tendsto_treeSize_div_leaf {μ : PMF ℕ} {θ : ℝ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hap : Aperiodic μ) (hDA : ∃ a, StableDomain μ θ a) {q : ℕ → ℕ}
    (hqtop : Tendsto q atTop atTop) (hq : ∀ k, LeafAdmissible μ (q k)) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun k => (leafTreeLaw μ (q k)).toMeasure.real
      {τ | ε < |(treeSize τ : ℝ) / q k - 1 / (μ 0).toReal|}) atTop (𝓝 0) := by
  exact BGWLeaves.LeafLimits.Helpers.tendsto_treeSize_div_leaf hc hne hap hDA hqtop hq hε

/-- **Leaf-index discrepancy (`hleaf` of BGW `tendsto_rooted_leaf_laws_of_contour`)**: under
`P_μ[· | λ = n]` the leaf-index discrepancy `max_k |ℓ_k/ζ - k/λ|` tends to `0` in probability.  Not
printed (Corollary 3.3, `cor_Lambda`, uniformly in the time, and the monotonicity of `ℓ_k`). -/
theorem tendsto_leafIndex_discrepancy {μ : PMF ℕ} {θ : ℝ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hap : Aperiodic μ) (hDA : ∃ a, StableDomain μ θ a) {q : ℕ → ℕ}
    (hqtop : Tendsto q atTop atTop) (hq : ∀ k, LeafAdmissible μ (q k)) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun k => (leafTreeLaw μ (q k)).toMeasure.real
      {τ | ∃ j < ContinuumTrees.LeafMeasure.numLeaves (toPlaneTree τ),
        ε < |(ContinuumTrees.LeafMeasure.leafIndex (toPlaneTree τ) j : ℝ) /
            ((toPlaneTree τ).size : ℝ) -
          (j : ℝ) / (ContinuumTrees.LeafMeasure.numLeaves (toPlaneTree τ) : ℝ)|}) atTop (𝓝 0) := by
  exact BGWLeaves.LeafLimits.Helpers.tendsto_leafIndex_discrepancy hc hne hap hDA hqtop hq hε

/-- **Vervaat transform at the path level** (the identity behind Corollary 6.7):
`V(stepPath x B) = stepPath (V x) B` for `B > 0` and a word `x` with some negative prefix sum (the
project's discrete Vervaat transform `vervaat`).  Not printed (glue).  Proof: BGW `vervaatD_stepPath`,
with `vervaat_eq_rotate_vervaatIndex`. -/
theorem vervaatD_stepPath_vervaat {x : List ℤ}
    (hx : ∃ j, 1 ≤ j ∧ j ≤ x.length ∧ (x.take j).sum < 0) {B : ℝ} (hB : 0 < B) :
    Skorokhod.vervaatD (Skorokhod.stepPath x B) = Skorokhod.stepPath (vervaat x) B := by
  exact BGWLeaves.LeafLimits.Helpers.vervaatD_stepPath_vervaat hx hB

/-! ## 4.5, 4.6: conditioning on `λ ≥ n` -/

/-- **Theorem 4.5 (`thm:inv1`, line 1237)**: for `τ_n ∼ P_μ[· | λ ≥ n]`,
`((B_ζ/ζ) C_{2ζt}(τ_n))_{0 ≤ t ≤ 1} → H^exc` in law in `C([0,1])`, `ζ = ζ(τ_n)`.
Form: STRONGER than printed: any admissible norming `B`.  No `hnl` (§4, before the standing assumption
of line 1269).  Measurability: `measurable_rescaledContour_treeSize`.
Proof: Theorem 4.1 (`thm_cv1`) at `B_ζ/ζ` (the test `F(B_ζ/ζ · C(τ))` is a fixed bounded function
of the tree), Proposition 4.4(i)/(ii) (`prop_passage_i`, `prop_passage_ii`),
`leafCutoff_surjective`; portmanteau via `tendsto_iff_forall_integral_tendsto`. -/
theorem thm_inv1 {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hap : Aperiodic μ) (hB : IsRealStableAttracted (realOffspringStepLaw μ) θ B) :
    Tendsto (fun n : ℕ => (leafGeTreeLaw μ n).map
        (fun τ => rescaledContour (treeSize τ) (B (treeSize τ) / treeSize τ) τ))
      atTop (𝓝 ((excLaw θ).map Prod.snd)) := by
  exact BGWLeaves.LeafLimits.LeafGe.thm_inv1 hc hne hap hB

/-- **Remark 4.6 (line 1259)**: finite variance `σ²`: `(σ/(2√ζ) C_{2ζt}(τ_n))_{0 ≤ t ≤ 1} → e`, the
normalized Brownian excursion (`VervaatBridge.law`), for `τ_n ∼ P_μ[· | λ ≥ n]`.  Form: PRINTED.  Measurability: `measurable_rescaledContour_treeSize` with
amplitude `z ↦ σ/(2√z)`.  Proof: `thm_inv1` with `B_n = σ√(n/2)` (`norming_of_integrable_sq`),
`σ/(2√z) = (B_z/z)/√2` (BGW `finiteVarianceNorming_div`), `(excLaw 2).map snd = (√2 e)` (BGW
`excLaw_two_map_snd`), continuous scaling by `1/√2`. -/
theorem rem_inv1_finiteVariance {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hap : Aperiodic μ) (hfin : MemLp (fun j : ℕ => (j : ℝ)) 2 μ.toMeasure) :
    Tendsto (fun n : ℕ => (leafGeTreeLaw μ n).map (fun τ => rescaledContour (treeSize τ)
        (Real.sqrt (∫ z : ℤ, (z : ℝ) ^ 2 ∂stepLaw μ) / (2 * Real.sqrt (treeSize τ))) τ))
      atTop (𝓝 ContinuumTrees.VervaatBridge.law) := by
  exact BGWLeaves.LeafLimits.LeafGe.rem_inv1_finiteVariance hc hne hap hfin

/-! ## 5.8-5.10: conditioning on `λ = n` -/

/-- **Lemma 5.8 (`lem:absolue`, line 1505)**: for `a ∈ (0,1)`, `r_n` as in `rGreatest` and
`τ_n ∼ P_μ[· | λ = n]`, the pair `absPair` converges to `(X_t, H_t)_{0 ≤ t ≤ a}` under `N(· | ζ = 1)`.
Form: STRONGER (any admissible norming) and RESTRICTED: added hypothesis `hnl` (line 1269, the §5
standing assumption); carrier `D([0,a]) × C([0,a])` for the printed `D([0,a], ℝ²)` (equivalent: the
limit second coordinate is continuous); the indicator cut-offs of the proof must avoid the atoms of
`X_a`.  `r_n = rGreatest μ n` is never junk here: its defining set is finite and non-empty for `n ≥ 1`
because `0 < μ₀ < 1` (from `hc`, `hne`).  Measurability: `measurable_absPair`.
Proof: Proposition 5.2 (`prop_abscon`), the density estimate `eq:cva` from Corollary 5.5
(`cor_tejhnique_i/ii`) and `gammaA_eq_paper`, Lemma 5.6 (`lem_CVf_i`), Theorem 5.1
(`thm_cvW`), Lemma 5.7 (`lem_CVproba_pair`), Proposition 4.4(ii), Proposition 5.3 (`prop_Gamma`),
the continuous mapping theorem with cut-offs off the atoms. -/
theorem lem_absolue {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hap : Aperiodic μ) (hB : IsRealStableAttracted (realOffspringStepLaw μ) θ B)
    (hnl : ¬ IsLatticeLaw (etaLaw μ)) {a : ℝ≥0} (ha : a ∈ Set.Ioo (0 : ℝ≥0) 1) {q : ℕ → ℕ}
    (hqtop : Tendsto q atTop atTop) (hq : ∀ k, LeafAdmissible μ (q k)) :
    Tendsto (fun k => (leafTreeLaw μ (q k)).map
        (absPair (μ 0).toReal B (rGreatest μ (q k)) a (NNReal.coe_pos.mpr ha.1)))
      atTop (𝓝 ((excLaw θ).map (restrictPair ha.2.le))) := by
  exact BGWLeaves.LeafLimits.Absolue.lem_absolue hc hne hap hB hnl ha hqtop hq

/-- **Theorem 5.9(i) (`thm:cvG`, `eq:H0`, line 1574)**: for `a ∈ (0,1)` and `τ_n ∼ P_μ[· | λ = n]`,
`(W_{⌊ζ t⌋}(τ_n)/B_ζ)_{0 ≤ t ≤ a} → (X_t)_{0 ≤ t ≤ a}` under `N(· | ζ = 1)`.  Form: STRONGER (any
admissible norming) and RESTRICTED: added hypothesis `hnl` (line 1269).  This is the `a < 1` case of
`thm_cvW3` composed with the restriction (the printed remark of line 1599 says it holds with `a = 1`); it
is kept as the printed intermediate statement.  Measurability:
`measurable_rescaledLuka_treeSize` and BGW `measurable_restrict`.
Proof: for target horizon `a`, choose `a < b < 1`. Apply Lemma 5.8 at `b` and Lemma 5.7 from `[0,b]`
to `[0,a]`, with `K_n = B_{r_n}/B_ζ` and `S_n = b ζ / T_{b μ₀ r_n}`. Use eventual positivity of the clock;
define the time factor arbitrarily positive on exceptional samples (Lemma 5.7 needs a strictly larger
input horizon).  Inputs: `tendsto_treeSize_div_leaf`, Lemma 5.6(ii)
`lem_CVf_ii`, BGW `IsRealStableAttracted.tendsto_norming_ratio`. -/
theorem thm_cvG_i {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hap : Aperiodic μ) (hB : IsRealStableAttracted (realOffspringStepLaw μ) θ B)
    (hnl : ¬ IsLatticeLaw (etaLaw μ)) {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {q : ℕ → ℕ}
    (hqtop : Tendsto q atTop atTop) (hq : ∀ k, LeafAdmissible μ (q k)) :
    Tendsto (fun k => (leafTreeLaw μ (q k)).map
        (fun τ => Skorokhod.restrict ha1.le (rescaledLuka (treeSize τ) (B (treeSize τ)) τ)))
      atTop (𝓝 ((levyExcLaw θ).map (Skorokhod.restrict ha1.le))) := by
  exact BGWLeaves.LeafLimits.ContourHeight.thm_cvG_i hc hne hap hB hnl ha0 ha1 hqtop hq

/-- **Theorem 5.9(ii) (`thm:cvG`, `eq:H`, line 1579)**:
`((B_ζ/ζ) C_{2ζt}(τ_n), (B_ζ/ζ) H_{ζt}(τ_n))_{0 ≤ t ≤ 1} → (H_t, H_t)_{0 ≤ t ≤ 1}` under `N(· | ζ = 1)`,
in `C([0,1])²` (a joint, diagonal limit).  Form: STRONGER (any admissible norming) and RESTRICTED: added
hypothesis `hnl` (line 1269).  Measurability: `measurable_codingTriple`, then `Prod.snd`.
Proof: `eq:cvH` from Lemma 5.8 and 5.7; the contour/height comparison `eq:ineg`-`eq:HC` (discrete, BGW
`contourHeightError` machinery at random size); time reversal of the contour under `P_μ[· | λ = n]`
(discrete) and terminal oscillation control
(`tendsto_continuous_of_tendsto_restrict_of_oscillation`); `H^exc_1 = 0` (BGW
`excLaw_height_endpoints_pos`). -/
theorem thm_cvG_ii {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hap : Aperiodic μ) (hB : IsRealStableAttracted (realOffspringStepLaw μ) θ B)
    (hnl : ¬ IsLatticeLaw (etaLaw μ)) {q : ℕ → ℕ}
    (hqtop : Tendsto q atTop atTop) (hq : ∀ k, LeafAdmissible μ (q k)) :
    Tendsto (fun k => (leafTreeLaw μ (q k)).map (fun τ => (codingTriple B τ).2))
      atTop (𝓝 ((excLaw θ).map (fun p => (p.2, p.2)))) := by
  exact BGWLeaves.LeafLimits.ContourHeight.thm_cvG_ii hc hne hap hB hnl hqtop hq

/-- **Remark 5.10 (`rem:changement`, line 1587)**, in its strongest (joint, whole-interval) form: the
random factors `1/B_ζ` and `B_ζ/ζ` can be replaced by `μ₀^{1/θ}/B_n` and `μ₀^{1-1/θ} B_n/n` in the main
theorem (hence in 5.9 and 6.1, by projection).  Form: STRONGER (joint form; any admissible norming) and
RESTRICTED: added hypothesis `hnl` (line 1269).  Measurability: `measurable_codingTripleAt`.
Proof: `intro_II`, `tendsto_treeSize_div_leaf`, `IsRealStableAttracted.tendsto_norming_ratio`,
Slutsky's lemma and continuity of `(x, c) ↦ c • x`. -/
theorem rem_changement {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hap : Aperiodic μ) (hB : IsRealStableAttracted (realOffspringStepLaw μ) θ B)
    (hnl : ¬ IsLatticeLaw (etaLaw μ)) {q : ℕ → ℕ}
    (hqtop : Tendsto q atTop atTop) (hq : ∀ k, LeafAdmissible μ (q k)) :
    Tendsto (fun k => (leafTreeLaw μ (q k)).map (codingTripleAt (μ 0).toReal θ B (q k)))
      atTop (𝓝 (excTripleLaw θ)) := by
  exact BGWLeaves.LeafLimits.Joint.rem_changement hc hne hap hB hnl hqtop hq

/-- **GH claim after 5.10 (lines 1593-1597)**, in the rooted measured GHP form: `τ_n` with graph distance
times `μ₀^{1-1/θ} B_n/n` and the uniform measure on its vertices converges in law to the `θ`-stable tree
`T_{H^exc}` (with its mass measure).  Form: STRONGER than the printed Gromov-Hausdorff claim (root and
measure kept; any admissible norming) and RESTRICTED: added hypothesis `hnl` (line 1269).
Measurability: `measurable_scaledTreeGHP`.
Proof: BGW `FiniteTree.tendsto_rooted_laws_of_paperContour_remarkDivisor` with `N n = n`,
`hsize` from `tendsto_treeSize_div_leaf`, `hlim` from 5.9(ii) and 5.10.  That theorem
requires `0 < B n` for ALL `n` (apply it to a sequence modified on finitely many `k`). -/
theorem cvG_GHP {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hap : Aperiodic μ) (hB : IsRealStableAttracted (realOffspringStepLaw μ) θ B)
    (hnl : ¬ IsLatticeLaw (etaLaw μ)) {q : ℕ → ℕ}
    (hqtop : Tendsto q atTop atTop) (hq : ∀ k, LeafAdmissible μ (q k)) :
    Tendsto (fun k => (leafTreeLaw μ (q k)).map
        (scaledTreeGHP ((μ 0).toReal ^ (1 - 1 / θ) * B (q k) / q k)))
      atTop (𝓝 (((excLaw θ).map Prod.snd).map ContinuumTrees.Coding.rootedMeasuredGHSpace)) := by
  exact BGWLeaves.LeafLimits.Trees.cvG_GHP hc hne hap hB hnl hqtop hq

/-- The Borel structure on `GHSpace`, declared locally exactly as in BGW
(`BGW/MetricMeasure/RootedUnderlyingGH.lean`, `ghMeasurableSpace`): BGW provides no global instance.
The elaborated type of `cvG_GH` mentions this constant and `ghBorelSpace`; the proof module (which cannot
import this file) declares its own local `borel GHSpace` instances, and its theorem proves `cvG_GH` by
`exact`, the two instances being definitionally equal. -/
noncomputable local instance ghMeasurableSpace : MeasurableSpace GromovHausdorff.GHSpace :=
  borel GromovHausdorff.GHSpace

/-- The local Borel-space instance accompanying `ghMeasurableSpace` (named so that other modules can
re-activate it). -/
local instance ghBorelSpace : BorelSpace GromovHausdorff.GHSpace := ⟨rfl⟩

/-- **GH claim after 5.10 (lines 1593-1597)**, printed (Gromov-Hausdorff) form: forget root and measure in
`cvG_GHP`.  The laws on `GHSpace` use its Borel σ-algebra (local instance above, as in BGW).  Form: PRINTED
claim (any admissible norming, STRONGER) and RESTRICTED: added hypothesis `hnl` (line 1269).
Measurability: `measurable_forgetToGH_scaledTreeGHP` (for any σ-algebra on `GHSpace`).
Proof: BGW `Coding.tendsto_map_forgetToGH`. -/
theorem cvG_GH {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hap : Aperiodic μ) (hB : IsRealStableAttracted (realOffspringStepLaw μ) θ B)
    (hnl : ¬ IsLatticeLaw (etaLaw μ)) {q : ℕ → ℕ}
    (hqtop : Tendsto q atTop atTop) (hq : ∀ k, LeafAdmissible μ (q k)) :
    Tendsto (fun k => (leafTreeLaw μ (q k)).map (fun τ => ContinuumTrees.Coding.forgetToGH
        (scaledTreeGHP ((μ 0).toReal ^ (1 - 1 / θ) * B (q k) / q k) τ)))
      atTop (𝓝 ((((excLaw θ).map Prod.snd).map ContinuumTrees.Coding.rootedMeasuredGHSpace).map
        ContinuumTrees.Coding.forgetToGH)) := by
  exact BGWLeaves.LeafLimits.Trees.cvG_GH hc hne hap hB hnl hqtop hq

/-! ## 6.7, 6.1: the Łukasiewicz path on the whole interval -/

/-- **Corollary 6.7 (`cor:vervaatC`, line 2128)**: the law of `(W_{⌊ζ t⌋}(τ)/B_ζ)_{0 ≤ t ≤ 1}` under
`P_μ[· | λ = n]` is the law of `V((W_{⌊T_n t⌋}/B_{T_n})_{0 ≤ t ≤ 1})` under `P[· | W_{T_n} = -1]`.
Form: STRONGER: null-safe form (conditional MEASURES, no positivity hypothesis: both conditional measures
vanish together, Proposition 6.5 and `iidWalk_bridgeAtMark_ne_zero_iff`); any offspring law, any `B`
positive on `m ≥ 1` (a discrete identity, no attraction).  Measurability of both maps (needed for the
equation to have content): `measurable_rescaledLuka_treeSize`, `measurable_vervaatD_bridgeWalkPath`.
Proof: Proposition 6.5 (`prop_vervaatdiscrete_joint`), `vervaatD_stepPath_vervaat`,
`rescaledLuka_eq_stepPath` (`Coding.Defs`), summation over the countable set of words. -/
theorem cor_vervaatC (μ : PMF ℕ) (B : ℕ → ℝ) (hBpos : ∀ m, 1 ≤ m → 0 < B m) {n : ℕ}
    (hn : 1 ≤ n) :
    ((bienaymeLaw μ.toMeasure)[|leafCountEvent n]).map
        (fun τ => rescaledLuka (treeSize τ) (B (treeSize τ)) τ) =
      ((iidWalk μ)[|bridgeAtMark n]).map (fun ω => Skorokhod.vervaatD (bridgeWalkPath B n ω)) := by
  exact BGWLeaves.LeafLimits.VervaatLaw.cor_vervaatC μ B hBpos hn

/-- **Proof of Theorem 6.1, `eq:cvBr` and the time-reversal step (lines 2246-2312)**: under
`P[· | W_{T_n} = -1]`, `(W_{⌊T_n t⌋}/B_{T_n})_{0 ≤ t ≤ 1} → X^br` in law on `D([0,1])`.  Not a numbered
statement: it is the bridge invariance principle established inside the proof of 6.1.  Form: STRONGER
(any admissible norming) and RESTRICTED: added hypothesis `hnl` (line 1269; line 1996 announces the weaker
"`P[λ = n] > 0` for `n` large", see the header).  `bridgeWalkLaw μ (q k)` is the genuine conditional law
for `q k ≥ 1` (`iidWalk_bridgeAtMark_ne_zero_iff`, `coe_bridgeWalkLaw`).  Measurability:
`measurable_bridgeWalkPath`.  Proof: Lemma 6.10 (`lem_absolueC2`), Lemma 6.11 (signed local
estimate, needs `hnl`), Lemma 6.2 (`lem_CVf2_ii`), Proposition 6.9(ii), cut-offs off
the atoms, Lemma 5.7, Proposition 6.8 (`timeReversal_map`) and the terminal oscillation bound
(`Skorokhod.tendsto_of_tendsto_restrict_of_oscillation`).  As in Theorem 5.9(i), use a larger prefix
`b > a`, with time factor `b T_n/T_{bn}`, before restricting to `[0,a]`. -/
theorem tendsto_bridgeWalkPath {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ} (hc : IsCritical μ)
    (hne : μ 1 ≠ 1) (hap : Aperiodic μ)
    (hB : IsRealStableAttracted (realOffspringStepLaw μ) θ B)
    (hnl : ¬ IsLatticeLaw (etaLaw μ)) {q : ℕ → ℕ}
    (hqtop : Tendsto q atTop atTop) (hq : ∀ k, LeafAdmissible μ (q k)) :
    Tendsto (fun k => (bridgeWalkLaw μ (q k)).map (bridgeWalkPath B (q k)))
      atTop (𝓝 (stableBridgeLaw θ)) := by
  exact BGWLeaves.LeafLimits.Bridge.tendsto_bridgeWalkPath hc hne hap hB hnl hqtop hq

/-- **Theorem 6.1 (`thm:cvW3`, line 1986)**: for `τ_n ∼ P_μ[· | λ = n]`,
`(W_{⌊ζ t⌋}(τ_n)/B_ζ)_{0 ≤ t ≤ 1} → X^exc` (law of `X` under `N(· | ζ = 1)`, `levyExcLaw θ`) in law on
`D([0,1])`.  Form: STRONGER (any admissible norming) and RESTRICTED: added hypothesis `hnl` (line 1269;
the §6 text, lines 1996-1997, assumes only the weaker "`P[λ = n] > 0` for `n` large"; `hnl` is a
sufficient restriction).  Measurability: `measurable_rescaledLuka_treeSize`.
Proof, given `tendsto_bridgeWalkPath`: Corollary 6.7, the continuous mapping theorem with
Proposition 6.9(i) (`prop_bridge_i`); positivity of `B` on the relevant sizes is eventual (replace `B` on finitely many sizes,
which changes nothing in law asymptotically). -/
theorem thm_cvW3 {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hap : Aperiodic μ) (hB : IsRealStableAttracted (realOffspringStepLaw μ) θ B)
    (hnl : ¬ IsLatticeLaw (etaLaw μ)) {q : ℕ → ℕ}
    (hqtop : Tendsto q atTop atTop) (hq : ∀ k, LeafAdmissible μ (q k)) :
    Tendsto (fun k => (leafTreeLaw μ (q k)).map
        (fun τ => rescaledLuka (treeSize τ) (B (treeSize τ)) τ))
      atTop (𝓝 (levyExcLaw θ)) := by
  exact BGWLeaves.LeafLimits.Walk.thm_cvW3 hc hne hap hB hnl hqtop hq

/-! ## Introduction (II): the main theorem -/

/-- **Introduction (II) (line 254), the main theorem**: for `τ_n ∼ P_μ[· | λ = n]`,
`(W_{⌊ζ t⌋}(τ_n)/B_ζ, (B_ζ/ζ) C_{2ζt}(τ_n), (B_ζ/ζ) H_{ζt}(τ_n))_{0 ≤ t ≤ 1} → (X^exc, H^exc, H^exc)`
JOINTLY, in law on `D([0,1]) × C([0,1]) × C([0,1])`, with `(X^exc, H^exc)` the pair `(X, H)` under
`N(· | ζ = 1)` (`excTripleLaw θ`).  The product carrier `D × C × C` is the natural reading of the printed
display (which does not say which topology on triples) and is equivalent to `D(ℝ³)` here since the last
two coordinates are continuous.  Form: STRONGER than printed (any admissible norming `B`) and
RESTRICTED: added hypothesis `hnl` (line 1269); the printed generality (no `hnl`) is
`intro_II_general`, NOT covered by this statement.  Measurability: `measurable_codingTriple`.
Proof (joint convergence): the walk marginal is 6.1, the (contour, height) marginal is 5.9(ii);
the JOINT law on `[0,a]` comes from Lemma 5.8 (the pair (W, H) jointly) and the contour-height comparison
`eq:HC`; the extension of the joint law to `[0,1]` needs the terminal controls of both proofs at once and
the identification of the limit through the a.s. continuity of `X^exc` at `1` (BGW's terminal
oscillation control on `D(ℝ × ℝ²)` via `prodWithCont`, `tendsto_map_splitProdWithCont`).  The printed
proof gives the walk marginal; the joint statement needs this coupling argument. -/
theorem intro_II {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hap : Aperiodic μ) (hB : IsRealStableAttracted (realOffspringStepLaw μ) θ B)
    (hnl : ¬ IsLatticeLaw (etaLaw μ)) {q : ℕ → ℕ}
    (hqtop : Tendsto q atTop atTop) (hq : ∀ k, LeafAdmissible μ (q k)) :
    Tendsto (fun k => (leafTreeLaw μ (q k)).map (codingTriple B)) atTop (𝓝 (excTripleLaw θ)) := by
  exact BGWLeaves.LeafLimits.Joint.intro_II hc hne hap hB hnl hqtop hq

/-- **Introduction (II) (line 254), canonical-norming, non-lattice corollary**: with the corrected
norming `B_n = norming (stepLaw μ) θ n` (corrections 1 and 2 of `FORMALIZATION_REPORT.md`), which is
eventually positive and tends to `∞`, along ALL `n → ∞` (under `hnl` every
large `n` is admissible, and `leafTreeLaw` is junk at the finitely many others).
Form: RESTRICTED corollary, NOT the printed generality: it adds `hnl` (line 1269), uses all sufficiently
large sizes, and supplies an eventually positive canonical sequence, whereas line 254 promises a positive
sequence and convergence along the attainable sizes without `hnl` (the printed generality is
`intro_II_general`, `BGWLeaves.LeafLimitsGeneral`).  Proof: from `intro_II`,
`isRealStableAttracted_norming`, `eventually_leafAdmissible`. -/
theorem intro_II_canonical {μ : PMF ℕ} {θ : ℝ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hap : Aperiodic μ) (hDA : ∃ a, StableDomain μ θ a) (hnl : ¬ IsLatticeLaw (etaLaw μ)) :
    (∀ᶠ n in atTop, 0 < norming (stepLaw μ) θ n) ∧
      Tendsto (norming (stepLaw μ) θ) atTop atTop ∧
      Tendsto (fun n : ℕ => (leafTreeLaw μ n).map (codingTriple (norming (stepLaw μ) θ)))
        atTop (𝓝 (excTripleLaw θ)) := by
  exact BGWLeaves.LeafLimits.Joint.intro_II_canonical hc hne hap hDA hnl

/-- **Introduction, GHP claim (lines 326-328)**, with the uniform measure on the LEAVES (the reading that
uses Corollary 3.3; the vertex-measure reading is `cvG_GHP`): `τ_n` with graph distance times
`μ₀^{1-1/θ} B_n/n` and the uniform leaf measure converges in law, rooted measured GHP, to the stable tree
with its mass measure.  Form: an explicit INTERPRETATION of the printed claim (which does not name the
measure), STRONGER (any admissible norming) and RESTRICTED: added hypothesis `hnl` (line 1269).
Measurability: `measurable_scaledLeafTreeGHP`.
Proof: BGW `LeafMeasure.tendsto_rooted_leaf_laws_of_contour_of_top` with `hleaf` from
`tendsto_leafIndex_discrepancy`, `hratio` from `tendsto_treeSize_div_leaf`, `hlim` from 5.9(ii)
and 5.10.  That theorem's `hlim` is on `contourFunction` (clock
`2(ζ-1)`) whereas `rem_changement` gives the paper clock `2ζ` (adapter: BGW
`tendsto_map_contour_of_tendsto_map_paperContour`); it requires `0 < b n` for ALL `n` (modify finitely
many `k`). -/
theorem intro_GHP_leaf {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hap : Aperiodic μ) (hB : IsRealStableAttracted (realOffspringStepLaw μ) θ B)
    (hnl : ¬ IsLatticeLaw (etaLaw μ)) {q : ℕ → ℕ}
    (hqtop : Tendsto q atTop atTop) (hq : ∀ k, LeafAdmissible μ (q k)) :
    Tendsto (fun k => (leafTreeLaw μ (q k)).map
        (scaledLeafTreeGHP ((μ 0).toReal ^ (1 - 1 / θ) * B (q k) / q k)))
      atTop (𝓝 (((excLaw θ).map Prod.snd).map ContinuumTrees.Coding.rootedMeasuredGHSpace)) := by
  exact BGWLeaves.LeafLimits.Trees.intro_GHP_leaf hc hne hap hB hnl hqtop hq

end BGWLeaves
