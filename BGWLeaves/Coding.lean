module

public import BGWLeaves.Coding.Defs
public import BGWLeaves.Conditioning.Defs
public import BGWLeaves.LeafMass
public import BGWLeaves.StableAnalysis
public import BGW.StableTrees.RealAttraction
public import BGW.StableTrees.TailPairBasic
public import BGW.StableTrees.ExactContourPaths
public import BGW.StableTrees.NonmonotoneNorming
public import BGW.StableTrees.JointExcursion
public import BGW.Skorokhod.ExitPartition
public import BGW.Skorokhod.VervaatStep
public import BGW.Tree.DFS
public import BGW.Tree.Height
public import BGW.Tree.Excursion
public import BGW.StableTrees.Defs
public import BGW.Tree
public import BGWLeaves.StableAnalysis.Defs
import BGWLeaves.Coding.Proof

/-!
# Tranche 2, package M11 `Coding`: the results still to be proved

Source: arXiv:1110.2163v4 (`.orchestration/t2-arch/paper_utf8.tex` line numbers): the proposition of
line 515 (`eq:Hmes`), the coding claims of the Introduction (`intro:enc`, lines 226-232 and 496), the
admissibility of the leaf-conditioned laws of Introduction (II) (line 254, through Theorem 3.1(ii)), and
the norming of `(H_θ)`.

Each declaration here is a statement audited for freezing (audit A, `.orchestration/t2-audit-a`); its
proof is to be supplied in the provider modules `BGWLeaves.Coding.*` (imported through
`BGWLeaves.Coding.Proof`).  Definitions and PROVED bridges (`coe_leafTreeLaw`, the identifications of
`rescaledLuka`, `rescaledHeight`, `rescaledContour` with BGW's path maps, `rescaledLuka_eq_stepPath`, and
the measurability of every coding map) are in `BGWLeaves.Coding.Defs`.

Layout.
* The proposition of line 515 and `intro:enc` (provider `Discrete`): `prop_Hmes`,
  `intro_enc_lukasiewicz_end`, `intro_enc_lukasiewicz_injective`.
* Non-vacuity of the leaf-conditioned statements (provider `Admissible`): `infinite_leafAdmissible`,
  `exists_seq_leafAdmissible`, `eventually_leafAdmissible`.
* The norming (provider `Norming`): `isRealStableAttracted_norming`,
  `stableDomain_of_isRealStableAttracted`.
-/

@[expose] public section

namespace BGWLeaves

open MeasureTheory ProbabilityTheory Filter BGW
open BGW.StableTrees BGW.LocallyFinite BGWLeaves.StableAnalysis
open scoped ENNReal NNReal Topology

/-! ## The proposition of line 515 and the coding claims -/

/-- **The proposition of line 515 (`eq:Hmes`)**, printed form: for `0 ≤ n < ζ(τ)`,
`H_n(τ) = #{0 ≤ j < n : W_j(τ) = inf_{j ≤ k ≤ n} W_k(τ)}`; "`W_j` is the infimum over `[j,n]`" is
written `∀ k ∈ [j,n], W_j ≤ W_k` (equivalent: the infimum of a finite set is attained).
`t.height i = |u(i)|`, `t.lukasiewicz j = W_j(t)`.  Form: PRINTED.  No added hypothesis.
ROUTINE: this is `BGW.PlaneTree.height_eq_card_recordMin`. -/
theorem prop_Hmes (t : PlaneTree) (i : Fin t.size) :
    t.height i = ((Finset.range i.val).filter
      (fun j => ∀ k, j ≤ k → k ≤ i.val → t.lukasiewicz j ≤ t.lukasiewicz k)).card := by
  exact BGWLeaves.Coding.Discrete.prop_Hmes t i

/-- **`intro:enc` (line 496)**: "necessarily `W_{ζ(τ)}(τ) = -1`".  Form: PRINTED.  ROUTINE
(`PlaneTree.lukasiewicz`, `sum_degrees_add_one`). -/
theorem intro_enc_lukasiewicz_end (t : PlaneTree) : t.lukasiewicz t.size = -1 := by
  exact BGWLeaves.Coding.Discrete.intro_enc_lukasiewicz_end t

/-- **`intro:enc` (lines 226-232)**: the Łukasiewicz path determines the tree (the increment word
`(W_1, W_2 - W_1, …, W_ζ - W_{ζ-1})` is injective).  Form: PRINTED, PARTIAL: DOCUMENTED OMISSION (audit A,
m8): the printed claim is that each of the three codings `W`, `C`, `H` determines `τ`; only the claim
for `W` is stated, because no proof of the tranche uses the claims for `C` and `H`.
ROUTINE: `BGW.PlaneTree.increments_injective`. -/
theorem intro_enc_lukasiewicz_injective :
    Function.Injective (fun t : PlaneTree => t.increments) := by
  exact BGWLeaves.Coding.Discrete.intro_enc_lukasiewicz_injective

/-! ## Non-vacuity of the leaf-conditioned statements -/

/-- Under `(H_θ)` (spelled out as in tranche 1) the set of `n` with `P_μ[λ = n] > 0` is infinite.
Not printed (non-vacuity of the statements "along the `n` with `P_μ[λ = n] > 0`" of Introduction (II),
line 254).  ROUTINE: Theorem 3.1(ii) (`ltn_ii_tendsto`, tranche 1), along `g ∣ n - 1`. -/
theorem infinite_leafAdmissible {μ : PMF ℕ} {θ : ℝ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hap : Aperiodic μ) (hDA : ∃ a, StableDomain μ θ a) :
    {n : ℕ | LeafAdmissible μ n}.Infinite := by
  exact BGWLeaves.Coding.Admissible.infinite_leafAdmissible hc hne hap hDA

/-- Sequence form of `infinite_leafAdmissible` (the hypothesis shape `hqtop`, `hq` of every
leaf-conditioned convergence of packages M13 and M14).  Not printed.  ROUTINE. -/
theorem exists_seq_leafAdmissible {μ : PMF ℕ} {θ : ℝ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hap : Aperiodic μ) (hDA : ∃ a, StableDomain μ θ a) :
    ∃ q : ℕ → ℕ, Tendsto q atTop atTop ∧ ∀ k, LeafAdmissible μ (q k) := by
  exact BGWLeaves.Coding.Admissible.exists_seq_leafAdmissible hc hne hap hDA

/-- Under the §5 standing assumption (line 1269: `supp μ ∖ {0}` non-lattice, written
`¬ IsLatticeLaw (etaLaw μ)` as in tranche 1) every large `n` is admissible: this is the "so that
`P[λ = n] > 0` for `n` large" of line 1269.  Form: PRINTED claim of line 1269.  ROUTINE: Theorem 3.1(ii)
with `g = 1` (`hnl` forces `gcd(supp(K - 1 | K ≥ 1)) = 1`). -/
theorem eventually_leafAdmissible {μ : PMF ℕ} {θ : ℝ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hap : Aperiodic μ) (hDA : ∃ a, StableDomain μ θ a) (hnl : ¬ IsLatticeLaw (etaLaw μ)) :
    ∀ᶠ n in atTop, LeafAdmissible μ n := by
  exact BGWLeaves.Coding.Admissible.eventually_leafAdmissible hc hne hap hDA hnl

/-! ## The norming: BGW's admissible normings versus the corrected `norming` of tranche 1 -/

/-- The corrected norming `B_n = norming (stepLaw μ) θ n` of tranche 1 (R2, R4) is an admissible norming
in BGW's sense.  Not printed (glue between the two formalizations of `(H_θ)`).  The hypothesis
`hne : μ 1 ≠ 1` is not needed by the proof (only `hc`, through `mean_stepLaw`); it is kept for
uniformity with the other statements (audit A, m4).
ROUTINE+: `locallimit_i` + `mean_stepLaw` give tranche 1's
`IsStableAttracted (stepLaw μ) θ 0 (norming …)`; tranche 1's `BGWLeaves.StableAnalysis.{intWalk, norming,
IsStableAttracted}` and BGW's `BGW.StableTrees.Attraction.*` are two copies of the same definitions,
identified field by field (the two `intWalk` by a `funext` induction); then BGW's public
`Attraction.IsStableAttracted.isRealStableAttracted`, and `realOffspringStepLaw μ = castLaw (stepLaw μ)` by
definition. -/
theorem isRealStableAttracted_norming {μ : PMF ℕ} {θ : ℝ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hDA : ∃ a, StableDomain μ θ a) :
    IsRealStableAttracted (realOffspringStepLaw μ) θ (norming (stepLaw μ) θ) := by
  exact BGWLeaves.Coding.Norming.isRealStableAttracted_norming hc hne hDA

/-- Conversely an admissible norming gives `(H_θ)(ii)` in tranche 1's form and is equivalent to the
corrected norming.  Not printed (glue).
ROUTINE+: BOTH BGW helpers `isStableAttracted_of_isRealStableAttracted` and
`exists_stableDomain_norming_ratio` (`NonmonotoneNorming.lean:37, 59`) are `private` (audit A, m4; Sol
audit): re-derive the first from the public `sumLaw_castLaw`, `integral_exp_neg_mul_stableLaw` and
`eq_stableLaw_of_laplace`, then `IsStableAttracted.exists_stableDomain`; the ratio `B/norming → 1` from
tranche 1's `norming_isEquivalent` (the two copies of the attraction definitions are identified as in
`isRealStableAttracted_norming`). -/
theorem stableDomain_of_isRealStableAttracted {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ}
    (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hB : IsRealStableAttracted (realOffspringStepLaw μ) θ B) :
    (∃ a, StableDomain μ θ a) ∧ Tendsto (fun n => B n / norming (stepLaw μ) θ n) atTop (𝓝 1) := by
  exact BGWLeaves.Coding.Norming.stableDomain_of_isRealStableAttracted hc hne hB

end BGWLeaves
