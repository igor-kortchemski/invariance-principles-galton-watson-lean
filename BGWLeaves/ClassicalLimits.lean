module

public import BGWLeaves.ClassicalLimits.Defs
public import BGWLeaves.Coding.Defs
public import BGWLeaves.Conditioning.Defs
public import BGWLeaves.Vervaat.Defs
public import BGWLeaves.LocalEstimates.Defs
public import BGWLeaves.StableAnalysis
public import BGW.StableTrees.RealAttraction
public import BGW.StableTrees.ExactContourPaths
public import BGW.StableTrees.TailPairBasic
public import BGW.StableTrees.NonmonotoneNorming
public import BGW.StableTrees.JointExcursion
public import BGW.StableTrees.GammaIdentity
public import BGW.StableTrees.UnitExcursionLaw
public import BGW.StableTrees.UnitExcursionLawBasic
public import BGW.StableTrees.ExcursionMeasureBasic
public import BGW.StableTrees.BrownianPair
public import BGW.StableTrees.StableLaw
public import BGW.StableTrees.StableProcessLaw
public import BGW.StableTrees.StableProcessMarkov
public import BGW.StableTrees.StableProcessBrownian
public import BGW.StableTrees.StableProcessNoNegativeJumps
public import BGW.StableTrees.ExcursionLifetimeTail
public import BGW.StableTrees.VervaatIto
public import BGW.StableTrees.StableBridgeMinimum
public import BGW.StableTrees.StableBridgeClosed
public import BGW.StableTrees.BridgeProjective
public import BGW.StableTrees.BridgeProjectiveClose
public import BGW.StableTrees.KendallAdapter
public import BGW.ContinuumTrees.BrownianD
public import BGW.ContinuumTrees.VervaatBridge
public import BGW.Skorokhod.Scaling
public import BGW.Skorokhod.ScalingContinuous
public import BGW.Skorokhod.ExitPartition
public import BGW.Skorokhod.Vervaat
public import BGW.Skorokhod.VervaatStep
public import BGW.Skorokhod.VervaatRotate
public import BGW.StableTrees.Defs
public import BGW.StableTrees.ForestLocalLimitDefs
public import BGW.StableTrees.DiscreteForestTreeLaws
public import BGW.StableTrees.Scalar.Density
public import BGW.ContinuumTrees.ExcursionCarrier
public import BGW.Skorokhod.Basic
public import BGW.Skorokhod.Measurable
public import BGW.Skorokhod.Restrict
public import BGW.Skorokhod.Continuous
public import BGW.LocallyFinite.Basic
public import BGWLeaves.StableAnalysis.Defs
import BGWLeaves.ClassicalLimits.Proof

/-!
# Tranche 2, package M12 `ClassicalLimits`: the cited results in the paper's form

Source: arXiv:1110.2163v4 (`.orchestration/t2-arch/paper_utf8.tex` line numbers): Theorem 4.1
(Duquesne, `thm:cv1`, line 1123), Remark 4.2 (line 1134), the objects of §5.1 (lines 1286-1353),
Theorem 5.1 (`thm:cvW`, line 1370), Proposition 5.3 (`prop:Gamma`, line 1402), Lemma 5.7
(`lem:CVproba`, line 1487), Lemma 6.2(ii) (`lem:CVf2`, line 2009), Definition 6.6 (line 2116),
Proposition 6.9 (`prop:bridge`, line 2160), and the C33.5 glue between `BGWLeaves.vervaat` and BGW's
rotation.

The cited results are PROVED in `../BGW-formalization`; each is stated here once, in the paper's form, as
a theorem to be proved from BGW (no cited-input `Prop`).  Every statement uses BGW's objects directly
(`exactTreeLaw`, `tailTreeLaw`, `treeContourPath`, `treePairPath`, `excLaw`, `tailExcLaw`,
`levyExcLaw`, `stableBridgeLaw`, `stableProcessLaw`, `vervaatD`).  Audited by audit A
(`.orchestration/t2-audit-a`).

Norming: every limit statement is for an ARBITRARY admissible norming `B`
(`IsRealStableAttracted (realOffspringStepLaw μ) θ B`, BGW's `…_of_attracted` theorems), which is
STRONGER than the paper's "the" sequence `B_n`; the corrected norming of tranche 1 is one of them
(`isRealStableAttracted_norming`, package M11).

Measurability: the maps pushed forward here are measurable by BGW (`measurable_treeContourPath`,
`measurable_treePairPath`, `measurable_timeSpaceScale_fixed`, `measurable_vervaatD`, `measurable_restrict`,
`measurable_restrictPair`, `measurable_excursionPair`, `measurable_eval`) or by the proved bridges of
`BGWLeaves.ClassicalLimits.Defs` (`measurable_timeSpaceScale`, `measurable_timeSpaceScaleC`,
`measurable_leafClockPath`).

Layout.
* One-line consequences of BGW (provider `Cited`): `thm_cv1`, `thm_cv1_printed`, `rem_cv1`,
  `height_exc_endpoints`, the §5.1 facts `sec51_*`, `thm_cvW`, `prop_Gamma`, the kernel identities
  `pDens_eq_stableDensityAt`, `qKernel_eq_kernel`, `sizeTailKernel_eq_kernel`, `gammaA_eq_paper`,
  `def_vervaatC`, `prop_bridge_i`, `prop_bridge_ii`, `vervaat_eq_rotate_vervaatIndex`.
* Lemma 5.7 (provider `Perturbation`): `lem_CVproba`, `lem_CVproba_pair`.
* Lemma 6.2(ii) (provider `WalkClock`): `lem_CVf2_ii`.
-/

@[expose] public section

namespace BGWLeaves

open MeasureTheory ProbabilityTheory Filter BGW
open BGW.StableTrees BGW.LocallyFinite BGWLeaves.StableAnalysis
open scoped ENNReal NNReal Topology

/-! ## 4.1 Duquesne's theorem and Remark 4.2 -/

/-- **Theorem 4.1 (Duquesne, `thm:cv1`, line 1123)**: for `τ_n ∼ P_μ[· | ζ = n]`,
`((B_n/n) C_{2nt}(τ_n))_{0 ≤ t ≤ 1} → H^exc` in law in `C([0,1], ℝ)`.
Form: STRONGER than printed: any admissible norming `B`; no aperiodicity; along any sequence of sizes
`q k → ∞` with `P_μ[ζ = q k] > 0` (BGW `Admissible`).  No added hypothesis.
ROUTINE: second marginal of BGW `ExactContour.tendsto_exactHeightContourLaw_of_attracted` (C29.a1). -/
theorem thm_cv1 {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hB : IsRealStableAttracted (realOffspringStepLaw μ) θ B) {q : ℕ → ℕ}
    (hqtop : Tendsto q atTop atTop) (hq : ∀ k, Admissible μ (q k)) :
    Tendsto (fun k => (DiscreteForest.exactTreeLaw μ (q k)).map
        (ExactContour.treeContourPath B (q k) 1)) atTop (𝓝 ((excLaw θ).map Prod.snd)) := by
  exact BGWLeaves.ClassicalLimits.Cited.thm_cv1 hc hne hB hqtop hq

/-- **Theorem 4.1 (`thm:cv1`, line 1123), printed form**: under `(H_θ)` (spelled out as in tranche 1)
and with the corrected norming `B_n = norming (stepLaw μ) θ n` of tranche 1 (R2, R4), along ALL `n → ∞`
(aperiodicity makes every large `n` admissible; `exactTreeLaw` is a junk Dirac law at the finitely many
others).  Form: PRINTED, with the CORRECTED norming of tranche 1.  ROUTINE from `thm_cv1`,
`isRealStableAttracted_norming` (M11) and `sizeEvent_ne_zero_eventually`. -/
theorem thm_cv1_printed {μ : PMF ℕ} {θ : ℝ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hap : Aperiodic μ) (hDA : ∃ a, StableDomain μ θ a) :
    Tendsto (fun n : ℕ => (DiscreteForest.exactTreeLaw μ n).map
        (ExactContour.treeContourPath (norming (stepLaw μ) θ) n 1)) atTop
      (𝓝 ((excLaw θ).map Prod.snd)) := by
  exact BGWLeaves.ClassicalLimits.Cited.thm_cv1_printed hc hne hap hDA

/-- **Remark 4.2 (line 1134)**: the limit `H^exc` of Theorem 4.1 is the height process under
`N(· | ζ = 1)` (the second coordinate of `excursionPair` under `unitExcursionLaw`).  Form: PRINTED.
ROUTINE (definitional, `Measure.map_map`). -/
theorem rem_cv1 (θ : ℝ) :
    (excLaw θ).map Prod.snd = (unitExcursionLaw θ).map (fun e => (excursionPair θ 1 e).2) := by
  exact BGWLeaves.ClassicalLimits.Cited.rem_cv1 θ

/-- **Introduction, lines 237-240, and §5.1 (line 1351)**: `H^exc` is a random continuous function on
`[0,1]` that vanishes at `0` and `1` and is positive on `(0,1)`.  Form: PRINTED.  ROUTINE: BGW
`excLaw_height_endpoints_pos` (C26.H5). -/
theorem height_exc_endpoints {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ h ∂((excLaw θ).map Prod.snd).toMeasure,
      h ⟨0, le_rfl, zero_le_one⟩ = 0 ∧ h ⟨1, zero_le_one, le_rfl⟩ = 0 ∧
        ∀ t : Set.Icc (0 : ℝ) 1, 0 < (t : ℝ) → (t : ℝ) < 1 → 0 < h t := by
  exact BGWLeaves.ClassicalLimits.Cited.height_exc_endpoints hθ

/-! ## §5.1 The stable process and its normalized excursion -/

/-- **§5.1, `eq:X` (line 1301)**: `E[exp(-λ X_t)] = exp(t λ^θ)` for `λ ≥ 0`, `0 < t ≤ T`.
Form: PRINTED.  ROUTINE: BGW `map_eval_stableProcessLaw`, `integral_exp_neg_mul_stableLawAt` (C15, C16). -/
theorem sec51_laplace {θ T : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (hT : 0 < T) (t : Set.Icc (0 : ℝ) T)
    (ht : 0 < (t : ℝ)) {lam : ℝ} (hlam : 0 ≤ lam) :
    ∫ f, Real.exp (-lam * f t) ∂(stableProcessLaw θ T).toMeasure = Real.exp (t * lam ^ θ) := by
  exact BGWLeaves.ClassicalLimits.Cited.sec51_laplace hθ hT t ht hlam

/-- **§5.1 (line 1306)**: scaling, `(c^{-1/θ} X_{ct})_{t ≤ T}` has the law of `(X_t)_{t ≤ T}`.
Form: PRINTED.  ROUTINE: BGW `stableProcessLaw_scaling` (C16.P2). -/
theorem sec51_scaling {θ T : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (hT : 0 < T) {c : ℝ} (hc : 0 < c) :
    (stableProcessLaw θ (c * T)).map
        (fun f : Skorokhod.D (c * T) ℝ => Skorokhod.timeSpaceScale T (mul_pos hc hT).le
          (f, c ^ (-(1 / θ)), (⟨c, Set.mem_Ioi.mpr hc⟩ : Set.Ioi (0 : ℝ)))) =
      stableProcessLaw θ T := by
  exact BGWLeaves.ClassicalLimits.Cited.sec51_scaling hθ hT hc

/-- **§5.1 (lines 1308-1310)**: `p_t = stableDensityAt θ t` is the density of `X_t`, for `0 < t ≤ T`.
Form: PRINTED (the existence of the density `p_t` of `X_t`).  This statement REPLACES the draft's
`eq_scaling` (audit A, m2): the printed `eq:scaling` (line 1310), `p_{λs}(x) = λ^{-1/θ} p_s(x λ^{-1/θ})`,
holds for every `θ` by the definition of BGW's `stableDensityAt θ t x = t^{-1/θ} p_1(t^{-1/θ} x)`, so it
carries no content until `stableDensityAt θ t` is identified with the density of `X_t`, which is this
statement (audit A, m2: the replacement of the redundant restatement `eq_scaling` is an allowed change approved by
the coordinator; owner decision Q6 keeps the §5.1 restatements, and `sec51_density` is one of them).
ROUTINE: BGW `map_eval_stableProcessLaw` and `stableLawAt_eq_withDensity`. -/
theorem sec51_density {θ T : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (hT : 0 < T) (t : Set.Icc (0 : ℝ) T)
    (ht : 0 < (t : ℝ)) :
    (stableProcessLaw θ T : Measure (Skorokhod.D T ℝ)).map (fun f => f t) =
      volume.withDensity (fun x => ENNReal.ofReal (stableDensityAt θ t x)) := by
  exact BGWLeaves.ClassicalLimits.Cited.sec51_density hθ hT t ht

/-- **§5.1 (line 1314)**: `X` has no negative jumps (hence `I` is continuous).  Form: PRINTED.
ROUTINE: BGW `ae_leftLim_le_stableProcessLaw` (C16.P4). -/
theorem sec51_noNegativeJumps {θ T : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (hT : 0 < T) :
    ∀ᵐ f : Skorokhod.D T ℝ ∂(stableProcessLaw θ T).toMeasure,
      ∀ t : Set.Icc (0 : ℝ) T, Function.leftLim (f : Set.Icc (0 : ℝ) T → ℝ) t ≤ f t := by
  exact BGWLeaves.ClassicalLimits.Cited.sec51_noNegativeJumps hθ hT

/-- **§5.1 (line 1304)**: for `θ = 2`, `X` is `√2` times standard Brownian motion.  Form: PRINTED.
ROUTINE: BGW `stableProcessLaw_two` (C19.1). -/
theorem sec51_two_process {T : ℝ} (hT : 0 < T) :
    stableProcessLaw 2 T = ContinuumTrees.BrownianD.wienerD (NNReal.sqrt 2) T := by
  exact BGWLeaves.ClassicalLimits.Cited.sec51_two_process hT

/-- **§5.1 (line 1333)**: `N(ζ > t) ∈ (0, ∞)` for `t > 0` (explicitly `t^{-1/θ}/Γ(1 - 1/θ)`).
Form: PRINTED.  ROUTINE: BGW `excursionMeasure_lifetime_tail` (C21.3). -/
theorem sec51_lifetime_tail {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {t : ℝ} (ht : 0 < t) :
    0 < excursionMeasure θ {e : Excursion | t < (e.lifetime : ℝ)} ∧
      excursionMeasure θ {e : Excursion | t < (e.lifetime : ℝ)} < ⊤ := by
  exact BGWLeaves.ClassicalLimits.Cited.sec51_lifetime_tail hθ ht

/-- **Normalized excursion: endpoints and positivity** (BGW C22.E1).  NOT PRINTED as such (audit A, m5):
lines 1336-1337 only say that the normalized excursion has unit lifetime, and the excursion space of
line 1322 only asks `ω ≥ 0`, `ω(0) = 0`, `ζ = sup{s : ω(s) > 0}`; positivity on `(0,1)`, `X^exc_1 = 0`
and the left limit `0` at `1` are the classical facts used in the proofs of Lemma 5.8 and
Proposition 6.9.  Form: classical fact, stated for its use.  ROUTINE: BGW `levyExcLaw_endpoints_pos`. -/
theorem sec51_exc_endpoints {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ x : Skorokhod.D 1 ℝ ∂(levyExcLaw θ).toMeasure,
      x ⟨0, le_rfl, zero_le_one⟩ = 0 ∧
        (∀ t : Set.Icc (0 : ℝ) 1, 0 < (t : ℝ) → (t : ℝ) < 1 → 0 < x t) ∧
        x ⟨1, zero_le_one, le_rfl⟩ = 0 ∧
        Function.leftLim (x : Set.Icc (0 : ℝ) 1 → ℝ) ⟨1, zero_le_one, le_rfl⟩ = 0 := by
  exact BGWLeaves.ClassicalLimits.Cited.sec51_exc_endpoints hθ

/-- **§5.1 (lines 1338, 1345) and Remark 4.6 input**: for `θ = 2`, `(X^exc, H^exc) = (√2 e, √2 e)`
in law, `e` the normalized Brownian excursion (`VervaatBridge.law`); in particular "`H = X`"
under `N(· | ζ = 1)`.  Form: CORRECTED reading: the printed "`H = X`" for `θ = 2` should read
`H = X - I` (R14/N4), which is the same under `N`.  ROUTINE: BGW `BrownianIdentification.excLaw_two`
(C30.a2). -/
theorem sec51_two_exc :
    excLaw 2 = ContinuumTrees.VervaatBridge.law.map
      (fun e => (Skorokhod.ofContinuous (T := 1) (Real.sqrt 2 • e), Real.sqrt 2 • e)) := by
  exact BGWLeaves.ClassicalLimits.Cited.sec51_two_exc

/-! ## 5.1 Duquesne-Le Gall under `ζ ≥ n` -/

/-- **Theorem 5.1 (`thm:cvW`, line 1370)**: for `τ_n ∼ P_μ[· | ζ ≥ n]`,
`(W_{⌊nt⌋}(τ_n)/B_n, (B_n/n) H_{nt}(τ_n))_{0 ≤ t ≤ T}` converges in law in `D([0,T]) × C([0,T])` to
`(X_t, H_t)_{0 ≤ t ≤ T}` under `N(· | ζ > 1)` (`tailExcLaw θ T`).
Form: STRONGER and CORRECTED.  The printed display indexes the left side on `t ≥ 0` and the right side on
`[0,1]` (R7, N2); formalized on every horizon `T > 0` (the paper uses `T = 1`); for `T > 1` the limit is
`N(· | ζ > 1)` STOPPED AT ZERO after its lifetime (BGW `tailExcLaw` docstring), which matches the
discrete padding.  STRONGER: any admissible norming, no aperiodicity.  The paper attributes the joint
statement to Duquesne and Le Gall; the cited remark concerns only the height/contour, not the joint
`(W, H)` (N1, `CLASSICAL_THEORY_INPUTS.md`), which BGW proves (C28).  The walk coordinate stays at
`-1/B_n` after `ζ` (the paper extends it by `0`: difference `≤ 1/B_n`, BGW
`dist_treePrefixPath_closed_le`).  ROUTINE: BGW `TailPair.tendsto_tailPairLaw_of_attracted` (C28). -/
theorem thm_cvW {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hB : IsRealStableAttracted (realOffspringStepLaw μ) θ B) {T : ℝ≥0} (hT : 0 < T) :
    Tendsto (fun n : ℕ => (DiscreteForest.tailTreeLaw μ n).map (TailPair.treePairPath B n T))
      atTop (𝓝 (tailExcLaw θ T)) := by
  exact BGWLeaves.ClassicalLimits.Cited.thm_cvW hc hne hB hT

/-! ## 5.3 The `Γ_a` identity -/

/-- **Proposition 5.3 (`prop:Gamma`, line 1402)**: for `0 < a < 1` and `F` bounded measurable on
`D([0,a]) × C([0,a])`,
`N(F((X_t)_{t ≤ a}, (H_t)_{t ≤ a}) | ζ = 1) = N(F((X_t)_{t ≤ a}, (H_t)_{t ≤ a}) Γ_a(X_a) | ζ > 1)`.
Form: STRONGER and CORRECTED carrier: the printed space `D([0,a], ℝ²)` is replaced by `D([0,a]) × C([0,a])`
(R14/N15: the height is continuous; the product topology is the one used); `F` may be signed (printed:
`ℝ₊`).  `Γ_a = θ q_{1-a} / ∫_{1-a}^∞ q_s ds` is BGW's `gammaA` (`gammaA_eq_paper` below).  ROUTINE: BGW
`gamma_identity` (C24). -/
theorem prop_Gamma {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (a : ℝ≥0) (ha : a ∈ Set.Ioo (0 : ℝ≥0) 1)
    (F : Skorokhod.D (a : ℝ) ℝ × C(Set.Icc (0 : ℝ) a, ℝ) → ℝ) (hF : Measurable F)
    (hFb : ∃ C : ℝ, ∀ z, |F z| ≤ C) :
    ∫ z, F (restrictPair ha.2.le z) ∂(excLaw θ).toMeasure =
      ∫ z, F (restrictPair ha.2.le z) * gammaA θ a (evalEnd a (restrictPair ha.2.le z).1)
        ∂(tailExcLaw θ 1).toMeasure := by
  exact BGWLeaves.ClassicalLimits.Cited.prop_Gamma hθ a ha F hF hFb

/-- Tranche 1's density `BGWLeaves.pDens θ s x` is BGW's `stableDensityAt θ s x`, for all real
arguments.  Not printed (kernel glue, audit A m3).  ROUTINE (unfolding, `neg_div`, `mul_comm`). -/
theorem pDens_eq_stableDensityAt (θ s x : ℝ) : BGWLeaves.pDens θ s x = stableDensityAt θ s x := by
  exact BGWLeaves.ClassicalLimits.Cited.pDens_eq_stableDensityAt θ s x

/-- Tranche 1's kernel `q_s(x) = (x/s) p_s(-x)` (`BGWLeaves.qKernel`) is BGW's, for all real arguments.
Not printed (kernel glue, audit A m3).  ROUTINE. -/
theorem qKernel_eq_kernel (θ s x : ℝ) :
    BGWLeaves.qKernel θ s x = BGW.StableTrees.qKernel θ s x := by
  exact BGWLeaves.ClassicalLimits.Cited.qKernel_eq_kernel θ s x

/-- Tranche 1's `∫_s^∞ q_u(x) du` (`BGWLeaves.sizeTailKernel`) is BGW's, for all real arguments.
Not printed (kernel glue, audit A m3).  ROUTINE. -/
theorem sizeTailKernel_eq_kernel (θ s x : ℝ) :
    BGWLeaves.sizeTailKernel θ s x = BGW.StableTrees.sizeTailKernel θ s x := by
  exact BGWLeaves.ClassicalLimits.Cited.sizeTailKernel_eq_kernel θ s x

/-- BGW's `Γ_a` is the paper's `θ q_{1-a}(x) / ∫_{1-a}^∞ q_s(x) ds` (line 1402), written with tranche 1's
kernels `BGWLeaves.qKernel` and `BGWLeaves.sizeTailKernel` (`LocalEstimates/Defs.lean`); needed to plug
Lemma 5.5 (tranche 1, in the project's kernels) into Proposition 5.3 (BGW's kernel).  Form: the printed
definition of `Γ_a`, as a pointwise identity for ALL real `θ, a, x` (audit A, m3: the draft's hypotheses
`0 < a < 1`, `x > 0` were unused and are dropped).  ROUTINE (`gammaA` unfolds, then the two kernel
identities above). -/
theorem gammaA_eq_paper (θ a x : ℝ) :
    gammaA θ a x = θ * BGWLeaves.qKernel θ (1 - a) x / BGWLeaves.sizeTailKernel θ (1 - a) x := by
  exact BGWLeaves.ClassicalLimits.Cited.gammaA_eq_paper θ a x

/-! ## 5.7 Random time and space perturbation -/

/-- **Lemma 5.7 (`lem:CVproba`, line 1487)**: if `Z^n → Z` in law on `D([0,T], E)`, `Z` a.s. continuous
at `a ∈ (0,T)`, and the random factors `K_n ∈ E`, `S_n > 0` tend to `1` in probability, then
`(K_n Z^n_{S_n t})_{0 ≤ t ≤ a} → (Z_t)_{0 ≤ t ≤ a}` in law on `D([0,a], E)`.
Form: CORRECTED and STRONGER (R7, R14/N10).  Corrected: the printed conclusion has `ℝ` and `X` for `ℝ^d`
and `Z` (typo).  Stronger: the factor `K_n` acts through the ring structure of `E` (e.g.
`E = ℝ × ℝ` coordinatewise), which gives the separate per-coordinate factors that the proof of 5.9 needs
(N10), and `K_n` NEED NOT BE POSITIVE (printed: `K_n > 0`); the varying probability spaces `Ω n` replace
"random variables on one space".  The printed `D([0,∞))` is replaced by a finite horizon `T > a`
(enough for every use; BGW has no `D([0,∞))`); `S_n t` is clipped at `T` (`timeSpaceScale`).  The pair
`(W, H) ∈ D × C` of 5.1, 5.8, 5.9 is covered by the product variant `lem_CVproba_pair` (audit A, m7).
The pushed-forward map is measurable by `measurable_timeSpaceScale` (proved, `ClassicalLimits.Defs`).
ANALYSIS: BGW `tendsto_map_prodMk_of_tendsto_of_error` (C10.2), `continuousAt_timeSpaceScale` (C6.4),
`tendsto_map_of_ae_continuousAt` (C9). -/
theorem lem_CVproba {E : Type*} [NormedRing E] [MeasurableSpace E] [BorelSpace E]
    [TopologicalSpace.SeparableSpace E] {T a : ℝ} (ha : 0 < a) (haT : a < T)
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] (P : ∀ n, ProbabilityMeasure (Ω n))
    (Z : ∀ n, Ω n → Skorokhod.D T E) (K : ∀ n, Ω n → E) (S : ∀ n, Ω n → Set.Ioi (0 : ℝ))
    (hZm : ∀ n, Measurable (Z n)) (hKm : ∀ n, Measurable (K n))
    (hSm : ∀ n, Measurable (fun ω => ((S n ω : ℝ))))
    (L : ProbabilityMeasure (Skorokhod.D T E))
    (hZ : Tendsto (fun n => (P n).map (Z n)) atTop (𝓝 L))
    (hcont : ∀ᵐ f : Skorokhod.D T E ∂L.toMeasure,
      ContinuousAt (f : Set.Icc (0 : ℝ) T → E) ⟨a, ha.le, haT.le⟩)
    (hK : ∀ ε > 0, Tendsto (fun n => (P n).toMeasure.real {ω | ε < dist (K n ω) 1}) atTop (𝓝 0))
    (hS : ∀ ε > 0,
      Tendsto (fun n => (P n).toMeasure.real {ω | ε < dist ((S n ω : ℝ)) 1}) atTop (𝓝 0)) :
    Tendsto (fun n => (P n).map (fun ω =>
        Skorokhod.timeSpaceScale a (ha.le.trans haT.le) (Z n ω, K n ω, S n ω)))
      atTop (𝓝 (L.map (Skorokhod.restrict haT.le))) := by
  exact BGWLeaves.ClassicalLimits.Perturbation.lem_CVproba ha haT P Z K S hZm hKm hSm L hZ hcont hK hS

/-- **Lemma 5.7 (`lem:CVproba`, line 1487), pair form** for `(W, H) ∈ D([0,T]) × C([0,T])` (the carrier of
Theorem 5.1, used in the proof of Lemma 5.8, lines 1505-1560): if `Z^n = (X^n, Y^n) → Z` in law, the first
coordinate of `Z` is a.s. continuous at `a ∈ (0,T)`, and the factors `K_n = (K¹_n, K²_n) ∈ ℝ²`, `S_n > 0`
tend to `1` in probability, then `((K¹_n X^n_{S_n t}, K²_n Y^n_{S_n t}))_{0 ≤ t ≤ a} → Z|_{[0,a]}` in law
on `D([0,a]) × C([0,a])`.  NEW statement (audit A, m7; allowed change): the printed lemma is for
`D([0,∞), ℝ^d)`; the product carrier `D × C` replaces `D(ℝ²)` as in Proposition 5.3 (N15).  Form:
CORRECTED and STRONGER as `lem_CVproba` (signed factors, separate per-coordinate factors, finite horizon,
varying `Ω n`).  The pushed-forward map is measurable by `measurable_timeSpaceScale` and
`measurable_timeSpaceScaleC` (proved, `ClassicalLimits.Defs`).  ANALYSIS: as `lem_CVproba`, with BGW
`continuous_timeSpaceScaleC` for the continuous coordinate. -/
theorem lem_CVproba_pair {T a : ℝ≥0} (ha : 0 < a) (haT : a < T)
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] (P : ∀ n, ProbabilityMeasure (Ω n))
    (Z : ∀ n, Ω n → Skorokhod.D (T : ℝ) ℝ × C(Set.Icc (0 : ℝ) T, ℝ))
    (K : ∀ n, Ω n → ℝ × ℝ) (S : ∀ n, Ω n → Set.Ioi (0 : ℝ))
    (hZm : ∀ n, Measurable (Z n)) (hKm : ∀ n, Measurable (K n))
    (hSm : ∀ n, Measurable (fun ω => ((S n ω : ℝ))))
    (L : ProbabilityMeasure (Skorokhod.D (T : ℝ) ℝ × C(Set.Icc (0 : ℝ) T, ℝ)))
    (hZ : Tendsto (fun n => (P n).map (Z n)) atTop (𝓝 L))
    (hcont : ∀ᵐ z : Skorokhod.D (T : ℝ) ℝ × C(Set.Icc (0 : ℝ) T, ℝ) ∂L.toMeasure,
      ContinuousAt (z.1 : Set.Icc (0 : ℝ) T → ℝ)
        ⟨(a : ℝ), a.coe_nonneg, NNReal.coe_le_coe.2 haT.le⟩)
    (hK : ∀ ε > 0, Tendsto (fun n => (P n).toMeasure.real {ω | ε < dist (K n ω) 1}) atTop (𝓝 0))
    (hS : ∀ ε > 0,
      Tendsto (fun n => (P n).toMeasure.real {ω | ε < dist ((S n ω : ℝ)) 1}) atTop (𝓝 0)) :
    Tendsto (fun n => (P n).map (fun ω =>
        (Skorokhod.timeSpaceScale (a : ℝ) T.coe_nonneg ((Z n ω).1, (K n ω).1, S n ω),
          Skorokhod.timeSpaceScaleC (a : ℝ) T.coe_nonneg ((Z n ω).2, (K n ω).2, S n ω))))
      atTop (𝓝 (L.map (restrictPair haT.le))) := by
  exact BGWLeaves.ClassicalLimits.Perturbation.lem_CVproba_pair ha haT P Z K S hZm hKm hSm L hZ hcont hK hS

/-! ## 6.2(ii) The walk at the leaf clock -/

/-- **Lemma 6.2(ii) (`lem:CVf2`, line 2009)**: for every `a > 0`,
`(W_{⌊(t/a) T_{an}⌋} / B_{n/μ₀})_{0 ≤ t ≤ a} → (X_t)_{0 ≤ t ≤ a}` in law under `P` (`B_u = B_{⌊u⌋}`,
line 2002).  Form: STRONGER: any admissible norming `B`; no aperiodicity (the paper's `(H_θ)` includes
it).  No added hypothesis.  The pushed-forward map is measurable by `measurable_leafClockPath` (proved).
ANALYSIS (article side, C17.iii), route (audit A, m9): BGW's FCLT
`IsRealStableAttracted.tendsto_stepPathLaw` for `(W_{⌊nt⌋}/B_n)` on a horizon `T' > a/μ₀`; then
Lemma 5.7 (`lem_CVproba`) with the time factor `S_n = μ₀ T_{an}/(an) → 1` (Lemma 6.2(i), `lem_CVf2_i`,
tranche 1) and the space factor `K_n = B_n / B_{⌊n/μ₀⌋} → μ₀^{1/θ}` (`tendsto_norming_floor_ratio`), and
finally the scaling `sec51_scaling` with `c = 1/μ₀`.  (The horizon `T'` belongs to the proof, not to the
statement.) -/
theorem lem_CVf2_ii {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hB : IsRealStableAttracted (realOffspringStepLaw μ) θ B) {a : ℝ} (ha : 0 < a) :
    Tendsto (fun n : ℕ => (walkLawPM μ).map (leafClockPath (μ 0).toReal B n ha))
      atTop (𝓝 (stableProcessLaw θ a)) := by
  exact BGWLeaves.ClassicalLimits.WalkClock.lem_CVf2_ii hc hne hB ha

/-! ## 6.6 The continuous Vervaat transformation, 6.9 the stable bridge -/

/-- **Definition 6.6 (line 2116)**: on `D₀([0,1]) = {ω(0) = 0}`, BGW's `vervaatD` is the printed
`V`: with `g₁ = inf{t : ω(t-) ∧ ω(t) = inf ω}` (`vervaatTime`),
`V(ω)(t) = ω(g₁ + t) - inf ω` if `g₁ + t ≤ 1`, `ω(g₁ + t - 1) + ω(1) - inf ω` otherwise.  Form: PRINTED
(BGW's formula carries an extra `- ω(0)`, zero on `D₀`, hence the hypothesis `hf0`, which is the printed
domain `D₀`).  ROUTINE (unfolding). -/
theorem def_vervaatC (f : Skorokhod.D 1 ℝ) (hf0 : f ⟨0, le_rfl, zero_le_one⟩ = 0)
    (t : Set.Icc (0 : ℝ) 1) :
    Skorokhod.vervaatD f t =
      if (Skorokhod.vervaatTime f : ℝ) + t ≤ 1 then
        f (Set.projIcc 0 1 zero_le_one ((Skorokhod.vervaatTime f : ℝ) + t)) - ⨅ s, f s
      else
        f (Set.projIcc 0 1 zero_le_one ((Skorokhod.vervaatTime f : ℝ) + t - 1)) +
          f ⟨1, zero_le_one, le_rfl⟩ - ⨅ s, f s := by
  exact BGWLeaves.ClassicalLimits.Cited.def_vervaatC f hf0 t

/-- **Proposition 6.9(i) (`prop:bridge`, line 2161)**: `V` is a.s. continuous at `X^br`, and `V(X^br)`
has the law of `X^exc` under `N(· | ζ = 1)`.  Form: PRINTED (the printed proof is incomplete, R14/N5:
uniqueness of the minimum alone does not give continuity; BGW proves the statement with the extra
continuity of `X^br` at its minimum time and at `1`, C32, C34).  ROUTINE: BGW
`stableBridgeLaw_ae_continuousAt_vervaatD`, `VervaatIto.map_vervaatD_stableBridgeLaw` (C34, C35). -/
theorem prop_bridge_i {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    (∀ᵐ f ∂(stableBridgeLaw θ).toMeasure, ContinuousAt Skorokhod.vervaatD f) ∧
      (stableBridgeLaw θ).map Skorokhod.vervaatD = levyExcLaw θ := by
  exact BGWLeaves.ClassicalLimits.Cited.prop_bridge_i hθ

/-- **Proposition 6.9(ii) (line 2163)**: for `a ∈ (0,1)` and `F` bounded on `D([0,a])`,
`E[F(X^br_t; t ≤ a)] = E[F(X_t; t ≤ a) p_{1-a}(-X_a)/p_1(0)]`.  Form: STRONGER: `F` bounded measurable
(printed: bounded continuous).  The bridge law on `D([0,1])` is BGW's projective-limit construction
(R14/N6: the printed (ii) is the definition on `[0,a]`; existence on `[0,1]` with `X^br_{1-} = 0` is BGW
C31).  ROUTINE: BGW `integral_restrict_stableBridgeLaw` (C31.a(i)). -/
theorem prop_bridge_ii {θ a : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (ha : 0 < a) (ha1 : a < 1)
    {F : Skorokhod.D a ℝ → ℝ} (hF : Measurable F) (hFb : ∃ C : ℝ, ∀ x, |F x| ≤ C) :
    ∫ f, F (Skorokhod.restrict ha1.le f) ∂(stableBridgeLaw θ).toMeasure =
      ∫ g, F g * (stableDensityAt θ (1 - a) (-(g ⟨a, ha.le, le_rfl⟩)) /
        Scalar.stableDensity θ 0) ∂(stableProcessLaw θ a).toMeasure := by
  exact BGWLeaves.ClassicalLimits.Cited.prop_bridge_ii hθ ha ha1 hF hFb

/-- **C33.5 glue**: tranche 1's discrete Vervaat transform (Definition 6.3, `BGWLeaves.vervaat`) is
BGW's rotation `x.rotate (vervaatIndex x)` (the two index definitions are the same `sInf`;
`cyclicShift_eq_rotate`).  Not printed (glue between the two formalizations).  ROUTINE. -/
theorem vervaat_eq_rotate_vervaatIndex (x : List ℤ) :
    vervaat x = x.rotate (Skorokhod.vervaatIndex x) := by
  exact BGWLeaves.ClassicalLimits.Cited.vervaat_eq_rotate_vervaatIndex x

end BGWLeaves
