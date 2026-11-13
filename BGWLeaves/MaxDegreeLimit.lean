module

public import BGWLeaves.MaxDegreeLimit.Defs
public import BGWLeaves.Coding.Defs
public import BGWLeaves.Conditioning.Defs
public import BGWLeaves.Vervaat.Defs
public import BGWLeaves.StableAnalysis
public import BGW.StableTrees.RealAttraction
public import BGW.StableTrees.UnitExcursionLawBasic
public import BGW.StableTrees.ExcursionJump
public import BGW.Skorokhod.Jump
public import Mathlib.MeasureTheory.Measure.DiracProba
public import BGW.StableTrees.Defs
public import BGW.Skorokhod.Basic
public import BGW.Skorokhod.Measurable
public import BGW.LocallyFinite.Basic
public import BGWLeaves.StableAnalysis.Defs
import BGWLeaves.MaxDegreeLimit.Proof

/-!
# Tranche 2, package M14 `MaxDegreeLimit`: the maximal degree of a tree with `n` leaves

Source: arXiv:1110.2163v4 (`.orchestration/t2-arch/paper_utf8.tex`): Theorem 7.1(i) (`thm:max`,
line 2357), the discussion before it (lines 2345-2351) and the identity `Δ̄(W(τ)) = Δ(τ) - 1` (C36.N14).

Each declaration here is a statement audited for freezing (audit B, `.orchestration/t2-audit-b`); its
proof is to be supplied in the provider modules `BGWLeaves.MaxDegreeLimit.*` (imported through
`BGWLeaves.MaxDegreeLimit.Proof`).  The measurability of the rescaled maximal degree is PROVED in
`BGWLeaves.MaxDegreeLimit.Defs` (`measurable_scaledMaxDegree`).  This file imports no statements file of
another package.  The standing hypotheses are those of `BGWLeaves.LeafLimits` (see its header for `hnl`:
the §5 standing assumption of line 1269, a sufficient restriction kept by owner decision Q2; `hap` and
`hne` are redundant next to it, kept for uniformity).

Layout.
* Provider `Jump`: `maxJump_rescaledLuka`, `thm_max_i`, `thm_max_i_pos`, `thm_max_two_zero`.
-/

@[expose] public section

namespace BGWLeaves

open MeasureTheory ProbabilityTheory Filter BGW
open BGW.StableTrees BGW.LocallyFinite BGWLeaves.StableAnalysis
open scoped ENNReal NNReal Topology

/-- **C36.N14**: `Δ̄(W(τ)) = Δ(τ) - 1` for a finite tree with at least two vertices, at every positive
scale (false for the one-vertex tree: `Δ̄ = 0`, `Δ - 1 = -1`).  Not printed as a statement (used in the
proof of Theorem 7.1(i), line 2357).  Moved from the M13 draft (it serves only M14).  ROUTINE. -/
theorem maxJump_rescaledLuka (τ : LocallyFinite.Tree) (hτ : FiniteVertices τ)
    (h2 : 2 ≤ treeSize τ) {b : ℝ} (hb : 0 < b) :
    Skorokhod.maxJump (rescaledLuka (treeSize τ) b τ) = ((maxDegree (toPlaneTree τ) : ℝ) - 1) / b := by
  exact BGWLeaves.MaxDegreeLimit.Jump.maxJump_rescaledLuka τ hτ h2 hb

/-- **Theorem 7.1(i) (`thm:max`, line 2357)**: if `1 < θ < 2`, `μ₀^{1/θ} Δ(τ_n)/B_n → Δ̄(X^exc)` in law,
`τ_n ∼ P_μ[· | λ = n]`.  The printed theorem already uses `μ₀^{1/θ} Δ/B_n` (lines 2357-2358).  Applying
the largest-positive-jump functional first gives `μ₀^{1/θ}(Δ - 1)/B_n`; the difference tends to zero
(Astra review, amendment 1).
Form: STRONGER (any admissible norming; `1 < θ` comes from `hB`) and RESTRICTED: added hypothesis `hnl`
(line 1269, inherited from 6.1 and 5.10; Theorem 7.1 does not state it).  Measurability:
`measurable_scaledMaxDegree` (proved).  ROUTINE+: 6.1 with Remark 5.10 (`rem_changement`, first
coordinate), `maxJump_rescaledLuka` (`ζ ≥ 2` w.h.p.), BGW `lipschitzWith_two_maxJump` (C36). -/
theorem thm_max_i {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hap : Aperiodic μ) (hB : IsRealStableAttracted (realOffspringStepLaw μ) θ B)
    (hnl : ¬ IsLatticeLaw (etaLaw μ)) (hθ2 : θ < 2) {q : ℕ → ℕ}
    (hqtop : Tendsto q atTop atTop) (hq : ∀ k, LeafAdmissible μ (q k)) :
    Tendsto (fun k => (leafTreeLaw μ (q k)).map
        (fun τ => (μ 0).toReal ^ (1 / θ) * (maxDegree (toPlaneTree τ) : ℝ) / B (q k)))
      atTop (𝓝 ((levyExcLaw θ).map Skorokhod.maxJump)) := by
  exact BGWLeaves.MaxDegreeLimit.Jump.thm_max_i hc hne hap hB hnl hθ2 hqtop hq

/-- **Theorem 7.1(i), discussion (line 2349)**: the limit `Δ̄(X^exc)` is a.s. positive for `θ < 2`.
Form: PRINTED.  The conjunct `θ ≤ 2` of `hθ` is redundant next to `hθ2` (kept to match BGW's hypothesis
shape).  ROUTINE: BGW `ae_maxJump_pos_levyExcLaw` (C22.E3). -/
theorem thm_max_i_pos {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (hθ2 : θ < 2) :
    ∀ᵐ x : Skorokhod.D 1 ℝ ∂(levyExcLaw θ).toMeasure, 0 < Skorokhod.maxJump x := by
  exact BGWLeaves.MaxDegreeLimit.Jump.thm_max_i_pos hθ hθ2

/-- **Discussion before Theorem 7.1 (line 2351)**: for `θ = 2`, `X^exc` is continuous, so
`μ₀^{1/2} Δ(τ_n)/B_n → 0` in law (in probability).  Form: STRONGER than printed (audit B, B-4): the printed
remark is for finite variance `σ² < ∞` only; this statement covers every `θ = 2` attraction, with finite
OR infinite variance (only the continuity of `X^exc` is used, so no constant of R4 is involved); any
admissible norming.  RESTRICTED: added hypothesis `hnl` (line 1269).  Measurability:
`measurable_scaledMaxDegree` (proved).  ROUTINE+: as `thm_max_i` with BGW
`ae_maxJump_eq_zero_levyExcLaw_two` (C22.E3). -/
theorem thm_max_two_zero {μ : PMF ℕ} {B : ℕ → ℝ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hap : Aperiodic μ) (hB : IsRealStableAttracted (realOffspringStepLaw μ) 2 B)
    (hnl : ¬ IsLatticeLaw (etaLaw μ)) {q : ℕ → ℕ}
    (hqtop : Tendsto q atTop atTop) (hq : ∀ k, LeafAdmissible μ (q k)) :
    Tendsto (fun k => (leafTreeLaw μ (q k)).map
        (fun τ => (μ 0).toReal ^ (1 / 2 : ℝ) * (maxDegree (toPlaneTree τ) : ℝ) / B (q k)))
      atTop (𝓝 (diracProba 0)) := by
  exact BGWLeaves.MaxDegreeLimit.Jump.thm_max_two_zero hc hne hap hB hnl hqtop hq

end BGWLeaves
