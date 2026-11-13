module

public import BGWLeaves.GeneralAFunctional.WalkPrefix
public import BGWLeaves.GeneralAFunctional.WalkTerminal

/-!
The full A-marked bridge principle and the walk side of Theorem 8.1(II).

The prefix principle includes μ(A)=1, where all steps are marked almost surely
and the clock is deterministic. At μ(A)=0 an admissible sequence tending to
infinity is impossible. Thus neither boundary requires division by 1-μ(A).
-/

@[expose] public section

namespace BGWLeaves.GeneralAFunctional.WalkMain

open MeasureTheory ProbabilityTheory Filter BGW
open BGW.StableTrees BGW.LocallyFinite BGWLeaves.StableAnalysis
open BGWLeaves.GeneralAFunctional.Walk BGWLeaves.GeneralAFunctional.WalkVervaat
open scoped ENNReal NNReal Topology

/-- The full A-marked bridge principle, from proper prefixes and terminal
oscillation control by C11b. -/
theorem tendsto_aBridgeWalkPath {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ} {A : Set ℕ}
    (hA : A.Nonempty) (hc : IsCritical μ) (hne : μ 1 ≠ 1) (hap : Aperiodic μ)
    (hB : IsRealStableAttracted (realOffspringStepLaw μ) θ B)
    (hAfin : ¬ Integrable (fun z : ℤ => (z : ℝ) ^ 2) (stepLaw μ) → A.Finite ∨ Aᶜ.Finite)
    {q : ℕ → ℕ} (hqtop : Tendsto q atTop atTop) (hq : ∀ k, ZetaAAdmissible μ A (q k)) :
    Tendsto (fun k => (aBridgeLaw μ A (q k)).map (aBridgeWalkPath A B (q k)))
      atTop (𝓝 (stableBridgeLaw θ)) := by
  by_cases hmass : μ.toMeasure A = 0
  · exact False.elim ((mark_mass_ne_zero_of_admissible_sequence hc hne hqtop hq) hmass)
  · let a : ℕ → ℝ := fun j => 1 - 1 / ((j : ℝ) + 2)
    have ha0 (j : ℕ) : 0 ≤ a j := by
      dsimp [a]
      have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
      have hd : 0 < (j : ℝ) + 2 := by positivity
      exact (sub_pos.mpr ((div_lt_one hd).mpr (by linarith))).le
    have ha1 (j : ℕ) : a j < 1 := by
      dsimp [a]
      exact sub_lt_self _ (by positivity)
    have halim : Tendsto a atTop (𝓝 1) := by
      have ht := (tendsto_const_nhds (x := (1 : ℝ))).sub
        ((tendsto_atTop_add_const_right atTop (2 : ℝ)
          tendsto_natCast_atTop_atTop).const_div_atTop (1 : ℝ))
      simpa only [sub_zero] using ht
    have hpre := fun (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s < 1) =>
      WalkPrefix.aBridge_prefix_tendsto hA hc hne hap hB hAfin hqtop hq hs0 hs1
    exact Skorokhod.tendsto_of_tendsto_restrict_of_oscillation
      (fun k => aBridgeLaw μ A (q k))
      (fun k => measurable_aBridgeWalkPath A B (q k)) zero_lt_one ha0 ha1 halim
      (fun j => hpre (a j) (ha0 j) (ha1 j))
      (stableBridgeLaw_ae_continuousAt hB.index_mem ⟨1, zero_le_one, le_rfl⟩)
      (WalkTerminal.aBridge_terminal_oscillation hA hc hne hap hB hAfin hqtop hq
        hpre ha0 ha1 halim)

/-- (W_A) The walk side of Theorem 8.1(II), with the original random total-size
normalization. The signature is exactly that of `m15-split/Parts.lean`. -/
theorem general_walk_tendsto {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ} {A : Set ℕ} (hA : A.Nonempty)
    (hc : IsCritical μ) (hne : μ 1 ≠ 1) (hap : Aperiodic μ)
    (hB : IsRealStableAttracted (realOffspringStepLaw μ) θ B)
    (hAfin : ¬ Integrable (fun z : ℤ => (z : ℝ) ^ 2) (stepLaw μ) → A.Finite ∨ Aᶜ.Finite)
    {q : ℕ → ℕ} (hqtop : Tendsto q atTop atTop) (hq : ∀ k, ZetaAAdmissible μ A (q k)) :
    Tendsto (fun k => (zetaATreeLaw μ A (q k)).map
        (fun τ => rescaledLuka (treeSize τ) (B (treeSize τ)) τ))
      atTop (𝓝 (levyExcLaw θ)) := by
  exact walk_tendsto_of_bridge hB hqtop hq
    (tendsto_aBridgeWalkPath hA hc hne hap hB hAfin hqtop hq)

end BGWLeaves.GeneralAFunctional.WalkMain
