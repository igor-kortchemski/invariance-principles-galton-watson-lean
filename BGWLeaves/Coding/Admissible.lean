module

public import BGWLeaves.Coding.Defs
public import BGWLeaves.LeafMass
public import BGWLeaves.StableAnalysis
public import BGWLeaves.GeneralA
public import BGWLeaves.LocalEstimates

/-!
# Admissible sizes: non-vacuity of the leaf-conditioned statements

Proofs of the non-vacuity of the leaf-conditioned statements:
`infinite_leafAdmissible`, `exists_seq_leafAdmissible` and `eventually_leafAdmissible` of
`BGWLeaves.Coding`, exported in namespace `BGWLeaves.Coding.Admissible` with exactly the types stated
there.

Route: Theorem 3.1(i) (`ltn_i_arith`: for `n` large, `P_μ[λ = n + 1] > 0` iff
`g ∣ n`, with `g = arithFactor μ {0} ≥ 1`) gives the admissible sizes `g (N + k) + 1`; under the
non-lattice assumption on `etaLaw μ`, `g = 1` (otherwise every `k ≥ 1` of the support satisfies
`g ∣ k - 1`, a lattice, by `nonLattice_etaLaw_iff`).  The analytic hypotheses `(H_θ)` (`hap`, `hDA`)
are not needed.
-/

@[expose] public section

namespace BGWLeaves.Coding.Admissible

open Filter BGW BGW.StableTrees BGWLeaves.StableAnalysis

/-- A positive leaf probability is an admissible size. -/
theorem leafAdmissible_of_leafProb_pos {μ : PMF ℕ} {n : ℕ} (h : 0 < leafProb μ n) :
    LeafAdmissible μ n := by
  intro h0
  simp [leafProb, MeasureTheory.Measure.real, h0] at h

/-- The admissible sizes `g (N + k) + 1` given by Theorem 3.1(i). -/
theorem exists_leafAdmissible_affine {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1) :
    ∃ N : ℕ, ∀ k : ℕ, LeafAdmissible μ (arithFactor μ {0} * (N + k) + 1) := by
  obtain ⟨N, hN⟩ := ltn_i_arith hc hne
  have hg : 1 ≤ arithFactor μ {0} := (arithFactor_isGreatest hc hne {0}).1.1
  refine ⟨N, fun k => leafAdmissible_of_leafProb_pos ?_⟩
  exact (hN _ (by nlinarith)).2 (dvd_mul_right _ _)

set_option linter.unusedVariables false in
theorem exists_seq_leafAdmissible {μ : PMF ℕ} {θ : ℝ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hap : Aperiodic μ) (hDA : ∃ a, StableDomain μ θ a) :
    ∃ q : ℕ → ℕ, Tendsto q atTop atTop ∧ ∀ k, LeafAdmissible μ (q k) := by
  obtain ⟨N, hN⟩ := exists_leafAdmissible_affine hc hne
  have hg : 1 ≤ arithFactor μ {0} := (arithFactor_isGreatest hc hne {0}).1.1
  refine ⟨fun k => arithFactor μ {0} * (N + k) + 1, ?_, hN⟩
  refine tendsto_atTop_mono (fun k => ?_) tendsto_id
  show k ≤ arithFactor μ {0} * (N + k) + 1
  nlinarith

set_option linter.unusedVariables false in
theorem infinite_leafAdmissible {μ : PMF ℕ} {θ : ℝ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hap : Aperiodic μ) (hDA : ∃ a, StableDomain μ θ a) :
    {n : ℕ | LeafAdmissible μ n}.Infinite := by
  obtain ⟨N, hN⟩ := exists_leafAdmissible_affine hc hne
  have hg : 1 ≤ arithFactor μ {0} := (arithFactor_isGreatest hc hne {0}).1.1
  refine Set.infinite_of_forall_exists_gt fun a => ⟨_, hN a, ?_⟩
  nlinarith

/-- Under the non-lattice assumption on `etaLaw μ`, the leaf gcd `arithFactor μ {0}` is `1`. -/
theorem arithFactor_zero_eq_one_of_nonLattice {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hnl : ¬ IsLatticeLaw (etaLaw μ)) : arithFactor μ {0} = 1 := by
  have hG := arithFactor_isGreatest hc hne {0}
  by_contra h1
  have h2 : 2 ≤ arithFactor μ {0} := by have := hG.1.1; omega
  refine (nonLattice_etaLaw_iff hc hne).1 hnl ⟨1, arithFactor μ {0}, h2, fun k hk hk0 => ?_⟩
  exact hG.1.2 _ ⟨k, hk, Or.inr ⟨by simpa using hk0, rfl⟩⟩

set_option linter.unusedVariables false in
theorem eventually_leafAdmissible {μ : PMF ℕ} {θ : ℝ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hap : Aperiodic μ) (hDA : ∃ a, StableDomain μ θ a) (hnl : ¬ IsLatticeLaw (etaLaw μ)) :
    ∀ᶠ n in atTop, LeafAdmissible μ n := by
  obtain ⟨N, hN⟩ := ltn_i_arith hc hne
  have hg := arithFactor_zero_eq_one_of_nonLattice hc hne hnl
  refine eventually_atTop.2 ⟨N + 1, fun n hn => ?_⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact leafAdmissible_of_leafProb_pos ((hN m (by omega)).2 (by rw [hg]; exact one_dvd m))

end BGWLeaves.Coding.Admissible
