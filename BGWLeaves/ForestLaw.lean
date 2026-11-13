module

public import BGWLeaves.ForestLaw.Defs
import BGWLeaves.ForestLaw.Proof

/-!
# The forest law and Proposition 1.6 (M2)

Source: arXiv:1110.2163v4, Section 1.3 (lines 503–562): the law of `j` independent
Galton–Watson trees, `eq:LambdaUtile` and Proposition 1.6 (`prop:K`).
-/

@[expose] public section

namespace BGWLeaves

open MeasureTheory ProbabilityTheory BGW
open scoped ENNReal

/-- The actual `j`-tree law of the event `ζ = p`, `λ = n` is the total forest weight. -/
theorem pi_bienaymeLaw_forestEvent (μ : Measure ℕ) [IsProbabilityMeasure μ] (j p n : ℕ) :
    Measure.pi (fun _ : Fin j => LocallyFinite.bienaymeLaw μ) (forestEvent j p n) =
      forestLeafWeight (fun d => μ {d}) j p n := by
  exact BGWLeaves.ForestLaw.Transport.pi_bienaymeLaw_forestEvent μ j p n

/-- `eq:LambdaUtile`: `P[Λ(p)=n, W_p=-j] = P[S_p=n] P[W'_{p-n}=n-j]`. -/
theorem pi_leafMarkedBridges (μ : Measure ℕ) [IsProbabilityMeasure μ] (h0 : μ {0} ≠ 1)
    {j p n : ℕ} (hj : 1 ≤ j) (hn : n ≤ p) :
    Measure.pi (fun _ : Fin p => μ) (leafMarkedForestBridges j p n) =
      (p.choose n : ℝ≥0∞) * μ {0} ^ n * (1 - μ {0}) ^ (p - n) *
        Measure.pi (fun _ : Fin (p - n) => eta μ) {ω | ∑ i, ω i + j = n} := by
  exact BGWLeaves.ForestLaw.Factorization.pi_leafMarkedBridges μ h0 hj hn

/-- Proposition 1.6 (`prop:K`): `P_{μ,j}(ζ = p, λ = n) = (j/p) P[S_p = n] P[W'_{p-n} = n-j]`. -/
theorem prop_K (μ : Measure ℕ) [IsProbabilityMeasure μ] (h0 : μ {0} ≠ 1)
    {j p n : ℕ} (hj : 1 ≤ j) (hp : 1 ≤ p) (hn : n ≤ p) :
    Measure.pi (fun _ : Fin j => LocallyFinite.bienaymeLaw μ) (forestEvent j p n) =
      ((j : ℝ≥0∞) / p) * ((p.choose n : ℝ≥0∞) * μ {0} ^ n * (1 - μ {0}) ^ (p - n)) *
        Measure.pi (fun _ : Fin (p - n) => eta μ) {ω | ∑ i, ω i + j = n} := by
  have hp0 : (p : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hpT : (p : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top p
  have hbridge : ∑' ω : Fin p → ℕ,
      (leafMarkedForestBridges j p n).indicator (fun ω => ∏ i, (fun d => μ {d}) (ω i)) ω =
        Measure.pi (fun _ : Fin p => μ) (leafMarkedForestBridges j p n) :=
    (BGW.pi_eq_tsum_indicator μ (leafMarkedForestBridges j p n)).symm
  have hkey := natCast_mul_forestLeafWeight (fun d => μ {d}) hj p n
  rw [hbridge] at hkey
  rw [pi_bienaymeLaw_forestEvent μ j p n]
  calc forestLeafWeight (fun d => μ {d}) j p n
      = (p : ℝ≥0∞)⁻¹ * ((p : ℝ≥0∞) * forestLeafWeight (fun d => μ {d}) j p n) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel hp0 hpT, one_mul]
    _ = (p : ℝ≥0∞)⁻¹ * ((j : ℝ≥0∞) *
          Measure.pi (fun _ : Fin p => μ) (leafMarkedForestBridges j p n)) := by rw [hkey]
    _ = ((j : ℝ≥0∞) / p) *
          Measure.pi (fun _ : Fin p => μ) (leafMarkedForestBridges j p n) := by
        rw [div_eq_mul_inv]; ring
    _ = _ := by rw [pi_leafMarkedBridges μ h0 hj hn]; ring

end BGWLeaves
