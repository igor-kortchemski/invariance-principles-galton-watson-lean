module

public import BGWLeaves.MarkedForest.Defs
import BGWLeaves.MarkedForest.Proof

/-!
# The multiplied leaf-marked forest identity

Source: arXiv:1110.2163v4, Section 1.3, `eq:kemperman` and its marked version used in the proof of
Proposition 1.6 (`prop:K`, step 3): for `j ≥ 1` roots, `p` vertices and `n` leaves,
`p * F_w(j, p, n) = j * ∑_ω 1{∑ ω_i + j = p, #{i : ω_i = 0} = n} ∏ w(ω_i)`.
-/

@[expose] public section

namespace BGWLeaves

open BGW
open scoped ENNReal

/-- **Multiplied leaf-marked Kemperman identity for forests.** For arbitrary weights
`w : ℕ → ℝ≥0∞`, `j ≥ 1` roots, `p` vertices and `n` leaves,
`p * F_w(j, p, n) = j * ∑_ω 1{∑ ω_i + j = p, #{i : ω_i = 0} = n} ∏ w(ω_i)`.
No division and no positivity or conditioning assumption is involved. -/
theorem natCast_mul_forestLeafWeight (w : ℕ → ℝ≥0∞) {j : ℕ} (hj : 1 ≤ j) (p n : ℕ) :
    (p : ℝ≥0∞) * forestLeafWeight w j p n =
      (j : ℝ≥0∞) * ∑' ω : Fin p → ℕ,
        (leafMarkedForestBridges j p n).indicator (fun ω => ∏ i, w (ω i)) ω := by
  exact BGWLeaves.MarkedForest.Proof.result w hj p n

end BGWLeaves
