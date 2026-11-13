/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.ExactContourPaths
public import BGW.StableTrees.ExactContourPrefixLaw
import BGW.StableTrees.SurvivalBasic
import Mathlib.Analysis.Normed.Group.Bounded

/-!
# Contour comparison on compact sets of height prefixes

A larger height prefix controls the contour on a smaller prefix by deterministic bracketing.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal Classical
open BGW.Skorokhod BGW.StableTrees

namespace BGW.StableTrees.ExactContour

open BGW.StableTrees.DiscreteForest BGW.StableTrees.TailPair

private theorem compact_oscillation {a : ℝ≥0}
    (K : Set C(Icc (0 : ℝ) (a : ℝ), ℝ)) (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ g ∈ K, ∀ s t : Icc (0 : ℝ) (a : ℝ),
      |(s : ℝ) - t| ≤ δ → |g s - g t| ≤ ε := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have heval : Continuous (fun p : K × Icc (0 : ℝ) (a : ℝ) => p.1.val p.2) := by fun_prop
  obtain ⟨η, hη, hbound⟩ := Metric.uniformContinuous_iff.mp
    (CompactSpace.uniformContinuous_of_continuous heval) ε hε
  refine ⟨η / 2, half_pos hη, ?_⟩
  intro g hg s t hst
  have hd : dist ((⟨g, hg⟩ : K), s) ((⟨g, hg⟩ : K), t) < η := by
    rw [Prod.dist_eq, dist_self, max_eq_right dist_nonneg, Subtype.dist_eq, Real.dist_eq]
    exact hst.trans_lt (half_lt_self hη)
  exact (show |g s - g t| < ε by simpa only [Real.dist_eq] using hbound hd).le

/-- On a compact set of larger height prefixes, the contour/height error vanishes uniformly. -/
theorem eventually_contourHeightError_le_of_compact {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ}
    (h : StableDomain μ θ B) {a a' : ℝ≥0} (haa' : a < a') (ha' : a' < 1)
    (K : Set C(Icc (0 : ℝ) (a' : ℝ), ℝ)) (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ t : PlaneTree, t.size = n → treeHeightPath B n a' t.toLocallyFinite ∈ K →
      contourHeightError B n a t.toLocallyFinite ≤ ε := by
  obtain ⟨M, hM, hbound⟩ := hK.isBounded.exists_pos_norm_le
  obtain ⟨δ, hδ, hosc⟩ := compact_oscillation K hK (show 0 < ε / 3 by positivity)
  let b : ℝ := ((a : ℝ) + a') / 2
  have hab : (a : ℝ) < b := by dsimp [b]; exact_mod_cast (show a < (a + a') / 2 by
    change (a : ℝ) < ((a : ℝ) + a') / 2; linarith [show (a : ℝ) < a' from haa'])
  have hba' : b < a' := by dsimp [b]; linarith [show (a : ℝ) < a' from haa']
  have hb0 : 0 ≤ b := a.coe_nonneg.trans hab.le
  have haR : (a' : ℝ) < 1 := ha'
  have hb1 : b < 1 := hba'.trans (show (a' : ℝ) < 1 from ha')
  have hB := Scalar.tendsto_atTop h
  have hnR : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hratio := Survival.tendsto_B_div_n h
  filter_upwards [eventually_ge_atTop 1,
    hnR.eventually_ge_atTop (2 / ((a' : ℝ) - b)),
    hnR.eventually_ge_atTop (2 / (b - a)),
    hnR.eventually_ge_atTop (1 / δ),
    hB.eventually_ge_atTop (M / (b - a)),
    hB.eventually_ge_atTop (M / (2 * δ)),
    hratio.eventually_le_const
      (show 0 < ε / 3 by positivity)] with n hn hnA hnGap hnδ hBM hBδ hsmall
  intro t ht hmem
  have hn0 : 0 < n := by omega
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn0
  have hc : 0 < B n / n := div_pos (h.pos n hn0) hnpos
  let m := ⌊b * n⌋₊
  have hmlo : (m : ℝ) ≤ b * n := Nat.floor_le (by positivity)
  have hmhi : b * n < (m : ℝ) + 1 := Nat.lt_floor_add_one _
  have hmA : (m : ℝ) + 1 ≤ a' * n := by
    have hh := (div_le_iff₀ (sub_pos.mpr hba')).mp hnA
    nlinarith
  have hmSize : m + 1 ≤ t.size := by
    rw [ht]
    have : (m : ℝ) + 1 ≤ n := hmA.trans (by nlinarith)
    exact_mod_cast this
  have hg (x : ℝ) (hx0 : 0 ≤ x) (hx : x ≤ (a' : ℝ) * n) :
      B n / n * t.heightLin x = treeHeightPath B n a' t.toLocallyFinite
        ⟨x / n, div_nonneg hx0 hnpos.le, (div_le_iff₀ hnpos).mpr hx⟩ := by
    rw [treeHeightPath_toLocallyFinite]
    congr 2
    field_simp
  have hval (j : ℕ) (hj : (j : ℝ) ≤ (a' : ℝ) * n) :
      B n / n * (t.heightSeq j : ℝ) ≤ M := by
    rw [← PlaneTree.heightLin_natCast, hg j (Nat.cast_nonneg _) hj]
    exact (le_abs_self _).trans ((Real.norm_eq_abs _ ▸
      ContinuousMap.norm_coe_le_norm _ _).trans (hbound _ hmem))
  have hmval := hval m (by linarith)
  have hbuf : ∀ u : ℝ, 0 ≤ u → u ≤ (a : ℝ) * n →
      2 * u + (t.heightSeq m : ℝ) ≤ 2 * m := by
    intro u _ hu
    have hh := (div_le_iff₀ (sub_pos.mpr hab)).mp hnGap
    have hhB := (div_le_iff₀ (sub_pos.mpr hab)).mp hBM
    have hhH : (t.heightSeq m : ℝ) ≤ (b - a) * n := by
      apply (mul_le_mul_iff_right₀ (h.pos n hn0)).mp
      have hv : B n * (t.heightSeq m : ℝ) ≤ M * n := by
        exact (div_le_iff₀ hnpos).mp (by simpa only [div_mul_eq_mul_div] using hmval)
      have hhBn := mul_le_mul_of_nonneg_right hhB hnpos.le
      nlinarith
    nlinarith
  let : Nonempty (Icc (0 : ℝ) (a : ℝ)) := ⟨⟨0, le_rfl, a.coe_nonneg⟩⟩
  apply ciSup_le
  intro s
  rw [treeContourLin_toLocallyFinite]
  have hhlin : treeHeightLin t.toLocallyFinite ((n : ℝ) * s) =
      t.heightLin ((n : ℝ) * s) := by
    rw [treeHeightLin, dite_eq_left t.finiteVertices_toLocallyFinite]
    change (PlaneTree.equivFiniteVertices.symm (PlaneTree.equivFiniteVertices t)).heightLin _ = _
    rw [Equiv.symm_apply_apply]
  rw [hhlin, ← mul_sub, abs_mul, abs_of_pos hc]
  have hu0 : 0 ≤ (n : ℝ) * (s : ℝ) := mul_nonneg hnpos.le s.property.1
  have hu : (n : ℝ) * (s : ℝ) ≤ (a : ℝ) * n := by nlinarith [s.property.2]
  have huM : (n : ℝ) * (s : ℝ) ≤ (m : ℝ) + 1 := by
    have hh := (div_le_iff₀ (sub_pos.mpr hab)).mp hnGap
    nlinarith
  have hω : 1 ≤ (n : ℝ) * δ := by
    have hh := (div_le_iff₀ hδ).mp hnδ
    nlinarith
  have hhalf (j : ℕ) (hj : j ≤ m) : (t.heightSeq j : ℝ) / 2 ≤ (n : ℝ) * δ := by
    have hjR : (j : ℝ) ≤ m := by exact_mod_cast hj
    have hh := hval j (by linarith)
    have hH : B n * (t.heightSeq j : ℝ) ≤ M * n := by
      exact (div_le_iff₀ hnpos).mp (by simpa only [div_mul_eq_mul_div] using hh)
    have hBδ' := (div_le_iff₀ (by positivity : 0 < 2 * δ)).mp hBδ
    nlinarith [h.pos n hn0]
  have hmod (x y : ℝ) (hx0 : 0 ≤ x) (hx : x ≤ (m : ℝ) + 1)
      (hy0 : 0 ≤ y) (hy : y ≤ (m : ℝ) + 1) (hxy : |x - y| ≤ (n : ℝ) * δ) :
      |t.heightLin x - t.heightLin y| ≤ (ε / 3) / (B n / n) := by
    let sx : Icc (0 : ℝ) (a' : ℝ) :=
      ⟨x / n, div_nonneg hx0 hnpos.le, (div_le_iff₀ hnpos).mpr (hx.trans hmA)⟩
    let sy : Icc (0 : ℝ) (a' : ℝ) :=
      ⟨y / n, div_nonneg hy0 hnpos.le, (div_le_iff₀ hnpos).mpr (hy.trans hmA)⟩
    have hd : |(sx : ℝ) - sy| ≤ δ := by
      change |x / n - y / n| ≤ δ
      rw [← sub_div, abs_div, abs_of_pos hnpos]
      exact (div_le_iff₀ hnpos).mpr (by nlinarith)
    have hh := hosc _ hmem sx sy hd
    rw [← hg x hx0 (hx.trans hmA), ← hg y hy0 (hy.trans hmA),
      ← mul_sub, abs_mul, abs_of_pos hc] at hh
    exact (le_div_iff₀ hc).mpr (by simpa only [mul_comm] using hh)
  have hh := PlaneTree.contourLin_two_mul_sub_heightLin_le_prefix t hu0 huM hmSize
    (hbuf _ hu0 hu) hω hhalf hmod
  have hmule := mul_le_mul_of_nonneg_left hh hc.le
  have hid : (B n / n) * (2 * ((ε / 3) / (B n / n)) + 1) =
      2 * (ε / 3) + B n / n := by field_simp [(h.pos n hn0).ne', hnpos.ne']
  rw [hid] at hmule
  simpa only [mul_assoc] using hmule.trans
    (show 2 * (ε / 3) + B n / n ≤ ε by linarith)

end BGW.StableTrees.ExactContour
