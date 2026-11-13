/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.ExcursionLifetimeTail
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! Identification of the lifetime image measure by its finite positive tails.

Reference: J. Bertoin, *Lévy Processes*, Cambridge University Press, 1996, Chapters IV and VIII. -/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees

private theorem measure_eq_of_positive_tails {μ ν : Measure ℝ≥0}
    (hμ0 : μ {0} = 0) (hν0 : ν {0} = 0)
    (hfinite : ∀ t : ℝ≥0, 0 < t → μ (Ioi t) ≠ ⊤)
    (heq : ∀ t : ℝ≥0, 0 < t → μ (Ioi t) = ν (Ioi t)) : μ = ν := by
  have hrestr (ε : ℝ≥0) (hε : 0 < ε) : μ.restrict (Ioi ε) = ν.restrict (Ioi ε) := by
    let : IsFiniteMeasure (μ.restrict (Ioi ε)) :=
      isFiniteMeasure_restrict.mpr (hfinite ε hε)
    let : IsFiniteMeasure (ν.restrict (Ioi ε)) :=
      isFiniteMeasure_restrict.mpr (by rw [← heq ε hε]; exact hfinite ε hε)
    apply Measure.ext_of_Iic
    intro t
    rw [← compl_Ioi, measure_compl measurableSet_Ioi (measure_ne_top _ _),
      measure_compl measurableSet_Ioi (measure_ne_top _ _)]
    simp only [Measure.restrict_apply MeasurableSet.univ, univ_inter,
      Measure.restrict_apply measurableSet_Ioi, Ioi_inter_Ioi]
    rw [heq ε hε, heq (max t ε) (hε.trans_le (le_max_right t ε))]
  let S : ℕ → Set ℝ≥0 := fun n => Ioi (1 / (n + 1 : ℝ≥0))
  have hU : (⋃ n, S n) = Ioi 0 := by
    ext x
    constructor
    · intro hx
      obtain ⟨n, hn⟩ := mem_iUnion.mp hx
      exact (by positivity : (0 : ℝ≥0) < 1 / (n + 1 : ℝ≥0)).trans hn
    · intro hx
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt hx
      exact mem_iUnion.mpr ⟨n, hn⟩
  have hpos : μ.restrict (Ioi 0) = ν.restrict (Ioi 0) := by
    rw [← hU]
    exact Measure.restrict_iUnion_congr.mpr (fun n => hrestr _ (by positivity))
  have hμ : μ.restrict (Ioi 0) = μ := by
    apply Measure.restrict_eq_self_of_ae_mem
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hμ0] with x hx
    exact (pos_iff_ne_zero : (0 : ℝ≥0) < x ↔ x ≠ 0).mpr (by simpa using hx)
  have hν : ν.restrict (Ioi 0) = ν := by
    apply Measure.restrict_eq_self_of_ae_mem
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hν0] with x hx
    exact (pos_iff_ne_zero : (0 : ℝ≥0) < x ↔ x ≠ 0).mpr (by simpa using hx)
  exact hμ.symm.trans (hpos.trans hν)

private theorem powerDensity_tail {a K : ℝ} (ha : 0 < a) (hK : 0 ≤ K)
    (t : ℝ≥0) (ht : 0 < t) :
    (lebNN.withDensity (fun u : ℝ≥0 => ENNReal.ofReal (K * (u : ℝ) ^ (-1 - a))))
      (Ioi t) = ENNReal.ofReal (K / a * (t : ℝ) ^ (-a)) := by
  have htR : 0 < (t : ℝ) := ht
  rw [withDensity_apply _ measurableSet_Ioi]
  have himage : ((↑) : ℝ≥0 → ℝ) '' Ioi t = Ioi (t : ℝ) := by
    ext x
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact hu
    · intro hx
      exact ⟨⟨x, htR.le.trans hx.le⟩, hx, rfl⟩
  change (∫⁻ u in Ioi t, ENNReal.ofReal (K * (u : ℝ) ^ (-1 - a))
    ∂volume.comap ((↑) : ℝ≥0 → ℝ)) = _
  have hi : (∫⁻ u in Ioi t, ENNReal.ofReal (K * (u : ℝ) ^ (-1 - a))
      ∂volume.comap ((↑) : ℝ≥0 → ℝ)) =
      ∫⁻ u in ((↑) : ℝ≥0 → ℝ) '' Ioi t, ENNReal.ofReal (K * u ^ (-1 - a)) :=
    setLIntegral_subtype (s := Ici (0 : ℝ)) measurableSet_Ici (Ioi t)
      (fun u => ENNReal.ofReal (K * u ^ (-1 - a)))
  rw [hi, himage]
  rw [← ofReal_integral_eq_lintegral_ofReal]
  · congr 1
    rw [integral_const_mul, integral_Ioi_rpow_of_lt (by linarith) htR]
    rw [show -1 - a + 1 = -a by ring]
    field_simp
  · exact (integrableOn_Ioi_rpow_of_lt (by linarith : -1 - a < -1) htR).const_mul K
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact mul_nonneg hK (Real.rpow_nonneg (htR.le.trans hu.le) _)

/-- **Lifetime density**: the image of `N` under the lifetime is
`(1/θ)/Γ(1-1/θ) · t^{-1-1/θ} dt` on `(0,∞)` (Lévy measure of the passage subordinator). -/
theorem excursionMeasure_lifetime_density {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    (excursionMeasure θ).map Excursion.lifetime =
      lebNN.withDensity (fun t : ℝ≥0 =>
        ENNReal.ofReal ((1 / θ) / Real.Gamma (1 - 1 / θ) * (t : ℝ) ^ (-1 - 1 / θ))) := by
  have hθ0 : 0 < θ := lt_trans zero_lt_one hθ.1
  have ha : 0 < 1 / θ := one_div_pos.mpr hθ0
  have hG : 0 < Real.Gamma (1 - 1 / θ) :=
    Real.Gamma_pos_of_pos (sub_pos.mpr ((div_lt_one hθ0).mpr hθ.1))
  apply measure_eq_of_positive_tails
  · rw [Measure.map_apply measurable_excursion_lifetime (measurableSet_singleton 0)]
    have hz : Excursion.lifetime ⁻¹' ({0} : Set ℝ≥0) = ∅ := by
      ext e
      simp [e.lifetime_pos.ne']
    rw [hz, measure_empty]
  · exact (withDensity_absolutelyContinuous _ _) lebNN_singleton_zero
  · intro t ht
    rw [Measure.map_apply measurable_excursion_lifetime measurableSet_Ioi]
    exact (excursionMeasure_lifetime_slab_lt_top hθ ht).ne
  · intro t ht
    rw [Measure.map_apply measurable_excursion_lifetime measurableSet_Ioi]
    change excursionMeasure θ {e : Excursion | (t : ℝ) < (e.lifetime : ℝ)} = _
    rw [excursionMeasure_lifetime_tail hθ (t : ℝ) ht,
      powerDensity_tail ha (div_pos ha hG).le t ht]
    congr 1
    field_simp

end BGW.StableTrees
