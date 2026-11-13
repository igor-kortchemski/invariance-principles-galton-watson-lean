/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.HeightProcessAncestral

/-!
# Support of ancestral exploration measures

Future-infimum Stieltjes measures agree strictly before an ancestor. Clock order separates
the earlier and later heights, transporting the fixed-horizon support bounds to every
ancestor. Rational horizons give one event for ancestral support tops. The final window
identity records the deterministic source truncation needed for exploration restart.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod
namespace BGW.StableTrees

private theorem stieltjes_restrict_Iio_eq {F G : StieltjesFunction ℝ} {s : ℝ}
    (he : ∀ x < s, F x = G x) : F.measure.restrict (Iio s) = G.measure.restrict (Iio s) := by
  have hl : Function.leftLim F s = Function.leftLim G s := by
    rw [F.mono.leftLim_eq_sSup, G.mono.leftLim_eq_sSup]
    congr 1
    exact image_congr (fun x hx => he x hx)
  apply Measure.ext_of_Ioc'
  · intro a b _
    exact ne_top_of_le_ne_top (StieltjesFunction.measure_Ioc F a b ▸ ENNReal.ofReal_ne_top)
      (Measure.restrict_le_self _)
  · intro a b hab
    rw [Measure.restrict_apply measurableSet_Ioc, Measure.restrict_apply measurableSet_Ioc]
    by_cases hb : b < s
    · have hsub : Ioc a b ⊆ Iio s := fun _ hx => hx.2.trans_lt hb
      rw [inter_eq_left.mpr hsub, StieltjesFunction.measure_Ioc,
        StieltjesFunction.measure_Ioc, he a (hab.trans hb), he b hb]
    · by_cases ha : a < s
      · have heq : Ioc a b ∩ Iio s = Ioo a s := by
          ext x
          constructor
          · exact fun hx => ⟨hx.1.1, hx.2⟩
          · exact fun hx => ⟨⟨hx.1, hx.2.le.trans (not_lt.mp hb)⟩, hx.2⟩
        rw [heq, StieltjesFunction.measure_Ioo, StieltjesFunction.measure_Ioo, he a ha, hl]
      · have heq : Ioc a b ∩ Iio s = ∅ := by
          apply eq_empty_iff_forall_notMem.mpr
          intro x hx
          exact (not_lt_of_ge (not_lt.mp ha)) (hx.1.1.trans hx.2)
        simp only [heq, measure_empty]

/-- Before an ancestral time, the two future-infimum functions coincide. -/
theorem futureInf_eq_before_ancestor (f : DLoc) {u s q : ℝ≥0} (hus : u < s) (hsq : s ≤ q)
    (ha : Function.leftLim f.1 s ≤ futureInf f q s) : futureInf f q u = futureInf f s u := by
  have hle : futureInf f s u ≤ Function.leftLim f.1 s := by
    have : (𝓝[<] s).NeBot := nhdsLT_neBot_of_exists_lt ⟨u, hus⟩
    apply ge_of_tendsto (f.2.tendsto_nhdsLT_leftLim s)
    filter_upwards [Ioo_mem_nhdsLT hus] with v hv
    exact futureInf_le_eval f s u v ⟨(min_le_left _ _).trans hv.1.le, hv.2.le⟩
  rw [futureInf_split f hus.le hsq, min_eq_left (hle.trans ha)]

/-- The exploration source before an ancestor does not depend on the later horizon. -/
theorem explorationStieltjes_restrict_before_ancestor (f : DLoc) {s q : ℝ≥0}
    (hs : 0 < s) (hsq : s ≤ q) (ha : Function.leftLim f.1 s ≤ futureInf f q s) :
    (explorationStieltjes f s).measure.restrict (Ioo 0 (s : ℝ)) =
      (explorationStieltjes f q).measure.restrict (Ioo 0 (s : ℝ)) := by
  have he : ∀ x < (s : ℝ), explorationStieltjes f s x = explorationStieltjes f q x := by
    intro x hx
    have hus : x.toNNReal < s := by
      have hh := (Real.toNNReal_lt_toNNReal_iff (show (0 : ℝ) < s from by
        exact_mod_cast hs)).mpr hx
      simpa only [Real.toNNReal_coe] using hh
    have hF (t : ℝ≥0) : explorationStieltjes f t x = futureInf f t x.toNNReal := by
      simp only [explorationStieltjes, dite_eq_left (explorationStieltjes_spec f t), futureInfFun]
    rw [hF, hF, futureInf_eq_before_ancestor f hus hsq ha]
  have hh := stieltjes_restrict_Iio_eq he
  have hh' := congrArg (fun μ : Measure ℝ => μ.restrict (Ioi 0)) hh
  simpa only [Measure.restrict_restrict measurableSet_Ioi, Ioi_inter_Iio] using hh'

/-- Away from its terminal height, an ancestral exploration uses the earlier source window. -/
theorem exploration_apply_before_ancestor (θ : ℝ) (f : DLoc) {s q : ℝ≥0}
    (hs : 0 < s) (hsq : s ≤ q) (ha : Function.leftLim f.1 s ≤ futureInf f q s)
    {B : Set ℝ≥0} (hB : MeasurableSet B) (hn : (height θ f s).toNNReal ∉ B) :
    exploration θ f s B = ((explorationStieltjes f q).measure.restrict
      (Ioo 0 (s : ℝ))) ((fun x : ℝ => (height θ f x.toNNReal).toNNReal) ⁻¹' B) := by
  rw [exploration, Measure.map_apply (measurable_exploration_heightMap θ f) hB]
  have heq : ((fun x : ℝ => (height θ f x.toNNReal).toNNReal) ⁻¹' B) ∩ Ioc 0 (s : ℝ) =
      ((fun x : ℝ => (height θ f x.toNNReal).toNNReal) ⁻¹' B) ∩ Ioo 0 (s : ℝ) := by
    ext x
    constructor
    · rintro ⟨hx, hx0, hxs⟩
      refine ⟨hx, hx0, lt_of_le_of_ne hxs ?_⟩
      intro he
      apply hn
      simpa only [he, mem_preimage, Real.toNNReal_coe] using hx
    · exact fun hx => ⟨hx.1, hx.2.1, hx.2.2.le⟩
  rw [Measure.restrict_apply ((measurable_exploration_heightMap θ f) hB), heq,
    ← Measure.restrict_apply ((measurable_exploration_heightMap θ f) hB),
    explorationStieltjes_restrict_before_ancestor f hs hsq ha]

/-- At a fixed horizon, every ancestor has an upper support bound and no gaps below its height. -/
theorem ae_exploration_support_ancestors_fixed {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    {q : ℝ≥0} (hq : 0 < q) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∀ s : ℝ≥0, s ≤ q →
      Function.leftLim f.1 s ≤ futureInf f q s →
      exploration θ f s (Ioi (height θ f s).toNNReal) = 0 ∧
      ∀ h : ℝ≥0, (h : ℝ) < height θ f s → ∀ ε : ℝ, 0 < ε →
        0 < exploration θ f s (Metric.ball h ε) := by
  filter_upwards [ae_height_ancestor_fixed hθ hq, ae_reversed_clock_prefix hθ hq,
    ae_support_gapfree_fixed hθ q, ae_leftLim_le_stableLocalLaw hθ] with f ha hg hgap hf
  intro s hsq hsanc
  by_cases hs0 : s = 0
  · subst s
    have hz : exploration θ f 0 univ = 0 := by
      rw [exploration_univ, futureInf_self, sub_self, ENNReal.ofReal_zero]
    refine ⟨measure_mono_null (subset_univ _) hz, ?_⟩
    intro h hh
    rw [height_zero] at hh
    exact ((not_lt_of_ge h.2) hh).elim
  have hs : 0 < s := pos_iff_ne_zero.mpr hs0
  let H := height θ f s
  let R := H.toNNReal
  have hnon : 0 ≤ H := (ha s hsq hsanc).2.1
  have hR : (R : ℝ) = H := Real.coe_toNNReal _ hnon
  let μ := (explorationStieltjes f q).measure.restrict (Ioc 0 (q : ℝ))
  let ν := (explorationStieltjes f q).measure.restrict (Ioo 0 (s : ℝ))
  let A := fun x : ℝ => (height θ f x.toNNReal).toNNReal
  have hA : Measurable A := measurable_exploration_heightMap θ f
  have hsub : Ioo 0 (s : ℝ) ⊆ Ioc 0 (q : ℝ) := by
    intro x hx
    exact ⟨hx.1, hx.2.le.trans (by exact_mod_cast hsq)⟩
  have hν : ν = μ.restrict (Ioo 0 (s : ℝ)) := by
    dsimp only [μ]
    rw [Measure.restrict_restrict measurableSet_Ioo, inter_eq_left.mpr hsub]
  have hord : ∀ᵐ x ∂μ, (x < (s : ℝ) → (A x : ℝ) ≤ H) ∧
      ((s : ℝ) ≤ x → H ≤ (A x : ℝ)) := by
    filter_upwards [ae_exploration_ancestral_times f hf q, ae_restrict_mem measurableSet_Ioc]
      with x hx hxt
    have hxp : x.toNNReal ≤ q := Real.toNNReal_le_iff_le_coe.mpr hxt.2
    have hc := ha x.toNNReal hxp hx
    have heS := (ha s hsq hsanc).2.2.2
    have heX := hc.2.2.2
    have hAX : (A x : ℝ) = height θ f x.toNNReal := Real.coe_toNNReal _ hc.2.1
    rw [hAX]
    constructor
    · intro hxs
      have hxs' : x.toNNReal ≤ s := Real.toNNReal_le_iff_le_coe.mpr hxs.le
      have hm := hg.2.2.1 (show (⟨q - s, show q - s ≤ q from tsub_le_self⟩ : Iic q) ≤
        ⟨q - x.toNNReal, show q - x.toNNReal ≤ q from tsub_le_self⟩ from
          tsub_le_tsub_left hxs' q)
      change supLocalTime θ (reversedAt q f) (q - s) ≤
        supLocalTime θ (reversedAt q f) (q - x.toNNReal) at hm
      dsimp [H]
      rw [heS, heX]
      exact sub_le_sub_left hm _
    · intro hsx
      have hsx' : s ≤ x.toNNReal := by
        exact_mod_cast (show (s : ℝ) ≤ (x.toNNReal : ℝ) by
          rw [Real.coe_toNNReal _ hxt.1.le]; exact hsx)
      have hm := hg.2.2.1 (show
        (⟨q - x.toNNReal, show q - x.toNNReal ≤ q from tsub_le_self⟩ : Iic q) ≤
        ⟨q - s, show q - s ≤ q from tsub_le_self⟩ from tsub_le_tsub_left hsx' q)
      change supLocalTime θ (reversedAt q f) (q - x.toNNReal) ≤
        supLocalTime θ (reversedAt q f) (q - s) at hm
      dsimp [H]
      rw [heS, heX]
      exact sub_le_sub_left hm _
  have hνord : ∀ᵐ x ∂ν, (A x : ℝ) ≤ H := by
    rw [hν]
    filter_upwards [ae_restrict_of_ae hord, ae_restrict_mem measurableSet_Ioo]
      with x hx hxs using hx.1 hxs.2
  have hupp : exploration θ f s (Ioi R) = 0 := by
    have hn : (height θ f s).toNNReal ∉ Ioi R := by
      change ¬R < R
      exact lt_irrefl _
    rw [exploration_apply_before_ancestor θ f hs hsq hsanc measurableSet_Ioi hn]
    apply measure_eq_zero_iff_ae_notMem.mpr
    filter_upwards [hνord] with x hx
    intro hmem
    have hh : (R : ℝ) < (A x : ℝ) := by exact_mod_cast (show R < A x from hmem)
    rw [hR] at hh
    exact (not_lt_of_ge hx) hh
  refine ⟨hupp, ?_⟩
  intro h hh ε hε
  let δ := min ε ((H - (h : ℝ)) / 2)
  have hδ : 0 < δ := lt_min hε (half_pos (sub_pos.mpr hh))
  have hδH : δ ≤ (H - (h : ℝ)) / 2 := min_le_right _ _
  have hδE : δ ≤ ε := min_le_left _ _
  have hball (x : ℝ≥0) (hx : x ∈ Metric.ball h δ) : (x : ℝ) < H := by
    have hx' : |(x : ℝ) - h| < δ := hx
    have hxle := le_abs_self ((x : ℝ) - h)
    linarith only [hx', hxle, hδH, hh]
  have hRn : R ∉ Metric.ball h δ := by
    intro hm
    have hi := hball R hm
    rw [hR] at hi
    exact (lt_irrefl _) hi
  have hbelow : μ (A ⁻¹' Metric.ball h δ) = ν (A ⁻¹' Metric.ball h δ) := by
    conv_rhs => rw [hν, Measure.restrict_apply (hA measurableSet_ball)]
    apply measure_congr
    filter_upwards [hord, ae_restrict_mem measurableSet_Ioc] with x hx hxt
    apply propext
    constructor
    · intro hm
      refine ⟨hm, ?_⟩
      have hxs : x < (s : ℝ) := by
        by_contra hn
        exact (not_lt_of_ge (hx.2 (not_lt.mp hn))) (hball (A x) hm)
      exact ⟨hxt.1, hxs⟩
    · exact And.left
  have hHq : H ≤ height θ f q := by
    have he := (ha s hsq hsanc).2.2.2
    have hM : 0 ≤ supLocalTime θ (reversedAt q f) (q - s) := by
      rw [supLocalTime_eq_toReal]
      exact ENNReal.toReal_nonneg
    change H ≤ supLocalTime θ (reversedAt q f) q
    rw [show H = _ from he]
    exact sub_le_self _ hM
  have hpos := hgap h (hh.trans_le hHq) δ hδ
  have heq : exploration θ f q (Metric.ball h δ) = exploration θ f s (Metric.ball h δ) := by
    rw [exploration, Measure.map_apply (measurable_exploration_heightMap θ f) measurableSet_ball]
    change μ (A ⁻¹' Metric.ball h δ) = _
    rw [hbelow, exploration_apply_before_ancestor θ f hs hsq hsanc measurableSet_ball hRn]
  rw [heq] at hpos
  exact hpos.trans_le (measure_mono (Metric.ball_subset_ball hδE))

/-- An upper support bound and positivity below a nonnegative level identify its support top. -/
theorem topHeight_eq_of_support_bounds {ρ : Measure ℝ≥0} {H : ℝ} (hfinite : 0 ≤ H)
    (habove : ρ (Ioi H.toNNReal) = 0)
    (hgap : ∀ h : ℝ≥0, (h : ℝ) < H → ∀ ε : ℝ, 0 < ε → 0 < ρ (Metric.ball h ε)) :
    (topHeight ρ : ℝ) = H := by
  let R := (H).toNNReal
  have hR : (R : ℝ) = H := Real.coe_toNNReal _ hfinite
  have hb : ∀ h ∈ {h : ℝ≥0 | ∀ ε : ℝ, 0 < ε → 0 < ρ (Metric.ball h ε)}, h ≤ R :=
    fun _ hh => support_le_of_mass_above_zero habove hh
  have hupper : topHeight ρ ≤ R := csSup_le' hb
  have hlower : R ≤ topHeight ρ := by
    by_contra hn
    have htR : (topHeight ρ : ℝ) < (R : ℝ) := NNReal.coe_lt_coe.mpr (not_le.mp hn)
    let u : ℝ≥0 := ⟨((topHeight ρ : ℝ) + R) / 2, by positivity⟩
    have huR : (u : ℝ) < H := by
      change ((topHeight ρ : ℝ) + R) / 2 < _
      rw [← hR]
      linarith only [htR]
    have hu : ∀ ε : ℝ, 0 < ε → 0 < ρ (Metric.ball u ε) := hgap u huR
    have hule : u ≤ topHeight ρ := le_csSup ⟨R, hb⟩ hu
    have htu : (topHeight ρ : ℝ) < u := by
      change (topHeight ρ : ℝ) < ((topHeight ρ : ℝ) + R) / 2
      linarith only [htR]
    exact (not_lt_of_ge (NNReal.coe_le_coe.mpr hule)) htu
  exact (congrArg (fun x : ℝ≥0 => (x : ℝ)) (le_antisymm hupper hlower)).trans hR

/-- **Ancestral top identification**: a.s., for every `t` and ancestral `s` (same antecedent as
`ae_heightApprox_ancestral`), the top of the support of `ρ_s` is `H_s`. -/
theorem ae_topHeight_ancestral {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∀ t s : ℝ≥0,
      ((s < t ∧ Function.leftLim f.1 s ≤ futureInf f t s) ∨
        (s = t ∧ Function.leftLim f.1 t < f.1 t)) →
      (topHeight (exploration θ f s) : ℝ) = height θ f s := by
  have hrat (q : ℚ) : ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), 0 < (q : ℝ) →
      ∀ s : ℝ≥0, s ≤ (q : ℝ).toNNReal →
        Function.leftLim f.1 s ≤ futureInf f (q : ℝ).toNNReal s →
          (topHeight (exploration θ f s) : ℝ) = height θ f s := by
    by_cases hq : 0 < (q : ℝ)
    · filter_upwards [ae_exploration_support_ancestors_fixed hθ (Real.toNNReal_pos.mpr hq)]
        with f hf
      intro _ s hs ha
      have hh := hf s hs ha
      apply topHeight_eq_of_support_bounds _ hh.1 hh.2
      rw [height, supLocalTime_eq_toReal]
      exact ENNReal.toReal_nonneg
    · exact Eventually.of_forall (fun _ h => (hq h).elim)
  filter_upwards [ae_all_iff.mpr hrat] with f hf
  intro t s ha
  obtain ⟨q, hq, hs, hanc⟩ := exists_rat_horizon_of_ancestor f ha
  exact hf q hq s hs hanc

/-- Future infima across a deterministic restart split into the old and fresh windows. -/
theorem futureInf_restart_window (f : DLoc) (t r : ℝ≥0) {s : ℝ≥0} (hst : s ≤ t) :
    futureInf f (t + r) s = min (futureInf f t s)
      (f.1 t + futureInf (DLoc.shift t f) r 0) := by
  rw [futureInf_split f hst (le_add_right le_rfl)]
  have he := futureInf_eq_runningInf_shift f (t + r) t
  rw [min_eq_left (le_add_right le_rfl), add_tsub_cancel_left,
    ← futureInf_zero_eq_runningInf] at he
  rw [he]

end BGW.StableTrees
