/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.ExcursionLifetime
public import BGW.StableTrees.ExcursionMeasure
public import BGW.StableTrees.MarkedExcursions
public import BGW.StableTrees.UnitExcursionLaw
public import BGW.StableTrees.StraddlingExcursionPotential

/-!
# The excursion straddling a fixed time

Extraction of the passage jump containing a fixed positive time, with its lifetime,
normalized path and measurable data.

## References

J. Bertoin, *Lévy Processes*, Cambridge University Press, 1996, Chapter IV.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees

/-! ### Definitions -/

/-- Start `g_t = T_{L_t -}` of the excursion straddling `t`. -/
noncomputable def straddleStart (t : ℝ≥0) (f : DLoc) : ℝ≥0 :=
  passageTimeMinus (localTimeNN f t) f

/-- End `d_t = T_{L_t}` of the excursion straddling `t`. -/
noncomputable def straddleEnd (t : ℝ≥0) (f : DLoc) : ℝ≥0 :=
  passageTime (localTimeNN f t) f

/-- Lifetime `ζ_t = d_t - g_t` as a real number. -/
noncomputable def straddleLife (t : ℝ≥0) (f : DLoc) : ℝ :=
  (straddleEnd t f : ℝ) - (straddleStart t f : ℝ)

/-- The excursion of `X - I` straddling `t`: the cut of `f` at the jump level `L_t`. -/
noncomputable def straddlingExcursion (t : ℝ≥0) (f : DLoc) : Excursion :=
  jumpExcursion (localTimeNN f t) f

/-- Claimed density of `(g_t, ζ_t)` on `ℝ × ℝ`:
`straddleAgeDensity g * lifetimeDensity ζ` on `{0 < g < t < g + ζ}`. -/
noncomputable def straddleDensity (θ : ℝ) (t : ℝ≥0) (p : ℝ × ℝ) : ℝ≥0∞ :=
  {p : ℝ × ℝ | 0 < p.1 ∧ p.1 < (t : ℝ) ∧ (t : ℝ) < p.1 + p.2}.indicator
    (fun p => straddleAgeDensity θ p.1 * lifetimeDensity θ p.2) p

/-- The claimed law of `(g_t, ζ_t)`. -/
noncomputable def straddleLaw (θ : ℝ) (t : ℝ≥0) : Measure (ℝ × ℝ) :=
  volume.withDensity (straddleDensity θ t)

/-- Claimed density of `g_t` on `ℝ`: `g^{α-1} (t-g)^{-α} / (Γ(α) Γ(1-α))` on `(0, t)`. -/
noncomputable def straddleStartDensity (θ : ℝ) (t : ℝ≥0) (g : ℝ) : ℝ≥0∞ :=
  (Ioo (0 : ℝ) (t : ℝ)).indicator
    (fun g => ENNReal.ofReal (g ^ (1 / θ - 1) * ((t : ℝ) - g) ^ (-(1 / θ)) /
      (Real.Gamma (1 / θ) * Real.Gamma (1 - 1 / θ)))) g

/-- Joint data: `((g_t, ζ_t), normalized straddling excursion)`. -/
noncomputable def straddleData (θ : ℝ) (t : ℝ≥0) (f : DLoc) : (ℝ × ℝ) × Excursion :=
  (((straddleStart t f : ℝ), straddleLife t f), normalizeExc θ (straddlingExcursion t f))

/-- **Straddling excursion, a.s. facts** (`g_t < t < d_t`, unique straddling jump level, valid
cut, lifetime tag `d_t - g_t`, and `R_t > 0` for `R = X - I`). -/
theorem ae_straddle_spec {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {t : ℝ≥0} (ht : 0 < t) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc),
      localTimeNN f t ∈ passageJumpSet f ∧
      straddleStart t f < t ∧ t < straddleEnd t f ∧
      0 < (reflectedFrom 0 f).1 t ∧
      cutValid (straddleStart t f) (straddleEnd t f) f ∧
      ((straddlingExcursion t f).lifetime : ℝ) = straddleLife t f ∧
      ∀ x ∈ passageJumpSet f,
        t ∈ Ioo (passageTimeMinus x f) (passageTime x f) → x = localTimeNN f t  := by
  filter_upwards [ae_reflected_pos_fixed hθ ht,
    ae_pos_set_eq_iUnion_jump_intervals hθ, ae_localTime_passageTime hθ,
    ae_jumpExcursion_spec hθ, ae_jump_intervals_disjoint hθ] with f hp hu hL hj hd
  have hm : t ∈ ⋃ x ∈ passageJumpSet f,
      Ioo (passageTimeMinus x f) (passageTime x f) := by
    rw [← hu]
    exact hp
  obtain ⟨x, hx, hxt⟩ := Set.mem_iUnion₂.mp hm
  have heq : x = localTimeNN f t := by
    have hl := runningInfLoc_antitone f hxt.1.le
    have hr := runningInfLoc_antitone f hxt.2.le
    have hg := (hL x).2
    have hdd := (hL x).1
    have hlocal : localTime f t = (x : ℝ) := by
      dsimp [localTime] at hg hdd ⊢
      linarith
    simp [localTimeNN, hlocal]
  subst x
  obtain ⟨hv, hlife, _⟩ := hj _ hx
  refine ⟨hx, hxt.1, hxt.2, hp, hv, ?_, ?_⟩
  · change ((jumpExcursion (localTimeNN f t) f).lifetime : ℝ) = _
    rw [hlife, NNReal.coe_sub hx.2.le]
    rfl
  · intro y hy hyt
    rcases lt_trichotomy y (localTimeNN f t) with hlt | he | hgt
    · exact False.elim ((hyt.2.trans (hd y hy _ hx hlt)).not_gt hxt.1)
    · exact he
    · exact False.elim ((hxt.2.trans (hd _ hx y hy hgt)).not_gt hyt.1)

set_option maxHeartbeats 400000 in
-- Kernel conversion unfolds the local-time and passage definitions in these compositions.
private theorem measurable_localTimeNN_fixed (t : ℝ≥0) :
    Measurable (fun f : DLoc => localTimeNN f t) := by
  have hp : Measurable (fun f : DLoc => (t, f)) := measurable_const.prodMk measurable_id
  have hl : Measurable (fun f : DLoc => localTime f t) :=
    measurable_localTime_uncurry.comp hp
  unfold localTimeNN
  exact measurable_real_toNNReal.comp hl

private theorem measurable_straddleStart (t : ℝ≥0) : Measurable (straddleStart t) := by
  have hp : Measurable (fun f : DLoc => (localTimeNN f t, f)) :=
    (measurable_localTimeNN_fixed t).prodMk measurable_id
  unfold straddleStart
  exact measurable_passageTimeMinus_uncurry.comp hp

private theorem measurable_straddleEnd (t : ℝ≥0) : Measurable (straddleEnd t) := by
  have hp : Measurable (fun f : DLoc => (localTimeNN f t, f)) :=
    (measurable_localTimeNN_fixed t).prodMk measurable_id
  unfold straddleEnd
  exact Measurable.comp
    (g := fun p : ℝ≥0 × DLoc => passageTime p.1 p.2)
    (f := fun f : DLoc => (localTimeNN f t, f))
    measurable_passageTime_uncurry hp

private theorem measurable_straddlingExcursion (t : ℝ≥0) :
    Measurable (straddlingExcursion t) := by
  exact measurable_excursionCut.comp ((measurable_straddleStart t).prodMk
    ((measurable_straddleEnd t).prodMk measurable_id))

/-- The joint data of the straddling excursion is `AEMeasurable` (needed for `Measure.map`). -/
theorem aemeasurable_straddleData {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (t : ℝ≥0) :
    AEMeasurable (straddleData θ t) (stableLocalLaw θ : Measure DLoc)  := by
  have _hθ := hθ -- interface: the stable index is part of the statement, unused in the proof
  exact (((measurable_coe_nnreal_real.comp (measurable_straddleStart t)).prodMk
    ((measurable_coe_nnreal_real.comp (measurable_straddleEnd t)).sub
      (measurable_coe_nnreal_real.comp (measurable_straddleStart t)))).prodMk
    ((measurable_normalizeExc θ).comp (measurable_straddlingExcursion t))).aemeasurable

/-- The straddling excursion itself is `AEMeasurable`. -/
theorem aemeasurable_straddlingExcursion {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (t : ℝ≥0) :
    AEMeasurable (straddlingExcursion t) (stableLocalLaw θ : Measure DLoc)  := by
  have _hθ := hθ -- interface: the stable index is part of the statement, unused in the proof
  exact (measurable_straddlingExcursion t).aemeasurable

/-- **`g_t` and `d_t` as last/first zero of the reflected process** around `t`
(`R = X - I = reflectedFrom 0 f`; `g_t = sup{s ≤ t : R_s = 0}`, `d_t = inf{s > t : R_s = 0}`). -/
theorem ae_straddle_zero_description {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {t : ℝ≥0}
    (ht : 0 < t) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc),
      straddleStart t f = sSup {s : ℝ≥0 | s ≤ t ∧ (reflectedFrom 0 f).1 s = 0} ∧
      straddleEnd t f = sInf {s : ℝ≥0 | t < s ∧ (reflectedFrom 0 f).1 s = 0} := by
  filter_upwards [ae_straddle_spec hθ ht, ae_isExcursionInterval_of_jump hθ] with f hs hi
  have hv := hi _ hs.1
  have hgt : straddleStart t f < t := hs.2.1
  have htd : t < straddleEnd t f := hs.2.2.1
  have hpos : ∀ s, straddleStart t f < s → s < straddleEnd t f →
      0 < (reflectedFrom 0 f).1 s := hv.2.1
  have hg0 : (reflectedFrom 0 f).1 (straddleStart t f) = 0 := hv.2.2.2.1
  have hd0 : (reflectedFrom 0 f).1 (straddleEnd t f) = 0 := hv.2.2.2.2
  constructor
  · apply le_antisymm
    · exact le_csSup ⟨t, fun s hs => hs.1⟩ ⟨hgt.le, hg0⟩
    · apply csSup_le (s := {s : ℝ≥0 | s ≤ t ∧ (reflectedFrom 0 f).1 s = 0})
        ⟨straddleStart t f, hgt.le, hg0⟩
      intro s hs
      by_contra hn
      exact (ne_of_gt (hpos s (lt_of_not_ge hn) (hs.1.trans_lt htd))) hs.2
  · apply le_antisymm
    · apply le_csInf (s := {s : ℝ≥0 | t < s ∧ (reflectedFrom 0 f).1 s = 0})
        ⟨straddleEnd t f, htd, hd0⟩
      intro s hs
      by_contra hn
      exact (ne_of_gt (hpos s (hgt.trans hs.1) (lt_of_not_ge hn))) hs.2
    · exact csInf_le ⟨0, fun s _ => s.2⟩ ⟨htd, hd0⟩

/-- **Chaumont's path formula** (unnormalized `X`): a.s. the normalized straddling
excursion is `s ↦ ζ_t^{-1/θ} (X_{min(g_t + ζ_t s, d_t)} - X_{g_t})`. -/
theorem ae_normalize_straddling_path {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {t : ℝ≥0}
    (ht : 0 < t) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∀ s : ℝ≥0,
      (normalizeExc θ (straddlingExcursion t f)).path.1 s =
        (straddleLife t f) ^ (-(1 / θ)) *
          (f.1 (min (straddleStart t f + (straddleEnd t f - straddleStart t f) * s)
              (straddleEnd t f)) - f.1 (straddleStart t f)) := by
  filter_upwards [ae_straddle_spec hθ ht] with f hs
  have hv := hs.2.2.2.2.1
  have hl := hs.2.2.2.2.2.1
  have he : (straddlingExcursion t f).lifetime = straddleEnd t f - straddleStart t f :=
    excursionCut_lifetime hv
  intro s
  change (((straddlingExcursion t f).lifetime : ℝ)⁻¹) ^ (1 / θ) *
    (straddlingExcursion t f).path.1
      (s / (((straddlingExcursion t f).lifetime : ℝ)⁻¹).toNNReal) = _
  rw [Real.inv_rpow (by positivity), ← Real.rpow_neg (by positivity), hl]
  have hinv : (((straddlingExcursion t f).lifetime : ℝ)⁻¹).toNNReal =
      (straddlingExcursion t f).lifetime⁻¹ := by
    rw [← NNReal.coe_inv, Real.toNNReal_coe]
  rw [← hl, hinv, div_inv_eq_mul, he]
  change _ * (excursionCut (straddleStart t f) (straddleEnd t f) f).path.1 _ = _
  rw [excursionCut_eval hv, mul_comm s]

end BGW.StableTrees
