/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.MarkedExcursionsSupport
import Mathlib.Algebra.Order.GroupWithZero.OrderIso

/-!
# Scaling the marked excursion measure

Time dilation is an order isomorphism, so it commutes with the infima defining passage times
and the suprema defining their left endpoints. Excursion cuts scale with these endpoints.

(J. Bertoin, *Lévy Processes*, Cambridge University Press, 1996, Chapter IV and Chapter VIII.)
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees

private theorem passage_scale_inf {f F : DLoc} {w b : ℝ≥0} (hw : 0 < w) (hb : 0 < b)
    (hF : ∀ t, F.1 (b * t) = (w : ℝ) * f.1 t) (x : ℝ≥0) :
    firstPassageBelow (w * x) F =
      (OrderIso.mulLeft₀ b hb).withTopCongr (firstPassageBelow x f) := by
  let e := OrderIso.mulLeft₀ b hb
  have hp (t : ℝ≥0) : F.1 (b * t) < -((w * x : ℝ≥0) : ℝ) ↔ f.1 t < -(x : ℝ) := by
    rw [hF, NNReal.coe_mul]
    have hw' : 0 < (w : ℝ) := by exact_mod_cast hw
    constructor <;> intro h <;> nlinarith
  change (⨅ (t : ℝ≥0) (_ : F.1 t < -((w * x : ℝ≥0) : ℝ)), (t : WithTop ℝ≥0)) =
    e.withTopCongr (⨅ (t : ℝ≥0) (_ : f.1 t < -(x : ℝ)), (t : WithTop ℝ≥0))
  rw [← e.toEquiv.iInf_comp (g := fun t =>
    ⨅ _ : F.1 t < -((w * x : ℝ≥0) : ℝ), (t : WithTop ℝ≥0))]
  simp only [OrderIso.map_iInf]
  apply iInf_congr
  intro t
  change (⨅ (_ : F.1 (b * t) < -((w * x : ℝ≥0) : ℝ)), ((b * t : ℝ≥0) : WithTop ℝ≥0)) = _
  simp only [hp]
  rfl
private theorem passage_sup {f : DLoc}
    (hT : ∀ x, firstPassageBelow x f = (passageTime x f : WithTop ℝ≥0)) (x : ℝ≥0) :
    (⨆ y : Set.Iio x, firstPassageBelow y f) = (passageTimeMinus x f : WithTop ℝ≥0) := by
  have hb : (⨆ y : Set.Iio x, firstPassageBelow y f) ≤ firstPassageBelow x f :=
    iSup_le fun y => firstPassageBelow_mono f y.2.le
  obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.mp
    (ne_top_of_le_ne_top (by rw [hT x]; exact WithTop.coe_ne_top) hb)
  simp only [passageTimeMinus, ← ht, WithTop.untopD_coe]

private theorem passageMinus_scale {f F : DLoc} {w b : ℝ≥0} (hw : 0 < w) (hb : 0 < b)
    (hF : ∀ t, F.1 (b * t) = (w : ℝ) * f.1 t)
    (hT : ∀ x, firstPassageBelow x f = (passageTime x f : WithTop ℝ≥0)) (x : ℝ≥0) :
    passageTimeMinus (w * x) F = b * passageTimeMinus x f := by
  let e : Iio x ≃ Iio (w * x) :=
    { toFun := fun y => ⟨w * y, (OrderIso.mulLeft₀ w hw).strictMono y.2⟩
      invFun := fun z => ⟨(z : ℝ≥0) / w, (div_lt_iff₀ hw).mpr
        (by simpa only [mul_comm] using (show (z : ℝ≥0) < w * x from z.2))⟩
      left_inv := fun y => Subtype.ext (mul_div_cancel_left₀ _ hw.ne')
      right_inv := fun z => Subtype.ext (mul_div_cancel₀ _ hw.ne') }
  have hsup : (⨆ y : Iio (w * x), firstPassageBelow y F) =
      (OrderIso.mulLeft₀ b hb).withTopCongr (⨆ y : Iio x, firstPassageBelow y f) := by
    rw [← e.iSup_comp, OrderIso.map_iSup]
    apply iSup_congr
    intro y
    exact passage_scale_inf hw hb hF y
  rw [passage_sup hT x] at hsup
  unfold passageTimeMinus
  rw [hsup]
  rfl

private theorem scaleLoc_mul_eval (θ : ℝ) (c : Ioi (0 : ℝ)) (f : DLoc) (t : ℝ≥0) :
    (scaleLoc θ c f).1 ((c : ℝ).toNNReal * t) =
      (((c : ℝ).toNNReal ^ (1 / θ) : ℝ≥0) : ℝ) * f.1 t := by
  change (c : ℝ) ^ (1 / θ) * f.1 (((c : ℝ).toNNReal * t) / (c : ℝ).toNNReal) = _
  rw [mul_div_cancel_left₀ _ (ne_of_gt (Real.toNNReal_pos.mpr c.2)),
    NNReal.coe_rpow, Real.coe_toNNReal _ c.2.le]

private theorem excursionCut_scale {θ : ℝ} (c : Ioi (0 : ℝ)) {f : DLoc} {g d : ℝ≥0}
    (hc : cutValid g d f) :
    excursionCut ((c : ℝ).toNNReal * g) ((c : ℝ).toNNReal * d) (scaleLoc θ c f) =
      excursionScale θ c (excursionCut g d f) := by
  let b := (c : ℝ).toNNReal
  have hb : 0 < b := Real.toNNReal_pos.mpr c.2
  have hA : 0 < (c : ℝ) ^ (1 / θ) := Real.rpow_pos_of_pos c.2 _
  have hev (t : ℝ≥0) : (scaleLoc θ c f).1 (b * t) =
      (c : ℝ) ^ (1 / θ) * f.1 t := by
    change (c : ℝ) ^ (1 / θ) * f.1 (b * t / b) = _
    rw [mul_div_cancel_left₀ _ hb.ne']
  have hc' : cutValid (b * g) (b * d) (scaleLoc θ c f) := by
    refine ⟨(OrderIso.mulLeft₀ b hb).strictMono hc.1, ?_, ?_⟩
    · rw [hev, hev, hc.2.1]
    · intro t hgt htd
      have ht : t = b * (t / b) := (mul_div_cancel₀ _ hb.ne').symm
      rw [ht, hev, hev]
      apply mul_le_mul_of_nonneg_left _ hA.le
      apply hc.2.2
      · apply (le_div_iff₀ hb).mpr
        simpa only [mul_comm] using hgt
      · apply (div_le_iff₀ hb).mpr
        simpa only [mul_comm] using htd
  apply Subtype.ext
  apply Prod.ext
  · apply Subtype.ext
    funext t
    change (excursionCut (b * g) (b * d) (scaleLoc θ c f)).path.1 t =
      (c : ℝ) ^ (1 / θ) * (excursionCut g d f).path.1 (t / b)
    rw [excursionCut_eval hc', excursionCut_eval hc]
    change (c : ℝ) ^ (1 / θ) * f.1 (min (b * g + t) (b * d) / b) -
      (c : ℝ) ^ (1 / θ) * f.1 (b * g / b) = _
    have hmin : min (b * g + t) (b * d) / b = min (g + t / b) d := by
      rw [← min_div_div_right hb.le, add_div, mul_div_cancel_left₀ _ hb.ne',
        mul_div_cancel_left₀ _ hb.ne']
    rw [hmin, mul_div_cancel_left₀ _ hb.ne']
    ring
  · apply Subtype.ext
    change (excursionCut (b * g) (b * d) (scaleLoc θ c f)).lifetime =
      b * (excursionCut g d f).lifetime
    rw [excursionCut_lifetime hc', excursionCut_lifetime hc, mul_tsub]

/-- **Marked scaling** (convention `scaleLoc θ c f t = c^{1/θ} f (t/c)`, `excursionScale θ c e t =
c^{1/θ} e (t/c)`): for each `c > 0`, a.s. the point measure of `scaleLoc θ c f` is the image of that
of `f` under `(x, e) ↦ (c^{1/θ} x, S_c e)`.  (Taking `c = 1/c'` gives the path `c'^{-1/θ} X_{c' ·}`
and the map `(c'^{-1/θ} x, S_{1/c'} e)`.) -/
theorem ae_excursionPointMeasure_scaleLoc {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (c : Set.Ioi (0 : ℝ)) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc),
      excursionPointMeasure (scaleLoc θ c f) =
        Measure.map (fun p : ℝ≥0 × Excursion =>
            ((c : ℝ).toNNReal ^ (1 / θ) * p.1, excursionScale θ c p.2))
          (excursionPointMeasure f) := by
  filter_upwards [ae_passageTime_eq_firstPassageBelow hθ, ae_jumpExcursion_spec hθ,
    ae_passageJumpSet_countable hθ] with f hT hs hcount
  classical
  let b := (c : ℝ).toNNReal
  let w : ℝ≥0 := b ^ (1 / θ)
  let F := scaleLoc θ c f
  have hb : 0 < b := Real.toNNReal_pos.mpr c.2
  have hw : 0 < w := by
    rw [← NNReal.coe_pos]
    change 0 < ((b ^ (1 / θ) : ℝ≥0) : ℝ)
    rw [NNReal.coe_rpow]
    exact Real.rpow_pos_of_pos (by exact_mod_cast hb) _
  have hF (t : ℝ≥0) : F.1 (b * t) = (w : ℝ) * f.1 t := scaleLoc_mul_eval θ c f t
  have hpass (x : ℝ≥0) : firstPassageBelow (w * x) F =
      ((b * passageTime x f : ℝ≥0) : WithTop ℝ≥0) := by
    rw [passage_scale_inf hw hb hF x, hT.1 x]
    rfl
  have htime (x : ℝ≥0) : passageTime (w * x) F = b * passageTime x f := by
    unfold passageTime
    rw [hpass x]
    rfl
  have hminus (x : ℝ≥0) : passageTimeMinus (w * x) F = b * passageTimeMinus x f :=
    passageMinus_scale hw hb hF hT.1 x
  have hJ (x : ℝ≥0) : w * x ∈ passageJumpSet F ↔ x ∈ passageJumpSet f := by
    change (0 < w * x ∧ passageTimeMinus (w * x) F < passageTime (w * x) F) ↔ _
    rw [htime, hminus]
    have hpos : 0 < w * x ↔ 0 < x := by
      have he : w * 0 < w * x ↔ 0 < x := (OrderIso.mulLeft₀ w hw).lt_iff_lt
      simpa only [mul_zero] using he
    rw [hpos]
    exact and_congr_right fun _ => (OrderIso.mulLeft₀ b hb).lt_iff_lt
  have hJset : passageJumpSet F = (fun x => w * x) '' passageJumpSet f := by
    ext z
    constructor
    · intro hz
      have heq : w * (z / w) = z := mul_div_cancel₀ _ hw.ne'
      refine ⟨z / w, (hJ _).mp (heq.symm ▸ hz), heq⟩
    · rintro ⟨x, hx, rfl⟩
      exact (hJ x).mpr hx
  have hcountF : (passageJumpSet F).Countable := by
    rw [hJset]
    exact hcount.image _
  have hmark (x : ℝ≥0) (hx : x ∈ passageJumpSet f) :
      jumpExcursion (w * x) F = excursionScale θ c (jumpExcursion x f) := by
    unfold jumpExcursion
    rw [htime, hminus]
    exact excursionCut_scale c (hs x hx).1
  have hm : Measurable (fun p : ℝ≥0 × Excursion => (w * p.1, excursionScale θ c p.2)) :=
    (measurable_const.mul measurable_fst).prodMk
      ((measurable_excursionScale θ c).comp measurable_snd)
  ext s hsm
  rw [Measure.map_apply hm hsm, excursionPointMeasure_apply hcountF hsm,
    excursionPointMeasure_apply hcount (hm hsm)]
  let A : Set ℝ≥0 := {z ∈ passageJumpSet F | (z, jumpExcursion z F) ∈ s}
  let B : Set ℝ≥0 := {x ∈ passageJumpSet f | (w * x, excursionScale θ c (jumpExcursion x f)) ∈ s}
  let e₀ : B → A := fun x => ⟨w * x, (hJ x).mpr x.2.1, by
    rw [hmark x x.2.1]
    exact x.2.2⟩
  have hinj : Function.Injective e₀ := by
    intro x y h
    exact Subtype.ext ((OrderIso.mulLeft₀ w hw).injective (congrArg Subtype.val h))
  have hsurj : Function.Surjective e₀ := by
    intro z
    have heq : w * ((z : ℝ≥0) / w) = z := mul_div_cancel₀ _ hw.ne'
    have hx : (z : ℝ≥0) / w ∈ passageJumpSet f := (hJ _).mp (heq.symm ▸ z.2.1)
    refine ⟨⟨(z : ℝ≥0) / w, hx, ?_⟩, Subtype.ext heq⟩
    rw [← hmark _ hx, heq]
    exact z.2.2
  exact congrArg (fun n : ℕ∞ => (n : ℝ≥0∞))
    (Set.encard_congr (Equiv.ofBijective e₀ ⟨hinj, hsurj⟩)).symm

end BGW.StableTrees
