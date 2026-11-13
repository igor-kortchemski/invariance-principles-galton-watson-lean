/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.Skorokhod.RestrictContinuity

/-!
# Infima of càdlàg paths on suffixes and windows

Suffix and bounded-window infima are J1-continuous at paths continuous at the relevant
left endpoint. The window statement is obtained by restriction to an initial segment.
-/

@[expose] public section

open Set Filter Topology
open BGW.Skorokhod

namespace BGW.Skorokhod

/-- The infimum of a compact càdlàg path over a suffix beginning at `c`. -/
noncomputable def suffixInf {T : ℝ} (f : D T ℝ) (c : Icc (0 : ℝ) T) : ℝ :=
  ⨅ s : {s : Icc (0 : ℝ) T // c ≤ s}, f s

private theorem bddBelow_suffix {T : ℝ} (g : D T ℝ) (c : Icc (0 : ℝ) T) :
    BddBelow (range fun s : {s : Icc (0 : ℝ) T // c ≤ s} => g s) := by
  obtain ⟨C, hC⟩ : ∃ C, ∀ x y : Icc (0 : ℝ) T, dist (g x) (g y) ≤ C := by
    rw [← Metric.isBounded_range_iff]
    exact isBounded_range g
  refine ⟨g c - C, ?_⟩
  rintro _ ⟨s, rfl⟩
  have he : |g s - g c| ≤ C := by simpa only [Real.dist_eq] using hC s c
  linarith [(abs_le.mp he).1]

/-- Suffix infima are J1-continuous at paths continuous at the initial endpoint. -/
theorem continuousAt_suffixInf {T : ℝ} {c : Icc (0 : ℝ) T} {f : D T ℝ}
    (hf : ContinuousAt f c) : ContinuousAt (fun g : D T ℝ => suffixInf g c) f := by
  have hT : 0 ≤ T := c.2.1.trans c.2.2
  have : Nonempty {s : Icc (0 : ℝ) T // c ≤ s} := ⟨⟨c, le_rfl⟩⟩
  have hle (g : D T ℝ) (s : Icc (0 : ℝ) T) (hs : c ≤ s) : suffixInf g c ≤ g s :=
    ciInf_le (bddBelow_suffix g c) ⟨s, hs⟩
  obtain ⟨σ, hd, hp⟩ :=
    (tendsto_iff_exists_timeChange (u := id) (f := f)).mp tendsto_id
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨η, hη, hfη⟩ := (Metric.continuousAt_iff.mp hf) (ε / 4) (by positivity)
  have hd' := (tendsto_order.1 hd).2 η hη
  have hp' := (tendsto_order.1 hp).2 (ε / 4) (by positivity)
  have hc' := Metric.tendsto_nhds.mp (continuousAt_eval hf) (ε / 4) (by positivity)
  filter_upwards [hd', hp', hc'] with g hgd hgp hgc
  have hdisp (s : Icc (0 : ℝ) T) : |(σ g s : ℝ) - s| < η :=
    (le_ciSup (bddAbove_displacement hT (σ g)) s).trans_lt hgd
  have hval (s : Icc (0 : ℝ) T) : dist (g (σ g s)) (f s) < ε / 4 :=
    (le_ciSup (bddAbove_comp_dist hT g f (σ g)) s).trans_lt hgp
  have hlower : suffixInf f c - ε / 2 ≤ suffixInf g c := by
    apply le_ciInf
    intro s
    let v := (σ g).symm s.val
    have hv : dist (g s.val) (f v) < ε / 4 := by
      simpa only [v, OrderIso.apply_symm_apply] using hval v
    by_cases hcv : c ≤ v
    · have hh := hle f v hcv
      rw [Real.dist_eq, abs_lt] at hv
      linarith
    · have hvc : (v : ℝ) < c := lt_of_not_ge hcv
      have hcs : (c : ℝ) ≤ (σ g v : ℝ) := by
        simpa only [v, OrderIso.apply_symm_apply] using
          (show (c : ℝ) ≤ (s.val : ℝ) from s.2)
      have hvη : dist v c < η := by
        rw [Subtype.dist_eq, Real.dist_eq, abs_lt]
        have hh := abs_lt.mp (hdisp v)
        constructor <;> linarith
      have hh := hfη hvη
      have hc := hle f c le_rfl
      rw [Real.dist_eq, abs_lt] at hh hv
      linarith
  have hupper : suffixInf g c - ε / 2 ≤ suffixInf f c := by
    apply le_ciInf
    intro v
    by_cases hcs : c ≤ σ g v.val
    · have hb := hle g (σ g v.val) hcs
      have hv := hval v.val
      rw [Real.dist_eq, abs_lt] at hv
      linarith
    · have hsc : (σ g v.val : ℝ) < c := lt_of_not_ge hcs
      have hcv : (c : ℝ) ≤ v.val := v.2
      have hvη : dist v.val c < η := by
        rw [Subtype.dist_eq, Real.dist_eq, abs_lt]
        have hh := abs_lt.mp (hdisp v.val)
        constructor <;> linarith
      have hh := hfη hvη
      have hc := hle g c le_rfl
      rw [Real.dist_eq, abs_lt] at hh hgc
      linarith
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

/-- The infimum of a finite path over a closed subinterval. -/
noncomputable def windowInf {T : ℝ} (f : D T ℝ) {a b : ℝ}
    (ha : 0 ≤ a) (_hab : a ≤ b) (hbT : b ≤ T) : ℝ :=
  ⨅ u : Icc a b, f ⟨u, ha.trans u.2.1, u.2.2.trans hbT⟩

private theorem windowInf_eq_suffixInf {T a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hbT : b ≤ T) (f : D T ℝ) :
    windowInf f ha hab hbT = suffixInf (restrict hbT f) ⟨a, ha, hab⟩ := by
  let e : {s : Icc (0 : ℝ) b // (⟨a, ha, hab⟩ : Icc (0 : ℝ) b) ≤ s} ≃ Icc a b :=
    { toFun := fun u => ⟨u.1, u.2, u.1.2.2⟩
      invFun := fun u => ⟨⟨u, ha.trans u.2.1, u.2.2⟩, u.2.1⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact (Equiv.iInf_comp (g := fun u : Icc a b =>
    f ⟨u, ha.trans u.2.1, u.2.2.trans hbT⟩) e).symm

/-- Window infima are J1-continuous if both endpoints are continuity points; the
original terminal endpoint needs no continuity premise. -/
theorem continuousAt_windowInf {T a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hbT : b ≤ T)
    {f : D T ℝ} (hfa : ContinuousAt f ⟨a, ha, hab.trans hbT⟩)
    (hfb : b = T ∨ ContinuousAt f ⟨b, ha.trans hab, hbT⟩) :
    ContinuousAt (fun g : D T ℝ => windowInf g ha hab hbT) f := by
  let c : Icc (0 : ℝ) b := ⟨a, ha, hab⟩
  let inc : Icc (0 : ℝ) b → Icc (0 : ℝ) T :=
    fun u => ⟨u, u.2.1, u.2.2.trans hbT⟩
  have hinc : Continuous inc := Continuous.subtype_mk continuous_subtype_val _
  have hfc0 : ContinuousAt (f ∘ inc) c := hfa.comp hinc.continuousAt
  have hfc : ContinuousAt (restrict hbT f) c := hfc0
  have hr : ContinuousAt (restrict (E := ℝ) hbT) f := by
    rcases hfb with he | hf
    · subst b
      have heq : restrict (E := ℝ) hbT = id := by
        funext g
        apply BGW.Skorokhod.ext
        intro u
        rfl
      rw [heq]
      exact continuousAt_id
    · exact continuousAt_restrict (ha.trans hab) hbT hf
  have hs := (continuousAt_suffixInf hfc).comp hr
  simpa only [Function.comp_def, c, ← windowInf_eq_suffixInf ha hab hbT] using hs

end BGW.Skorokhod
