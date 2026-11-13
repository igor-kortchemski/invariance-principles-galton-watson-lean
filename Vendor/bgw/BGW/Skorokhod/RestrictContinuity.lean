/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.Skorokhod.RestrictContinuityTimeChange

/-!
# Continuity of restriction and stopping

Restriction is continuous at paths continuous at the new terminal endpoint.
-/

@[expose] public section

open Set Filter Topology

namespace BGW.Skorokhod

variable {T : ℝ} {E : Type*}

/-- Restriction is continuous at every path continuous at `a` (C6.2). -/
theorem continuousAt_restrict [MetricSpace E] {a : ℝ} (ha : 0 ≤ a) (haT : a ≤ T) {f : D T E}
    (hf : ContinuousAt f ⟨a, ha, haT⟩) : ContinuousAt (restrict haT) f := by
  by_cases ha0 : a = 0
  · subst a
    let C : E → D 0 E := fun x => ⟨fun _ => x, IsCadlag.const⟩
    have hC : LipschitzWith 1 C := by
      apply LipschitzWith.mk_one
      intro x y
      have : Nonempty (Icc (0 : ℝ) 0) := ⟨⟨0, le_rfl, le_rfl⟩⟩
      simpa [C] using dist_le_iSup_dist (C x) (C y)
    have heq : restrict haT = C ∘ (fun g : D T E => g ⟨0, ha, haT⟩) := by
      funext g
      apply ext
      intro t
      have ht : (t : ℝ) = 0 := le_antisymm t.2.2 t.2.1
      exact congrArg g (Subtype.ext ht)
    rw [heq]
    exact hC.continuous.continuousAt.comp (continuousAt_eval hf)
  have : Nonempty (Icc (0 : ℝ) a) := ⟨⟨0, le_rfl, ha⟩⟩
  have ha' : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
  let inc : Icc (0 : ℝ) a → Icc (0 : ℝ) T := fun t =>
    ⟨t, t.2.1, t.2.2.trans haT⟩
  have hinc : Continuous inc := Continuous.subtype_mk continuous_subtype_val _
  obtain ⟨σ, hd, hp⟩ :=
    (tendsto_iff_exists_timeChange (u := id) (f := f)).mp tendsto_id
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨η, hη, hfη⟩ := (Metric.continuousAt_iff.mp hf) (ε / 4) (by positivity)
  let δ := min (min (η / 4) (ε / 4)) (a / 2)
  have hδ : 0 < δ := lt_min (lt_min (by positivity) (by positivity)) (by positivity)
  have hδη : δ ≤ η / 4 := (min_le_left _ _).trans (min_le_left _ _)
  have hδε : δ ≤ ε / 4 := (min_le_left _ _).trans (min_le_right _ _)
  have hδa : δ ≤ a / 2 := min_le_right _ _
  let r := a - δ
  have hr : 0 ≤ r := by dsimp [r]; linarith
  have hra : r < a := by dsimp [r]; linarith
  let R : Icc (0 : ℝ) a := ⟨r, hr, hra.le⟩
  have hd' : ∀ᶠ g in 𝓝 f, (⨆ t, |(σ g t : ℝ) - t|) < δ / 2 := by
    filter_upwards [(tendsto_order.1 hd).2 (δ / 2) (by positivity)] with g hg using hg
  have hp' : ∀ᶠ g in 𝓝 f, (⨆ t, dist (g (σ g t)) (f t)) < ε / 4 := by
    filter_upwards [(tendsto_order.1 hp).2 (ε / 4) (by positivity)] with g hg using hg
  filter_upwards [hd', hp'] with g hgd hgp
  have hdisp (t : Icc (0 : ℝ) T) : |(σ g t : ℝ) - t| < δ / 2 :=
    (le_ciSup (bddAbove_displacement (ha.trans haT) (σ g)) t).trans_lt hgd
  have hval (t : Icc (0 : ℝ) T) : dist (g (σ g t)) (f t) < ε / 4 :=
    (le_ciSup (bddAbove_comp_dist (ha.trans haT) g f (σ g)) t).trans_lt hgp
  have hR : (σ g (inc R) : ℝ) < a := by
    have hh := (abs_lt.mp (hdisp (inc R))).2
    change (σ g (inc R) : ℝ) - r < δ / 2 at hh
    dsimp [r] at hh ⊢
    linarith
  obtain ⟨τ, hhead, htail⟩ := exists_endpoint_timeChange hr hra
    (fun t => (σ g (inc t) : ℝ))
    (continuous_subtype_val.comp ((σ g).continuous.comp hinc))
    (fun x y hxy => (σ g).strictMono hxy)
    (by simpa [inc] using congrArg Subtype.val (TimeChange.apply_zero (σ g) (ha.trans haT))) hR
  have htime (t : Icc (0 : ℝ) a) : |(τ t : ℝ) - t| ≤ ε / 2 := by
    by_cases ht : (t : ℝ) ≤ r
    · rw [hhead t ht]
      exact (hdisp (inc t)).le.trans (by linarith)
    · have hrt := htail t (le_of_not_ge ht)
      have hRdisp := abs_lt.mp (hdisp (inc R))
      have hta := t.2.2
      have hτa := (τ t).2.2
      change -(δ / 2) < (σ g (inc R) : ℝ) - r ∧
        (σ g (inc R) : ℝ) - r < δ / 2 at hRdisp
      rw [abs_le]
      dsimp [r] at *
      constructor <;> linarith
  have hpath (t : Icc (0 : ℝ) a) :
      dist ((restrict haT f) t) ((restrict haT g) (τ t)) ≤ 3 * ε / 4 := by
    by_cases ht : (t : ℝ) ≤ r
    · have heq : inc (τ t) = σ g (inc t) := Subtype.ext (hhead t ht)
      change dist (f (inc t)) (g (inc (τ t))) ≤ _
      rw [heq, dist_comm]
      exact (hval (inc t)).le.trans (by linarith)
    · let v := (σ g).symm (inc (τ t))
      have hv : dist (g (inc (τ t))) (f v) < ε / 4 := by
        simpa only [v, OrderIso.apply_symm_apply] using hval v
      have hrv : inc R ≤ v := by
        apply (σ g).le_iff_le.mp
        change (σ g (inc R) : ℝ) ≤ (σ g v : ℝ)
        simpa only [v, OrderIso.apply_symm_apply] using htail t (le_of_not_ge ht)
      have hvd := abs_lt.mp (hdisp v)
      have hvη : dist v ⟨a, ha, haT⟩ < η := by
        rw [Subtype.dist_eq, Real.dist_eq, abs_lt]
        have hvupper : (σ g v : ℝ) ≤ a := by
          simpa only [v, OrderIso.apply_symm_apply] using (τ t).2.2
        change r ≤ (v : ℝ) at hrv
        dsimp [r] at hrv
        constructor <;> linarith
      have htη : dist (inc t) ⟨a, ha, haT⟩ < η := by
        rw [Subtype.dist_eq, Real.dist_eq, abs_lt]
        have ht' : r < (t : ℝ) := lt_of_not_ge ht
        have hta := t.2.2
        change -η < (t : ℝ) - a ∧ (t : ℝ) - a < η
        dsimp [r] at ht'
        constructor <;> linarith
      change dist (f (inc t)) (g (inc (τ t))) ≤ _
      calc
        _ ≤ dist (f (inc t)) (f ⟨a, ha, haT⟩) +
            dist (f ⟨a, ha, haT⟩) (f v) + dist (f v) (g (inc (τ t))) :=
          dist_triangle4 _ _ _ _
        _ ≤ 3 * ε / 4 := by
          rw [dist_comm (f ⟨a, ha, haT⟩) (f v),
            dist_comm (f v) (g (inc (τ t)))]
          have hh := hfη htη
          have hh' := hfη hvη
          linarith
  rw [dist_comm, dist_eq_j1Dist]
  apply lt_of_le_of_lt (j1Dist_le_timeChange_cost ha _ _ τ)
  apply max_lt
  · exact (ciSup_le htime).trans_lt (by linarith)
  · exact (ciSup_le hpath).trans_lt (by linarith)

/-- Stopping at `a` is continuous at every path continuous at `a` (C6.2). -/
theorem continuousAt_stop [MetricSpace E] {a : ℝ} (ha : 0 ≤ a) (haT : a ≤ T) {f : D T E}
    (hf : ContinuousAt f ⟨a, ha, haT⟩) : ContinuousAt (stop a) f := by
  have heq : stop (E := E) a = extendConst ha haT ∘ restrict haT := by
    funext g
    exact stop_eq_extendConst_restrict ha haT g
  rw [heq]
  exact (lipschitzWith_one_extendConst ha haT).continuous.continuousAt.comp
    (continuousAt_restrict ha haT hf)


private theorem bddAbove_oscillation (g : D T ℝ) (c : Icc (0 : ℝ) T) :
    BddAbove (range fun s : {s : Icc (0 : ℝ) T // c ≤ s} => |g s - g c|) := by
  let k : D T ℝ := ⟨fun _ => g c, IsCadlag.const⟩
  obtain ⟨B, hB⟩ := bddAbove_range_dist g k (OrderIso.refl _)
  refine ⟨B, ?_⟩
  rintro _ ⟨s, rfl⟩
  simpa [k, Real.dist_eq] using hB ⟨s, rfl⟩

/-- The oscillation `sup_{s ≥ c} |g s - g c|` after time `c` is continuous at every path
continuous at `c` (C6.3). -/
theorem continuousAt_oscillationFrom {c : Set.Icc (0 : ℝ) T} {f : D T ℝ}
    (hf : ContinuousAt f c) :
    ContinuousAt (fun g : D T ℝ => ⨆ s : {s : Set.Icc (0 : ℝ) T // c ≤ s}, |g s - g c|) f := by
  let O := fun g : D T ℝ => ⨆ s : {s : Icc (0 : ℝ) T // c ≤ s}, |g s - g c|
  have hnonneg (g : D T ℝ) : 0 ≤ O g := by
    simpa [O] using le_ciSup (bddAbove_oscillation g c) ⟨c, le_rfl⟩
  have hT : 0 ≤ T := c.2.1.trans c.2.2
  have : Nonempty {s : Icc (0 : ℝ) T // c ≤ s} := ⟨⟨c, le_rfl⟩⟩
  obtain ⟨σ, hd, hp⟩ :=
    (tendsto_iff_exists_timeChange (u := id) (f := f)).mp tendsto_id
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨η, hη, hfη⟩ := (Metric.continuousAt_iff.mp hf) (ε / 8) (by positivity)
  have hd' := (tendsto_order.1 hd).2 η hη
  have hp' := (tendsto_order.1 hp).2 (ε / 8) (by positivity)
  have hc' := Metric.tendsto_nhds.mp (continuousAt_eval hf) (ε / 8) (by positivity)
  filter_upwards [hd', hp', hc'] with g hgd hgp hgc
  have hdisp (t : Icc (0 : ℝ) T) : |(σ g t : ℝ) - t| < η :=
    (le_ciSup (bddAbove_displacement hT (σ g)) t).trans_lt hgd
  have hval (t : Icc (0 : ℝ) T) : dist (g (σ g t)) (f t) < ε / 8 :=
    (le_ciSup (bddAbove_comp_dist hT g f (σ g)) t).trans_lt hgp
  have hupper : O g ≤ O f + ε / 2 := by
    apply ciSup_le
    intro s
    let v := (σ g).symm s.val
    have hv : dist (g s.val) (f v) < ε / 8 := by
      simpa only [v, OrderIso.apply_symm_apply] using hval v
    have hfv : |f v - f c| ≤ O f + ε / 8 := by
      by_cases hcv : c ≤ v
      · exact (le_ciSup (bddAbove_oscillation f c) ⟨v, hcv⟩).trans (by linarith)
      · have hvc : (v : ℝ) < c := lt_of_not_ge hcv
        have hcs : (c : ℝ) ≤ (σ g v : ℝ) := by
          simpa only [v, OrderIso.apply_symm_apply] using
            (show (c : ℝ) ≤ (s.val : ℝ) from s.2)
        have hvη : dist v c < η := by
          rw [Subtype.dist_eq, Real.dist_eq, abs_lt]
          have hh := abs_lt.mp (hdisp v)
          constructor <;> linarith
        have hh := hfη hvη
        rw [Real.dist_eq] at hh
        linarith [hnonneg f]
    have htri := dist_triangle4 (g s.val) (f v) (f c) (g c)
    simp only [Real.dist_eq] at hv hgc htri
    change |g s.val - g c| ≤ O f + ε / 2
    have habs : |f c - g c| = |g c - f c| := abs_sub_comm _ _
    linarith
  have hlower : O f ≤ O g + ε / 2 := by
    apply ciSup_le
    intro v
    by_cases hcs : c ≤ σ g v.val
    · have hb : |g (σ g v.val) - g c| ≤ O g :=
        le_ciSup (bddAbove_oscillation g c) ⟨σ g v.val, hcs⟩
      have hv := hval v.val
      have htri := dist_triangle4 (f v.val) (g (σ g v.val)) (g c) (f c)
      simp only [Real.dist_eq] at hv hgc htri
      have habs : |f v.val - g (σ g v.val)| = |g (σ g v.val) - f v.val| :=
        abs_sub_comm _ _
      change |f v.val - f c| ≤ O g + ε / 2
      linarith
    · have hsc : (σ g v.val : ℝ) < c := lt_of_not_ge hcs
      have hcv : (c : ℝ) ≤ v.val := v.2
      have hvη : dist v.val c < η := by
        rw [Subtype.dist_eq, Real.dist_eq, abs_lt]
        have hh := abs_lt.mp (hdisp v.val)
        constructor <;> linarith
      have hh := hfη hvη
      rw [Real.dist_eq] at hh
      change |f v.val - f c| ≤ O g + ε / 2
      linarith [hnonneg g]
  change dist (O g) (O f) < ε
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

end BGW.Skorokhod
