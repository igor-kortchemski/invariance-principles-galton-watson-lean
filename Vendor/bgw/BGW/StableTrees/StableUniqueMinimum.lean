/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module
public import BGW.StableTrees.StableProcessMarkov
public import BGW.StableTrees.StableDensityAPI
public import BGW.Skorokhod.Vervaat
public import BGW.Skorokhod.MeasurableExtrema

/-!
# Uniqueness of generalized minima of stable Lévy paths

A generalized minimizer of a càdlàg path is a time at which the value or the left limit equals the
infimum. Under a stable Lévy law it is almost surely unique: two distinct minimizers are separated
by rational windows whose generalized minima differ by an atom-free increment independent of both
(P. W. Millar, Zero-one laws and the minimum of a Markov process, Trans. Amer. Math. Soc. 226
(1977), 365–391; J. Bertoin, *Lévy Processes*, Cambridge University Press, 1996, Chapter VI).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped Topology

namespace BGW.StableTrees

open BGW.Skorokhod

/-- Generalized value of `f` at `s`: the minimum of the left limit and the value. -/
noncomputable def genVal {T : ℝ} (f : D T ℝ) (s : Set.Icc (0 : ℝ) T) : ℝ :=
  min (Function.leftLim f s) (f s)

/-- Generalized minimum over a set of times. -/
noncomputable def genMin {T : ℝ} (f : D T ℝ) (J : Set (Set.Icc (0 : ℝ) T)) : ℝ :=
  ⨅ s : J, genVal f s

/-- The window `[a,b]` of times. -/
def window (T a b : ℝ) : Set (Set.Icc (0 : ℝ) T) := {s | a ≤ (s : ℝ) ∧ (s : ℝ) ≤ b}

/-- `g` is a generalized minimizer of `f`. -/
def IsGenMinimizer {T : ℝ} (f : D T ℝ) (g : Set.Icc (0 : ℝ) T) : Prop :=
  genVal f g = ⨅ t, f t

/-- Existence of a generalized minimizer (wrapper of `exists_min_leftLim`). -/
theorem exists_isGenMinimizer {T : ℝ} (hT : 0 ≤ T) (f : D T ℝ) :
    ∃ g, IsGenMinimizer f g :=
  exists_min_leftLim f hT

private theorem iInf_le_leftLim_gen {T : ℝ} (f : D T ℝ) (s : Set.Icc (0 : ℝ) T) :
    (⨅ t, f t) ≤ Function.leftLim f s := by
  apply isClosed_Ici.mem_of_mapClusterPt (mapClusterPt_leftLim f s)
  exact Filter.Eventually.of_forall fun t => ciInf_le (isBounded_range f).bddBelow t

/-- The generalized value is bounded below by the global infimum. -/
theorem iInf_le_genVal {T : ℝ} (f : D T ℝ) (s : Set.Icc (0 : ℝ) T) :
    (⨅ t, f t) ≤ genVal f s :=
  le_min (iInf_le_leftLim_gen f s) (ciInf_le (isBounded_range f).bddBelow s)

private theorem bddBelow_genVal {T : ℝ} (f : D T ℝ) (J : Set (Set.Icc (0 : ℝ) T)) :
    BddBelow (Set.range fun s : J => genVal f s) := by
  refine ⟨⨅ t, f t, ?_⟩
  rintro _ ⟨s, rfl⟩
  exact iInf_le_genVal f s

/-- A generalized minimizer in a window gives the window the global minimum. -/
theorem genMin_eq_iInf_of_mem {T : ℝ} (f : D T ℝ) {J : Set (Set.Icc (0 : ℝ) T)}
    {g : Set.Icc (0 : ℝ) T} (hg : IsGenMinimizer f g) (hgJ : g ∈ J) :
    genMin f J = ⨅ t, f t := by
  let _ : Nonempty J := ⟨⟨g, hgJ⟩⟩
  apply le_antisymm
  · exact (ciInf_le (bddBelow_genVal f J) ⟨g, hgJ⟩).trans_eq hg
  · exact le_ciInf fun s => iInf_le_genVal f s

private theorem genMin_eq_iInf_of_separation {T : ℝ} {f : D T ℝ}
    {g₁ g₂ : Set.Icc (0 : ℝ) T} (h₁₂ : g₁ < g₂)
    (h₁ : IsGenMinimizer f g₁) (h₂ : IsGenMinimizer f g₂) :
    ∃ b c : ℚ, 0 ≤ (b : ℝ) ∧ (b : ℝ) < c ∧ (c : ℝ) ≤ T ∧
      genMin f (window T 0 b) = genMin f (window T c T) := by
  have h₁₂R : (g₁ : ℝ) < g₂ := h₁₂
  obtain ⟨b, hg₁b, hbg₂⟩ := exists_rat_btwn h₁₂R
  obtain ⟨c, hbc, hcg₂⟩ := exists_rat_btwn hbg₂
  have hg₁J : g₁ ∈ window T 0 b := by
    exact ⟨g₁.property.1, hg₁b.le⟩
  have hg₂J : g₂ ∈ window T c T := by
    exact ⟨hcg₂.le, g₂.property.2⟩
  refine ⟨b, c, g₁.property.1.trans hg₁b.le, hbc, hcg₂.le.trans g₂.property.2, ?_⟩
  rw [genMin_eq_iInf_of_mem f h₁ hg₁J, genMin_eq_iInf_of_mem f h₂ hg₂J]

/-- Separation: two distinct generalized minimizers are separated by rationals `b < c`, and the
windows `[0,b]`, `[c,T]` have equal generalized minima. -/
theorem exists_rat_separation {T : ℝ} {f : D T ℝ} {g₁ g₂ : Set.Icc (0 : ℝ) T}
    (h₁ : IsGenMinimizer f g₁) (h₂ : IsGenMinimizer f g₂) (hne : g₁ ≠ g₂) :
    ∃ b c : ℚ, 0 ≤ (b : ℝ) ∧ (b : ℝ) < c ∧ (c : ℝ) ≤ T ∧
      genMin f (window T 0 b) = genMin f (window T c T) := by
  rcases lt_or_gt_of_ne hne with h₁₂ | h₂₁
  · exact genMin_eq_iInf_of_separation h₁₂ h₁ h₂
  · obtain ⟨b, c, hb, hbc, hc, hmin⟩ := genMin_eq_iInf_of_separation h₂₁ h₂ h₁
    exact ⟨b, c, hb, hbc, hc, hmin⟩

/-- If a path has a generalized minimizer but not a unique one, some rational pair separates. -/
theorem exists_rat_pair_of_not_existsUnique {T : ℝ} (hT : 0 ≤ T) {f : D T ℝ}
    (h : ¬ ∃! g : Set.Icc (0 : ℝ) T, IsGenMinimizer f g) :
    ∃ b c : ℚ, 0 ≤ (b : ℝ) ∧ (b : ℝ) < c ∧ (c : ℝ) ≤ T ∧
      genMin f (window T 0 b) = genMin f (window T c T) := by
  obtain ⟨g, hg⟩ := exists_isGenMinimizer hT f
  have hother : ∃ g' : Set.Icc (0 : ℝ) T, IsGenMinimizer f g' ∧ g' ≠ g := by
    by_contra hn
    push Not at hn
    exact h ⟨g, hg, fun g' hg' => hn g' hg'⟩
  obtain ⟨g', hg', hne⟩ := hother
  exact exists_rat_separation hg' hg hne

private theorem genMin_of_empty {T : ℝ} (f : D T ℝ) {J : Set (Set.Icc (0 : ℝ) T)}
    (hJ : J = ∅) : genMin f J = 0 := by
  subst J
  exact (@iSup_of_empty' ℝᵒᵈ (∅ : Set (Set.Icc (0 : ℝ) T)) _ (by simp)
    (fun s => genVal f s)).trans Real.sInf_empty

private theorem iInf_eval_le_leftLim_of_lt {T : ℝ} (f : D T ℝ) {a b : ℝ}
    (ha : 0 ≤ a) (hbT : b ≤ T) (s : Set.Icc (0 : ℝ) T) (has : a < (s : ℝ))
    (hsb : (s : ℝ) ≤ b) :
    (⨅ t : window T a b, f t) ≤ Function.leftLim f s := by
  let _ : Nonempty (window T a b) := ⟨⟨s, has.le, hsb⟩⟩
  apply isClosed_Ici.mem_of_mapClusterPt (mapClusterPt_leftLim f s)
  let aT : Set.Icc (0 : ℝ) T := ⟨a, ha, has.le.trans (hsb.trans hbT)⟩
  have hmem : Set.Ioi aT ∈ 𝓝[Set.Iic s] s :=
    mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds (show aT < s from has))
  filter_upwards [self_mem_nhdsWithin, hmem] with t hts hta
  have htJ : t ∈ window T a b := by
    change aT < t at hta
    exact ⟨hta.le, hts.trans hsb⟩
  exact ciInf_le ((isBounded_range f).bddBelow.mono (by
    rintro _ ⟨t, rfl⟩
    exact ⟨t, rfl⟩)) (⟨t, htJ⟩ : window T a b)

private theorem genMin_window_formula {T : ℝ} (f : D T ℝ) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hbT : b ≤ T) :
    genMin f (window T a b) =
      min (Function.leftLim f ⟨a, ha, hab.trans hbT⟩) (⨅ s : window T a b, f s) := by
  let aT : Set.Icc (0 : ℝ) T := ⟨a, ha, hab.trans hbT⟩
  have haJ : aT ∈ window T a b := ⟨le_rfl, hab⟩
  let _ : Nonempty (window T a b) := ⟨⟨aT, haJ⟩⟩
  apply le_antisymm
  · apply le_min
    · exact (ciInf_le (bddBelow_genVal f _) ⟨aT, haJ⟩).trans (min_le_left _ _)
    · apply le_ciInf
      intro s
      exact (ciInf_le (bddBelow_genVal f _) s).trans (min_le_right _ _)
  · apply le_ciInf
    intro s
    by_cases hs : (s : Set.Icc (0 : ℝ) T) = aT
    · have hval : (⨅ t : window T a b, f t) ≤ f s :=
        ciInf_le ((isBounded_range f).bddBelow.mono (by
          rintro _ ⟨t, rfl⟩
          exact ⟨t, rfl⟩)) s
      have hs' : s = ⟨aT, haJ⟩ := Subtype.ext hs
      rw [hs'] at hval ⊢
      exact le_min (min_le_left _ _) ((min_le_right _ _).trans hval)
    · have has : a < ((s : Set.Icc (0 : ℝ) T) : ℝ) := by
        exact lt_of_le_of_ne s.property.1 (fun h => hs (Subtype.ext h.symm))
      apply le_min
      · exact (min_le_right _ _).trans (iInf_eval_le_leftLim_of_lt f ha hbT s has s.property.2)
      · exact (min_le_right _ _).trans (ciInf_le ((isBounded_range f).bddBelow.mono (by
          rintro _ ⟨t, rfl⟩
          exact ⟨t, rfl⟩)) s)

/-- Measurability of window generalized minima (via rational infima / `measurable_iInf_eval`). -/
theorem measurable_genMinOn {T : ℝ} (a b : ℝ) :
    Measurable (fun f : D T ℝ => genMin f (window T a b)) := by
  let a' := max a 0
  let b' := min b T
  have ha' : 0 ≤ a' := le_max_right _ _
  have hb'T : b' ≤ T := min_le_right _ _
  have hwindow : window T a b = window T a' b' := by
    ext s
    change (a ≤ (s : ℝ) ∧ (s : ℝ) ≤ b) ↔ (a' ≤ (s : ℝ) ∧ (s : ℝ) ≤ b')
    constructor
    · exact fun hs => ⟨max_le hs.1 s.property.1, le_min hs.2 s.property.2⟩
    · exact fun hs => ⟨(le_max_left _ _).trans hs.1, hs.2.trans (min_le_left _ _)⟩
  rw [hwindow]
  by_cases hab : a' ≤ b'
  · have hJ : window T a' b' = Set.Icc ⟨a', ha', hab.trans hb'T⟩
        ⟨b', ha'.trans hab, hb'T⟩ := by
      ext s
      change (a' ≤ (s : ℝ) ∧ (s : ℝ) ≤ b') ↔ _
      rfl
    have hformula (f : D T ℝ) := genMin_window_formula f ha' hab hb'T
    simp_rw [hformula]
    exact (measurable_leftLim_eval _).min (measurable_iInf_eval (hJ ▸ Set.ordConnected_Icc))
  · have hempty : window T a' b' = ∅ := by
      ext s
      simp only [window, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      exact fun hs => hab (hs.1.trans hs.2)
    have heq (f : D T ℝ) := genMin_of_empty f hempty
    simp_rw [heq]
    exact measurable_const

private theorem leftLim_restrict_gen {T b : ℝ} (hbT : b ≤ T) (f : D T ℝ)
    (s : Set.Icc (0 : ℝ) b) :
    Function.leftLim (restrict (E := ℝ) hbT f) s =
      Function.leftLim f ⟨s, s.property.1, s.property.2.trans hbT⟩ := by
  let inc : Set.Icc (0 : ℝ) b → Set.Icc (0 : ℝ) T := fun t =>
    ⟨t, t.property.1, t.property.2.trans hbT⟩
  by_cases hs0 : (s : ℝ) = 0
  · have hsbot : IsBot s := by
      intro t
      change (s : ℝ) ≤ (t : ℝ)
      simpa [hs0] using t.property.1
    have hincbot : IsBot (inc s) := by
      intro t
      change (s : ℝ) ≤ (t : ℝ)
      simpa [hs0] using t.property.1
    rw [leftLim_eq_of_isBot hsbot, leftLim_eq_of_isBot hincbot]
    rfl
  · have hsne : ∃ r : Set.Icc (0 : ℝ) b, r < s := by
      have hb : 0 ≤ b := s.property.1.trans s.property.2
      refine ⟨⟨0, le_rfl, hb⟩, ?_⟩
      change (0 : ℝ) < (s : ℝ)
      exact lt_of_le_of_ne s.property.1 (Ne.symm hs0)
    let _ : (nhdsWithin s (Set.Iio s)).NeBot := nhdsLT_neBot_of_exists_lt hsne
    apply leftLim_eq_of_tendsto
    have hinc : Continuous inc := Continuous.subtype_mk continuous_subtype_val _
    have hmap : Filter.Tendsto inc (nhdsWithin s (Set.Iio s))
        (nhdsWithin (inc s) (Set.Iio (inc s))) := by
      apply tendsto_nhdsWithin_iff.mpr
      refine ⟨tendsto_nhdsWithin_of_tendsto_nhds hinc.continuousAt, ?_⟩
      filter_upwards [self_mem_nhdsWithin] with t ht
      exact ht
    exact ((isCadlag f).tendsto_nhdsLT_leftLim (inc s)).comp hmap

private theorem genVal_restrict_gen {T b : ℝ} (hbT : b ≤ T) (f : D T ℝ)
    (s : Set.Icc (0 : ℝ) b) :
    genVal f (⟨s, s.property.1, s.property.2.trans hbT⟩ : Set.Icc (0 : ℝ) T) =
      genVal (restrict (E := ℝ) hbT f) s := by
  unfold genVal
  rw [leftLim_restrict_gen]
  rfl

/-- The window minimum on `[a,b]` only depends on the restriction to `[0,b]`. -/
theorem genMin_window_eq_restrict {T : ℝ} {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hbT : b ≤ T)
    (f : D T ℝ) :
    genMin f (window T a b) = genMin (restrict (E := ℝ) hbT f) (window b a b) := by
  let _ : Nonempty (window T a b) :=
    ⟨⟨⟨a, ha, hab.trans hbT⟩, le_rfl, hab⟩⟩
  let _ : Nonempty (window b a b) := ⟨⟨⟨a, ha, hab⟩, le_rfl, hab⟩⟩
  apply le_antisymm
  · apply le_ciInf
    intro s
    rw [← genVal_restrict_gen hbT f s]
    exact ciInf_le (bddBelow_genVal f _)
      ⟨⟨s.1, s.1.property.1, s.1.property.2.trans hbT⟩, s.2⟩
  · apply le_ciInf
    intro s
    let u : Set.Icc (0 : ℝ) T := ⟨s.1, s.1.property.1, s.2.2.trans hbT⟩
    let v : Set.Icc (0 : ℝ) b := ⟨s.1, s.1.property.1, s.2.2⟩
    change genMin (restrict (E := ℝ) hbT f) (window b a b) ≤ genVal f u
    rw [genVal_restrict_gen hbT f v]
    exact ciInf_le (bddBelow_genVal (restrict (E := ℝ) hbT f) _) ⟨v, s.2⟩

private theorem leftLim_shiftIncrement_gen {T c : ℝ} (hc : 0 ≤ c) (hcT : c ≤ T)
    (f : D T ℝ) (hf : ContinuousAt f (⟨c, hc, hcT⟩ : Set.Icc (0 : ℝ) T))
    (s : Set.Icc (0 : ℝ) (T - c)) :
    Function.leftLim (shiftIncrement hc hcT f) s =
      Function.leftLim f ⟨c + s, add_nonneg hc s.property.1, by linarith [s.property.2]⟩ -
        f ⟨c, hc, hcT⟩ := by
  let cT : Set.Icc (0 : ℝ) T := ⟨c, hc, hcT⟩
  let inc : Set.Icc (0 : ℝ) (T - c) → Set.Icc (0 : ℝ) T := fun t =>
    ⟨c + t, add_nonneg hc t.property.1, by linarith [t.property.2]⟩
  by_cases hs0 : (s : ℝ) = 0
  · have hsbot : IsBot s := by
      intro t
      change (s : ℝ) ≤ (t : ℝ)
      simpa [hs0] using t.property.1
    have hleft : Function.leftLim f cT = f cT :=
      hf.continuousWithinAt.leftLim_eq
    have hinc : inc s = cT := by
      apply Subtype.ext
      simp [inc, cT, hs0]
    have htime : (⟨c + s, add_nonneg hc s.property.1, by linarith [s.property.2]⟩ :
        Set.Icc (0 : ℝ) T) = cT := hinc
    rw [leftLim_eq_of_isBot hsbot, htime, hleft]
    simp [shiftIncrement, hs0, cT]
  · have hsne : ∃ r : Set.Icc (0 : ℝ) (T - c), r < s := by
      refine ⟨⟨0, le_rfl, sub_nonneg.mpr hcT⟩, ?_⟩
      change (0 : ℝ) < (s : ℝ)
      exact lt_of_le_of_ne s.property.1 (Ne.symm hs0)
    let _ : (nhdsWithin s (Set.Iio s)).NeBot := nhdsLT_neBot_of_exists_lt hsne
    apply leftLim_eq_of_tendsto
    have hinc : Continuous inc :=
      Continuous.subtype_mk (continuous_const.add continuous_subtype_val) _
    have hmap : Filter.Tendsto inc (nhdsWithin s (Set.Iio s))
        (nhdsWithin (inc s) (Set.Iio (inc s))) := by
      apply tendsto_nhdsWithin_iff.mpr
      refine ⟨tendsto_nhdsWithin_of_tendsto_nhds hinc.continuousAt, ?_⟩
      filter_upwards [self_mem_nhdsWithin] with t ht
      change c + (t : ℝ) < c + (s : ℝ)
      exact add_lt_add_right ht c
    exact (((isCadlag f).tendsto_nhdsLT_leftLim (inc s)).comp hmap).sub tendsto_const_nhds

private theorem genVal_shiftIncrement_gen {T c : ℝ} (hc : 0 ≤ c) (hcT : c ≤ T)
    (f : D T ℝ) (hf : ContinuousAt f (⟨c, hc, hcT⟩ : Set.Icc (0 : ℝ) T))
    (s : Set.Icc (0 : ℝ) (T - c)) :
    genVal f ⟨c + s, add_nonneg hc s.property.1, by linarith [s.property.2]⟩ =
      f ⟨c, hc, hcT⟩ + genVal (shiftIncrement hc hcT f) s := by
  unfold genVal
  rw [leftLim_shiftIncrement_gen hc hcT f hf s]
  simp only [shiftIncrement, coe_mk]
  rw [min_sub_sub_right]
  ring

/-- On `{ContinuousAt f c}` the window minimum on `[c,d]` is `f c` plus the window
minimum of the shifted increment path on `[0, d-c]`. -/
theorem genMin_window_eq_of_continuousAt {T : ℝ} {c d : ℝ} (hc : 0 ≤ c) (hcd : c ≤ d)
    (hdT : d ≤ T) (f : D T ℝ) (hcT : c ≤ T)
    (hf : ContinuousAt f (⟨c, hc, hcT⟩ : Set.Icc (0 : ℝ) T)) :
    genMin f (window T c d) =
      f ⟨c, hc, hcT⟩ + genMin (shiftIncrement hc hcT f) (window (T - c) 0 (d - c)) := by
  let _ : Nonempty (window T c d) := ⟨⟨⟨c, hc, hcT⟩, le_rfl, hcd⟩⟩
  let _ : Nonempty (window (T - c) 0 (d - c)) :=
    ⟨⟨⟨0, le_rfl, sub_nonneg.mpr (hcd.trans hdT)⟩, le_rfl, sub_nonneg.mpr hcd⟩⟩
  let fwd : window T c d → window (T - c) 0 (d - c) := fun s =>
    ⟨⟨(s : ℝ) - c, sub_nonneg.mpr s.property.1, by linarith [s.property.2]⟩,
      sub_nonneg.mpr s.property.1, by linarith [s.property.2]⟩
  let bwd : window (T - c) 0 (d - c) → window T c d := fun s =>
    ⟨⟨c + s, add_nonneg hc s.1.property.1, by linarith [s.1.property.2]⟩,
      le_add_of_nonneg_right s.1.property.1, by linarith [s.2.2]⟩
  have hval (s : window (T - c) 0 (d - c)) :
      genVal f (bwd s) = f ⟨c, hc, hcT⟩ + genVal (shiftIncrement hc hcT f) s := by
    simpa [bwd] using genVal_shiftIncrement_gen hc hcT f hf s
  apply le_antisymm
  · have hle : genMin f (window T c d) - f ⟨c, hc, hcT⟩ ≤
        genMin (shiftIncrement hc hcT f) (window (T - c) 0 (d - c)) := by
      apply le_ciInf
      intro s
      have hs := ciInf_le (bddBelow_genVal f _) (bwd s)
      have hv := hval s
      change (⨅ t : window T c d, genVal f t) - f ⟨c, hc, hcT⟩ ≤
        genVal (shiftIncrement hc hcT f) s
      change (⨅ t : window T c d, genVal f t) ≤ genVal f (bwd s) at hs
      linarith
    linarith
  · apply le_ciInf
    intro s
    have hs : bwd (fwd s) = s := by
      apply Subtype.ext
      apply Subtype.ext
      dsimp [bwd, fwd]
      ring
    rw [← hs, hval]
    have hmin := ciInf_le (bddBelow_genVal (shiftIncrement hc hcT f) _) (fwd s)
    change f ⟨c, hc, hcT⟩ + (⨅ t : window (T - c) 0 (d - c),
      genVal (shiftIncrement hc hcT f) t) ≤
        f ⟨c, hc, hcT⟩ + genVal (shiftIncrement hc hcT f) (fwd s)
    exact add_le_add_right hmin _

private theorem indepFun_middle_of_indep_pair {Ω ρ σ ζ : Type*}
    [MeasurableSpace Ω] [MeasurableSpace ρ] [MeasurableSpace σ] [MeasurableSpace ζ]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {R : Ω → ρ} {S : Ω → σ} {Z : Ω → ζ}
    (hR : Measurable R) (hS : Measurable S) (hZ : Measurable Z)
    (h₁ : IndepFun R (fun ω => (Z ω, S ω)) μ)
    (h₂ : IndepFun (fun ω => (R ω, Z ω)) S μ) :
    IndepFun Z (fun ω => (R ω, S ω)) μ := by
  have hRS : IndepFun R S μ := h₁.comp measurable_id measurable_snd
  have hZS : IndepFun Z S μ := h₂.comp measurable_snd measurable_id
  rw [indepFun_iff_measure_inter_preimage_eq_mul]
  intro U V hU hV
  have hE : MeasurableSet (Z ⁻¹' U) := hZ hU
  induction V, hV using MeasurableSpace.induction_on_inter generateFrom_prod.symm
    isPiSystem_prod with
  | empty => simp
  | basic V hV =>
      obtain ⟨A, hA, B, hB, rfl⟩ := hV
      simp only [mk_preimage_prod]
      calc
        μ (Z ⁻¹' U ∩ (R ⁻¹' A ∩ S ⁻¹' B)) =
            μ (R ⁻¹' A ∩ (Z ⁻¹' U ∩ S ⁻¹' B)) := by
              congr 1
              ext ω
              aesop
        _ = μ (R ⁻¹' A) * μ (Z ⁻¹' U ∩ S ⁻¹' B) :=
          h₁.measure_inter_preimage_eq_mul A (U ×ˢ B) hA (hU.prod hB)
        _ = μ (R ⁻¹' A) * (μ (Z ⁻¹' U) * μ (S ⁻¹' B)) := by
          rw [hZS.measure_inter_preimage_eq_mul U B hU hB]
        _ = μ (Z ⁻¹' U) * (μ (R ⁻¹' A) * μ (S ⁻¹' B)) := by
          ac_rfl
        _ = μ (Z ⁻¹' U) * μ (R ⁻¹' A ∩ S ⁻¹' B) := by
          rw [hRS.measure_inter_preimage_eq_mul A B hA hB]
  | compl V hV ih =>
      have hW : MeasurableSet ((fun ω => (R ω, S ω)) ⁻¹' V) := (hR.prodMk hS) hV
      simp only [preimage_compl]
      rw [← Set.sdiff_eq, ← Set.sdiff_self_inter,
        measure_sdiff inter_subset_left (hE.inter hW).nullMeasurableSet (measure_ne_top _ _),
        ih, measure_compl hW (measure_ne_top _ _), measure_univ, ENNReal.mul_sub, mul_one]
      exact fun _ _ => measure_ne_top _ _
  | iUnion V hdisj hV ih =>
      have hW (i : ℕ) : MeasurableSet ((fun ω => (R ω, S ω)) ⁻¹' V i) :=
        (hR.prodMk hS) (hV i)
      have hd : ∀ i j, i ≠ j → Disjoint ((fun ω => (R ω, S ω)) ⁻¹' V i)
          ((fun ω => (R ω, S ω)) ⁻¹' V j) := fun _ _ h => (hdisj h).preimage _
      have hd' : ∀ i j, i ≠ j → Disjoint (Z ⁻¹' U ∩ (fun ω => (R ω, S ω)) ⁻¹' V i)
          (Z ⁻¹' U ∩ (fun ω => (R ω, S ω)) ⁻¹' V j) := fun i j h =>
        ((hd i j h).inter_left' _).inter_right' _
      simp only [preimage_iUnion, inter_iUnion]
      rw [measure_iUnion hd' (fun i => hE.inter (hW i)),
        measure_iUnion hd hW, ← ENNReal.tsum_mul_left]
      congr 1
      funext i
      exact ih i

private noncomputable def horizonCast {u v : ℝ} (h : u = v) (g : D u ℝ) : D v ℝ := h ▸ g

private theorem measurable_horizonCast {u v : ℝ} (h : u = v) :
    Measurable (horizonCast h) := by
  subst v
  exact measurable_id

private theorem horizonCast_apply {u v : ℝ} (h : u = v) (g : D u ℝ)
    (t : Set.Icc (0 : ℝ) v) :
    horizonCast h g t = g ⟨t, t.property.1, by rw [h]; exact t.property.2⟩ := by
  subst v
  rfl

private noncomputable def shiftIncrementAfter {T b c : ℝ} (hbc : b < c) (hcT : c ≤ T)
    (g : D (T - b) ℝ) : D (T - c) ℝ :=
  horizonCast (show T - b - (c - b) = T - c by ring)
    (shiftIncrement (sub_nonneg.mpr hbc.le) (by linarith : c - b ≤ T - b) g)

private theorem measurable_shiftIncrementAfter {T b c : ℝ} (hbc : b < c) (hcT : c ≤ T) :
    Measurable (shiftIncrementAfter (T := T) hbc hcT) := by
  exact (measurable_horizonCast (show T - b - (c - b) = T - c by ring)).comp
    (measurable_shiftIncrement _ _)

private theorem shiftIncrementAfter_comp {T b c : ℝ} (hb : 0 ≤ b) (hbc : b < c)
    (hcT : c ≤ T) (f : D T ℝ) :
    shiftIncrementAfter hbc hcT (shiftIncrement hb (hbc.le.trans hcT) f) =
      shiftIncrement (hb.trans hbc.le) hcT f := by
  ext t
  rw [shiftIncrementAfter, horizonCast_apply]
  simp only [shiftIncrement, coe_mk]
  have htime : (⟨b + (c - b + (t : ℝ)),
        add_nonneg hb (add_nonneg (sub_nonneg.mpr hbc.le) t.property.1),
        by linarith [t.property.2]⟩ : Set.Icc (0 : ℝ) T) =
      ⟨c + (t : ℝ), add_nonneg (hb.trans hbc.le) t.property.1, by linarith [t.property.2]⟩ := by
    apply Subtype.ext
    ring
  rw [htime]
  simp

/-- Increments of a stable Lévy law have no atoms. -/
theorem IsStableLevyLaw.measure_increment_eq {θ T : ℝ} {P : ProbabilityMeasure (D T ℝ)}
    (hθ : 1 < θ ∧ θ ≤ 2) (hP : IsStableLevyLaw θ T P) {s u : ℝ} (hs : 0 ≤ s) (hsu : s < u)
    (huT : u ≤ T) (x : ℝ) :
    (P : Measure (D T ℝ))
        ({f : D T ℝ | f ⟨u, hs.trans hsu.le, huT⟩ - f ⟨s, hs, hsu.le.trans huT⟩ = x} :
          Set (D T ℝ)) = 0 := by
  let r : Set.Icc (0 : ℝ) T := ⟨s, hs, hsu.le.trans huT⟩
  let t : Set.Icc (0 : ℝ) T := ⟨u, hs.trans hsu.le, huT⟩
  let X : D T ℝ → ℝ := fun f => f t - f r
  have hX : Measurable X := (measurable_eval _).sub (measurable_eval _)
  have hmap : Measure.map X (P : Measure (D T ℝ)) =
      (stableLawAt θ ((t : ℝ) - r) : Measure ℝ) := hP.map_sub_eval r t hsu
  calc
    (P : Measure (D T ℝ)) {f | f ⟨u, hs.trans hsu.le, huT⟩ -
        f ⟨s, hs, hsu.le.trans huT⟩ = x} = Measure.map X (P : Measure (D T ℝ)) {x} := by
      rw [Measure.map_apply hX (measurableSet_singleton x)]
      rfl
    _ = (stableLawAt θ ((t : ℝ) - r) : Measure ℝ) {x} := by rw [hmap]
    _ = 0 := stableLawAt_singleton hθ (sub_pos.mpr hsu) x

/-- Three-way independence: for `0 ≤ b < c ≤ T`, the increment `f c - f b` is independent of the
pair (past restricted to `[0,b]`, increment path after `c`), for the product σ-algebra. -/
theorem IsStableLevyLaw.indepFun_increment_restrict_shiftIncrement {θ T : ℝ}
    {P : ProbabilityMeasure (D T ℝ)} (hP : IsStableLevyLaw θ T P) {b c : ℝ}
    (hb : 0 ≤ b) (hbc : b < c) (hcT : c ≤ T) :
    IndepFun
      (fun f : D T ℝ =>
        f ⟨c, hb.trans hbc.le, hcT⟩ - f ⟨b, hb, hbc.le.trans hcT⟩)
      (fun f : D T ℝ =>
        (restrict (E := ℝ) (hbc.le.trans hcT) f,
          shiftIncrement (hb.trans hbc.le) hcT f))
      (P : Measure (D T ℝ)) := by
  let hbT : b ≤ T := hbc.le.trans hcT
  let hc : 0 ≤ c := hb.trans hbc.le
  let R : D T ℝ → D b ℝ := restrict hbT
  let S : D T ℝ → D (T - c) ℝ := shiftIncrement hc hcT
  let Z : D T ℝ → ℝ := fun f => f ⟨c, hc, hcT⟩ - f ⟨b, hb, hbT⟩
  let evalZ : D (T - b) ℝ → ℝ := fun g =>
    g ⟨c - b, sub_nonneg.mpr hbc.le, by linarith⟩
  have hZcomp : (fun f => Z f) = evalZ ∘ shiftIncrement hb hbT := by
    funext f
    simp only [Function.comp_apply, evalZ, shiftIncrement, coe_mk, Z]
    have ht : (⟨b + (c - b), by positivity, by linarith⟩ : Set.Icc (0 : ℝ) T) =
        ⟨c, hc, hcT⟩ := by
      apply Subtype.ext
      ring
    rw [ht]
  have hScomp : (fun f => S f) =
      (shiftIncrementAfter hbc hcT) ∘ shiftIncrement hb hbT := by
    funext f
    exact (shiftIncrementAfter_comp hb hbc hcT f).symm
  have hpair : Measurable (fun g : D (T - b) ℝ =>
      (evalZ g, shiftIncrementAfter hbc hcT g)) :=
    (measurable_eval _).prodMk (measurable_shiftIncrementAfter hbc hcT)
  have h₁ : IndepFun R (fun f => (Z f, S f)) (P : Measure (D T ℝ)) := by
    have hcomp : (fun f => (Z f, S f)) =
        (fun g : D (T - b) ℝ => (evalZ g, shiftIncrementAfter hbc hcT g)) ∘
          shiftIncrement hb hbT := by
      funext f
      exact Prod.ext (congrFun hZcomp f) (congrFun hScomp f)
    rw [hcomp]
    exact (hP.indepFun_restrict_shiftIncrement hb hbT).comp measurable_id hpair
  let pastPair : D c ℝ → D b ℝ × ℝ := fun g =>
    (restrict hbc.le g, g ⟨c, hc, le_rfl⟩ - g ⟨b, hb, hbc.le⟩)
  have hpastPair : Measurable pastPair := by
    exact (measurable_restrict _).prodMk ((measurable_eval _).sub (measurable_eval _))
  have h₂ : IndepFun (fun f => (R f, Z f)) S (P : Measure (D T ℝ)) := by
    have hcomp : (fun f => (R f, Z f)) = pastPair ∘ restrict hcT := by
      funext f
      apply Prod.ext
      · apply BGW.Skorokhod.ext
        intro t
        rfl
      · rfl
    rw [hcomp]
    exact (hP.indepFun_restrict_shiftIncrement hc hcT).comp hpastPair measurable_id
  change IndepFun Z (fun f => (R f, S f)) (P : Measure (D T ℝ))
  exact indepFun_middle_of_indep_pair (measurable_restrict hbT)
    (measurable_shiftIncrement hc hcT) ((measurable_eval _).sub (measurable_eval _)) h₁ h₂

/-- Key lemma: for separated windows `[a,b]`, `[c,d]` (`0 ≤ a ≤ b < c ≤ d ≤ T`), the generalized
minima over them coincide with probability zero. Proof: write them as `A` and `X_b + Z + M`
with `Z = X_c - X_b` atom-free and independent of `(past through b, increment path after c)`
(`IsStableLevyLaw.indepFun_restrict_shiftIncrement` at `b`, `c`, the three-way independence
lemma `IsStableLevyLaw.indepFun_increment_restrict_shiftIncrement`, and the two measurability
adapters `genMin_window_eq_restrict`, `genMin_window_eq_of_continuousAt`; `ae_continuousAt` at
`c`). -/
theorem IsStableLevyLaw.measure_genMin_window_eq_zero {θ T : ℝ} {P : ProbabilityMeasure (D T ℝ)}
    (hθ : 1 < θ ∧ θ ≤ 2) (hT : 0 < T) (hP : IsStableLevyLaw θ T P)
    {a b c d : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hbc : b < c) (hcd : c ≤ d) (hdT : d ≤ T) :
    (P : Measure (D T ℝ))
        ({f : D T ℝ | genMin f (window T a b) = genMin f (window T c d)} :
          Set (D T ℝ)) = 0 := by
  let hb : 0 ≤ b := ha.trans hab
  let hc : 0 ≤ c := hb.trans hbc.le
  let hbT : b ≤ T := hbc.le.trans (hcd.trans hdT)
  let hcT : c ≤ T := hcd.trans hdT
  let bT : Set.Icc (0 : ℝ) T := ⟨b, hb, hbT⟩
  let cT : Set.Icc (0 : ℝ) T := ⟨c, hc, hcT⟩
  let R : D T ℝ → D b ℝ := restrict hbT
  let S : D T ℝ → D (T - c) ℝ := shiftIncrement hc hcT
  let Z : D T ℝ → ℝ := fun f => f cT - f bT
  let pair : D T ℝ → D b ℝ × D (T - c) ℝ := fun f => (R f, S f)
  let H : D b ℝ × D (T - c) ℝ → ℝ := fun q =>
    genMin q.1 (window b a b) - q.1 ⟨b, hb, le_rfl⟩ -
      genMin q.2 (window (T - c) 0 (d - c))
  let joint : D T ℝ → ℝ × (D b ℝ × D (T - c) ℝ) := fun f => (Z f, pair f)
  let E : Set (ℝ × (D b ℝ × D (T - c) ℝ)) := {q | q.1 = H q.2}
  have hZ : Measurable Z := (measurable_eval _).sub (measurable_eval _)
  have hPair : Measurable pair := (measurable_restrict hbT).prodMk
    (measurable_shiftIncrement hc hcT)
  have hJoint : Measurable joint := hZ.prodMk hPair
  have hH : Measurable H := by
    exact (((measurable_genMinOn a b).comp measurable_fst).sub
      ((measurable_eval _).comp measurable_fst)).sub
        ((measurable_genMinOn 0 (d - c)).comp measurable_snd)
  have hE : MeasurableSet E := measurableSet_eq_fun measurable_fst (hH.comp measurable_snd)
  have hind : IndepFun Z pair (P : Measure (D T ℝ)) :=
    hP.indepFun_increment_restrict_shiftIncrement hb hbc hcT
  have hmapZ : Measure.map Z (P : Measure (D T ℝ)) =
      (stableLawAt θ (c - b) : Measure ℝ) := hP.map_sub_eval bT cT hbc
  have hgraph : (P : Measure (D T ℝ)) (joint ⁻¹' E) = 0 := by
    calc
      (P : Measure (D T ℝ)) (joint ⁻¹' E) =
          Measure.map joint (P : Measure (D T ℝ)) E :=
        (Measure.map_apply hJoint hE).symm
      _ = (Measure.map Z (P : Measure (D T ℝ))).prod
          (Measure.map pair (P : Measure (D T ℝ))) E := by
        rw [hind.map_prod_eq_prod_map_map hZ.aemeasurable hPair.aemeasurable]
      _ = ∫⁻ q, Measure.map Z (P : Measure (D T ℝ))
          ((fun z => (z, q)) ⁻¹' E) ∂Measure.map pair (P : Measure (D T ℝ)) :=
        Measure.prod_apply_symm hE
      _ = 0 := by
        have hsec (q : D b ℝ × D (T - c) ℝ) :
            (fun z => (z, q)) ⁻¹' E = {H q} := by
          ext z
          rfl
        simp_rw [hsec]
        rw [hmapZ]
        simp [stableLawAt_singleton hθ (sub_pos.mpr hbc)]
  have hcont : (P : Measure (D T ℝ)) {f | ¬ ContinuousAt f cT} = 0 := by
    rw [← ae_iff]
    exact hP.ae_continuousAt hθ hT cT
  apply measure_mono_null (show {f : D T ℝ |
    genMin f (window T a b) = genMin f (window T c d)} ⊆
      joint ⁻¹' E ∪ {f | ¬ ContinuousAt f cT} from ?_)
    (measure_union_null hgraph hcont)
  intro f hf
  by_cases hfc : ContinuousAt f cT
  · apply Or.inl
    have hleft := genMin_window_eq_restrict ha hab hbT f
    have hright := genMin_window_eq_of_continuousAt hc hcd hdT f hcT hfc
    change Z f = H (pair f)
    dsimp [Z, H, pair]
    rw [← hleft]
    have hM : genMin (shiftIncrement hc hcT f) (window (T - c) 0 (d - c)) =
        genMin f (window T c d) - f cT := by
      change genMin (shiftIncrement hc hcT f) (window (T - c) 0 (d - c)) =
        genMin f (window T c d) - f ⟨c, hc, hcT⟩
      linarith
    rw [hM]
    change f cT - f bT = genMin f (window T a b) - f bT -
      (genMin f (window T c d) - f cT)
    dsimp [bT, cT] at hf ⊢
    linarith
  · exact Or.inr hfc

/-- Main theorem: almost surely there is exactly one generalized minimizer. -/
theorem IsStableLevyLaw.ae_existsUnique_generalizedMinimizer {θ T : ℝ}
    {P : ProbabilityMeasure (D T ℝ)} (hθ : 1 < θ ∧ θ ≤ 2) (hT : 0 < T)
    (hP : IsStableLevyLaw θ T P) :
    ∀ᵐ f : D T ℝ ∂(P : Measure (D T ℝ)),
      ∃! g : Set.Icc (0 : ℝ) T, min (Function.leftLim f g) (f g) = ⨅ t, f t := by
  let Q := {q : ℚ × ℚ // 0 ≤ (q.1 : ℝ) ∧ (q.1 : ℝ) < q.2 ∧ (q.2 : ℝ) ≤ T}
  have hne (q : Q) : ∀ᵐ f : D T ℝ ∂(P : Measure (D T ℝ)),
      genMin f (window T 0 q.1.1) ≠ genMin f (window T q.1.2 T) := by
    rw [ae_iff]
    simpa only [Classical.not_not] using hP.measure_genMin_window_eq_zero hθ hT
      (a := 0) (b := q.1.1) (c := q.1.2) (d := T) le_rfl q.property.1 q.property.2.1
        q.property.2.2 le_rfl
  have hsep : ∀ᵐ f : D T ℝ ∂(P : Measure (D T ℝ)), ∀ q : Q,
      genMin f (window T 0 q.1.1) ≠ genMin f (window T q.1.2 T) := ae_all_iff.mpr hne
  change ∀ᵐ f : D T ℝ ∂(P : Measure (D T ℝ)), ∃! g, IsGenMinimizer f g
  filter_upwards [hsep] with f hf
  obtain ⟨g, hg⟩ := exists_isGenMinimizer hT.le f
  refine ⟨g, hg, ?_⟩
  intro y hy
  by_contra hgy
  obtain ⟨b, c, hb, hbc, hc, heq⟩ := exists_rat_separation hy hg hgy
  exact hf ⟨(b, c), hb, hbc, hc⟩ heq

/-- The same for the canonical stable process law. -/
theorem stableProcessLaw_ae_existsUnique_generalizedMinimizer {θ T : ℝ}
    (hθ : 1 < θ ∧ θ ≤ 2) (hT : 0 < T) :
    ∀ᵐ f : D T ℝ ∂(stableProcessLaw θ T : Measure (D T ℝ)),
      ∃! g : Set.Icc (0 : ℝ) T, min (Function.leftLim f g) (f g) = ⨅ t, f t :=
  (isStableLevyLaw_stableProcessLaw hθ hT).ae_existsUnique_generalizedMinimizer hθ hT

/-- Transfer to any measure absolutely continuous w.r.t. a stable Lévy law. -/
theorem ae_existsUnique_generalizedMinimizer_of_absolutelyContinuous {θ T : ℝ}
    {P : ProbabilityMeasure (D T ℝ)} (hθ : 1 < θ ∧ θ ≤ 2) (hT : 0 < T)
    (hP : IsStableLevyLaw θ T P) {μ : Measure (D T ℝ)} (hμ : μ ≪ (P : Measure (D T ℝ))) :
    ∀ᵐ f : D T ℝ ∂μ, ∃! g : Set.Icc (0 : ℝ) T, IsGenMinimizer f g :=
  hμ.ae_le (hP.ae_existsUnique_generalizedMinimizer hθ hT)

private theorem genMin_le_genVal_of_mem {T : ℝ} (f : D T ℝ)
    {J : Set (Set.Icc (0 : ℝ) T)} {g : Set.Icc (0 : ℝ) T} (hg : g ∈ J) :
    genMin f J ≤ genVal f g := by
  let _ : Nonempty J := ⟨⟨g, hg⟩⟩
  exact ciInf_le (bddBelow_genVal f J) ⟨g, hg⟩

private theorem genMin_eq_of_window_minimizer {T : ℝ} (f : D T ℝ)
    {J K : Set (Set.Icc (0 : ℝ) T)} {g : Set.Icc (0 : ℝ) T}
    (hgJ : g ∈ J) (hJK : J ⊆ K) (hg : genVal f g = genMin f K) :
    genMin f J = genMin f K := by
  let _ : Nonempty J := ⟨⟨g, hgJ⟩⟩
  let _ : Nonempty K := ⟨⟨g, hJK hgJ⟩⟩
  apply le_antisymm
  · rw [← hg]
    exact genMin_le_genVal_of_mem f hgJ
  · apply le_ciInf
    intro t
    exact genMin_le_genVal_of_mem f (hJK t.property)

private theorem exists_window_minimizer {T b : ℝ} (hb : 0 ≤ b) (hbT : b ≤ T)
    (f : D T ℝ) :
    ∃ g : Set.Icc (0 : ℝ) T, (g : ℝ) ≤ b ∧ genVal f g = genMin f (window T 0 b) := by
  obtain ⟨g, hg⟩ := exists_isGenMinimizer hb (restrict (E := ℝ) hbT f)
  let gT : Set.Icc (0 : ℝ) T := ⟨g, g.property.1, g.property.2.trans hbT⟩
  refine ⟨gT, g.property.2, ?_⟩
  have hgJ : g ∈ window b 0 b := ⟨g.property.1, g.property.2⟩
  calc
    genVal f gT = genVal (restrict (E := ℝ) hbT f) g := genVal_restrict_gen hbT f g
    _ = ⨅ t, restrict (E := ℝ) hbT f t := hg
    _ = genMin (restrict (E := ℝ) hbT f) (window b 0 b) :=
      (genMin_eq_iInf_of_mem (restrict (E := ℝ) hbT f) hg hgJ).symm
    _ = genMin f (window T 0 b) := (genMin_window_eq_restrict le_rfl hb hbT f).symm

private theorem exists_rat_window_separation_of_lt {T b : ℝ} {f : D T ℝ}
    {g₁ g₂ : Set.Icc (0 : ℝ) T} (h₁₂ : g₁ < g₂)
    (h₁ : (g₁ : ℝ) ≤ b ∧ genVal f g₁ = genMin f (window T 0 b))
    (h₂ : (g₂ : ℝ) ≤ b ∧ genVal f g₂ = genMin f (window T 0 b)) :
    ∃ q r : ℚ, 0 ≤ (q : ℝ) ∧ (q : ℝ) < r ∧ (r : ℝ) ≤ b ∧
      genMin f (window T 0 q) = genMin f (window T r b) := by
  have h₁₂R : (g₁ : ℝ) < g₂ := h₁₂
  obtain ⟨q, hg₁q, hqg₂⟩ := exists_rat_btwn h₁₂R
  obtain ⟨r, hqr, hrg₂⟩ := exists_rat_btwn hqg₂
  have hq : 0 ≤ (q : ℝ) := g₁.property.1.trans hg₁q.le
  have hqbg : (q : ℝ) ≤ b := hqg₂.le.trans h₂.1
  have hr : (r : ℝ) ≤ b := hrg₂.le.trans h₂.1
  have hg₁J : g₁ ∈ window T 0 q := ⟨g₁.property.1, hg₁q.le⟩
  have hg₂J : g₂ ∈ window T r b := ⟨hrg₂.le, h₂.1⟩
  have hleft : genMin f (window T 0 q) = genMin f (window T 0 b) :=
    genMin_eq_of_window_minimizer f hg₁J (fun _ hs => ⟨hs.1, hs.2.trans hqbg⟩) h₁.2
  have hright : genMin f (window T r b) = genMin f (window T 0 b) :=
    genMin_eq_of_window_minimizer f hg₂J (fun _ hs => ⟨hq.trans (hqr.le.trans hs.1), hs.2⟩) h₂.2
  exact ⟨q, r, hq, hqr, hr, hleft.trans hright.symm⟩

private theorem exists_rat_window_separation {T b : ℝ} {f : D T ℝ}
    {g₁ g₂ : Set.Icc (0 : ℝ) T}
    (h₁ : (g₁ : ℝ) ≤ b ∧ genVal f g₁ = genMin f (window T 0 b))
    (h₂ : (g₂ : ℝ) ≤ b ∧ genVal f g₂ = genMin f (window T 0 b)) (hne : g₁ ≠ g₂) :
    ∃ q r : ℚ, 0 ≤ (q : ℝ) ∧ (q : ℝ) < r ∧ (r : ℝ) ≤ b ∧
      genMin f (window T 0 q) = genMin f (window T r b) := by
  rcases lt_or_gt_of_ne hne with h₁₂ | h₂₁
  · exact exists_rat_window_separation_of_lt h₁₂ h₁ h₂
  · obtain ⟨q, r, hq, hqr, hr, heq⟩ := exists_rat_window_separation_of_lt h₂₁ h₂ h₁
    exact ⟨q, r, hq, hqr, hr, heq⟩

/-- Window-relative uniqueness: a.s. there is a unique time `g ≤ b` whose generalized value
is the generalized minimum over `[0,b]`. -/
theorem IsStableLevyLaw.ae_existsUnique_windowMinimizer {θ T : ℝ}
    {P : ProbabilityMeasure (D T ℝ)} (hθ : 1 < θ ∧ θ ≤ 2) (hT : 0 < T)
    (hP : IsStableLevyLaw θ T P) {b : ℝ} (hb : 0 < b) (hbT : b ≤ T) :
    ∀ᵐ f : D T ℝ ∂(P : Measure (D T ℝ)),
      ∃! g : Set.Icc (0 : ℝ) T, (g : ℝ) ≤ b ∧ genVal f g = genMin f (window T 0 b) := by
  let Q := {q : ℚ × ℚ // 0 ≤ (q.1 : ℝ) ∧ (q.1 : ℝ) < q.2 ∧ (q.2 : ℝ) ≤ b}
  have hne (q : Q) : ∀ᵐ f : D T ℝ ∂(P : Measure (D T ℝ)),
      genMin f (window T 0 q.1.1) ≠ genMin f (window T q.1.2 b) := by
    rw [ae_iff]
    simpa only [Classical.not_not] using hP.measure_genMin_window_eq_zero hθ hT
      (a := 0) (b := q.1.1) (c := q.1.2) (d := b) le_rfl q.property.1 q.property.2.1
        q.property.2.2 hbT
  have hsep : ∀ᵐ f : D T ℝ ∂(P : Measure (D T ℝ)), ∀ q : Q,
      genMin f (window T 0 q.1.1) ≠ genMin f (window T q.1.2 b) := ae_all_iff.mpr hne
  filter_upwards [hsep] with f hf
  obtain ⟨g, hg⟩ := exists_window_minimizer hb.le hbT f
  refine ⟨g, hg, ?_⟩
  intro y hy
  by_contra hgy
  obtain ⟨q, r, hq, hqr, hr, heq⟩ := exists_rat_window_separation hy hg hgy
  exact hf ⟨(q, r), hq, hqr, hr⟩ heq

/-- Transfer of window-relative uniqueness to measures absolutely continuous with respect to a
stable Lévy law. -/
theorem ae_existsUnique_windowMinimizer_of_absolutelyContinuous {θ T : ℝ}
    {P : ProbabilityMeasure (D T ℝ)} (hθ : 1 < θ ∧ θ ≤ 2) (hT : 0 < T)
    (hP : IsStableLevyLaw θ T P) {b : ℝ} (hb : 0 < b) (hbT : b ≤ T)
    {μ : Measure (D T ℝ)} (hμ : μ ≪ (P : Measure (D T ℝ))) :
    ∀ᵐ f : D T ℝ ∂μ,
      ∃! g : Set.Icc (0 : ℝ) T, (g : ℝ) ≤ b ∧ genVal f g = genMin f (window T 0 b) :=
  hμ.ae_le (hP.ae_existsUnique_windowMinimizer hθ hT hb hbT)

end BGW.StableTrees
