/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.Skorokhod.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
public import Mathlib.MeasureTheory.Function.Floor
public import Mathlib.Topology.UnitInterval

/-!
# Measurable approximations of càdlàg paths

This module collects path measurability tools for the later Borel and cylinder results.
-/

@[expose] public section

open Set Filter Topology

namespace BGW.Skorokhod

variable {α β γ : Type*}

/-- A measurable map with countable range remains measurable after any function on its range. -/
theorem Measurable.comp_of_countable_range [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass β] [MeasurableSpace γ] {g : α → β} (hg : Measurable g)
    (hgc : (Set.range g).Countable) (f : β → γ) : Measurable (f ∘ g) := by
  let g' : α → Set.range g := fun x => ⟨g x, ⟨x, rfl⟩⟩
  have hg' : Measurable g' := hg.subtype_mk
  let _ : Countable (Set.range g) := hgc
  have hf : Measurable (fun x : Set.range g => f x) := measurable_of_countable _
  exact hf.comp hg'

variable {T : ℝ} {E : Type*}

/-- Right continuity gives a right neighborhood on which a path stays close to its value. -/
theorem exists_right_oscillation [MetricSpace E] (f : D T E)
    (t : Set.Icc (0 : ℝ) T) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ s : Set.Icc (0 : ℝ) T,
      (t : ℝ) ≤ s → (s : ℝ) < (t : ℝ) + δ → dist (f s) (f t) < ε := by
  obtain ⟨δ, hδ, hclose⟩ :=
    Metric.continuousWithinAt_iff.mp ((isCadlag f).isRightContinuous t) ε hε
  refine ⟨δ, hδ, fun s hts hsδ => ?_⟩
  by_cases hst : s = t
  · simpa [hst] using hε
  · have hst' : (s : ℝ) ≠ t := fun h => hst (Subtype.ext h)
    have htlt : (t : ℝ) < s := lt_of_le_of_ne hts (Ne.symm hst')
    apply hclose (Set.mem_Ioi.mpr htlt)
    · have : dist s t < δ := by
        rw [Subtype.dist_eq, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hts)]
        linarith
      exact this

/-- A left limit controls path values in a sufficiently small left neighborhood. -/
theorem exists_left_oscillation [MetricSpace E] (f : D T E)
    (t : Set.Icc (0 : ℝ) T) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ s : Set.Icc (0 : ℝ) T,
      (t : ℝ) - δ < s → (s : ℝ) < t →
        dist (f s) (Function.leftLim f t) < ε := by
  have hlim := (isCadlag f).tendsto_nhdsLT_leftLim t
  have hball : {s | dist (f s) (Function.leftLim f t) < ε} ∈ 𝓝[Set.Iio t] t :=
    hlim.eventually (Metric.ball_mem_nhds _ hε)
  obtain ⟨δ, hδ, hsub⟩ := Metric.mem_nhdsWithin_iff.mp hball
  refine ⟨δ, hδ, fun s hsδ hst => ?_⟩
  apply hsub
  constructor
  · change dist s t < δ
    rw [Subtype.dist_eq, Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr (le_of_lt hst))]
    linarith
  · exact Set.mem_Iio.mpr hst

/-- A neighborhood of a time has small oscillation on each side of that time. -/
theorem exists_local_path_ball [MetricSpace E] (f : D T E)
    (t : Set.Icc (0 : ℝ) T) {ε : ℝ} (hε : 0 < ε) :
    ∃ r > 0, ∀ s : Set.Icc (0 : ℝ) T, dist s t < r →
      ((s : ℝ) < t → dist (f s) (Function.leftLim f t) < ε / 2) ∧
      (t ≤ s → dist (f s) (f t) < ε / 2) := by
  obtain ⟨δl, hδl, hl⟩ := exists_left_oscillation f t (half_pos hε)
  obtain ⟨δr, hδr, hr⟩ := exists_right_oscillation f t (half_pos hε)
  refine ⟨min δl δr, lt_min hδl hδr, fun s hst => ?_⟩
  constructor
  · intro hs
    apply hl s
    · have hdist : (t : ℝ) - (s : ℝ) < min δl δr := by
        have := (abs_lt.mp (by
          rw [← Real.dist_eq, ← Subtype.dist_eq]
          exact hst)).1
        linarith
      linarith [min_le_left δl δr]
    · exact hs
  · intro hs
    apply hr s hs
    have hdist : (s : ℝ) - (t : ℝ) < min δl δr := by
      have := (abs_lt.mp (by
        rw [← Real.dist_eq, ← Subtype.dist_eq]
        exact hst)).2
      linarith
    linarith [min_le_right δl δr]

/-- A half-open partition on which a càdlàg path has arbitrarily small oscillation. -/
theorem exists_small_oscillation_partition [MetricSpace E] (f : D T E)
    (hT : 0 ≤ T) {ε : ℝ} (hε : 0 < ε) :
    ∃ u : ℕ → Set.Icc (0 : ℝ) T,
      u 0 = ⟨0, le_rfl, hT⟩ ∧ Monotone u ∧
      (∃ m, ∀ n ≥ m, (u n : ℝ) = T) ∧
      ∀ n (s v : Set.Icc (0 : ℝ) T),
        (u n : ℝ) ≤ s → s < u (n + 1) →
        (u n : ℝ) ≤ v → v < u (n + 1) → dist (f s) (f v) < ε := by
  classical
  choose rad hrad hlocal using fun t : Set.Icc (0 : ℝ) T =>
    exists_local_path_ball f t hε
  let cover : Set.Icc (0 : ℝ) T → Set (Set.Icc (0 : ℝ) T) :=
    fun t => Metric.ball t (rad t)
  have hopen : ∀ t, IsOpen (cover t) := fun t => Metric.isOpen_ball
  have hcover : (Set.univ : Set (Set.Icc (0 : ℝ) T)) ⊆ ⋃ t, cover t := by
    intro t _
    refine Set.mem_iUnion.mpr ⟨t, ?_⟩
    exact Metric.mem_ball.mpr (by simpa using hrad t)
  obtain ⟨t, ht0, htmono, hteventually, hrefines⟩ :=
    exists_monotone_Icc_subset_open_cover_Icc hT hopen hcover
  obtain ⟨m, htm⟩ := hteventually
  have hbase : ∀ n, ∃ c : Set.Icc (0 : ℝ) T,
      Set.Icc (t n) (t (n + 1)) ⊆ cover c := by
    intro n
    obtain ⟨c, hc⟩ := hrefines n
    exact ⟨c, hc⟩
  choose c hc using hbase
  let mid : ℕ → Set.Icc (0 : ℝ) T :=
    fun n => max (t n) (min (c n) (t (n + 1)))
  have hmid_lower (n : ℕ) : t n ≤ mid n := le_max_left _ _
  have hmid_upper (n : ℕ) : mid n ≤ t (n + 1) :=
    max_le (htmono (Nat.le_succ n)) (min_le_right _ _)
  have hmid_lowerR (n : ℕ) : (t n : ℝ) ≤ mid n :=
    Subtype.coe_le_coe.mp (hmid_lower n)
  have hmid_upperR (n : ℕ) : (mid n : ℝ) ≤ t (n + 1) :=
    Subtype.coe_le_coe.mp (hmid_upper n)
  let u : ℕ → Set.Icc (0 : ℝ) T := fun n =>
    if n % 2 = 0 then t (n / 2) else mid (n / 2)
  have hu_even (n : ℕ) : u (2 * n) = t n := by
    have hmod : (2 * n) % 2 = 0 ∧ (2 * n) / 2 = n := by omega
    simp [u, hmod.1, hmod.2]
  have hu_odd (n : ℕ) : u (2 * n + 1) = mid n := by
    have hmod : (2 * n + 1) % 2 = 1 ∧ (2 * n + 1) / 2 = n := by omega
    simp [u, hmod.1, hmod.2]
  have hsucc : ∀ n, u n ≤ u (n + 1) := by
    intro n
    have hmod : n % 2 = 0 ∨ n % 2 = 1 := by omega
    rcases hmod with he | ho
    · let q := n / 2
      have hn : n = 2 * q := by omega
      rw [hn]
      calc
        u (2 * q) = t q := hu_even q
        _ ≤ mid q := hmid_lower q
        _ = u (2 * q + 1) := (hu_odd q).symm
    · let q := n / 2
      have hn : n = 2 * q + 1 := by omega
      rw [hn]
      calc
        u (2 * q + 1) = mid q := hu_odd q
        _ ≤ t (q + 1) := hmid_upper q
        _ = u (2 * (q + 1)) := (hu_even (q + 1)).symm
  have hmono : Monotone u := monotone_nat_of_le_succ hsucc
  have hu0 : u 0 = ⟨0, le_rfl, hT⟩ := by
    rw [hu_even 0]
    apply Subtype.ext
    simpa using ht0
  have hu_eventually : ∃ k, ∀ n ≥ k, (u n : ℝ) = T := by
    refine ⟨2 * m, fun n hn => ?_⟩
    have hmod : n % 2 = 0 ∨ n % 2 = 1 := by omega
    rcases hmod with he | ho
    · let q := n / 2
      have hnq : n = 2 * q := by omega
      have hqm : q ≥ m := by omega
      rw [hnq, hu_even]
      exact htm q hqm
    · let q := n / 2
      have hnq : n = 2 * q + 1 := by omega
      have hqm : q ≥ m := by omega
      have hq1m : q + 1 ≥ m := by omega
      rw [hnq, hu_odd]
      have hq : (t q : ℝ) = T := htm q hqm
      have hq1 : (t (q + 1) : ℝ) = T := htm (q + 1) hq1m
      have hmidT : (mid q : ℝ) = T := by
        have hlo : (t q : ℝ) ≤ (mid q : ℝ) := by exact_mod_cast hmid_lower q
        have hhi : (mid q : ℝ) ≤ (t (q + 1) : ℝ) := by
          exact_mod_cast hmid_upper q
        linarith
      exact hmidT
  refine ⟨u, hu0, hmono, hu_eventually, ?_⟩
  intro n s v hns hsnv hnv hsvn
  let q := n / 2
  have hmod : n % 2 = 0 ∨ n % 2 = 1 := by omega
  rcases hmod with he | ho
  · have hn : n = 2 * q := by omega
    have hn1 : n + 1 = 2 * q + 1 := by omega
    have hstart : u n = t q := by rw [hn]; exact hu_even q
    have hend : u (n + 1) = mid q := by
      calc
        u (n + 1) = u (2 * q + 1) := congrArg u hn1
        _ = mid q := hu_odd q
    have hns' : (t q : ℝ) ≤ s := by simpa [hstart] using hns
    have hsnv' : (s : ℝ) < mid q := by simpa [hend] using hsnv
    have hnv' : (t q : ℝ) ≤ v := by simpa [hstart] using hnv
    have hsvn' : (v : ℝ) < mid q := by simpa [hend] using hsvn
    have hsball : s ∈ cover (c q) := by
      apply hc q
      exact ⟨Subtype.coe_le_coe.mpr hns', Subtype.coe_le_coe.mpr
        ((le_of_lt hsnv').trans (by exact_mod_cast hmid_upper q))⟩
    have hvball : v ∈ cover (c q) := by
      apply hc q
      exact ⟨Subtype.coe_le_coe.mpr hnv', Subtype.coe_le_coe.mpr
        ((le_of_lt hsvn').trans (by exact_mod_cast hmid_upper q))⟩
    have hside : c q ≤ t q ∨ t q < c q := by
      by_cases hright : t q < c q
      · exact Or.inr hright
      · exact Or.inl (le_of_not_gt hright)
    rcases hside with hleft | hright
    · have hmid : mid q = t q := by
        simp [mid, max_eq_left hleft,
          min_eq_left (le_trans hleft (htmono (Nat.le_succ q)))]
      have hempty : False := by
        have hs' : (s : ℝ) < t q := by simpa [hmid] using hsnv'
        have hs'' : (t q : ℝ) ≤ s := hns'
        exact (not_lt_of_ge hs'') hs'
      exact hempty.elim
    · have hmid : mid q ≤ c q := by
        apply max_le
        · exact_mod_cast hright.le
        · exact min_le_left _ _
      have hsl : (s : ℝ) < c q := lt_of_lt_of_le hsnv' (by exact_mod_cast hmid)
      have hvl : (v : ℝ) < c q := lt_of_lt_of_le hsvn' (by exact_mod_cast hmid)
      have hsclose := (hlocal (c q) s hsball).1 hsl
      have hvclose := (hlocal (c q) v hvball).1 hvl
      calc
        dist (f s) (f v) ≤
            dist (f s) (Function.leftLim f (c q)) +
              dist (Function.leftLim f (c q)) (f v) := dist_triangle _ _ _
        _ < ε / 2 + ε / 2 := by
          exact add_lt_add hsclose (by simpa [dist_comm] using hvclose)
        _ = ε := by ring
  · have hn : n = 2 * q + 1 := by omega
    have hn1 : n + 1 = 2 * (q + 1) := by omega
    have hstart : u n = mid q := by
      calc
        u n = u (2 * q + 1) := congrArg u hn
        _ = mid q := hu_odd q
    have hend : u (n + 1) = t (q + 1) := by
      calc
        u (n + 1) = u (2 * (q + 1)) := congrArg u hn1
        _ = t (q + 1) := hu_even (q + 1)
    have hns' : (mid q : ℝ) ≤ s := by simpa [hstart] using hns
    have hsnv' : (s : ℝ) < t (q + 1) := by simpa [hend] using hsnv
    have hnv' : (mid q : ℝ) ≤ v := by simpa [hstart] using hnv
    have hsvn' : (v : ℝ) < t (q + 1) := by simpa [hend] using hsvn
    have hsball : s ∈ cover (c q) := by
      apply hc q
      have hloR : (t q : ℝ) ≤ s := (hmid_lowerR q).trans hns'
      have hhiR : (s : ℝ) ≤ t (q + 1) := le_of_lt hsnv'
      exact ⟨Subtype.coe_le_coe.mpr hloR, Subtype.coe_le_coe.mpr hhiR⟩
    have hvball : v ∈ cover (c q) := by
      apply hc q
      have hloR : (t q : ℝ) ≤ v := (hmid_lowerR q).trans hnv'
      have hhiR : (v : ℝ) ≤ t (q + 1) := le_of_lt hsvn'
      exact ⟨Subtype.coe_le_coe.mpr hloR, Subtype.coe_le_coe.mpr hhiR⟩
    have hside : t (q + 1) ≤ c q ∨ c q < t (q + 1) := by
      by_cases hright : c q < t (q + 1)
      · exact Or.inr hright
      · exact Or.inl (le_of_not_gt hright)
    rcases hside with hempty | hright
    · have hmid : mid q = t (q + 1) := by
        simp [mid, min_eq_right hempty, max_eq_right (htmono (Nat.le_succ q))]
      have hempty' : False := by
        have hs' : (s : ℝ) < t (q + 1) := by simpa [hmid] using hsnv'
        have hs'' : (t (q + 1) : ℝ) ≤ s := by simpa [hmid] using hns'
        exact (not_lt_of_ge hs'') hs'
      exact hempty'.elim
    · have hmid : c q ≤ mid q := by
        simp [mid, min_eq_left hright.le]
      have hsl : c q ≤ s := le_trans (by exact_mod_cast hmid) hns'
      have hvl : c q ≤ v := le_trans (by exact_mod_cast hmid) hnv'
      have hsclose := (hlocal (c q) s hsball).2 hsl
      have hvclose := (hlocal (c q) v hvball).2 hvl
      calc
        dist (f s) (f v) ≤ dist (f s) (f (c q)) + dist (f (c q)) (f v) :=
          dist_triangle _ _ _
        _ < ε / 2 + ε / 2 := by
          exact add_lt_add hsclose (by simpa [dist_comm] using hvclose)
        _ = ε := by ring

/-- A càdlàg path is uniformly approximated by functions constant on half-open partition blocks. -/
theorem exists_uniform_step_approximation [MetricSpace E] (f : D T E)
    (hT : 0 ≤ T) {ε : ℝ} (hε : 0 < ε) :
    ∃ u : ℕ → Set.Icc (0 : ℝ) T, ∃ g : Set.Icc (0 : ℝ) T → E,
      u 0 = ⟨0, le_rfl, hT⟩ ∧ Monotone u ∧
      (∃ m, ∀ n ≥ m, (u n : ℝ) = T) ∧
      (∀ n (s : Set.Icc (0 : ℝ) T), (u n : ℝ) ≤ s → s < u (n + 1) →
        g s = f (u n)) ∧
      (∀ s, dist (g s) (f s) < ε) := by
  classical
  obtain ⟨u, hu0, hmono, hterm, hpart⟩ :=
    exists_small_oscillation_partition f hT hε
  obtain ⟨m, htm⟩ := hterm
  let P : Set.Icc (0 : ℝ) T → ℕ → Prop := fun s n => (s : ℝ) < u (n + 1)
  have hex (s : Set.Icc (0 : ℝ) T) (hs : (s : ℝ) < T) : ∃ n, P s n := by
    refine ⟨m, ?_⟩
    dsimp [P]
    rw [htm (m + 1) (by omega)]
    exact hs
  let idx : Set.Icc (0 : ℝ) T → ℕ := fun s =>
    if hs : (s : ℝ) < T then Nat.find (hex s hs) else 0
  let g : Set.Icc (0 : ℝ) T → E := fun s =>
    if hs : (s : ℝ) < T then f (u (idx s)) else f s
  have hidx_spec (s : Set.Icc (0 : ℝ) T) (hs : (s : ℝ) < T) : P s (idx s) := by
    simpa [idx, hs] using Nat.find_spec (hex s hs)
  have hidx_min (s : Set.Icc (0 : ℝ) T) (hs : (s : ℝ) < T) :
      ∀ k < idx s, ¬ P s k := by
    intro k hk
    have hk' : k < Nat.find (hex s hs) := by simpa [idx, hs] using hk
    simpa [idx, hs] using Nat.find_min (hex s hs) hk'
  have hidx_lower (s : Set.Icc (0 : ℝ) T) (hs : (s : ℝ) < T) :
      (u (idx s) : ℝ) ≤ s := by
    by_cases hzero : idx s = 0
    · have hfind : Nat.find (hex s hs) = 0 := by simpa [idx, hs] using hzero
      have hu0R : (u 0 : ℝ) = 0 := congrArg Subtype.val hu0
      simpa [idx, hs, hfind, hu0R] using s.2.1
    · have hpos : 1 ≤ idx s := Nat.one_le_iff_ne_zero.mpr hzero
      have hprev : idx s - 1 < idx s := by omega
      have hnot : ¬ (s : ℝ) < u (idx s) := by
        simpa [P, Nat.sub_add_cancel hpos] using hidx_min s hs (idx s - 1) hprev
      exact le_of_not_gt hnot
  have hstep (n : ℕ) (s : Set.Icc (0 : ℝ) T)
      (hslo : (u n : ℝ) ≤ s) (hshi : s < u (n + 1)) : g s = f (u n) := by
    have hsT : (s : ℝ) < T := lt_of_lt_of_le hshi (u (n + 1)).property.2
    have hP : P s n := hshi
    have hidxle : idx s ≤ n := by
      simpa [idx, hsT] using Nat.find_min' (hex s hsT) hP
    have hidxge : n ≤ idx s := by
      by_contra hn
      have hlt : idx s < n := Nat.lt_of_not_ge hn
      have hmono' : (u (idx s + 1) : ℝ) ≤ u n := by
        exact_mod_cast hmono (Nat.succ_le_of_lt hlt)
      have hle : (u (idx s + 1) : ℝ) ≤ s := hmono'.trans hslo
      have hnot : ¬ P s (idx s) := by
        dsimp [P]
        exact not_lt_of_ge hle
      exact hnot (hidx_spec s hsT)
    have hidx : idx s = n := Nat.le_antisymm hidxle hidxge
    simp [g, hsT, hidx]
  have happrox (s : Set.Icc (0 : ℝ) T) : dist (g s) (f s) < ε := by
    by_cases hsT : (s : ℝ) < T
    · have hsmall := hpart (idx s) (u (idx s)) s le_rfl
        (lt_of_le_of_lt (hidx_lower s hsT) (hidx_spec s hsT))
        (hidx_lower s hsT) (hidx_spec s hsT)
      simpa [g, hsT] using hsmall
    · simpa [g, hsT] using hε
  exact ⟨u, g, hu0, hmono, ⟨m, htm⟩, hstep, happrox⟩

/-- A càdlàg path has only finitely many jumps larger than any fixed positive threshold. -/
theorem finite_setOf_jump_gt [MetricSpace E] (f : D T E) {ε : ℝ} (hε : 0 < ε) :
    {t : Set.Icc (0 : ℝ) T | ε < dist (Function.leftLim f t) (f t)}.Finite := by
  classical
  by_cases hT : 0 ≤ T
  · obtain ⟨u, hu0, _, hterm, hpart⟩ :=
      exists_small_oscillation_partition f hT (show 0 < ε / 2 by positivity)
    obtain ⟨m, htm⟩ := hterm
    let K := 2 * m
    let F : Set (Set.Icc (0 : ℝ) T) := u '' Set.Iic K
    have hF : F.Finite := (finite_Iic K).image u
    have hsub : {t : Set.Icc (0 : ℝ) T | ε < dist (Function.leftLim f t) (f t)} ⊆ F := by
      intro t ht
      by_contra hnotF
      have hnotMem : t ∉ F := hnotF
      by_cases htT : (t : ℝ) = T
      · have hKm : K ≥ m := by dsimp [K]; omega
        have huK : u K = t := by
          apply Subtype.ext
          exact (htm K hKm).trans htT.symm
        exact hnotMem ⟨K, Set.mem_Iic.mpr le_rfl, huK⟩
      · have htlt : (t : ℝ) < T := lt_of_le_of_ne t.2.2 htT
        let P : ℕ → Prop := fun n => (t : ℝ) < u (n + 1)
        have hPK : P K := by
          dsimp [P, K]
          have hKm : 2 * m + 1 ≥ m := by omega
          rw [htm (2 * m + 1) hKm]
          exact htlt
        have hex : ∃ n, P n := ⟨K, hPK⟩
        let n := Nat.find hex
        have hPn : P n := Nat.find_spec hex
        have hmin : ∀ k < n, ¬ P k := by
          intro k hk
          exact Nat.find_min hex hk
        have hnK : n ≤ K := by
          by_contra hn
          have hKn : K < n := Nat.lt_of_not_ge hn
          exact (hmin K hKn) hPK
        have hlo : (u n : ℝ) ≤ t := by
          by_cases hn0 : n = 0
          · have hfind0 : Nat.find hex = 0 := by simpa [n] using hn0
            change (u (Nat.find hex) : ℝ) ≤ t
            simpa [hfind0, hu0] using t.2.1
          · have hpos : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
            have hprev : n - 1 < n := by omega
            have hnot : ¬ (t : ℝ) < u n := by
              simpa [P, Nat.sub_add_cancel hpos] using hmin (n - 1) hprev
            exact le_of_not_gt hnot
        have hneq : (u n : ℝ) ≠ t := by
          intro heq
          apply hnotMem
          exact ⟨n, Set.mem_Iic.mpr hnK, Subtype.ext heq⟩
        have hleft : (u n : ℝ) < t := lt_of_le_of_ne hlo hneq
        have hright : (t : ℝ) < u (n + 1) := hPn
        have hleftSub : u n < t := Subtype.coe_lt_coe.mpr hleft
        have hgt : Set.Ioi (u n) ∈ 𝓝[Set.Iio t] t :=
          mem_nhdsWithin_iff_exists_mem_nhds_inter.mpr
            ⟨Set.Ioi (u n), Ioi_mem_nhds hleftSub, Set.inter_subset_left⟩
        have hev : ∀ᶠ s in 𝓝[Set.Iio t] t,
            dist (f s) (f t) ≤ ε / 2 := by
          filter_upwards [self_mem_nhdsWithin, hgt] with s hst hsu
          have hstR : (s : ℝ) < t := by exact_mod_cast hst
          have hsuR : (u n : ℝ) < s := by exact_mod_cast hsu
          have hsmall := hpart n s t hsuR.le (lt_trans hstR hright) hleft.le hright
          exact hsmall.le
        have hnebot : NeBot (𝓝[Set.Iio t] t) := by
          rw [← mem_closure_iff_nhdsWithin_neBot, closure_Iio'
            (Set.Iio_nonempty.mpr (not_isMin_iff.mpr ⟨u n, hleftSub⟩))]
          exact Set.mem_Iic.mpr le_rfl
        have hdist : Tendsto (fun s => dist (f s) (f t)) (𝓝[Set.Iio t] t)
            (𝓝 (dist (Function.leftLim f t) (f t))) :=
          ((isCadlag f).tendsto_nhdsLT_leftLim t).dist tendsto_const_nhds
        have hbound : dist (Function.leftLim f t) (f t) ≤ ε / 2 :=
          @IsClosed.mem_of_tendsto ℝ _ (Set.Icc (0 : ℝ) T)
            (dist (Function.leftLim f t) (f t)) (Set.Iic (ε / 2))
            (fun s : Set.Icc (0 : ℝ) T => dist (f s) (f t))
            (𝓝[Set.Iio t] t) hnebot isClosed_Iic hdist hev
        change ε < dist (Function.leftLim f t) (f t) at ht
        linarith
    exact hF.subset hsub
  · have hTneg : T < 0 := lt_of_not_ge hT
    apply Set.finite_empty.subset
    intro t ht
    have ht0 : 0 ≤ (t : ℝ) := t.2.1
    have htT : (t : ℝ) ≤ T := t.2.2
    change ε < dist (Function.leftLim f t) (f t) at ht
    linarith

/-- The set of discontinuity times of a càdlàg path is countable. -/
theorem countable_setOf_jump_ne [MetricSpace E] (f : D T E) :
    {t : Set.Icc (0 : ℝ) T | Function.leftLim f t ≠ f t}.Countable := by
  classical
  let A : ℕ → Set (Set.Icc (0 : ℝ) T) := fun n =>
    {t | 1 / (n + 1 : ℝ) < dist (Function.leftLim f t) (f t)}
  have hA : ∀ n, (A n).Countable := by
    intro n
    exact (finite_setOf_jump_gt f (by positivity)).countable
  have hsubset : {t : Set.Icc (0 : ℝ) T | Function.leftLim f t ≠ f t} ⊆ ⋃ n, A n := by
    intro t ht
    have hdist : 0 < dist (Function.leftLim f t) (f t) := dist_pos.mpr ht
    obtain ⟨n, hn⟩ := exists_nat_gt ((dist (Function.leftLim f t) (f t))⁻¹)
    have hden : (dist (Function.leftLim f t) (f t))⁻¹ < (n + 1 : ℝ) := by
      exact hn.trans (by norm_num)
    have hfrac : 1 / (n + 1 : ℝ) < dist (Function.leftLim f t) (f t) := by
      rw [div_lt_iff₀ (by positivity)]
      have hmul := mul_lt_mul_of_pos_left hden hdist
      field_simp at hmul ⊢
      nlinarith
    exact Set.mem_iUnion.mpr ⟨n, hfrac⟩
  exact (countable_iUnion hA).mono hsubset

/-- The next dyadic grid point, capped at the terminal time. -/
noncomputable def dyadicRightTime (hT : 0 ≤ T) (n : ℕ) (t : Set.Icc (0 : ℝ) T) :
    Set.Icc (0 : ℝ) T := by
  let k : ℝ := (2 : ℝ) ^ n
  let u : ℝ := (((Nat.ceil (k * (t : ℝ)) + 1 : ℕ) : ℝ) / k)
  have hk : 0 < k := by positivity
  have hceil : k * (t : ℝ) ≤ (Nat.ceil (k * (t : ℝ)) : ℝ) := Nat.le_ceil _
  have htRaw : (t : ℝ) ≤ u := by
    dsimp [u]
    rw [le_div_iff₀ hk]
    norm_num at *
    nlinarith
  exact ⟨min u T, le_min (le_trans t.2.1 htRaw) hT, min_le_right _ _⟩

/-- The dyadic right approximation is measurable as a function of time. -/
theorem measurable_dyadicRightTime (hT : 0 ≤ T) (n : ℕ) :
    Measurable (dyadicRightTime (T := T) hT n) := by
  classical
  unfold dyadicRightTime
  apply Measurable.subtype_mk
  have hk : 0 < (2 : ℝ) ^ n := by positivity
  have hcoe : Measurable fun t : Set.Icc (0 : ℝ) T => (t : ℝ) :=
    continuous_subtype_val.measurable
  have hmul : Measurable fun t : Set.Icc (0 : ℝ) T => (2 : ℝ) ^ n * (t : ℝ) :=
    measurable_const.mul hcoe
  have hceil : Measurable fun t : Set.Icc (0 : ℝ) T => Nat.ceil ((2 : ℝ) ^ n * (t : ℝ)) :=
    Nat.measurable_ceil.comp hmul
  have hcast : Measurable fun m : ℕ => (m : ℝ) := measurable_of_countable _
  have hraw : Measurable fun t : Set.Icc (0 : ℝ) T =>
      (((Nat.ceil ((2 : ℝ) ^ n * (t : ℝ)) + 1 : ℕ) : ℝ) / (2 : ℝ) ^ n) := by
    simpa using (hcast.comp (hceil.add_const 1)).div_const ((2 : ℝ) ^ n)
  have hmin : Measurable fun t : Set.Icc (0 : ℝ) T =>
      min ((((Nat.ceil ((2 : ℝ) ^ n * (t : ℝ)) + 1 : ℕ) : ℝ) / (2 : ℝ) ^ n)) T :=
    hraw.min measurable_const
  simpa using hmin

/-- For each fixed grid level, the dyadic right approximation has countable range. -/
theorem countable_range_dyadicRightTime (hT : 0 ≤ T) (n : ℕ) :
    (Set.range (dyadicRightTime (T := T) hT n)).Countable := by
  classical
  let g : ℕ → Set.Icc (0 : ℝ) T := fun m =>
    ⟨min ((((m + 1 : ℕ) : ℝ) / (2 : ℝ) ^ n)) T,
      le_min (by positivity) hT, min_le_right _ _⟩
  apply (countable_range g).mono
  rintro x ⟨t, rfl⟩
  refine ⟨Nat.ceil ((2 : ℝ) ^ n * (t : ℝ)), ?_⟩
  simp [dyadicRightTime, g]

/-- The dyadic right approximation never precedes the given time. -/
theorem le_dyadicRightTime (hT : 0 ≤ T) (n : ℕ) (t : Set.Icc (0 : ℝ) T) :
    t ≤ dyadicRightTime (T := T) hT n t := by
  apply Subtype.coe_le_coe.mpr
  unfold dyadicRightTime
  dsimp only
  let k : ℝ := (2 : ℝ) ^ n
  have hk : 0 < k := by positivity
  have hceil : k * (t : ℝ) ≤ (Nat.ceil (k * (t : ℝ)) : ℝ) := Nat.le_ceil _
  have hraw : (t : ℝ) ≤ (((Nat.ceil (k * (t : ℝ)) + 1 : ℕ) : ℝ) / k) := by
    rw [le_div_iff₀ hk]
    push_cast
    nlinarith
  exact le_min hraw t.2.2

/-- The next dyadic grid point is strictly to the right before the terminal time. -/
theorem lt_dyadicRightTime (hT : 0 ≤ T) (n : ℕ) {t : Set.Icc (0 : ℝ) T}
    (ht : (t : ℝ) < T) : t < dyadicRightTime (T := T) hT n t := by
  apply Subtype.coe_lt_coe.mpr
  unfold dyadicRightTime
  dsimp only
  let k : ℝ := (2 : ℝ) ^ n
  have hk : 0 < k := by positivity
  have hceil : k * (t : ℝ) ≤ (Nat.ceil (k * (t : ℝ)) : ℝ) := Nat.le_ceil _
  have hraw : (t : ℝ) < (((Nat.ceil (k * (t : ℝ)) + 1 : ℕ) : ℝ) / k) := by
    rw [lt_div_iff₀ hk]
    push_cast
    nlinarith
  exact lt_min hraw ht

/-- Dyadic right times converge to the time being approximated. -/
theorem tendsto_dyadicRightTime (hT : 0 ≤ T) (t : Set.Icc (0 : ℝ) T) :
    Tendsto (fun n => dyadicRightTime (T := T) hT n t) atTop (𝓝 t) := by
  rw [tendsto_iff_dist_tendsto_zero]
  have hpow : Tendsto (fun n : ℕ => (2 : ℝ) ^ n) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have herr : Tendsto (fun n : ℕ => 2 * ((2 : ℝ) ^ n)⁻¹) atTop (𝓝 0) := by
    convert (tendsto_inv_atTop_zero.comp hpow).const_mul 2 using 1 <;> simp [mul_comm]
  refine squeeze_zero (fun n => dist_nonneg) ?_ herr
  intro n
  have hq : (t : ℝ) ≤ (dyadicRightTime (T := T) hT n t : ℝ) :=
    Subtype.coe_le_coe.mp (le_dyadicRightTime hT n t)
  have hraw_lt :
      (((Nat.ceil (((2 : ℝ) ^ n) * (t : ℝ)) + 1 : ℕ) : ℝ) / (2 : ℝ) ^ n) <
        (t : ℝ) + 2 * ((2 : ℝ) ^ n)⁻¹ := by
    have hk : 0 < (2 : ℝ) ^ n := by positivity
    have hceil :
        (Nat.ceil ((2 : ℝ) ^ n * (t : ℝ)) : ℝ) < (2 : ℝ) ^ n * (t : ℝ) + 1 :=
      Nat.ceil_lt_add_one (mul_nonneg (by positivity) t.2.1)
    rw [div_lt_iff₀ hk]
    push_cast
    field_simp [ne_of_gt hk]
    nlinarith
  have hupper : (dyadicRightTime (T := T) hT n t : ℝ) ≤
      (t : ℝ) + 2 * ((2 : ℝ) ^ n)⁻¹ := by
    have hmin : (dyadicRightTime (T := T) hT n t : ℝ) ≤
        (((Nat.ceil (((2 : ℝ) ^ n) * (t : ℝ)) + 1 : ℕ) : ℝ) / (2 : ℝ) ^ n) := by
      unfold dyadicRightTime
      exact min_le_left _ _
    exact hmin.trans hraw_lt.le
  have hdist : dist (dyadicRightTime (T := T) hT n t) t ≤
      2 * ((2 : ℝ) ^ n)⁻¹ := by
    rw [Subtype.dist_eq, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hq)]
    linarith
  exact hdist

/-- Every càdlàg path on a positive compact interval is Borel measurable in time. -/
theorem measurable_path [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    (f : D T E) (hT : 0 < T) : Measurable (f : Set.Icc (0 : ℝ) T → E) := by
  let hT0 : 0 ≤ T := hT.le
  let g : ℕ → Set.Icc (0 : ℝ) T → E := fun n t => f (dyadicRightTime hT0 n t)
  have hg : ∀ n, Measurable (g n) := by
    intro n
    exact Measurable.comp_of_countable_range (measurable_dyadicRightTime hT0 n)
      (countable_range_dyadicRightTime hT0 n) f
  have hlim : Tendsto g atTop (𝓝 (f : Set.Icc (0 : ℝ) T → E)) := by
    rw [tendsto_pi_nhds]
    intro t
    by_cases ht : (t : ℝ) = T
    · have hqt : ∀ n, dyadicRightTime hT0 n t = t := by
        intro n
        apply Subtype.ext
        exact le_antisymm
          (by simpa [ht] using (dyadicRightTime hT0 n t).property.2)
          (Subtype.coe_le_coe.mp (le_dyadicRightTime hT0 n t))
      simp [g, hqt]
    · have htT : (t : ℝ) < T := lt_of_le_of_ne t.2.2 (by
        intro hEq
        exact ht hEq)
      have hwithin :
          Tendsto (fun n => dyadicRightTime hT0 n t) atTop
            (𝓝[Set.Ioi t] t) := by
        apply tendsto_nhdsWithin_iff.mpr
        exact ⟨tendsto_dyadicRightTime hT0 t,
          Filter.Eventually.of_forall fun n => lt_dyadicRightTime hT0 n htT⟩
      exact (isCadlag f).isRightContinuous t |>.tendsto.comp hwithin
  exact measurable_of_tendsto_metrizable hg hlim

end BGW.Skorokhod
