/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.StableBridgeClosed
public import BGW.StableTrees.BridgeProjective
public import BGW.StableTrees.StableContinuousMinimum
public import BGW.StableTrees.StableProcessLaw
public import BGW.Skorokhod.Restrict
public import BGW.Skorokhod.Vervaat
public import BGW.Skorokhod.VervaatContinuity

/-!
# The minimum of the stable bridge and continuity of the Vervaat transform

Strict prefixes of the closed stable bridge are absolutely continuous with respect to the stable
process. The unique continuous interior minimum theorem therefore applies to every dyadic prefix.
A countable intersection of these events gives uniqueness, interiority and continuity of the global
generalized minimum of the bridge. The deterministic Vervaat continuity theorem then applies, and
strict positivity away from the endpoints follows from uniqueness of the minimizing time
(L. Chaumont, Excursion normalisée, méandre et pont pour les processus de Lévy stables, Bull. Sci.
Math. 121 (1997), 377–403; W. Vervaat, A relation between Brownian bridge and Brownian excursion,
Ann. Probab. 7 (1979), 143–149).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology

namespace BGW.StableTrees

open BGW.Skorokhod

/-! ### Deterministic adapters between a path and its restriction to `[0,a]` -/

/-- Left limits in the restriction agree with those of the original path (also at `t = a`, since
only a left neighbourhood is used; at `t = 0` both are the value). -/
theorem leftLim_restrict_eq {T a : ℝ} (ha : 0 ≤ a) (haT : a ≤ T) (f : D T ℝ)
    (t : Set.Icc (0 : ℝ) a) :
    Function.leftLim (restrict (E := ℝ) haT f) t =
      Function.leftLim f (⟨t, t.2.1, t.2.2.trans haT⟩ : Set.Icc (0 : ℝ) T) := by
  let inc : Set.Icc (0 : ℝ) a → Set.Icc (0 : ℝ) T := fun u =>
    ⟨u, u.2.1, u.2.2.trans haT⟩
  by_cases ht0 : (t : ℝ) = 0
  · have htbot : IsBot t := by
      intro u
      change (t : ℝ) ≤ (u : ℝ)
      simpa [ht0] using u.2.1
    have hincbot : IsBot (inc t) := by
      intro u
      change (t : ℝ) ≤ (u : ℝ)
      simpa [ht0] using u.2.1
    rw [leftLim_eq_of_isBot htbot, leftLim_eq_of_isBot hincbot]
    rfl
  · have htpos : 0 < (t : ℝ) := lt_of_le_of_ne t.2.1 (Ne.symm ht0)
    let za : Set.Icc (0 : ℝ) a := ⟨0, le_rfl, ha⟩
    let zT : Set.Icc (0 : ℝ) T := ⟨0, le_rfl, ha.trans haT⟩
    have hza : za < t := htpos
    have hzT : zT < inc t := htpos
    let _ : (𝓝[<] t).NeBot := nhdsLT_neBot_of_exists_lt ⟨za, hza⟩
    let _ : (𝓝[<] inc t).NeBot := nhdsLT_neBot_of_exists_lt ⟨zT, hzT⟩
    apply leftLim_eq_of_tendsto
    have hinc : Continuous inc := Continuous.subtype_mk continuous_subtype_val _
    have hleft : Tendsto inc (𝓝[<] t) (𝓝[<] inc t) := by
      apply tendsto_nhdsWithin_iff.mpr
      refine ⟨tendsto_nhdsWithin_of_tendsto_nhds hinc.continuousAt, ?_⟩
      filter_upwards [self_mem_nhdsWithin] with u hu
      exact hu
    exact ((isCadlag f).tendsto_nhdsLT_leftLim (inc t)).comp hleft

/-- Continuity of the restriction at an interior time `t < a` gives continuity of the original. -/
theorem continuousAt_of_continuousAt_restrict {T a : ℝ} (ha : 0 ≤ a) (haT : a ≤ T) (f : D T ℝ)
    {t : Set.Icc (0 : ℝ) a} (ht : (t : ℝ) < a)
    (h : ContinuousAt (restrict (E := ℝ) haT f) t) :
    ContinuousAt f (⟨t, t.2.1, t.2.2.trans haT⟩ : Set.Icc (0 : ℝ) T) := by
  let _ : Nonempty (Set.Icc (0 : ℝ) a) := ⟨⟨0, le_rfl, ha⟩⟩
  let tT : Set.Icc (0 : ℝ) T := ⟨t, t.2.1, t.2.2.trans haT⟩
  change ContinuousAt f tT
  rw [Metric.continuousAt_iff] at h ⊢
  intro ε hε
  obtain ⟨δ, hδ, hδf⟩ := h ε hε
  refine ⟨min δ (a - t), lt_min hδ (sub_pos.mpr ht), ?_⟩
  intro u hu
  have huδ : dist u tT < δ := hu.trans_le (min_le_left _ _)
  have huAdist : dist u tT < a - t := hu.trans_le (min_le_right _ _)
  have huA : (u : ℝ) < a := by
    have hu_abs : |(u : ℝ) - t| < a - t := by
      simpa only [tT, Subtype.dist_eq, Real.dist_eq] using huAdist
    linarith [((abs_lt.mp hu_abs).2 : (u : ℝ) - t < a - t)]
  let ua : Set.Icc (0 : ℝ) a := ⟨u, u.2.1, huA.le⟩
  have hua : dist ua t < δ := by
    simpa [ua, tT, Subtype.dist_eq, Real.dist_eq] using huδ
  exact hδf hua

/-- If a generalized minimizer `g` of `f` lies in `[0,a]`, the prefix infimum is the global one. -/
theorem iInf_restrict_eq_of_genMin {T a : ℝ} (ha : 0 ≤ a) (haT : a ≤ T) (f : D T ℝ)
    {g : Set.Icc (0 : ℝ) T} (hg : IsGenMinimizer f g) (hga : (g : ℝ) ≤ a) :
    (⨅ t, restrict (E := ℝ) haT f t) = ⨅ t, f t := by
  let _ : Nonempty (Set.Icc (0 : ℝ) a) := ⟨⟨0, le_rfl, ha⟩⟩
  let ga : Set.Icc (0 : ℝ) a := ⟨g, g.2.1, hga⟩
  apply le_antisymm
  · calc
      (⨅ t, restrict (E := ℝ) haT f t) ≤ genVal (restrict (E := ℝ) haT f) ga :=
        iInf_le_genVal _ _
      _ = genVal f g := by
        unfold genVal
        rw [leftLim_restrict_eq ha haT f ga]
        rfl
      _ = ⨅ t, f t := hg
  · exact le_ciInf fun t =>
      ciInf_le (isBounded_range f).bddBelow ⟨t, t.2.1, t.2.2.trans haT⟩

/-- Endpoints are not generalized minimizers of a bridge path with negative infimum. -/
theorem not_isGenMinimizer_endpoints {f : D 1 ℝ}
    (h0 : f ⟨0, le_rfl, zero_le_one⟩ = 0) (h1 : f ⟨1, zero_le_one, le_rfl⟩ = 0)
    (hl : Function.leftLim f ⟨1, zero_le_one, le_rfl⟩ = 0) (hneg : (⨅ t, f t) < 0) :
    ¬ IsGenMinimizer f ⟨0, le_rfl, zero_le_one⟩ ∧ ¬ IsGenMinimizer f ⟨1, zero_le_one, le_rfl⟩ := by
  constructor
  · intro h
    have hval : min (Function.leftLim f ⟨0, le_rfl, zero_le_one⟩)
        (f ⟨0, le_rfl, zero_le_one⟩) = 0 := by
      rw [leftLim_eq_of_isBot (fun u => u.2.1), h0, min_self]
    rw [show (⨅ t, f t) = 0 from h.symm.trans hval] at hneg
    exact (lt_irrefl 0 hneg)
  · intro h
    have hval : min (Function.leftLim f ⟨1, zero_le_one, le_rfl⟩)
        (f ⟨1, zero_le_one, le_rfl⟩) = 0 := by rw [hl, h1, min_self]
    rw [show (⨅ t, f t) = 0 from h.symm.trans hval] at hneg
    exact (lt_irrefl 0 hneg)

/-! ### Probabilistic transfers to bridge prefixes -/

/-- The bridge takes a negative value: the infimum is `< 0` (regularity of `0` through a
prefix, plus `f 0 = 0` a.s.). -/
theorem stableBridgeLaw_ae_iInf_neg {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f : D 1 ℝ ∂(stableBridgeLaw θ : Measure (D 1 ℝ)), (⨅ t, f t) < 0 := by
  let a : ℝ := 1 / 2
  have ha : 0 < a := by norm_num [a]
  have ha1 : a < 1 := by norm_num [a]
  have hreg := (isStableLevyLaw_stableProcessLaw hθ ha).ae_regular_at_zero hθ ha
  have hmapped := (map_restrict_stableBridgeLaw_absolutelyContinuous hθ ha ha1).ae_le hreg
  have hpre := ae_of_ae_map (measurable_restrict ha1.le).aemeasurable hmapped
  filter_upwards [stableBridgeLaw_endpoints hθ, hpre] with f he hr
  obtain ⟨s, -, -, hs⟩ := (hr 1 zero_lt_one).1
  let t : Set.Icc (0 : ℝ) 1 := ⟨s, s.2.1, s.2.2.trans ha1.le⟩
  have hst : restrict (E := ℝ) ha1.le f s = f t := rfl
  have hz : restrict (E := ℝ) ha1.le f ⟨0, le_rfl, ha.le⟩ =
      f ⟨0, le_rfl, zero_le_one⟩ := rfl
  rw [hst, hz, he.1] at hs
  exact (ciInf_le (isBounded_range f).bddBelow t).trans_lt hs

/-- The unique continuous minimum theorem on each strict prefix `[0,a]`, `0 < a < 1`, transferred
through the absolutely continuous prefix law. -/
theorem stableBridgeLaw_ae_prefix_unique_continuous_minimum {θ a : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    (ha : 0 < a) (ha1 : a < 1) :
    ∀ᵐ f : D 1 ℝ ∂(stableBridgeLaw θ : Measure (D 1 ℝ)),
      ∃ g : Set.Icc (0 : ℝ) a,
        0 < (g : ℝ) ∧ (g : ℝ) < a ∧ ContinuousAt (restrict (E := ℝ) ha1.le f) g ∧
        min (Function.leftLim (restrict (E := ℝ) ha1.le f) g) (restrict (E := ℝ) ha1.le f g) =
          ⨅ t, restrict (E := ℝ) ha1.le f t ∧
        ∀ s : Set.Icc (0 : ℝ) a,
          min (Function.leftLim (restrict (E := ℝ) ha1.le f) s) (restrict (E := ℝ) ha1.le f s) =
            (⨅ t, restrict (E := ℝ) ha1.le f t) → s = g := by
  have hstable := (isStableLevyLaw_stableProcessLaw hθ ha).ae_unique_continuous_minimum hθ ha
  have hmapped := (map_restrict_stableBridgeLaw_absolutelyContinuous hθ ha ha1).ae_le hstable
  exact ae_of_ae_map (measurable_restrict ha1.le).aemeasurable hmapped

/-! ### The minimum of the bridge -/

/-- **Unique continuous interior minimum of the bridge.** Under the closed stable bridge law, almost
surely the infimum is negative and the generalized minimizer, `vervaatTime f`, is unique,
interior, and a continuity point of `f`. -/
theorem stableBridgeLaw_ae_minimum {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f : D 1 ℝ ∂(stableBridgeLaw θ : Measure (D 1 ℝ)),
      (⨅ t, f t) < 0 ∧
      (0 < (vervaatTime f : ℝ) ∧ (vervaatTime f : ℝ) < 1) ∧
      ContinuousAt f (vervaatTime f) ∧
      ∀ t : Set.Icc (0 : ℝ) 1,
        min (Function.leftLim f t) (f t) = (⨅ s, f s) → t = vervaatTime f := by
  have hprefix : ∀ᵐ f : D 1 ℝ ∂(stableBridgeLaw θ : Measure (D 1 ℝ)), ∀ n : ℕ,
      ∃ g : Set.Icc (0 : ℝ) (bridgeHorizon n),
        0 < (g : ℝ) ∧ (g : ℝ) < bridgeHorizon n ∧
        ContinuousAt (restrict (E := ℝ) (bridgeHorizon_lt_one n).le f) g ∧
        min (Function.leftLim (restrict (E := ℝ) (bridgeHorizon_lt_one n).le f) g)
          (restrict (E := ℝ) (bridgeHorizon_lt_one n).le f g) =
            ⨅ t, restrict (E := ℝ) (bridgeHorizon_lt_one n).le f t ∧
        ∀ s : Set.Icc (0 : ℝ) (bridgeHorizon n),
          min (Function.leftLim (restrict (E := ℝ) (bridgeHorizon_lt_one n).le f) s)
            (restrict (E := ℝ) (bridgeHorizon_lt_one n).le f s) =
              (⨅ t, restrict (E := ℝ) (bridgeHorizon_lt_one n).le f t) → s = g :=
    ae_all_iff.mpr fun n => stableBridgeLaw_ae_prefix_unique_continuous_minimum hθ
      (bridgeHorizon_pos n) (bridgeHorizon_lt_one n)
  filter_upwards [stableBridgeLaw_ae_iInf_neg hθ, stableBridgeLaw_endpoints hθ, hprefix]
    with f hneg he hp
  have hvmin : IsGenMinimizer f (vervaatTime f) := min_leftLim_vervaatTime f
  have hends := not_isGenMinimizer_endpoints he.1 he.2.1 he.2.2 hneg
  have hv0 : 0 < (vervaatTime f : ℝ) := by
    apply lt_of_le_of_ne (vervaatTime f).2.1
    intro h
    apply hends.1
    have hz : vervaatTime f = ⟨0, le_rfl, zero_le_one⟩ := Subtype.ext h.symm
    rwa [← hz]
  have hv1 : (vervaatTime f : ℝ) < 1 := by
    apply lt_of_le_of_ne (vervaatTime f).2.2
    intro h
    apply hends.2
    have hz : vervaatTime f = ⟨1, zero_le_one, le_rfl⟩ := Subtype.ext h
    rwa [← hz]
  have prefix_minimizer {a : ℝ} (ha : 0 < a) (ha1 : a < 1)
      {u : Set.Icc (0 : ℝ) 1} (hu : IsGenMinimizer f u) (hua : (u : ℝ) ≤ a) :
      IsGenMinimizer (restrict (E := ℝ) ha1.le f) ⟨u, u.2.1, hua⟩ := by
    have hi := iInf_restrict_eq_of_genMin ha.le ha1.le f hu hua
    change min (Function.leftLim (restrict (E := ℝ) ha1.le f) ⟨u, u.2.1, hua⟩)
      (restrict (E := ℝ) ha1.le f ⟨u, u.2.1, hua⟩) = _
    rw [leftLim_restrict_eq ha.le ha1.le f ⟨u, u.2.1, hua⟩, hi]
    exact hu
  have hcont : ContinuousAt f (vervaatTime f) := by
    obtain ⟨n, hn⟩ := exists_bridgeHorizon_ge hv1
    let m := n + 1
    have hvm : (vervaatTime f : ℝ) < bridgeHorizon m :=
      hn.trans_lt (strictMono_bridgeHorizon (Nat.lt_succ_self n))
    obtain ⟨g, hg0, hgm, hgc, hgmin, hguniq⟩ := hp m
    let va : Set.Icc (0 : ℝ) (bridgeHorizon m) := ⟨vervaatTime f, (vervaatTime f).2.1, hvm.le⟩
    have hvpre : IsGenMinimizer (restrict (E := ℝ) (bridgeHorizon_lt_one m).le f) va :=
      prefix_minimizer (bridgeHorizon_pos m) (bridgeHorizon_lt_one m) hvmin hvm.le
    have hvg : va = g := hguniq va hvpre
    have hgc' : ContinuousAt (restrict (E := ℝ) (bridgeHorizon_lt_one m).le f) va := by
      rwa [hvg]
    exact continuousAt_of_continuousAt_restrict (bridgeHorizon_pos m).le
      (bridgeHorizon_lt_one m).le f hvm hgc'
  refine ⟨hneg, ⟨hv0, hv1⟩, hcont, ?_⟩
  intro t ht
  have htmin : IsGenMinimizer f t := ht
  have ht0 : (t : ℝ) ≠ 0 := by
    intro h
    apply hends.1
    have hz : t = ⟨0, le_rfl, zero_le_one⟩ := Subtype.ext h
    rwa [← hz]
  have ht1 : (t : ℝ) ≠ 1 := by
    intro h
    apply hends.2
    have hz : t = ⟨1, zero_le_one, le_rfl⟩ := Subtype.ext h
    rwa [← hz]
  have htlt : (t : ℝ) < 1 := lt_of_le_of_ne t.2.2 ht1
  have hmax : max (vervaatTime f : ℝ) (t : ℝ) < 1 := max_lt hv1 htlt
  obtain ⟨n, hn⟩ := exists_bridgeHorizon_ge hmax
  let m := n + 1
  have hma : max (vervaatTime f : ℝ) (t : ℝ) < bridgeHorizon m :=
    hn.trans_lt (strictMono_bridgeHorizon (Nat.lt_succ_self n))
  have hvm : (vervaatTime f : ℝ) ≤ bridgeHorizon m := (le_max_left _ _).trans hma.le
  have htm : (t : ℝ) ≤ bridgeHorizon m := (le_max_right _ _).trans hma.le
  obtain ⟨g, hg0, hgm, hgc, hgmin, hguniq⟩ := hp m
  let va : Set.Icc (0 : ℝ) (bridgeHorizon m) := ⟨vervaatTime f, (vervaatTime f).2.1, hvm⟩
  let ta : Set.Icc (0 : ℝ) (bridgeHorizon m) := ⟨t, t.2.1, htm⟩
  have hvpre : IsGenMinimizer (restrict (E := ℝ) (bridgeHorizon_lt_one m).le f) va :=
    prefix_minimizer (bridgeHorizon_pos m) (bridgeHorizon_lt_one m) hvmin hvm
  have htpre : IsGenMinimizer (restrict (E := ℝ) (bridgeHorizon_lt_one m).le f) ta :=
    prefix_minimizer (bridgeHorizon_pos m) (bridgeHorizon_lt_one m) htmin htm
  have hta : ta = va := (hguniq ta htpre).trans (hguniq va hvpre).symm
  have hval := congrArg (fun u : Set.Icc (0 : ℝ) (bridgeHorizon m) => (u : ℝ)) hta
  exact Subtype.ext hval

/-- The same in `∃`-form with `IsGenMinimizer`. -/
theorem stableBridgeLaw_ae_existsUnique_continuous_minimizer {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f : D 1 ℝ ∂(stableBridgeLaw θ : Measure (D 1 ℝ)),
      (⨅ t, f t) < 0 ∧
      ∃ g : Set.Icc (0 : ℝ) 1,
        0 < (g : ℝ) ∧ (g : ℝ) < 1 ∧ ContinuousAt f g ∧ IsGenMinimizer f g ∧
        ∀ s : Set.Icc (0 : ℝ) 1, IsGenMinimizer f s → s = g := by
  filter_upwards [stableBridgeLaw_ae_minimum hθ] with f hf
  exact ⟨hf.1, vervaatTime f, hf.2.1.1, hf.2.1.2, hf.2.2.1,
    min_leftLim_vervaatTime f, hf.2.2.2⟩

/-! ### Continuity of the Vervaat transform at the bridge -/

/-- **Vervaat continuity.** Under the bridge law, the càdlàg Vervaat map is almost surely continuous
at the path. -/
theorem stableBridgeLaw_ae_continuousAt_vervaatD {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f : D 1 ℝ ∂(stableBridgeLaw θ : Measure (D 1 ℝ)), ContinuousAt vervaatD f := by
  filter_upwards [stableBridgeLaw_endpoints hθ, stableBridgeLaw_ae_minimum hθ,
    stableBridgeLaw_ae_continuousAt hθ ⟨1, zero_le_one, le_rfl⟩] with f he hm h1
  exact (continuousAt_vervaatD he.1 h1 hm.2.2.2 hm.2.1 hm.2.2.1).1

/-- **Vervaat endpoints.** Almost surely the Vervaat image starts and ends at `0`, is continuous at
`1`, and is continuous at the wrap point `1 - vervaatTime f`. -/
theorem stableBridgeLaw_ae_vervaat_endpoints {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f : D 1 ℝ ∂(stableBridgeLaw θ : Measure (D 1 ℝ)),
      vervaatD f ⟨0, le_rfl, zero_le_one⟩ = 0 ∧
      vervaatD f ⟨1, zero_le_one, le_rfl⟩ = 0 ∧
      ContinuousAt (vervaatD f) ⟨1, zero_le_one, le_rfl⟩ ∧
      ContinuousAt (vervaatD f) (Set.projIcc 0 1 zero_le_one (1 - (vervaatTime f : ℝ))) := by
  filter_upwards [stableBridgeLaw_endpoints hθ, stableBridgeLaw_ae_minimum hθ,
    stableBridgeLaw_ae_continuousAt hθ ⟨1, zero_le_one, le_rfl⟩] with f he hm h1
  have hc := continuousAt_vervaatD he.1 h1 hm.2.2.2 hm.2.1 hm.2.2.1
  have hv := vervaatD_one_of_continuousAt hm.2.1.1 hm.2.2.1
  exact ⟨hc.2.1, by rw [hv.1, he.2.1, he.1, sub_zero], hv.2, hc.2.2⟩

/-- **Strict positivity of the Vervaat image.** Almost surely the Vervaat transform of the bridge
path is strictly positive on `(0, 1)` (the excursion property). -/
theorem stableBridgeLaw_ae_vervaatD_pos {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f : D 1 ℝ ∂(stableBridgeLaw θ : Measure (D 1 ℝ)),
      ∀ t : Set.Icc (0 : ℝ) 1, 0 < (t : ℝ) → (t : ℝ) < 1 → 0 < vervaatD f t := by
  filter_upwards [stableBridgeLaw_endpoints hθ, stableBridgeLaw_ae_minimum hθ] with f he hm
  intro t ht0 ht1
  have hvalue {u : Set.Icc (0 : ℝ) 1} (hu : u ≠ vervaatTime f) : (⨅ s, f s) < f u := by
    have hle : (⨅ s, f s) ≤ f u := ciInf_le (isBounded_range f).bddBelow u
    apply lt_of_le_of_ne hle
    intro heq
    apply hu
    apply hm.2.2.2 u
    apply le_antisymm
    · rw [heq]
      exact min_le_right _ _
    · exact iInf_le_genVal f u
  change 0 < if (vervaatTime f : ℝ) + t ≤ 1 then
    f (Set.projIcc 0 1 zero_le_one ((vervaatTime f : ℝ) + t)) - ⨅ s, f s
  else
    f (Set.projIcc 0 1 zero_le_one ((vervaatTime f : ℝ) + t - 1)) +
      f ⟨1, zero_le_one, le_rfl⟩ - (⨅ s, f s) - f ⟨0, le_rfl, zero_le_one⟩
  by_cases ht : (vervaatTime f : ℝ) + t ≤ 1
  · rw [ite_eq_left ht, sub_pos]
    apply hvalue
    intro hu
    have hmem : (vervaatTime f : ℝ) + t ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨add_nonneg (vervaatTime f).2.1 t.2.1, ht⟩
    have heq := congrArg Subtype.val hu
    rw [projIcc_of_mem zero_le_one hmem] at heq
    dsimp at heq
    linarith
  · rw [ite_eq_right ht]
    have hsum : 1 < (vervaatTime f : ℝ) + t := lt_of_not_ge ht
    have hmem : (vervaatTime f : ℝ) + t - 1 ∈ Set.Icc (0 : ℝ) 1 := by
      constructor <;> linarith [(vervaatTime f).2.2, t.2.2]
    have hu : Set.projIcc 0 1 zero_le_one ((vervaatTime f : ℝ) + t - 1) ≠
        vervaatTime f := by
      intro hu
      have heq := congrArg Subtype.val hu
      rw [projIcc_of_mem zero_le_one hmem] at heq
      dsimp at heq
      linarith
    simpa [he.1, he.2.1] using sub_pos.mpr (hvalue hu)

end BGW.StableTrees
